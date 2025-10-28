# logos_agi_v1/services/database/db_service.py

from dotenv import load_dotenv

load_dotenv()

import os
import pika
import json
import logging
import time
import signal
import sys
from persistence_manager import PersistenceManager

# --- Configuration ---
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - DB_SERVICE - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("/data/db_service.log", mode="a"),
    ],
)

RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
RABBITMQ_PORT = int(os.getenv("RABBITMQ_PORT", "5672"))
RABBITMQ_USER = os.getenv("RABBITMQ_USER", "guest")
RABBITMQ_PASS = os.getenv("RABBITMQ_PASS", "guest")

# Queue configuration
DB_WRITE_QUEUE = "db_write_queue"
DB_QUERY_QUEUE = "db_query_queue"  # For future read operations
DB_RESPONSE_QUEUE = "db_response_queue"  # For query responses


class DatabaseService:
    """
    Main database service that consumes messages from RabbitMQ queues
    and handles database operations through the PersistenceManager.
    """

    def __init__(self):
        self.persistence_manager = PersistenceManager()
        self.connection = None
        self.channel = None
        self.is_running = False

        # Setup graceful shutdown handling
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

        self._connect_to_rabbitmq()
        logging.info("DatabaseService initialized successfully.")

    def _connect_to_rabbitmq(self):
        """Establishes connection to RabbitMQ with retries and proper error handling."""
        max_retries = 10
        retry_delay = 5

        for attempt in range(1, max_retries + 1):
            try:
                credentials = pika.PlainCredentials(RABBITMQ_USER, RABBITMQ_PASS)
                parameters = pika.ConnectionParameters(
                    host=RABBITMQ_HOST,
                    port=RABBITMQ_PORT,
                    credentials=credentials,
                    heartbeat=600,  # 10 minutes
                    blocked_connection_timeout=300,  # 5 minutes
                )

                self.connection = pika.BlockingConnection(parameters)
                self.channel = self.connection.channel()

                # Setup queues and bindings
                self._setup_queues()

                logging.info(
                    f"Successfully connected to RabbitMQ at {RABBITMQ_HOST}:{RABBITMQ_PORT}"
                )
                return

            except pika.exceptions.AMQPConnectionError as e:
                logging.warning(
                    f"Attempt {attempt}/{max_retries}: Failed to connect to RabbitMQ: {e}"
                )
                if attempt < max_retries:
                    logging.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                else:
                    logging.error("Could not connect to RabbitMQ after all attempts. Exiting.")
                    sys.exit(1)
            except Exception as e:
                logging.error(f"Unexpected error connecting to RabbitMQ: {e}")
                sys.exit(1)

    def _setup_queues(self):
        """Declares and configures all necessary queues."""
        try:
            # Write queue for database operations
            self.channel.queue_declare(
                queue=DB_WRITE_QUEUE,
                durable=True,
                arguments={"x-max-length": 10000},  # Prevent unbounded queue growth
            )

            # Query queue for read operations (future expansion)
            self.channel.queue_declare(
                queue=DB_QUERY_QUEUE, durable=True, arguments={"x-max-length": 5000}
            )

            # Response queue for query results
            self.channel.queue_declare(
                queue=DB_RESPONSE_QUEUE, durable=True, arguments={"x-max-length": 5000}
            )

            # Set QoS to process one message at a time
            self.channel.basic_qos(prefetch_count=1)

            logging.info("All database service queues declared successfully.")

        except Exception as e:
            logging.error(f"Failed to setup queues: {e}")
            raise

    def handle_write_request(self, ch, method, properties, body):
        """
        Callback function to handle incoming write requests on the write queue.

        Expected message format:
        {
            "table": "table_name",
            "data": {...},
            "operation": "save|execute",  # optional, defaults to "save"
            "request_id": "unique_id"     # optional, for tracking
        }
        """
        start_time = time.time()
        request_id = "unknown"

        try:
            # Parse message
            message = json.loads(body.decode("utf-8"))
            request_id = message.get("request_id", f"req_{int(time.time() * 1000)}")
            table = message.get("table")
            data = message.get("data")
            operation = message.get("operation", "save")

            logging.info(
                f"Processing write request {request_id} for table '{table}', operation: {operation}"
            )

            # Validate required fields
            if not table:
                raise ValueError("Missing required 'table' field in message")
            if not data and operation == "save":
                raise ValueError("Missing required 'data' field for save operation")

            # Process the request based on operation type
            success = False
            if operation == "save":
                success = self.persistence_manager.save(table, data)
            elif operation == "execute":
                # For direct SQL execution (use with caution)
                sql = data.get("sql")
                params = data.get("params", ())
                if sql:
                    success = self.persistence_manager.execute(sql, params)
                else:
                    raise ValueError("SQL statement required for execute operation")
            else:
                raise ValueError(f"Unknown operation: {operation}")

            if success:
                processing_time = time.time() - start_time
                logging.info(
                    f"Successfully processed request {request_id} in {processing_time:.3f}s"
                )

                # Log successful operations to system log
                self.persistence_manager.log_system_event(
                    source="database_service",
                    data={
                        "operation": operation,
                        "table": table,
                        "request_id": request_id,
                        "processing_time": processing_time,
                        "status": "success",
                    },
                )
            else:
                logging.error(f"Failed to process request {request_id}")

        except json.JSONDecodeError as e:
            logging.error(f"Invalid JSON in request {request_id}: {e}")
        except ValueError as e:
            logging.error(f"Invalid request {request_id}: {e}")
        except Exception as e:
            logging.error(f"Unexpected error processing request {request_id}: {e}")
        finally:
            # Always acknowledge the message to prevent redelivery
            try:
                ch.basic_ack(delivery_tag=method.delivery_tag)
            except Exception as e:
                logging.error(f"Failed to acknowledge message: {e}")

    def handle_query_request(self, ch, method, properties, body):
        """
        Callback function to handle incoming query requests.

        Expected message format:
        {
            "query": "SELECT * FROM table WHERE condition = ?",
            "params": [...],
            "request_id": "unique_id",
            "reply_to": "response_queue_name"  # optional
        }
        """
        start_time = time.time()
        request_id = "unknown"

        try:
            # Parse message
            message = json.loads(body.decode("utf-8"))
            request_id = message.get("request_id", f"query_{int(time.time() * 1000)}")
            query = message.get("query")
            params = message.get("params", ())
            reply_to = message.get("reply_to", DB_RESPONSE_QUEUE)

            logging.info(f"Processing query request {request_id}")

            if not query:
                raise ValueError("Missing required 'query' field in message")

            # Execute query
            results = self.persistence_manager.query(query, params)
            processing_time = time.time() - start_time

            # Prepare response
            response = {
                "request_id": request_id,
                "status": "success",
                "results": results,
                "row_count": len(results),
                "processing_time": processing_time,
            }

            # Send response
            self.channel.basic_publish(
                exchange="",
                routing_key=reply_to,
                body=json.dumps(response),
                properties=pika.BasicProperties(
                    delivery_mode=2, correlation_id=request_id  # Make message persistent
                ),
            )

            logging.info(
                f"Query request {request_id} completed in {processing_time:.3f}s, returned {len(results)} rows"
            )

        except json.JSONDecodeError as e:
            logging.error(f"Invalid JSON in query request {request_id}: {e}")
        except Exception as e:
            logging.error(f"Error processing query request {request_id}: {e}")

            # Send error response
            try:
                error_response = {
                    "request_id": request_id,
                    "status": "error",
                    "error": str(e),
                    "processing_time": time.time() - start_time,
                }

                reply_to = (
                    message.get("reply_to", DB_RESPONSE_QUEUE)
                    if "message" in locals()
                    else DB_RESPONSE_QUEUE
                )
                self.channel.basic_publish(
                    exchange="",
                    routing_key=reply_to,
                    body=json.dumps(error_response),
                    properties=pika.BasicProperties(correlation_id=request_id),
                )
            except Exception as send_error:
                logging.error(f"Failed to send error response: {send_error}")
        finally:
            # Acknowledge the message
            try:
                ch.basic_ack(delivery_tag=method.delivery_tag)
            except Exception as e:
                logging.error(f"Failed to acknowledge query message: {e}")

    def start_consuming(self):
        """Starts consuming messages from the declared queues."""
        try:
            # Setup consumers
            self.channel.basic_consume(
                queue=DB_WRITE_QUEUE, on_message_callback=self.handle_write_request
            )

            self.channel.basic_consume(
                queue=DB_QUERY_QUEUE, on_message_callback=self.handle_query_request
            )

            self.is_running = True
            logging.info("Database Service is running and waiting for messages...")
            logging.info(f"Listening on queues: {DB_WRITE_QUEUE}, {DB_QUERY_QUEUE}")

            # Log service startup
            self.persistence_manager.log_system_event(
                source="database_service",
                data={
                    "event": "service_started",
                    "queues": [DB_WRITE_QUEUE, DB_QUERY_QUEUE],
                    "database_stats": self.persistence_manager.get_database_stats(),
                },
            )

            # Start consuming
            self.channel.start_consuming()

        except KeyboardInterrupt:
            logging.info("Received interrupt signal, shutting down gracefully...")
            self._shutdown()
        except Exception as e:
            logging.error(f"Error in consumer loop: {e}")
            self._shutdown()

    def _signal_handler(self, signum, frame):
        """Handle system signals for graceful shutdown."""
        logging.info(f"Received signal {signum}, initiating shutdown...")
        self._shutdown()

    def _shutdown(self):
        """Gracefully shutdown the database service."""
        if self.is_running:
            self.is_running = False

            # Log service shutdown
            try:
                self.persistence_manager.log_system_event(
                    source="database_service",
                    data={
                        "event": "service_shutdown",
                        "database_stats": self.persistence_manager.get_database_stats(),
                    },
                )
            except Exception as e:
                logging.error(f"Failed to log shutdown event: {e}")

            # Stop consuming messages
            if self.channel and self.channel.is_open:
                try:
                    self.channel.stop_consuming()
                    logging.info("Stopped consuming messages.")
                except Exception as e:
                    logging.error(f"Error stopping consumer: {e}")

            # Close connections
            if self.connection and self.connection.is_open:
                try:
                    self.connection.close()
                    logging.info("RabbitMQ connection closed.")
                except Exception as e:
                    logging.error(f"Error closing connection: {e}")

            # Close persistence manager
            try:
                self.persistence_manager.close()
            except Exception as e:
                logging.error(f"Error closing persistence manager: {e}")

            logging.info("Database Service has shut down gracefully.")


def main():
    """Main entry point for the database service."""
    try:
        logging.info("Starting Database Service...")

        # Create and start the service
        db_service = DatabaseService()
        db_service.start_consuming()

    except Exception as e:
        logging.error(f"Failed to start Database Service: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
