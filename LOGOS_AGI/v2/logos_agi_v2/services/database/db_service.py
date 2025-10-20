# logos_agi_v1/services/database/db_service.py

from dotenv import load_dotenv

load_dotenv()

import os
import pika
import json
import logging
import time
from persistence_manager import PersistenceManager

# --- Basic Configuration ---
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - DB_SERVICE - %(message)s"
)

RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
DB_WRITE_QUEUE = "db_write_queue"


class DatabaseService:
    def __init__(self):
        self.persistence_manager = PersistenceManager()
        self.connection = self._connect_to_rabbitmq()
        self.channel = self.connection.channel()
        self._setup_queues()

    def _connect_to_rabbitmq(self):
        """Establishes and returns a connection to RabbitMQ with retries."""
        for i in range(5):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(host=RABBITMQ_HOST))
                logging.info("Successfully connected to RabbitMQ.")
                return connection
            except pika.exceptions.AMQPConnectionError as e:
                logging.warning(f"Attempt {i+1}/5: Failed to connect to RabbitMQ: {e}. Retrying...")
                time.sleep(5)
        logging.error("Could not connect to RabbitMQ after several attempts. Exiting.")
        exit(1)

    def _setup_queues(self):
        """Declares the queues this service will listen to."""
        logging.info(f"Declaring queue: {DB_WRITE_QUEUE}")
        self.channel.queue_declare(queue=DB_WRITE_QUEUE, durable=True)

    def handle_write_request(self, ch, method, properties, body):
        """Callback function to handle incoming messages on the write queue."""
        try:
            message = json.loads(body)
            logging.info(f"Received write request for table '{message.get('table')}'")
            table = message.get("table")
            data = message.get("data")
            if not table or not data:
                logging.error("Invalid write request: missing 'table' or 'data'.")
                ch.basic_ack(delivery_tag=method.delivery_tag)
                return
            self.persistence_manager.save(table, data)
            logging.info(f"Successfully processed write request for table '{table}'.")
        except json.JSONDecodeError:
            logging.error("Failed to decode JSON from message body.")
        except Exception as e:
            logging.error(f"An unexpected error occurred while processing write request: {e}")
        ch.basic_ack(delivery_tag=method.delivery_tag)

    def start_consuming(self):
        """Starts consuming messages from the declared queues."""
        self.channel.basic_qos(prefetch_count=1)
        self.channel.basic_consume(
            queue=DB_WRITE_QUEUE, on_message_callback=self.handle_write_request
        )
        logging.info("Database Service is running and waiting for messages...")
        try:
            self.channel.start_consuming()
        except KeyboardInterrupt:
            self.channel.stop_consuming()
        self.connection.close()
        logging.info("Database Service has shut down.")


if __name__ == "__main__":
    db_service = DatabaseService()
    db_service.start_consuming()
