# logos_agi_v1/services/logos_nexus/logos_nexus.py

import os
import pika
import json
import time
import logging
from threading import Thread
from self_improvement_manager import SelfImprovementManager
from dotenv import load_dotenv
load_dotenv()

# --- Basic Configuration ---
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - LOGOS - %(message)s')

RABBITMQ_HOST = os.getenv('RABBITMQ_HOST', 'rabbitmq')
GOAL_QUEUE = 'goal_queue'            # Receives new goals from Keryx
STRATEGIC_TASK_QUEUE = 'strategic_task_queue' # Sends tasks to Archon
DB_WRITE_QUEUE = 'db_write_queue'    # Sends data to be saved by DB Service

class LogosNexus:
    def __init__(self):
        self.connection = self._connect_to_rabbitmq()
        self.channel = self.connection.channel()
        self._setup_queues()
        self.self_improvement_manager = SelfImprovementManager(self.channel)

        # In-memory state (a real system would persist this more robustly)
        self.active_goals = {}
        self.system_priorities = [] # List of goal_ids ordered by priority

    def _connect_to_rabbitmq(self):
        # Retry logic for startup robustness
        for i in range(10):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(host=RABBITMQ_HOST))
                logging.info("Logos Nexus successfully connected to RabbitMQ.")
                return connection
            except pika.exceptions.AMQPConnectionError as e:
                logging.warning(f"Attempt {i+1}/10: Logos Nexus failed to connect to RabbitMQ: {e}. Retrying in 5s...")
                time.sleep(5)
        logging.error("Logos Nexus could not connect to RabbitMQ. Exiting.")
        exit(1)

    def _setup_queues(self):
        """Declare all necessary queues."""
        self.channel.queue_declare(queue=GOAL_QUEUE, durable=True)
        self.channel.queue_declare(queue=STRATEGIC_TASK_QUEUE, durable=True)
        self.channel.queue_declare(queue=DB_WRITE_QUEUE, durable=True)
        logging.info("Logos Nexus queues declared successfully.")

    def _publish_to_db(self, table, data):
        """Helper to send a write request to the database service."""
        message = {'table': table, 'data': data}
        self.channel.basic_publish(
            exchange='',
            routing_key=DB_WRITE_QUEUE,
            body=json.dumps(message),
            properties=pika.BasicProperties(delivery_mode=2)
        )

    def process_new_goal(self, ch, method, properties, body):
        """Callback for handling incoming goals from the Keryx API."""
        try:
            goal_data = json.loads(body)
            goal_id = goal_data['goal_id']
            logging.info(f"Received new goal {goal_id}: '{goal_data['goal_description']}'")

            # 1. Update internal state
            self.active_goals[goal_id] = goal_data
            # Simple priority insertion - could be more complex
            self.system_priorities.append(goal_id)
            self.system_priorities.sort(key=lambda gid: self.active_goals[gid].get('priority', 5))

            # 2. Persist the new goal's status
            db_record = {
                'goal_id': goal_id,
                'status': 'acknowledged',
                'description': goal_data['goal_description'],
                'priority': goal_data.get('priority', 5)
            }
            self._publish_to_db('goals', db_record)

            # 3. Formulate and dispatch a strategic task to Archon Nexus
            strategic_task = {
                'task_id': f"strat_{goal_id}",
                'goal_id': goal_id,
                'type': 'ANALYZE_AND_PLAN',
                'prompt': f"Formulate a high-level plan to achieve the following goal: {goal_data['goal_description']}"
            }

            self.channel.basic_publish(
                exchange='',
                routing_key=STRATEGIC_TASK_QUEUE,
                body=json.dumps(strategic_task),
                properties=pika.BasicProperties(delivery_mode=2)
            )
            logging.info(f"Dispatched strategic task for goal {goal_id} to Archon Nexus.")

        except Exception as e:
            logging.error(f"Error processing new goal: {e}")

        ch.basic_ack(delivery_tag=method.delivery_tag)

    def start_main_loop(self):
        """The main operational loop of the Logos Nexus."""
        # Start a separate thread for consuming messages so the main loop isn't blocked.
        consumer_thread = Thread(target=self.start_consuming, daemon=True)
        consumer_thread.start()

        logging.info("Logos Nexus Main Loop started. Monitoring system state.")
        while True:
            # This loop represents the "consciousness" or "will" of the AGI.
            # It reviews priorities, checks system health, and initiates meta-level tasks.

            # For example, trigger the self-improvement cycle every 60 seconds
            time.sleep(60)
            logging.info("Main loop tick: Initiating self-improvement analysis.")
            self.self_improvement_manager.run_analysis_cycle()

    def start_consuming(self):
        """Starts consuming goals from the goal_queue."""
        self.channel.basic_qos(prefetch_count=1)
        self.channel.basic_consume(queue=GOAL_QUEUE, on_message_callback=self.process_new_goal)

        logging.info("Logos Nexus is now consuming goals from the queue.")
        try:
            self.channel.start_consuming()
        except Exception as e:
            logging.error(f"Consumer unexpectedly stopped: {e}")


if __name__ == '__main__':
    logos = LogosNexus()
    logos.start_main_loop()
