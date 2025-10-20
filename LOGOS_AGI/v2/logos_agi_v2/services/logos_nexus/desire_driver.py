import os
import pika
import json
import time
import logging
import asyncio
import uuid
from threading import Thread
from .desire_driver import GodelianDesireDriver
from .goal_manager import GoalManager
from .asi_controller import ASILiftoffController
from .self_improvement_manager import SelfImprovementManager
from core.unified_formalisms import UnifiedFormalismValidator, ModalProposition

class LogosNexus:
    def __init__(self, rabbitmq_host='rabbitmq'):
        self.logger = logging.getLogger("LOGOS_NEXUS")
        self.rabbitmq_host = rabbitmq_host
        self.validator = UnifiedFormalismValidator()
        self.desire_driver = GodelianDesireDriver()
        self.goal_manager = GoalManager()
        self.self_improvement_manager = SelfImprovementManager(self)
        self.asi_controller = ASILiftoffController(self)
        self.connection, self.channel = self._connect_rabbitmq()
        self._setup_queues()

    def _connect_rabbitmq(self):
        for _ in range(10):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(self.rabbitmq_host, heartbeat=600))
                channel = connection.channel()
                self.logger.info("Logos Nexus connected to RabbitMQ.")
                return connection, channel
            except pika.exceptions.AMQPConnectionError:
                self.logger.warning("RabbitMQ not ready for Logos Nexus. Retrying in 5s...")
                time.sleep(5)
        raise ConnectionError("Could not connect to RabbitMQ")

    def _setup_queues(self):
        self.channel.queue_declare(queue='logos_nexus_requests', durable=True)
        self.channel.queue_declare(queue='archon_goals', durable=True)
        self.channel.queue_declare(queue='task_result_queue', durable=True)

    def publish(self, queue, payload):
        try:
            # Pika is not thread-safe, so we need a new connection for publishing from async context
            connection = pika.BlockingConnection(pika.ConnectionParameters(self.rabbitmq_host))
            channel = connection.channel()
            channel.basic_publish(exchange='', routing_key=queue, body=json.dumps(payload), properties=pika.BasicProperties(delivery_mode=2))
            connection.close()
            self.logger.info(f"Published to {queue}: Task {payload.get('task_id')}")
        except Exception as e:
            self.logger.error(f"Failed to publish to {queue}: {e}")

    def on_external_request(self, ch, method, properties, body):
        try:
            data = json.loads(body)
            query = data.get('query')
            task_id = data.get('task_id', str(uuid.uuid4()))
            self.logger.info(f"Received external request [{task_id}]: '{query}'")
            
            validation_req = {"proposition": ModalProposition(query), "operation": "evaluate", "entity": "external_goal", "context": {}}
            result = self.validator.validate_agi_operation(validation_req)
            
            if result.get("authorized"):
                self.logger.info(f"Request [{task_id}] PASSED TLM validation.")
                goal = self.goal_manager.propose_goal(name=query, source="external")
                self.goal_manager.adopt_goal(goal)
                payload = {"goal_description": goal.name, "task_id": task_id, "token": result["token"]}
                self.publish('archon_goals', payload)
            else:
                self.logger.error(f"Request [{task_id}] REJECTED by TLM: {result.get('reason')}")
        except Exception as e:
            self.logger.error(f"Error in on_external_request: {e}", exc_info=True)
        finally:
            ch.basic_ack(delivery_tag=method.delivery_tag)

    def on_result_received(self, ch, method, properties, body):
        self.logger.info(f"Received a final result: {body.decode()}")
        ch.basic_ack(delivery_tag=method.delivery_tag)

    def start_consuming(self):
        self.channel.basic_consume(queue='logos_nexus_requests', on_message_callback=self.on_external_request)
        self.channel.basic_consume(queue='task_result_queue', on_message_callback=self.on_result_received)
        self.logger.info("Logos Nexus consuming requests and results.")
        self.channel.start_consuming()

    def run_autonomous_loop(self):
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        # We need to adapt the publish method for asyncio
        async def async_publish(queue, payload):
            self.publish(queue, payload)
        self.asi_controller.logos_nexus.publish = async_publish # Monkey-patch for async context
        loop.run_until_complete(self.asi_controller.start())
        loop.close()

    def start(self):
        consumer_thread = Thread(target=self.start_consuming, daemon=True)
        consumer_thread.start()
        
        autonomous_thread = Thread(target=self.run_autonomous_loop, daemon=True)
        autonomous_thread.start()

        self.logger.info("Logos Nexus started with consumer and autonomous loops.")
        while True:
            time.sleep(10)

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    rabbitmq_host = os.getenv("RABBITMQ_HOST", "rabbitmq")
    nexus = LogosNexus(rabbitmq_host=rabbitmq_host)
    nexus.start()