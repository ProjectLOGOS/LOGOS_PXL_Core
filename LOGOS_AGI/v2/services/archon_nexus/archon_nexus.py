import os
import pika
import json
import time
import logging
import uuid
from .agent_system import AgentOrchestrator
from .workflow_architect import WorkflowArchitect

class ArchonNexus:
    def __init__(self, rabbitmq_host='rabbitmq'):
        self.logger = logging.getLogger("ARCHON_NEXUS")
        self.rabbitmq_host = rabbitmq_host
        self.orchestrator = AgentOrchestrator(db_manager=None) # DB would be a proper client
        self.workflow_architect = WorkflowArchitect()
        self.active_workflows = {}
        self.connection, self.channel = self._connect_rabbitmq()
        self._setup_queues()

    def _connect_rabbitmq(self):
        for _ in range(10):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(self.rabbitmq_host, heartbeat=600))
                channel = connection.channel()
                self.logger.info("Archon Nexus connected to RabbitMQ.")
                return connection, channel
            except pika.exceptions.AMQPConnectionError:
                self.logger.warning("RabbitMQ not ready for Archon Nexus. Retrying in 5s...")
                time.sleep(5)
        raise ConnectionError("Could not connect to RabbitMQ")

    def _setup_queues(self):
        self.channel.queue_declare(queue='archon_goals', durable=True)
        self.channel.queue_declare(queue='task_result_queue', durable=True)
        self.channel.queue_declare(queue='thonoc_task_queue', durable=True)
        self.channel.queue_declare(queue='telos_task_queue', durable=True)
        self.channel.queue_declare(queue='tetragnos_task_queue', durable=True)

    def on_goal_received(self, ch, method, properties, body):
        try:
            data = json.loads(body)
            goal_desc = data['goal_description']
            task_id = data.get('task_id', 'unknown_task')
            self.logger.info(f"Received goal [{task_id}]: '{goal_desc}'")

            # This is a simplified workflow: just execute directly
            result = self.orchestrator.execute_goal(goal_desc)
            
            response = {'subsystem': 'Archon', 'task_id': task_id, 'status': result.get('status'), 'result': result}
            self.channel.basic_publish(exchange='', routing_key='task_result_queue', body=json.dumps(response))

            self.logger.info(f"Goal [{task_id}] execution finished with status: {result.get('status')}")
        except Exception as e:
            self.logger.error(f"Error processing goal: {e}", exc_info=True)
        finally:
            ch.basic_ack(delivery_tag=method.delivery_tag)

    def on_result_received(self, ch, method, properties, body):
        self.logger.info(f"Received a worker result: {body.decode()}")
        ch.basic_ack(delivery_tag=method.delivery_tag)

    def start(self):
        self.channel.basic_consume(queue='archon_goals', on_message_callback=self.on_goal_received)
        self.channel.basic_consume(queue='task_result_queue', on_message_callback=self.on_result_received)
        self.logger.info("Archon Nexus consuming goals and results.")
        self.channel.start_consuming()

class TrinityNexusIntegration:
    """Trinity integration system for enhanced subsystem coordination."""
    
    def __init__(self, component_name: str):
        self.component = component_name
        self.trinity_state = {
            "existence": 0.33,
            "goodness": 0.33, 
            "truth": 0.34
        }
        self.validation_active = True
    
    def trinity_compute(self, operation, input_data):
        """Execute Trinity-enhanced computation with validation."""
        try:
            # Enhance input with Trinity context
            enhanced_data = {
                "original_data": input_data,
                "trinity_enhancement": self.trinity_state,
                "component": self.component,
                "validation_timestamp": time.time()
            }
            
            # Execute operation with enhancement
            result = operation(enhanced_data)
            
            # Validate Trinity coherence
            if self._validate_trinity_coherence(result):
                return result
            else:
                return {"status": "trinity_validation_failed", "component": self.component}
                
        except Exception as e:
            return {
                "status": "trinity_computation_error", 
                "error": str(e),
                "component": self.component
            }
    
    def _validate_trinity_coherence(self, result):
        """Validate computational result maintains Trinity coherence."""
        # Basic coherence checks
        if result is None:
            return False
        if isinstance(result, dict) and result.get("status") == "error":
            return False
        return True

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    rabbitmq_host = os.getenv("RABBITMQ_HOST", "rabbitmq")
    nexus = ArchonNexus(rabbitmq_host=rabbitmq_host)
    nexus.start()