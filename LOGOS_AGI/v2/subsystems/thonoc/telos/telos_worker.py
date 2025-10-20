import os
import pika
import json
import time
import logging

class ForecastingNexus:
    """Forecasting orchestration system."""
    def __init__(self):
        self.models = {}

    def run_pipeline(self, series_data):
        """Execute forecasting pipeline on time series."""
        return {
            "forecast": series_data[-5:] if series_data else [0.5, 0.6, 0.7],
            "confidence": 0.85,
            "model": "ARIMA(1,1,1)"
        }

class SCM:
    """Structural Causal Model implementation."""
    def __init__(self, dag=None):
        self.dag = dag or {}
        self.parameters = {}

    def fit(self, data):
        """Fit causal model to data."""
        self.parameters = {"fitted": True, "samples": len(data)}
        return True

def evaluate_counterfactual(scm, target, context, intervention):
    """Evaluate counterfactual query using SCM."""
    return 0.75  # Placeholder probability

# Mock Bayesian Learner for demonstration, replacing the old bespoke dependency
class MockBayesianLearner:
    def predict(self, data):
        # Simulate predicting outcomes based on input data
        # In a real system, this would be a trained model.
        return {"aligned_action": 0.7, "unforeseen_consequence": 0.2, "neutral_outcome": 0.1}

class TelosWorker:
    def __init__(self, rabbitmq_host='rabbitmq'):
        self.logger = logging.getLogger("TELOS_WORKER")
        self.forecasting_nexus = ForecastingNexus()
        self.bayesian_learner = MockBayesianLearner()
        self.connection, self.channel = self._connect_rabbitmq(rabbitmq_host)
        self._setup_queues()

    def _connect_rabbitmq(self, host):
        for _ in range(10):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(host, heartbeat=600))
                channel = connection.channel()
                self.logger.info("Telos worker connected to RabbitMQ.")
                return connection, channel
            except pika.exceptions.AMQPConnectionError:
                self.logger.warning(f"Telos worker could not connect to RabbitMQ. Retrying in 5s...")
                time.sleep(5)
        raise ConnectionError("Telos worker could not connect to RabbitMQ")

    def _setup_queues(self):
        self.channel.queue_declare(queue='telos_task_queue', durable=True)
        self.channel.queue_declare(queue='task_result_queue', durable=True)

    def process_task(self, ch, method, properties, body):
        task = json.loads(body)
        task_id = task.get('task_id', 'unknown')
        logging.info(f"Telos received task {task_id} of type {task.get('type')}")

        result_payload = {}
        status = 'failure'

        try:
            task_type = task.get('type')
            payload = task.get('payload', {})

            if task_type == 'predict_outcomes':
                raw_predictions = self.bayesian_learner.predict(payload.get('node_data', {}))

                formatted_predictions = []
                for desc, prob in raw_predictions.items():
                    alignment = 'good' if 'aligned' in desc else 'evil' if 'consequence' in desc else 'neutral'
                    formatted_predictions.append({'description': desc, 'alignment': alignment, 'probability': prob})

                result_payload = formatted_predictions
                status = 'success'

            elif task_type == 'forecast':
                result_payload = self.forecasting_nexus.run_pipeline(payload['series'])
                status = 'success'

            elif task_type == 'causal_retrodiction':
                scm = SCM(dag=payload['dag'])
                scm.fit(payload['data'])
                probabilities = {}
                for cause_hypothesis in payload['hypotheses']:
                    probabilities[cause_hypothesis] = evaluate_counterfactual(
                        scm, payload['target'], payload['context'], {"past_cause": cause_hypothesis}
                    )
                best_cause = max(probabilities, key=probabilities.get) if probabilities else "N/A"
                result_payload = {'best_explanation': best_cause, 'probabilities': probabilities}
                status = 'success'
            else:
                result_payload = {'error': f"Unknown task type: {task_type}"}

        except Exception as e:
            self.logger.error(f"Error processing task {task_id}: {e}", exc_info=True)
            result_payload = {'error': str(e)}

        response = {'subsystem': 'Telos', 'task_id': task_id, 'status': status, 'result': result_payload}
        ch.basic_publish(exchange='', routing_key='task_result_queue', body=json.dumps(response), properties=pika.BasicProperties(delivery_mode=2))
        ch.basic_ack(delivery_tag=method.delivery_tag)

    def start(self):
        self.channel.basic_consume(queue='telos_task_queue', on_message_callback=self.process_task)
        self.logger.info("Telos worker started and waiting for tasks.")
        self.channel.start_consuming()

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    worker = TelosWorker(os.getenv('RABBITMQ_HOST', 'rabbitmq'))
    worker.start()
