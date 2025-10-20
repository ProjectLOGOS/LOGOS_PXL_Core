from dotenv import load_dotenv
load_dotenv()

# logos_agi_v1/services/keryx_api/gateway_service.py

import os
import pika
import json
import uuid
import logging
from flask import Flask, request, jsonify
from threading import Thread

# --- Basic Configuration ---
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - KERYX - %(message)s')

RABBITMQ_HOST = os.getenv('RABBITMQ_HOST', 'rabbitmq')
GOAL_QUEUE = 'goal_queue'

app = Flask(__name__)

# --- Connection Management ---
def get_rabbitmq_connection():
    """Establishes a connection to RabbitMQ."""
    try:
        connection = pika.BlockingConnection(pika.ConnectionParameters(host=RABBITMQ_HOST))
        logging.info("Successfully connected to RabbitMQ.")
        return connection
    except pika.exceptions.AMQPConnectionError as e:
        logging.error(f"Failed to connect to RabbitMQ: {e}")
        return None

# --- API Endpoints ---
@app.route('/submit_goal', methods=['POST'])
def submit_goal():
    """API endpoint to receive a new high-level goal."""
    if not request.json or 'goal_description' not in request.json:
        logging.warning("Received invalid submission: 'goal_description' missing.")
        return jsonify({'status': 'error', 'message': 'Missing "goal_description" in request body.'}), 400

    goal_data = request.json
    goal_id = str(uuid.uuid4())
    message = {
        'goal_id': goal_id,
        'goal_description': goal_data['goal_description'],
        'priority': goal_data.get('priority', 5),
        'status': 'submitted'
    }

    connection = get_rabbitmq_connection()
    if not connection:
        return jsonify({'status': 'error', 'message': 'Could not connect to the messaging backend.'}), 503

    try:
        channel = connection.channel()
        channel.queue_declare(queue=GOAL_QUEUE, durable=True)
        channel.basic_publish(
            exchange='',
            routing_key=GOAL_QUEUE,
            body=json.dumps(message),
            properties=pika.BasicProperties(delivery_mode=2)
        )
        logging.info(f"Published goal {goal_id} to {GOAL_QUEUE}")
        connection.close()
        return jsonify({'status': 'success', 'message': 'Goal submitted successfully.', 'goal_id': goal_id}), 202
    except Exception as e:
        logging.error(f"Error publishing goal {goal_id} to RabbitMQ: {e}")
        if connection and connection.is_open:
            connection.close()
        return jsonify({'status': 'error', 'message': 'An internal error occurred.'}), 500

@app.route('/health', methods=['GET'])
def health_check():
    """Simple health check endpoint."""
    return jsonify({'status': 'ok'}), 200

# --- Main Execution ---
if __name__ == '__main__':
    logging.info("Starting Keryx API Gateway service...")
    app.run(host='0.0.0.0', port=5000, debug=True)
