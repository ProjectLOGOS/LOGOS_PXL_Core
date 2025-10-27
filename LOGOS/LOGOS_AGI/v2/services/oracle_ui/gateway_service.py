from flask import Flask, request, jsonify
import pika
import json
import uuid
import os
import logging

logging.basicConfig(level=logging.INFO, format="%(asctime)s - KERYX - %(levelname)s - %(message)s")

app = Flask(__name__)
RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")


def publish_goal(goal_data):
    try:
        connection = pika.BlockingConnection(pika.ConnectionParameters(host=RABBITMQ_HOST))
        channel = connection.channel()
        channel.queue_declare(queue="logos_nexus_requests", durable=True)
        channel.basic_publish(
            exchange="",
            routing_key="logos_nexus_requests",
            body=json.dumps(goal_data),
            properties=pika.BasicProperties(delivery_mode=2),
        )
        connection.close()
        return True
    except Exception as e:
        app.logger.error(f"Error publishing to RabbitMQ: {e}")
        return False


@app.route("/submit_goal", methods=["POST"])
def submit_goal():
    data = request.get_json()
    if not data or "goal_description" not in data:
        return jsonify({"error": "'goal_description' is required."}), 400

    message = {"query": data["goal_description"], "task_id": str(uuid.uuid4())}
    if publish_goal(message):
        return jsonify({"status": "Goal submitted.", "task_id": message["task_id"]}), 202
    else:
        return jsonify({"error": "Failed to communicate with AGI system."}), 503


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
