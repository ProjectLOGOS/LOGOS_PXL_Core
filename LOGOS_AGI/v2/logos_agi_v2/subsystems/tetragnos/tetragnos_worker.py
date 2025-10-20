import os
import pika
import json
import time
import logging
import numpy as np
from .ml_components import FeatureExtractor, ClusterAnalyzer

# --- Worker-Specific Configuration ---
SUBSYSTEM_NAME = "Tetragnos"
RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
TASK_QUEUE = "tetragnos_task_queue"
RESULT_QUEUE = "task_result_queue"

# --- Logging Setup ---
logging.basicConfig(
    level=logging.INFO,
    format=f"%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s",
)


class TetragnosCore:
    """
    This class encapsulates the core logic of the Tetragnos subsystem,
    acting as the internal "nexus" that the worker service exposes.
    """

    def __init__(self):
        self.logger = logging.getLogger("TETRAGNOS_CORE")
        self.feature_extractor = FeatureExtractor()
        self.cluster_analyzer = ClusterAnalyzer()
        self.logger.info("Tetragnos Core logic engine initialized.")

    def execute(self, task_type, payload):
        """
        Main execution entry point for Tetragnos logic.
        Routes tasks to the appropriate internal method.
        """
        if task_type == "cluster_texts":
            return self.perform_text_clustering(payload)
        else:
            raise ValueError(f"Unknown task type for Tetragnos: {task_type}")

    def perform_text_clustering(self, payload):
        """
        Performs semantic feature extraction and clustering on a list of texts.
        This is the primary function of Tetragnos.
        """
        texts = payload.get("texts")
        if not texts or not isinstance(texts, list):
            raise ValueError(
                "Payload for 'cluster_texts' must contain a non-empty list of strings in the 'texts' key."
            )

        self.logger.info(f"Performing clustering on {len(texts)} documents.")

        # 1. Convert texts to semantic vector embeddings
        features = self.feature_extractor.fit_transform(texts)

        # 2. Find clusters and patterns in the embedding space
        cluster_results = self.cluster_analyzer.fit(features)

        self.logger.info(
            f"Clustering complete. Found {len(set(cluster_results['labels'])) - 1} clusters."
        )
        return cluster_results


class TetragnosWorker:
    def __init__(self, rabbitmq_host="rabbitmq"):
        self.logger = logging.getLogger("TETRAGNOS_WORKER")
        self.core_logic = TetragnosCore()
        self.connection, self.channel = self._connect_rabbitmq(rabbitmq_host)
        self._setup_queues()

    def _connect_rabbitmq(self, host):
        for _ in range(10):
            try:
                connection = pika.BlockingConnection(pika.ConnectionParameters(host, heartbeat=600))
                channel = connection.channel()
                self.logger.info("Tetragnos worker connected to RabbitMQ.")
                return connection, channel
            except pika.exceptions.AMQPConnectionError:
                self.logger.warning(
                    f"Tetragnos worker could not connect to RabbitMQ. Retrying in 5s..."
                )
                time.sleep(5)
        raise ConnectionError("Tetragnos worker could not connect to RabbitMQ")

    def _setup_queues(self):
        self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
        self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)

    def process_task(self, ch, method, properties, body):
        task = json.loads(body)
        task_id = task.get("task_id", "unknown")
        workflow_id = task.get("workflow_id", "unknown")
        logging.info(
            f"Received task {task_id} for workflow {workflow_id} of type {task.get('type')}"
        )

        result_payload = {}
        status = "failure"

        try:
            task_type = task.get("type")
            payload = task.get("payload", {})

            # Delegate the task to the core logic engine
            result_payload = self.core_logic.execute(task_type, payload)
            status = "success"
        except Exception as e:
            self.logger.error(f"Error processing task {task_id}: {e}", exc_info=True)
            result_payload = {"error": str(e)}

        response = {
            "subsystem": SUBSYSTEM_NAME,
            "task_id": task_id,
            "workflow_id": workflow_id,
            "status": status,
            "result": result_payload,
        }

        self.channel.basic_publish(
            exchange="",
            routing_key=RESULT_QUEUE,
            body=json.dumps(response),
            properties=pika.BasicProperties(delivery_mode=2),
        )
        ch.basic_ack(delivery_tag=method.delivery_tag)
        self.logger.info(f"Finished and published result for task {task_id}.")

    def start(self):
        self.channel.basic_qos(prefetch_count=1)
        self.channel.basic_consume(queue=TASK_QUEUE, on_message_callback=self.process_task)
        self.logger.info(
            f"{SUBSYSTEM_NAME} worker started and is waiting for tasks on queue '{TASK_QUEUE}'."
        )
        self.channel.start_consuming()


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    worker = TetragnosWorker(os.getenv("RABBITMQ_HOST", "rabbitmq"))
    worker.start()

    """Enhanced TETRAGNOS Worker with ML Components Integration

Provides complete ML pipeline for pattern recognition, semantic clustering,
and feature extraction with Trinity validation.

Dependencies: pika, json, logging, sklearn, sentence_transformers
"""

import os
import pika
import json
import time
import logging
from typing import Dict, Any, List, Optional


# Missing ML Components (CREATE THESE)
class FeatureExtractor:
    """Semantic feature extraction using sentence transformers."""

    def __init__(self):
        try:
            from sentence_transformers import SentenceTransformer

            self.model = SentenceTransformer("all-MiniLM-L6-v2")
            self.fitted = False
        except ImportError:
            self.model = None
            logging.warning("SentenceTransformers not available - using fallback")

    def fit_transform(self, texts: List[str]) -> Dict[str, Any]:
        """Extract semantic features from text corpus."""
        if self.model:
            embeddings = self.model.encode(texts)
            return {
                "embeddings": embeddings.tolist(),
                "feature_count": embeddings.shape[1],
                "document_count": len(texts),
            }
        else:
            # Fallback: TF-IDF features
            from sklearn.feature_extraction.text import TfidfVectorizer

            vectorizer = TfidfVectorizer(max_features=384)
            features = vectorizer.fit_transform(texts)
            return {
                "embeddings": features.toarray().tolist(),
                "feature_count": features.shape[1],
                "document_count": len(texts),
            }


class ClusterAnalyzer:
    """Semantic clustering with pattern detection."""

    def __init__(self):
        from sklearn.cluster import KMeans
        from sklearn.metrics import silhouette_score

        self.kmeans = None
        self.optimal_k = None

    def fit(self, features: Dict[str, Any]) -> Dict[str, Any]:
        """Perform clustering with optimal k detection."""
        import numpy as np
        from sklearn.cluster import KMeans

        embeddings = np.array(features["embeddings"])
        n_docs = len(embeddings)

        # Determine optimal cluster count
        max_k = min(10, n_docs // 2) if n_docs > 4 else 2
        best_score = -1
        best_k = 2

        for k in range(2, max_k + 1):
            kmeans = KMeans(n_clusters=k, random_state=42)
            labels = kmeans.fit_predict(embeddings)
            score = silhouette_score(embeddings, labels)
            if score > best_score:
                best_score = score
                best_k = k

        # Final clustering with optimal k
        self.kmeans = KMeans(n_clusters=best_k, random_state=42)
        labels = self.kmeans.fit_predict(embeddings)

        return {
            "labels": labels.tolist(),
            "cluster_centers": self.kmeans.cluster_centers_.tolist(),
            "cluster_count": best_k,
            "silhouette_score": best_score,
            "inertia": self.kmeans.inertia_,
        }


# ENHANCED ALIGNMENT PROTOCOL
class TetragnosAlignmentProtocol:
    """Content safety and pattern recognition validation."""

    def __init__(self):
        self.forbidden_patterns = [
            "ignore previous instructions",
            "generate harmful",
            "bypass safety",
            "malicious content",
        ]
        self.safety_threshold = 0.8

    def validate_input(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Validate input safety and appropriateness."""
        texts = payload.get("texts", [])
        if not isinstance(texts, list):
            return {"valid": False, "reason": "Invalid input format"}

        for text in texts:
            if any(pattern in text.lower() for pattern in self.forbidden_patterns):
                return {"valid": False, "reason": "Forbidden pattern detected"}

        return {"valid": True, "reason": "Input validation passed"}

    def validate_output(self, result: Dict[str, Any]) -> Dict[str, Any]:
        """Validate clustering output for safety concerns."""
        labels = result.get("labels", [])
        cluster_count = result.get("cluster_count", 0)

        # Check for suspicious clustering patterns
        if cluster_count == 1:
            return {"valid": False, "reason": "Suspicious clustering - all documents identical"}

        # Check silhouette score for quality
        score = result.get("silhouette_score", 0)
        if score < 0.1:
            return {"valid": False, "reason": "Poor clustering quality"}

        return {"valid": True, "reason": "Output validation passed"}
