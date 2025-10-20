# logos_agi_v1/subsystems/tetragnos/tetragnos_worker.py

"""
TETRAGNOS Pattern Recognition Worker

The Pattern Recognizer - handles natural language processing, semantic clustering,
feature extraction, and translation between natural language and computational formats.

Responsibilities:
- Text clustering and pattern recognition
- Feature extraction from unstructured data
- Natural language to formal language translation
- Semantic similarity analysis
- Dimensional reduction and classification
"""

import os
import sys
import json
import time
import logging
import signal
import uuid
from typing import Dict, List, Any, Optional, Tuple
from datetime import datetime

# RabbitMQ and messaging
import pika

# Core LOGOS imports
try:
    from core.cognitive.feature_extraction import FeatureExtractor
    from core.ml.clustering import ClusterAnalyzer
    from core.nlp.translation import TranslationEngine
    from core.data_structures import TaskDescriptor, OperationResult
except ImportError:
    # Fallback implementations if core modules aren't available
    pass

# ML and NLP libraries with fallbacks
try:
    import numpy as np
    from sklearn.feature_extraction.text import TfidfVectorizer
    from sklearn.cluster import KMeans, DBSCAN
    from sklearn.metrics.pairwise import cosine_similarity
    from sklearn.decomposition import PCA
    from sentence_transformers import SentenceTransformer
    SKLEARN_AVAILABLE = True
    SENTENCE_TRANSFORMERS_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False
    SENTENCE_TRANSFORMERS_AVAILABLE = False

# Configuration
SUBSYSTEM_NAME = "TETRAGNOS"
RABBITMQ_HOST = os.getenv('RABBITMQ_HOST', 'rabbitmq')
RABBITMQ_PORT = int(os.getenv('RABBITMQ_PORT', '5672'))
TASK_QUEUE = 'tetragnos_task_queue'
RESULT_QUEUE = 'task_result_queue'

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f'%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('/app/logs/tetragnos_worker.log', mode='a')
    ]
)

class TetragnosCoreEngine:
    """
    Core logic engine for TETRAGNOS subsystem.
    Encapsulates pattern recognition, feature extraction, and ML operations.
    """
    
    def __init__(self):
        self.logger = logging.getLogger("TETRAGNOS_CORE")
        self.worker_id = f"tetragnos_{uuid.uuid4().hex[:8]}"
        
        # Initialize ML components
        self._initialize_ml_components()
        
        # Pattern cache for performance optimization
        self.pattern_cache = {}
        self.feature_cache = {}
        
        self.logger.info(f"TETRAGNOS Core Engine initialized with worker ID: {self.worker_id}")
    
    def _initialize_ml_components(self):
        """Initialize machine learning and NLP components."""
        try:
            if SKLEARN_AVAILABLE:
                self.tfidf_vectorizer = TfidfVectorizer(
                    max_features=1000,
                    stop_words='english',
                    ngram_range=(1, 2)
                )
                self.kmeans_clusterer = KMeans(n_clusters=5, random_state=42)
                self.dbscan_clusterer = DBSCAN(eps=0.5, min_samples=2)
                self.pca_reducer = PCA(n_components=50)
                self.logger.info("Scikit-learn components initialized")
            
            if SENTENCE_TRANSFORMERS_AVAILABLE:
                self.sentence_transformer = SentenceTransformer('all-MiniLM-L6-v2')
                self.logger.info("Sentence transformer model loaded")
            
        except Exception as e:
            self.logger.warning(f"ML component initialization failed: {e}")
            # Create fallback implementations
            self._create_fallback_components()
    
    def _create_fallback_components(self):
        """Create simple fallback implementations when ML libraries aren't available."""
        self.logger.info("Creating fallback ML components")
        
        class FallbackVectorizer:
            def fit_transform(self, texts):
                # Simple word counting vectorization
                vocab = set()
                for text in texts:
                    vocab.update(text.lower().split())
                vocab = list(vocab)
                
                vectors = []
                for text in texts:
                    words = text.lower().split()
                    vector = [words.count(word) for word in vocab]
                    vectors.append(vector)
                return np.array(vectors) if 'numpy' in sys.modules else vectors
        
        self.tfidf_vectorizer = FallbackVectorizer()
    
    def execute(self, task_type: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """
        Main execution entry point for TETRAGNOS tasks.
        Routes tasks to appropriate processing methods.
        """
        try:
            self.logger.info(f"Executing task type: {task_type}")
            
            if task_type == 'cluster_texts':
                return self._cluster_texts(payload)
            elif task_type == 'translate_text':
                return self._translate_text(payload)
            elif task_type == 'extract_features':
                return self._extract_features(payload)
            elif task_type == 'analyze_patterns':
                return self._analyze_patterns(payload)
            elif task_type == 'semantic_similarity':
                return self._compute_semantic_similarity(payload)
            else:
                return {
                    'status': 'error',
                    'error': f'Unknown task type: {task_type}',
                    'supported_tasks': ['cluster_texts', 'translate_text', 'extract_features', 'analyze_patterns', 'semantic_similarity']
                }
                
        except Exception as e:
            self.logger.error(f"Error executing task {task_type}: {e}", exc_info=True)
            return {
                'status': 'error',
                'error': str(e),
                'task_type': task_type
            }
    
    def _cluster_texts(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Perform text clustering analysis."""
        texts = payload.get('texts', [])
        method = payload.get('method', 'kmeans')
        n_clusters = payload.get('n_clusters', 5)
        
        if not texts:
            return {'status': 'error', 'error': 'No texts provided for clustering'}
        
        try:
            # Vectorize texts
            if hasattr(self, 'sentence_transformer') and SENTENCE_TRANSFORMERS_AVAILABLE:
                # Use sentence transformers for better semantic representation
                embeddings = self.sentence_transformer.encode(texts)
            else:
                # Fall back to TF-IDF
                embeddings = self.tfidf_vectorizer.fit_transform(texts)
                if hasattr(embeddings, 'toarray'):
                    embeddings = embeddings.toarray()
            
            # Perform clustering
            if method == 'kmeans' and SKLEARN_AVAILABLE:
                clusterer = KMeans(n_clusters=min(n_clusters, len(texts)), random_state=42)
                cluster_labels = clusterer.fit_predict(embeddings)
            elif method == 'dbscan' and SKLEARN_AVAILABLE:
                clusterer = DBSCAN(eps=0.5, min_samples=2)
                cluster_labels = clusterer.fit_predict(embeddings)
            else:
                # Simple fallback clustering
                cluster_labels = [i % n_clusters for i in range(len(texts))]
            
            # Organize results
            clusters = {}
            for i, label in enumerate(cluster_labels):
                if label not in clusters:
                    clusters[label] = []
                clusters[label].append({
                    'text': texts[i],
                    'index': i
                })
            
            # Calculate cluster statistics
            cluster_stats = {}
            for label, items in clusters.items():
                cluster_stats[label] = {
                    'size': len(items),
                    'representative_text': items[0]['text'],  # First text as representative
                    'coherence_score': len(items) / len(texts)  # Simple coherence metric
                }
            
            return {
                'status': 'success',
                'method': method,
                'clusters': clusters,
                'cluster_statistics': cluster_stats,
                'total_clusters': len(clusters),
                'total_texts': len(texts)
            }
            
        except Exception as e:
            return {
                'status': 'error',
                'error': f'Clustering failed: {str(e)}',
                'method': method
            }
    
    def _translate_text(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Translate between natural language and formal representations."""
        text = payload.get('text', '')
        source_format = payload.get('source_format', 'natural_language')
        target_format = payload.get('target_format', 'logical_form')
        
        try:
            if source_format == 'natural_language' and target_format == 'logical_form':
                # Convert natural language to logical form
                logical_form = self._natural_to_logical(text)
                return {
                    'status': 'success',
                    'original_text': text,
                    'translated_form': logical_form,
                    'translation_type': 'natural_to_logical',
                    'confidence': 0.85
                }
            
            elif source_format == 'logical_form' and target_format == 'natural_language':
                # Convert logical form to natural language
                natural_text = self._logical_to_natural(text)
                return {
                    'status': 'success',
                    'original_form': text,
                    'translated_text': natural_text,
                    'translation_type': 'logical_to_natural',
                    'confidence': 0.80
                }
            
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported translation: {source_format} -> {target_format}',
                    'supported_translations': [
                        'natural_language -> logical_form',
                        'logical_form -> natural_language'
                    ]
                }
                
        except Exception as e:
            return {
                'status': 'error',
                'error': f'Translation failed: {str(e)}',
                'source_format': source_format,
                'target_format': target_format
            }
    
    def _natural_to_logical(self, text: str) -> str:
        """Convert natural language to logical form."""
        # Simplified natural language to logic translation
        text = text.lower().strip()
        
        # Basic pattern matching for common logical structures
        if 'all' in text and 'are' in text:
            # Universal quantification pattern
            return f"∀x: {text.replace('all', '').replace('are', '→').strip()}"
        elif 'some' in text or 'exists' in text:
            # Existential quantification pattern
            return f"∃x: {text.replace('some', '').replace('exists', '').strip()}"
        elif 'if' in text and 'then' in text:
            # Implication pattern
            parts = text.split('if')[1].split('then')
            antecedent = parts[0].strip() if len(parts) > 0 else ''
            consequent = parts[1].strip() if len(parts) > 1 else ''
            return f"({antecedent} → {consequent})"
        elif 'not' in text:
            # Negation pattern
            return f"¬({text.replace('not', '').strip()})"
        else:
            # Default propositional form
            return f"P({text.replace(' ', '_')})"
    
    def _logical_to_natural(self, logical_form: str) -> str:
        """Convert logical form to natural language."""
        # Simplified logic to natural language translation
        form = logical_form.strip()
        
        if form.startswith('∀'):
            return f"For all x, {form[2:].replace('→', 'implies').replace(':', ', ')}"
        elif form.startswith('∃'):
            return f"There exists an x such that {form[2:].replace(':', ', ')}"
        elif '→' in form:
            parts = form.replace('(', '').replace(')', '').split('→')
            antecedent = parts[0].strip() if len(parts) > 0 else ''
            consequent = parts[1].strip() if len(parts) > 1 else ''
            return f"If {antecedent}, then {consequent}"
        elif form.startswith('¬'):
            return f"It is not the case that {form[1:].replace('(', '').replace(')', '')}"
        else:
            return form.replace('_', ' ').replace('P(', '').replace(')', '')
    
    def _extract_features(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Extract semantic features from text or data."""
        data = payload.get('data', [])
        feature_type = payload.get('feature_type', 'semantic')
        
        try:
            if feature_type == 'semantic' and isinstance(data, list) and all(isinstance(item, str) for item in data):
                # Extract semantic features from text
                if hasattr(self, 'sentence_transformer'):
                    features = self.sentence_transformer.encode(data)
                    feature_names = [f"semantic_dim_{i}" for i in range(features.shape[1])]
                else:
                    # Fallback to simple text features
                    features = []
                    for text in data:
                        words = text.lower().split()
                        features.append([
                            len(words),  # word count
                            len(text),   # character count
                            len(set(words)),  # unique words
                            sum(1 for word in words if len(word) > 6)  # complex words
                        ])
                    feature_names = ['word_count', 'char_count', 'unique_words', 'complex_words']
                
                return {
                    'status': 'success',
                    'features': features.tolist() if hasattr(features, 'tolist') else features,
                    'feature_names': feature_names,
                    'feature_dimensions': len(feature_names),
                    'data_points': len(data)
                }
            
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported feature extraction for type: {feature_type}',
                    'supported_types': ['semantic']
                }
                
        except Exception as e:
            return {
                'status': 'error',
                'error': f'Feature extraction failed: {str(e)}',
                'feature_type': feature_type
            }
    
    def _analyze_patterns(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Analyze patterns in data using various techniques."""
        data = payload.get('data', [])
        analysis_type = payload.get('analysis_type', 'frequency')
        
        try:
            if analysis_type == 'frequency':
                # Frequency analysis
                if isinstance(data, list) and all(isinstance(item, str) for item in data):
                    # Text frequency analysis
                    word_freq = {}
                    for text in data:
                        words = text.lower().split()
                        for word in words:
                            word_freq[word] = word_freq.get(word, 0) + 1
                    
                    # Sort by frequency
                    sorted_freq = sorted(word_freq.items(), key=lambda x: x[1], reverse=True)
                    
                    return {
                        'status': 'success',
                        'analysis_type': 'frequency',
                        'word_frequencies': dict(sorted_freq[:20]),  # Top 20
                        'total_unique_words': len(word_freq),
                        'total_words': sum(word_freq.values()),
                        'most_common': sorted_freq[0] if sorted_freq else None
                    }
                
                else:
                    # General frequency analysis
                    item_freq = {}
                    for item in data:
                        item_freq[str(item)] = item_freq.get(str(item), 0) + 1
                    
                    sorted_freq = sorted(item_freq.items(), key=lambda x: x[1], reverse=True)
                    
                    return {
                        'status': 'success',
                        'analysis_type': 'frequency',
                        'item_frequencies': dict(sorted_freq),
                        'total_unique_items': len(item_freq),
                        'total_items': len(data),
                        'most_common': sorted_freq[0] if sorted_freq else None
                    }
            
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported analysis type: {analysis_type}',
                    'supported_types': ['frequency']
                }
                
        except Exception as e:
            return {
                'status': 'error',
                'error': f'Pattern analysis failed: {str(e)}',
                'analysis_type': analysis_type
            }
    
    def _compute_semantic_similarity(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Compute semantic similarity between texts."""
        texts = payload.get('texts', [])
        comparison_type = payload.get('comparison_type', 'pairwise')
        
        try:
            if len(texts) < 2:
                return {
                    'status': 'error',
                    'error': 'At least 2 texts required for similarity computation'
                }
            
            # Get embeddings
            if hasattr(self, 'sentence_transformer'):
                embeddings = self.sentence_transformer.encode(texts)
                similarities = cosine_similarity(embeddings)
            else:
                # Fallback: simple word overlap similarity
                similarities = []
                for i, text1 in enumerate(texts):
                    row = []
                    words1 = set(text1.lower().split())
                    for j, text2 in enumerate(texts):
                        words2 = set(text2.lower().split())
                        if len(words1) == 0 or len(words2) == 0:
                            similarity = 0.0
                        else:
                            intersection = len(words1.intersection(words2))
                            union = len(words1.union(words2))
                            similarity = intersection / union if union > 0 else 0.0
                        row.append(similarity)
                    similarities.append(row)
            
            if comparison_type == 'pairwise':
                # Return full similarity matrix
                return {
                    'status': 'success',
                    'similarity_matrix': similarities.tolist() if hasattr(similarities, 'tolist') else similarities,
                    'texts': texts,
                    'comparison_type': 'pairwise',
                    'most_similar_pair': self._find_most_similar_pair(similarities, texts)
                }
            
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported comparison type: {comparison_type}',
                    'supported_types': ['pairwise']
                }
                
        except Exception as e:
            return {
                'status': 'error',
                'error': f'Similarity computation failed: {str(e)}',
                'comparison_type': comparison_type
            }
    
    def _find_most_similar_pair(self, similarity_matrix, texts):
        """Find the most similar pair of texts."""
        max_similarity = 0
        best_pair = None
        
        for i in range(len(texts)):
            for j in range(i + 1, len(texts)):
                if hasattr(similarity_matrix, 'shape'):
                    similarity = similarity_matrix[i][j]
                else:
                    similarity = similarity_matrix[i][j]
                
                if similarity > max_similarity:
                    max_similarity = similarity
                    best_pair = {
                        'text1': texts[i],
                        'text2': texts[j],
                        'similarity': float(similarity),
                        'indices': [i, j]
                    }
        
        return best_pair


class TetragnosWorker:
    """
    Main TETRAGNOS worker class that handles RabbitMQ communication
    and orchestrates the core engine operations.
    """
    
    def __init__(self):
        self.logger = logging.getLogger("TETRAGNOS_WORKER")
        self.core_engine = TetragnosCoreEngine()
        self.connection = None
        self.channel = None
        self.is_running = False
        
        # Setup graceful shutdown handling
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
        
        self._connect_to_rabbitmq()
        self.logger.info("TETRAGNOS Worker initialized successfully")
    
    def _connect_to_rabbitmq(self):
        """Establish connection to RabbitMQ with retry logic."""
        max_retries = 10
        retry_delay = 5
        
        for attempt in range(1, max_retries + 1):
            try:
                credentials = pika.PlainCredentials('guest', 'guest')
                parameters = pika.ConnectionParameters(
                    host=RABBITMQ_HOST,
                    port=RABBITMQ_PORT,
                    credentials=credentials,
                    heartbeat=600,
                    blocked_connection_timeout=300
                )
                
                self.connection = pika.BlockingConnection(parameters)
                self.channel = self.connection.channel()
                
                self._setup_queues()
                
                self.logger.info(f"Successfully connected to RabbitMQ at {RABBITMQ_HOST}:{RABBITMQ_PORT}")
                return
                
            except pika.exceptions.AMQPConnectionError as e:
                self.logger.warning(f"Attempt {attempt}/{max_retries}: Failed to connect to RabbitMQ: {e}")
                if attempt < max_retries:
                    self.logger.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                else:
                    self.logger.error("Could not connect to RabbitMQ after all attempts. Exiting.")
                    sys.exit(1)
            except Exception as e:
                self.logger.error(f"Unexpected error connecting to RabbitMQ: {e}")
                sys.exit(1)
    
    def _setup_queues(self):
        """Declare and configure queues."""
        try:
            self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
            self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)
            self.channel.basic_qos(prefetch_count=1)
            
            self.logger.info(f"Queues configured: {TASK_QUEUE} -> {RESULT_QUEUE}")
            
        except Exception as e:
            self.logger.error(f"Failed to setup queues: {e}")
            raise
    
    def process_task(self, ch, method, properties, body):
        """Process incoming task messages."""
        start_time = time.time()
        task_id = "unknown"
        
        try:
            # Parse message
            task = json.loads(body.decode('utf-8'))
            task_id = task.get('task_id', f'tetragnos_{int(time.time() * 1000)}')
            workflow_id = task.get('workflow_id', 'unknown')
            task_type = task.get('type', 'unknown')
            payload = task.get('payload', {})
            
            self.logger.info(f"Processing task {task_id} (workflow: {workflow_id}) of type: {task_type}")
            
            # Execute task using core engine
            result_payload = self.core_engine.execute(task_type, payload)
            status = 'success' if result_payload.get('status') == 'success' else 'failure'
            
            processing_time = time.time() - start_time
            
            # Prepare response
            response = {
                'subsystem': SUBSYSTEM_NAME,
                'task_id': task_id,
                'workflow_id': workflow_id,
                'status': status,
                'result': result_payload,
                'processing_time': processing_time,
                'timestamp': datetime.utcnow().isoformat()
            }
            
            # Publish result
            self.channel.basic_publish(
                exchange='',
                routing_key=RESULT_QUEUE,
                body=json.dumps(response),
                properties=pika.BasicProperties(
                    delivery_mode=2,  # Make message persistent
                    correlation_id=task_id
                )
            )
            
            self.logger.info(f"Task {task_id} completed in {processing_time:.3f}s with status: {status}")
            
        except json.JSONDecodeError as e:
            self.logger.error(f"Invalid JSON in task {task_id}: {e}")
            self._send_error_response(task_id, f"Invalid JSON: {str(e)}")
        except Exception as e:
            self.logger.error(f"Error processing task {task_id}: {e}", exc_info=True)
            self._send_error_response(task_id, str(e))
        finally:
            # Always acknowledge the message
            try:
                ch.basic_ack(delivery_tag=method.delivery_tag)
            except Exception as e:
                self.logger.error(f"Failed to acknowledge message: {e}")
    
    def _send_error_response(self, task_id: str, error_message: str):
        """Send error response for failed tasks."""
        try:
            error_response = {
                'subsystem': SUBSYSTEM_NAME,
                'task_id': task_id,
                'status': 'error',
                'error': error_message,
                'timestamp': datetime.utcnow().isoformat()
            }
            
            self.channel.basic_publish(
                exchange='',
                routing_key=RESULT_QUEUE,
                body=json.dumps(error_response),
                properties=pika.BasicProperties(correlation_id=task_id)
            )
        except Exception as e:
            self.logger.error(f"Failed to send error response: {e}")
    
    def start_consuming(self):
        """Start consuming messages from the task queue."""
        try:
            self.channel.basic_consume(
                queue=TASK_QUEUE,
                on_message_callback=self.process_task
            )
            
            self.is_running = True
            self.logger.info(f"{SUBSYSTEM_NAME} Worker started and listening on queue: {TASK_QUEUE}")
            
            self.channel.start_consuming()
            
        except KeyboardInterrupt:
            self.logger.info("Received interrupt signal, shutting down gracefully...")
            self._shutdown()
        except Exception as e:
            self.logger.error(f"Error in consumer loop: {e}")
            self._shutdown()
    
    def _signal_handler(self, signum, frame):
        """Handle system signals for graceful shutdown."""
        self.logger.info(f"Received signal {signum}, initiating shutdown...")
        self._shutdown()
    
    def _shutdown(self):
        """Gracefully shutdown the worker."""
        if self.is_running:
            self.is_running = False
            
            # Stop consuming messages
            if self.channel and self.channel.is_open:
                try:
                    self.channel.stop_consuming()
                    self.logger.info("Stopped consuming messages")
                except Exception as e:
                    self.logger.error(f"Error stopping consumer: {e}")
            
            # Close connections
            if self.connection and self.connection.is_open:
                try:
                    self.connection.close()
                    self.logger.info("RabbitMQ connection closed")
                except Exception as e:
                    self.logger.error(f"Error closing connection: {e}")
            
            self.logger.info("TETRAGNOS Worker shutdown complete")


def main():
    """Main entry point for the TETRAGNOS worker."""
    try:
        worker = TetragnosWorker()
        worker.start_consuming()
    except Exception as e:
        logging.error(f"Failed to start TETRAGNOS worker: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()