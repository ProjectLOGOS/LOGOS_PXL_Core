#!/usr/bin/env python3
"""TETRAGNOS Advanced Pattern Recognition Worker

High-performance NLP worker using SentenceTransformers and scikit-learn for
sophisticated pattern recognition, semantic analysis, and feature extraction.

Core Capabilities:
- Advanced semantic embeddings via SentenceTransformers
- Sophisticated clustering using DBSCAN and hierarchical methods
- Multi-dimensional feature extraction and analysis
- Real-time pattern recognition and classification

Dependencies: sentence_transformers, sklearn, numpy, pandas
"""

import os
import sys
import json
import time
import logging
import signal
import uuid
from typing import Dict, List, Any, Optional, Tuple, Union
from datetime import datetime
import threading
from concurrent.futures import ThreadPoolExecutor

# RabbitMQ messaging
import pika

# External libraries for advanced ML capabilities
import numpy as np
import pandas as pd
from sentence_transformers import SentenceTransformer
from sklearn.cluster import DBSCAN, AgglomerativeClustering, KMeans
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity
from sklearn.decomposition import PCA, UMAP
from sklearn.manifold import TSNE
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import Pipeline

# Configuration
SUBSYSTEM_NAME = "TETRAGNOS"
RABBITMQ_HOST = os.getenv('RABBITMQ_HOST', 'rabbitmq')
RABBITMQ_PORT = int(os.getenv('RABBITMQ_PORT', '5672'))
TASK_QUEUE = 'tetragnos_task_queue'
RESULT_QUEUE = 'task_result_queue'

# Model configuration
DEFAULT_MODEL = 'all-MiniLM-L6-v2'
EMBEDDING_CACHE_SIZE = 10000
MAX_BATCH_SIZE = 32

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f'%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('/app/logs/tetragnos_worker.log', mode='a')
    ]
)

class AdvancedSemanticEngine:
    """High-performance semantic analysis engine using SentenceTransformers."""
    
    def __init__(self, model_name: str = DEFAULT_MODEL):
        """Initialize semantic engine with specified transformer model.
        
        Args:
            model_name: HuggingFace model identifier for SentenceTransformer
        """
        self.logger = logging.getLogger("SEMANTIC_ENGINE")
        self.model_name = model_name
        self._model = None
        self.embedding_cache = {}
        self.cache_hits = 0
        self.cache_misses = 0
        
    def _ensure_model_loaded(self):
        """Lazy loading of SentenceTransformer model for memory efficiency."""
        if self._model is None:
            self.logger.info(f"Loading SentenceTransformer model: {self.model_name}")
            self._model = SentenceTransformer(self.model_name)
            self.logger.info("Model loaded successfully")
    
    def encode_texts(self, texts: List[str], batch_size: int = MAX_BATCH_SIZE) -> np.ndarray:
        """Generate semantic embeddings for text collection.
        
        Args:
            texts: Collection of text strings for encoding
            batch_size: Processing batch size for memory optimization
            
        Returns:
            Dense embedding matrix (n_texts, embedding_dim)
        """
        self._ensure_model_loaded()
        
        # Check cache for existing embeddings
        uncached_texts = []
        cached_embeddings = {}
        
        for i, text in enumerate(texts):
            text_hash = hash(text)
            if text_hash in self.embedding_cache:
                cached_embeddings[i] = self.embedding_cache[text_hash]
                self.cache_hits += 1
            else:
                uncached_texts.append((i, text))
                self.cache_misses += 1
        
        # Generate embeddings for uncached texts
        embeddings = np.zeros((len(texts), self._model.get_sentence_embedding_dimension()))
        
        if uncached_texts:
            indices, texts_to_encode = zip(*uncached_texts)
            new_embeddings = self._model.encode(
                list(texts_to_encode),
                batch_size=batch_size,
                show_progress_bar=False,
                convert_to_numpy=True
            )
            
            # Store new embeddings
            for idx, embedding in zip(indices, new_embeddings):
                embeddings[idx] = embedding
                text_hash = hash(texts[idx])
                if len(self.embedding_cache) < EMBEDDING_CACHE_SIZE:
                    self.embedding_cache[text_hash] = embedding
        
        # Insert cached embeddings
        for idx, embedding in cached_embeddings.items():
            embeddings[idx] = embedding
            
        return embeddings
    
    def compute_similarity_matrix(self, embeddings: np.ndarray) -> np.ndarray:
        """Compute pairwise cosine similarity matrix for embeddings.
        
        Args:
            embeddings: Dense embedding matrix
            
        Returns:
            Symmetric similarity matrix (n_texts, n_texts)
        """
        return cosine_similarity(embeddings)

class AdvancedClusteringEngine:
    """Sophisticated clustering engine with multiple algorithms and optimization."""
    
    def __init__(self):
        self.logger = logging.getLogger("CLUSTERING_ENGINE")
        self.scaler = StandardScaler()
        
    def adaptive_clustering(self, embeddings: np.ndarray, method: str = 'auto') -> Dict[str, Any]:
        """Perform adaptive clustering with automatic algorithm selection.
        
        Args:
            embeddings: Dense feature matrix for clustering
            method: Clustering algorithm ('auto', 'dbscan', 'hierarchical', 'kmeans')
            
        Returns:
            Comprehensive clustering results with metadata
        """
        if method == 'auto':
            method = self._select_optimal_method(embeddings)
            
        # Normalize embeddings for clustering
        normalized_embeddings = self.scaler.fit_transform(embeddings)
        
        if method == 'dbscan':
            return self._dbscan_clustering(normalized_embeddings)
        elif method == 'hierarchical':
            return self._hierarchical_clustering(normalized_embeddings)
        elif method == 'kmeans':
            return self._kmeans_clustering(normalized_embeddings)
        else:
            raise ValueError(f"Unsupported clustering method: {method}")
    
    def _select_optimal_method(self, embeddings: np.ndarray) -> str:
        """Select optimal clustering algorithm based on data characteristics.
        
        Args:
            embeddings: Feature matrix for analysis
            
        Returns:
            Recommended clustering algorithm identifier
        """
        n_samples, n_features = embeddings.shape
        
        if n_samples < 50:
            return 'hierarchical'  # Better for small datasets
        elif n_samples > 10000:
            return 'kmeans'  # Scalable for large datasets
        else:
            return 'dbscan'  # Robust for medium datasets
    
    def _dbscan_clustering(self, embeddings: np.ndarray) -> Dict[str, Any]:
        """DBSCAN clustering with automatic parameter tuning."""
        # Adaptive parameter selection
        eps = self._estimate_eps(embeddings)
        min_samples = max(2, int(np.log2(len(embeddings))))
        
        clusterer = DBSCAN(eps=eps, min_samples=min_samples, metric='cosine')
        cluster_labels = clusterer.fit_predict(embeddings)
        
        return {
            'algorithm': 'dbscan',
            'labels': cluster_labels.tolist(),
            'n_clusters': len(set(cluster_labels)) - (1 if -1 in cluster_labels else 0),
            'n_noise': np.sum(cluster_labels == -1),
            'parameters': {'eps': eps, 'min_samples': min_samples},
            'silhouette_score': self._compute_silhouette_score(embeddings, cluster_labels)
        }
    
    def _hierarchical_clustering(self, embeddings: np.ndarray) -> Dict[str, Any]:
        """Agglomerative hierarchical clustering with linkage optimization."""
        # Determine optimal number of clusters using elbow method
        optimal_k = self._find_optimal_k(embeddings, max_k=min(20, len(embeddings)//2))
        
        clusterer = AgglomerativeClustering(
            n_clusters=optimal_k,
            linkage='ward',
            metric='euclidean'
        )
        cluster_labels = clusterer.fit_predict(embeddings)
        
        return {
            'algorithm': 'hierarchical',
            'labels': cluster_labels.tolist(),
            'n_clusters': optimal_k,
            'parameters': {'linkage': 'ward', 'metric': 'euclidean'},
            'silhouette_score': self._compute_silhouette_score(embeddings, cluster_labels)
        }
    
    def _kmeans_clustering(self, embeddings: np.ndarray) -> Dict[str, Any]:
        """K-means clustering with automatic K selection."""
        optimal_k = self._find_optimal_k(embeddings, max_k=min(20, len(embeddings)//2))
        
        clusterer = KMeans(
            n_clusters=optimal_k,
            init='k-means++',
            n_init=10,
            random_state=42
        )
        cluster_labels = clusterer.fit_predict(embeddings)
        
        return {
            'algorithm': 'kmeans',
            'labels': cluster_labels.tolist(),
            'n_clusters': optimal_k,
            'centroids': clusterer.cluster_centers_.tolist(),
            'parameters': {'init': 'k-means++', 'n_init': 10},
            'silhouette_score': self._compute_silhouette_score(embeddings, cluster_labels),
            'inertia': clusterer.inertia_
        }
    
    def _estimate_eps(self, embeddings: np.ndarray) -> float:
        """Estimate optimal eps parameter for DBSCAN using k-distance graph."""
        from sklearn.neighbors import NearestNeighbors
        
        k = 4  # Standard heuristic
        nbrs = NearestNeighbors(n_neighbors=k, metric='cosine').fit(embeddings)
        distances, _ = nbrs.kneighbors(embeddings)
        distances = np.sort(distances[:, k-1], axis=0)
        
        # Find knee point in distance curve
        diffs = np.diff(distances)
        knee_point = np.argmax(diffs) + 1
        return distances[knee_point]
    
    def _find_optimal_k(self, embeddings: np.ndarray, max_k: int) -> int:
        """Find optimal number of clusters using elbow method."""
        inertias = []
        k_range = range(2, max_k + 1)
        
        for k in k_range:
            kmeans = KMeans(n_clusters=k, init='k-means++', n_init=10, random_state=42)
            kmeans.fit(embeddings)
            inertias.append(kmeans.inertia_)
        
        # Find elbow point
        if len(inertias) < 2:
            return 2
            
        diffs = np.diff(inertias)
        elbow_point = np.argmax(diffs[:-1] - diffs[1:]) + 2
        return elbow_point
    
    def _compute_silhouette_score(self, embeddings: np.ndarray, labels: np.ndarray) -> float:
        """Compute silhouette score for clustering quality assessment."""
        from sklearn.metrics import silhouette_score
        
        if len(set(labels)) < 2:
            return -1.0  # Invalid clustering
            
        try:
            return silhouette_score(embeddings, labels, metric='cosine')
        except:
            return -1.0

class AdvancedFeatureExtractor:
    """Multi-modal feature extraction with dimensionality reduction."""
    
    def __init__(self):
        self.logger = logging.getLogger("FEATURE_EXTRACTOR")
        self.tfidf_vectorizer = TfidfVectorizer(
            max_features=10000,
            ngram_range=(1, 3),
            stop_words='english'
        )
        
    def extract_comprehensive_features(self, texts: List[str]) -> Dict[str, Any]:
        """Extract comprehensive feature set from text collection.
        
        Args:
            texts: Collection of text documents
            
        Returns:
            Multi-modal feature analysis results
        """
        results = {
            'statistical_features': self._extract_statistical_features(texts),
            'linguistic_features': self._extract_linguistic_features(texts),
            'tfidf_features': self._extract_tfidf_features(texts),
            'n_documents': len(texts),
            'extraction_timestamp': datetime.utcnow().isoformat()
        }
        
        return results
    
    def _extract_statistical_features(self, texts: List[str]) -> Dict[str, Any]:
        """Extract statistical text features."""
        lengths = [len(text) for text in texts]
        word_counts = [len(text.split()) for text in texts]
        
        return {
            'char_length_stats': {
                'mean': np.mean(lengths),
                'std': np.std(lengths),
                'min': np.min(lengths),
                'max': np.max(lengths),
                'median': np.median(lengths)
            },
            'word_count_stats': {
                'mean': np.mean(word_counts),
                'std': np.std(word_counts),
                'min': np.min(word_counts),
                'max': np.max(word_counts),
                'median': np.median(word_counts)
            }
        }
    
    def _extract_linguistic_features(self, texts: List[str]) -> Dict[str, Any]:
        """Extract linguistic complexity features."""
        features = []
        
        for text in texts:
            words = text.split()
            sentences = text.split('.')
            
            # Basic linguistic metrics
            avg_word_length = np.mean([len(word) for word in words]) if words else 0
            avg_sentence_length = np.mean([len(sent.split()) for sent in sentences]) if sentences else 0
            
            features.append({
                'avg_word_length': avg_word_length,
                'avg_sentence_length': avg_sentence_length,
                'vocabulary_richness': len(set(words)) / len(words) if words else 0
            })
        
        return {
            'per_document_features': features,
            'aggregate_features': {
                'avg_word_length_mean': np.mean([f['avg_word_length'] for f in features]),
                'avg_sentence_length_mean': np.mean([f['avg_sentence_length'] for f in features]),
                'vocabulary_richness_mean': np.mean([f['vocabulary_richness'] for f in features])
            }
        }
    
    def _extract_tfidf_features(self, texts: List[str]) -> Dict[str, Any]:
        """Extract TF-IDF feature matrix."""
        try:
            tfidf_matrix = self.tfidf_vectorizer.fit_transform(texts)
            feature_names = self.tfidf_vectorizer.get_feature_names_out()
            
            # Top features analysis
            feature_scores = np.mean(tfidf_matrix.toarray(), axis=0)
            top_indices = np.argsort(feature_scores)[-20:][::-1]
            top_features = [(feature_names[i], feature_scores[i]) for i in top_indices]
            
            return {
                'matrix_shape': tfidf_matrix.shape,
                'n_features': len(feature_names),
                'top_features': top_features,
                'sparsity': 1.0 - (tfidf_matrix.nnz / (tfidf_matrix.shape[0] * tfidf_matrix.shape[1]))
            }
        except Exception as e:
            self.logger.error(f"TF-IDF extraction failed: {e}")
            return {'error': str(e)}

class TetragnosCore:
    """Advanced TETRAGNOS reasoning core with external library integration."""
    
    def __init__(self):
        self.logger = logging.getLogger("TETRAGNOS_CORE")
        self.semantic_engine = AdvancedSemanticEngine()
        self.clustering_engine = AdvancedClusteringEngine()
        self.feature_extractor = AdvancedFeatureExtractor()
        self.task_count = 0
        
    def execute(self, task_type: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Execute TETRAGNOS task with advanced ML capabilities.
        
        Args:
            task_type: Specific task identifier
            payload: Task parameters and data
            
        Returns:
            Comprehensive task execution results
        """
        self.task_count += 1
        start_time = time.time()
        
        try:
            if task_type == "cluster_texts":
                result = self._cluster_texts_advanced(payload)
            elif task_type == "extract_features":
                result = self._extract_features_advanced(payload)
            elif task_type == "semantic_similarity":
                result = self._compute_semantic_similarity(payload)
            elif task_type == "analyze_patterns":
                result = self._analyze_patterns_advanced(payload)
            elif task_type == "translate_text":
                result = self._translate_text_advanced(payload)
            else:
                raise ValueError(f"Unsupported task type: {task_type}")
            
            execution_time = time.time() - start_time
            
            result.update({
                'execution_time': execution_time,
                'task_id': payload.get('task_id', f'tetragnos_{self.task_count}'),
                'subsystem': 'tetragnos',
                'status': 'completed',
                'timestamp': datetime.utcnow().isoformat()
            })
            
            return result
            
        except Exception as e:
            self.logger.error(f"Task execution failed: {e}", exc_info=True)
            return {
                'task_id': payload.get('task_id', f'tetragnos_{self.task_count}'),
                'subsystem': 'tetragnos',
                'status': 'failed',
                'error': str(e),
                'execution_time': time.time() - start_time,
                'timestamp': datetime.utcnow().isoformat()
            }
    
    def _cluster_texts_advanced(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Advanced text clustering using SentenceTransformers and multiple algorithms."""
        texts = payload.get('texts', [])
        method = payload.get('method', 'auto')
        
        if not texts:
            raise ValueError("No texts provided for clustering")
        
        # Generate semantic embeddings
        embeddings = self.semantic_engine.encode_texts(texts)
        
        # Perform clustering
        clustering_result = self.clustering_engine.adaptive_clustering(embeddings, method)
        
        # Add cluster interpretability
        cluster_summaries = self._generate_cluster_summaries(texts, clustering_result['labels'])
        
        return {
            'clustering_result': clustering_result,
            'cluster_summaries': cluster_summaries,
            'embedding_stats': {
                'shape': embeddings.shape,
                'cache_hits': self.semantic_engine.cache_hits,
                'cache_misses': self.semantic_engine.cache_misses
            }
        }
    
    def _extract_features_advanced(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Advanced feature extraction with multiple modalities."""
        texts = payload.get('texts', [])
        include_embeddings = payload.get('include_embeddings', False)
        
        if not texts:
            raise ValueError("No texts provided for feature extraction")
        
        # Extract comprehensive features
        features = self.feature_extractor.extract_comprehensive_features(texts)
        
        # Optionally include semantic embeddings
        if include_embeddings:
            embeddings = self.semantic_engine.encode_texts(texts)
            features['semantic_embeddings'] = {
                'shape': embeddings.shape,
                'dimensionality': embeddings.shape[1]
            }
        
        return {'features': features}
    
    def _compute_semantic_similarity(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Compute semantic similarity matrix using transformer embeddings."""
        texts = payload.get('texts', [])
        
        if not texts:
            raise ValueError("No texts provided for similarity computation")
        
        embeddings = self.semantic_engine.encode_texts(texts)
        similarity_matrix = self.semantic_engine.compute_similarity_matrix(embeddings)
        
        return {
            'similarity_matrix': similarity_matrix.tolist(),
            'matrix_shape': similarity_matrix.shape,
            'max_similarity': float(np.max(similarity_matrix)),
            'min_similarity': float(np.min(similarity_matrix)),
            'mean_similarity': float(np.mean(similarity_matrix))
        }
    
    def _analyze_patterns_advanced(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Advanced pattern analysis combining multiple techniques."""
        texts = payload.get('texts', [])
        
        if not texts:
            raise ValueError("No texts provided for pattern analysis")
        
        # Multi-modal analysis
        embeddings = self.semantic_engine.encode_texts(texts)
        features = self.feature_extractor.extract_comprehensive_features(texts)
        clustering = self.clustering_engine.adaptive_clustering(embeddings)
        
        return {
            'pattern_analysis': {
                'semantic_patterns': clustering,
                'linguistic_patterns': features['linguistic_features'],
                'statistical_patterns': features['statistical_features']
            },
            'insights': self._generate_pattern_insights(texts, embeddings, clustering)
        }
    
    def _translate_text_advanced(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Advanced text translation with semantic preservation analysis."""
        text = payload.get('text', '')
        target_language = payload.get('target_language', 'en')
        
        # Placeholder for advanced translation - would integrate with translation models
        # For now, return identity translation with semantic analysis
        original_embedding = self.semantic_engine.encode_texts([text])
        
        return {
            'original_text': text,
            'translated_text': text,  # Placeholder
            'target_language': target_language,
            'semantic_preservation_score': 1.0,  # Placeholder
            'original_embedding_shape': original_embedding.shape
        }
    
    def _generate_cluster_summaries(self, texts: List[str], labels: List[int]) -> Dict[str, Any]:
        """Generate interpretable summaries for each cluster."""
        clusters = {}
        
        for i, label in enumerate(labels):
            if label not in clusters:
                clusters[label] = []
            clusters[label].append(texts[i])
        
        summaries = {}
        for cluster_id, cluster_texts in clusters.items():
            if cluster_id == -1:  # Noise cluster in DBSCAN
                summaries[cluster_id] = {
                    'size': len(cluster_texts),
                    'label': 'noise',
                    'sample_texts': cluster_texts[:3]
                }
            else:
                summaries[cluster_id] = {
                    'size': len(cluster_texts),
                    'sample_texts': cluster_texts[:3],
                    'avg_length': np.mean([len(text) for text in cluster_texts])
                }
        
        return summaries
    
    def _generate_pattern_insights(self, texts: List[str], embeddings: np.ndarray, clustering: Dict[str, Any]) -> Dict[str, Any]:
        """Generate high-level insights from pattern analysis."""
        return {
            'diversity_score': float(np.mean(np.std(embeddings, axis=0))),
            'clustering_quality': clustering.get('silhouette_score', -1),
            'optimal_clusters': clustering.get('n_clusters', 0),
            'text_complexity': {
                'avg_length': np.mean([len(text) for text in texts]),
                'length_variance': np.var([len(text) for text in texts])
            }
        }

class TetragnosWorker:
    """Advanced TETRAGNOS worker with external library integration."""
    
    def __init__(self):
        self.logger = logging.getLogger("TETRAGNOS_WORKER")
        self.core = TetragnosCore()
        self.connection = None
        self.channel = None
        self.should_stop = False
        
        # Setup signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
        
    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully."""
        self.logger.info(f"Received signal {signum}, shutting down...")
        self.should_stop = True
        
    def start(self):
        """Start the TETRAGNOS worker service."""
        self.logger.info("Starting TETRAGNOS Advanced Worker...")
        
        while not self.should_stop:
            try:
                self._connect_and_consume()
            except Exception as e:
                self.logger.error(f"Connection error: {e}")
                time.sleep(5)  # Wait before reconnection
                
    def _connect_and_consume(self):
        """Establish RabbitMQ connection and start consuming tasks."""
        # Connect to RabbitMQ
        self.connection = pika.BlockingConnection(
            pika.ConnectionParameters(
                host=RABBITMQ_HOST,
                port=RABBITMQ_PORT,
                heartbeat=600,
                blocked_connection_timeout=300
            )
        )
        
        self.channel = self.connection.channel()
        
        # Declare queues
        self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
        self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)
        
        # Configure QoS
        self.channel.basic_qos(prefetch_count=1)
        
        # Setup consumer
        self.channel.basic_consume(
            queue=TASK_QUEUE,
            on_message_callback=self._process_task,
            auto_ack=False
        )
        
        self.logger.info("TETRAGNOS Worker ready for advanced ML tasks")
        
        # Start consuming
        while not self.should_stop:
            try:
                self.connection.process_data_events(time_limit=1)
            except KeyboardInterrupt:
                break
                
        # Cleanup
        if self.connection and not self.connection.is_closed:
            self.connection.close()
            
    def _process_task(self, channel, method, properties, body):
        """Process incoming task with advanced ML capabilities."""
        try:
            # Parse task
            task_data = json.loads(body.decode('utf-8'))
            task_id = task_data.get('task_id', str(uuid.uuid4()))
            task_type = task_data.get('task_type', 'unknown')
            payload = task_data.get('payload', {})
            
            self.logger.info(f"Processing advanced task {task_id}: {task_type}")
            
            # Execute task using advanced core
            result = self.core.execute(task_type, payload)
            
            # Publish result
            self._publish_result(result)
            
            # Acknowledge task completion
            channel.basic_ack(delivery_tag=method.delivery_tag)
            
            self.logger.info(f"Task {task_id} completed successfully")
            
        except Exception as e:
            self.logger.error(f"Task processing error: {e}", exc_info=True)
            
            # Send error result
            error_result = {
                'task_id': task_data.get('task_id', 'unknown'),
                'subsystem': 'tetragnos',
                'status': 'failed',
                'error': str(e),
                'timestamp': datetime.utcnow().isoformat()
            }
            
            self._publish_result(error_result)
            channel.basic_ack(delivery_tag=method.delivery_tag)
            
    def _publish_result(self, result: Dict[str, Any]):
        """Publish task result to result queue."""
        try:
            self.channel.basic_publish(
                exchange='',
                routing_key=RESULT_QUEUE,
                body=json.dumps(result),
                properties=pika.BasicProperties(delivery_mode=2)  # Persistent
            )
        except Exception as e:
            self.logger.error(f"Failed to publish result: {e}")

def main():
    """Main entry point for TETRAGNOS advanced worker."""
    worker = TetragnosWorker()
    worker.start()

if __name__ == "__main__":
    main()