# ml_components.py

import numpy as np
from typing import List, Dict, Any
from translation_engine import translate

# Text embedding imports
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD

# Clustering imports
from sklearn.cluster import DBSCAN
from sklearn.manifold import UMAP

# Prediction imports
from sklearn.ensemble import RandomForestRegressor

class FeatureExtractor:
    """
    Combines ontological axis values (existence, goodness, truth)
    with lightweight text embeddings (TF-IDF + SVD).
    """
    def __init__(self, n_components: int = 50):
        self.vectorizer = TfidfVectorizer(max_features=1000)
        self.svd = TruncatedSVD(n_components=n_components)
        self._fitted = False

    def fit_transform(self, texts: List[str]) -> np.ndarray:
        tfidf = self.vectorizer.fit_transform(texts)
        emb = self.svd.fit_transform(tfidf)
        self._fitted = True
        return emb

    def transform(self, texts: List[str]) -> np.ndarray:
        if not self._fitted:
            raise RuntimeError("FeatureExtractor: call fit_transform() first")
        tfidf = self.vectorizer.transform(texts)
        return self.svd.transform(tfidf)

    def extract(self, payloads: List[Any]) -> np.ndarray:
        """
        Given a list of payloads (string or dict with 'text'),
        returns an array of shape (N, 3 + n_components) combining:
          - [existence, goodness, truth]
          - text embedding vector
        """
        texts = [
            p if isinstance(p, str) else p.get('text', '') for p in payloads
        ]
        if not self._fitted:
            text_embs = self.fit_transform(texts)
        else:
            text_embs = self.transform(texts)

        axes = []
        for p in payloads:
            text = p if isinstance(p, str) else p.get('text', '')
            vec = translate(text)
            axes.append([vec.existence, vec.goodness, vec.truth])
        axes_arr = np.array(axes)

        return np.hstack([axes_arr, text_embs])

class ClusterAnalyzer:
    """
    Performs dimensionality reduction + clustering on feature arrays.
    """
    def __init__(self, eps: float = 0.5, min_samples: int = 5, n_neighbors: int = 15):
        self.reducer = UMAP(n_neighbors=n_neighbors, min_dist=0.1)
        self.clusterer = DBSCAN(eps=eps, min_samples=min_samples)

    def fit(self, features: np.ndarray) -> Dict[str, np.ndarray]:
        """
        features: (N, D)
        Returns a dict with:
          - 'embedding_2d': (N, 2) UMAP projection
          - 'labels':       (N,) cluster labels ( -1 = noise )
        """
        emb2d = self.reducer.fit_transform(features)
        labels = self.clusterer.fit_predict(emb2d)
        return {'embedding_2d': emb2d, 'labels': labels}

    def find_gaps(self, labels: np.ndarray) -> np.ndarray:
        """
        Given cluster labels, returns indices of 'noise' points for gap seeding.
        """
        return np.where(labels == -1)[0]

class NextNodePredictor:
    """
    A simple regressor to predict next node coordinates (x, y, z)
    from feature vectors.
    """
    def __init__(self):
        self.model = RandomForestRegressor(n_estimators=50)

    def train(self, X: np.ndarray, y: np.ndarray):
        """
        X: (N, D) feature matrix
        y: (N, 3) target coordinates
        """
        self.model.fit(X, y)

    def predict(self, features: np.ndarray) -> np.ndarray:
        """
        features: (M, D) new feature matrix
        returns: (M, 3) predicted (x, y, z) positions
        """
        return self.model.predict(features)
