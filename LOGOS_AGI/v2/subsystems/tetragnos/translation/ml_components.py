import numpy as np
from sentence_transformers import SentenceTransformer
from sklearn.cluster import DBSCAN
from umap import UMAP
from typing import List, Any


class FeatureExtractor:
    def __init__(self, model_name: str = "all-MiniLM-L6-v2"):
        try:
            self.model = SentenceTransformer(model_name)
            print(f"[Tetragnos] Loaded sentence transformer model: {model_name}")
        except Exception as e:
            print(f"[Tetragnos] ERROR: Could not load SentenceTransformer model. {e}")
            self.model = None

    def fit_transform(self, texts: list) -> np.ndarray:
        if not self.model:
            return np.zeros((len(texts), 384))
        embeddings = self.model.encode(texts, show_progress_bar=False)
        return embeddings


class ClusterAnalyzer:
    def __init__(
        self, eps: float = 0.5, min_samples: int = 2, n_neighbors: int = 5, n_components: int = 2
    ):
        self.eps = eps
        self.min_samples = min_samples
        self.n_neighbors = n_neighbors
        self.n_components = n_components
        self.reducer = None
        self.clusterer = None

    def fit(self, features: np.ndarray) -> dict:
        if features.shape[0] < 2:
            return {"embedding_2d": features.tolist(), "labels": [0] * features.shape[0]}

        n_neighbors_val = min(features.shape[0] - 1, self.n_neighbors)
        if n_neighbors_val < 1:
            n_neighbors_val = 1

        self.reducer = UMAP(
            n_neighbors=n_neighbors_val, n_components=self.n_components, min_dist=0.1
        )
        self.clusterer = DBSCAN(eps=self.eps, min_samples=self.min_samples)

        emb2d = self.reducer.fit_transform(features)
        labels = self.clusterer.fit_predict(emb2d)
        return {"embedding_2d": emb2d.tolist(), "labels": labels.tolist()}
