"""
Tetragnos Subsystem FastAPI Application

Provides REST API interface for the Tetragnos pattern recognition subsystem.
"""

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import logging
import os
import numpy as np
from sklearn.cluster import KMeans
from sklearn.feature_extraction.text import TfidfVectorizer

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("tetragnos_app")

app = FastAPI(
    title="Tetragnos Pattern Recognition API",
    description="Advanced pattern recognition and clustering subsystem",
    version="1.0.0"
)

class ClusteringRequest(BaseModel):
    texts: list[str]
    num_clusters: int = 5

class ClusteringResponse(BaseModel):
    clusters: list[list[str]]
    cluster_centers: list[list[float]]
    success: bool
    message: str

def perform_text_clustering(texts, num_clusters=5):
    """Perform text clustering using TF-IDF and K-means"""
    try:
        # Create TF-IDF vectors
        vectorizer = TfidfVectorizer(max_features=1000, stop_words='english')
        tfidf_matrix = vectorizer.fit_transform(texts)

        # Perform clustering
        kmeans = KMeans(n_clusters=num_clusters, random_state=42, n_init=10)
        clusters = kmeans.fit_predict(tfidf_matrix)

        # Organize texts by cluster
        cluster_texts = [[] for _ in range(num_clusters)]
        for text, cluster_id in zip(texts, clusters):
            cluster_texts[cluster_id].append(text)

        return {
            "clusters": cluster_texts,
            "cluster_centers": kmeans.cluster_centers_.tolist(),
            "success": True
        }
    except Exception as e:
        return {
            "clusters": [],
            "cluster_centers": [],
            "success": False,
            "error": str(e)
        }

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {"status": "healthy", "subsystem": "tetragnos"}

@app.post("/cluster", response_model=ClusteringResponse)
async def cluster_texts(request: ClusteringRequest):
    """Perform text clustering on the provided texts"""
    try:
        logger.info(f"Processing clustering request with {len(request.texts)} texts")

        # Execute clustering
        result = perform_text_clustering(request.texts, request.num_clusters)

        if not result["success"]:
            raise HTTPException(status_code=500, detail=f"Clustering failed: {result.get('error', 'Unknown error')}")

        return ClusteringResponse(
            clusters=result.get("clusters", []),
            cluster_centers=result.get("cluster_centers", []),
            success=True,
            message="Clustering completed successfully"
        )

    except Exception as e:
        logger.error(f"Clustering failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Clustering failed: {str(e)}")

@app.get("/status")
async def get_status():
    """Get subsystem status"""
    return {
        "subsystem": "tetragnos",
        "status": "active",
        "capabilities": ["text_clustering", "pattern_recognition"],
        "version": "1.0.0"
    }

@app.post("/process")
async def process_task(request: dict):
    """Generic task processing endpoint for worker integration"""
    try:
        task = request.get("task", "")
        parameters = request.get("parameters", {})

        if task == "pattern_recognition" or task == "cluster":
            # Route to clustering endpoint
            cluster_req = ClusteringRequest(**parameters)
            return await cluster_texts(cluster_req)
        else:
            raise HTTPException(status_code=400, detail=f"Unknown task: {task}")

    except Exception as e:
        logger.error(f"Task processing failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Task processing failed: {str(e)}")

if __name__ == "__main__":
    import uvicorn
    port = int(os.getenv("PORT", 8065))
    uvicorn.run(app, host="0.0.0.0", port=port)