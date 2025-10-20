# logos_agi_v1/subsystems/tetragnos/lambda_engine/logos_lambda_core.py

import logging
# --- External Library Imports ---
import torch
from sentence_transformers import SentenceTransformer

# --- NEW SCIKIT-LEARN INTEGRATION ---
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.naive_bayes import MultinomialNB
from sklearn.pipeline import make_pipeline
# --- End Imports ---

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - TETRAGNOS_CORE - %(message)s')

class TetragnosCore:
    """
    Core logic for the Tetragnos subsystem. Handles ML/NLP tasks using
    PyTorch, Sentence-Transformers, and Scikit-learn.
    """
    def __init__(self):
        """
        Initializes the core and loads/trains necessary models.
        """
        logging.info("Initializing TetragnosCore...")
        try:
            # PyTorch and Sentence-Transformers setup
            self.device = "cuda" if torch.cuda.is_available() else "cpu"
            logging.info(f"Using device: {self.device}")
            self.embedding_model = SentenceTransformer('all-MiniLM-L6-v2', device=self.device)
            logging.info("SentenceTransformer model loaded successfully.")

            # --- NEW: Train a simple Scikit-learn model on startup ---
            logging.info("Training a simple scikit-learn text classifier...")
            # Sample data for a toy model
            train_data = [
                "This piece of software is amazing and wonderful",
                "I am so happy with this result",
                "This is a terrible, awful bug",
                "I am very angry about this problem"
            ]
            train_labels = ["positive", "positive", "negative", "negative"]
            
            # Create a model pipeline: text -> TF-IDF vectors -> Naive Bayes classifier
            self.sentiment_classifier = make_pipeline(
                TfidfVectorizer(),
                MultinomialNB()
            )
            self.sentiment_classifier.fit(train_data, train_labels)
            logging.info("Scikit-learn sentiment classifier trained successfully.")
            # --- END NEW ---

        except Exception as e:
            logging.error(f"Failed to initialize models: {e}", exc_info=True)
            self.embedding_model = None
            self.sentiment_classifier = None
        
    def execute(self, payload: dict) -> dict:
        """
        Executes a task based on the payload.
        """
        if not all([self.embedding_model, self.sentiment_classifier]):
            raise RuntimeError("TetragnosCore is not properly initialized. A model failed to load.")

        action = payload.get('action')
        logging.info(f"Executing action: {action}")

        if action == 'generate_embedding':
            text = payload.get('text')
            if not text:
                raise ValueError("Payload for 'generate_embedding' must contain 'text'.")
            
            embedding = self.embedding_model.encode(text, convert_to_tensor=True)
            return {"embedding": embedding.cpu().tolist(), "model": "all-MiniLM-L6-v2"}
            
        # --- NEW ACTION USING THE SKLEARN MODEL ---
        elif action == 'classify_sentiment_classic':
            text_to_classify = payload.get('text')
            if not text_to_classify:
                raise ValueError("Payload for 'classify_sentiment_classic' must contain 'text'.")

            # The pipeline handles vectorization and prediction
            prediction = self.sentiment_classifier.predict([text_to_classify])[0]
            probabilities = self.sentiment_classifier.predict_proba([text_to_classify])[0]
            
            confidence = max(probabilities)
            classes = self.sentiment_classifier.classes_

            return {
                "text": text_to_classify,
                "sentiment": prediction,
                "confidence": float(confidence),
                "model": "scikit-learn MultinomialNB"
            }
        # --- END NEW ---
        
        else:
            # Fallback for old sentiment analysis placeholder
            if action == 'sentiment_analysis':
                logging.warning("Action 'sentiment_analysis' is deprecated. Use 'classify_sentiment_classic'.")
                text_ref = payload.get('input_ref', 'no text provided')
                return {"sentiment": "neutral", "confidence": 0.5, "details": f"Analyzed text related to {text_ref}"}

            raise NotImplementedError(f"Action '{action}' is not implemented in TetragnosCore.")