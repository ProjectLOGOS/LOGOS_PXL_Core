"""
bayesian_data_parser.py

Handles loading/saving of Bayesian prediction data.
"""
import pandas as pd
from pathlib import Path
import json
from typing import Dict, Optional
from datetime import datetime

class BayesianDataHandler:
    def __init__(self, data_dir: str = "data/bayesian_ml"):
        self.data_dir = Path(data_dir)
        self.predictions_file = self.data_dir / "predictions.csv"
        self.metadata_file = self.data_dir / "metadata.json"
        self._init_storage()

    def _init_storage(self):
        self.data_dir.mkdir(parents=True, exist_ok=True)
        if not self.predictions_file.exists():
            pd.DataFrame(columns=[
                'timestamp','prediction','confidence','variance','hypothesis','evidence'
            ]).to_csv(self.predictions_file, index=False)
        if not self.metadata_file.exists():
            meta = {
                'model_version':'1.0',
                'last_updated': datetime.now().isoformat(),
                'performance_metrics': {}, 
                'model_parameters': {}
            }
            self.save_metadata(meta)

    def save_prediction(self, prediction, hypothesis: str) -> None:
        row = {
            'timestamp': prediction.timestamp,
            'prediction': prediction.prediction,
            'confidence': prediction.confidence,
            'variance': prediction.variance,
            'hypothesis': hypothesis,
            'evidence': json.dumps(prediction.metadata['evidence'])
        }
        pd.DataFrame([row]).to_csv(self.predictions_file, mode='a', header=False, index=False)

    def get_predictions(self, start_date: Optional[str]=None,
                              end_date: Optional[str]=None,
                              min_confidence: float=0.0):
        df = pd.read_csv(self.predictions_file, parse_dates=['timestamp'])
        if start_date:
            df = df[df.timestamp >= pd.to_datetime(start_date)]
        if end_date:
            df = df[df.timestamp <= pd.to_datetime(end_date)]
        if min_confidence > 0:
            df = df[df.confidence >= min_confidence]
        return df

    def save_metadata(self, metadata: Dict) -> None:
        metadata['last_updated'] = datetime.now().isoformat()
        with open(self.metadata_file, 'w') as f:
            json.dump(metadata, f, indent=2)

    def get_metadata(self) -> Dict:
        with open(self.metadata_file) as f:
            return json.load(f)

    def cleanup_old_data(self, days_to_keep: int = 30) -> None:
        df = pd.read_csv(self.predictions_file, parse_dates=['timestamp'])
        cutoff = pd.Timestamp.now() - pd.Timedelta(days=days_to_keep)
        df = df[df.timestamp >= cutoff]
        df.to_csv(self.predictions_file, index=False)
