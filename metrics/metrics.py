"""
Metrics collection for LOGOS Alignment Core proof operations
"""

import csv
import os
import time
from typing import Any


class Metrics:
    """Collects and logs proof operation metrics"""

    def __init__(self, csv_path: str = "metrics/proofs.csv"):
        self.csv_path = csv_path
        self.ensure_csv_exists()

    def ensure_csv_exists(self):
        """Ensure CSV file exists with proper headers"""
        if not os.path.exists(self.csv_path):
            os.makedirs(os.path.dirname(self.csv_path), exist_ok=True)
            with open(self.csv_path, "w", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(["timestamp", "obligation", "duration_ms", "result"])

    def log(self, obligation: str, duration_ms: int, result: str):
        """Log a proof operation metric"""
        timestamp = int(time.time())

        try:
            with open(self.csv_path, "a", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([timestamp, obligation, duration_ms, result])
        except Exception:
            # Silent fail to avoid disrupting proof operations
            pass

    def get_stats(self) -> dict[str, Any]:
        """Get summary statistics from logged metrics"""
        if not os.path.exists(self.csv_path):
            return {"error": "no_metrics_file"}

        stats = {
            "total_proofs": 0,
            "allows": 0,
            "denies": 0,
            "avg_duration_ms": 0,
            "max_duration_ms": 0,
        }

        try:
            with open(self.csv_path) as f:
                reader = csv.DictReader(f)
                durations = []

                for row in reader:
                    stats["total_proofs"] += 1
                    if row["result"] == "ALLOW":
                        stats["allows"] += 1
                    elif row["result"] == "DENY":
                        stats["denies"] += 1

                    duration = int(row["duration_ms"])
                    durations.append(duration)
                    stats["max_duration_ms"] = max(stats["max_duration_ms"], duration)

                if durations:
                    stats["avg_duration_ms"] = sum(durations) / len(durations)

        except Exception as e:
            stats["error"] = str(e)

        return stats
