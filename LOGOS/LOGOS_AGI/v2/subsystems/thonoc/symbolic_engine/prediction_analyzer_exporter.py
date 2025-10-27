"""
prediction_analyzer_exporter.py

THŌNOC Prediction Analyzer/Exporter.
"""
import json
import pandas as pd
import matplotlib.pyplot as plt
import argparse

def load_predictions(path="prediction_log.jsonl"):
    """Load all prediction logs from a JSONL file."""
    with open(path, "r") as f:
        return [json.loads(line) for line in f]

def summarize(preds):
    df = pd.DataFrame(preds)
    print(f"\nLoaded {len(df)} predictions.")
    print("Modal Counts:\n", df['modal_status'].value_counts())
    print(f"Average Coherence: {df['coherence'].mean():.3f}")
    return df

def plot_coherence(df):
    plt.figure()
    plt.hist(df['coherence'], bins=20)
    plt.title("Coherence Distribution")
    plt.xlabel("Coherence"); plt.ylabel("Count")
    plt.show()

def filter_predictions(df, modal=None, min_coherence=None):
    r = df.copy()
    if modal:          r = r[r['modal_status']==modal]
    if min_coherence:  r = r[r['coherence']>=min_coherence]
    return r

def export_predictions(df, out_file="filtered_predictions.csv", fmt="csv"):
    if fmt=="json":
        df.to_json(out_file, orient="records", indent=2)
    else:
        df.to_csv(out_file, index=False)
    print(f"[✔] Exported {len(df)} rows to {out_file}")

class FractalKnowledgeStore:
    """Simple JSONL-backed knowledge store for THŌNOC."""
    def __init__(self, config: dict):
        self.path = config.get("storage_path", "knowledge_store.jsonl")
    def store_node(self, **kwargs) -> str:
        node_id = kwargs.get("query_id", str(uuid.uuid4()))
        with open(self.path, "a") as f:
            f.write(json.dumps({"id":node_id, **kwargs}) + "\n")
        return node_id
    def get_node(self, node_id: str):
        try:
            with open(self.path) as f:
                for line in f:
                    rec = json.loads(line)
                    if rec.get("id")==node_id:
                        return rec
        except FileNotFoundError:
            return None
        return None

if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", default="prediction_log.jsonl")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--hist", action="store_true")
    parser.add_argument("--modal", choices=["necessary","actual","possible","impossible"])
    parser.add_argument("--min-coh", type=float)
    parser.add_argument("--export", choices=["csv","json"])
    args = parser.parse_args()

    preds = load_predictions(args.file)
    df = summarize(preds) if args.summary else pd.DataFrame(preds)
    if args.hist:           plot_coherence(df)
    df2 = filter_predictions(df, args.modal, args.min_coh)
    if args.export:         export_predictions(df2, fmt=args.export)
