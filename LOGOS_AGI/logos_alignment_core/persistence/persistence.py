import json
import os


def ensure_parent(path: str):
    os.makedirs(os.path.dirname(path), exist_ok=True)


class AuditLog:
    def __init__(self, path: str):
        self.path = path
        ensure_parent(path)

    def append(self, record: dict):
        with open(self.path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
