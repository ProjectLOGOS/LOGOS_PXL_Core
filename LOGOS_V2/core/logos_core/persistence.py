"""
Persistence Layer - Audit logging for all proof-gated decisions
Maintains JSONL audit trail as required by fail-closed design
"""

import json
import os
import time
from datetime import datetime
from typing import Any


class AuditLog:
    def __init__(self, audit_path: str):
        self.audit_path = audit_path
        # Ensure audit directory exists
        os.makedirs(os.path.dirname(audit_path), exist_ok=True)

    def append(self, record: dict[str, Any]) -> None:
        """
        Append an audit record to the JSONL log

        Args:
            record: Audit record containing ts, obligation, provenance, decision, proof
        """
        # Ensure timestamp is present
        if "ts" not in record:
            record["ts"] = int(time.time())

        # Add human-readable timestamp
        record["timestamp_iso"] = datetime.fromtimestamp(record["ts"]).isoformat()

        # Write to JSONL file (one JSON object per line)
        with open(self.audit_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record) + "\n")

    def query_recent(self, limit: int = 100) -> list:
        """
        Query recent audit records

        Args:
            limit: Maximum number of records to return

        Returns:
            List of recent audit records
        """
        if not os.path.exists(self.audit_path):
            return []

        records = []
        with open(self.audit_path, encoding="utf-8") as f:
            lines = f.readlines()

        # Get the last 'limit' lines
        recent_lines = lines[-limit:] if len(lines) > limit else lines

        for line in recent_lines:
            try:
                record = json.loads(line.strip())
                records.append(record)
            except json.JSONDecodeError:
                # Skip malformed lines
                continue

        return records

    def query_by_decision(self, decision: str, limit: int = 100) -> list:
        """
        Query audit records by decision type (ALLOW/DENY)

        Args:
            decision: Decision type to filter by
            limit: Maximum number of records to return

        Returns:
            List of matching audit records
        """
        if not os.path.exists(self.audit_path):
            return []

        records = []
        count = 0

        with open(self.audit_path, encoding="utf-8") as f:
            for line in f:
                if count >= limit:
                    break

                try:
                    record = json.loads(line.strip())
                    if record.get("decision") == decision:
                        records.append(record)
                        count += 1
                except json.JSONDecodeError:
                    continue

        return records

    def query_by_obligation_pattern(self, pattern: str, limit: int = 100) -> list:
        """
        Query audit records by obligation pattern

        Args:
            pattern: String pattern to search for in obligations
            limit: Maximum number of records to return

        Returns:
            List of matching audit records
        """
        if not os.path.exists(self.audit_path):
            return []

        records = []
        count = 0

        with open(self.audit_path, encoding="utf-8") as f:
            for line in f:
                if count >= limit:
                    break

                try:
                    record = json.loads(line.strip())
                    obligation = record.get("obligation", "")
                    if pattern.lower() in obligation.lower():
                        records.append(record)
                        count += 1
                except json.JSONDecodeError:
                    continue

        return records

    def get_stats(self) -> dict[str, Any]:
        """
        Get statistics about the audit log

        Returns:
            Dict with audit log statistics
        """
        if not os.path.exists(self.audit_path):
            return {"exists": False, "total_records": 0, "file_size_bytes": 0}

        total_records = 0
        allow_count = 0
        deny_count = 0

        with open(self.audit_path, encoding="utf-8") as f:
            for line in f:
                try:
                    record = json.loads(line.strip())
                    total_records += 1
                    decision = record.get("decision", "")
                    if decision == "ALLOW":
                        allow_count += 1
                    elif decision == "DENY":
                        deny_count += 1
                except json.JSONDecodeError:
                    continue

        file_size = os.path.getsize(self.audit_path)

        return {
            "exists": True,
            "total_records": total_records,
            "allow_count": allow_count,
            "deny_count": deny_count,
            "file_size_bytes": file_size,
            "audit_path": self.audit_path,
        }

    def validate_integrity(self) -> dict[str, Any]:
        """
        Validate integrity of the audit log

        Returns:
            Dict with validation results
        """
        if not os.path.exists(self.audit_path):
            return {"valid": True, "message": "No audit log exists yet", "malformed_lines": 0}

        total_lines = 0
        malformed_lines = 0

        with open(self.audit_path, encoding="utf-8") as f:
            for line_num, line in enumerate(f, 1):
                total_lines += 1
                try:
                    record = json.loads(line.strip())
                    # Validate required fields
                    required_fields = ["ts", "obligation", "provenance", "decision"]
                    for field in required_fields:
                        if field not in record:
                            malformed_lines += 1
                            break
                except json.JSONDecodeError:
                    malformed_lines += 1

        return {
            "valid": malformed_lines == 0,
            "total_lines": total_lines,
            "malformed_lines": malformed_lines,
            "integrity_percentage": ((total_lines - malformed_lines) / max(total_lines, 1)) * 100,
        }
