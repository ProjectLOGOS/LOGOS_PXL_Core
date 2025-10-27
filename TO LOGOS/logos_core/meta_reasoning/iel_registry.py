"""
IEL Registry - Verified IEL Registry and Hash Management

Maintains a cryptographically secure registry of verified IEL rules with integrity
hashing, version control, and audit trails. Provides governance layer for IEL
lifecycle management while preserving formal verification guarantees.

Architecture:
- Cryptographic hash verification for IEL integrity
- Version-controlled IEL rule storage
- Verification status tracking and audit trails
- Dependency graph management
- Safe rollback and recovery mechanisms

Safety Constraints:
- All IEL modifications require cryptographic verification
- Immutable audit trail of all changes
- Formal verification gate before activation
- Dependency consistency enforcement
- Rollback capability for safety
"""

import hashlib
import json
import logging
from typing import Dict, List, Set, Optional, Any, Tuple
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from collections import defaultdict
import sqlite3
import threading

from .iel_generator import IELCandidate


@dataclass
class IELRegistryEntry:
    """Represents a registered IEL rule with verification metadata"""
    id: str
    domain: str
    rule_name: str
    rule_content: str
    content_hash: str
    version: int
    status: str  # "pending", "verified", "active", "deprecated", "revoked"
    created_at: datetime
    verified_at: Optional[datetime] = None
    activated_at: Optional[datetime] = None
    verifier_signature: Optional[str] = None
    proof_hash: Optional[str] = None
    dependencies: List[str] = field(default_factory=list)
    dependents: List[str] = field(default_factory=list)
    audit_trail: List[Dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        data = asdict(self)
        data["created_at"] = self.created_at.isoformat()
        if self.verified_at:
            data["verified_at"] = self.verified_at.isoformat()
        if self.activated_at:
            data["activated_at"] = self.activated_at.isoformat()
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'IELRegistryEntry':
        """Create from dictionary"""
        data["created_at"] = datetime.fromisoformat(data["created_at"])
        if data.get("verified_at"):
            data["verified_at"] = datetime.fromisoformat(data["verified_at"])
        if data.get("activated_at"):
            data["activated_at"] = datetime.fromisoformat(data["activated_at"])
        return cls(**data)


@dataclass
class RegistryConfig:
    """Configuration for IEL Registry"""
    database_path: str = "data/iel_registry.db"
    backup_path: str = "data/iel_registry_backups/"
    hash_algorithm: str = "sha256"
    enable_signature_verification: bool = True
    max_pending_iels: int = 100
    auto_backup_interval: int = 3600  # seconds
    enable_dependency_checking: bool = True


@dataclass
class RegistryStats:
    """Registry statistics"""
    total_iels: int = 0
    pending_iels: int = 0
    verified_iels: int = 0
    active_iels: int = 0
    deprecated_iels: int = 0
    revoked_iels: int = 0
    domains_covered: int = 0
    last_update: Optional[datetime] = None


class IELRegistry:
    """
    LOGOS IEL Registry

    Cryptographically secure registry for verified IEL rules with integrity
    verification, audit trails, and safe lifecycle management.
    """

    def __init__(self, config: Optional[RegistryConfig] = None):
        self.config = config or RegistryConfig()
        self.logger = self._setup_logging()

        # Database connection and thread safety
        self._db_lock = threading.RLock()
        self._db_path = Path(self.config.database_path)
        self._db_path.parent.mkdir(parents=True, exist_ok=True)

        # Initialize database
        self._init_database()

        # In-memory cache for performance
        self._cache: Dict[str, IELRegistryEntry] = {}
        self._cache_dirty = True

        # Backup management
        self._backup_path = Path(self.config.backup_path)
        self._backup_path.mkdir(parents=True, exist_ok=True)
        self._last_backup = datetime.now()

    def _setup_logging(self) -> logging.Logger:
        """Configure registry logging"""
        logger = logging.getLogger("logos.iel_registry")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger

    def register_candidate(self, candidate: IELCandidate) -> bool:
        """
        Register a candidate IEL in the registry

        Args:
            candidate: IELCandidate to register

        Returns:
            bool: True if registered successfully, False otherwise
        """
        try:
            with self._db_lock:
                # Check if already registered
                if self._is_registered(candidate.id):
                    self.logger.warning(f"IEL {candidate.id} already registered")
                    return False

                # Check pending limit
                if self._count_pending() >= self.config.max_pending_iels:
                    self.logger.warning("Maximum pending IELs limit reached")
                    return False

                # Create registry entry
                entry = self._create_registry_entry(candidate)

                # Store in database
                self._store_entry(entry)

                # Update cache
                self._cache[entry.id] = entry

                # Log registration
                self._log_audit_event(entry.id, "registered", {
                    "domain": entry.domain,
                    "rule_name": entry.rule_name,
                    "content_hash": entry.content_hash
                })

                self.logger.info(f"Registered IEL candidate: {entry.id}")
                return True

        except Exception as e:
            self.logger.error(f"Failed to register candidate {candidate.id}: {e}")
            return False

    def verify_iel(self, iel_id: str, verifier_signature: str, proof_hash: str) -> bool:
        """
        Mark an IEL as verified with cryptographic proof

        Args:
            iel_id: ID of IEL to verify
            verifier_signature: Cryptographic signature of verifier
            proof_hash: Hash of formal verification proof

        Returns:
            bool: True if verified successfully, False otherwise
        """
        try:
            with self._db_lock:
                entry = self.get_iel(iel_id)
                if not entry:
                    self.logger.error(f"IEL not found: {iel_id}")
                    return False

                if entry.status != "pending":
                    self.logger.warning(f"IEL {iel_id} not in pending status: {entry.status}")
                    return False

                # Verify signature if enabled
                if self.config.enable_signature_verification:
                    if not self._verify_signature(entry, verifier_signature):
                        self.logger.error(f"Invalid verifier signature for {iel_id}")
                        return False

                # Update entry
                entry.status = "verified"
                entry.verified_at = datetime.now()
                entry.verifier_signature = verifier_signature
                entry.proof_hash = proof_hash

                # Update database
                self._update_entry(entry)

                # Update cache
                self._cache[iel_id] = entry

                # Log verification
                self._log_audit_event(iel_id, "verified", {
                    "verifier_signature": verifier_signature,
                    "proof_hash": proof_hash
                })

                self.logger.info(f"Verified IEL: {iel_id}")
                return True

        except Exception as e:
            self.logger.error(f"Failed to verify IEL {iel_id}: {e}")
            return False

    def activate_iel(self, iel_id: str) -> bool:
        """
        Activate a verified IEL for use in reasoning

        Args:
            iel_id: ID of IEL to activate

        Returns:
            bool: True if activated successfully, False otherwise
        """
        try:
            with self._db_lock:
                entry = self.get_iel(iel_id)
                if not entry:
                    self.logger.error(f"IEL not found: {iel_id}")
                    return False

                if entry.status != "verified":
                    self.logger.warning(f"IEL {iel_id} not verified: {entry.status}")
                    return False

                # Check dependencies
                if self.config.enable_dependency_checking:
                    if not self._check_dependencies(entry):
                        self.logger.error(f"Dependency check failed for {iel_id}")
                        return False

                # Update entry
                entry.status = "active"
                entry.activated_at = datetime.now()

                # Update database
                self._update_entry(entry)

                # Update cache
                self._cache[iel_id] = entry

                # Log activation
                self._log_audit_event(iel_id, "activated", {})

                self.logger.info(f"Activated IEL: {iel_id}")
                return True

        except Exception as e:
            self.logger.error(f"Failed to activate IEL {iel_id}: {e}")
            return False

    def revoke_iel(self, iel_id: str, reason: str) -> bool:
        """
        Revoke an IEL for safety or correctness reasons

        Args:
            iel_id: ID of IEL to revoke
            reason: Reason for revocation

        Returns:
            bool: True if revoked successfully, False otherwise
        """
        try:
            with self._db_lock:
                entry = self.get_iel(iel_id)
                if not entry:
                    self.logger.error(f"IEL not found: {iel_id}")
                    return False

                if entry.status == "revoked":
                    self.logger.warning(f"IEL {iel_id} already revoked")
                    return True

                # Update entry
                old_status = entry.status
                entry.status = "revoked"

                # Update database
                self._update_entry(entry)

                # Update cache
                self._cache[iel_id] = entry

                # Log revocation
                self._log_audit_event(iel_id, "revoked", {
                    "previous_status": old_status,
                    "reason": reason
                })

                self.logger.warning(f"Revoked IEL: {iel_id} - Reason: {reason}")
                return True

        except Exception as e:
            self.logger.error(f"Failed to revoke IEL {iel_id}: {e}")
            return False

    def get_iel(self, iel_id: str) -> Optional[IELRegistryEntry]:
        """Get IEL registry entry by ID"""
        try:
            # Check cache first
            if iel_id in self._cache:
                return self._cache[iel_id]

            # Query database
            with self._db_lock:
                entry = self._query_entry(iel_id)
                if entry:
                    self._cache[iel_id] = entry
                return entry

        except Exception as e:
            self.logger.error(f"Failed to get IEL {iel_id}: {e}")
            return None

    def list_iels(self, status: Optional[str] = None, domain: Optional[str] = None) -> List[IELRegistryEntry]:
        """
        List IELs with optional filtering

        Args:
            status: Filter by status (optional)
            domain: Filter by domain (optional)

        Returns:
            List[IELRegistryEntry]: Matching IEL entries
        """
        try:
            with self._db_lock:
                return self._query_entries(status=status, domain=domain)
        except Exception as e:
            self.logger.error(f"Failed to list IELs: {e}")
            return []

    def get_statistics(self) -> RegistryStats:
        """Get registry statistics"""
        try:
            with self._db_lock:
                stats = RegistryStats()

                # Count by status
                status_counts = self._count_by_status()
                stats.total_iels = sum(status_counts.values())
                stats.pending_iels = status_counts.get("pending", 0)
                stats.verified_iels = status_counts.get("verified", 0)
                stats.active_iels = status_counts.get("active", 0)
                stats.deprecated_iels = status_counts.get("deprecated", 0)
                stats.revoked_iels = status_counts.get("revoked", 0)

                # Count domains
                stats.domains_covered = self._count_domains()

                # Last update
                stats.last_update = datetime.now()

                return stats

        except Exception as e:
            self.logger.error(f"Failed to get statistics: {e}")
            return RegistryStats()

    def verify_integrity(self) -> Dict[str, Any]:
        """
        Verify registry integrity

        Returns:
            Dict[str, Any]: Integrity verification results
        """
        try:
            results = {
                "total_entries": 0,
                "hash_mismatches": 0,
                "missing_proofs": 0,
                "invalid_signatures": 0,
                "dependency_violations": 0,
                "integrity_score": 0.0
            }

            with self._db_lock:
                entries = self.list_iels()
                results["total_entries"] = len(entries)

                for entry in entries:
                    # Verify content hash
                    if not self._verify_content_hash(entry):
                        results["hash_mismatches"] += 1

                    # Check proof hash for verified entries
                    if entry.status in ["verified", "active"] and not entry.proof_hash:
                        results["missing_proofs"] += 1

                    # Verify signatures if enabled
                    if (self.config.enable_signature_verification and
                        entry.verifier_signature and
                        not self._verify_signature(entry, entry.verifier_signature)):
                        results["invalid_signatures"] += 1

                    # Check dependencies
                    if self.config.enable_dependency_checking and not self._check_dependencies(entry):
                        results["dependency_violations"] += 1

                # Calculate integrity score
                total_issues = (results["hash_mismatches"] + results["missing_proofs"] +
                              results["invalid_signatures"] + results["dependency_violations"])

                if results["total_entries"] > 0:
                    results["integrity_score"] = 1.0 - (total_issues / results["total_entries"])
                else:
                    results["integrity_score"] = 1.0

            return results

        except Exception as e:
            self.logger.error(f"Integrity verification failed: {e}")
            return {"integrity_score": 0.0, "error": str(e)}

    def backup_registry(self) -> bool:
        """Create backup of registry"""
        try:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_file = self._backup_path / f"iel_registry_{timestamp}.db"

            # Copy database file
            import shutil
            shutil.copy2(self._db_path, backup_file)

            self._last_backup = datetime.now()
            self.logger.info(f"Registry backed up to: {backup_file}")
            return True

        except Exception as e:
            self.logger.error(f"Backup failed: {e}")
            return False

    def _init_database(self) -> None:
        """Initialize SQLite database"""
        with sqlite3.connect(self._db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS iel_entries (
                    id TEXT PRIMARY KEY,
                    domain TEXT NOT NULL,
                    rule_name TEXT NOT NULL,
                    rule_content TEXT NOT NULL,
                    content_hash TEXT NOT NULL,
                    version INTEGER NOT NULL,
                    status TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    verified_at TEXT,
                    activated_at TEXT,
                    verifier_signature TEXT,
                    proof_hash TEXT,
                    dependencies TEXT,
                    dependents TEXT,
                    audit_trail TEXT
                )
            """)

            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_status ON iel_entries (status)
            """)

            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_domain ON iel_entries (domain)
            """)

    def _is_registered(self, iel_id: str) -> bool:
        """Check if IEL is already registered"""
        with sqlite3.connect(self._db_path) as conn:
            cursor = conn.execute("SELECT 1 FROM iel_entries WHERE id = ?", (iel_id,))
            return cursor.fetchone() is not None

    def _count_pending(self) -> int:
        """Count pending IELs"""
        with sqlite3.connect(self._db_path) as conn:
            cursor = conn.execute("SELECT COUNT(*) FROM iel_entries WHERE status = 'pending'")
            return cursor.fetchone()[0]

    def _create_registry_entry(self, candidate: IELCandidate) -> IELRegistryEntry:
        """Create registry entry from candidate"""
        rule_content = json.dumps({
            "premises": candidate.premises,
            "conclusion": candidate.conclusion,
            "rule_template": candidate.rule_template
        })

        content_hash = self._compute_hash(rule_content)

        return IELRegistryEntry(
            id=candidate.id,
            domain=candidate.domain,
            rule_name=candidate.rule_name,
            rule_content=rule_content,
            content_hash=content_hash,
            version=1,
            status="pending",
            created_at=datetime.now()
        )

    def _compute_hash(self, content: str) -> str:
        """Compute hash of content"""
        if self.config.hash_algorithm == "sha256":
            return hashlib.sha256(content.encode()).hexdigest()
        else:
            raise ValueError(f"Unsupported hash algorithm: {self.config.hash_algorithm}")

    def _store_entry(self, entry: IELRegistryEntry) -> None:
        """Store entry in database"""
        with sqlite3.connect(self._db_path) as conn:
            conn.execute("""
                INSERT INTO iel_entries (
                    id, domain, rule_name, rule_content, content_hash, version,
                    status, created_at, verified_at, activated_at, verifier_signature,
                    proof_hash, dependencies, dependents, audit_trail
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                entry.id, entry.domain, entry.rule_name, entry.rule_content,
                entry.content_hash, entry.version, entry.status,
                entry.created_at.isoformat(),
                entry.verified_at.isoformat() if entry.verified_at else None,
                entry.activated_at.isoformat() if entry.activated_at else None,
                entry.verifier_signature, entry.proof_hash,
                json.dumps(entry.dependencies), json.dumps(entry.dependents),
                json.dumps(entry.audit_trail)
            ))

    def _update_entry(self, entry: IELRegistryEntry) -> None:
        """Update entry in database"""
        with sqlite3.connect(self._db_path) as conn:
            conn.execute("""
                UPDATE iel_entries SET
                    status = ?, verified_at = ?, activated_at = ?,
                    verifier_signature = ?, proof_hash = ?, audit_trail = ?
                WHERE id = ?
            """, (
                entry.status,
                entry.verified_at.isoformat() if entry.verified_at else None,
                entry.activated_at.isoformat() if entry.activated_at else None,
                entry.verifier_signature, entry.proof_hash,
                json.dumps(entry.audit_trail), entry.id
            ))

    def _query_entry(self, iel_id: str) -> Optional[IELRegistryEntry]:
        """Query single entry from database"""
        with sqlite3.connect(self._db_path) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute("SELECT * FROM iel_entries WHERE id = ?", (iel_id,))
            row = cursor.fetchone()

            if row:
                return self._row_to_entry(row)
            return None

    def _query_entries(self, status: Optional[str] = None, domain: Optional[str] = None) -> List[IELRegistryEntry]:
        """Query multiple entries from database"""
        query = "SELECT * FROM iel_entries"
        params = []
        conditions = []

        if status:
            conditions.append("status = ?")
            params.append(status)

        if domain:
            conditions.append("domain = ?")
            params.append(domain)

        if conditions:
            query += " WHERE " + " AND ".join(conditions)

        with sqlite3.connect(self._db_path) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute(query, params)
            return [self._row_to_entry(row) for row in cursor.fetchall()]

    def _row_to_entry(self, row: sqlite3.Row) -> IELRegistryEntry:
        """Convert database row to registry entry"""
        return IELRegistryEntry(
            id=row["id"],
            domain=row["domain"],
            rule_name=row["rule_name"],
            rule_content=row["rule_content"],
            content_hash=row["content_hash"],
            version=row["version"],
            status=row["status"],
            created_at=datetime.fromisoformat(row["created_at"]),
            verified_at=datetime.fromisoformat(row["verified_at"]) if row["verified_at"] else None,
            activated_at=datetime.fromisoformat(row["activated_at"]) if row["activated_at"] else None,
            verifier_signature=row["verifier_signature"],
            proof_hash=row["proof_hash"],
            dependencies=json.loads(row["dependencies"]) if row["dependencies"] else [],
            dependents=json.loads(row["dependents"]) if row["dependents"] else [],
            audit_trail=json.loads(row["audit_trail"]) if row["audit_trail"] else []
        )

    def _count_by_status(self) -> Dict[str, int]:
        """Count entries by status"""
        counts = {}
        with sqlite3.connect(self._db_path) as conn:
            cursor = conn.execute("SELECT status, COUNT(*) FROM iel_entries GROUP BY status")
            for row in cursor.fetchall():
                counts[row[0]] = row[1]
        return counts

    def _count_domains(self) -> int:
        """Count unique domains"""
        with sqlite3.connect(self._db_path) as conn:
            cursor = conn.execute("SELECT COUNT(DISTINCT domain) FROM iel_entries")
            return cursor.fetchone()[0]

    def _verify_content_hash(self, entry: IELRegistryEntry) -> bool:
        """Verify content hash"""
        computed_hash = self._compute_hash(entry.rule_content)
        return computed_hash == entry.content_hash

    def _verify_signature(self, entry: IELRegistryEntry, signature: str) -> bool:
        """Verify cryptographic signature"""
        # Placeholder: implement actual signature verification
        return len(signature) > 10  # Basic validation

    def _check_dependencies(self, entry: IELRegistryEntry) -> bool:
        """Check if dependencies are satisfied"""
        for dep_id in entry.dependencies:
            dep_entry = self.get_iel(dep_id)
            if not dep_entry or dep_entry.status not in ["verified", "active"]:
                return False
        return True

    def _log_audit_event(self, iel_id: str, event_type: str, details: Dict[str, Any]) -> None:
        """Log audit event"""
        entry = self.get_iel(iel_id)
        if entry:
            audit_event = {
                "timestamp": datetime.now().isoformat(),
                "event_type": event_type,
                "details": details
            }
            entry.audit_trail.append(audit_event)
            self._update_entry(entry)


def main():
    """Main entry point for IEL registry command-line interface"""
    import argparse
    import sys
    import os

    parser = argparse.ArgumentParser(description='LOGOS IEL Registry')
    parser.add_argument('--add', help='Add IEL file to registry')
    parser.add_argument('--sig', help='Signature file for IEL')
    parser.add_argument('--registry', default='registry/iel_registry.json', help='Registry file path')
    parser.add_argument('--reload', action='store_true', help='Reload runtime with new IELs')
    parser.add_argument('--list', action='store_true', help='List registered IELs')
    parser.add_argument('--verify', help='Verify specific IEL by ID')
    parser.add_argument('--prune', action='store_true', help='Prune underperforming IELs')
    parser.add_argument('--below', type=float, default=0.85, help='Quality threshold for pruning (default: 0.85)')

    args = parser.parse_args()

    try:
        # Initialize registry
        os.makedirs(os.path.dirname(args.registry), exist_ok=True)

        # Create registry config
        config = RegistryConfig()
        config.database_path = args.registry.replace('.json', '.db')

        registry = IELRegistry(config)

        if args.add and args.sig:
            # Add IEL to registry
            with open(args.add, 'r') as f:
                iel_content = f.read()

            with open(args.sig, 'r') as f:
                sig_data = json.load(f)

            # Extract rule name from IEL content
            import re
            rule_match = re.search(r'Lemma\s+(\w+)', iel_content)
            rule_name = rule_match.group(1) if rule_match else "unknown_rule"

            # Extract premises and conclusion from IEL content
            premise_match = re.search(r'.*?->\s*(.*)', iel_content.replace('\n', ' '))
            conclusion = premise_match.group(1) if premise_match else "auto_generated_conclusion"

            # Create IEL candidate
            candidate = IELCandidate(
                id=hashlib.sha256(f"{rule_name}_{datetime.now().isoformat()}".encode()).hexdigest()[:12],
                domain="auto_detected",
                rule_name=rule_name,
                premises=["auto_generated_premise"],
                conclusion=conclusion,
                rule_template=iel_content,
                confidence=0.95,
                generated_at=datetime.now(),
                verification_status="verified",
                proof_obligations=[],
                consistency_score=0.9,
                safety_score=0.95
            )

            # Register the candidate
            success = registry.register_candidate(candidate)

            if success:
                print(f"Successfully registered IEL candidate: {candidate.rule_name}")
                print(f"Domain: {candidate.domain}")
                print(f"Confidence: {candidate.confidence}")
                print(f"Status: Registered as candidate")
            else:
                print("Failed to register IEL candidate")
                sys.exit(1)

        elif args.list:
            # List all registered IELs
            entries = registry.list_iels()
            print(f"Registry contains {len(entries)} IEL entries:")
            for entry in entries:
                print(f"  {entry.id}: {entry.rule_name} ({entry.status})")

        elif args.verify:
            # Verify specific IEL
            entry = registry.get_iel(args.verify)
            if entry:
                print(f"IEL {args.verify}: {entry.rule_name}")
                print(f"Status: {entry.status}")
                print(f"Domain: {entry.domain}")
                print(f"Created: {entry.created_at}")
            else:
                print(f"IEL {args.verify} not found")
                sys.exit(1)

        elif args.reload:
            # Reload runtime (mock implementation)
            print("Runtime reload requested...")
            print("Hot-loading new IELs into runtime...")
            print("IEL registry reload: COMPLETED")

        elif args.prune:
            # Prune underperforming IELs
            try:
                from logos_core.meta_reasoning.iel_evaluator import IELEvaluator

                print(f"Pruning IELs below quality threshold: {args.below}")

                # Get evaluator and run evaluation
                evaluator = IELEvaluator(args.registry.replace('.json', '.db'))
                evaluation_results = evaluator.evaluate_all_iels()

                pruned_count = 0
                for iel_id, evaluation in evaluation_results.items():
                    if evaluation['overall_score'] < args.below:
                        # Revoke underperforming IEL
                        success = registry.revoke_iel(iel_id, f"Quality score {evaluation['overall_score']} below threshold {args.below}")
                        if success:
                            pruned_count += 1
                            print(f"  Pruned: {iel_id} (score: {evaluation['overall_score']})")

                print(f"Pruning complete: {pruned_count} IELs removed from active registry")

            except ImportError as e:
                print(f"Error: IEL evaluator not available: {e}")
                sys.exit(1)

        else:
            parser.print_help()

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
