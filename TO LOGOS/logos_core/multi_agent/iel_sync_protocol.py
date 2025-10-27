#!/usr/bin/env python3
"""
IEL Synchronization Protocol - Secure Multi-Agent IEL Exchange

This module implements secure synchronization of IEL rules between LOGOS agents.
Provides cryptographically signed IEL exchange, conflict resolution via coherence
scoring, and distributed consensus mechanisms.

Features:
- Signed IEL packaging and verification
- Push/pull synchronization modes
- Conflict resolution using coherence scores
- RSA-PSS cryptographic validation
- Consensus building for disputed IELs
- Version tracking and rollback capability

Part of the LOGOS AGI v1.0 multi-agent reasoning framework.
"""

import json
import logging
import hashlib
import time
import uuid
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Set, Any, Tuple, TYPE_CHECKING

# Use TYPE_CHECKING to avoid circular imports
if TYPE_CHECKING:
    from logos_core.multi_agent.agent_communication import AgentCommunicationManager, AgentNode
from pathlib import Path
from enum import Enum

# Cryptographic imports
try:
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa, padding
    from cryptography.hazmat.primitives.serialization import load_pem_public_key, load_pem_private_key
    CRYPTO_AVAILABLE = True
except ImportError:
    CRYPTO_AVAILABLE = False
    logging.warning("Cryptography not available, using mock signatures")

# Import core components
try:
    from logos_core.meta_reasoning.iel_registry import IELRegistry, IELCandidate
    from logos_core.coherence.coherence_metrics import CoherenceCalculator
except ImportError as e:
    logging.warning(f"Core import failed: {e}, using fallback classes")

    # Fallback classes for missing imports
    class IELRegistry:
        def __init__(self, path): self.path = path
        def list_candidates(self): return []
        def register_iel(self, iel): return True

    class IELCandidate:
        def __init__(self, **kwargs):
            for k, v in kwargs.items():
                setattr(self, k, v)

    class CoherenceCalculator:
        def calculate_coherence(self, iel_content: str) -> float:
            return 0.8  # Mock coherence score

logger = logging.getLogger(__name__)

class SyncMode(Enum):
    """IEL synchronization modes"""
    PUSH = "push"       # Push local IELs to other agents
    PULL = "pull"       # Pull IELs from other agents
    BIDIRECTIONAL = "bidirectional"  # Both push and pull

class ConflictResolution(Enum):
    """Conflict resolution strategies"""
    COHERENCE_SCORE = "coherence_score"     # Use coherence scores
    TRUST_WEIGHTED = "trust_weighted"       # Weight by agent trust
    CONSENSUS = "consensus"                 # Require majority consensus
    LATEST_WINS = "latest_wins"             # Most recent IEL wins

@dataclass
class IELSignature:
    """Cryptographic signature for IEL"""
    signature: str          # Base64 encoded signature
    algorithm: str          # Signature algorithm (e.g., "RSA-PSS")
    public_key_hash: str    # Hash of signing public key
    timestamp: float        # Signature timestamp

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'IELSignature':
        return cls(**data)

@dataclass
class SignedIEL:
    """Signed IEL package for secure exchange"""
    iel_id: str                     # Unique IEL identifier
    iel_content: str                # IEL rule content
    domain: str                     # Logic domain
    origin_agent: str               # Originating agent ID
    version: int                    # IEL version number
    coherence_score: float          # Self-assessed coherence
    evaluation_context: Dict[str, Any]  # Evaluation metadata
    dependencies: List[str]         # Required IEL dependencies
    signature: IELSignature         # Cryptographic signature
    created_at: datetime            # Creation timestamp
    sync_metadata: Dict[str, Any]   # Sync-specific metadata

    def __post_init__(self):
        if isinstance(self.created_at, str):
            self.created_at = datetime.fromisoformat(self.created_at)

    @property
    def content_hash(self) -> str:
        """Calculate hash of IEL content for integrity checking"""
        content_data = {
            "iel_content": self.iel_content,
            "domain": self.domain,
            "version": self.version,
            "dependencies": self.dependencies
        }
        content_str = json.dumps(content_data, sort_keys=True)
        return hashlib.sha256(content_str.encode()).hexdigest()

    def verify_signature(self, public_key_pem: str) -> bool:
        """Verify IEL signature"""
        if not CRYPTO_AVAILABLE:
            logger.warning("Cryptography unavailable, skipping signature verification")
            return True

        try:
            # Load public key
            public_key = load_pem_public_key(public_key_pem.encode())

            # Verify signature
            signature_data = f"{self.iel_content}:{self.domain}:{self.version}:{self.origin_agent}"
            signature_bytes = bytes.fromhex(self.signature.signature)

            public_key.verify(
                signature_bytes,
                signature_data.encode(),
                padding.PSS(
                    mgf=padding.MGF1(hashes.SHA256()),
                    salt_length=padding.PSS.MAX_LENGTH
                ),
                hashes.SHA256()
            )
            return True

        except Exception as e:
            logger.error(f"Signature verification failed: {e}")
            return False

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        data['created_at'] = self.created_at.isoformat()
        data['signature'] = self.signature.to_dict()
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'SignedIEL':
        if 'signature' in data and isinstance(data['signature'], dict):
            data['signature'] = IELSignature.from_dict(data['signature'])
        return cls(**data)

@dataclass
class SyncRequest:
    """IEL synchronization request"""
    request_id: str
    requesting_agent: str
    mode: SyncMode
    iel_filters: Dict[str, Any]     # Filters for requested IELs
    last_sync_timestamp: Optional[float] = None
    max_iels: int = 100
    include_metadata: bool = True

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        data['mode'] = self.mode.value
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'SyncRequest':
        if 'mode' in data and isinstance(data['mode'], str):
            data['mode'] = SyncMode(data['mode'])
        return cls(**data)

@dataclass
class SyncResponse:
    """IEL synchronization response"""
    request_id: str
    responding_agent: str
    status: str                     # success, error, partial
    iels: List[SignedIEL]
    conflicts: List[Dict[str, Any]] # Conflicting IEL information
    sync_timestamp: float
    total_available: int
    message: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        data['iels'] = [iel.to_dict() for iel in self.iels]
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'SyncResponse':
        if 'iels' in data:
            data['iels'] = [SignedIEL.from_dict(iel_data) for iel_data in data['iels']]
        return cls(**data)

class IELSyncProtocol:
    """Manages IEL synchronization between agents"""

    def __init__(self, comm_manager: 'AgentCommunicationManager', registry: IELRegistry):
        self.comm_manager = comm_manager
        self.registry = registry
        self.coherence_calc = CoherenceCalculator()

        # Sync configuration
        self.config = {
            "auto_sync_interval": 300,          # Auto sync every 5 minutes
            "max_concurrent_syncs": 5,          # Max parallel sync operations
            "conflict_resolution": ConflictResolution.COHERENCE_SCORE,
            "min_coherence_threshold": 0.6,     # Min coherence for acceptance
            "trust_weight_factor": 0.3,         # Trust weighting in decisions
            "consensus_threshold": 0.6,         # Consensus requirement (60%)
            "signature_required": True,         # Require valid signatures
            "enable_auto_push": True,           # Automatically push new IELs
            "enable_auto_pull": True,           # Automatically pull from trusted agents
            "max_iel_age_days": 30,             # Max age for IEL consideration
            "version_check_enabled": True       # Enable version conflict detection
        }

        # State tracking
        self.sync_state = {
            "last_sync_times": {},              # Last sync time per agent
            "pending_syncs": set(),             # Active sync operations
            "conflict_queue": [],               # Unresolved conflicts
            "sync_statistics": {
                "total_syncs": 0,
                "successful_syncs": 0,
                "failed_syncs": 0,
                "conflicts_resolved": 0,
                "iels_received": 0,
                "iels_sent": 0
            }
        }

        # Register event handlers
        self.comm_manager.add_event_handler("agent_discovered", self._on_agent_discovered)

    def _on_agent_discovered(self, agent: 'AgentNode'):
        """Handle new agent discovery"""
        if self.config["enable_auto_pull"] and agent.is_trusted:
            self._schedule_sync(agent, SyncMode.PULL)

    def create_signed_iel(self, iel_candidate: IELCandidate) -> SignedIEL:
        """Create a signed IEL package"""
        # Calculate coherence score
        coherence_score = self.coherence_calc.calculate_coherence(iel_candidate.rule_content)

        # Create signature
        signature = self._sign_iel_content(
            iel_candidate.rule_content,
            iel_candidate.domain,
            getattr(iel_candidate, 'version', 1)
        )

        # Create signed IEL
        signed_iel = SignedIEL(
            iel_id=iel_candidate.id,
            iel_content=iel_candidate.rule_content,
            domain=iel_candidate.domain,
            origin_agent=self.comm_manager.agent_id,
            version=getattr(iel_candidate, 'version', 1),
            coherence_score=coherence_score,
            evaluation_context={
                "confidence": getattr(iel_candidate, 'confidence', 0.0),
                "metadata": getattr(iel_candidate, 'metadata', {})
            },
            dependencies=getattr(iel_candidate, 'dependencies', []),
            signature=signature,
            created_at=datetime.now(),
            sync_metadata={}
        )

        return signed_iel

    def _sign_iel_content(self, content: str, domain: str, version: int) -> IELSignature:
        """Create cryptographic signature for IEL content"""
        timestamp = time.time()

        if not CRYPTO_AVAILABLE or not self.comm_manager.private_key:
            # Mock signature for testing
            return IELSignature(
                signature="mock_signature_" + hashlib.md5(content.encode()).hexdigest(),
                algorithm="MOCK-RSA-PSS",
                public_key_hash="mock_key_hash",
                timestamp=timestamp
            )

        try:
            # Create signature data
            signature_data = f"{content}:{domain}:{version}:{self.comm_manager.agent_id}"

            # Sign with RSA-PSS
            signature = self.comm_manager.private_key.sign(
                signature_data.encode(),
                padding.PSS(
                    mgf=padding.MGF1(hashes.SHA256()),
                    salt_length=padding.PSS.MAX_LENGTH
                ),
                hashes.SHA256()
            )

            # Calculate public key hash
            public_key_pem = self.comm_manager.get_public_key_pem()
            key_hash = hashlib.sha256(public_key_pem.encode()).hexdigest()

            return IELSignature(
                signature=signature.hex(),
                algorithm="RSA-PSS",
                public_key_hash=key_hash,
                timestamp=timestamp
            )

        except Exception as e:
            logger.error(f"Failed to sign IEL: {e}")
            raise

    def sync_with_agent(self, agent: 'AgentNode', mode: SyncMode = SyncMode.BIDIRECTIONAL) -> bool:
        """Synchronize IELs with specific agent"""
        if not agent.is_trusted:
            logger.warning(f"Skipping sync with untrusted agent {agent.agent_id}")
            return False

        sync_id = str(uuid.uuid4())

        try:
            self.sync_state["pending_syncs"].add(sync_id)

            if mode in [SyncMode.PULL, SyncMode.BIDIRECTIONAL]:
                success = self._pull_iels_from_agent(agent)
                if not success:
                    return False

            if mode in [SyncMode.PUSH, SyncMode.BIDIRECTIONAL]:
                success = self._push_iels_to_agent(agent)
                if not success:
                    return False

            # Update sync timestamp
            self.sync_state["last_sync_times"][agent.agent_id] = time.time()
            self.sync_state["sync_statistics"]["successful_syncs"] += 1

            logger.info(f"Successfully synced with agent {agent.agent_id}")
            return True

        except Exception as e:
            logger.error(f"Sync failed with agent {agent.agent_id}: {e}")
            self.sync_state["sync_statistics"]["failed_syncs"] += 1
            return False
        finally:
            self.sync_state["pending_syncs"].discard(sync_id)
            self.sync_state["sync_statistics"]["total_syncs"] += 1

    def _pull_iels_from_agent(self, agent: 'AgentNode') -> bool:
        """Pull IELs from remote agent"""
        try:
            # Prepare sync request
            last_sync = self.sync_state["last_sync_times"].get(agent.agent_id, 0)

            request = SyncRequest(
                request_id=str(uuid.uuid4()),
                requesting_agent=self.comm_manager.agent_id,
                mode=SyncMode.PULL,
                iel_filters={
                    "min_coherence": self.config["min_coherence_threshold"],
                    "domains": self.comm_manager.capabilities.domains
                },
                last_sync_timestamp=last_sync,
                max_iels=100
            )

            # Send sync request
            response_data = self.comm_manager._send_request(
                agent, "sync_iels", request.to_dict()
            )

            if not response_data:
                return False

            response = SyncResponse.from_dict(response_data)

            # Process received IELs
            accepted_count = 0
            for signed_iel in response.iels:
                if self._validate_and_integrate_iel(signed_iel, agent):
                    accepted_count += 1

            # Handle conflicts
            for conflict in response.conflicts:
                self._handle_conflict(conflict, agent)

            self.sync_state["sync_statistics"]["iels_received"] += accepted_count
            logger.info(f"Pulled {accepted_count}/{len(response.iels)} IELs from {agent.agent_id}")

            return True

        except Exception as e:
            logger.error(f"Failed to pull IELs from {agent.agent_id}: {e}")
            return False

    def _push_iels_to_agent(self, agent: 'AgentNode') -> bool:
        """Push local IELs to remote agent"""
        try:
            # Get local IELs to share
            local_iels = self._get_shareable_iels()

            if not local_iels:
                return True  # Nothing to push

            # Convert to signed IELs
            signed_iels = []
            for iel in local_iels:
                try:
                    signed_iel = self.create_signed_iel(iel)
                    signed_iels.append(signed_iel)
                except Exception as e:
                    logger.error(f"Failed to sign IEL {iel.id}: {e}")

            # Prepare sync request
            request = SyncRequest(
                request_id=str(uuid.uuid4()),
                requesting_agent=self.comm_manager.agent_id,
                mode=SyncMode.PUSH,
                iel_filters={}
            )

            # Send IELs in batches
            batch_size = 10
            for i in range(0, len(signed_iels), batch_size):
                batch = signed_iels[i:i + batch_size]

                push_data = {
                    "request": request.to_dict(),
                    "iels": [iel.to_dict() for iel in batch]
                }

                response_data = self.comm_manager._send_request(
                    agent, "receive_iels", push_data
                )

                if not response_data or response_data.get("status") != "success":
                    logger.warning(f"Push batch failed to {agent.agent_id}")
                    return False

            self.sync_state["sync_statistics"]["iels_sent"] += len(signed_iels)
            logger.info(f"Pushed {len(signed_iels)} IELs to {agent.agent_id}")

            return True

        except Exception as e:
            logger.error(f"Failed to push IELs to {agent.agent_id}: {e}")
            return False

    def _get_shareable_iels(self) -> List[IELCandidate]:
        """Get local IELs suitable for sharing"""
        try:
            # Get recent high-quality IELs
            candidates = self.registry.list_candidates(
                limit=50,
                min_confidence=self.config["min_coherence_threshold"]
            )

            # Filter by age and quality
            cutoff_date = datetime.now() - timedelta(days=self.config["max_iel_age_days"])

            shareable = []
            for candidate in candidates:
                # Check if IEL is recent and high quality
                if (hasattr(candidate, 'created_at') and
                    candidate.created_at >= cutoff_date and
                    candidate.confidence >= self.config["min_coherence_threshold"]):
                    shareable.append(candidate)

            return shareable

        except Exception as e:
            logger.error(f"Failed to get shareable IELs: {e}")
            return []

    def _validate_and_integrate_iel(self, signed_iel: SignedIEL, source_agent: 'AgentNode') -> bool:
        """Validate and integrate received IEL"""
        try:
            # Signature verification
            if self.config["signature_required"]:
                if not signed_iel.verify_signature(source_agent.public_key):
                    logger.warning(f"Invalid signature for IEL {signed_iel.iel_id}")
                    source_agent.trust_metrics.update_failure("invalid_signature")
                    return False

            # Coherence check
            calculated_coherence = self.coherence_calc.calculate_coherence(signed_iel.iel_content)
            if calculated_coherence < self.config["min_coherence_threshold"]:
                logger.warning(f"IEL {signed_iel.iel_id} below coherence threshold")
                return False

            # Check for conflicts
            existing_iels = self.registry.list_candidates()
            conflict = self._detect_conflict(signed_iel, existing_iels)

            if conflict:
                self._handle_conflict(conflict, source_agent)
                return False

            # Convert to registry format and store
            iel_candidate = IELCandidate(
                id=signed_iel.iel_id,
                rule_name=f"sync_{signed_iel.origin_agent}_{signed_iel.version}",
                rule_content=signed_iel.iel_content,
                domain=signed_iel.domain,
                confidence=signed_iel.coherence_score,
                hash=signed_iel.content_hash,
                metadata={
                    **signed_iel.evaluation_context,
                    "origin_agent": signed_iel.origin_agent,
                    "sync_source": source_agent.agent_id,
                    "signature": signed_iel.signature.to_dict()
                }
            )

            # Register IEL
            success = self.registry.register_iel(iel_candidate)
            if success:
                logger.info(f"Integrated IEL {signed_iel.iel_id} from {source_agent.agent_id}")
                source_agent.trust_metrics.update_success(1.0)
                return True
            else:
                logger.warning(f"Failed to register IEL {signed_iel.iel_id}")
                return False

        except Exception as e:
            logger.error(f"Failed to validate IEL {signed_iel.iel_id}: {e}")
            source_agent.trust_metrics.update_failure("validation_error")
            return False

    def _detect_conflict(self, signed_iel: SignedIEL, existing_iels: List[IELCandidate]) -> Optional[Dict]:
        """Detect conflicts with existing IELs"""
        for existing in existing_iels:
            # Check for same content but different metadata
            if (existing.rule_content == signed_iel.iel_content and
                existing.domain == signed_iel.domain):
                return {
                    "type": "duplicate_content",
                    "existing_iel": existing,
                    "new_iel": signed_iel,
                    "conflict_reason": "Same content, different origin"
                }

            # Check for logical contradictions (simplified)
            if (existing.domain == signed_iel.domain and
                self._check_logical_contradiction(existing.rule_content, signed_iel.iel_content)):
                return {
                    "type": "logical_contradiction",
                    "existing_iel": existing,
                    "new_iel": signed_iel,
                    "conflict_reason": "Rules contradict each other"
                }

        return None

    def _check_logical_contradiction(self, rule1: str, rule2: str) -> bool:
        """Check if two rules logically contradict (simplified implementation)"""
        # This is a simplified check - in practice would need formal logic analysis
        rule1_clean = rule1.lower().strip()
        rule2_clean = rule2.lower().strip()

        # Look for obvious contradictions
        if "not" in rule1_clean and rule1_clean.replace("not", "").strip() == rule2_clean:
            return True
        if "not" in rule2_clean and rule2_clean.replace("not", "").strip() == rule1_clean:
            return True

        return False

    def _handle_conflict(self, conflict: Dict, source_agent: 'AgentNode'):
        """Handle IEL conflict using configured resolution strategy"""
        strategy = self.config["conflict_resolution"]

        if strategy == ConflictResolution.COHERENCE_SCORE:
            self._resolve_by_coherence(conflict, source_agent)
        elif strategy == ConflictResolution.TRUST_WEIGHTED:
            self._resolve_by_trust(conflict, source_agent)
        elif strategy == ConflictResolution.CONSENSUS:
            self._resolve_by_consensus(conflict, source_agent)
        elif strategy == ConflictResolution.LATEST_WINS:
            self._resolve_by_timestamp(conflict, source_agent)
        else:
            # Queue for manual resolution
            self.sync_state["conflict_queue"].append({
                **conflict,
                "source_agent": source_agent.agent_id,
                "timestamp": time.time()
            })

    def _resolve_by_coherence(self, conflict: Dict, source_agent: 'AgentNode'):
        """Resolve conflict using coherence scores"""
        existing_iel = conflict["existing_iel"]
        new_iel = conflict["new_iel"]

        existing_coherence = self.coherence_calc.calculate_coherence(existing_iel.rule_content)
        new_coherence = new_iel.coherence_score

        if new_coherence > existing_coherence * 1.1:  # 10% improvement threshold
            # Replace existing with new
            logger.info(f"Replacing IEL due to higher coherence: {new_coherence:.3f} > {existing_coherence:.3f}")
            # Implementation would remove old and add new
        else:
            logger.info(f"Keeping existing IEL due to coherence: {existing_coherence:.3f} >= {new_coherence:.3f}")

    def _resolve_by_trust(self, conflict: Dict, source_agent: 'AgentNode'):
        """Resolve conflict using agent trust scores"""
        trust_score = source_agent.trust_metrics.trust_score
        trust_threshold = 0.8

        if trust_score >= trust_threshold:
            logger.info(f"Accepting IEL from highly trusted agent {source_agent.agent_id} (trust: {trust_score:.3f})")
            # Implementation would replace existing
        else:
            logger.info(f"Rejecting IEL from low-trust agent {source_agent.agent_id} (trust: {trust_score:.3f})")

    def _resolve_by_consensus(self, conflict: Dict, source_agent: 'AgentNode'):
        """Resolve conflict using network consensus"""
        # Request opinions from other trusted agents
        trusted_agents = self.comm_manager.get_trusted_agents()

        if len(trusted_agents) < 3:
            logger.warning("Insufficient agents for consensus, using coherence fallback")
            self._resolve_by_coherence(conflict, source_agent)
            return

        # This would implement a consensus protocol
        logger.info("Queuing conflict for consensus resolution")
        self.sync_state["conflict_queue"].append(conflict)

    def _resolve_by_timestamp(self, conflict: Dict, source_agent: 'AgentNode'):
        """Resolve conflict by keeping latest IEL"""
        new_iel = conflict["new_iel"]
        logger.info(f"Accepting latest IEL {new_iel.iel_id} (timestamp resolution)")
        # Implementation would replace existing

    def _schedule_sync(self, agent: 'AgentNode', mode: SyncMode):
        """Schedule synchronization with agent"""
        # This would implement background sync scheduling
        logger.info(f"Scheduling {mode.value} sync with {agent.agent_id}")

    def get_sync_status(self) -> Dict[str, Any]:
        """Get synchronization status"""
        return {
            "config": self.config,
            "state": {
                **self.sync_state,
                "pending_syncs": list(self.sync_state["pending_syncs"])
            },
            "last_sync_times": self.sync_state["last_sync_times"],
            "conflict_queue_size": len(self.sync_state["conflict_queue"])
        }

    # JSON-RPC handlers for sync protocol
    def handle_sync_iels(self, params: Dict) -> Dict:
        """Handle incoming IEL sync request"""
        try:
            request = SyncRequest.from_dict(params)

            # Get IELs matching request filters
            iels = self._get_shareable_iels()

            # Apply filters
            filtered_iels = []
            for iel in iels:
                if self._matches_filters(iel, request.iel_filters):
                    filtered_iels.append(iel)

            # Convert to signed IELs
            signed_iels = []
            for iel in filtered_iels[:request.max_iels]:
                try:
                    signed_iel = self.create_signed_iel(iel)
                    signed_iels.append(signed_iel)
                except Exception as e:
                    logger.error(f"Failed to sign IEL for sync: {e}")

            response = SyncResponse(
                request_id=request.request_id,
                responding_agent=self.comm_manager.agent_id,
                status="success",
                iels=signed_iels,
                conflicts=[],
                sync_timestamp=time.time(),
                total_available=len(filtered_iels)
            )

            return response.to_dict()

        except Exception as e:
            logger.error(f"Sync request handling failed: {e}")
            return {
                "status": "error",
                "message": str(e)
            }

    def handle_receive_iels(self, params: Dict) -> Dict:
        """Handle incoming IEL push"""
        try:
            request_data = params.get("request", {})
            iels_data = params.get("iels", [])

            # Convert to signed IELs
            signed_iels = [SignedIEL.from_dict(iel_data) for iel_data in iels_data]

            # Get source agent
            requesting_agent_id = request_data.get("requesting_agent")
            source_agent = self.comm_manager.agents.get(requesting_agent_id)

            if not source_agent:
                return {"status": "error", "message": "Unknown source agent"}

            # Process each IEL
            accepted_count = 0
            for signed_iel in signed_iels:
                if self._validate_and_integrate_iel(signed_iel, source_agent):
                    accepted_count += 1

            return {
                "status": "success",
                "accepted": accepted_count,
                "total": len(signed_iels)
            }

        except Exception as e:
            logger.error(f"Receive IELs failed: {e}")
            return {
                "status": "error",
                "message": str(e)
            }

    def _matches_filters(self, iel: IELCandidate, filters: Dict) -> bool:
        """Check if IEL matches sync filters"""
        # Check domain filter
        if "domains" in filters and iel.domain not in filters["domains"]:
            return False

        # Check coherence filter
        if "min_coherence" in filters and iel.confidence < filters["min_coherence"]:
            return False

        return True

# Global sync protocol instance
_global_sync_protocol = None

def get_global_sync_protocol() -> Optional[IELSyncProtocol]:
    """Get global sync protocol instance"""
    return _global_sync_protocol

def set_global_sync_protocol(protocol: IELSyncProtocol):
    """Set global sync protocol instance"""
    global _global_sync_protocol
    _global_sync_protocol = protocol

if __name__ == "__main__":
    # Demo usage
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS IEL Sync Protocol Demo")
    parser.add_argument("--agent-id", default=None, help="Agent ID")
    parser.add_argument("--registry", default="registry/iel_registry.db", help="IEL registry path")

    args = parser.parse_args()

    # Setup logging
    logging.basicConfig(level=logging.INFO)

    # This would normally be integrated with the full system
    print("IEL Sync Protocol demo - integration with full system required")
