"""
Multi-Agent LOGOS System - Distributed Reasoning and Communication

This module enables LOGOS instances to form distributed reasoning networks,
sharing IELs, coordinating problem-solving, and building consensus across
multiple autonomous agents.

Components:
- agent_communication: Agent discovery, trust management, secure communication
- iel_sync_protocol: Cryptographically signed IEL exchange and conflict resolution

Part of the LOGOS AGI v1.0 multi-agent reasoning framework.
"""

from .agent_communication import (
    AgentCommunicationManager,
    AgentNode,
    AgentCapabilities,
    TrustMetrics,
    get_global_comm_manager,
    set_global_comm_manager
)

from .iel_sync_protocol import (
    IELSyncProtocol,
    SignedIEL,
    IELSignature,
    SyncMode,
    ConflictResolution,
    get_global_sync_protocol,
    set_global_sync_protocol
)

__all__ = [
    'AgentCommunicationManager',
    'AgentNode',
    'AgentCapabilities',
    'TrustMetrics',
    'IELSyncProtocol',
    'SignedIEL',
    'IELSignature',
    'SyncMode',
    'ConflictResolution',
    'get_global_comm_manager',
    'set_global_comm_manager',
    'get_global_sync_protocol',
    'set_global_sync_protocol'
]
