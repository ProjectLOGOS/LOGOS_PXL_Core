"""
LOGOS AGI v1.0 Governance Module

Signs verified IELs and enforces policy for autonomous reasoning safety.
Provides cryptographic governance layer for AGI enhancement while preserving 
formal verification guarantees.
"""

from .iel_signer import IELSigner
from .policy import PolicyManager

__all__ = ['IELSigner', 'PolicyManager']