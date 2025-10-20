"""
LOGOS AGI v1.0 Daemon Module

Passive background verification and autonomous reasoning gap detection.
Maintains continuous coherence validation while preserving formal verification guarantees.
"""

from .logos_daemon import LogosDaemon
from .gap_detector import GapDetector

__all__ = ['LogosDaemon', 'GapDetector']
