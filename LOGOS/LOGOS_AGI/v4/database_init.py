# logos_agi_v1/services/database/__init__.py

"""
LOGOS AGI Database Service

This package provides the persistence layer for the LOGOS AGI system,
including ontological knowledge storage, goal management, and system logging.

Components:
- PersistenceManager: Low-level SQLite database operations
- DatabaseService: RabbitMQ message consumer and service orchestrator

The service handles:
- Ontological nodes with fractal positioning and trinity vectors
- AGI goals and their lifecycle management
- System event logging and monitoring
- Semantic glyph storage and retrieval
- Node relationship mapping

Database Schema:
- system_log: General system events and monitoring data
- goals: AGI goal definitions and status tracking
- nodes: Ontological knowledge nodes with spatial indexing
- relations: Relationships between ontological nodes
- semantic_glyphs: Complex semantic representations with fractal properties
"""

__version__ = "1.0.0"
__author__ = "LOGOS AGI Development Team"

from .persistence_manager import PersistenceManager
from .db_service import DatabaseService

__all__ = ["PersistenceManager", "DatabaseService"]
