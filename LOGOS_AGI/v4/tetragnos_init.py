# logos_agi_v1/subsystems/tetragnos/__init__.py

"""
TETRAGNOS - The Pattern Recognizer

Advanced pattern recognition, natural language processing, and semantic analysis
subsystem for the LOGOS AGI architecture.

Capabilities:
- Text clustering and semantic analysis
- Feature extraction from unstructured data
- Natural language to formal language translation
- Pattern recognition and classification
- Semantic similarity computation
- Dimensional reduction and visualization

This subsystem serves as the primary interface between natural language input
and the formal reasoning systems of TELOS and THONOC.
"""

__version__ = "1.0.0"
__author__ = "LOGOS AGI Development Team"
__subsystem__ = "TETRAGNOS"

from .tetragnos_worker import TetragnosWorker, TetragnosCoreEngine

__all__ = [
    "TetragnosWorker",
    "TetragnosCoreEngine"
]

# Subsystem metadata
SUBSYSTEM_INFO = {
    "name": "TETRAGNOS",
    "version": __version__,
    "description": "Pattern Recognition and Natural Language Processing",
    "capabilities": [
        "text_clustering",
        "feature_extraction",
        "semantic_analysis",
        "pattern_recognition",
        "language_translation",
        "similarity_computation"
    ],
    "input_queues": ["tetragnos_task_queue"],
    "output_queues": ["task_result_queue"],
    "dependencies": [
        "scikit-learn",
        "sentence-transformers",
        "numpy",
        "nltk"
    ]
}
