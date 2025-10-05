# logos_agi_v1/subsystems/thonoc/__init__.py

"""
THONOC - The Logician

Formal reasoning, proof construction, and modal logic subsystem
for the LOGOS AGI architecture.

Capabilities:
- Formal proof construction and verification
- Modal logic reasoning (necessity, possibility, knowledge, belief)
- Lambda calculus evaluation and type checking
- Axiomatic system validation
- Logical consistency checking
- Theorem proving and mathematical reasoning
- Consequence assignment and moral reasoning

This subsystem provides the foundational logical and mathematical reasoning
capabilities that underpin all higher-order AGI functions.
"""

__version__ = "1.0.0"
__author__ = "LOGOS AGI Development Team"
__subsystem__ = "THONOC"

from .thonoc_worker import ThonocWorker, ThonocCoreEngine

__all__ = [
    "ThonocWorker", 
    "ThonocCoreEngine"
]

# Subsystem metadata
SUBSYSTEM_INFO = {
    "name": "THONOC",
    "version": __version__,
    "description": "Formal Logic and Mathematical Reasoning",
    "capabilities": [
        "proof_construction",
        "modal_reasoning",
        "lambda_evaluation",
        "consistency_checking",
        "theorem_proving",
        "consequence_assignment",
        "axiomatic_validation"
    ],
    "input_queues": ["thonoc_task_queue"],
    "output_queues": ["task_result_queue"],
    "dependencies": [
        "z3-solver",
        "sympy",
        "lark",
        "networkx",
        "pysmt"
    ]
}