"""
ModalPraxis Domain: Modal Logic Praxis

This domain focuses on the praxis of modal logic and modalities:
- Modal operators (necessity, possibility, obligation)
- Modal logic systems (K, T, S4, S5)
- Multi-modal logics
- Temporal and deontic modalities
"""

from .modal_logic import ModalLogic
from .modal_reasoner import ModalReasoner
from .multi_modal_system import MultiModalSystem

__all__ = ['ModalLogic', 'ModalReasoner', 'MultiModalSystem']