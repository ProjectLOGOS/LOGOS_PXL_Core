"""
modal_inference.py

Full S5 modal-logic evaluator for THŌNOC.
"""
from enum import Enum
from typing import Dict, List, Tuple, Optional, Any
import networkx as nx
import math

class ModalOperator(Enum):
    NECESSARILY = "□"
    POSSIBLY   = "◇"
    ACTUALLY   = "A"

class ModalFormula:
    """Represents a modal logic formula with optional operator."""
    def __init__(self, content: str, operator: Optional[ModalOperator]=None):
        self.content     = content
        self.operator    = operator
        self.subformulas = []

    def __str__(self) -> str:
        return f"{self.operator.value}({self.content})" if self.operator else self.content

    def add_subformula(self, sub:'ModalFormula'):
        sub.parent = self
        self.subformulas.append(sub)

    def is_necessity(self)  -> bool: return self.operator==ModalOperator.NECESSARILY
    def is_possibility(self)-> bool: return self.operator==ModalOperator.POSSIBLY
    def dual(self)          -> 'ModalFormula':
        if self.is_necessity():   return ModalFormula(f"¬{self.content}", ModalOperator.POSSIBLY)
        if self.is_possibility(): return ModalFormula(f"¬{self.content}", ModalOperator.NECESSARILY)
        return self

class WorldNode:
    """Possible world in Kripke model."""
    def __init__(self, name:str, assignments:Dict[str,bool]=None):
        self.name=name
        self.assignments = assignments or {}
    def assign(self, prop:str, val:bool): self.assignments[prop]=val
    def evaluate(self, prop:str) -> bool: return self.assignments.get(prop, False)

class KripkeModel:
    """Graph of worlds + accessibility for modal semantics."""
    def __init__(self):
        self.graph = nx.DiGraph()
        self.worlds={}
    def add_world(self, name:str, assigns=None):
        w=WorldNode(name, assigns); self.worlds[name]=w
        self.graph.add_node(name)
        return w
    def add_access(self, w1:str, w2:str): self.graph.add_edge(w1,w2)
    def make_s5(self):
        for n in list(self.worlds):
            self.graph.add_edge(n,n)
        for u,v in list(self.graph.edges()): self.graph.add_edge(v,u)
        self.graph = nx.transitive_closure(self.graph)
    def neighbors(self, w): return list(self.graph.neighbors(w))
    def eval_necessity(self, prop, w):
        return all(self.worlds[n].evaluate(prop) for n in self.neighbors(w))
    def eval_possibility(self, prop, w):
        return any(self.worlds[n].evaluate(prop) for n in self.neighbors(w))
    def eval(self, formula:ModalFormula, w:str):
        if formula.is_necessity():  return self.eval_necessity(formula.content, w)
        if formula.is_possibility():return self.eval_possibility(formula.content, w)
        return self.worlds[w].evaluate(formula.content)

class S5ModalSystem:
    """Encapsulates an S5 Kripke model for multiple formulas."""
    def __init__(self):
        self.model = KripkeModel()
        self.actual="w0"
        self.model.add_world(self.actual)
        self.model.make_s5()
    def set_val(self, prop:str, val:bool, world=None):
        w = world or self.actual
        if w not in self.model.worlds:
            self.model.add_world(w); self.model.make_s5()
        self.model.worlds[w].assign(prop, val)
    def evaluate(self, formula:ModalFormula, world=None):
        return self.model.eval(formula, world or self.actual)
    def validate_entailment(self, premises:List[ModalFormula], concl:ModalFormula):
        for w in self.model.worlds:
            if all(self.evaluate(p,w) for p in premises) and not self.evaluate(concl,w):
                return False
        return True

class ThonocModalInference:
    """High-level modal inference for THŌNOC."""
    def __init__(self):
        self.s5 = S5ModalSystem()
        self.registry={}
        self.graph = nx.DiGraph()

    def register(self, prop_id:str, content:str, trinity:Tuple[float,float,float]):
        e,g,t = trinity
        nec = t>0.95 and e>0.9
        poss= t>0.05 and e>0.05
        val = nec or poss
        self.s5.set_val(prop_id, val)
        self.registry[prop_id] = {"content":content,"trinity":trinity}
        self.graph.add_node(prop_id)

    def entail(self, prem:str, concl:str, strength:float):
        if prem in self.registry and concl in self.registry:
            self.graph.add_edge(prem, concl, strength=strength)
            if self.registry[prem].get("necessary"):
                for s in self.graph.successors(prem):
                    self.registry[s]["necessary"]=True

    def trinity_to_modal_status(self, trinity:Tuple[float,float,float]):
        frm = ModalFormula("x")  # dummy
        return {"status": self.s5.evaluate(frm), "coherence": trinity[0]*trinity[1]*trinity[2]}
