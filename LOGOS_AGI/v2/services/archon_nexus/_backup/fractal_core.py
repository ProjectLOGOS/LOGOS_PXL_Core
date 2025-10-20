# fractal_core.py
"""
Unified Fractal Ontology and Navigation Core

This module combines:
 - Ontological fractal database (persistent storage, multi-dimensional indexing)
 - TrinityVector and FractalPosition data types
 - KD-tree spatial indexing for trinity and complex space
 - FractalNavigator for Mandelbrot-based mapping, stability, and theological exploration

All overlapping definitions have been merged and redundant code removed for clarity and performance.
"""
import sqlite3
import json
import time
import math
import hashlib
import heapq
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict, field

# --- Core Data Types ---

class TrinityDimension(Enum):
    EXISTENCE = "existence"
    GOODNESS  = "goodness"
    TRUTH     = "truth"
    COHERENCE = "coherence"  # Z-axis placeholder for future 3D use

@dataclass
class TrinityVector:
    """Represents a metaphysical vector (E, G, T, C)."""
    existence: float
    goodness:  float
    truth:     float
    coherence: float = 0.0  # Placeholder Z-axis (raw coherence score)

    def as_tuple(self) -> Tuple[float, float, float, float]:
        return (self.existence, self.goodness, self.truth, self.coherence)

    def to_complex(self) -> complex:
        # Map to complex plane: real = E*T, imag = G
        return complex(self.existence * self.truth, self.goodness)

    def serialize(self) -> Dict[str, float]:
        return asdict(self)

    @classmethod
    def deserialize(cls, data: Dict[str, float]) -> 'TrinityVector':
        return cls(
            existence=data.get("existence", 0.0),
            goodness=data.get("goodness", 0.0),
            truth=data.get("truth", 0.0),
            coherence=data.get("coherence", 0.0)
        )

@dataclass
class FractalPosition:
    """Position in fractal space with escape-time metrics."""
    c_real: float
    c_imag: float
    iterations: int
    in_set: bool
    escape_radius: float = 2.0

    @property
    def complex(self) -> complex:
        return complex(self.c_real, self.c_imag)

    def serialize(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def deserialize(cls, data: Dict[str, Any]) -> 'FractalPosition':
        return cls(**data)

@dataclass
class OntologicalNode:
    """A node carrying query, vector, and fractal position."""
    id:        str
    query:     str
    trinity:   TrinityVector
    position:  FractalPosition
    created_at: float
    parent_id: Optional[str] = None
    children:  List[str]   = field(default_factory=list)
    metadata:  Dict[str,Any] = field(default_factory=dict)

    def serialize(self) -> Dict[str,Any]:
        return {
            "id": self.id,
            "query": self.query,
            "trinity": self.trinity.serialize(),
            "position": self.position.serialize(),
            "created_at": self.created_at,
            "parent_id": self.parent_id,
            "children": self.children,
            "metadata": self.metadata
        }

    @classmethod
    def deserialize(cls, data: Dict[str,Any]) -> 'OntologicalNode':
        return cls(
            id=data["id"],
            query=data["query"],
            trinity=TrinityVector.deserialize(data["trinity"]),
            position=FractalPosition.deserialize(data["position"]),
            created_at=data["created_at"],
            parent_id=data.get("parent_id"),
            children=data.get("children", []),
            metadata=data.get("metadata", {})
        )

# --- Spatial Indexing ---

class KDNode:
    __slots__ = ("id","point","left","right")
    def __init__(self, node_id: str, point: List[float]):
        self.id = node_id
        self.point = point
        self.left = None
        self.right = None

class KDTree:
    def __init__(self, k: int):
        self.k = k
        self.root = None

    def insert(self, node_id: str, point: List[float]):
        self.root = self._insert(self.root, node_id, point, 0)

    def _insert(self, node, node_id, point, depth):
        if node is None:
            return KDNode(node_id, point)
        axis = depth % self.k
        if point[axis] < node.point[axis]:
            node.left = self._insert(node.left, node_id, point, depth+1)
        else:
            node.right = self._insert(node.right, node_id, point, depth+1)
        return node

    def k_nearest(self, point: List[float], k: int) -> List[Tuple[str,float]]:
        heap = []  # (-dist, id)
        self._knn(self.root, point, 0, k, heap)
        return [(nid, -d) for d,nid in sorted(heap, reverse=True)]

    def _knn(self, node, point, depth, k, heap):
        if not node: return
        dist = sum((a-b)**2 for a,b in zip(point,node.point))
        entry = (-dist, node.id)
        if len(heap) < k:
            heapq.heappush(heap, entry)
        elif entry > heap[0]:
            heapq.heapreplace(heap, entry)
        axis = depth % self.k
        diff = point[axis] - node.point[axis]
        first, second = (node.left, node.right) if diff < 0 else (node.right, node.left)
        self._knn(first, point, depth+1, k, heap)
        if len(heap)<k or diff*diff < -heap[0][0]:
            self._knn(second, point, depth+1, k, heap)

# --- Ontological Fractal Database ---

class FractalDB:
    """Persistent SQLite-backed fractal knowledge database."""
    def __init__(self, db_path: str = ':memory:'):
        self.conn = sqlite3.connect(db_path)
        self._initialize()
        self.trinity_idx = KDTree(k=4)  # include coherence axis if needed in future
        self.complex_idx = KDTree(k=2)
        self.cache: Dict[str,OntologicalNode] = {}

    def _initialize(self):
        with self.conn:
            self.conn.execute("""
            CREATE TABLE IF NOT EXISTS nodes(
              id TEXT PRIMARY KEY, query TEXT, trinity TEXT,
              position TEXT, created_at REAL, parent_id TEXT, metadata TEXT
            )""")
            self.conn.execute("""
            CREATE TABLE IF NOT EXISTS relations(
              src TEXT, tgt TEXT, type TEXT, weight REAL, metadata TEXT,
              PRIMARY KEY(src,tgt,type)
            )""")

    def store(self, node: OntologicalNode):
        data = node.serialize()
        with self.conn:
            self.conn.execute(
                'INSERT OR REPLACE INTO nodes VALUES(?,?,?,?,?,?,?)',
                (data['id'], data['query'], json.dumps(data['trinity']),
                 json.dumps(data['position']), data['created_at'],
                 data['parent_id'], json.dumps(data['metadata']))
            )
        # index
        self.trinity_idx.insert(node.id, list(node.trinity.as_tuple()))
        self.complex_idx.insert(node.id, [node.position.c_real, node.position.c_imag])
        self.cache[node.id] = node

    def get(self, node_id: str) -> Optional[OntologicalNode]:
        if node_id in self.cache:
            return self.cache[node_id]
        cur = self.conn.execute('SELECT * FROM nodes WHERE id=?', (node_id,))
        row = cur.fetchone()
        if not row: return None
        _,query,tri_js,pos_js,created,parent,meta_js = row
        node = OntologicalNode(
            id=node_id,
            query=query,
            trinity=TrinityVector.deserialize(json.loads(tri_js)),
            position=FractalPosition.deserialize(json.loads(pos_js)),
            created_at=created,
            parent_id=parent,
            children=[],
            metadata=json.loads(meta_js or '{}')
        )
        self.cache[node_id] = node
        return node

# --- Fractal Navigation ---

class FractalNavigator:
    """Maps TrinityVectors into fractal positions and analyzes orbits."""
    def __init__(self, max_iter:int=100, escape_radius:float=2.0):
        self.max_iter = max_iter
        self.escape_radius = escape_radius

    def compute_position(self, trinity: TrinityVector) -> FractalPosition:
        c = trinity.to_complex()
        z = 0+0j
        for i in range(self.max_iter):
            z = z*z + c
            if abs(z) > self.escape_radius:
                return FractalPosition(c.real, c.imag, i, False, self.escape_radius)
        return FractalPosition(c.real, c.imag, self.max_iter, True, self.escape_radius)

    def stability(self, pos: FractalPosition) -> float:
        return 1.0 if pos.in_set else pos.iterations / self.max_iter

    def orbital_properties(self, trinity: TrinityVector) -> Dict[str,Any]:
        pos = self.compute_position(trinity)
        st = self.stability(pos)
        # Lyapunov exponent approx
        derivs = []
        z = 0+0j
        for _ in range(min(pos.iterations,50)):
            derivs.append(abs(2*z))
            z = z*z + trinity.to_complex()
        lyap = sum(math.log(max(d,1e-10)) for d in derivs[1:]) / max(1,len(derivs)-1)
        # angle mapping
        angle = math.degrees(math.atan2(trinity.goodness, trinity.existence*trinity.truth)) % 360
        dir = ('transcendent' if angle<90 else 'immanent' if angle<180
               else 'contingent' if angle<270 else 'necessary')
        return {
            'iterations': pos.iterations,
            'in_set': pos.in_set,
            'stability': st,
            'lyapunov': lyap,
            'direction': dir,
            'magnitude': abs(trinity.to_complex()),
            'angle': angle
        }

# --- End of module ---
