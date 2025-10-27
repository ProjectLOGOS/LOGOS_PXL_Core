import sqlite3, json, time, math, hashlib, heapq
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional, Tuple


@dataclass
class FractalPosition:
    c_real: float
    c_imag: float
    iterations: int
    in_set: bool

    def serialize(self):
        return asdict(self)

    @classmethod
    def deserialize(cls, data):
        return cls(**data)


@dataclass
class TrinityVector:
    existence: float
    goodness: float
    truth: float

    def as_tuple(self):
        return (self.existence, self.goodness, self.truth)

    def serialize(self):
        return asdict(self)

    @classmethod
    def deserialize(cls, data):
        return cls(**data)


@dataclass
class OntologicalNode:
    id: str
    query: str
    trinity_vector: TrinityVector
    fractal_position: FractalPosition
    created_at: float
    parent_id: Optional[str] = None
    children_ids: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def serialize(self):
        return {
            "id": self.id,
            "query": self.query,
            "trinity_vector": self.trinity_vector.serialize(),
            "fractal_position": self.fractal_position.serialize(),
            "created_at": self.created_at,
            "parent_id": self.parent_id,
            "children_ids": self.children_ids,
            "metadata": self.metadata,
        }

    @classmethod
    def deserialize(cls, data):
        data["trinity_vector"] = TrinityVector.deserialize(data["trinity_vector"])
        data["fractal_position"] = FractalPosition.deserialize(data["fractal_position"])
        return cls(**data)


class KDNode:
    def __init__(self, node_id, point):
        self.id = node_id
        self.point = point
        self.left = None
        self.right = None


class KDTree:
    def __init__(self, k):
        self.k = k
        self.root = None

    def insert(self, node_id, point):
        self.root = self._insert(self.root, node_id, point, 0)

    def _insert(self, node, node_id, point, depth):
        if node is None:
            return KDNode(node_id, point)
        axis = depth % self.k
        if point[axis] < node.point[axis]:
            node.left = self._insert(node.left, node_id, point, depth + 1)
        else:
            node.right = self._insert(node.right, node_id, point, depth + 1)
        return node

    def k_nearest_neighbors(self, point, k):
        heap = []
        self._knn_search(self.root, point, 0, k, heap)
        return [(nid, -d) for d, nid in sorted(heap, reverse=True)]

    def _knn_search(self, node, point, depth, k, heap):
        if not node:
            return
        dist = sum((a - b) ** 2 for a, b in zip(point, node.point))
        entry = (-dist, node.id)
        if len(heap) < k:
            heapq.heappush(heap, entry)
        elif entry > heap[0]:
            heapq.heapreplace(heap, entry)
        axis = depth % self.k
        diff = point[axis] - node.point[axis]
        first, second = (node.left, node.right) if diff < 0 else (node.right, node.left)
        self._knn_search(first, point, depth + 1, k, heap)
        if len(heap) < k or diff**2 < -heap[0][0]:
            self._knn_search(second, point, depth + 1, k, heap)


class FractalKnowledgeDatabase:
    def __init__(self, db_path: str = ":memory:"):
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        self.trinity_index = KDTree(k=3)
        self.complex_index = KDTree(k=2)
        self.cache: Dict[str, OntologicalNode] = {}
        self._initialize_database()
        self._load_indices_from_db()

    def _initialize_database(self):
        with self.conn:
            self.conn.execute(
                "CREATE TABLE IF NOT EXISTS nodes (id TEXT PRIMARY KEY, data TEXT NOT NULL)"
            )

    def _load_indices_from_db(self):
        print("[DB Manager] Loading existing nodes into spatial indices...")
        cursor = self.conn.execute("SELECT data FROM nodes")
        count = 0
        for row in cursor:
            try:
                node = OntologicalNode.deserialize(json.loads(row[0]))
                self.trinity_index.insert(node.id, list(node.trinity_vector.as_tuple()))
                self.complex_index.insert(
                    node.id, [node.fractal_position.c_real, node.fractal_position.c_imag]
                )
                self.cache[node.id] = node
                count += 1
            except Exception as e:
                print(f"[DB Manager] Error loading node from DB row: {e}")
        print(f"[DB Manager] Loaded and indexed {count} nodes.")

    def store_node(self, node: OntologicalNode):
        serialized_data = json.dumps(node.serialize())
        with self.conn:
            self.conn.execute(
                "INSERT OR REPLACE INTO nodes (id, data) VALUES (?, ?)", (node.id, serialized_data)
            )
        self.trinity_index.insert(node.id, list(node.trinity_vector.as_tuple()))
        self.complex_index.insert(
            node.id, [node.fractal_position.c_real, node.fractal_position.c_imag]
        )
        self.cache[node.id] = node

    def get_node(self, node_id: str) -> Optional[OntologicalNode]:
        if node_id in self.cache:
            return self.cache[node_id]
        cursor = self.conn.execute("SELECT data FROM nodes WHERE id = ?", (node_id,))
        row = cursor.fetchone()
        if not row:
            return None
        node = OntologicalNode.deserialize(json.loads(row[0]))
        self.cache[node_id] = node
        return node

    def find_nearest_by_trinity(self, vector: TrinityVector, k: int = 5) -> List[Tuple[str, float]]:
        point = list(vector.as_tuple())
        return self.trinity_index.k_nearest_neighbors(point, k)

    def find_nearest_by_position(
        self, position: FractalPosition, k: int = 5
    ) -> List[Tuple[str, float]]:
        point = [position.c_real, position.c_imag]
        return self.complex_index.k_nearest_neighbors(point, k)
