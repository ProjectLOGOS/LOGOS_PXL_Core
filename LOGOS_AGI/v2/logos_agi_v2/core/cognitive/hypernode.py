import uuid
import time
from enum import Enum
from typing import Dict, Any, List, Optional


class Color(Enum):
    GREEN = "green"
    VIOLET = "violet"
    ORANGE = "orange"
    BLUE = "blue"
    YELLOW = "yellow"
    RED = "red"


class HyperNode:
    """
    The dynamic, evolving 'Cognitive Packet' that travels through the AGI.
    It represents a single, unified thought decomposed into its multiple,
    parallel linguistic representations.
    """

    def __init__(self, goal_id: str, initial_query: str):
        self.goal_id = goal_id
        self.initial_query = initial_query
        self.created_at = time.time()
        self.components: Dict[Color, Dict[str, Any]] = {}

    def add_color_component(
        self,
        color: Color,
        data_payload: Dict,
        trinity_vector: Dict,
        coherence_status: bool,
        is_enriched: bool = False,
    ):
        """Adds or updates a linguistic component to the Hyper-Node."""
        self.components[color] = {
            "node_id": f"{self.goal_id}_{color.value}",
            "color": color,
            "data_payload": data_payload,
            "trinity_vector": trinity_vector,
            "coherence_status": coherence_status,
            "is_enriched": is_enriched,
            "updated_at": time.time(),
        }

    def get_color_component(self, color: Color) -> Optional[Dict[str, Any]]:
        """Retrieves a specific linguistic component."""
        return self.components.get(color)

    def get_all_components(self) -> List[Dict[str, Any]]:
        """Returns all current components of the thought."""
        return list(self.components.values())

    def serialize(self) -> Dict[str, Any]:
        """Serializes the entire Hyper-Node for transmission."""
        # Need to handle Enum serialization
        serialized_components = {}
        for color_enum, data in self.components.items():
            comp = data.copy()
            comp["color"] = color_enum.value
            serialized_components[color_enum.value] = comp

        return {
            "goal_id": self.goal_id,
            "initial_query": self.initial_query,
            "created_at": self.created_at,
            "components": serialized_components,
        }
