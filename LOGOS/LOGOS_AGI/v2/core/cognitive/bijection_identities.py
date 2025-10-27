from enum import Enum
from typing import Tuple, Dict, Any

# Assuming HyperNode class is defined in the same package
from .hypernode import HyperNode


class Color(Enum):
    GREEN = "green"
    VIOLET = "violet"
    ORANGE = "orange"
    BLUE = "blue"
    YELLOW = "yellow"
    RED = "red"


class Subsystem:
    TELOS = "Telos"
    THONOC = "Thonoc"
    TETRAGNOS = "Tetragnos"


class BijectiveIdentity:
    """
    Base class for a subsystem's static, resident identity node.
    It holds the key to its native language and the rules for its internal thought processes.
    """

    def __init__(self, subsystem: str, primary_color: Color, decomp_colors: Tuple[Color, Color]):
        self.subsystem = subsystem
        self.primary_color = primary_color
        self.decomp_colors = decomp_colors  # (internal language 1, internal language 2)
        self.is_unlocked = False
        self.merged_data = None

    def attempt_unlock_and_merge(self, hyper_node: HyperNode) -> bool:
        """
        The key/lock mechanism. Merges if the incoming Hyper-Node's relevant color
        component is coherent and matches the subsystem's primary color.
        """
        color_component = hyper_node.get_color_component(self.primary_color)
        if color_component and color_component["coherence_status"]:
            self.is_unlocked = True
            self.merged_data = color_component["data_payload"]
            print(f"[{self.subsystem}] Static Node UNLOCKED with {self.primary_color.value} key.")
            return True
        print(f"[{self.subsystem}] Static Node unlock FAILED for {self.primary_color.value} key.")
        return False

    def internal_decomposition(self) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        """
        Performs the internal cognitive act of creating two specialized perspectives
        from one unified concept (the merged data).
        """
        if not self.is_unlocked:
            raise PermissionError("Cannot perform internal decomposition on a locked node.")

        # This is a conceptual transformation. A real system would have complex logic here.
        # Perspective 1 (e.g., Blue)
        data_1 = self.merged_data.copy()
        data_1["internal_perspective"] = self.decomp_colors[0].value

        # Perspective 2 (e.g., Yellow)
        data_2 = self.merged_data.copy()
        data_2["internal_perspective"] = self.decomp_colors[1].value

        print(
            f"[{self.subsystem}] Performed internal decomposition: {self.primary_color.value} -> {self.decomp_colors[0].value} + {self.decomp_colors[1].value}"
        )
        return (
            {"color": self.decomp_colors[0], "payload": data_1},
            {"color": self.decomp_colors[1], "payload": data_2},
        )

    def reset(self):
        """Resets the node to its default, locked state after a cognitive cycle."""
        self.is_unlocked = False
        self.merged_data = None


class TelosBijectiveIdentity(BijectiveIdentity):
    def __init__(self):
        super().__init__(Subsystem.TELOS, Color.GREEN, (Color.BLUE, Color.YELLOW))


class ThonocBijectiveIdentity(BijectiveIdentity):
    def __init__(self):
        super().__init__(Subsystem.THONOC, Color.VIOLET, (Color.BLUE, Color.RED))


class TetragnosBijectiveIdentity(BijectiveIdentity):
    def __init__(self):
        super().__init__(Subsystem.TETRAGNOS, Color.ORANGE, (Color.RED, Color.YELLOW))
