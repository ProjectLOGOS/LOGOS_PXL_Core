"""
Belief Network Framework

Provides probabilistic graphical models for belief representation,
inference, and belief propagation.
"""

from typing import Dict, List, Any, Optional, Set, Tuple
from collections import defaultdict
import math

class BeliefNode:
    """Represents a node in the belief network."""

    def __init__(self, name: str, states: List[str], cpt: Optional[Dict] = None):
        self.name = name
        self.states = states
        self.cpt = cpt or {}  # Conditional Probability Table
        self.parents: List['BeliefNode'] = []
        self.children: List['BeliefNode'] = []
        self.beliefs = {state: 1.0 / len(states) for state in states}  # Uniform prior

    def add_parent(self, parent: 'BeliefNode'):
        """Add a parent node."""
        if parent not in self.parents:
            self.parents.append(parent)
            parent.children.append(self)

    def set_cpt(self, cpt: Dict):
        """Set conditional probability table."""
        self.cpt = cpt

    def update_belief(self, evidence: Dict[str, str]):
        """Update beliefs based on evidence."""
        # Simplified belief update - in practice would use full Bayesian inference
        if self.name in evidence:
            observed_state = evidence[self.name]
            for state in self.states:
                self.beliefs[state] = 1.0 if state == observed_state else 0.0
        else:
            # Normalize beliefs
            total = sum(self.beliefs.values())
            if total > 0:
                for state in self.beliefs:
                    self.beliefs[state] /= total

class BeliefNetwork:
    """
    Probabilistic graphical model for belief representation and inference.

    Supports Bayesian networks, belief propagation, and probabilistic reasoning.
    """

    def __init__(self):
        self.nodes: Dict[str, BeliefNode] = {}
        self.edges: Set[Tuple[str, str]] = set()

    def add_node(self, node: BeliefNode):
        """Add a node to the network."""
        self.nodes[node.name] = node

    def add_edge(self, parent_name: str, child_name: str):
        """Add a directed edge between nodes."""
        if parent_name in self.nodes and child_name in self.nodes:
            parent = self.nodes[parent_name]
            child = self.nodes[child_name]
            child.add_parent(parent)
            self.edges.add((parent_name, child_name))

    def set_evidence(self, evidence: Dict[str, str]):
        """Set evidence for nodes."""
        for node_name, state in evidence.items():
            if node_name in self.nodes:
                self.nodes[node_name].update_belief(evidence)

    def propagate_beliefs(self, max_iterations: int = 10):
        """Propagate beliefs through the network."""
        for _ in range(max_iterations):
            updated = False
            for node in self.nodes.values():
                old_beliefs = node.beliefs.copy()
                node.update_belief({})  # Update based on current network state
                if old_beliefs != node.beliefs:
                    updated = True
            if not updated:
                break

    def query_probability(self, node_name: str, state: str) -> float:
        """Query probability of a state for a node."""
        if node_name not in self.nodes:
            return 0.0
        return self.nodes[node_name].beliefs.get(state, 0.0)

    def get_most_likely_state(self, node_name: str) -> Optional[str]:
        """Get the most likely state for a node."""
        if node_name not in self.nodes:
            return None
        node = self.nodes[node_name]
        return max(node.beliefs.items(), key=lambda x: x[1])[0] if node.beliefs else None

    def calculate_joint_probability(self, states: Dict[str, str]) -> float:
        """Calculate joint probability of a set of states."""
        probability = 1.0

        # Process nodes in topological order
        processed = set()
        to_process = [name for name in self.nodes.keys() if not self.nodes[name].parents]

        while to_process:
            current_name = to_process.pop()
            if current_name in processed:
                continue

            current_node = self.nodes[current_name]
            if current_name in states:
                state_prob = current_node.beliefs.get(states[current_name], 0.0)
                probability *= state_prob

            processed.add(current_name)

            # Add children that have all parents processed
            for child in current_node.children:
                if all(p.name in processed for p in child.parents):
                    to_process.append(child.name)

        return probability

    def find_independencies(self) -> List[Tuple[str, str, List[str]]]:
        """Find conditional independencies in the network."""
        independencies = []

        for node1_name in self.nodes:
            for node2_name in self.nodes:
                if node1_name != node2_name:
                    # Check d-separation
                    separating_set = self._find_d_separator(node1_name, node2_name)
                    if separating_set is not None:
                        independencies.append((node1_name, node2_name, separating_set))

        return independencies

    def _find_d_separator(self, node1: str, node2: str) -> Optional[List[str]]:
        """Find d-separator between two nodes."""
        # Simplified d-separation check
        # In practice, would implement full d-separation algorithm
        return []  # Assume no separation for simplicity

    def learn_structure(self, data: List[Dict[str, str]], max_edges: int = 10):
        """Learn network structure from data."""
        # Simplified structure learning
        node_names = list(self.nodes.keys())

        for i in range(len(node_names)):
            for j in range(i + 1, len(node_names)):
                node1, node2 = node_names[i], node_names[j]

                # Check if adding edge improves fit
                if len(self.edges) < max_edges:
                    # Simplified scoring
                    score = self._calculate_edge_score(node1, node2, data)
                    if score > 0.1:  # Arbitrary threshold
                        self.add_edge(node1, node2)

    def _calculate_edge_score(self, node1: str, node2: str, data: List[Dict[str, str]]) -> float:
        """Calculate score for adding an edge."""
        # Simplified scoring based on mutual information
        count_matrix = defaultdict(lambda: defaultdict(int))

        for sample in data:
            state1 = sample.get(node1)
            state2 = sample.get(node2)
            if state1 and state2:
                count_matrix[state1][state2] += 1

        # Calculate mutual information (simplified)
        total_samples = len(data)
        mutual_info = 0.0

        for state1_counts in count_matrix.values():
            for count in state1_counts.values():
                if count > 0:
                    p_joint = count / total_samples
                    mutual_info += p_joint * math.log(p_joint)

        return mutual_info

    def validate_network(self) -> Dict[str, Any]:
        """Validate the belief network structure."""
        issues = []

        # Check for cycles
        if self._has_cycles():
            issues.append("Network contains cycles")

        # Check for disconnected components
        components = self._find_components()
        if len(components) > 1:
            issues.append(f"Network has {len(components)} disconnected components")

        # Check CPT completeness
        for node_name, node in self.nodes.items():
            if not node.cpt and node.parents:
                issues.append(f"Node {node_name} missing CPT")

        return {
            "valid": len(issues) == 0,
            "issues": issues,
            "nodes": len(self.nodes),
            "edges": len(self.edges),
            "components": len(components)
        }

    def _has_cycles(self) -> bool:
        """Check if network has cycles."""
        visited = set()
        rec_stack = set()

        def has_cycle_util(node_name: str) -> bool:
            visited.add(node_name)
            rec_stack.add(node_name)

            for child in self.nodes[node_name].children:
                if child.name not in visited:
                    if has_cycle_util(child.name):
                        return True
                elif child.name in rec_stack:
                    return True

            rec_stack.remove(node_name)
            return False

        for node_name in self.nodes:
            if node_name not in visited:
                if has_cycle_util(node_name):
                    return True

        return False

    def _find_components(self) -> List[Set[str]]:
        """Find connected components."""
        visited = set()
        components = []

        def dfs(node_name: str, component: Set[str]):
            visited.add(node_name)
            component.add(node_name)

            node = self.nodes[node_name]
            for parent in node.parents:
                if parent.name not in visited:
                    dfs(parent.name, component)
            for child in node.children:
                if child.name not in visited:
                    dfs(child.name, component)

        for node_name in self.nodes:
            if node_name not in visited:
                component = set()
                dfs(node_name, component)
                components.append(component)

        return components

    def get_network_statistics(self) -> Dict[str, Any]:
        """Get statistics about the belief network."""
        node_degrees = {}
        for node_name, node in self.nodes.items():
            node_degrees[node_name] = len(node.parents) + len(node.children)

        return {
            "nodes": len(self.nodes),
            "edges": len(self.edges),
            "average_degree": sum(node_degrees.values()) / len(node_degrees) if node_degrees else 0,
            "max_degree": max(node_degrees.values()) if node_degrees else 0,
            "components": len(self._find_components()),
            "has_cycles": self._has_cycles()
        }