#!/usr/bin/env python3
"""Advanced Workflow Architect with NetworkX DAG Construction

Sophisticated workflow design system using NetworkX for optimal task orchestration.
Builds complex directed acyclic graphs for multi-subsystem reasoning workflows.

Core Capabilities:
- Dynamic DAG construction using NetworkX
- Intelligent task dependency analysis
- Optimal execution order computation via topological sorting
- Resource-aware workflow optimization

Dependencies: networkx, numpy
"""

import logging
import uuid
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import Any

import networkx as nx


class TaskType(Enum):
    """Enumeration of available task types across subsystems."""

    # TETRAGNOS tasks
    CLUSTER_TEXTS = "cluster_texts"
    EXTRACT_FEATURES = "extract_features"
    SEMANTIC_SIMILARITY = "semantic_similarity"
    ANALYZE_PATTERNS = "analyze_patterns"
    TRANSLATE_TEXT = "translate_text"

    # TELOS tasks
    FORECAST_SERIES = "forecast_series"
    CAUSAL_DISCOVERY = "causal_discovery"
    ANALYZE_INTERVENTION = "analyze_intervention"
    TEST_HYPOTHESIS = "test_hypothesis"
    PREDICT_OUTCOMES = "predict_outcomes"
    CAUSAL_RETRODICTION = "causal_retrodiction"
    BUILD_CAUSAL_MODEL = "build_causal_model"

    # THONOC tasks
    CONSTRUCT_PROOF = "construct_proof"
    EVALUATE_LAMBDA = "evaluate_lambda"
    MODAL_REASONING = "modal_reasoning"
    CONSISTENCY_CHECK = "consistency_check"
    THEOREM_PROVING = "theorem_proving"
    ASSIGN_CONSEQUENCE = "assign_consequence"


class Subsystem(Enum):
    """Enumeration of reasoning subsystems."""

    TETRAGNOS = "tetragnos"
    TELOS = "telos"
    THONOC = "thonoc"


@dataclass
class TaskNode:
    """Represents a single task node in the workflow DAG."""

    task_id: str
    task_type: TaskType
    subsystem: Subsystem
    payload: dict[str, Any]
    estimated_duration: float = 30.0  # seconds
    resource_requirements: dict[str, float] = None
    priority: int = 1  # 1=low, 5=high

    def __post_init__(self):
        if self.resource_requirements is None:
            self.resource_requirements = {"cpu": 1.0, "memory": 512.0}


@dataclass
class WorkflowTemplate:
    """Template for common workflow patterns."""

    name: str
    description: str
    task_sequence: list[dict[str, Any]]
    dependency_rules: list[tuple[str, str]]  # (prerequisite, dependent)


class AdvancedWorkflowArchitect:
    """Advanced workflow design engine using NetworkX for DAG construction."""

    def __init__(self):
        self.logger = logging.getLogger("WORKFLOW_ARCHITECT")
        self.task_templates = self._initialize_task_templates()
        self.workflow_templates = self._initialize_workflow_templates()
        self.subsystem_capabilities = self._initialize_subsystem_capabilities()

    def design_workflow(
        self, goal_description: str, goal_context: dict[str, Any] = None
    ) -> nx.DiGraph:
        """Design optimal workflow DAG for achieving the specified goal.

        Args:
            goal_description: Natural language description of the goal
            goal_context: Additional context and constraints

        Returns:
            NetworkX DiGraph representing the optimal workflow
        """
        self.logger.info(f"Designing workflow for goal: {goal_description}")

        # Initialize workflow DAG
        workflow_dag = nx.DiGraph()

        # Analyze goal requirements
        goal_analysis = self._analyze_goal_requirements(goal_description, goal_context)

        # Select appropriate workflow template or design custom workflow
        if goal_analysis["template_match"]:
            workflow_dag = self._build_from_template(goal_analysis)
        else:
            workflow_dag = self._design_custom_workflow(goal_analysis)

        # Optimize workflow structure
        optimized_dag = self._optimize_workflow(workflow_dag, goal_analysis)

        # Validate DAG properties
        self._validate_workflow_dag(optimized_dag)

        # Add workflow metadata
        self._add_workflow_metadata(optimized_dag, goal_description, goal_analysis)

        self.logger.info(
            f"Workflow designed with {optimized_dag.number_of_nodes()} tasks and {optimized_dag.number_of_edges()} dependencies"
        )

        return optimized_dag

    def _analyze_goal_requirements(
        self, goal_description: str, context: dict[str, Any] = None
    ) -> dict[str, Any]:
        """Analyze goal to determine required capabilities and workflow structure."""
        context = context or {}
        goal_lower = goal_description.lower()

        # Capability analysis
        required_capabilities = set()

        # Pattern recognition keywords
        if any(
            keyword in goal_lower
            for keyword in ["analyze", "pattern", "cluster", "classify", "similarity"]
        ):
            required_capabilities.add("pattern_recognition")

        # Causal reasoning keywords
        if any(
            keyword in goal_lower
            for keyword in ["cause", "effect", "predict", "forecast", "intervention"]
        ):
            required_capabilities.add("causal_reasoning")

        # Logical reasoning keywords
        if any(
            keyword in goal_lower
            for keyword in ["prove", "logic", "theorem", "consistency", "modal"]
        ):
            required_capabilities.add("logical_reasoning")

        # Symbolic computation keywords
        if any(keyword in goal_lower for keyword in ["equation", "symbolic", "lambda", "calculus"]):
            required_capabilities.add("symbolic_computation")

        # Time series keywords
        if any(
            keyword in goal_lower for keyword in ["time series", "forecast", "trend", "temporal"]
        ):
            required_capabilities.add("time_series_analysis")

        # Determine complexity level
        complexity_indicators = ["complex", "comprehensive", "detailed", "thorough", "multi-step"]
        complexity_level = sum(1 for indicator in complexity_indicators if indicator in goal_lower)

        # Template matching
        template_match = self._find_matching_template(required_capabilities, complexity_level)

        return {
            "required_capabilities": required_capabilities,
            "complexity_level": min(complexity_level, 3),  # Cap at 3
            "template_match": template_match,
            "goal_type": self._classify_goal_type(goal_description),
            "estimated_resources": self._estimate_resource_requirements(
                required_capabilities, complexity_level
            ),
            "parallel_opportunities": self._identify_parallel_opportunities(required_capabilities),
        }

    def _build_from_template(self, goal_analysis: dict[str, Any]) -> nx.DiGraph:
        """Build workflow from matching template."""
        template = goal_analysis["template_match"]
        workflow_dag = nx.DiGraph()

        self.logger.info(f"Building workflow from template: {template.name}")

        # Create task nodes from template
        task_nodes = {}
        for task_spec in template.task_sequence:
            task_node = self._create_task_node_from_spec(task_spec)
            task_nodes[task_node.task_id] = task_node
            workflow_dag.add_node(task_node.task_id, task_node=task_node)

        # Add dependencies from template
        for prereq, dependent in template.dependency_rules:
            if prereq in task_nodes and dependent in task_nodes:
                workflow_dag.add_edge(task_nodes[prereq].task_id, task_nodes[dependent].task_id)

        return workflow_dag

    def _design_custom_workflow(self, goal_analysis: dict[str, Any]) -> nx.DiGraph:
        """Design custom workflow based on goal analysis."""
        workflow_dag = nx.DiGraph()

        self.logger.info("Designing custom workflow")

        # Create foundational analysis stage
        foundation_tasks = self._create_foundation_tasks(goal_analysis)
        for task in foundation_tasks:
            workflow_dag.add_node(task.task_id, task_node=task)

        # Create specialized reasoning stages
        reasoning_tasks = self._create_reasoning_tasks(goal_analysis)
        for task in reasoning_tasks:
            workflow_dag.add_node(task.task_id, task_node=task)

        # Create synthesis stage
        synthesis_tasks = self._create_synthesis_tasks(goal_analysis)
        for task in synthesis_tasks:
            workflow_dag.add_node(task.task_id, task_node=task)

        # Add dependencies between stages
        self._add_stage_dependencies(
            workflow_dag, foundation_tasks, reasoning_tasks, synthesis_tasks
        )

        # Add intra-stage dependencies
        self._add_intra_stage_dependencies(workflow_dag, reasoning_tasks)

        return workflow_dag

    def _create_foundation_tasks(self, goal_analysis: dict[str, Any]) -> list[TaskNode]:
        """Create foundational analysis tasks."""
        tasks = []

        # Always start with pattern analysis for understanding
        if "pattern_recognition" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"foundation_pattern_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.ANALYZE_PATTERNS,
                    subsystem=Subsystem.TETRAGNOS,
                    payload={"analysis_type": "foundational"},
                    priority=5,
                )
            )

        # Add feature extraction if needed
        if goal_analysis["complexity_level"] >= 2:
            tasks.append(
                TaskNode(
                    task_id=f"foundation_features_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.EXTRACT_FEATURES,
                    subsystem=Subsystem.TETRAGNOS,
                    payload={"extraction_type": "comprehensive"},
                    priority=4,
                )
            )

        return tasks

    def _create_reasoning_tasks(self, goal_analysis: dict[str, Any]) -> list[TaskNode]:
        """Create specialized reasoning tasks based on capabilities."""
        tasks = []

        # Causal reasoning tasks
        if "causal_reasoning" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"causal_discovery_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.CAUSAL_DISCOVERY,
                    subsystem=Subsystem.TELOS,
                    payload={"method": "pc"},
                    estimated_duration=60.0,
                    priority=4,
                )
            )

            if goal_analysis["complexity_level"] >= 2:
                tasks.append(
                    TaskNode(
                        task_id=f"causal_model_{uuid.uuid4().hex[:8]}",
                        task_type=TaskType.BUILD_CAUSAL_MODEL,
                        subsystem=Subsystem.TELOS,
                        payload={"include_interventions": True},
                        estimated_duration=90.0,
                        priority=3,
                    )
                )

        # Logical reasoning tasks
        if "logical_reasoning" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"consistency_check_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.CONSISTENCY_CHECK,
                    subsystem=Subsystem.THONOC,
                    payload={"logic_type": "propositional"},
                    estimated_duration=45.0,
                    priority=4,
                )
            )

            if goal_analysis["complexity_level"] >= 2:
                tasks.append(
                    TaskNode(
                        task_id=f"theorem_prove_{uuid.uuid4().hex[:8]}",
                        task_type=TaskType.THEOREM_PROVING,
                        subsystem=Subsystem.THONOC,
                        payload={"strategy": "resolution"},
                        estimated_duration=120.0,
                        priority=3,
                    )
                )

        # Time series analysis
        if "time_series_analysis" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"forecast_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.FORECAST_SERIES,
                    subsystem=Subsystem.TELOS,
                    payload={"periods": 12, "include_volatility": True},
                    estimated_duration=75.0,
                    priority=3,
                )
            )

        # Symbolic computation
        if "symbolic_computation" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"symbolic_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.EVALUATE_LAMBDA,
                    subsystem=Subsystem.THONOC,
                    payload={"symbolic_mode": True},
                    estimated_duration=40.0,
                    priority=3,
                )
            )

        return tasks

    def _create_synthesis_tasks(self, goal_analysis: dict[str, Any]) -> list[TaskNode]:
        """Create synthesis and integration tasks."""
        tasks = []

        # Always include hypothesis testing for validation
        tasks.append(
            TaskNode(
                task_id=f"synthesis_hypothesis_{uuid.uuid4().hex[:8]}",
                task_type=TaskType.TEST_HYPOTHESIS,
                subsystem=Subsystem.TELOS,
                payload={"test_type": "bayesian"},
                estimated_duration=50.0,
                priority=2,
            )
        )

        # Add consequence assignment for logical integration
        if "logical_reasoning" in goal_analysis["required_capabilities"]:
            tasks.append(
                TaskNode(
                    task_id=f"synthesis_consequences_{uuid.uuid4().hex[:8]}",
                    task_type=TaskType.ASSIGN_CONSEQUENCE,
                    subsystem=Subsystem.THONOC,
                    payload={"scope": "comprehensive"},
                    estimated_duration=60.0,
                    priority=2,
                )
            )

        return tasks

    def _add_stage_dependencies(
        self,
        dag: nx.DiGraph,
        foundation: list[TaskNode],
        reasoning: list[TaskNode],
        synthesis: list[TaskNode],
    ):
        """Add dependencies between workflow stages."""
        # Foundation -> Reasoning dependencies
        for foundation_task in foundation:
            for reasoning_task in reasoning:
                dag.add_edge(foundation_task.task_id, reasoning_task.task_id)

        # Reasoning -> Synthesis dependencies
        for reasoning_task in reasoning:
            for synthesis_task in synthesis:
                dag.add_edge(reasoning_task.task_id, synthesis_task.task_id)

    def _add_intra_stage_dependencies(self, dag: nx.DiGraph, reasoning_tasks: list[TaskNode]):
        """Add dependencies within reasoning stage where logical."""
        # Find causal discovery and causal model tasks
        causal_discovery = None
        causal_model = None

        for task in reasoning_tasks:
            if task.task_type == TaskType.CAUSAL_DISCOVERY:
                causal_discovery = task
            elif task.task_type == TaskType.BUILD_CAUSAL_MODEL:
                causal_model = task

        # Causal discovery should precede causal modeling
        if causal_discovery and causal_model:
            dag.add_edge(causal_discovery.task_id, causal_model.task_id)

    def _optimize_workflow(self, dag: nx.DiGraph, goal_analysis: dict[str, Any]) -> nx.DiGraph:
        """Optimize workflow structure for efficiency and resource utilization."""
        optimized_dag = dag.copy()

        # Identify parallel execution opportunities
        parallel_groups = self._identify_parallel_groups(optimized_dag)

        # Balance resource utilization
        self._balance_resource_utilization(optimized_dag, parallel_groups)

        # Optimize critical path
        critical_path = self._find_critical_path(optimized_dag)
        self._optimize_critical_path(optimized_dag, critical_path)

        return optimized_dag

    def _identify_parallel_groups(self, dag: nx.DiGraph) -> list[list[str]]:
        """Identify groups of tasks that can be executed in parallel."""
        parallel_groups = []

        # Get topological generations (tasks at same level)
        for generation in nx.topological_generations(dag):
            if len(generation) > 1:
                parallel_groups.append(list(generation))

        return parallel_groups

    def _balance_resource_utilization(self, dag: nx.DiGraph, parallel_groups: list[list[str]]):
        """Balance resource utilization across parallel task groups."""
        for group in parallel_groups:
            total_cpu = sum(
                dag.nodes[task_id]["task_node"].resource_requirements["cpu"] for task_id in group
            )
            total_memory = sum(
                dag.nodes[task_id]["task_node"].resource_requirements["memory"] for task_id in group
            )

            # Log resource utilization for monitoring
            self.logger.debug(
                f"Parallel group resource usage - CPU: {total_cpu}, Memory: {total_memory}MB"
            )

    def _find_critical_path(self, dag: nx.DiGraph) -> list[str]:
        """Find the critical path (longest path) through the workflow."""
        # Calculate longest path using task durations
        longest_path = []
        max_duration = 0

        # Find all simple paths from sources to sinks
        sources = [node for node in dag.nodes() if dag.in_degree(node) == 0]
        sinks = [node for node in dag.nodes() if dag.out_degree(node) == 0]

        for source in sources:
            for sink in sinks:
                try:
                    for path in nx.all_simple_paths(dag, source, sink):
                        path_duration = sum(
                            dag.nodes[task_id]["task_node"].estimated_duration for task_id in path
                        )
                        if path_duration > max_duration:
                            max_duration = path_duration
                            longest_path = path
                except nx.NetworkXNoPath:
                    continue

        return longest_path

    def _optimize_critical_path(self, dag: nx.DiGraph, critical_path: list[str]):
        """Optimize tasks on the critical path for faster execution."""
        for task_id in critical_path:
            task_node = dag.nodes[task_id]["task_node"]
            # Increase priority for critical path tasks
            task_node.priority = min(task_node.priority + 1, 5)
            # Optimize resource allocation
            task_node.resource_requirements["cpu"] *= 1.2  # Boost CPU allocation

    def _validate_workflow_dag(self, dag: nx.DiGraph):
        """Validate that the workflow DAG meets requirements."""
        # Check if DAG is actually acyclic
        if not nx.is_directed_acyclic_graph(dag):
            raise ValueError("Workflow contains cycles - not a valid DAG")

        # Check connectivity
        if not nx.is_weakly_connected(dag):
            self.logger.warning("Workflow DAG is not connected - may have isolated components")

        # Check for reasonable size
        if dag.number_of_nodes() > 50:
            self.logger.warning(
                f"Large workflow with {dag.number_of_nodes()} tasks - consider optimization"
            )

        # Validate task node data
        for node_id, node_data in dag.nodes(data=True):
            if "task_node" not in node_data:
                raise ValueError(f"Node {node_id} missing task_node data")

    def _add_workflow_metadata(
        self, dag: nx.DiGraph, goal_description: str, goal_analysis: dict[str, Any]
    ):
        """Add metadata to the workflow DAG."""
        dag.graph["metadata"] = {
            "goal_description": goal_description,
            "creation_timestamp": datetime.utcnow().isoformat(),
            "total_tasks": dag.number_of_nodes(),
            "total_dependencies": dag.number_of_edges(),
            "estimated_total_duration": sum(
                dag.nodes[node]["task_node"].estimated_duration for node in dag.nodes()
            ),
            "critical_path_duration": sum(
                dag.nodes[task_id]["task_node"].estimated_duration
                for task_id in self._find_critical_path(dag)
            ),
            "required_capabilities": list(goal_analysis["required_capabilities"]),
            "complexity_level": goal_analysis["complexity_level"],
            "parallel_opportunities": len(self._identify_parallel_groups(dag)),
        }

    def get_execution_order(self, dag: nx.DiGraph) -> list[str]:
        """Get optimal execution order using topological sort.

        Args:
            dag: Workflow DAG

        Returns:
            List of task IDs in optimal execution order
        """
        try:
            return list(nx.topological_sort(dag))
        except nx.NetworkXError as e:
            self.logger.error(f"Failed to compute execution order: {e}")
            return []

    def get_parallel_execution_stages(self, dag: nx.DiGraph) -> list[list[str]]:
        """Get stages of tasks that can be executed in parallel.

        Args:
            dag: Workflow DAG

        Returns:
            List of stages, each containing task IDs that can run in parallel
        """
        return [list(generation) for generation in nx.topological_generations(dag)]

    def _initialize_task_templates(self) -> dict[str, dict[str, Any]]:
        """Initialize task templates for common operations."""
        return {
            "basic_analysis": {
                "tasks": [TaskType.ANALYZE_PATTERNS, TaskType.EXTRACT_FEATURES],
                "subsystems": [Subsystem.TETRAGNOS],
                "complexity": 1,
            },
            "causal_analysis": {
                "tasks": [TaskType.CAUSAL_DISCOVERY, TaskType.BUILD_CAUSAL_MODEL],
                "subsystems": [Subsystem.TELOS],
                "complexity": 2,
            },
            "logical_analysis": {
                "tasks": [TaskType.CONSISTENCY_CHECK, TaskType.THEOREM_PROVING],
                "subsystems": [Subsystem.THONOC],
                "complexity": 2,
            },
        }

    def _initialize_workflow_templates(self) -> dict[str, WorkflowTemplate]:
        """Initialize predefined workflow templates."""
        return {
            "comprehensive_analysis": WorkflowTemplate(
                name="comprehensive_analysis",
                description="Comprehensive multi-modal analysis workflow",
                task_sequence=[
                    {"type": "analyze_patterns", "subsystem": "tetragnos"},
                    {"type": "causal_discovery", "subsystem": "telos"},
                    {"type": "consistency_check", "subsystem": "thonoc"},
                    {"type": "test_hypothesis", "subsystem": "telos"},
                ],
                dependency_rules=[
                    ("analyze_patterns", "causal_discovery"),
                    ("analyze_patterns", "consistency_check"),
                    ("causal_discovery", "test_hypothesis"),
                    ("consistency_check", "test_hypothesis"),
                ],
            )
        }

    def _initialize_subsystem_capabilities(self) -> dict[Subsystem, set[str]]:
        """Initialize mapping of subsystems to their capabilities."""
        return {
            Subsystem.TETRAGNOS: {
                "pattern_recognition",
                "feature_extraction",
                "clustering",
                "semantic_analysis",
                "translation",
            },
            Subsystem.TELOS: {
                "causal_reasoning",
                "time_series_analysis",
                "prediction",
                "intervention_analysis",
                "hypothesis_testing",
                "forecasting",
            },
            Subsystem.THONOC: {
                "logical_reasoning",
                "theorem_proving",
                "symbolic_computation",
                "modal_reasoning",
                "consistency_checking",
                "proof_construction",
            },
        }

    def _find_matching_template(
        self, capabilities: set[str], complexity: int
    ) -> WorkflowTemplate | None:
        """Find workflow template that matches required capabilities."""
        # Simplified template matching - would be more sophisticated in production
        if len(capabilities) >= 3 and complexity >= 2:
            return self.workflow_templates.get("comprehensive_analysis")
        return None

    def _classify_goal_type(self, goal_description: str) -> str:
        """Classify the type of goal for optimization."""
        goal_lower = goal_description.lower()

        if any(word in goal_lower for word in ["analyze", "understand", "examine"]):
            return "analysis"
        elif any(word in goal_lower for word in ["predict", "forecast", "estimate"]):
            return "prediction"
        elif any(word in goal_lower for word in ["prove", "verify", "validate"]):
            return "verification"
        elif any(word in goal_lower for word in ["solve", "compute", "calculate"]):
            return "computation"
        else:
            return "general"

    def _estimate_resource_requirements(
        self, capabilities: set[str], complexity: int
    ) -> dict[str, float]:
        """Estimate total resource requirements for the workflow."""
        base_cpu = len(capabilities) * 0.5
        base_memory = len(capabilities) * 256

        complexity_multiplier = 1 + (complexity * 0.5)

        return {
            "total_cpu": base_cpu * complexity_multiplier,
            "total_memory": base_memory * complexity_multiplier,
            "estimated_duration": len(capabilities) * 60 * complexity_multiplier,
        }

    def _identify_parallel_opportunities(self, capabilities: set[str]) -> int:
        """Identify opportunities for parallel execution."""
        # Different capability types can often be parallelized
        parallelizable_pairs = [
            ("pattern_recognition", "logical_reasoning"),
            ("causal_reasoning", "symbolic_computation"),
            ("time_series_analysis", "theorem_proving"),
        ]

        parallel_count = 0
        for cap1, cap2 in parallelizable_pairs:
            if cap1 in capabilities and cap2 in capabilities:
                parallel_count += 1

        return parallel_count

    def _create_task_node_from_spec(self, task_spec: dict[str, Any]) -> TaskNode:
        """Create TaskNode from task specification."""
        task_type_str = task_spec.get("type", "")
        subsystem_str = task_spec.get("subsystem", "")

        # Convert strings to enums
        task_type = TaskType(task_type_str) if task_type_str else TaskType.ANALYZE_PATTERNS
        subsystem = Subsystem(subsystem_str) if subsystem_str else Subsystem.TETRAGNOS

        return TaskNode(
            task_id=f"{task_type.value}_{uuid.uuid4().hex[:8]}",
            task_type=task_type,
            subsystem=subsystem,
            payload=task_spec.get("payload", {}),
            estimated_duration=task_spec.get("duration", 30.0),
            priority=task_spec.get("priority", 3),
        )
