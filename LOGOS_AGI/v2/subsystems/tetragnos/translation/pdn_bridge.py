"""3PDN Translation Bridge

Bidirectional translation bridge between natural language and Lambda Logos
ontological representations. Implements the 3PDN (SIGN → MIND → BRIDGE)
translation layers with support for trinity vector extraction.

Dependencies: typing, json, re
"""

from typing import Dict, List, Tuple, Optional, Union, Any
import re
import json
import logging

# Import from other modules (adjust paths as needed)
from ..core.lambda_engine import LogosExpr, Variable, Value, Application, SufficientReason, LambdaEngine
from ..ontology.trinity_vector import TrinityVector
from ..utils.data_structures import OntologicalType

logger = logging.getLogger(__name__)

class TranslationResult:
    """Holds results of 3PDN translation."""
    
    def __init__(self, 
                query: str, 
                trinity_vector: TrinityVector,
                layers: Dict[str, Any] = None):
        """Initialize translation result.
        
        Args:
            query: Original query string
            trinity_vector: Extracted trinity vector
            layers: 3PDN layer data
        """
        self.query = query
        self.trinity_vector = trinity_vector
        self.layers = layers or {
            "SIGN": [],       # Lexical/token layer
            "MIND": {},       # Semantic/meaning layer
            "BRIDGE": {}      # Ontological mapping layer
        }
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary representation."""
        return {
            "query": self.query,
            "trinity_vector": self.trinity_vector.to_dict(),
            "layers": self.layers
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'TranslationResult':
        """Create from dictionary representation."""
        trinity_data = data.get("trinity_vector", {})
        if isinstance(trinity_data, dict):
            trinity_vector = TrinityVector.from_dict(trinity_data)
        else:
            trinity_vector = TrinityVector(*trinity_data)
            
        return cls(
            query=data.get("query", ""),
            trinity_vector=trinity_vector,
            layers=data.get("layers", {})
        )

class PDNBridge:
    """Bridge between natural language and Lambda Logos."""
    
    def __init__(self, lambda_engine: Optional[LambdaEngine] = None):
        """Initialize PDN bridge.
        
        Args:
            lambda_engine: Lambda engine instance
        """
        self.lambda_engine = lambda_engine
        
        # Dictionary of common terms for quick translation
        self.common_terms = self._initialize_common_terms()
        
        # Semantic categories for MIND layer
        self.semantic_categories = {
            "ontological": ["exists", "being", "reality", "substance", "exist"],
            "moral": ["good", "evil", "right", "wrong", "ought", "justice"],
            "epistemic": ["know", "truth", "knowledge", "believe", "fact"],
            "causal": ["cause", "effect", "result", "origin", "create"],
            "modal": ["necessary", "possible", "impossible", "contingent"],
            "logical": ["follows", "entails", "implies", "contradicts"]
        }
        
        logger.info("PDN Bridge initialized")
    
    def _initialize_common_terms(self) -> Dict[str, LogosExpr]:
        """Initialize dictionary of common Lambda terms.
        
        Returns:
            Dictionary of common terms
        """
        if not self.lambda_engine:
            logger.warning("Lambda engine not available for term initialization")
            return {}
            
        # Ontological values
        ei_val = self.lambda_engine.create_value("ei", "EXISTENCE")
        og_val = self.lambda_engine.create_value("og", "GOODNESS")
        at_val = self.lambda_engine.create_value("at", "TRUTH")
        
        # Sufficient reason operators
        sr_eg = self.lambda_engine.create_sr("EXISTENCE", "GOODNESS", 3)
        sr_gt = self.lambda_engine.create_sr("GOODNESS", "TRUTH", 2)
        
        # Basic applications
        eg_app = self.lambda_engine.create_application(sr_eg, ei_val)
        gt_app = self.lambda_engine.create_application(sr_gt, og_val)
        
        # Connect dictionary
        return {
            "existence": ei_val,
            "goodness": og_val,
            "truth": at_val,
            "sr_eg": sr_eg,
            "sr_gt": sr_gt,
            "existence_implies_goodness": eg_app,
            "goodness_implies_truth": gt_app
        }
    
    def natural_to_lambda(self, query: str, translation_result: Optional[Dict[str, Any]] = None) -> Tuple[LogosExpr, Dict[str, Any]]:
        """Convert natural language to Lambda expression.
        
        Args:
            query: Natural language query
            translation_result: Optional external translation result
            
        Returns:
            (Lambda expression, Translation result) tuple
        """
        # If translation result provided, use it
        if translation_result:
            return self._translation_to_lambda(translation_result), translation_result
        
        # Otherwise, create a translation result
        translation = self._translate(query)
        lambda_expr = self._translation_to_lambda(translation.to_dict())
        
        return lambda_expr, translation.to_dict()
    
    def _translate(self, query: str) -> TranslationResult:
        """Translate natural language to 3PDN representation.
        
        Args:
            query: Natural language query
            
        Returns:
            Translation result
        """
        # SIGN layer: Extract tokens/keywords
        sign_layer = self._extract_sign_layer(query)
        
        # MIND layer: Map to semantic categories
        mind_layer = self._extract_mind_layer(sign_layer)
        
        # BRIDGE layer: Map to ontological dimensions
        bridge_layer = self._extract_bridge_layer(mind_layer)
        
        # Extract trinity vector
        trinity_vector = TrinityVector(
            existence=bridge_layer.get("existence", 0.5),
            goodness=bridge_layer.get("goodness", 0.5),
            truth=bridge_layer.get("truth", 0.5)
        )
        
        # Create layers dictionary
        layers = {
            "SIGN": sign_layer,
            "MIND": mind_layer,
            "BRIDGE": bridge_layer
        }
        
        return TranslationResult(query, trinity_vector, layers)
    
    def _extract_sign_layer(self, query: str) -> List[str]:
        """Extract SIGN layer (tokens) from query.
        
        Args:
            query: Natural language query
            
        Returns:
            List of tokens
        """
        # Tokenize and normalize
        tokens = [
            token.lower() 
            for token in re.findall(r'\b\w+\b', query)
            if len(token) > 1 and token.lower() not in ["the", "a", "an", "is", "are", "to"]
        ]
        
        return tokens
    
    def _extract_mind_layer(self, sign_layer: List[str]) -> Dict[str, float]:
        """Extract MIND layer (semantic categories) from SIGN layer.
        
        Args:
            sign_layer: SIGN layer tokens
            
        Returns:
            Semantic category weights
        """
        # Initialize categories
        categories = {
            "ontological": 0.0,
            "moral": 0.0,
            "epistemic": 0.0,
            "causal": 0.0,
            "modal": 0.0,
            "logical": 0.0
        }
        
        # Count matches in each category
        for token in sign_layer:
            for category, keywords in self.semantic_categories.items():
                if any(token == keyword or token.startswith(keyword) for keyword in keywords):
                    categories[category] += 1.0
        
        # Normalize to range [0,1]
        total = sum(categories.values())
        if total > 0:
            categories = {k: v / total for k, v in categories.items()}
        else:
            # Default to slight ontological bias if no clear category
            categories["ontological"] = 0.4
            categories["epistemic"] = 0.3
            categories["moral"] = 0.3
        
        return categories
    
    def _extract_bridge_layer(self, mind_layer: Dict[str, float]) -> Dict[str, float]:
        """Extract BRIDGE layer (ontological dimensions) from MIND layer.
        
        Args:
            mind_layer: MIND layer semantic categories
            
        Returns:
            Ontological dimension values
        """
        # Initialize dimensions with neutral values
        dimensions = {
            "existence": 0.5,
            "goodness": 0.5,
            "truth": 0.5
        }
        
        # Apply semantic category weights to dimensions
        # Ontological primarily affects existence
        dimensions["existence"] += 0.4 * mind_layer.get("ontological", 0)
        
        # Moral primarily affects goodness
        dimensions["goodness"] += 0.4 * mind_layer.get("moral", 0)
        
        # Epistemic primarily affects truth
        dimensions["truth"] += 0.4 * mind_layer.get("epistemic", 0)
        
        # Secondary effects
        dimensions["existence"] += 0.2 * mind_layer.get("causal", 0)
        dimensions["truth"] += 0.2 * mind_layer.get("logical", 0)
        
        # Modal affects all dimensions
        modal_factor = 0.1 * mind_layer.get("modal", 0)
        dimensions["existence"] += modal_factor
        dimensions["goodness"] += modal_factor
        dimensions["truth"] += modal_factor
        
        # Ensure values are in range [0,1]
        for dim in dimensions:
            dimensions[dim] = max(0.0, min(1.0, dimensions[dim]))
        
        return dimensions
    
    def _translation_to_lambda(self, translation: Dict[str, Any]) -> LogosExpr:
        """Convert 3PDN translation to Lambda expression.
        
        Args:
            translation: 3PDN translation result
            
        Returns:
            Lambda expression
        """
        if not self.lambda_engine:
            logger.warning("Lambda engine not available for translation")
            return None
            
        # Extract trinity vector
        trinity_data = translation.get("trinity_vector", {})
        if isinstance(trinity_data, dict):
            trinity = (
                trinity_data.get("existence", 0.5),
                trinity_data.get("goodness", 0.5),
                trinity_data.get("truth", 0.5)
            )
        else:
            trinity = trinity_data
        
        # Determine strongest dimension
        dims = [("existence", trinity[0]), ("goodness", trinity[1]), ("truth", trinity[2])]
        primary_dim = max(dims, key=lambda x: x[1])
        
        # Create expression based on primary dimension
        if primary_dim[0] == "existence":
            return self.common_terms["existence"]
        elif primary_dim[0] == "goodness":
            return self.common_terms["goodness"]
        elif primary_dim[0] == "truth":
            return self.common_terms["truth"]
        
        # Default fallback
        return self.common_terms["existence"]
    
    def lambda_to_natural(self, expr: LogosExpr) -> str:
        """Convert Lambda expression to natural language.
        
        Args:
            expr: Lambda expression
            
        Returns:
            Natural language representation
        """
        if not expr:
            return "undefined expression"
            
        # Basic conversion based on expression type
        if isinstance(expr, Variable):
            if expr.onto_type == OntologicalType.EXISTENCE:
                return f"a concept of existence named {expr.name}"
            elif expr.onto_type == OntologicalType.GOODNESS:
                return f"a concept of goodness named {expr.name}"
            elif expr.onto_type == OntologicalType.TRUTH:
                return f"a concept of truth named {expr.name}"
            else:
                return f"a variable named {expr.name}"
        
        elif isinstance(expr, Value):
            if expr.value == "ei":
                return "existence itself"
            elif expr.value == "og":
                return "objective goodness"
            elif expr.value == "at":
                return "absolute truth"
            else:
                return f"the value {expr.value}"
        
        elif isinstance(expr, SufficientReason):
            if (expr.source_type == OntologicalType.EXISTENCE and 
                expr.target_type == OntologicalType.GOODNESS):
                return "the principle that existence implies goodness"
            elif (expr.source_type == OntologicalType.GOODNESS and 
                  expr.target_type == OntologicalType.TRUTH):
                return "the principle that goodness implies truth"
            else:
                return f"a sufficient reason operator from {expr.source_type.value} to {expr.target_type.value}"
        
        elif isinstance(expr, Application):
            # Handle common applications
            func_str = str(expr.func)
            arg_str = str(expr.arg)
            
            # Special case for common patterns
            if func_str == str(self.common_terms.get("sr_eg", "")) and arg_str == "ei:𝔼":
                return "existence implies goodness"
            elif func_str == str(self.common_terms.get("sr_gt", "")) and arg_str == "og:𝔾":
                return "goodness implies truth"
            else:
                func_natural = self.lambda_to_natural(expr.func)
                arg_natural = self.lambda_to_natural(expr.arg)
                return f"the application of {func_natural} to {arg_natural}"
        
        # Default fallback
        return str(expr)
    
    def lambda_to_3pdn(self, expr: LogosExpr) -> Dict[str, Any]:
        """Convert Lambda expression to 3PDN representation.
        
        Args:
            expr: Lambda expression
            
        Returns:
            3PDN representation with SIGN, MIND, BRIDGE layers
        """
        # Extract type information
        type_info = self._extract_type_info(expr)
        
        # Generate semantic categories
        semantic = self._map_to_semantic(type_info)
        
        # Generate ontological dimensions
        ontological = self._map_to_ontological(semantic)
        
        # Create 3PDN representation
        return {
            "layers": {
                "SIGN": self._expr_to_sign(expr),
                "MIND": semantic,
                "BRIDGE": ontological
            },
            "trinity_vector": (
                ontological.get("existence", 0.5),
                ontological.get("goodness", 0.5),
                ontological.get("truth", 0.5)
            ),
            "expr": str(expr)
        }
    
    def _extract_type_info(self, expr: LogosExpr) -> Dict[str, Any]:
        """Extract type information from Lambda expression.
        
        Args:
            expr: Lambda expression
            
        Returns:
            Type information dictionary
        """
        # Simple implementation - would use Lambda engine's type checker in full system
        if isinstance(expr, Variable):
            return {"type": "simple", "value": expr.onto_type}
        
        elif isinstance(expr, Value):
            return {"type": "simple", "value": expr.onto_type}
        
        elif isinstance(expr, SufficientReason):
            return {
                "type": "sr",
                "source": expr.source_type,
                "target": expr.target_type
            }
        
        elif isinstance(expr, Application):
            # Recursive type extraction
            func_type = self._extract_type_info(expr.func)
            arg_type = self._extract_type_info(expr.arg)
            
            return {
                "type": "application",
                "func_type": func_type,
                "arg_type": arg_type
            }
        
        # Default type info
        return {"type": "unknown"}
    
    def _map_to_semantic(self, type_info: Dict[str, Any]) -> Dict[str, float]:
        """Map type information to semantic categories.
        
        Args:
            type_info: Type information
            
        Returns:
            Semantic category weights
        """
        # Initialize with default values
        semantic = {
            "ontological": 0.0,
            "moral": 0.0,
            "epistemic": 0.0,
            "causal": 0.0,
            "modal": 0.0,
            "logical": 0.0
        }
        
        # Map simple types directly
        if type_info.get("type") == "simple":
            value = type_info.get("value")
            if value == OntologicalType.EXISTENCE:
                semantic["ontological"] = 0.8
                semantic["causal"] = 0.2
            elif value == OntologicalType.GOODNESS:
                semantic["moral"] = 0.9
                semantic["ontological"] = 0.1
            elif value == OntologicalType.TRUTH:
                semantic["epistemic"] = 0.7
                semantic["logical"] = 0.3
        
        # Map SR operators
        elif type_info.get("type") == "sr":
            source = type_info.get("source")
            target = type_info.get("target")
            
            if source == OntologicalType.EXISTENCE and target == OntologicalType.GOODNESS:
                semantic["ontological"] = 0.5
                semantic["moral"] = 0.5
            elif source == OntologicalType.GOODNESS and target == OntologicalType.TRUTH:
                semantic["moral"] = 0.4
                semantic["epistemic"] = 0.6
        
        # Map applications
        elif type_info.get("type") == "application":
            # Combine function and argument semantics
            func_type = type_info.get("func_type", {})
            arg_type = type_info.get("arg_type", {})
            
            if func_type.get("type") == "sr" and arg_type.get("type") == "simple":
                # Specific handling for SR applications
                source = func_type.get("source")
                target = func_type.get("target")
                arg_value = arg_type.get("value")
                
                if source == arg_value:
                    # Valid SR application - emphasize target dimension
                    if target == OntologicalType.GOODNESS:
                        semantic["moral"] = 0.7
                        semantic["ontological"] = 0.3
                    elif target == OntologicalType.TRUTH:
                        semantic["epistemic"] = 0.7
                        semantic["moral"] = 0.3
        
        return semantic
    
    def _map_to_ontological(self, semantic: Dict[str, float]) -> Dict[str, float]:
        """Map semantic categories to ontological dimensions.
        
        Args:
            semantic: Semantic categories
            
        Returns:
            Ontological dimension values
        """
        # Initialize with neutral values
        ontological = {
            "existence": 0.5,
            "goodness": 0.5,
            "truth": 0.5
        }
        
        # Apply semantic weights to dimensions
        if semantic.get("ontological", 0) > 0:
            ontological["existence"] = 0.5 + 0.5 * semantic["ontological"]
        
        if semantic.get("moral", 0) > 0:
            ontological["goodness"] = 0.5 + 0.5 * semantic["moral"]
        
        if semantic.get("epistemic", 0) > 0:
            ontological["truth"] = 0.5 + 0.5 * semantic["epistemic"]
        
        if semantic.get("logical", 0) > 0:
            ontological["truth"] = max(ontological["truth"], 0.5 + 0.4 * semantic["logical"])
        
        if semantic.get("causal", 0) > 0:
            ontological["existence"] = max(ontological["existence"], 0.5 + 0.3 * semantic["causal"])
        
        # Ensure values are within [0, 1]
        for key in ontological:
            ontological[key] = min(max(ontological[key], 0), 1)
        
        return ontological
    
    def _expr_to_sign(self, expr: LogosExpr) -> List[str]:
        """Convert expression to SIGN layer tokens.
        
        Args:
            expr: Lambda expression
            
        Returns:
            List of tokens
        """
        # Convert to string and tokenize
        expr_str = str(expr)
        tokens = expr_str.replace('(', ' ( ').replace(')', ' ) ').replace('.', ' . ').split()
        
        # Filter and clean
        return [token for token in tokens if token.strip()]

class PDNBottleneckSolver:
    """Specialized tooling for addressing the 3PDN bottleneck."""
    
    def __init__(self, bridge: PDNBridge):
        """Initialize bottleneck solver.
        
        Args:
            bridge: PDN bridge instance
        """
        self.bridge = bridge
    
    def create_lambda_target(self, query: str, translation_result: Dict[str, Any]) -> Dict[str, Any]:
        """Create optimized Lambda target from translation result.
        
        Args:
            query: Original query
            translation_result: Translation result
            
        Returns:
            Lambda target data
        """
        # Extract trinity vector
        trinity_data = translation_result.get("trinity_vector", {})
        if isinstance(trinity_data, dict):
            trinity = (
                trinity_data.get("existence", 0.5),
                trinity_data.get("goodness", 0.5),
                trinity_data.get("truth", 0.5)
            )
        else:
            trinity = trinity_data
        
        # Determine strongest dimensions (top 2)
        dims = [
            ("existence", trinity[0]), 
            ("goodness", trinity[1]), 
            ("truth", trinity[2])
        ]
        dims.sort(key=lambda x: x[1], reverse=True)
        
        # Create Lambda target based on dimensions
        if dims[0][0] == "existence":
            # Existence-focused
            if dims[1][0] == "goodness" and dims[1][1] > 0.6:
                # Existence implies goodness
                target = self.bridge.common_terms.get("existence_implies_goodness")
            else:
                # Pure existence
                target = self.bridge.common_terms.get("existence")
                
        elif dims[0][0] == "goodness":
            # Goodness-focused
            if dims[1][0] == "truth" and dims[1][1] > 0.6:
                # Goodness implies truth
                target = self.bridge.common_terms.get("goodness_implies_truth")
            else:
                # Pure goodness
                target = self.bridge.common_terms.get("goodness")
                
        elif dims[0][0] == "truth":
            # Truth-focused
            target = self.bridge.common_terms.get("truth")
        
        else:
            # Default fallback
            target = self.bridge.common_terms.get("existence")
        
        # Generate target data
        target_data = {
            "query": query,
            "trinity_vector": trinity,
            "lambda_expr": str(target),
            "lambda_dict": self.bridge.lambda_engine.expr_to_dict(target) if self.bridge.lambda_engine else {},
            "natural": self.bridge.lambda_to_natural(target)
        }
        
        return target_data