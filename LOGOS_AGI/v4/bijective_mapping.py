# --- START OF FILE core/bijective_mapping.py ---

#!/usr/bin/env python3
"""
Bijective Mapping System for LOGOS AGI
Trinity-grounded bijective mappings between logical and transcendental domains

This module implements the OBDC (Orthogonal Dual-Bijection Confluence) kernel
that provides bijective mappings between different domains while preserving
Trinity structure.

File: core/bijective_mapping.py
Author: LOGOS AGI Development Team
Version: 2.0.0
Date: 2025-01-28
"""

import numpy as np
import json
import time
import logging
import hashlib
import os
import sys
from typing import Dict, List, Tuple, Any, Optional, Callable, Set
from dataclasses import dataclass, field
from enum import Enum
from abc import ABC, abstractmethod

# ALIGNMENT CORE: Replace direct mapping with OBDC kernel
sys.path.append(os.path.join(os.path.dirname(__file__), '..', '..'))
from obdc.kernel import OBDCKernel
from logos_core.reference_monitor import ReferenceMonitor

def load_alignment_config():
    """Load alignment core configuration."""
    config_path = os.path.join(os.path.dirname(__file__), '..', '..', 'configs', 'config.json')
    with open(config_path, 'r') as f:
        return json.load(f)

try:
    from core.data_structures import TrinityVector
except ImportError:
    @dataclass
    class TrinityVector:
        logos: float
        pneuma: float
        sarx: float
        
        def __init__(self, logos: float = 1/3, pneuma: float = 1/3, sarx: float = 1/3):
            self.logos = logos
            self.pneuma = pneuma
            self.sarx = sarx

# =========================================================================
# I. DOMAIN DEFINITIONS
# =========================================================================

class DomainType(Enum):
    """Types of domains in bijective mappings"""
    LOGICAL = "logical"                 # Logical/symbolic domain
    TRANSCENDENTAL = "transcendental"   # Transcendental/metaphysical domain
    MATHEMATICAL = "mathematical"       # Mathematical domain
    SEMANTIC = "semantic"              # Semantic/linguistic domain
    CAUSAL = "causal"                  # Causal domain
    TEMPORAL = "temporal"              # Temporal domain

@dataclass
class Domain:
    """Mathematical domain for bijective mappings"""
    domain_id: str
    name: str
    domain_type: DomainType
    elements: Set[Any] = field(default_factory=set)
    operations: Dict[str, Callable] = field(default_factory=dict)
    properties: Dict[str, Any] = field(default_factory=dict)
    trinity_grounding: TrinityVector = field(default_factory=lambda: TrinityVector(1/3, 1/3, 1/3))
    
    def add_element(self, element: Any) -> bool:
        """Add element to domain"""
        if element not in self.elements:
            self.elements.add(element)
            return True
        return False
    
    def add_operation(self, name: str, operation: Callable) -> bool:
        """Add operation to domain"""
        if name not in self.operations:
            self.operations[name] = operation
            return True
        return False
    
    def validate_element(self, element: Any) -> bool:
        """Validate that element belongs to this domain"""
        return element in self.elements

# =========================================================================
# II. BIJECTIVE MAPPING STRUCTURES
# =========================================================================

@dataclass
class BijectiveMapping:
    """Bijective mapping between two domains"""
    mapping_id: str
    name: str
    source_domain: Domain
    target_domain: Domain
    forward_map: Dict[Any, Any] = field(default_factory=dict)
    inverse_map: Dict[Any, Any] = field(default_factory=dict)
    mapping_function: Optional[Callable] = None
    inverse_function: Optional[Callable] = None
    trinity_preserving: bool = True
    created_at: float = field(default_factory=time.time)
    
    def map_forward(self, source_element: Any) -> Optional[Any]:
        """Map element from source to target domain.
        
        ALIGNMENT CORE: All mappings now go through OBDC kernel with proofs.
        """
        
        # Check if element is in source domain
        if not self.source_domain.validate_element(source_element):
            return None
        
        # ALIGNMENT CORE: Use OBDC kernel for structure-preserving mapping
        alignment_config = load_alignment_config()
        obdc_kernel = OBDCKernel(alignment_config)
        reference_monitor = ReferenceMonitor(alignment_config)
        
        # Require proof for mapping operation
        action = f"bijective_map({self.source_domain.domain_type.value}→{self.target_domain.domain_type.value})"
        provenance = f"bijective_mapping:{self.mapping_id}"
        
        try:
            proof_token = reference_monitor.require_proof_token(action, provenance)
            logging.info(f"Mapping {self.mapping_id} authorized with proof {proof_token}")
        except PermissionError as e:
            logging.error(f"Mapping {self.mapping_id} denied: {e}")
            return None
        
        # Use explicit mapping if available
        if source_element in self.forward_map:
            return self.forward_map[source_element]
        
        # Use mapping function if available
        if self.mapping_function:
            try:
                return self.mapping_function(source_element)
            except Exception:
                return None
        
        return None
    
    def map_inverse(self, target_element: Any) -> Optional[Any]:
        """Map element from target to source domain"""
        
        # Check if element is in target domain
        if not self.target_domain.validate_element(target_element):
            return None
        
        # Use explicit inverse mapping if available
        if target_element in self.inverse_map:
            return self.inverse_map[target_element]
        
        # Use inverse function if available
        if self.inverse_function:
            try:
                return self.inverse_function(target_element)
            except Exception:
                return None
        
        return None
    
    def add_mapping_pair(self, source_element: Any, target_element: Any) -> bool:
        """Add bijective mapping pair"""
        
        # Validate elements belong to respective domains
        if not self.source_domain.validate_element(source_element):
            return False
        if not self.target_domain.validate_element(target_element):
            return False
        
        # Check for conflicts
        if source_element in self.forward_map and self.forward_map[source_element] != target_element:
            return False
        if target_element in self.inverse_map and self.inverse_map[target_element] != source_element:
            return False
        
        # Add mapping
        self.forward_map[source_element] = target_element
        self.inverse_map[target_element] = source_element
        
        return True
    
    def verify_bijection(self) -> Dict[str, Any]:
        """Verify that mapping is truly bijective"""
        
        # Check that forward mapping is injective (one-to-one)
        forward_values = list(self.forward_map.values())
        injective = len(forward_values) == len(set(forward_values))
        
        # Check that inverse mapping is consistent
        inverse_consistent = True
        for source, target in self.forward_map.items():
            if target not in self.inverse_map or self.inverse_map[target] != source:
                inverse_consistent = False
                break
        
        # Check surjectivity (onto) - all target elements are mapped to
        target_elements_mapped = set(self.forward_map.values())
        all_target_elements = self.target_domain.elements
        surjective = target_elements_mapped == all_target_elements
        
        return {
            "injective": injective,
            "surjective": surjective,
            "bijective": injective and surjective,
            "inverse_consistent": inverse_consistent,
            "total_mappings": len(self.forward_map)
        }

# =========================================================================
# III. TRINITY CONFLUENCE SYSTEM
# =========================================================================

class TrinityConfluence:
    """Ensures Trinity structure is preserved across bijective mappings"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)
    
    def verify_trinity_preservation(self, mapping: BijectiveMapping) -> Dict[str, Any]:
        """Verify that bijective mapping preserves Trinity structure"""
        
        # Check if domains have Trinity grounding
        source_trinity = mapping.source_domain.trinity_grounding
        target_trinity = mapping.target_domain.trinity_grounding
        
        # Calculate Trinity preservation score
        trinity_distance = self._calculate_trinity_distance(source_trinity, target_trinity)
        trinity_preserved = trinity_distance < 0.1  # Tolerance threshold
        
        # Check Trinity product preservation
        source_product = source_trinity.trinity_product()
        target_product = target_trinity.trinity_product()
        product_preserved = abs(source_product - target_product) < 0.01
        
        return {
            "trinity_preserved": trinity_preserved,
            "trinity_distance": trinity_distance,
            "product_preserved": product_preserved,
            "source_trinity_product": source_product,
            "target_trinity_product": target_product
        }
    
    def _calculate_trinity_distance(self, trinity1: TrinityVector, trinity2: TrinityVector) -> float:
        """Calculate distance between two Trinity vectors"""
        
        dx = trinity1.existence - trinity2.existence
        dy = trinity1.goodness - trinity2.goodness
        dz = trinity1.truth - trinity2.truth
        
        return (dx**2 + dy**2 + dz**2)**0.5
    
    def enforce_trinity_confluence(self, mappings: List[BijectiveMapping]) -> Dict[str, Any]:
        """Enforce confluence across multiple bijective mappings"""
        
        confluence_violations = []
        
        # Check all pairs of mappings for confluence
        for i, mapping1 in enumerate(mappings):
            for mapping2 in mappings[i+1:]:
                confluence = self._check_mapping_confluence(mapping1, mapping2)
                if not confluence["confluent"]:
                    confluence_violations.append({
                        "mapping1": mapping1.mapping_id,
                        "mapping2": mapping2.mapping_id,
                        "violation": confluence["violation_reason"]
                    })
        
        return {
            "confluent": len(confluence_violations) == 0,
            "violations": confluence_violations,
            "total_mappings": len(mappings)
        }
    
    def _check_mapping_confluence(self, mapping1: BijectiveMapping, mapping2: BijectiveMapping) -> Dict[str, Any]:
        """Check confluence between two mappings"""
        
        # If mappings share domains, check for conflicts
        if mapping1.target_domain == mapping2.source_domain:
            # Composition should be well-defined
            return self._check_composition_confluence(mapping1, mapping2)
        
        # If no shared domains, they're automatically confluent
        return {"confluent": True, "violation_reason": None}
    
    def _check_composition_confluence(self, mapping1: BijectiveMapping, mapping2: BijectiveMapping) -> Dict[str, Any]:
        """Check confluence for composable mappings"""
        
        # Check that composition is well-defined
        for source_element in mapping1.forward_map:
            intermediate = mapping1.map_forward(source_element)
            if intermediate is not None:
                final = mapping2.map_forward(intermediate)
                if final is None:
                    return {
                        "confluent": False,
                        "violation_reason": f"Composition breaks at {intermediate}"
                    }
        
        return {"confluent": True, "violation_reason": None}

# =========================================================================
# IV. OBDC KERNEL IMPLEMENTATION
# =========================================================================

class OBDCKernel:
    """Orthogonal Dual-Bijection Confluence Kernel"""
    
    def __init__(self):
        self.domains: Dict[str, Domain] = {}
        self.mappings: Dict[str, BijectiveMapping] = {}
        self.confluence_system = TrinityConfluence()
        self.logger = logging.getLogger(__name__)
        
        # Initialize fundamental domains
        self._initialize_fundamental_domains()
    
    def _initialize_fundamental_domains(self):
        """Initialize fundamental domains for LOGOS system"""
        
        # Logical Domain
        logical_domain = Domain(
            domain_id="logical",
            name="Logical Domain",
            domain_type=DomainType.LOGICAL,
            trinity_grounding=TrinityVector(0.2, 0.3, 0.5)  # Higher truth weight
        )
        logical_domain.elements.update([True, False, "unknown", "contradiction"])
        self.add_domain(logical_domain)
        
        # Transcendental Domain
        transcendental_domain = Domain(
            domain_id="transcendental",
            name="Transcendental Domain", 
            domain_type=DomainType.TRANSCENDENTAL,
            trinity_grounding=TrinityVector(0.5, 0.3, 0.2)  # Higher existence weight
        )
        transcendental_domain.elements.update(["being", "essence", "form", "unity"])
        self.add_domain(transcendental_domain)
        
        # Mathematical Domain
        mathematical_domain = Domain(
            domain_id="mathematical",
            name="Mathematical Domain",
            domain_type=DomainType.MATHEMATICAL,
            trinity_grounding=TrinityVector(0.4, 0.2, 0.4)  # Balanced existence and truth
        )
        mathematical_domain.elements.update([0, 1, -1, "infinity", "pi", "e"])
        self.add_domain(mathematical_domain)
        
        # Semantic Domain
        semantic_domain = Domain(
            domain_id="semantic",
            name="Semantic Domain",
            domain_type=DomainType.SEMANTIC,
            trinity_grounding=TrinityVector(0.3, 0.5, 0.2)  # Higher goodness weight
        )
        semantic_domain.elements.update(["meaning", "reference", "symbol", "concept"])
        self.add_domain(semantic_domain)
        
        self.logger.info("Initialized fundamental domains")
    
    def add_domain(self, domain: Domain) -> bool:
        """Add domain to kernel"""
        if domain.domain_id in self.domains:
            self.logger.warning(f"Domain {domain.domain_id} already exists")
            return False
        
        self.domains[domain.domain_id] = domain
        self.logger.info(f"Added domain: {domain.name}")
        return True
    
    def add_mapping(self, mapping: BijectiveMapping) -> bool:
        """Add bijective mapping to kernel"""
        if mapping.mapping_id in self.mappings:
            self.logger.warning(f"Mapping {mapping.mapping_id} already exists")
            return False
        
        # Verify Trinity preservation
        trinity_check = self.confluence_system.verify_trinity_preservation(mapping)
        if not trinity_check["trinity_preserved"]:
            self.logger.error(f"Mapping {mapping.mapping_id} violates Trinity preservation")
            return False
        
        self.mappings[mapping.mapping_id] = mapping
        self.logger.info(f"Added mapping: {mapping.name}")
        return True
    
    def create_fundamental_mappings(self):
        """Create fundamental bijective mappings between core domains"""
        
        # Logical ↔ Transcendental mapping
        logical_transcendental = BijectiveMapping(
            mapping_id="logical_transcendental",
            name="Logical-Transcendental Bijection",
            source_domain=self.domains["logical"],
            target_domain=self.domains["transcendental"]
        )
        
        # Define explicit mappings
        logical_transcendental.add_mapping_pair(True, "being")
        logical_transcendental.add_mapping_pair(False, "essence")
        logical_transcendental.add_mapping_pair("unknown", "form")
        logical_transcendental.add_mapping_pair("contradiction", "unity")
        
        self.add_mapping(logical_transcendental)
        
        # Mathematical ↔ Semantic mapping
        mathematical_semantic = BijectiveMapping(
            mapping_id="mathematical_semantic",
            name="Mathematical-Semantic Bijection",
            source_domain=self.domains["mathematical"],
            target_domain=self.domains["semantic"]
        )
        
        mathematical_semantic.add_mapping_pair(0, "reference")
        mathematical_semantic.add_mapping_pair(1, "meaning")
        mathematical_semantic.add_mapping_pair(-1, "symbol")
        mathematical_semantic.add_mapping_pair("infinity", "concept")
        
        self.add_mapping(mathematical_semantic)
        
        self.logger.info("Created fundamental bijective mappings")
    
    def compose_mappings(self, mapping1_id: str, mapping2_id: str) -> Optional[BijectiveMapping]:
        """Compose two bijective mappings"""
        
        if mapping1_id not in self.mappings or mapping2_id not in self.mappings:
            self.logger.error("One or both mappings not found")
            return None
        
        mapping1 = self.mappings[mapping1_id]
        mapping2 = self.mappings[mapping2_id]
        
        # Check composability
        if mapping1.target_domain != mapping2.source_domain:
            self.logger.error("Mappings are not composable")
            return None
        
        # Create composed mapping
        composed = BijectiveMapping(
            mapping_id=f"composed_{mapping1_id}_{mapping2_id}",
            name=f"Composition: {mapping1.name} ∘ {mapping2.name}",
            source_domain=mapping1.source_domain,
            target_domain=mapping2.target_domain
        )
        
        # Compute composition
        for source_element in mapping1.forward_map:
            intermediate = mapping1.map_forward(source_element)
            if intermediate is not None:
                final = mapping2.map_forward(intermediate)
                if final is not None:
                    composed.add_mapping_pair(source_element, final)
        
        return composed
    
    def verify_kernel_integrity(self) -> Dict[str, Any]:
        """Verify overall OBDC kernel integrity"""
        
        # Verify all mappings are bijective
        bijection_results = {}
        for mapping_id, mapping in self.mappings.items():
            bijection_results[mapping_id] = mapping.verify_bijection()
        
        # Verify Trinity confluence
        confluence_result = self.confluence_system.enforce_trinity_confluence(list(self.mappings.values()))
        
        # Verify Trinity preservation
        trinity_preservation = {}
        for mapping_id, mapping in self.mappings.items():
            trinity_preservation[mapping_id] = self.confluence_system.verify_trinity_preservation(mapping)
        
        all_bijective = all(result["bijective"] for result in bijection_results.values())
        all_trinity_preserved = all(result["trinity_preserved"] for result in trinity_preservation.values())
        
        return {
            "kernel_integrity": all_bijective and confluence_result["confluent"] and all_trinity_preserved,
            "bijection_results": bijection_results,
            "confluence_result": confluence_result,
            "trinity_preservation": trinity_preservation,
            "total_domains": len(self.domains),
            "total_mappings": len(self.mappings)
        }
    
    def get_mapping_path(self, source_domain_id: str, target_domain_id: str) -> Optional[List[str]]:
        """Find bijective mapping path between domains"""
        
        if source_domain_id not in self.domains or target_domain_id not in self.domains:
            return None
        
        # Simple BFS to find path
        from collections import deque
        
        queue = deque([(source_domain_id, [])])
        visited = set()
        
        while queue:
            current_domain, path = queue.popleft()
            
            if current_domain == target_domain_id:
                return path
            
            if current_domain in visited:
                continue
            
            visited.add(current_domain)
            
            # Find mappings from current domain
            for mapping_id, mapping in self.mappings.items():
                if mapping.source_domain.domain_id == current_domain:
                    next_domain = mapping.target_domain.domain_id
                    if next_domain not in visited:
                        queue.append((next_domain, path + [mapping_id]))
                
                # Also check inverse direction
                if mapping.target_domain.domain_id == current_domain:
                    next_domain = mapping.source_domain.domain_id
                    if next_domain not in visited:
                        queue.append((next_domain, path + [f"{mapping_id}_inverse"]))
        
        return None
    
    def map_across_domains(self, element: Any, source_domain_id: str, target_domain_id: str) -> Optional[Any]:
        """Map element across multiple domains using bijective path"""
        
        # Find mapping path
        path = self.get_mapping_path(source_domain_id, target_domain_id)
        if not path:
            return None
        
        current_element = element
        
        # Follow the path
        for mapping_step in path:
            if mapping_step.endswith("_inverse"):
                mapping_id = mapping_step[:-8]  # Remove "_inverse"
                mapping = self.mappings[mapping_id]
                current_element = mapping.map_inverse(current_element)
            else:
                mapping = self.mappings[mapping_step]
                current_element = mapping.map_forward(current_element)
            
            if current_element is None:
                return None
        
        return current_element

# =========================================================================
# V. MODULE EXPORTS
# =========================================================================

__all__ = [
    'DomainType',
    'Domain',
    'BijectiveMapping',
    'TrinityConfluence',
    'OBDCKernel'
]

# Create global OBDC kernel instance
_global_obdc_kernel = None

def get_global_obdc_kernel() -> OBDCKernel:
    """Get the global OBDC kernel instance"""
    global _global_obdc_kernel
    if _global_obdc_kernel is None:
        _global_obdc_kernel = OBDCKernel()
        _global_obdc_kernel.create_fundamental_mappings()
    return _global_obdc_kernel

def verify_obdc_system() -> Dict[str, Any]:
    """Verify the complete OBDC system"""
    
    kernel = get_global_obdc_kernel()
    integrity_result = kernel.verify_kernel_integrity()
    
    return {
        "obdc_system_operational": integrity_result["kernel_integrity"],
        "details": integrity_result
    }

# --- END OF FILE core/bijective_mapping.py ---