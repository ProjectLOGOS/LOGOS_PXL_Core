"""
Gap Detector - Reasoning Gap Identification Across IEL/PXL

Identifies gaps in reasoning chains, missing inference rules, and potential
areas for IEL extension. Operates passively to detect opportunities for
autonomous system enhancement while preserving formal verification.

Architecture:
- Static analysis of proof dependencies
- Dynamic gap detection during reasoning
- IEL coverage analysis against PXL requirements
- Inference chain completeness validation
- Safety-bounded gap identification

Safety Constraints:
- Read-only analysis of existing proofs
- No modification of core logic without approval
- Bounded computational complexity
- Formal verification preservation
"""

import logging
from typing import Dict, List, Set, Optional, Any, Tuple
from dataclasses import dataclass, field
from pathlib import Path
import json
from datetime import datetime
from collections import defaultdict, deque

from ..unified_formalisms import UnifiedFormalisms


@dataclass
class ReasoningGap:
    """Represents an identified gap in reasoning coverage"""
    gap_type: str  # "missing_rule", "incomplete_chain", "coverage_gap", "boundary_gap"
    domain: str
    description: str
    severity: float  # 0.0 to 1.0
    required_premises: List[str]
    expected_conclusion: str
    suggested_iel: Optional[str] = None
    confidence: float = 0.0
    detected_at: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "gap_type": self.gap_type,
            "domain": self.domain,
            "description": self.description,
            "severity": self.severity,
            "required_premises": self.required_premises,
            "expected_conclusion": self.expected_conclusion,
            "suggested_iel": self.suggested_iel,
            "confidence": self.confidence,
            "detected_at": self.detected_at.isoformat()
        }


@dataclass 
class GapAnalysisResult:
    """Results of gap analysis across the system"""
    total_gaps: int
    gaps_by_type: Dict[str, int]
    gaps_by_domain: Dict[str, int]
    high_priority_gaps: List[ReasoningGap]
    coverage_metrics: Dict[str, float]
    analysis_timestamp: datetime = field(default_factory=datetime.now)


class GapDetector:
    """
    LOGOS Reasoning Gap Detector
    
    Analyzes the completeness of reasoning chains and identifies gaps where
    new IELs might be beneficial. Operates safely within formal verification
    boundaries.
    """
    
    def __init__(self):
        self.logger = self._setup_logging()
        self.unified_formalisms = UnifiedFormalisms()
        
        # Gap detection configuration
        self.min_gap_confidence = 0.3
        self.max_gaps_per_scan = 100
        self.severity_threshold = 0.5
        
        # Cache for performance
        self._premise_cache: Dict[str, Set[str]] = {}
        self._conclusion_cache: Dict[str, Set[str]] = {}
        self._rule_graph: Dict[str, List[str]] = defaultdict(list)
        
    def _setup_logging(self) -> logging.Logger:
        """Configure gap detector logging"""
        logger = logging.getLogger("logos.gap_detector")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger
        
    def detect_reasoning_gaps(self) -> List[ReasoningGap]:
        """
        Main entry point for gap detection
        
        Returns:
            List[ReasoningGap]: Identified reasoning gaps sorted by priority
        """
        self.logger.info("Starting reasoning gap detection")
        
        try:
            gaps = []
            
            # 1. Analyze IEL coverage gaps
            coverage_gaps = self._detect_coverage_gaps()
            gaps.extend(coverage_gaps)
            
            # 2. Analyze inference chain completeness
            chain_gaps = self._detect_chain_gaps()
            gaps.extend(chain_gaps)
            
            # 3. Analyze boundary gaps between domains
            boundary_gaps = self._detect_boundary_gaps()
            gaps.extend(boundary_gaps)
            
            # 4. Analyze missing inference rules
            rule_gaps = self._detect_missing_rules()
            gaps.extend(rule_gaps)
            
            # Filter and prioritize gaps
            filtered_gaps = self._filter_and_prioritize_gaps(gaps)
            
            self.logger.info(f"Gap detection completed: {len(filtered_gaps)} gaps identified")
            return filtered_gaps
            
        except Exception as e:
            self.logger.error(f"Gap detection failed: {e}")
            return []
            
    def analyze_gap_coverage(self) -> GapAnalysisResult:
        """
        Comprehensive gap analysis with metrics
        
        Returns:
            GapAnalysisResult: Detailed analysis of reasoning gap coverage
        """
        gaps = self.detect_reasoning_gaps()
        
        # Group gaps by type and domain
        gaps_by_type = defaultdict(int)
        gaps_by_domain = defaultdict(int)
        
        for gap in gaps:
            gaps_by_type[gap.gap_type] += 1
            gaps_by_domain[gap.domain] += 1
            
        # Identify high priority gaps
        high_priority_gaps = [
            gap for gap in gaps 
            if gap.severity >= self.severity_threshold and gap.confidence >= self.min_gap_confidence
        ]
        
        # Compute coverage metrics
        coverage_metrics = self._compute_coverage_metrics(gaps)
        
        return GapAnalysisResult(
            total_gaps=len(gaps),
            gaps_by_type=dict(gaps_by_type),
            gaps_by_domain=dict(gaps_by_domain),
            high_priority_gaps=high_priority_gaps,
            coverage_metrics=coverage_metrics
        )
        
    def _detect_coverage_gaps(self) -> List[ReasoningGap]:
        """Detect gaps in IEL coverage of reasoning domains"""
        gaps = []
        
        try:
            # Get current IEL coverage
            iel_domains = self._get_iel_domains()
            pxl_requirements = self._get_pxl_requirements()
            
            # Find uncovered requirements
            for domain, requirements in pxl_requirements.items():
                if domain not in iel_domains:
                    gap = ReasoningGap(
                        gap_type="coverage_gap",
                        domain=domain,
                        description=f"No IEL coverage for domain: {domain}",
                        severity=0.8,
                        required_premises=[f"domain_{domain}_requirements"],
                        expected_conclusion=f"iel_coverage_{domain}",
                        confidence=0.9
                    )
                    gaps.append(gap)
                    
                elif len(iel_domains[domain]) < len(requirements):
                    # Partial coverage
                    missing_count = len(requirements) - len(iel_domains[domain])
                    gap = ReasoningGap(
                        gap_type="coverage_gap",
                        domain=domain,
                        description=f"Partial IEL coverage in {domain}: {missing_count} missing rules",
                        severity=0.5 + (missing_count / len(requirements)) * 0.3,
                        required_premises=[f"domain_{domain}_partial"],
                        expected_conclusion=f"iel_complete_{domain}",
                        confidence=0.7
                    )
                    gaps.append(gap)
                    
        except Exception as e:
            self.logger.error(f"Coverage gap detection failed: {e}")
            
        return gaps
        
    def _detect_chain_gaps(self) -> List[ReasoningGap]:
        """Detect incomplete reasoning chains"""
        gaps = []
        
        try:
            # Analyze proof dependency chains
            chains = self._build_proof_chains()
            
            for chain_id, chain in chains.items():
                if self._is_chain_incomplete(chain):
                    missing_steps = self._find_missing_chain_steps(chain)
                    
                    for step in missing_steps:
                        gap = ReasoningGap(
                            gap_type="incomplete_chain",
                            domain=step.get("domain", "unknown"),
                            description=f"Missing reasoning step in chain {chain_id}: {step['description']}",
                            severity=step.get("severity", 0.5),
                            required_premises=step.get("premises", []),
                            expected_conclusion=step.get("conclusion", ""),
                            confidence=step.get("confidence", 0.6)
                        )
                        gaps.append(gap)
                        
        except Exception as e:
            self.logger.error(f"Chain gap detection failed: {e}")
            
        return gaps
        
    def _detect_boundary_gaps(self) -> List[ReasoningGap]:
        """Detect gaps at domain boundaries"""
        gaps = []
        
        try:
            # Find domain interfaces
            domain_interfaces = self._identify_domain_interfaces()
            
            for interface in domain_interfaces:
                if self._has_boundary_gap(interface):
                    gap = ReasoningGap(
                        gap_type="boundary_gap",
                        domain=f"{interface['source']}-{interface['target']}",
                        description=f"Missing connection between {interface['source']} and {interface['target']}",
                        severity=0.6,
                        required_premises=[f"interface_{interface['source']}", f"interface_{interface['target']}"],
                        expected_conclusion=f"bridge_{interface['source']}_{interface['target']}",
                        confidence=0.5
                    )
                    gaps.append(gap)
                    
        except Exception as e:
            self.logger.error(f"Boundary gap detection failed: {e}")
            
        return gaps
        
    def _detect_missing_rules(self) -> List[ReasoningGap]:
        """Detect missing inference rules"""
        gaps = []
        
        try:
            # Analyze inference patterns
            patterns = self._analyze_inference_patterns()
            
            for pattern in patterns:
                if self._is_rule_missing(pattern):
                    gap = ReasoningGap(
                        gap_type="missing_rule",
                        domain=pattern.get("domain", "unknown"),
                        description=f"Missing inference rule for pattern: {pattern['name']}",
                        severity=pattern.get("importance", 0.5),
                        required_premises=pattern.get("premises", []),
                        expected_conclusion=pattern.get("conclusion", ""),
                        suggested_iel=self._generate_iel_suggestion(pattern),
                        confidence=pattern.get("confidence", 0.4)
                    )
                    gaps.append(gap)
                    
        except Exception as e:
            self.logger.error(f"Missing rule detection failed: {e}")
            
        return gaps
        
    def _filter_and_prioritize_gaps(self, gaps: List[ReasoningGap]) -> List[ReasoningGap]:
        """Filter and prioritize gaps by confidence and severity"""
        # Filter by minimum confidence
        filtered = [gap for gap in gaps if gap.confidence >= self.min_gap_confidence]
        
        # Sort by priority (severity * confidence)
        filtered.sort(key=lambda g: g.severity * g.confidence, reverse=True)
        
        # Limit to maximum gaps
        return filtered[:self.max_gaps_per_scan]
        
    def _get_iel_domains(self) -> Dict[str, List[str]]:
        """Get current IEL coverage by domain"""
        try:
            # Placeholder: analyze current IEL structure
            return {
                "modal_logic": ["necessity", "possibility", "contingency"],
                "temporal_logic": ["always", "eventually", "until"],
                "epistemic_logic": ["knows", "believes", "justified"],
                "deontic_logic": ["obligatory", "permitted", "forbidden"]
            }
        except Exception as e:
            self.logger.error(f"IEL domain analysis failed: {e}")
            return {}
            
    def _get_pxl_requirements(self) -> Dict[str, List[str]]:
        """Get PXL requirements by domain"""
        try:
            # Placeholder: analyze PXL structure
            return {
                "modal_logic": ["necessity", "possibility", "contingency", "actuality"],
                "temporal_logic": ["always", "eventually", "until", "since"],
                "epistemic_logic": ["knows", "believes", "justified", "certain"],
                "deontic_logic": ["obligatory", "permitted", "forbidden", "supererogatory"],
                "mereology": ["part_of", "proper_part", "overlap", "disjoint"]
            }
        except Exception as e:
            self.logger.error(f"PXL requirement analysis failed: {e}")
            return {}
            
    def _build_proof_chains(self) -> Dict[str, Dict[str, Any]]:
        """Build proof dependency chains for analysis"""
        # Placeholder implementation
        return {
            "modal_chain_1": {
                "steps": ["premise_1", "modal_rule_1", "intermediate_1", "conclusion_1"],
                "complete": False,
                "missing": ["modal_rule_2"]
            },
            "temporal_chain_1": {
                "steps": ["temporal_premise", "until_rule", "conclusion_temporal"],
                "complete": True,
                "missing": []
            }
        }
        
    def _is_chain_incomplete(self, chain: Dict[str, Any]) -> bool:
        """Check if a proof chain is incomplete"""
        return not chain.get("complete", True) or len(chain.get("missing", [])) > 0
        
    def _find_missing_chain_steps(self, chain: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Find missing steps in a proof chain"""
        missing = []
        for step in chain.get("missing", []):
            missing.append({
                "description": f"Missing step: {step}",
                "premises": [f"premise_for_{step}"],
                "conclusion": f"conclusion_from_{step}",
                "severity": 0.6,
                "confidence": 0.5,
                "domain": "unknown"
            })
        return missing
        
    def _identify_domain_interfaces(self) -> List[Dict[str, str]]:
        """Identify interfaces between reasoning domains"""
        return [
            {"source": "modal_logic", "target": "temporal_logic"},
            {"source": "epistemic_logic", "target": "deontic_logic"},
            {"source": "temporal_logic", "target": "epistemic_logic"}
        ]
        
    def _has_boundary_gap(self, interface: Dict[str, str]) -> bool:
        """Check if there's a gap at domain boundary"""
        # Placeholder: check for missing bridging rules
        return interface["source"] == "modal_logic" and interface["target"] == "temporal_logic"
        
    def _analyze_inference_patterns(self) -> List[Dict[str, Any]]:
        """Analyze common inference patterns"""
        return [
            {
                "name": "modal_temporal_bridge",
                "domain": "modal_temporal",
                "premises": ["modal_premise", "temporal_context"],
                "conclusion": "modal_temporal_conclusion",
                "importance": 0.7,
                "confidence": 0.6
            },
            {
                "name": "epistemic_deontic_connection",
                "domain": "epistemic_deontic",
                "premises": ["epistemic_belief", "deontic_obligation"],
                "conclusion": "justified_obligation",
                "importance": 0.8,
                "confidence": 0.5
            }
        ]
        
    def _is_rule_missing(self, pattern: Dict[str, Any]) -> bool:
        """Check if inference rule is missing for pattern"""
        # Placeholder: check against current IEL registry
        return pattern["confidence"] > 0.4 and pattern["importance"] > 0.5
        
    def _generate_iel_suggestion(self, pattern: Dict[str, Any]) -> str:
        """Generate IEL suggestion for missing rule"""
        return f"IEL_{pattern['name']}: {' ∧ '.join(pattern['premises'])} → {pattern['conclusion']}"
        
    def _compute_coverage_metrics(self, gaps: List[ReasoningGap]) -> Dict[str, float]:
        """Compute coverage metrics from gap analysis"""
        if not gaps:
            return {"overall_coverage": 1.0, "domain_coverage": 1.0, "rule_coverage": 1.0}
            
        total_severity = sum(gap.severity for gap in gaps)
        max_possible_severity = len(gaps) * 1.0
        
        coverage = 1.0 - (total_severity / max_possible_severity) if max_possible_severity > 0 else 1.0
        
        return {
            "overall_coverage": coverage,
            "domain_coverage": max(0.0, 1.0 - len(set(gap.domain for gap in gaps)) * 0.1),
            "rule_coverage": max(0.0, 1.0 - len([g for g in gaps if g.gap_type == "missing_rule"]) * 0.2)
        }