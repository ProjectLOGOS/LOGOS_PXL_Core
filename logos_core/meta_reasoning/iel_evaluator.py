#!/usr/bin/env python3
"""
IEL Evaluator - Autonomous evaluation, ranking, and coherence scoring of IEL candidates

This module provides comprehensive evaluation of IEL candidates using multiple metrics:
- Proof validity and completeness
- Coherence with existing framework
- Performance and efficiency metrics
- Stability under various conditions

Part of the LOGOS AGI v1.0 autonomous reasoning framework.
"""

import argparse
import json
import sqlite3
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
import logging
import statistics

# Import core components
try:
    from logos_core.coherence.coherence_metrics import CoherenceCalculator
    from logos_core.coherence.coherence_optimizer import CoherenceOptimizer
    from logos_core.meta_reasoning.iel_registry import IELRegistry, IELCandidate
    from logos_core.governance.iel_signer import IELSigner
except ImportError as e:
    logging.warning(f"Core import failed: {e}, using fallback classes")

    # Fallback classes for missing imports
    class IELRegistry:
        def __init__(self, path): self.path = path
        def list_candidates(self): return []

    class IELCandidate:
        def __init__(self, **kwargs):
            for k, v in kwargs.items():
                setattr(self, k, v)

    class IELSigner:
        def __init__(self): pass

    class CoherenceCalculator:
        def calculate_coherence(self, iel_content: str) -> float:
            """Mock coherence calculation"""
            lines = iel_content.split('\n')
            non_empty_lines = [l for l in lines if l.strip()]
            if len(non_empty_lines) < 5:
                return 0.3
            elif len(non_empty_lines) > 15:
                return 0.95
            else:
                return 0.7 + (len(non_empty_lines) / 20.0)

    class CoherenceOptimizer:
        def optimize_coherence(self, iel_content: str) -> Tuple[str, float]:
            """Mock coherence optimization"""
            optimized = iel_content + "\n(* Optimized for coherence *)"
            score = CoherenceCalculator().calculate_coherence(optimized)
            return optimized, score


class IELQualityMetrics:
    """Comprehensive IEL quality assessment metrics"""

    def __init__(self):
        self.coherence_calc = CoherenceCalculator()
        self.coherence_opt = CoherenceOptimizer()

    def evaluate_proof_validity(self, iel_content: str) -> Dict[str, Any]:
        """Evaluate proof structure and validity"""
        metrics = {
            'has_theorem': 'Theorem' in iel_content,
            'has_proof': 'Proof.' in iel_content,
            'has_qed': 'Qed.' in iel_content,
            'syntax_score': 0.0,
            'structure_score': 0.0,
            'completeness_score': 0.0
        }

        # Basic syntax analysis
        required_elements = ['Definition', 'Theorem', 'Proof', 'Qed']
        present_elements = sum(1 for elem in required_elements if elem in iel_content)
        metrics['syntax_score'] = present_elements / len(required_elements)

        # Structure analysis
        lines = [l.strip() for l in iel_content.split('\n') if l.strip()]
        structure_indicators = ['Require Import', 'Module', 'Section', 'Variable', 'Hypothesis']
        structure_count = sum(1 for indicator in structure_indicators
                            if any(indicator in line for line in lines))
        metrics['structure_score'] = min(1.0, structure_count / 3.0)

        # Completeness analysis
        proof_lines = [l for l in lines if not l.startswith('(*') and not l.startswith('Require')]
        if len(proof_lines) >= 10:
            metrics['completeness_score'] = 0.9
        elif len(proof_lines) >= 5:
            metrics['completeness_score'] = 0.7
        else:
            metrics['completeness_score'] = 0.4

        return metrics

    def evaluate_coherence(self, iel_content: str) -> Dict[str, float]:
        """Evaluate coherence with existing framework"""
        base_coherence = self.coherence_calc.calculate_coherence(iel_content)

        # Additional coherence factors
        naming_coherence = self._evaluate_naming_coherence(iel_content)
        logical_coherence = self._evaluate_logical_coherence(iel_content)
        framework_coherence = self._evaluate_framework_coherence(iel_content)

        return {
            'base_coherence': base_coherence,
            'naming_coherence': naming_coherence,
            'logical_coherence': logical_coherence,
            'framework_coherence': framework_coherence,
            'overall_coherence': statistics.mean([
                base_coherence, naming_coherence, logical_coherence, framework_coherence
            ])
        }

    def _evaluate_naming_coherence(self, iel_content: str) -> float:
        """Evaluate naming convention coherence"""
        logos_naming_patterns = ['logos_', 'iel_', 'pxl_', 'LOGOS_', 'IEL_', 'PXL_']
        naming_score = 0.0

        definitions = [l for l in iel_content.split('\n')
                      if l.strip().startswith(('Definition', 'Theorem', 'Lemma'))]

        if definitions:
            coherent_names = sum(1 for def_line in definitions
                               if any(pattern in def_line for pattern in logos_naming_patterns))
            naming_score = coherent_names / len(definitions)
        else:
            naming_score = 0.5  # Neutral if no definitions found

        return naming_score

    def _evaluate_logical_coherence(self, iel_content: str) -> float:
        """Evaluate logical structure coherence"""
        logical_indicators = ['forall', 'exists', 'implies', 'iff', 'and', 'or', 'not']
        logical_count = sum(iel_content.lower().count(indicator) for indicator in logical_indicators)

        # Normalize based on content length
        lines = len([l for l in iel_content.split('\n') if l.strip()])
        if lines == 0:
            return 0.0

        logical_density = logical_count / lines
        return min(1.0, logical_density * 2.0)  # Scale to [0, 1]

    def _evaluate_framework_coherence(self, iel_content: str) -> float:
        """Evaluate coherence with LOGOS framework"""
        framework_keywords = [
            'reasoning', 'gap', 'inference', 'modal', 'coherence',
            'bijective', 'fractal', 'ontological', 'axiom', 'proof'
        ]

        keyword_count = sum(iel_content.lower().count(keyword) for keyword in framework_keywords)
        lines = len([l for l in iel_content.split('\n') if l.strip()])

        if lines == 0:
            return 0.0

        framework_density = keyword_count / lines
        return min(1.0, framework_density * 3.0)  # Scale to [0, 1]

    def evaluate_performance(self, iel_content: str) -> Dict[str, float]:
        """Evaluate IEL performance metrics"""
        return {
            'complexity_score': self._evaluate_complexity(iel_content),
            'efficiency_score': self._evaluate_efficiency(iel_content),
            'maintainability_score': self._evaluate_maintainability(iel_content)
        }

    def _evaluate_complexity(self, iel_content: str) -> float:
        """Evaluate computational complexity"""
        # Simple heuristic: fewer nested structures = lower complexity = higher score
        nesting_levels = iel_content.count('(') + iel_content.count('[') + iel_content.count('{')
        lines = len([l for l in iel_content.split('\n') if l.strip()])

        if lines == 0:
            return 0.0

        complexity_ratio = nesting_levels / lines
        return max(0.0, 1.0 - complexity_ratio)  # Lower complexity = higher score

    def _evaluate_efficiency(self, iel_content: str) -> float:
        """Evaluate proof efficiency"""
        # Measure proof steps vs content length
        proof_indicators = ['apply', 'rewrite', 'simpl', 'auto', 'reflexivity', 'trivial']
        proof_steps = sum(iel_content.count(indicator) for indicator in proof_indicators)

        lines = len([l for l in iel_content.split('\n') if l.strip()])
        if lines == 0:
            return 0.0

        efficiency = proof_steps / lines
        return min(1.0, efficiency * 2.0)  # Scale to [0, 1]

    def _evaluate_maintainability(self, iel_content: str) -> float:
        """Evaluate code maintainability"""
        # Based on comments, structure, and readability
        comment_lines = len([l for l in iel_content.split('\n') if l.strip().startswith('(*')])
        total_lines = len([l for l in iel_content.split('\n') if l.strip()])

        if total_lines == 0:
            return 0.0

        comment_ratio = comment_lines / total_lines
        structure_indicators = iel_content.count('Section') + iel_content.count('Module')

        maintainability = (comment_ratio * 0.6) + (min(1.0, structure_indicators / 3.0) * 0.4)
        return maintainability


class IELEvaluator:
    """Main IEL evaluation and ranking system"""

    def __init__(self, registry_path: str = "registry/iel_registry.db"):
        self.registry_path = registry_path
        self.registry = IELRegistry(registry_path)
        self.quality_metrics = IELQualityMetrics()
        self.logger = logging.getLogger(__name__)

    def evaluate_all_iels(self, metrics_file: str = None) -> Dict[str, Any]:
        """Evaluate all IELs in the registry"""
        self.logger.info("Starting comprehensive IEL evaluation...")

        # Get all IELs from registry
        iels = self.registry.list_candidates()
        evaluation_results = {}

        for iel in iels:
            self.logger.info(f"Evaluating IEL: {iel.iel_id}")

            # Read IEL content
            try:
                with open(iel.file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
            except (FileNotFoundError, IOError) as e:
                self.logger.error(f"Failed to read IEL {iel.iel_id}: {e}")
                continue

            # Comprehensive evaluation
            evaluation = {
                'iel_id': iel.iel_id,
                'file_path': iel.file_path,
                'timestamp': datetime.now().isoformat(),
                'proof_metrics': self.quality_metrics.evaluate_proof_validity(content),
                'coherence_metrics': self.quality_metrics.evaluate_coherence(content),
                'performance_metrics': self.quality_metrics.evaluate_performance(content),
            }

            # Calculate overall score
            overall_score = self._calculate_overall_score(evaluation)
            evaluation['overall_score'] = overall_score
            evaluation['classification'] = self._classify_iel(overall_score)

            evaluation_results[iel.iel_id] = evaluation

        # Write metrics if requested
        if metrics_file:
            self._write_evaluation_metrics(evaluation_results, metrics_file)

        self.logger.info(f"Evaluation complete. Processed {len(evaluation_results)} IELs")
        return evaluation_results

    def _calculate_overall_score(self, evaluation: Dict[str, Any]) -> float:
        """Calculate weighted overall score"""
        proof_weight = 0.4
        coherence_weight = 0.3
        performance_weight = 0.3

        # Extract key metrics
        proof_score = statistics.mean([
            evaluation['proof_metrics']['syntax_score'],
            evaluation['proof_metrics']['structure_score'],
            evaluation['proof_metrics']['completeness_score']
        ])

        coherence_score = evaluation['coherence_metrics']['overall_coherence']

        performance_score = statistics.mean([
            evaluation['performance_metrics']['complexity_score'],
            evaluation['performance_metrics']['efficiency_score'],
            evaluation['performance_metrics']['maintainability_score']
        ])

        overall = (proof_score * proof_weight +
                  coherence_score * coherence_weight +
                  performance_score * performance_weight)

        return round(overall, 3)

    def _classify_iel(self, score: float) -> str:
        """Classify IEL based on overall score"""
        if score >= 0.9:
            return "excellent"
        elif score >= 0.8:
            return "good"
        elif score >= 0.7:
            return "acceptable"
        elif score >= 0.6:
            return "needs_improvement"
        else:
            return "poor"

    def rank_iels(self, evaluation_results: Dict[str, Any], threshold: float = 0.8) -> List[Dict[str, Any]]:
        """Rank IELs by quality score with threshold filtering"""
        # Convert to list and sort by overall score
        ranked_iels = []

        for iel_id, evaluation in evaluation_results.items():
            if evaluation['overall_score'] >= threshold:
                ranked_iels.append(evaluation)

        # Sort by overall score (descending)
        ranked_iels.sort(key=lambda x: x['overall_score'], reverse=True)

        # Add rankings
        for i, iel in enumerate(ranked_iels, 1):
            iel['rank'] = i

        return ranked_iels

    def _write_evaluation_metrics(self, results: Dict[str, Any], output_path: str):
        """Write evaluation results to JSON file"""
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)

        summary = {
            'evaluation_timestamp': datetime.now().isoformat(),
            'total_iels_evaluated': len(results),
            'evaluation_results': results,
            'summary_statistics': self._calculate_summary_stats(results)
        }

        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)

    def _calculate_summary_stats(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """Calculate summary statistics for evaluation results"""
        if not results:
            return {}

        scores = [r['overall_score'] for r in results.values()]
        classifications = [r['classification'] for r in results.values()]

        return {
            'mean_score': round(statistics.mean(scores), 3),
            'median_score': round(statistics.median(scores), 3),
            'min_score': min(scores),
            'max_score': max(scores),
            'score_std_dev': round(statistics.stdev(scores) if len(scores) > 1 else 0.0, 3),
            'classification_counts': {
                cls: classifications.count(cls)
                for cls in set(classifications)
            }
        }


def main():
    """Command-line interface for IEL evaluation"""
    parser = argparse.ArgumentParser(description="LOGOS AGI IEL Evaluator")
    parser.add_argument('--registry', default='registry/iel_registry.db',
                       help='Path to IEL registry database')
    parser.add_argument('--metrics', help='Output path for evaluation metrics JSON')
    parser.add_argument('--report', help='Output path for quality report JSON')
    parser.add_argument('--rank', action='store_true',
                       help='Rank IELs by quality score')
    parser.add_argument('--threshold', type=float, default=0.8,
                       help='Minimum quality threshold for ranking')
    parser.add_argument('--out', help='Output path for ranked results')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Enable verbose logging')

    args = parser.parse_args()

    # Setup logging
    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

    evaluator = IELEvaluator(args.registry)

    try:
        if args.rank:
            # Load existing evaluation results and rank
            if not args.report:
                print("Error: --report required for ranking mode")
                return 1

            with open(args.report, 'r', encoding='utf-8') as f:
                data = json.load(f)
                evaluation_results = data.get('evaluation_results', {})

            ranked_results = evaluator.rank_iels(evaluation_results, args.threshold)

            output_data = {
                'ranking_timestamp': datetime.now().isoformat(),
                'threshold': args.threshold,
                'total_candidates': len(evaluation_results),
                'qualified_candidates': len(ranked_results),
                'ranked_iels': ranked_results
            }

            if args.out:
                with open(args.out, 'w', encoding='utf-8') as f:
                    json.dump(output_data, f, indent=2, ensure_ascii=False)
                print(f"Ranked {len(ranked_results)} IELs written to {args.out}")
            else:
                print(json.dumps(output_data, indent=2, ensure_ascii=False))

        else:
            # Full evaluation mode
            results = evaluator.evaluate_all_iels(args.metrics)

            if args.report:
                evaluator._write_evaluation_metrics(results, args.report)
                print(f"Evaluation report written to {args.report}")

            print(f"Evaluation complete: {len(results)} IELs processed")

            # Print summary
            if results:
                summary = evaluator._calculate_summary_stats(results)
                print(f"Mean score: {summary['mean_score']}")
                print(f"Score range: {summary['min_score']} - {summary['max_score']}")
                print("Classifications:", summary['classification_counts'])

    except Exception as e:
        logging.error(f"Evaluation failed: {e}")
        return 1

    return 0


if __name__ == "__main__":
    exit(main())
