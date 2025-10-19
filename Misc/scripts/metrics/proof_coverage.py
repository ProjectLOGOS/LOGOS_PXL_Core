#!/usr/bin/env python3
"""
Proof Coverage Analysis for LOGOS_PXL_Core
Scans all .v files for 'Admitted' statements and generates verification coverage reports.

Usage:
    python proof_coverage.py [--output-format json|text] [--detailed]
"""

import os
import re
import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional
import argparse
from datetime import datetime

@dataclass
class AdmittedProof:
    """Represents an unfinished proof marked as 'Admitted'"""
    file_path: str
    line_number: int
    theorem_name: Optional[str]
    context: str  # Surrounding lines for context
    priority: str  # high, medium, low based on module location
    module_category: str  # experimental, core, infra, etc.

@dataclass
class ModuleStats:
    """Statistics for a specific module or directory"""
    module_path: str
    total_v_files: int
    files_with_admitted: int
    total_admitted_count: int
    verification_ratio: float  # (total_files - files_with_admitted) / total_files
    priority_level: str

@dataclass
class CoverageReport:
    """Complete proof coverage analysis report"""
    timestamp: str
    repository_version: str
    total_v_files: int
    total_admitted_proofs: int
    overall_verification_ratio: float
    modules: List[ModuleStats]
    admitted_proofs: List[AdmittedProof]
    recommendations: List[str]

class ProofCoverageAnalyzer:
    """Analyzes Coq proof coverage across LOGOS_PXL_Core repository"""

    def __init__(self, repo_root: str):
        self.repo_root = Path(repo_root)
        self.admitted_pattern = re.compile(r'\bAdmitted\b', re.IGNORECASE)
        self.theorem_pattern = re.compile(r'(Theorem|Lemma|Definition|Fixpoint)\s+(\w+)', re.IGNORECASE)

        # Priority mapping based on module location
        self.priority_map = {
            'experimental': 'low',
            '_experimental': 'low',
            'core': 'high',
            'substrate': 'high',
            'theorems': 'medium',
            'infra': 'medium',
            'examples': 'low',
            'modal': 'high',
            'systems': 'medium'
        }

    def analyze_file(self, file_path: Path) -> List[AdmittedProof]:
        """Analyze a single .v file for Admitted statements"""
        admitted_proofs = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
        except (UnicodeDecodeError, FileNotFoundError):
            return admitted_proofs

        for i, line in enumerate(lines, 1):
            if self.admitted_pattern.search(line):
                # Extract context (3 lines before and after)
                start_idx = max(0, i - 4)
                end_idx = min(len(lines), i + 3)
                context_lines = lines[start_idx:end_idx]
                context = ''.join(context_lines).strip()

                # Try to find theorem name by looking backwards
                theorem_name = self._find_theorem_name(lines, i - 1)

                # Determine priority based on file path
                priority = self._determine_priority(file_path)
                module_category = self._determine_module_category(file_path)

                admitted_proof = AdmittedProof(
                    file_path=str(file_path.relative_to(self.repo_root)),
                    line_number=i,
                    theorem_name=theorem_name,
                    context=context,
                    priority=priority,
                    module_category=module_category
                )
                admitted_proofs.append(admitted_proof)

        return admitted_proofs

    def _find_theorem_name(self, lines: List[str], start_line: int) -> Optional[str]:
        """Find the theorem/lemma name by searching backwards from Admitted line"""
        for i in range(start_line, max(0, start_line - 20), -1):
            match = self.theorem_pattern.search(lines[i])
            if match:
                return match.group(2)
        return None

    def _determine_priority(self, file_path: Path) -> str:
        """Determine priority based on file path components"""
        path_parts = file_path.parts
        for part in path_parts:
            if part.lower() in self.priority_map:
                return self.priority_map[part.lower()]
        return 'medium'  # default

    def _determine_module_category(self, file_path: Path) -> str:
        """Categorize module based on directory structure"""
        path_str = str(file_path)
        if '_experimental' in path_str or 'experimental' in path_str:
            return 'experimental'
        elif 'core' in path_str.lower() or 'substrate' in path_str:
            return 'core'
        elif 'infra' in path_str:
            return 'infrastructure'
        elif 'theorems' in path_str:
            return 'theorems'
        elif 'examples' in path_str.lower():
            return 'examples'
        else:
            return 'other'

    def analyze_module(self, module_path: Path) -> ModuleStats:
        """Analyze a specific module directory"""
        v_files = list(module_path.glob('**/*.v'))
        total_v_files = len(v_files)

        files_with_admitted = 0
        total_admitted_count = 0

        for v_file in v_files:
            admitted_proofs = self.analyze_file(v_file)
            if admitted_proofs:
                files_with_admitted += 1
                total_admitted_count += len(admitted_proofs)

        verification_ratio = (total_v_files - files_with_admitted) / max(1, total_v_files)

        # Determine priority level for the module
        priority_level = self._determine_priority(module_path)

        return ModuleStats(
            module_path=str(module_path.relative_to(self.repo_root)),
            total_v_files=total_v_files,
            files_with_admitted=files_with_admitted,
            total_admitted_count=total_admitted_count,
            verification_ratio=verification_ratio,
            priority_level=priority_level
        )

    def generate_recommendations(self, admitted_proofs: List[AdmittedProof]) -> List[str]:
        """Generate prioritized recommendations for proof completion"""
        recommendations = []

        # Group by priority and module
        high_priority = [p for p in admitted_proofs if p.priority == 'high']
        medium_priority = [p for p in admitted_proofs if p.priority == 'medium']
        low_priority = [p for p in admitted_proofs if p.priority == 'low']

        if high_priority:
            recommendations.append(f"🔴 HIGH PRIORITY: Complete {len(high_priority)} core proofs first")
            for proof in high_priority[:3]:  # Show top 3
                recommendations.append(f"   • {proof.file_path}:{proof.line_number} - {proof.theorem_name or 'unnamed'}")

        if medium_priority:
            recommendations.append(f"🟡 MEDIUM PRIORITY: {len(medium_priority)} infrastructure proofs")

        if low_priority:
            recommendations.append(f"🟢 LOW PRIORITY: {len(low_priority)} experimental/example proofs")

        # Experimental modules can be quarantined
        experimental_count = len([p for p in admitted_proofs if p.module_category == 'experimental'])
        if experimental_count > 0:
            recommendations.append(f"💡 Consider quarantining {experimental_count} experimental proofs to _experimental/ directories")

        return recommendations

    def scan_repository(self) -> CoverageReport:
        """Perform complete repository scan and generate coverage report"""
        print("🔍 Scanning LOGOS_PXL_Core for proof coverage...")

        # Find all .v files
        pxl_iel_path = self.repo_root / "PXL_IEL_overlay_system"
        if not pxl_iel_path.exists():
            # Fallback to current directory
            pxl_iel_path = self.repo_root

        all_v_files = list(pxl_iel_path.glob('**/*.v'))
        total_v_files = len(all_v_files)

        print(f"📁 Found {total_v_files} .v files")

        # Analyze all files for admitted proofs
        all_admitted_proofs = []
        for v_file in all_v_files:
            admitted_proofs = self.analyze_file(v_file)
            all_admitted_proofs.extend(admitted_proofs)

        total_admitted = len(all_admitted_proofs)
        files_with_admitted = len(set(proof.file_path for proof in all_admitted_proofs))
        overall_verification_ratio = (total_v_files - files_with_admitted) / max(1, total_v_files)

        print(f"❌ Found {total_admitted} admitted proofs in {files_with_admitted} files")
        print(f"✅ Verification ratio: {overall_verification_ratio:.2%}")

        # Analyze key modules
        key_modules = [
            pxl_iel_path / "modules" / "infra",
            pxl_iel_path / "modules" / "IEL",
            pxl_iel_path / "coq",
        ]

        module_stats = []
        for module_path in key_modules:
            if module_path.exists():
                stats = self.analyze_module(module_path)
                module_stats.append(stats)

        # Generate recommendations
        recommendations = self.generate_recommendations(all_admitted_proofs)

        report = CoverageReport(
            timestamp=datetime.now().isoformat(),
            repository_version="v0.4.2-recovery",
            total_v_files=total_v_files,
            total_admitted_proofs=total_admitted,
            overall_verification_ratio=overall_verification_ratio,
            modules=module_stats,
            admitted_proofs=all_admitted_proofs,
            recommendations=recommendations
        )

        return report

    def save_report(self, report: CoverageReport, output_path: str, format: str = 'json'):
        """Save the coverage report to file"""
        if format == 'json':
            with open(output_path, 'w') as f:
                json.dump(asdict(report), f, indent=2)
            print(f"📊 Report saved to {output_path}")
        elif format == 'text':
            self._save_text_report(report, output_path)

    def _save_text_report(self, report: CoverageReport, output_path: str):
        """Save human-readable text report"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("# LOGOS_PXL_Core Proof Coverage Report\\n")
            f.write(f"Generated: {report.timestamp}\\n")
            f.write(f"Version: {report.repository_version}\\n\\n")

            f.write("## Summary\\n")
            f.write(f"- Total .v files: {report.total_v_files}\\n")
            f.write(f"- Admitted proofs: {report.total_admitted_proofs}\\n")
            f.write(f"- Verification ratio: {report.overall_verification_ratio:.2%}\\n\\n")

            f.write("## Recommendations\\n")
            for rec in report.recommendations:
                f.write(f"{rec}\\n")
            f.write("\\n")

            f.write("## Module Analysis\\n")
            for module in report.modules:
                f.write(f"### {module.module_path}\\n")
                f.write(f"- Files: {module.total_v_files}\\n")
                f.write(f"- With admitted: {module.files_with_admitted}\\n")
                f.write(f"- Total admitted: {module.total_admitted_count}\\n")
                f.write(f"- Verification: {module.verification_ratio:.2%}\\n\\n")

        print(f"📄 Text report saved to {output_path}")

def main():
    parser = argparse.ArgumentParser(description='LOGOS_PXL_Core Proof Coverage Analysis')
    parser.add_argument('--repo-root', default='.', help='Repository root directory')
    parser.add_argument('--output-format', choices=['json', 'text'], default='json', help='Output format')
    parser.add_argument('--output-file', help='Output file path')
    parser.add_argument('--detailed', action='store_true', help='Include detailed proof listings')

    args = parser.parse_args()

    # Determine output file
    if not args.output_file:
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        extension = 'json' if args.output_format == 'json' else 'md'
        args.output_file = f'proof_coverage_{timestamp}.{extension}'

    # Run analysis
    analyzer = ProofCoverageAnalyzer(args.repo_root)
    report = analyzer.scan_repository()

    # Print summary
    print("\\n" + "="*60)
    print("📊 PROOF COVERAGE ANALYSIS COMPLETE")
    print("="*60)
    print(f"📁 Total .v files: {report.total_v_files}")
    print(f"❌ Admitted proofs: {report.total_admitted_proofs}")
    print(f"✅ Verification ratio: {report.overall_verification_ratio:.2%}")
    print(f"🎯 Target for v0.5: 100% (zero admitted)")
    print("="*60)

    print("\\n🎯 RECOMMENDATIONS:")
    for rec in report.recommendations:
        print(f"  {rec}")

    # Save report
    analyzer.save_report(report, args.output_file, args.output_format)

    # Exit code based on verification ratio
    if report.overall_verification_ratio < 0.8:
        print("\\n⚠️  LOW VERIFICATION RATIO - Significant work needed for v0.5")
        return 1
    elif report.overall_verification_ratio < 0.95:
        print("\\n🔧 MODERATE VERIFICATION RATIO - Targeted proof completion needed")
        return 0
    else:
        print("\\n✅ HIGH VERIFICATION RATIO - On track for v0.5 release")
        return 0

if __name__ == '__main__':
    exit(main())
