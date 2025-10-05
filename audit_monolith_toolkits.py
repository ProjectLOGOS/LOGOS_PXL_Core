#!/usr/bin/env python3
"""
Monolith Toolkit Audit Script
Identifies and extracts logical toolkit components from LOGOS AGI monolith
for modularization and proof-gate integration.
"""

import ast
import os
import json
import glob
from pathlib import Path
from typing import Dict, List, Any
from dataclasses import dataclass

@dataclass
class ToolkitComponent:
    name: str
    type: str  # 'class', 'function', 'module'
    file_path: str
    line_start: int
    line_end: int
    dependencies: List[str]
    description: str
    complexity_score: int

# Keywords that indicate toolkit functionality
TOOLKIT_KEYWORDS = [
    # Core reasoning
    "predict", "forecast", "analyze", "reason", "infer", "deduce",
    # Planning and agents
    "plan", "agent", "workflow", "orchestrate", "coordinate", "schedule",
    # Learning and adaptation  
    "learn", "train", "adapt", "optimize", "evolve", "improve",
    # Data processing
    "process", "transform", "map", "reduce", "filter", "cluster",
    # Knowledge management
    "knowledge", "semantic", "ontology", "concept", "relation",
    # Causal reasoning
    "causal", "cause", "effect", "intervention", "counterfactual",
    # Modal logic
    "modal", "necessity", "possibility", "belief", "knowledge",
    # Toolkit indicators
    "toolkit", "service", "module", "component", "system"
]

def analyze_file(filepath: str) -> List[ToolkitComponent]:
    """Analyze a Python file and extract toolkit components."""
    components = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        tree = ast.parse(content, filename=filepath)
        
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                name = node.name.lower()
                
                # Check if this is a toolkit component
                is_toolkit = any(keyword in name for keyword in TOOLKIT_KEYWORDS)
                
                # Also check docstring for toolkit indicators
                if not is_toolkit and ast.get_docstring(node):
                    docstring = ast.get_docstring(node).lower()
                    is_toolkit = any(keyword in docstring for keyword in TOOLKIT_KEYWORDS)
                
                if is_toolkit:
                    # Calculate complexity score
                    complexity = calculate_complexity(node)
                    
                    # Extract dependencies (simplified)
                    deps = extract_dependencies(node)
                    
                    # Get description from docstring
                    description = ast.get_docstring(node) or f"{node.__class__.__name__} {node.name}"
                    
                    component = ToolkitComponent(
                        name=node.name,
                        type='class' if isinstance(node, ast.ClassDef) else 'function',
                        file_path=filepath,
                        line_start=node.lineno,
                        line_end=getattr(node, 'end_lineno', node.lineno),
                        dependencies=deps,
                        description=description[:200] + "..." if len(description) > 200 else description,
                        complexity_score=complexity
                    )
                    components.append(component)
    
    except Exception as e:
        print(f"Error analyzing {filepath}: {e}")
    
    return components

def calculate_complexity(node: ast.AST) -> int:
    """Calculate cyclomatic complexity of an AST node."""
    complexity = 1  # Base complexity
    
    for child in ast.walk(node):
        if isinstance(child, (ast.If, ast.While, ast.For, ast.Try, ast.With)):
            complexity += 1
        elif isinstance(child, ast.BoolOp):
            complexity += len(child.values) - 1
    
    return complexity

def extract_dependencies(node: ast.AST) -> List[str]:
    """Extract function/class names that this node depends on."""
    deps = set()
    
    for child in ast.walk(node):
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
            deps.add(child.func.id)
        elif isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
            if child.id[0].isupper():  # Likely a class name
                deps.add(child.id)
    
    return list(deps)[:10]  # Limit to first 10 dependencies

def audit_monolith(base_path: str) -> Dict[str, Any]:
    """Audit the entire LOGOS AGI monolith for toolkit components."""
    
    print("🔍 Auditing LOGOS AGI monolith for toolkit components...")
    
    # Find all Python files in LOGOS_AGI directory
    python_files = glob.glob(os.path.join(base_path, "LOGOS_AGI", "**", "*.py"), recursive=True)
    
    all_components = []
    file_stats = {}
    
    for filepath in python_files:
        print(f"   Analyzing: {os.path.relpath(filepath, base_path)}")
        components = analyze_file(filepath)
        all_components.extend(components)
        
        file_stats[filepath] = {
            'components_found': len(components),
            'file_size': os.path.getsize(filepath),
            'relative_path': os.path.relpath(filepath, base_path)
        }
    
    # Categorize components by type and complexity
    categories = {
        'high_complexity': [c for c in all_components if c.complexity_score > 10],
        'medium_complexity': [c for c in all_components if 5 <= c.complexity_score <= 10],
        'low_complexity': [c for c in all_components if c.complexity_score < 5],
        'classes': [c for c in all_components if c.type == 'class'],
        'functions': [c for c in all_components if c.type == 'function']
    }
    
    # Generate integration recommendations
    integration_plan = generate_integration_plan(all_components)
    
    audit_results = {
        'summary': {
            'total_files_analyzed': len(python_files),
            'total_components_found': len(all_components),
            'high_priority_components': len(categories['high_complexity']),
            'integration_candidates': len([c for c in all_components if c.complexity_score > 5])
        },
        'components': [
            {
                'name': c.name,
                'type': c.type,
                'file': os.path.relpath(c.file_path, base_path),
                'lines': f"{c.line_start}-{c.line_end}",
                'complexity': c.complexity_score,
                'dependencies': c.dependencies,
                'description': c.description
            }
            for c in sorted(all_components, key=lambda x: x.complexity_score, reverse=True)
        ],
        'categories': {k: len(v) for k, v in categories.items()},
        'file_stats': file_stats,
        'integration_plan': integration_plan
    }
    
    return audit_results

def generate_integration_plan(components: List[ToolkitComponent]) -> Dict[str, Any]:
    """Generate integration plan for proof-gate wrapping."""
    
    # Priority 1: High complexity components (need immediate proof wrapping)
    priority_1 = [c for c in components if c.complexity_score > 10]
    
    # Priority 2: Classes with external dependencies
    priority_2 = [c for c in components if c.type == 'class' and len(c.dependencies) > 5]
    
    # Priority 3: Functions that likely perform actions
    action_keywords = ['execute', 'perform', 'run', 'process', 'modify', 'update', 'create', 'delete']
    priority_3 = [c for c in components if any(kw in c.name.lower() for kw in action_keywords)]
    
    return {
        'phase_1_critical': [c.name for c in priority_1[:10]],
        'phase_2_classes': [c.name for c in priority_2[:10]], 
        'phase_3_actions': [c.name for c in priority_3[:10]],
        'integration_strategy': {
            'wrapper_pattern': 'reference_monitor.require_proof_token()',
            'audit_logging': 'Full provenance tracking required',
            'fallback_behavior': 'Fail-closed on authorization failure'
        }
    }

def main():
    """Main audit execution."""
    base_path = os.getcwd()
    
    print("=== LOGOS AGI Monolith Toolkit Audit ===")
    print(f"Base path: {base_path}")
    
    # Run the audit
    results = audit_monolith(base_path)
    
    # Save results
    output_file = "monolith_audit_results.json"
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    # Print summary
    print("\n📊 Audit Summary:")
    print(f"   Files analyzed: {results['summary']['total_files_analyzed']}")
    print(f"   Toolkit components found: {results['summary']['total_components_found']}")
    print(f"   High-priority components: {results['summary']['high_priority_components']}")
    print(f"   Integration candidates: {results['summary']['integration_candidates']}")
    
    print("\n🏷️ Component Categories:")
    for category, count in results['categories'].items():
        print(f"   {category}: {count}")
    
    print(f"\n💾 Detailed results saved to: {output_file}")
    
    print("\n🚀 Next Steps:")
    print("1. Review high-complexity components for proof-gate integration")
    print("2. Wrap action-performing functions with reference_monitor")
    print("3. Add audit logging to all identified toolkit operations")
    print("4. Test each component with DENY patterns to ensure fail-closed behavior")
    
    return results

if __name__ == "__main__":
    main()