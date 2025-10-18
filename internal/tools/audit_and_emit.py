#!/usr/bin/env python3
import argparse
import json
import os
import sys


def load_json(path):
    with open(path) as f:
        return json.load(f)

def find_minimal_cover(needs, property_caps):
    """Greedy minimal set cover"""
    uncovered = set(needs)
    selected = []
    properties = list(property_caps.keys())
    while uncovered:
        # Find property that covers most uncovered caps
        best_prop = max(properties, key=lambda p: len(set(property_caps[p]) & uncovered))
        covered = set(property_caps[best_prop]) & uncovered
        if not covered:
            return None  # Cannot cover
        selected.append(best_prop)
        uncovered -= covered
        properties.remove(best_prop)  # Don't select again
    return selected

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()

    if not (args.dry_run or args.write):
        print("Use --dry-run or --write")
        sys.exit(1)

    # Load configs
    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    config_dir = os.path.join(base_dir, 'config')
    pillar_obligations = load_json(os.path.join(base_dir, 'configs', 'pillar_obligations.json'))
    property_capabilities = load_json(os.path.join(base_dir, 'configs', 'property_capabilities.json'))
    router_rules = load_json(os.path.join(base_dir, 'configs', 'router_rules.json'))
    ontological_properties = load_json(os.path.join(config_dir, 'ontological_properties.json'))

    # Coverage report
    print("Coverage Report")
    print("=" * 50)
    all_covered = True
    pillar_selections = {}
    for pillar, data in router_rules.items():
        needs = data['needs']
        selected = find_minimal_cover(needs, property_capabilities)
        if selected is None:
            print(f"{pillar}: Cannot cover needs {needs}")
            all_covered = False
        else:
            pillar_selections[pillar] = selected
            print(f"{pillar}: {', '.join(selected)}")

    if not all_covered:
        print("Coverage incomplete")
        sys.exit(1)

    if args.dry_run:
        return

    if args.write:
        # Generate Spec.v files
        modules_dir = os.path.join(base_dir, 'modules', 'IEL')
        for pillar, properties in pillar_selections.items():
            for prop in properties:
                sub_dir = os.path.join(modules_dir, pillar, 'subdomains', prop)
                os.makedirs(sub_dir, exist_ok=True)
                spec_file = os.path.join(sub_dir, 'Spec.v')
                content = f"""From PXLs.Core Require Import PXL_Kernel.
From PXLs.Theo Require Import Props.
Module {prop}Sub.
  Import TheoProps.
  Definition V := {prop}.
  Theorem conservative : forall φ, V φ -> φ. (* prove from PXL lemmas chosen for {prop} *)
Admitted. (* must be proved before CI passes; no Admitted in final branch *)
End {prop}Sub.
"""
                with open(spec_file, 'w', encoding='utf-8') as f:
                    f.write(content)
        print("Generated subdomain Spec.v files")

if __name__ == '__main__':
    main()
