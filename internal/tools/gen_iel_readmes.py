#!/usr/bin/env python3
"""
Generate README.md files for each IEL praxis directory.
Lists all files in each directory with their relative paths.
"""

import os
import pathlib
from typing import List, Dict


def get_all_files(directory: pathlib.Path) -> List[pathlib.Path]:
    """Get all files in directory recursively, excluding hidden files and directories."""
    files = []
    for root, dirs, filenames in os.walk(directory):
        # Skip hidden directories
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != '_experimental']

        for filename in filenames:
            if not filename.startswith('.'):  # Skip hidden files
                files.append(pathlib.Path(root) / filename)

    return sorted(files)


def generate_readme(praxis_name: str, praxis_path: pathlib.Path, base_path: pathlib.Path) -> str:
    """Generate README content for a praxis directory."""
    files = get_all_files(praxis_path)

    content = f"# {praxis_name}\n\n"
    content += f"## Overview\n\n"
    content += f"This directory contains the {praxis_name} implementation within the IEL (Integrated Experiential Logic) framework.\n\n"

    if files:
        content += "## Files\n\n"
        for file_path in files:
            relative_path = file_path.relative_to(base_path)
            content += f"- `{relative_path}`\n"
        content += "\n"
    else:
        content += "No files found in this directory.\n\n"

    content += "## Development\n\n"
    content += "This praxis is part of the LOGOS PXL Core system. See the main README for development setup.\n"

    return content


def main():
    """Main function to generate READMEs for all IEL praxis directories."""
    base_path = pathlib.Path(__file__).parent.parent  # Go up one level from tools/
    iel_path = base_path / "modules" / "IEL"

    if not iel_path.exists():
        print(f"IEL directory not found: {iel_path}")
        return

    # Directories to process (excluding _experimental)
    praxis_dirs = [
        "AnthroPraxis",
        "Axiopraxis",
        "CosmoPraxis",
        "ErgoPraxis",
        "GnosiPraxis",
        "TeloPraxis",
        "ThemiPraxis",
        "infra/ChronoPraxis",
        "infra/ModalPraxis",
        "infra/TopoPraxis",
        "infra/TropoPraxis",
        "pillars",
        "source"
    ]

    generated_count = 0

    for praxis_dir in praxis_dirs:
        praxis_path = iel_path / praxis_dir
        if praxis_path.exists() and praxis_path.is_dir():
            readme_path = praxis_path / "README.md"
            readme_content = generate_readme(praxis_dir.replace('/', '_'), praxis_path, base_path)

            with open(readme_path, 'w', encoding='utf-8') as f:
                f.write(readme_content)

            print(f"Generated README for {praxis_dir}")
            generated_count += 1
        else:
            print(f"Directory not found: {praxis_path}")

    print(f"\nGenerated {generated_count} README files.")


if __name__ == "__main__":
    main()