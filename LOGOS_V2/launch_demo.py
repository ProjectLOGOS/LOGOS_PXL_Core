#!/usr/bin/env python3
"""
LOGOS Demo GUI Launcher
Simple launcher script for the LOGOS AGI demonstration interface
"""

import os
import sys
import subprocess
import time
from pathlib import Path

def launch_demo_gui():
    """Launch the LOGOS demo GUI with automatic browser opening"""

    # Get the directory of this script
    script_dir = Path(__file__).parent

    print("🤖 Starting LOGOS AGI Demo Interface...")
    print("=====================================")
    print()

    # Change to the project directory
    os.chdir(script_dir)

    # Check if we're in a codespace environment
    is_codespace = os.environ.get('CODESPACES', '').lower() == 'true' or 'github.dev' in os.environ.get('GITHUB_SERVER_URL', '')

    try:
        # Launch the demo GUI
        print("🚀 Launching demo interface...")
        if is_codespace:
            print("📱 Access the interface at: http://localhost:7860")
            print("💡 In codespace environment - open URL manually")
        else:
            print("📱 Browser will open automatically at: http://localhost:7860")
        print("💡 Close this terminal to stop the demo")
        print()

        # Run the demo GUI
        subprocess.run([
            sys.executable, "demo_gui.py"
        ], check=True)

    except KeyboardInterrupt:
        print("\n👋 Demo interface stopped by user")
    except subprocess.CalledProcessError as e:
        print(f"❌ Error launching demo: {e}")
        return 1
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        return 1

    return 0

if __name__ == "__main__":
    exit(launch_demo_gui())