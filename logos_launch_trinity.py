#!/usr/bin/env python3
"""
LOGOS Trinity Knot GUI - Launch Script

Initializes the LOGOS system and starts the Trinity Knot web interface.

Usage:
    python logos_launch_trinity.py [--port PORT]

Default port: 5000
Access: http://localhost:5000
"""

import sys
import os
import argparse
import webbrowser
import time
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))


def check_dependencies():
    """Verify required dependencies are available."""
    print("Checking dependencies...")

    required = {
        'fastapi': 'FastAPI',
        'uvicorn': 'Uvicorn',
        'websockets': 'WebSockets',
        'networkx': 'NetworkX'
    }

    optional = {
        'speech_recognition': 'SpeechRecognition (voice input)',
        'pyaudio': 'PyAudio (voice input)'
    }

    missing_required = []
    missing_optional = []

    for module, name in required.items():
        try:
            __import__(module)
            print(f"  ✓ {name}")
        except ImportError:
            print(f"  ✗ {name}")
            missing_required.append(name)

    for module, name in optional.items():
        try:
            __import__(module)
            print(f"  ✓ {name}")
        except ImportError:
            print(f"  ⚠ {name} (optional, voice input disabled)")
            missing_optional.append(name)

    if missing_required:
        print(f"\nERROR: Missing required dependencies: {', '.join(missing_required)}")
        print("Install with: pip install fastapi uvicorn websockets networkx")
        return False

    if missing_optional:
        print(f"\nNote: Optional features disabled due to missing: {', '.join(missing_optional)}")
        print("Install with: pip install SpeechRecognition pyaudio")

    return True


def initialize_extensions():
    """Initialize LOGOS extensions."""
    print("\nInitializing LOGOS extensions...")

    try:
        from boot.extensions_loader import ExtensionsManager

        extensions = ExtensionsManager()
        extensions.initialize_all()

        status = extensions.get_status()
        print(f"  ✓ Extensions loaded: {status['loaded']}/{status['total']}")

        if status['loaded'] < status['total']:
            print(f"  ⚠ Some extensions failed to load (see boot/extensions_loader.py)")

        return True
    except Exception as e:
        print(f"  ⚠ Extensions initialization warning: {e}")
        print("  Continuing with core functionality...")
        return True


def launch_server(port: int, open_browser: bool = True):
    """Launch the FastAPI server."""
    print(f"\nStarting Trinity Knot GUI on port {port}...")
    print(f"Access URL: http://localhost:{port}")
    print("\nTrinity Knot Features:")
    print("  • Real-time WebSocket communication")
    print("  • 4 animated states (stasis, listening, processing, speaking)")
    print("  • Text query interface")
    print("  • Voice input (if available)")
    print("  • File upload (10MB max)")
    print("  • NetworkX graph visualization")
    print("  • Session audit logging")
    print("\nPress Ctrl+C to stop the server.\n")

    # Wait a moment for server to start
    if open_browser:
        import threading
        def open_browser_delayed():
            time.sleep(2)
            webbrowser.open(f"http://localhost:{port}")

        threading.Thread(target=open_browser_delayed, daemon=True).start()

    # Launch uvicorn
    import uvicorn
    uvicorn.run(
        "logos_trinity_gui:app",
        host="0.0.0.0",
        port=port,
        reload=True,
        log_level="info"
    )


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Launch LOGOS Trinity Knot GUI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python logos_launch_trinity.py              # Default port 5000
  python logos_launch_trinity.py --port 8080  # Custom port
  python logos_launch_trinity.py --no-browser # Don't open browser

For more information, see PHASE_2_PROGRESS_REPORT.md
        """
    )
    parser.add_argument(
        '--port',
        type=int,
        default=5000,
        help='Port to run the server on (default: 5000)'
    )
    parser.add_argument(
        '--no-browser',
        action='store_true',
        help='Do not automatically open browser'
    )

    args = parser.parse_args()

    print("=" * 60)
    print(" LOGOS Trinity Knot GUI - Launch Script")
    print("=" * 60)

    # Step 1: Check dependencies
    if not check_dependencies():
        sys.exit(1)

    # Step 2: Initialize extensions
    if not initialize_extensions():
        print("\nWarning: Extensions initialization had issues.")
        response = input("Continue anyway? (y/n): ")
        if response.lower() != 'y':
            sys.exit(1)

    # Step 3: Launch server
    try:
        launch_server(args.port, open_browser=not args.no_browser)
    except KeyboardInterrupt:
        print("\n\nShutting down Trinity Knot GUI...")
        print("Goodbye!")
    except Exception as e:
        print(f"\n\nERROR: Server failed to start: {e}")
        print("See logs above for details.")
        sys.exit(1)


if __name__ == "__main__":
    main()
