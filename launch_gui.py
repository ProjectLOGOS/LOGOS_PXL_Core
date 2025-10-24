#!/usr/bin/env python3
"""
LOGOS AGI GUI Launcher
Choose between desktop (Tkinter) or web-based GUI
"""

import subprocess
import sys
import time
import webbrowser
import threading
from pathlib import Path
import argparse

def launch_desktop_gui():
    """Launch the desktop Tkinter GUI"""
    print("🖥️ Launching LOGOS Desktop GUI...")
    try:
        python_exe = Path(__file__).parent / ".venv" / "Scripts" / "python.exe"
        gui_script = Path(__file__).parent / "logos_gui.py"

        if python_exe.exists() and gui_script.exists():
            subprocess.run([str(python_exe), str(gui_script)])
        else:
            print("❌ Desktop GUI files not found. Running with system Python...")
            subprocess.run([sys.executable, "logos_gui.py"])

    except Exception as e:
        print(f"❌ Failed to launch desktop GUI: {e}")
        print("💡 Make sure Tkinter is installed: pip install tkinter")

def launch_web_gui():
    """Launch the web-based GUI"""
    print("🌐 Launching LOGOS Web GUI...")
    try:
        python_exe = Path(__file__).parent / ".venv" / "Scripts" / "python.exe"
        web_gui_script = Path(__file__).parent / "logos_web_gui.py"

        if python_exe.exists() and web_gui_script.exists():
            # Start web server in background
            process = subprocess.Popen([str(python_exe), str(web_gui_script)])
        else:
            print("❌ Web GUI files not found. Running with system Python...")
            process = subprocess.Popen([sys.executable, "logos_web_gui.py"])

        # Wait a moment for server to start
        print("⏳ Starting web server...")
        time.sleep(3)

        # Open browser
        print("🌐 Opening browser at http://localhost:3001")
        webbrowser.open("http://localhost:3001")

        print("\n" + "="*60)
        print("🎉 LOGOS AGI Web GUI is running!")
        print("📍 URL: http://localhost:3001")
        print("🛑 Press Ctrl+C to stop the server")
        print("="*60)

        # Keep the process running
        try:
            process.wait()
        except KeyboardInterrupt:
            print("\n🛑 Shutting down web server...")
            process.terminate()

    except Exception as e:
        print(f"❌ Failed to launch web GUI: {e}")
        print("💡 Make sure required packages are installed:")
        print("   pip install fastapi uvicorn aiohttp jinja2")

def launch_both():
    """Launch both desktop and web GUI"""
    print("🚀 Launching both Desktop and Web GUI...")

    # Launch web GUI in background
    web_thread = threading.Thread(target=launch_web_gui, daemon=True)
    web_thread.start()

    # Wait a moment
    time.sleep(2)

    # Launch desktop GUI (blocking)
    launch_desktop_gui()

def check_logos_api():
    """Check if LOGOS API is running"""
    try:
        import requests
        response = requests.get("http://localhost:8090/health", timeout=5)
        if response.status_code == 200:
            print("✅ LOGOS API is running on http://localhost:8090")
            return True
        else:
            print("⚠️ LOGOS API responded with status:", response.status_code)
            return False
    except Exception as e:
        print("❌ LOGOS API is not running")
        print("💡 Start the API first: python deploy_core_services.py")
        return False

def start_logos_api():
    """Start the LOGOS API if not running"""
    print("🚀 Starting LOGOS Core API...")
    try:
        python_exe = Path(__file__).parent / ".venv" / "Scripts" / "python.exe"
        api_script = Path(__file__).parent / "deploy_core_services.py"

        if python_exe.exists() and api_script.exists():
            process = subprocess.Popen([str(python_exe), str(api_script)])
            print("⏳ Waiting for API to start...")
            time.sleep(10)
            return process
        else:
            print("❌ API deployment script not found")
            return None

    except Exception as e:
        print(f"❌ Failed to start LOGOS API: {e}")
        return None

def main():
    parser = argparse.ArgumentParser(description="LOGOS AGI GUI Launcher")
    parser.add_argument("--mode", choices=["desktop", "web", "both"],
                       default="web", help="GUI mode to launch")
    parser.add_argument("--auto-start-api", action="store_true",
                       help="Automatically start LOGOS API if not running")
    parser.add_argument("--check-only", action="store_true",
                       help="Only check system status without launching GUI")

    args = parser.parse_args()

    print("🧠 LOGOS AGI GUI Launcher")
    print("=" * 40)

    # Check API status
    api_running = check_logos_api()

    if not api_running and args.auto_start_api:
        api_process = start_logos_api()
        if api_process:
            api_running = check_logos_api()

    if args.check_only:
        return

    if not api_running:
        print("\n⚠️ WARNING: LOGOS API is not running!")
        print("The GUI will have limited functionality.")
        print("To start the API: python deploy_core_services.py")

        choice = input("\nContinue anyway? (y/N): ").lower()
        if choice != 'y':
            print("👋 Goodbye!")
            return

    print(f"\n🚀 Launching GUI in {args.mode} mode...")

    if args.mode == "desktop":
        launch_desktop_gui()
    elif args.mode == "web":
        launch_web_gui()
    elif args.mode == "both":
        launch_both()

if __name__ == "__main__":
    main()
