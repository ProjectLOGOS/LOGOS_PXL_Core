#!/usr/bin/env python3
"""
Enhanced LOGOS AGI GUI Launcher
Includes new GPT-like chat interface with natural language processing
"""

import subprocess
import sys
import time
import webbrowser
import threading
from pathlib import Path
import argparse

def launch_chat_interface():
    """Launch the enhanced GPT-like chat interface"""
    print("💬 Launching LOGOS Enhanced Chat Interface...")
    try:
        python_exe = Path(__file__).parent / ".venv" / "Scripts" / "python.exe"
        chat_script = Path(__file__).parent / "logos_enhanced_chat_gui.py"

        if python_exe.exists() and chat_script.exists():
            # Start chat interface in background
            process = subprocess.Popen([str(python_exe), str(chat_script)])
        else:
            print("❌ Chat interface files not found. Running with system Python...")
            process = subprocess.Popen([sys.executable, "logos_enhanced_chat_gui.py"])

        # Wait a moment for server to start
        print("⏳ Starting chat interface...")
        time.sleep(3)

        # Open browser
        print("💬 Opening chat interface at http://localhost:3002")
        webbrowser.open("http://localhost:3002")

        print("\n" + "="*60)
        print("🎉 LOGOS Enhanced Chat Interface is running!")
        print("📍 URL: http://localhost:3002")
        print("💡 Features: GPT-like chat, Natural language processing")
        print("🛑 Press Ctrl+C to stop the server")
        print("="*60)

        # Keep the process running
        try:
            process.wait()
        except KeyboardInterrupt:
            print("\n🛑 Shutting down chat interface...")
            process.terminate()

    except Exception as e:
        print(f"❌ Failed to launch chat interface: {e}")
        print("💡 Make sure required packages are installed:")
        print("   pip install fastapi uvicorn aiohttp")

def launch_web_gui():
    """Launch the original web-based GUI"""
    print("🌐 Launching LOGOS Web GUI...")
    try:
        python_exe = Path(__file__).parent / ".venv" / "Scripts" / "python.exe"
        web_gui_script = Path(__file__).parent / "logos_web_gui.py"

        if python_exe.exists() and web_gui_script.exists():
            process = subprocess.Popen([str(python_exe), str(web_gui_script)])
        else:
            print("❌ Web GUI files not found. Running with system Python...")
            process = subprocess.Popen([sys.executable, "logos_web_gui.py"])

        time.sleep(3)
        print("🌐 Opening web GUI at http://localhost:3001")
        webbrowser.open("http://localhost:3001")

        print("\n" + "="*60)
        print("🎉 LOGOS Web GUI is running!")
        print("📍 URL: http://localhost:3001")
        print("🛑 Press Ctrl+C to stop the server")
        print("="*60)

        try:
            process.wait()
        except KeyboardInterrupt:
            print("\n🛑 Shutting down web GUI...")
            process.terminate()

    except Exception as e:
        print(f"❌ Failed to launch web GUI: {e}")

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

def launch_all():
    """Launch all interfaces"""
    print("🚀 Launching All LOGOS Interfaces...")

    # Launch chat interface in background
    chat_thread = threading.Thread(target=launch_chat_interface, daemon=True)
    chat_thread.start()

    time.sleep(2)

    # Launch web GUI in background
    web_thread = threading.Thread(target=launch_web_gui, daemon=True)
    web_thread.start()

    time.sleep(2)

    # Launch desktop GUI (blocking)
    launch_desktop_gui()

def check_logos_api():
    """Check if LOGOS API is running"""
    try:
        import requests
        response = requests.get("http://localhost:8090/health", timeout=5)
        if response.status_code == 200:
            print("✅ LOGOS Core API is running on http://localhost:8090")
            return True
        else:
            print("⚠️ LOGOS API responded with status:", response.status_code)
            return False
    except Exception as e:
        print("❌ LOGOS Core API is not running")
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
    parser = argparse.ArgumentParser(description="Enhanced LOGOS AGI GUI Launcher")
    parser.add_argument("--mode", choices=["chat", "web", "desktop", "all"],
                       default="chat", help="GUI mode to launch")
    parser.add_argument("--auto-start-api", action="store_true",
                       help="Automatically start LOGOS API if not running")
    parser.add_argument("--check-only", action="store_true",
                       help="Only check system status without launching GUI")

    args = parser.parse_args()

    print("🧠 Enhanced LOGOS AGI GUI Launcher")
    print("=" * 50)

    # Check API status
    api_running = check_logos_api()

    if not api_running and args.auto_start_api:
        api_process = start_logos_api()
        if api_process:
            api_running = check_logos_api()

    if args.check_only:
        return

    if not api_running:
        print("\n⚠️ WARNING: LOGOS Core API is not running!")
        print("The chat interface will have limited functionality.")
        print("To start the API: python deploy_core_services.py")

        choice = input("\nContinue anyway? (y/N): ").lower()
        if choice != 'y':
            print("👋 Goodbye!")
            return

    print(f"\n🚀 Launching LOGOS GUI in {args.mode} mode...")

    if args.mode == "chat":
        launch_chat_interface()
    elif args.mode == "web":
        launch_web_gui()
    elif args.mode == "desktop":
        launch_desktop_gui()
    elif args.mode == "all":
        launch_all()

if __name__ == "__main__":
    main()
