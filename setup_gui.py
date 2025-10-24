#!/usr/bin/env python3
"""
LOGOS AGI GUI Setup Script
Installs all required dependencies for both desktop and web GUI
"""

import subprocess
import sys
import os
from pathlib import Path

def run_command(command, description):
    """Run a command and handle errors"""
    print(f"📦 {description}...")
    try:
        result = subprocess.run(command, check=True, capture_output=True, text=True)
        print(f"✅ {description} - Success")
        return True
    except subprocess.CalledProcessError as e:
        print(f"❌ {description} - Failed: {e.stderr}")
        return False

def install_package(package_name):
    """Install a Python package"""
    return run_command([sys.executable, "-m", "pip", "install", package_name],
                      f"Installing {package_name}")

def setup_gui_dependencies():
    """Install all GUI dependencies"""
    print("🧠 LOGOS AGI GUI Setup")
    print("=" * 40)

    # Core dependencies
    packages = [
        "fastapi",
        "uvicorn[standard]",
        "aiohttp",
        "jinja2",
        "python-multipart",
        "requests",
        "websockets",
        "matplotlib",
        "numpy",
        "plotly",
        "pandas",
        "psutil"
    ]

    # Try to install tkinter (might be built-in)
    try:
        import tkinter
        print("✅ Tkinter already available")
    except ImportError:
        print("⚠️ Tkinter not found - this is usually included with Python")
        print("💡 If you're on Linux, install: sudo apt-get install python3-tk")

    success_count = 0
    for package in packages:
        if install_package(package):
            success_count += 1

    print(f"\n📊 Installation Summary: {success_count}/{len(packages)} packages installed")

    if success_count == len(packages):
        print("🎉 All dependencies installed successfully!")
        print("\nYou can now run:")
        print("  python launch_gui.py --mode web     # Web GUI")
        print("  python launch_gui.py --mode desktop # Desktop GUI")
        print("  python launch_gui.py --mode both    # Both GUIs")
    else:
        print("⚠️ Some packages failed to install. Check the errors above.")

    return success_count == len(packages)

def create_requirements_file():
    """Create a requirements.txt file for the GUI"""
    requirements = """# LOGOS AGI GUI Requirements
fastapi>=0.104.0
uvicorn[standard]>=0.24.0
aiohttp>=3.9.0
jinja2>=3.1.0
python-multipart>=0.0.6
requests>=2.31.0
websockets>=11.0
matplotlib>=3.7.0
numpy>=1.24.0
plotly>=5.17.0
pandas>=2.0.0
psutil>=5.9.0
"""

    requirements_path = Path("requirements_gui.txt")
    with open(requirements_path, "w") as f:
        f.write(requirements)

    print(f"📄 Created {requirements_path}")
    print("💡 You can also install with: pip install -r requirements_gui.txt")

def check_system_status():
    """Check current system status"""
    print("\n🔍 System Status Check")
    print("-" * 30)

    # Check Python version
    print(f"🐍 Python: {sys.version}")

    # Check if GUI files exist
    gui_files = [
        "logos_gui.py",
        "logos_web_gui.py",
        "launch_gui.py"
    ]

    for file in gui_files:
        if Path(file).exists():
            print(f"✅ {file} found")
        else:
            print(f"❌ {file} missing")

    # Check if LOGOS core exists
    if Path("logos_core").exists():
        print("✅ LOGOS core directory found")
    else:
        print("❌ LOGOS core directory missing")

    # Try to import key packages
    test_imports = [
        ("tkinter", "Desktop GUI support"),
        ("fastapi", "Web framework"),
        ("matplotlib", "Plotting"),
        ("numpy", "Numerical computing"),
        ("requests", "HTTP client")
    ]

    print("\n📦 Package Status:")
    for package, description in test_imports:
        try:
            __import__(package)
            print(f"✅ {package} - {description}")
        except ImportError:
            print(f"❌ {package} - {description} (not installed)")

def main():
    """Main setup function"""
    print("Welcome to LOGOS AGI GUI Setup!")
    print("This will install all required dependencies.\n")

    # Check current status
    check_system_status()

    # Ask user if they want to proceed
    print("\n" + "="*50)
    choice = input("Install GUI dependencies? (Y/n): ").lower()
    if choice == 'n':
        print("👋 Setup cancelled.")
        return

    # Create requirements file
    create_requirements_file()

    # Install dependencies
    success = setup_gui_dependencies()

    if success:
        print("\n🎉 Setup complete! Your LOGOS AGI GUI is ready.")
        print("\nNext steps:")
        print("1. Start LOGOS core: python deploy_core_services.py")
        print("2. Launch GUI: python launch_gui.py")
    else:
        print("\n⚠️ Setup incomplete. Please check errors above.")

if __name__ == "__main__":
    main()
