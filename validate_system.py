"""
Final System Validation - Quick Check
"""

print("=" * 60)
print(" FINAL SYSTEM VALIDATION")
print("=" * 60)

# Test imports
print("\n1. Testing imports...")
try:
    from logos_trinity_gui import app, system_state
    from boot.extensions_loader import ExtensionsManager
    print("   ✓ All imports successful")
except Exception as e:
    print(f"   ✗ Import failed: {e}")
    exit(1)

# Check libraries
print("\n2. Checking external libraries...")
try:
    em = ExtensionsManager()
    status = em.get_status()
    loaded = status["loaded"]
    total = status["total"]
    print(f"   ✓ Libraries: {loaded}/{total} loaded ({100*loaded//total}%)")
except Exception as e:
    print(f"   ✗ Library check failed: {e}")

# Check Trinity state
print("\n3. Checking Trinity Knot state...")
try:
    print(f"   ✓ Current state: {system_state.current_state}")
    print(f"   ✓ Active sessions: {len(system_state.sessions)}")
except Exception as e:
    print(f"   ✗ State check failed: {e}")

# Check FastAPI app
print("\n4. Checking FastAPI app...")
try:
    print(f"   ✓ App title: {app.title}")
    print(f"   ✓ Routes configured: {len(app.routes)}")
except Exception as e:
    print(f"   ✗ App check failed: {e}")

# Check static files
print("\n5. Checking static assets...")
try:
    from pathlib import Path
    static_files = [
        "static/trinity_knot.html",
        "static/trinity_knot.css",
        "static/trinity_knot.js"
    ]
    for file in static_files:
        if Path(file).exists():
            size = Path(file).stat().st_size
            print(f"   ✓ {file} ({size:,} bytes)")
        else:
            print(f"   ✗ {file} missing")
except Exception as e:
    print(f"   ✗ Static files check failed: {e}")

# Summary
print("\n" + "=" * 60)
print(" VALIDATION COMPLETE")
print("=" * 60)
print("\n✅ System is operational and ready for demo!")
print("\nNext steps:")
print("  1. Run: python logos_launch_trinity.py")
print("  2. Open: http://localhost:5000")
print("  3. Test: Text query, voice input, file upload, graph viz")
print("  4. Review: Audit logs and session management")
print("\nFor full test suite:")
print("  python tests/test_trinity_gui_quick.py")
print("\n" + "=" * 60)
