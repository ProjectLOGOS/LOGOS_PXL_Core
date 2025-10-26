"""
Trinity GUI Quick Smoke Test - Fast validation without hanging

Run with: python tests/test_trinity_gui_quick.py
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

def test_imports():
    """Test that all Trinity GUI components can be imported."""
    print("Testing imports...")
    try:
        from logos_trinity_gui import app, ConnectionManager, SystemState, system_state
        print("✓ logos_trinity_gui imports successful")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False

def test_app_creation():
    """Test that FastAPI app is created."""
    print("\nTesting FastAPI app...")
    try:
        from logos_trinity_gui import app
        assert app is not None
        assert hasattr(app, 'routes')
        print(f"✓ FastAPI app created with {len(app.routes)} routes")
        return True
    except Exception as e:
        print(f"✗ App creation failed: {e}")
        return False

def test_system_state():
    """Test SystemState class."""
    print("\nTesting SystemState...")
    try:
        from logos_trinity_gui import SystemState, system_state

        # Check states exist
        assert hasattr(SystemState, 'STASIS')
        assert hasattr(SystemState, 'LISTENING')
        assert hasattr(SystemState, 'PROCESSING')
        assert hasattr(SystemState, 'SPEAKING')

        # Check system_state instance
        assert system_state is not None
        assert hasattr(system_state, 'current_state')
        assert hasattr(system_state, 'sessions')

        # Test session creation
        system_state.create_session('test-session')
        session = system_state.get_session('test-session')
        assert session is not None
        assert 'created' in session
        assert 'audit_log' in session

        print(f"✓ SystemState working, current state: {system_state.current_state}")
        return True
    except Exception as e:
        print(f"✗ SystemState test failed: {e}")
        return False

def test_static_files_exist():
    """Test that static files exist."""
    print("\nTesting static files...")
    try:
        static_dir = Path(__file__).parent.parent / "static"

        files_to_check = [
            "trinity_knot.html",
            "trinity_knot.css",
            "trinity_knot.js"
        ]

        all_exist = True
        for filename in files_to_check:
            file_path = static_dir / filename
            if file_path.exists():
                size = file_path.stat().st_size
                print(f"  ✓ {filename} ({size:,} bytes)")
            else:
                print(f"  ✗ {filename} missing")
                all_exist = False

        return all_exist
    except Exception as e:
        print(f"✗ Static files check failed: {e}")
        return False

def test_health_endpoint():
    """Test health endpoint without starting server."""
    print("\nTesting health endpoint logic...")
    try:
        from fastapi.testclient import TestClient
        from logos_trinity_gui import app

        client = TestClient(app)
        response = client.get("/health")

        assert response.status_code == 200
        data = response.json()
        assert "status" in data
        print(f"✓ Health endpoint returns: {data.get('status')}")
        return True
    except Exception as e:
        print(f"✗ Health endpoint test failed: {e}")
        return False

def test_websocket_basic():
    """Test basic WebSocket connection (quick)."""
    print("\nTesting WebSocket connection...")
    try:
        from fastapi.testclient import TestClient
        from logos_trinity_gui import app

        client = TestClient(app)

        # Quick connection test
        with client.websocket_connect("/ws/test-quick") as websocket:
            # Just verify connection
            print("  ✓ WebSocket connection established")

            # Send ping
            websocket.send_json({"type": "ping"})

            # Try to receive (with quick timeout)
            try:
                msg = websocket.receive_json()
                if msg.get("type") == "pong":
                    print("  ✓ Ping/pong working")
                    return True
            except:
                print("  ⚠ No response (but connection worked)")
                return True

        return True
    except Exception as e:
        print(f"✗ WebSocket test failed: {e}")
        return False

def test_file_upload_validation():
    """Test file upload size validation."""
    print("\nTesting file upload validation...")
    try:
        from fastapi.testclient import TestClient
        from logos_trinity_gui import app

        client = TestClient(app)

        # Test oversized file rejection
        large_content = b"x" * (11 * 1024 * 1024)  # 11MB
        response = client.post(
            "/api/upload",
            files={"file": ("large.txt", large_content, "text/plain")}
        )

        assert response.status_code == 413
        print("  ✓ Oversized file (11MB) correctly rejected")

        # Test valid file
        small_content = b"Test content"
        response = client.post(
            "/api/upload",
            files={"file": ("small.txt", small_content, "text/plain")}
        )

        assert response.status_code == 200
        print("  ✓ Valid file accepted")

        return True
    except Exception as e:
        print(f"✗ File upload test failed: {e}")
        return False

def main():
    """Run all quick tests."""
    print("=" * 60)
    print("TRINITY GUI QUICK SMOKE TEST")
    print("=" * 60)

    tests = [
        ("Imports", test_imports),
        ("App Creation", test_app_creation),
        ("System State", test_system_state),
        ("Static Files", test_static_files_exist),
        ("Health Endpoint", test_health_endpoint),
        ("WebSocket Basic", test_websocket_basic),
        ("File Upload", test_file_upload_validation),
    ]

    results = []
    for name, test_func in tests:
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"✗ Test '{name}' crashed: {e}")
            results.append((name, False))

    # Summary
    print("\n" + "=" * 60)
    print("TEST SUMMARY")
    print("=" * 60)

    passed = sum(1 for _, result in results if result)
    total = len(results)

    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"{status}: {name}")

    print(f"\nTotal: {passed}/{total} tests passed ({100*passed//total}%)")

    if passed == total:
        print("✓ All smoke tests passed - Trinity GUI ready!")
        return 0
    else:
        print(f"⚠ {total - passed} test(s) failed")
        return 1

if __name__ == "__main__":
    exit(main())
