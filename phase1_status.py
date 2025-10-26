"""Quick status check for Phase 1"""
from boot.extensions_loader import extensions_manager

extensions_manager.initialize()
status = extensions_manager.get_status()

loaded_count = sum(1 for lib in status["libraries"].values() if lib["loaded"])
total_count = len(status["libraries"])

print("\n" + "="*60)
print("PHASE 1: EXTERNAL LIBRARY INTEGRATION - STATUS")
print("="*60)
print(f"\nLibraries Loaded: {loaded_count}/{total_count}")
print("\nWorking Libraries:")
for name, info in status["libraries"].items():
    if info["loaded"]:
        print(f"  [+] {name}")

print("\nMissing Libraries:")
for name, info in status["libraries"].items():
    if not info["loaded"]:
        reason = "Python 3.13 incompatible" if name == "pymc" else "C compiler required" if name == "pmdarima" else "Not installed"
        print(f"  [-] {name} ({reason})")

print("\n" + "="*60)
print(f"SUCCESS RATE: {(loaded_count/total_count)*100:.1f}%")
print("="*60 + "\n")
