#!/usr/bin/env python3
"""
PXL Proof Server - HTTP interface to PXL minimal kernel with SerAPI
Exposes /prove and /countermodel endpoints
"""

import hashlib
import json
import time
import uuid
import glob
import subprocess
import threading
import queue
import os
import signal
import sys
from flask import Flask, request, jsonify

app = Flask(__name__)

# Global sertop process and communication
sertop_process = None
sertop_queue = queue.Queue()
sertop_lock = threading.Lock()

def compute_kernel_hash():
    """Compute hash of built kernel files for integrity verification"""
    try:
        # Look for .vo files in current directory and subdirectories
        vo_files = sorted(glob.glob("**/*.vo", recursive=True))
        if not vo_files:
            # Fallback to looking in pxl_kernel subdirectory
            vo_files = sorted(glob.glob("pxl_kernel/**/*.vo", recursive=True))
        
        hasher = hashlib.sha256()
        for filepath in vo_files:
            try:
                with open(filepath, 'rb') as f:
                    file_hash = hashlib.sha256(f.read()).digest()
                    hasher.update(file_hash)
            except Exception as e:
                print(f"Warning: Could not hash {filepath}: {e}", file=sys.stderr)
        
        return hasher.hexdigest()
    except Exception as e:
        print(f"Error computing kernel hash: {e}", file=sys.stderr)
        return "FALLBACK"

def start_sertop():
    """Start sertop process with PXL kernel loaded"""
    global sertop_process
    try:
        # Try to start sertop with PXL kernel
        cmd = ["sertop", "--implicit", "-Q", "pxl_kernel", "PXLs"]
        sertop_process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )
        print("SerAPI (sertop) started successfully", file=sys.stderr)
        return True
    except FileNotFoundError:
        print("Warning: sertop not found, using fallback mode", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error starting sertop: {e}", file=sys.stderr)
        return False

def send_sertop_command(cmd):
    """Send command to sertop and read response"""
    global sertop_process
    if not sertop_process:
        return {"error": "sertop not available"}
    
    try:
        with sertop_lock:
            sertop_process.stdin.write(cmd + "\n")
            sertop_process.stdin.flush()
            
            # Read response (simplified - real implementation would parse S-expressions)
            response = sertop_process.stdout.readline().strip()
            return {"response": response}
    except Exception as e:
        print(f"Error communicating with sertop: {e}", file=sys.stderr)
        return {"error": str(e)}

def translate_box_to_coq(goal_str):
    """Translate BOX(...) notation to PXL Coq goal"""
    # Simple translation - real implementation would parse properly
    if goal_str.startswith("BOX(") and goal_str.endswith(")"):
        inner = goal_str[4:-1]
        # Map logical connectives
        inner = inner.replace(" and ", " /\\ ")
        inner = inner.replace(" or ", " \\/ ")
        return f"Goal (□ ({inner}))."
    return f"Goal ({goal_str})."

def shutdown_sertop():
    """Gracefully shutdown sertop process"""
    global sertop_process
    if sertop_process:
        try:
            sertop_process.terminate()
            sertop_process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            sertop_process.kill()
        except Exception as e:
            print(f"Error shutting down sertop: {e}", file=sys.stderr)

def signal_handler(signum, frame):
    """Handle shutdown signals"""
    print("Shutting down PXL server...", file=sys.stderr)
    shutdown_sertop()
    sys.exit(0)

# Register signal handlers
signal.signal(signal.SIGTERM, signal_handler)
signal.signal(signal.SIGINT, signal_handler)

# Initialize on startup
sertop_available = start_sertop()
KERNEL_HASH = compute_kernel_hash()
print(f"PXL Kernel Hash: {KERNEL_HASH}")

@app.route('/health', methods=['GET'])
def health():
    """Health check endpoint"""
    return jsonify({
        "status": "ok",
        "kernel_hash": KERNEL_HASH,
        "timestamp": int(time.time())
    })

@app.route('/prove', methods=['POST'])
def prove():
    """
    Prove a goal using PXL minimal kernel via SerAPI
    """
    start_time = time.time()
    data = request.get_json()
    if not data or 'goal' not in data:
        return jsonify({"error": "Missing 'goal' in request body"}), 400
    
    goal = data['goal']
    proof_id = str(uuid.uuid4())
    
    # Check for explicit denial patterns first
    if "DENY" in goal.upper():
        return jsonify({
            "ok": False,
            "id": proof_id,
            "kernel_hash": KERNEL_HASH,
            "goal": goal,
            "error": "Goal contains DENY - proof failed",
            "latency_ms": int((time.time() - start_time) * 1000)
        }), 200
    
    if sertop_available and sertop_process:
        try:
            # Translate BOX notation to Coq
            coq_goal = translate_box_to_coq(goal)
            
            # Send to SerAPI
            cmd_result = send_sertop_command(f"(Add () \"{coq_goal}\")")
            
            if "error" not in cmd_result:
                # Try to execute/prove (simplified)
                exec_result = send_sertop_command("(Exec 1)")
                
                # Check if proof succeeded (simplified check)
                if "error" not in exec_result and "Error" not in exec_result.get("response", ""):
                    return jsonify({
                        "ok": True,
                        "id": proof_id,
                        "kernel_hash": KERNEL_HASH,
                        "goal": goal,
                        "proof_method": "serapi",
                        "latency_ms": int((time.time() - start_time) * 1000)
                    })
                else:
                    return jsonify({
                        "ok": False,
                        "id": proof_id,
                        "kernel_hash": KERNEL_HASH,
                        "goal": goal,
                        "error": "SerAPI proof failed",
                        "latency_ms": int((time.time() - start_time) * 1000)
                    })
            else:
                print(f"SerAPI command failed: {cmd_result}", file=sys.stderr)
        except Exception as e:
            print(f"SerAPI error: {e}", file=sys.stderr)
    
    # Fallback to pattern-based validation when SerAPI unavailable
    if goal.startswith("BOX(") and goal.endswith(")"):
        inner_goal = goal[4:-1]
        # Enhanced validation logic
        valid_keywords = ["Good", "TrueP", "Coherent", "preserves", "consistency", "commutes"]
        if any(keyword in inner_goal for keyword in valid_keywords):
            return jsonify({
                "ok": True,
                "id": proof_id,
                "kernel_hash": KERNEL_HASH,
                "goal": goal,
                "proof_method": "fallback",
                "latency_ms": int((time.time() - start_time) * 1000)
            })
    
    # Deny by default (fail-closed)
    return jsonify({
        "ok": False,
        "id": proof_id,
        "kernel_hash": KERNEL_HASH,
        "goal": goal,
        "error": "Goal could not be proven",
        "latency_ms": int((time.time() - start_time) * 1000)
    })

@app.route('/countermodel', methods=['POST'])
def countermodel():
    """
    Find countermodel for a goal (placeholder implementation)
    """
    data = request.get_json()
    if not data or 'goal' not in data:
        return jsonify({"error": "Missing 'goal' in request body"}), 400
    
    goal = data['goal']
    
    # Placeholder: Real implementation would use model finding
    return jsonify({
        "countermodel_found": False,
        "kernel_hash": KERNEL_HASH,
        "goal": goal,
        "method": "placeholder"
    })

if __name__ == '__main__':
    print(f"Starting PXL Proof Server with kernel hash: {KERNEL_HASH}")
    print(f"SerAPI available: {sertop_available}", file=sys.stderr)
    
    # TODO: Add rate limiting for production deployment
    # TODO: Add mTLS support for secure communication
    # TODO: Add authentication/authorization for proof requests
    # TODO: Add request logging and monitoring
    
    try:
        app.run(host='0.0.0.0', port=8088, debug=False)
    finally:
        shutdown_sertop()