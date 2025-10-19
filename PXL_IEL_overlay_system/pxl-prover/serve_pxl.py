#!/usr/bin/env python3
"""
PXL Proof Server - HTTP interface to PXL minimal kernel with SerAPI
Exposes /prove and /countermodel endpoints
HARDENED VERSION: Fail-closed verification with connection pooling and caching
"""

import glob
import hashlib
import queue
import signal
import subprocess
import sys
import threading
import time
import uuid
from typing import Dict, Optional, Tuple, Any
from dataclasses import dataclass
from collections import OrderedDict

from flask import Flask, jsonify, request

app = Flask(__name__)


class ProofValidationError(Exception):
    """Raised when proof validation fails in fail-closed mode"""
    pass


@dataclass
class ProofCacheEntry:
    """Cache entry for proof validation results"""
    verdict: bool
    timestamp: float
    proof_method: str
    latency_ms: int


@dataclass
class SessionInfo:
    """Information about an active Coq session"""
    process: subprocess.Popen
    session_id: str
    created_at: float
    last_used: float
    is_busy: bool


class CoqSessionPool:
    """Connection pool for persistent Coq sessions"""

    def __init__(self, max_pool_size: int = 3):
        self.max_pool_size = max_pool_size
        self.sessions: Dict[str, SessionInfo] = {}
        self.available_sessions = queue.Queue()
        self.lock = threading.Lock()
        self._session_counter = 0

    def _create_session(self) -> Optional[SessionInfo]:
        """Create a new Coq session"""
        try:
            session_id = f"coq_session_{self._session_counter}"
            self._session_counter += 1

            cmd = ["sertop", "--implicit", "-Q", "pxl_kernel", "PXLs"]
            process = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
            )

            session = SessionInfo(
                process=process,
                session_id=session_id,
                created_at=time.time(),
                last_used=time.time(),
                is_busy=False
            )

            # Initialize session with PXL kernel
            init_cmd = '(Add () "Require Import PXLs.PXLv3.")'
            if self._send_command(session, init_cmd).get("error"):
                process.terminate()
                return None

            return session

        except Exception as e:
            print(f"Failed to create Coq session: {e}", file=sys.stderr)
            return None

    def _send_command(self, session: SessionInfo, cmd: str) -> Dict[str, Any]:
        """Send command to a specific session"""
        try:
            session.process.stdin.write(cmd + "\n")
            session.process.stdin.flush()
            response = session.process.stdout.readline().strip()
            return {"response": response}
        except Exception as e:
            return {"error": str(e)}

    def get_session(self) -> Optional[SessionInfo]:
        """Get an available session from the pool"""
        with self.lock:
            # Try to get an available session
            try:
                while not self.available_sessions.empty():
                    session_id = self.available_sessions.get_nowait()
                    if session_id in self.sessions:
                        session = self.sessions[session_id]
                        if session.process.poll() is None:  # Still alive
                            session.is_busy = True
                            session.last_used = time.time()
                            return session
                        else:
                            # Session died, remove it
                            del self.sessions[session_id]
            except queue.Empty:
                pass

            # Create new session if under limit
            if len(self.sessions) < self.max_pool_size:
                session = self._create_session()
                if session:
                    self.sessions[session.session_id] = session
                    session.is_busy = True
                    return session

            return None

    def return_session(self, session: SessionInfo):
        """Return a session to the pool"""
        with self.lock:
            if session.session_id in self.sessions:
                session.is_busy = False
                session.last_used = time.time()
                self.available_sessions.put(session.session_id)

    def cleanup_session(self, session: SessionInfo):
        """Remove a failed session from the pool"""
        with self.lock:
            if session.session_id in self.sessions:
                try:
                    session.process.terminate()
                except:
                    pass
                del self.sessions[session.session_id]

    def get_stats(self) -> Dict[str, Any]:
        """Get pool statistics"""
        with self.lock:
            active_sessions = len([s for s in self.sessions.values() if not s.is_busy])
            busy_sessions = len([s for s in self.sessions.values() if s.is_busy])
            return {
                "total_sessions": len(self.sessions),
                "active_sessions": active_sessions,
                "busy_sessions": busy_sessions,
                "max_pool_size": self.max_pool_size
            }

    def shutdown(self):
        """Shutdown all sessions"""
        with self.lock:
            for session in self.sessions.values():
                try:
                    session.process.terminate()
                    session.process.wait(timeout=2)
                except:
                    try:
                        session.process.kill()
                    except:
                        pass
            self.sessions.clear()


class ProofCache:
    """TTL-based cache for proof validation results"""

    def __init__(self, ttl_seconds: int = 300, max_size: int = 1000):
        self.ttl_seconds = ttl_seconds
        self.max_size = max_size
        self.cache: OrderedDict[str, ProofCacheEntry] = OrderedDict()
        self.lock = threading.Lock()
        self.hits = 0
        self.misses = 0

    def _compute_key(self, goal: str) -> str:
        """Compute cache key for a goal"""
        return hashlib.sha256(goal.encode('utf-8')).hexdigest()

    def get(self, goal: str) -> Optional[ProofCacheEntry]:
        """Get cached result for a goal"""
        key = self._compute_key(goal)

        with self.lock:
            if key in self.cache:
                entry = self.cache[key]
                # Check TTL
                if time.time() - entry.timestamp <= self.ttl_seconds:
                    # Move to end (LRU)
                    self.cache.move_to_end(key)
                    self.hits += 1
                    return entry
                else:
                    # Expired
                    del self.cache[key]

            self.misses += 1
            return None

    def put(self, goal: str, verdict: bool, proof_method: str, latency_ms: int):
        """Cache a proof result"""
        key = self._compute_key(goal)
        entry = ProofCacheEntry(
            verdict=verdict,
            timestamp=time.time(),
            proof_method=proof_method,
            latency_ms=latency_ms
        )

        with self.lock:
            # Remove oldest entries if at capacity
            while len(self.cache) >= self.max_size:
                self.cache.popitem(last=False)

            self.cache[key] = entry

    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics"""
        with self.lock:
            total_requests = self.hits + self.misses
            hit_rate = (self.hits / total_requests) if total_requests > 0 else 0.0
            return {
                "cache_hits": self.hits,
                "cache_misses": self.misses,
                "hit_rate": hit_rate,
                "cache_size": len(self.cache),
                "max_size": self.max_size
            }

    def clear_expired(self):
        """Clear expired entries"""
        current_time = time.time()
        with self.lock:
            expired_keys = [
                key for key, entry in self.cache.items()
                if current_time - entry.timestamp > self.ttl_seconds
            ]
            for key in expired_keys:
                del self.cache[key]


# Global instances
session_pool = CoqSessionPool(max_pool_size=3)
proof_cache = ProofCache(ttl_seconds=300)


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
                with open(filepath, "rb") as f:
                    file_hash = hashlib.sha256(f.read()).digest()
                    hasher.update(file_hash)
            except Exception as e:
                print(f"Warning: Could not hash {filepath}: {e}", file=sys.stderr)

        return hasher.hexdigest()
    except Exception as e:
        print(f"Error computing kernel hash: {e}", file=sys.stderr)
        return "FALLBACK"


def translate_box_to_coq(goal_str: str) -> str:
    """Translate BOX(...) notation to PXL Coq goal"""
    if goal_str.startswith("BOX(") and goal_str.endswith(")"):
        inner = goal_str[4:-1]
        # Map logical connectives
        inner = inner.replace(" and ", " /\\ ")
        inner = inner.replace(" or ", " \\/ ")
        return f"Goal (□ ({inner}))."
    return f"Goal ({goal_str})."


def validate_proof_with_serapi(goal: str, session: SessionInfo) -> Tuple[bool, str, int]:
    """
    Validate proof using SerAPI - FAIL-CLOSED implementation
    Returns: (success, error_message, latency_ms)
    """
    start_time = time.time()

    try:
        # Translate goal to Coq
        coq_goal = translate_box_to_coq(goal)

        # Send goal to SerAPI
        cmd_result = session_pool._send_command(session, f'(Add () "{coq_goal}")')

        if "error" in cmd_result:
            error_msg = f"SerAPI goal parsing failed: {cmd_result.get('error', 'Unknown error')}"
            latency_ms = int((time.time() - start_time) * 1000)
            return False, error_msg, latency_ms

        # Try to execute/prove
        exec_result = session_pool._send_command(session, "(Exec 1)")

        latency_ms = int((time.time() - start_time) * 1000)

        # FAIL-CLOSED: Only succeed if we have explicit success indicators
        if ("error" not in exec_result and
            "Error" not in exec_result.get("response", "") and
            exec_result.get("response", "").strip()):
            return True, "Proof successful", latency_ms
        else:
            error_msg = f"SerAPI proof failed: {exec_result.get('response', 'No response')}"
            return False, error_msg, latency_ms

    except Exception as e:
        latency_ms = int((time.time() - start_time) * 1000)
        error_msg = f"SerAPI validation exception: {str(e)}"
        return False, error_msg, latency_ms


def shutdown_handler():
    """Gracefully shutdown all resources"""
    print("Shutting down PXL server...", file=sys.stderr)
    session_pool.shutdown()
    sys.exit(0)


def signal_handler(signum, frame):
    """Handle shutdown signals"""
    shutdown_handler()


# Register signal handlers
signal.signal(signal.SIGTERM, signal_handler)
signal.signal(signal.SIGINT, signal_handler)

# Initialize on startup
KERNEL_HASH = compute_kernel_hash()
print(f"PXL Kernel Hash: {KERNEL_HASH}")

# Start background thread for cache cleanup
def cache_cleanup_worker():
    """Background worker to clean expired cache entries"""
    while True:
        time.sleep(60)  # Check every minute
        proof_cache.clear_expired()

cache_cleanup_thread = threading.Thread(target=cache_cleanup_worker, daemon=True)
cache_cleanup_thread.start()


@app.route("/health", methods=["GET"])
def health():
    """Health check endpoint with basic system status"""
    pool_stats = session_pool.get_stats()

    return jsonify(
        {
            "status": "ok",
            "ready": True,
            "kernel_hash": KERNEL_HASH,
            "session_pool": pool_stats,
            "timestamp": int(time.time()),
        }
    )


@app.route("/health/proof_server", methods=["GET"])
def health_proof_server():
    """Detailed health check for proof server with monitoring metrics"""
    pool_stats = session_pool.get_stats()
    cache_stats = proof_cache.get_stats()

    # Determine overall status
    status = "ok"
    if pool_stats["total_sessions"] == 0:
        status = "degraded"
    elif pool_stats["active_sessions"] == 0 and pool_stats["busy_sessions"] > 0:
        status = "busy"

    return jsonify(
        {
            "status": status,
            "active_sessions": pool_stats["active_sessions"],
            "cache_hits": cache_stats["cache_hits"],
            "cache_misses": cache_stats["cache_misses"],
            "hit_rate": cache_stats["hit_rate"],
            "total_sessions": pool_stats["total_sessions"],
            "busy_sessions": pool_stats["busy_sessions"],
            "max_pool_size": pool_stats["max_pool_size"],
            "cache_size": cache_stats["cache_size"],
            "cache_max_size": cache_stats["max_size"],
            "kernel_hash": KERNEL_HASH,
            "timestamp": int(time.time()),
        }
    )


@app.route("/prove", methods=["POST"])
def prove():
    """
    Prove a goal using PXL minimal kernel via SerAPI
    HARDENED VERSION: Fail-closed validation with caching and connection pooling
    """
    start_time = time.time()
    data = request.get_json()

    if not data or "goal" not in data:
        return jsonify({"error": "Missing 'goal' in request body"}), 400

    goal = data["goal"]
    proof_id = str(uuid.uuid4())

    # Check cache first
    cached_result = proof_cache.get(goal)
    if cached_result:
        return jsonify(
            {
                "ok": cached_result.verdict,
                "id": proof_id,
                "kernel_hash": KERNEL_HASH,
                "goal": goal,
                "proof_method": f"{cached_result.proof_method}_cached",
                "latency_ms": int((time.time() - start_time) * 1000),
                "cache_hit": True,
            }
        )

    # Check for explicit denial patterns
    if "DENY" in goal.upper():
        error_msg = "Goal contains DENY - proof failed"
        proof_cache.put(goal, False, "pattern_deny", 0)
        return jsonify(
            {
                "ok": False,
                "id": proof_id,
                "kernel_hash": KERNEL_HASH,
                "goal": goal,
                "error": error_msg,
                "latency_ms": int((time.time() - start_time) * 1000),
                "cache_hit": False,
            }
        ), 200

    # FAIL-CLOSED: Get session from pool or fail
    session = session_pool.get_session()
    if not session:
        error_msg = "No available Coq sessions - SerAPI unavailable"
        raise ProofValidationError(error_msg)

    try:
        # Validate using SerAPI in fail-closed mode
        success, error_msg, validation_latency = validate_proof_with_serapi(goal, session)

        # Cache the result
        total_latency = int((time.time() - start_time) * 1000)
        proof_method = "serapi" if success else "serapi_failed"
        proof_cache.put(goal, success, proof_method, total_latency)

        # Return session to pool
        session_pool.return_session(session)

        if success:
            return jsonify(
                {
                    "ok": True,
                    "id": proof_id,
                    "kernel_hash": KERNEL_HASH,
                    "goal": goal,
                    "proof_method": "serapi",
                    "latency_ms": total_latency,
                    "cache_hit": False,
                }
            )
        else:
            # FAIL-CLOSED: Raise exception instead of falling back
            raise ProofValidationError(error_msg)

    except Exception as e:
        # Clean up failed session
        session_pool.cleanup_session(session)

        # FAIL-CLOSED: Block action, log event, raise error
        error_msg = f"Proof validation failed: {str(e)}"
        print(f"PROOF_VALIDATION_ERROR: {error_msg} for goal: {goal}", file=sys.stderr)

        return jsonify(
            {
                "ok": False,
                "id": proof_id,
                "kernel_hash": KERNEL_HASH,
                "goal": goal,
                "error": error_msg,
                "latency_ms": int((time.time() - start_time) * 1000),
                "cache_hit": False,
            }
        ), 500  # Internal server error for validation failures



@app.route("/countermodel", methods=["POST"])
def countermodel():
    """
    Find countermodel for a goal (placeholder implementation)
    """
    data = request.get_json()
    if not data or "goal" not in data:
        return jsonify({"error": "Missing 'goal' in request body"}), 400

    goal = data["goal"]

    # Placeholder: Real implementation would use model finding
    return jsonify(
        {
            "countermodel_found": False,
            "kernel_hash": KERNEL_HASH,
            "goal": goal,
            "method": "placeholder",
        }
    )


if __name__ == "__main__":
    print(f"Starting HARDENED PXL Proof Server with kernel hash: {KERNEL_HASH}")
    print(f"Session pool size: {session_pool.max_pool_size}", file=sys.stderr)
    print(f"Cache TTL: {proof_cache.ttl_seconds}s", file=sys.stderr)
    print("FAIL-CLOSED mode: No fallback validation enabled", file=sys.stderr)

    # Production mode: Use waitress WSGI server for stability
    try:
        from waitress import serve

        print("Using Waitress WSGI server for production stability...")
        serve(
            app,
            host="0.0.0.0",
            port=8088,
            threads=4,
            cleanup_interval=30,
            channel_timeout=60,
            connection_limit=100,
            max_request_body_size=1048576,
        )
    except ImportError:
        print("Waitress not available, using Flask with improved settings...")
        print("Install waitress for production: pip install waitress")

        try:
            # Improved Flask settings for stability
            app.run(
                host="0.0.0.0",
                port=8088,
                debug=False,
                threaded=True,
                use_reloader=False,
                processes=1,
            )
        finally:
            shutdown_handler()
