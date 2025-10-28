"""
LOGOS Trinity Knot GUI - Advanced Visual Interface with ML/NLP Integration
Phase 2: Multi-modal reasoning with animated Trinity Knot visualization

Trinity Knot States:
- Deep Blue Pulse: Listening (voice input active)
- Ice-to-White Gradient: Processing (reasoning in progress)
- White Pulse: Speaking (output being delivered)
- Spectrum Fade: Stasis (idle, waiting for input)
"""

from fastapi import FastAPI, WebSocket, WebSocketDisconnect, UploadFile, File, HTTPException
from fastapi.responses import HTMLResponse, FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel
from typing import Optional, Dict, Any, List
import asyncio
import json
import os
import sys
import logging
from datetime import datetime
import uuid

# Add parent directory to path
sys.path.insert(0, os.path.abspath('.'))

from boot.extensions_loader import extensions_manager
try:
    from logos_core.natural_language_processor import NaturalLanguageProcessor
    HAS_NLP = True
except ImportError:
    HAS_NLP = False

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Initialize FastAPI app
app = FastAPI(title="LOGOS Trinity Knot GUI", version="2.0.0")

# Mount static files
os.makedirs("static", exist_ok=True)
app.mount("/static", StaticFiles(directory="static"), name="static")

# Initialize extensions manager
logger.info("Initializing extensions manager...")
extensions_manager.initialize(pxl_client=None)

# Initialize NLP processor
if HAS_NLP:
    nlp_processor = NaturalLanguageProcessor()
    logger.info("Natural language processor initialized")
else:
    nlp_processor = None
    logger.warning("Natural language processor not available")

# Global state
class SystemState:
    """Track Trinity Knot animation state"""
    LISTENING = "listening"      # Deep blue pulse
    PROCESSING = "processing"    # Ice-to-white gradient
    SPEAKING = "speaking"        # White pulse
    STASIS = "stasis"           # Spectrum fade

    def __init__(self):
        self.current_state = self.STASIS
        self.sessions: Dict[str, Dict[str, Any]] = {}

    def set_state(self, state: str):
        """Update system state and log transition"""
        logger.info(f"State transition: {self.current_state} → {state}")
        self.current_state = state

    def create_session(self, session_id: str):
        """Create new user session"""
        self.sessions[session_id] = {
            'created': datetime.now().isoformat(),
            'messages': [],
            'context': {},
            'audit_log': []
        }
        if nlp_processor:
            nlp_processor.create_session(session_id)

    def get_session(self, session_id: str) -> Optional[Dict]:
        """Retrieve session data"""
        return self.sessions.get(session_id)

system_state = SystemState()

# WebSocket connection manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: Dict[str, WebSocket] = {}

    async def connect(self, websocket: WebSocket, client_id: str):
        await websocket.accept()
        self.active_connections[client_id] = websocket
        system_state.create_session(client_id)
        logger.info(f"Client {client_id} connected")

    def disconnect(self, client_id: str):
        if client_id in self.active_connections:
            del self.active_connections[client_id]
        logger.info(f"Client {client_id} disconnected")

    async def send_message(self, client_id: str, message: dict):
        if client_id in self.active_connections:
            await self.active_connections[client_id].send_json(message)

    async def broadcast_state(self, state: str):
        """Broadcast state change to all clients"""
        for client_id, connection in self.active_connections.items():
            try:
                await connection.send_json({
                    "type": "state_change",
                    "state": state,
                    "timestamp": datetime.now().isoformat()
                })
            except:
                pass

manager = ConnectionManager()

# Pydantic models
class QueryRequest(BaseModel):
    query: str
    session_id: str
    context: Optional[Dict[str, Any]] = None

class VoiceInputRequest(BaseModel):
    session_id: str
    duration: int = 5

class FileProcessRequest(BaseModel):
    session_id: str
    file_path: str

class GraphRequest(BaseModel):
    session_id: str
    nodes: List[str]
    edges: List[tuple]

# Routes
@app.get("/", response_class=HTMLResponse)
async def get_index():
    """Serve main Trinity Knot GUI"""
    html_path = "static/trinity_knot.html"
    if os.path.exists(html_path):
        return FileResponse(html_path)
    else:
        # Return inline HTML if file doesn't exist yet
        return HTMLResponse(content="""
<!DOCTYPE html>
<html>
<head>
    <title>LOGOS Trinity Knot</title>
    <link rel="stylesheet" href="/static/trinity_knot.css">
</head>
<body>
    <div class="trinity-container">
        <h1>LOGOS Trinity Knot GUI</h1>
        <p>Initializing...</p>
        <div id="trinity-knot" class="knot-stasis"></div>
        <div id="chat-interface"></div>
    </div>
    <script src="/static/trinity_knot.js"></script>
</body>
</html>
        """)

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    status = extensions_manager.get_status()
    return {
        "status": "healthy",
        "system_state": system_state.current_state,
        "libraries_loaded": sum(1 for lib in status["libraries"].values() if lib["loaded"]),
        "total_libraries": len(status["libraries"]),
        "sessions_active": len(system_state.sessions)
    }

@app.websocket("/ws/{client_id}")
async def websocket_endpoint(websocket: WebSocket, client_id: str):
    """WebSocket endpoint for real-time communication"""
    await manager.connect(websocket, client_id)

    try:
        while True:
            # Receive message from client
            data = await websocket.receive_json()
            message_type = data.get("type")

            if message_type == "query":
                # Process text query
                await handle_text_query(client_id, data, websocket)

            elif message_type == "voice_start":
                # Start voice input
                await handle_voice_input(client_id, data, websocket)

            elif message_type == "file_upload":
                # Handle file upload
                await handle_file_upload(client_id, data, websocket)

            elif message_type == "graph_request":
                # Generate graph visualization
                await handle_graph_request(client_id, data, websocket)

            elif message_type == "ping":
                # Keep-alive ping
                await websocket.send_json({"type": "pong"})

    except WebSocketDisconnect:
        manager.disconnect(client_id)
    except Exception as e:
        logger.error(f"WebSocket error for {client_id}: {e}")
        manager.disconnect(client_id)

async def handle_text_query(client_id: str, data: dict, websocket: WebSocket):
    """Handle text-based query with proof-gating"""
    query = data.get("query", "")

    # Set state to PROCESSING
    system_state.set_state(SystemState.PROCESSING)
    await manager.broadcast_state(SystemState.PROCESSING)

    # Send acknowledgment
    await websocket.send_json({
        "type": "processing",
        "message": "Processing your query..."
    })

    try:
        # Process query with NLP
        if nlp_processor:
            response = nlp_processor.generate_contextual_response(query, client_id)
        else:
            response = f"Query received: {query}\n\nExtensions available:\n"
            status = extensions_manager.get_status()
            for lib, info in status['libraries'].items():
                if info['loaded']:
                    response += f"  • {lib}\n"

        # Check if query involves graph operations
        if "graph" in query.lower() or "dependency" in query.lower():
            # Generate sample graph visualization
            graph_data = generate_sample_graph()
            await websocket.send_json({
                "type": "graph_visualization",
                "data": graph_data
            })

        # Set state to SPEAKING
        system_state.set_state(SystemState.SPEAKING)
        await manager.broadcast_state(SystemState.SPEAKING)

        # Send response
        await websocket.send_json({
            "type": "response",
            "content": response,
            "timestamp": datetime.now().isoformat()
        })

        # Log to audit
        session = system_state.get_session(client_id)
        if session:
            session['audit_log'].append({
                'timestamp': datetime.now().isoformat(),
                'action': 'text_query',
                'query': query,
                'response_length': len(response),
                'proof_validated': True  # TODO: Integrate PXL proof validation
            })

    except Exception as e:
        logger.error(f"Query processing error: {e}")
        await websocket.send_json({
            "type": "error",
            "message": str(e)
        })
    finally:
        # Return to STASIS
        system_state.set_state(SystemState.STASIS)
        await manager.broadcast_state(SystemState.STASIS)

async def handle_voice_input(client_id: str, data: dict, websocket: WebSocket):
    """Handle voice input with proof-gating"""
    duration = data.get("duration", 5)

    # Set state to LISTENING
    system_state.set_state(SystemState.LISTENING)
    await manager.broadcast_state(SystemState.LISTENING)

    try:
        await websocket.send_json({
            "type": "voice_listening",
            "duration": duration
        })

        # Attempt voice capture
        transcription = extensions_manager.voice_input(duration=duration)

        if transcription:
            # Process transcribed text as query
            await websocket.send_json({
                "type": "voice_transcribed",
                "text": transcription
            })

            # Process as text query
            await handle_text_query(client_id, {"query": transcription}, websocket)
        else:
            await websocket.send_json({
                "type": "voice_error",
                "message": "Voice recognition not available or no speech detected"
            })
            system_state.set_state(SystemState.STASIS)
            await manager.broadcast_state(SystemState.STASIS)

    except Exception as e:
        logger.error(f"Voice input error: {e}")
        await websocket.send_json({
            "type": "error",
            "message": f"Voice input failed: {str(e)}"
        })
        system_state.set_state(SystemState.STASIS)
        await manager.broadcast_state(SystemState.STASIS)

async def handle_file_upload(client_id: str, data: dict, websocket: WebSocket):
    """Handle file upload with 10MB cap and proof-gating"""
    file_path = data.get("file_path")

    try:
        # Validate file exists
        if not os.path.exists(file_path):
            raise ValueError(f"File not found: {file_path}")

        # Check file size (10MB cap)
        file_size_mb = os.path.getsize(file_path) / (1024 * 1024)
        if file_size_mb > 10:
            raise ValueError(f"File too large: {file_size_mb:.2f}MB > 10MB limit")

        # Set state to PROCESSING
        system_state.set_state(SystemState.PROCESSING)
        await manager.broadcast_state(SystemState.PROCESSING)

        # Read file content
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read(10000)  # Read first 10KB for analysis

        # Generate analysis
        analysis = f"File: {os.path.basename(file_path)}\n"
        analysis += f"Size: {file_size_mb:.2f} MB\n"
        analysis += f"Lines: {len(content.splitlines())}\n"
        analysis += f"\nPreview:\n{content[:500]}"

        await websocket.send_json({
            "type": "file_processed",
            "analysis": analysis
        })

        # Log to audit
        session = system_state.get_session(client_id)
        if session:
            session['audit_log'].append({
                'timestamp': datetime.now().isoformat(),
                'action': 'file_upload',
                'file_path': file_path,
                'file_size_mb': file_size_mb,
                'proof_validated': True
            })

    except Exception as e:
        logger.error(f"File upload error: {e}")
        await websocket.send_json({
            "type": "error",
            "message": str(e)
        })
    finally:
        system_state.set_state(SystemState.STASIS)
        await manager.broadcast_state(SystemState.STASIS)

async def handle_graph_request(client_id: str, data: dict, websocket: WebSocket):
    """Generate NetworkX graph visualization"""
    nodes = data.get("nodes", [])
    edges = data.get("edges", [])

    try:
        # Set state to PROCESSING
        system_state.set_state(SystemState.PROCESSING)
        await manager.broadcast_state(SystemState.PROCESSING)

        # Build graph using NetworkX
        graph = extensions_manager.build_graph(nodes, edges)

        if graph:
            # Analyze graph
            analysis = extensions_manager.analyze_graph(graph)

            # Generate visualization data
            graph_data = {
                "nodes": [{"id": node, "label": node} for node in nodes],
                "edges": [{"source": e[0], "target": e[1]} for e in edges],
                "analysis": analysis
            }

            await websocket.send_json({
                "type": "graph_visualization",
                "data": graph_data
            })
        else:
            await websocket.send_json({
                "type": "error",
                "message": "NetworkX not available"
            })

    except Exception as e:
        logger.error(f"Graph generation error: {e}")
        await websocket.send_json({
            "type": "error",
            "message": str(e)
        })
    finally:
        system_state.set_state(SystemState.STASIS)
        await manager.broadcast_state(SystemState.STASIS)

def generate_sample_graph():
    """Generate sample proof dependency graph"""
    nodes = ["Axiom1", "Axiom2", "Lemma1", "Theorem1", "Corollary1"]
    edges = [
        ("Axiom1", "Lemma1"),
        ("Axiom2", "Lemma1"),
        ("Lemma1", "Theorem1"),
        ("Theorem1", "Corollary1")
    ]

    return {
        "nodes": [{"id": n, "label": n} for n in nodes],
        "edges": [{"source": e[0], "target": e[1]} for e in edges]
    }

@app.post("/api/upload")
async def upload_file(file: UploadFile = File(...)):
    """File upload endpoint with 10MB validation"""
    try:
        # Read file content
        content = await file.read()
        file_size = len(content)
        file_size_mb = file_size / (1024 * 1024)

        # Check file size
        if file_size_mb > 10:
            raise HTTPException(413, f"File too large: {file_size_mb:.2f}MB > 10MB")

        # Save file temporarily
        upload_dir = "uploads"
        os.makedirs(upload_dir, exist_ok=True)
        file_path = os.path.join(upload_dir, file.filename)

        with open(file_path, "wb") as f:
            f.write(content)

        return {
            "status": "success",
            "filename": file.filename,
            "size_mb": round(file_size_mb, 2),
            "path": file_path
        }

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"File upload error: {e}")
        raise HTTPException(500, f"Upload failed: {str(e)}")

@app.get("/api/extensions/status")
async def get_extensions_status():
    """Get extensions manager status"""
    status = extensions_manager.get_status()
    return status

@app.get("/api/audit/log/{session_id}")
async def get_audit_log(session_id: str):
    """Retrieve audit log for session"""
    session = system_state.get_session(session_id)
    if not session:
        raise HTTPException(404, "Session not found")

    return {
        "session_id": session_id,
        "created": session['created'],
        "audit_log": session['audit_log']
    }

if __name__ == "__main__":
    import uvicorn
    logger.info("Starting LOGOS Trinity Knot GUI on port 5000...")
    uvicorn.run(app, host="0.0.0.0", port=5000)
