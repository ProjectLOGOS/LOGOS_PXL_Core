import os

# Import the main chat app
from app import app as chat_app
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles

# Mount static files
static_dir = os.path.join(os.path.dirname(__file__), "static")
if os.path.exists(static_dir):
    chat_app.mount("/static", StaticFiles(directory=static_dir), name="static")


@chat_app.get("/")
async def serve_chat_interface():
    """Serve the main chat interface"""
    static_file = os.path.join(static_dir, "index.html")
    return FileResponse(static_file)


# This allows the app to be run directly
if __name__ == "__main__":
    import uvicorn

    print("🚀 Starting LOGOS Interactive Chat Service...")
    print("📱 Chat Interface: http://127.0.0.1:8080")
    print("🔗 WebSocket Endpoint: ws://127.0.0.1:8080/ws/{session_id}")
    print("📡 REST API: http://127.0.0.1:8080/docs")
    uvicorn.run(chat_app, host="127.0.0.1", port=8080, log_level="info")
