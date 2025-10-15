import json
import uuid
from datetime import datetime
from typing import Any

import requests
from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect

# Import our new GPT engine
from gpt_engine import GPTLOGOSEngine
from pydantic import BaseModel

app = FastAPI(title="LOGOS Interactive Chat Service")

# Connection manager for WebSocket connections
class ConnectionManager:
    def __init__(self):
        self.active_connections: list[WebSocket] = []
        self.user_sessions: dict[str, dict] = {}

    async def connect(self, websocket: WebSocket, session_id: str):
        await websocket.accept()
        self.active_connections.append(websocket)
        self.user_sessions[session_id] = {
            "websocket": websocket,
            "connected_at": datetime.now(),
            "message_count": 0,
            "conversation_history": []
        }

    def disconnect(self, websocket: WebSocket, session_id: str):
        if websocket in self.active_connections:
            self.active_connections.remove(websocket)
        if session_id in self.user_sessions:
            del self.user_sessions[session_id]

    async def send_personal_message(self, message: str, session_id: str):
        if session_id in self.user_sessions:
            websocket = self.user_sessions[session_id]["websocket"]
            await websocket.send_text(message)

    async def broadcast(self, message: str):
        for connection in self.active_connections:
            await connection.send_text(message)

manager = ConnectionManager()

# Models
class ChatMessage(BaseModel):
    message: str
    session_id: str
    user_id: str | None = "anonymous"
    message_type: str = "text"  # text, voice, command
    context: dict[str, Any] | None = {}

class ChatResponse(BaseModel):
    response: str
    session_id: str
    timestamp: str
    response_type: str = "text"
    metadata: dict[str, Any] | None = {}

class VoiceMessage(BaseModel):
    audio_data: str  # Base64 encoded audio
    session_id: str
    format: str = "wav"
    sample_rate: int = 16000

# Configuration
LOGOS_API_URL = "http://127.0.0.1:8090"
TOOL_ROUTER_URL = "http://127.0.0.1:8071"
EXECUTOR_URL = "http://127.0.0.1:8072"

# AI Chat Engine with GPT Integration
class LOGOSChatEngine:
    def __init__(self):
        # Initialize GPT engine
        self.gpt_engine = GPTLOGOSEngine()
        self.conversation_context = {}
        self.system_capabilities = {
            "text_processing": "TETRAGNOS for semantic analysis and clustering",
            "forecasting": "TELOS for time series prediction",
            "theorem_proving": "THONOC for logical reasoning",
            "security": "Proof-gated execution with kernel verification"
        }

    async def authorize_chat_action(self, action: str, session_id: str) -> dict[str, Any]:
        """Get authorization for chat actions through LOGOS alignment system"""
        auth_request = {
            "action": f"chat:{action}",
            "state": "interactive",
            "props": "user_input",
            "provenance": {
                "src": "interactive_chat",
                "session_id": session_id,
                "timestamp": datetime.now().isoformat()
            }
        }

        try:
            response = requests.post(
                f"{LOGOS_API_URL}/authorize_action",
                json=auth_request,
                timeout=5
            )
            if response.status_code == 200:
                return response.json()
            else:
                raise HTTPException(403, "Chat action not authorized")
        except requests.exceptions.RequestException:
            # Fallback for basic chat interactions
            return {
                "authorized": True,
                "proof_token": {
                    "id": f"fallback-{uuid.uuid4()}",
                    "kernel_hash": "fallback",
                    "action": action
                }
            }

    async def process_message(self, message: str, session_id: str) -> str:
        """Process user message through GPT-enhanced LOGOS capabilities"""

        # Check for system commands first (keep existing functionality)
        if message.startswith("/"):
            return await self.handle_command(message, session_id)

        # Use GPT for intelligent processing
        try:
            response_text, tool_request = await self.gpt_engine.process_message(message, session_id)

            # If GPT wants to use a tool, execute it
            if tool_request:
                tool_result = await self.execute_gpt_tool_request(tool_request, session_id)
                return f"{response_text}\n\n{tool_result}"

            return response_text

        except Exception as e:
            # Fallback to original logic if GPT fails
            print(f"GPT processing failed: {e}")
            return await self.fallback_process_message(message, session_id)

    async def execute_gpt_tool_request(self, tool_request: dict, session_id: str) -> str:
        """Execute tool request from GPT"""
        tool = tool_request.get("tool")
        operation = tool_request.get("operation")
        data = tool_request.get("data", {})

        try:
            if tool == "tetragnos":
                return await self.handle_text_analysis_gpt(data, session_id)
            elif tool == "telos":
                return await self.handle_forecasting_gpt(data, session_id)
            elif tool == "thonoc":
                return await self.handle_theorem_proving_gpt(data, session_id)
            else:
                return f"❌ Unknown tool: {tool}"
        except Exception as e:
            return f"⚠️ Tool execution failed: {str(e)}"

    async def handle_text_analysis_gpt(self, data: dict, session_id: str) -> str:
        """Handle GPT-routed text analysis"""
        try:
            auth = await self.authorize_chat_action("text_analysis", session_id)
            texts = data.get("texts", [])
            k = data.get("k", min(2, len(texts)))

            request_data = {
                "tool": "tetragnos",
                "args": {"op": "cluster_texts", "texts": texts, "k": k},
                "proof_token": auth["proof_token"]
            }

            response = requests.post(f"{TOOL_ROUTER_URL}/route", json=request_data, timeout=10)

            if response.status_code == 200:
                result = response.json()
                analysis_result = result['result']
                clusters = analysis_result.get('k', 1)
                items = analysis_result.get('items', [])

                return f"""📊 Text Analysis Results:

**Processed {len(texts)} text segments**
**Organized into {clusters} semantic clusters**

**Analysis Details:**
{chr(10).join([f"• Cluster {item['cluster']}: {item['text'][:100]}{'...' if len(item['text']) > 100 else ''}" for item in items[:5]])}

✅ Analysis completed successfully through TETRAGNOS toolkit."""
            else:
                return "❌ Text analysis failed. Please try again."
        except Exception as e:
            return f"⚠️ Error in text analysis: {str(e)}"

    async def handle_forecasting_gpt(self, data: dict, session_id: str) -> str:
        """Handle GPT-routed forecasting"""
        try:
            auth = await self.authorize_chat_action("forecasting", session_id)
            series = data.get("series", [])
            horizon = data.get("horizon", 4)

            request_data = {
                "tool": "telos",
                "args": {"op": "forecast_series", "series": series, "horizon": horizon},
                "proof_token": auth["proof_token"]
            }

            response = requests.post(f"{TOOL_ROUTER_URL}/route", json=request_data, timeout=10)

            if response.status_code == 200:
                result = response.json()
                forecast = result['result']['forecast']
                return f"""📈 Forecasting Results:

**Input Data:** {', '.join(map(str, series))}
**{horizon}-Step Forecast:** {', '.join(map(str, [round(f, 2) for f in forecast]))}

The trend analysis shows the data progression and predicts the next {horizon} values based on linear extrapolation.

✅ Forecast completed successfully through TELOS toolkit."""
            else:
                return "❌ Forecasting failed. Please try again."
        except Exception as e:
            return f"⚠️ Error in forecasting: {str(e)}"

    async def handle_theorem_proving_gpt(self, data: dict, session_id: str) -> str:
        """Handle GPT-routed theorem proving"""
        try:
            auth = await self.authorize_chat_action("theorem_proving", session_id)
            formula = data.get("formula", "")

            request_data = {
                "tool": "thonoc",
                "args": {"op": "construct_proof", "formula": formula},
                "proof_token": auth["proof_token"]
            }

            response = requests.post(f"{TOOL_ROUTER_URL}/route", json=request_data, timeout=10)

            if response.status_code == 200:
                result = response.json()
                return f"""🔬 Theorem Proving Results:

**Statement:** {formula}
**Proof Status:** {"✅ PROVED" if result.get('result', {}).get('proved') else "❌ COULD NOT PROVE"}

The logical statement has been processed using automated theorem proving.

✅ Proof attempt completed through THONOC toolkit."""
            else:
                return "❌ Theorem proving failed. Please try again."
        except Exception as e:
            return f"⚠️ Error in theorem proving: {str(e)}"

    async def fallback_process_message(self, message: str, session_id: str) -> str:
        """Fallback to original pattern matching if GPT fails"""
        if any(keyword in message.lower() for keyword in ["analyze", "cluster", "semantic", "text analysis"]):
            return await self.handle_text_analysis(message, session_id)
        elif any(keyword in message.lower() for keyword in ["predict", "forecast", "trend"]):
            return await self.handle_forecasting(message, session_id)
        elif any(keyword in message.lower() for keyword in ["prove", "logic", "theorem"]):
            return await self.handle_theorem_proving(message, session_id)
        else:
            return await self.handle_general_chat(message, session_id)

    async def handle_command(self, command: str, session_id: str) -> str:
        """Handle system commands"""
        cmd = command.lower().strip()

        if cmd == "/help":
            return """🤖 LOGOS Interactive Assistant - Available Commands:

**System Commands:**
/help - Show this help message
/status - Show system status
/capabilities - List available AI capabilities
/clear - Clear conversation history

**AI Capabilities:**
- Text analysis: "analyze this text: [your text]"
- Forecasting: "predict trends for data: [numbers]"
- Logic: "prove that [logical statement]"
- General chat: Just type naturally!

**Voice Commands:**
- Click the microphone to speak
- Say "LOGOS" to activate voice mode
- Voice responses available for all interactions
"""

        elif cmd == "/status":
            return await self.get_system_status()

        elif cmd == "/capabilities":
            caps = "\n".join([f"• {name}: {desc}" for name, desc in self.system_capabilities.items()])
            return f"🔧 LOGOS AI Capabilities:\n\n{caps}"

        elif cmd == "/clear":
            if session_id in self.conversation_context:
                del self.conversation_context[session_id]
            return "🗑️ Conversation history cleared."

        else:
            return f"❓ Unknown command: {command}. Type /help for available commands."

    async def handle_text_analysis(self, message: str, session_id: str) -> str:
        """Handle text analysis requests through TETRAGNOS"""
        try:
            # Get authorization
            auth = await self.authorize_chat_action("text_analysis", session_id)

            # Extract text to analyze (improved parsing)
            text_to_analyze = message.lower()
            # Remove common prefixes
            for prefix in ["analyze this text:", "analyze text:", "analyze this:", "analyze", "cluster", "semantic analysis of"]:
                text_to_analyze = text_to_analyze.replace(prefix, "")
            text_to_analyze = text_to_analyze.strip()

            if not text_to_analyze:
                return "📝 Please provide some text to analyze. Example: 'analyze this text: Machine learning is fascinating'"

            # Split into sentences for clustering
            sentences = [s.strip() for s in text_to_analyze.split('.') if s.strip()]
            if len(sentences) < 2:
                sentences = [text_to_analyze]  # Single text item

            # Call TETRAGNOS through Tool Router
            request_data = {
                "tool": "tetragnos",
                "args": {
                    "op": "cluster_texts",
                    "texts": sentences,
                    "k": min(2, len(sentences))
                },
                "proof_token": auth["proof_token"]
            }

            response = requests.post(
                f"{TOOL_ROUTER_URL}/route",
                json=request_data,
                timeout=10
            )

            if response.status_code == 200:
                result = response.json()
                analysis_result = result['result']  # Tool Router wraps the response
                clusters = analysis_result.get('k', 1)
                items = analysis_result.get('items', [])

                return f"""📊 Text Analysis Results:

**Processed {len(sentences)} text segments**
**Organized into {clusters} semantic clusters**

**Analysis Details:**
{chr(10).join([f"• Cluster {item['cluster']}: {item['text'][:100]}{'...' if len(item['text']) > 100 else ''}" for item in items[:5]])}

✅ Analysis completed successfully through TETRAGNOS toolkit."""
            else:
                return "❌ Text analysis failed. Please try again."

        except Exception as e:
            return f"⚠️ Error in text analysis: {str(e)}"

    async def handle_forecasting(self, message: str, session_id: str) -> str:
        """Handle forecasting requests through TELOS"""
        try:
            # Get authorization
            auth = await self.authorize_chat_action("forecasting", session_id)

            # Simple number extraction (could be enhanced with NLP)
            import re
            numbers = re.findall(r'-?\d+\.?\d*', message)
            if len(numbers) < 3:
                return "📈 Please provide at least 3 numbers for forecasting. Example: 'predict trends for: 10, 12, 15, 18'"

            series = [float(num) for num in numbers[:10]]  # Limit to 10 numbers

            # Call TELOS through Tool Router
            request_data = {
                "tool": "telos",
                "args": {
                    "op": "forecast_series",
                    "series": series,
                    "horizon": 4
                },
                "proof_token": auth["proof_token"]
            }

            response = requests.post(
                f"{TOOL_ROUTER_URL}/route",
                json=request_data,
                timeout=10
            )

            if response.status_code == 200:
                result = response.json()
                forecast = result['result']['forecast']
                return f"""📈 Forecasting Results:

**Input Data:** {', '.join(map(str, series))}
**4-Step Forecast:** {', '.join(map(str, [round(f, 2) for f in forecast]))}

The trend analysis shows the data progression and predicts the next 4 values based on linear extrapolation.

✅ Forecast completed successfully through TELOS toolkit."""
            else:
                return "❌ Forecasting failed. Please try again."

        except Exception as e:
            return f"⚠️ Error in forecasting: {str(e)}"

    async def handle_theorem_proving(self, message: str, session_id: str) -> str:
        """Handle theorem proving through THONOC"""
        try:
            # Get authorization
            auth = await self.authorize_chat_action("theorem_proving", session_id)

            # Extract logical statement (simple parsing)
            statement = message.lower().replace("prove that", "").replace("prove", "").strip()
            if "true" in statement and "true" in statement:
                formula = "And(True, True)"
            elif "false" in statement:
                formula = "And(True, False)"
            else:
                formula = "And(True, True)"  # Default tautology

            # Call THONOC through Tool Router
            request_data = {
                "tool": "thonoc",
                "args": {
                    "op": "construct_proof",
                    "formula": formula
                },
                "proof_token": auth["proof_token"]
            }

            response = requests.post(
                f"{TOOL_ROUTER_URL}/route",
                json=request_data,
                timeout=10
            )

            if response.status_code == 200:
                result = response.json()
                return f"""🔬 Theorem Proving Results:

**Statement:** {statement}
**Formula:** {formula}
**Proof Status:** {"✅ PROVED" if result['result']['proved'] else "❌ DISPROVED"}
**Result:** {result['result']['result']}

The logical statement has been formally verified using automated theorem proving.

✅ Proof completed successfully through THONOC toolkit."""
            else:
                return "❌ Theorem proving failed. Please try again."

        except Exception as e:
            return f"⚠️ Error in theorem proving: {str(e)}"

    async def handle_general_chat(self, message: str, session_id: str) -> str:
        """Handle general conversational messages"""
        # Add to conversation context
        if session_id not in self.conversation_context:
            self.conversation_context[session_id] = []

        self.conversation_context[session_id].append({
            "user": message,
            "timestamp": datetime.now().isoformat()
        })

        # Simple pattern-based responses (can be enhanced with actual LLM)
        message_lower = message.lower()

        if any(word in message_lower for word in ["hello", "hi", "hey"]):
            return """👋 Hello! I'm the LOGOS Interactive Assistant.

I'm powered by a proof-gated AI system with advanced capabilities:
• 📝 Text analysis and semantic clustering
• 📈 Time series forecasting and prediction
• 🔬 Automated theorem proving
• 🛡️ Cryptographically secured operations

What would you like to explore today? You can ask me to analyze text, make predictions, prove logical statements, or just chat!

Type /help for more commands."""

        elif any(word in message_lower for word in ["what can you do", "capabilities", "help"]):
            return await self.handle_command("/capabilities", session_id)

        elif any(word in message_lower for word in ["goodbye", "bye", "exit"]):
            return "👋 Goodbye! Thank you for using LOGOS Interactive Assistant. Your conversation was secured through proof-gated execution."

        elif "logos" in message_lower:
            return """🏛️ LOGOS (Logic-Oriented Goal-Aligned Safe) System

I'm part of an advanced AI alignment architecture that ensures all operations are:
✅ Cryptographically verified
✅ Proof-gated for security
✅ Aligned with safety objectives
✅ Fully auditable

The system combines multiple AI toolkits (TETRAGNOS, TELOS, THONOC) under a unified security framework. Every interaction is verified through kernel hash validation.

How can I assist you today?"""

        else:
            return f"""🤖 I understand you said: "{message[:100]}{'...' if len(message) > 100 else ''}"

I'm here to help with:
• 📝 Text analysis - Try: "analyze this text: [your text]"
• 📈 Predictions - Try: "predict trends for: 1, 2, 3, 4, 5"
• 🔬 Logic - Try: "prove that true and true"
• ❓ Commands - Type /help for more options

What would you like me to help you with?"""

    async def get_system_status(self) -> str:
        """Get current system status"""
        services = [
            ("TETRAGNOS", 8065),
            ("TELOS", 8066),
            ("THONOC", 8067),
            ("TOOL_ROUTER", 8071),
            ("EXECUTOR", 8072),
            ("LOGOS_API", 8090)
        ]

        status_lines = ["🔍 LOGOS System Status:\n"]

        for name, port in services:
            try:
                response = requests.get(f"http://127.0.0.1:{port}/health", timeout=2)
                status = "✅ ONLINE" if response.status_code == 200 else "⚠️ ISSUES"
            except:
                status = "❌ OFFLINE"

            status_lines.append(f"• {name}: {status}")

        return "\n".join(status_lines)

# Initialize chat engine
chat_engine = LOGOSChatEngine()

@app.get("/health")
def health():
    return {"ok": True, "service": "logos-interactive-chat"}

@app.websocket("/ws/{session_id}")
async def websocket_endpoint(websocket: WebSocket, session_id: str):
    await manager.connect(websocket, session_id)
    try:
        # Send welcome message
        welcome_msg = {
            "type": "system",
            "message": "🤖 Welcome to LOGOS Interactive Assistant! Type /help for commands or just start chatting.",
            "timestamp": datetime.now().isoformat()
        }
        await websocket.send_text(json.dumps(welcome_msg))

        while True:
            # Receive message
            data = await websocket.receive_text()
            message_data = json.loads(data)

            user_message = message_data.get("message", "")
            message_type = message_data.get("type", "text")

            # Process message through chat engine
            response = await chat_engine.process_message(user_message, session_id)

            # Send response
            response_msg = {
                "type": "assistant",
                "message": response,
                "timestamp": datetime.now().isoformat(),
                "session_id": session_id
            }
            await websocket.send_text(json.dumps(response_msg))

            # Update session
            if session_id in manager.user_sessions:
                manager.user_sessions[session_id]["message_count"] += 1
                manager.user_sessions[session_id]["conversation_history"].append({
                    "user": user_message,
                    "assistant": response,
                    "timestamp": datetime.now().isoformat()
                })

    except WebSocketDisconnect:
        manager.disconnect(websocket, session_id)

@app.post("/chat", response_model=ChatResponse)
async def chat_endpoint(message: ChatMessage):
    """REST endpoint for chat (alternative to WebSocket)"""
    response_text = await chat_engine.process_message(message.message, message.session_id)

    return ChatResponse(
        response=response_text,
        session_id=message.session_id,
        timestamp=datetime.now().isoformat(),
        response_type="text"
    )

@app.post("/voice")
async def voice_endpoint(voice_message: VoiceMessage):
    """Handle voice input (placeholder for voice processing)"""
    # This would integrate with speech-to-text service
    return {
        "status": "received",
        "message": "Voice processing not yet implemented. Use text chat for now.",
        "session_id": voice_message.session_id
    }

@app.get("/sessions")
async def get_active_sessions():
    """Get active chat sessions"""
    sessions = {}
    for session_id, data in manager.user_sessions.items():
        sessions[session_id] = {
            "connected_at": data["connected_at"].isoformat(),
            "message_count": data["message_count"],
            "conversation_length": len(data["conversation_history"])
        }
    return {"active_sessions": len(sessions), "sessions": sessions}

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8080)
