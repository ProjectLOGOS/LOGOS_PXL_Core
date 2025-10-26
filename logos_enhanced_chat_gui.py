#!/usr/bin/env python3
"""
LOGOS Enhanced Chat GUI
GPT-like natural language interface with conversational AI capabilities
"""

from fastapi import FastAPI, WebSocket, WebSocketDisconnect, Request, Form
from fastapi.responses import HTMLResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
import uvicorn
import asyncio
import json
import aiohttp
import uuid
from datetime import datetime
from typing import Dict, List, Optional
import sys
import os

# Add the project root to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.natural_language_processor import NaturalLanguageProcessor

app = FastAPI(title="LOGOS Enhanced Chat Interface", version="2.0.0")

# Initialize the natural language processor
nlp = NaturalLanguageProcessor()

# WebSocket connection manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: Dict[str, WebSocket] = {}

    async def connect(self, websocket: WebSocket, session_id: str):
        await websocket.accept()
        self.active_connections[session_id] = websocket

    def disconnect(self, session_id: str):
        if session_id in self.active_connections:
            del self.active_connections[session_id]

    async def send_message(self, session_id: str, message: dict):
        if session_id in self.active_connections:
            try:
                await self.active_connections[session_id].send_text(json.dumps(message))
            except:
                self.disconnect(session_id)

manager = ConnectionManager()

# Chat interface HTML template
CHAT_HTML = '''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>LOGOS AGI - Conversational AI</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            height: 100vh;
            display: flex;
            justify-content: center;
            align-items: center;
        }

        .chat-container {
            width: 900px;
            height: 600px;
            background: white;
            border-radius: 20px;
            box-shadow: 0 20px 60px rgba(0,0,0,0.1);
            display: flex;
            flex-direction: column;
            overflow: hidden;
        }

        .chat-header {
            background: linear-gradient(135deg, #4f46e5, #7c3aed);
            color: white;
            padding: 20px;
            text-align: center;
            border-radius: 20px 20px 0 0;
        }

        .chat-header h1 {
            font-size: 1.5rem;
            font-weight: 600;
            margin-bottom: 5px;
        }

        .chat-header p {
            opacity: 0.9;
            font-size: 0.9rem;
        }

        .chat-messages {
            flex: 1;
            overflow-y: auto;
            padding: 20px;
            background: #f8fafc;
        }

        .message {
            margin-bottom: 20px;
            display: flex;
            align-items: flex-start;
        }

        .message.user {
            flex-direction: row-reverse;
        }

        .message-content {
            max-width: 70%;
            padding: 15px 20px;
            border-radius: 18px;
            position: relative;
            font-size: 0.95rem;
            line-height: 1.5;
        }

        .message.user .message-content {
            background: #4f46e5;
            color: white;
            border-bottom-right-radius: 4px;
            margin-right: 10px;
        }

        .message.assistant .message-content {
            background: white;
            color: #374151;
            border: 1px solid #e5e7eb;
            border-bottom-left-radius: 4px;
            margin-left: 50px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.05);
        }

        .message-avatar {
            width: 40px;
            height: 40px;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            font-weight: bold;
            font-size: 0.8rem;
        }

        .message.user .message-avatar {
            background: #1f2937;
            color: white;
        }

        .message.assistant .message-avatar {
            background: linear-gradient(135deg, #4f46e5, #7c3aed);
            color: white;
            position: absolute;
            left: 20px;
        }

        .chat-input-container {
            padding: 20px;
            background: white;
            border-top: 1px solid #e5e7eb;
        }

        .chat-input-wrapper {
            display: flex;
            gap: 10px;
            align-items: flex-end;
        }

        .chat-input {
            flex: 1;
            padding: 15px 20px;
            border: 2px solid #e5e7eb;
            border-radius: 25px;
            outline: none;
            font-size: 0.95rem;
            resize: none;
            min-height: 20px;
            max-height: 100px;
            font-family: inherit;
            transition: border-color 0.2s;
        }

        .chat-input:focus {
            border-color: #4f46e5;
        }

        .send-button {
            background: #4f46e5;
            color: white;
            border: none;
            border-radius: 50%;
            width: 50px;
            height: 50px;
            cursor: pointer;
            display: flex;
            align-items: center;
            justify-content: center;
            transition: background-color 0.2s;
            font-size: 1.2rem;
        }

        .send-button:hover:not(:disabled) {
            background: #4338ca;
        }

        .send-button:disabled {
            background: #9ca3af;
            cursor: not-allowed;
        }

        .typing-indicator {
            display: none;
            align-items: center;
            margin: 10px 0;
            margin-left: 50px;
            color: #6b7280;
            font-style: italic;
            font-size: 0.9rem;
        }

        .typing-dots {
            display: inline-block;
            margin-left: 8px;
        }

        .typing-dots span {
            display: inline-block;
            width: 8px;
            height: 8px;
            border-radius: 50%;
            background: #6b7280;
            margin: 0 1px;
            animation: typing 1.4s infinite ease-in-out;
        }

        .typing-dots span:nth-child(1) { animation-delay: -0.32s; }
        .typing-dots span:nth-child(2) { animation-delay: -0.16s; }

        @keyframes typing {
            0%, 80%, 100% {
                transform: scale(0.8);
                opacity: 0.5;
            }
            40% {
                transform: scale(1);
                opacity: 1;
            }
        }

        .status-indicator {
            position: absolute;
            top: 20px;
            right: 20px;
            padding: 8px 15px;
            border-radius: 20px;
            font-size: 0.8rem;
            font-weight: 500;
        }

        .status-connected {
            background: #dcfce7;
            color: #166534;
        }

        .status-disconnected {
            background: #fef2f2;
            color: #dc2626;
        }

        .example-prompts {
            display: flex;
            gap: 10px;
            margin-top: 15px;
            flex-wrap: wrap;
        }

        .example-prompt {
            background: #f3f4f6;
            border: 1px solid #d1d5db;
            padding: 8px 15px;
            border-radius: 20px;
            font-size: 0.85rem;
            cursor: pointer;
            transition: all 0.2s;
        }

        .example-prompt:hover {
            background: #e5e7eb;
            border-color: #9ca3af;
        }

        @media (max-width: 768px) {
            .chat-container {
                width: 100%;
                height: 100vh;
                border-radius: 0;
            }

            .message-content {
                max-width: 85%;
            }
        }
    </style>
</head>
<body>
    <div class="chat-container">
        <div class="chat-header">
            <div class="status-indicator status-disconnected" id="status">Connecting...</div>
            <h1>🧠 LOGOS AGI</h1>
            <p>Advanced Conversational AI for Logic & Reasoning</p>
        </div>

        <div class="chat-messages" id="messages">
            <div class="message assistant">
                <div class="message-avatar">🧠</div>
                <div class="message-content">
                    Hello! I'm LOGOS, your AI reasoning assistant. I can help with logical analysis, modal logic, formal verification, and test whether statements are falsifiable.
                    <br><br>
                    What would you like to explore today?
                    <div class="example-prompts">
                        <div class="example-prompt" onclick="sendExample('Is the statement □(P → Q) ∧ ◊P ∧ ¬◊Q falsifiable?')">Test Falsifiability</div>
                        <div class="example-prompt" onclick="sendExample('What is the relationship between necessity and possibility in modal logic?')">Modal Logic Question</div>
                        <div class="example-prompt" onclick="sendExample('Can you explain how logical proofs work?')">Explain Proofs</div>
                    </div>
                </div>
            </div>
        </div>

        <div class="typing-indicator" id="typing">
            LOGOS is thinking
            <div class="typing-dots">
                <span></span>
                <span></span>
                <span></span>
            </div>
        </div>

        <div class="chat-input-container">
            <div class="chat-input-wrapper">
                <textarea
                    class="chat-input"
                    id="messageInput"
                    placeholder="Ask me about logic, reasoning, or test if a statement is falsifiable..."
                    rows="1"
                ></textarea>
                <button class="send-button" id="sendButton" onclick="sendMessage()">
                    ➤
                </button>
            </div>
        </div>
    </div>

    <script>
        let ws = null;
        let sessionId = generateUUID();

        function generateUUID() {
            return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
                const r = Math.random() * 16 | 0;
                const v = c == 'x' ? r : (r & 0x3 | 0x8);
                return v.toString(16);
            });
        }

        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            ws = new WebSocket(`${protocol}//${window.location.host}/ws/${sessionId}`);

            ws.onopen = function(event) {
                document.getElementById('status').textContent = 'Connected';
                document.getElementById('status').className = 'status-indicator status-connected';
            };

            ws.onmessage = function(event) {
                const data = JSON.parse(event.data);
                handleIncomingMessage(data);
            };

            ws.onclose = function(event) {
                document.getElementById('status').textContent = 'Disconnected';
                document.getElementById('status').className = 'status-indicator status-disconnected';
                // Attempt to reconnect after 3 seconds
                setTimeout(connectWebSocket, 3000);
            };

            ws.onerror = function(error) {
                console.log('WebSocket error:', error);
            };
        }

        function handleIncomingMessage(data) {
            const messagesContainer = document.getElementById('messages');
            const typing = document.getElementById('typing');

            if (data.type === 'response') {
                // Hide typing indicator
                typing.style.display = 'none';

                // Add assistant message
                const messageDiv = document.createElement('div');
                messageDiv.className = 'message assistant';
                messageDiv.innerHTML = `
                    <div class="message-avatar">🧠</div>
                    <div class="message-content">${formatMessage(data.content)}</div>
                `;
                messagesContainer.appendChild(messageDiv);
                messagesContainer.scrollTop = messagesContainer.scrollHeight;

                // Re-enable send button
                document.getElementById('sendButton').disabled = false;
            } else if (data.type === 'thinking') {
                // Show typing indicator
                typing.style.display = 'flex';
            }
        }

        function formatMessage(content) {
            // Convert newlines to <br> and preserve formatting
            return content
                .replace(/\\n/g, '<br>')
                .replace(/\\*\\*(.*?)\\*\\*/g, '<strong>$1</strong>')
                .replace(/\\*(.*?)\\*/g, '<em>$1</em>')
                .replace(/`(.*?)`/g, '<code style="background: #f3f4f6; padding: 2px 6px; border-radius: 4px; font-family: monospace;">$1</code>');
        }

        function sendMessage() {
            const input = document.getElementById('messageInput');
            const message = input.value.trim();

            if (message && ws && ws.readyState === WebSocket.OPEN) {
                // Add user message to chat
                addUserMessage(message);

                // Send to backend
                ws.send(JSON.stringify({
                    type: 'message',
                    content: message,
                    timestamp: new Date().toISOString()
                }));

                // Clear input and disable send button
                input.value = '';
                document.getElementById('sendButton').disabled = true;

                // Show thinking indicator
                document.getElementById('typing').style.display = 'flex';

                // Auto-resize textarea
                input.style.height = 'auto';
            }
        }

        function sendExample(exampleText) {
            document.getElementById('messageInput').value = exampleText;
            sendMessage();
        }

        function addUserMessage(message) {
            const messagesContainer = document.getElementById('messages');
            const messageDiv = document.createElement('div');
            messageDiv.className = 'message user';
            messageDiv.innerHTML = `
                <div class="message-avatar">U</div>
                <div class="message-content">${message}</div>
            `;
            messagesContainer.appendChild(messageDiv);
            messagesContainer.scrollTop = messagesContainer.scrollHeight;
        }

        // Auto-resize textarea
        document.getElementById('messageInput').addEventListener('input', function() {
            this.style.height = 'auto';
            this.style.height = Math.min(this.scrollHeight, 100) + 'px';
        });

        // Send message on Enter (but not Shift+Enter)
        document.getElementById('messageInput').addEventListener('keypress', function(e) {
            if (e.key === 'Enter' && !e.shiftKey) {
                e.preventDefault();
                sendMessage();
            }
        });

        // Connect on page load
        connectWebSocket();
    </script>
</body>
</html>
'''

@app.get("/", response_class=HTMLResponse)
async def get_chat_interface():
    """Serve the enhanced chat interface"""
    return CHAT_HTML

@app.websocket("/ws/{session_id}")
async def websocket_endpoint(websocket: WebSocket, session_id: str):
    """Handle WebSocket connections for real-time chat"""
    await manager.connect(websocket, session_id)

    # Create session in NLP processor
    nlp.create_session(session_id)

    try:
        while True:
            data = await websocket.receive_text()
            message_data = json.loads(data)

            if message_data.get('type') == 'message':
                # Process the user message
                user_message = message_data.get('content', '')

                # Send thinking indicator
                await manager.send_message(session_id, {
                    'type': 'thinking'
                })

                # Process with natural language processor
                response = await process_user_message(user_message, session_id)

                # Send response
                await manager.send_message(session_id, {
                    'type': 'response',
                    'content': response
                })

    except WebSocketDisconnect:
        manager.disconnect(session_id)

async def process_user_message(message: str, session_id: str) -> str:
    """Process user message and generate appropriate response"""
    message_lower = message.lower()

    try:
        # Handle direct questions about LOGOS itself without API calls
        if any(phrase in message_lower for phrase in ['describe your', 'what are you', 'tell me about you', 'your core', 'your logic']):
            return nlp.generate_contextual_response(message, session_id)

        # Handle capability and help questions directly
        elif any(phrase in message_lower for phrase in ['what can you', 'help me', 'can you do', 'capabilities']):
            return nlp.generate_contextual_response(message, session_id)

        # Handle explanation requests directly
        elif any(phrase in message_lower for phrase in ['explain', 'how does', 'what is', 'tell me about']) and not any(phrase in message_lower for phrase in ['falsifiable', 'countermodel']):
            return nlp.generate_contextual_response(message, session_id)

        # Check if this is a falsifiability query
        elif any(keyword in message_lower for keyword in ['falsifiable', 'countermodel', '□', '◊', 'test']) and any(op in message for op in ['□', '◊', '→', '∧', '∨', '¬', '~']):
            # Extract formula from message (simple heuristic)
            formula = extract_formula_from_message(message)
            if formula:
                # Call LOGOS API for falsifiability analysis
                result = await call_logos_falsifiability_api(formula)
                if result:
                    return nlp.process_falsifiability_result(result, session_id)

        # Check if this is a complex reasoning query that needs API processing
        elif any(keyword in message_lower for keyword in ['prove', 'verify', 'validate', 'check']) or (len(message.split()) > 15 and any(keyword in message_lower for keyword in ['logic', 'reasoning', 'analysis'])):
            # Call LOGOS API for reasoning
            result = await call_logos_reasoning_api(message)
            if result:
                return nlp.process_reasoning_result(result, session_id)

        # Check for system status requests
        elif any(keyword in message_lower for keyword in ['status', 'health', 'system', 'running']):
            result = await call_logos_status_api()
            if result:
                return nlp.process_system_status(result, session_id)

        # Generate contextual response for general conversation
        return nlp.generate_contextual_response(message, session_id)

    except Exception as e:
        print(f"Error processing message: {e}")
        return "I apologize, but I encountered an issue processing your request. Please try rephrasing your question or check if the LOGOS backend services are running properly."

def extract_formula_from_message(message: str) -> Optional[str]:
    """Extract modal logic formula from user message"""
    # Simple pattern matching for common modal logic patterns
    import re

    # Look for formulas with modal operators
    modal_patterns = [
        r'□\([^)]+\)',  # Necessity
        r'◊\([^)]+\)',  # Possibility
        r'[A-Z]\s*→\s*[A-Z]',  # Implications
        r'[A-Z]\s*∧\s*[A-Z]',  # Conjunctions
        r'[A-Z]\s*∨\s*[A-Z]',  # Disjunctions
    ]

    for pattern in modal_patterns:
        matches = re.findall(pattern, message)
        if matches:
            return matches[0]

    # Look for quoted formulas
    quotes_match = re.search(r'["\']([^"\']+)["\']', message)
    if quotes_match:
        return quotes_match.group(1)

    # Look for formulas after "is" or "test"
    formula_match = re.search(r'(?:is|test)\s+(.+?)(?:\s+falsifiable|\?|$)', message, re.IGNORECASE)
    if formula_match:
        return formula_match.group(1).strip()

    return None

async def call_logos_falsifiability_api(formula: str) -> Optional[Dict]:
    """Call LOGOS API for falsifiability analysis"""
    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(
                "http://localhost:8090/api/v1/falsifiability/validate",
                json={
                    "formula": formula,
                    "logic": "K",
                    "generate_countermodel": True
                },
                timeout=30
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    result['formula'] = formula  # Add original formula to result
                    return result
    except Exception as e:
        print(f"Error calling falsifiability API: {e}")
    return None

async def call_logos_reasoning_api(query: str) -> Optional[Dict]:
    """Call LOGOS API for reasoning analysis"""
    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(
                "http://localhost:8090/api/v1/reasoning/query",
                json={"question": query},
                timeout=30
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    result['query'] = query  # Add original query to result
                    return result
    except Exception as e:
        print(f"Error calling reasoning API: {e}")
    return None

async def call_logos_status_api() -> Optional[Dict]:
    """Call LOGOS API for system status"""
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(
                "http://localhost:8090/health",
                timeout=10
            ) as response:
                if response.status == 200:
                    return await response.json()
    except Exception as e:
        print(f"Error calling status API: {e}")
    return None

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {
        "status": "healthy",
        "service": "LOGOS Enhanced Chat GUI",
        "version": "2.0.0",
        "timestamp": datetime.now().isoformat()
    }

if __name__ == "__main__":
    print("🧠 LOGOS Enhanced Chat Interface")
    print("=" * 50)
    print("Starting GPT-like conversational AI interface...")
    print("URL: http://localhost:3003")
    print("Features: Natural language processing, Real-time chat, Logic translation")
    print("=" * 50)

    uvicorn.run(
        app,
        host="127.0.0.1",
        port=3003,
        log_level="info"
    )
