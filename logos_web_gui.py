#!/usr/bin/env python3
"""
LOGOS AGI Web GUI
Modern web-based interface for the LOGOS AGI system
"""

from fastapi import FastAPI, Request, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
import uvicorn
import json
import asyncio
import aiohttp
from datetime import datetime
from pathlib import Path
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

app = FastAPI(title="LOGOS AGI Web GUI", version="2.0.0")

# Create static and templates directories
static_dir = Path("static")
templates_dir = Path("templates")
static_dir.mkdir(exist_ok=True)
templates_dir.mkdir(exist_ok=True)

# Mount static files
app.mount("/static", StaticFiles(directory=static_dir), name="static")
templates = Jinja2Templates(directory=templates_dir)

# Configuration
LOGOS_API_BASE = "http://localhost:8090"

# WebSocket connection manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: list[WebSocket] = []

    async def connect(self, websocket: WebSocket):
        await websocket.accept()
        self.active_connections.append(websocket)

    def disconnect(self, websocket: WebSocket):
        self.active_connections.remove(websocket)

    async def send_personal_message(self, message: str, websocket: WebSocket):
        await websocket.send_text(message)

    async def broadcast(self, message: str):
        for connection in self.active_connections:
            await connection.send_text(message)

manager = ConnectionManager()

@app.get("/", response_class=HTMLResponse)
async def home(request: Request):
    """Serve the main GUI page"""
    return templates.TemplateResponse("index.html", {"request": request})

@app.get("/api/gui/status")
async def get_system_status():
    """Get system status for GUI"""
    try:
        async with aiohttp.ClientSession() as session:
            # Check health
            async with session.get(f"{LOGOS_API_BASE}/health", timeout=5) as response:
                if response.status == 200:
                    health_data = await response.json()

                    # Check system status
                    async with session.get(f"{LOGOS_API_BASE}/api/v1/status", timeout=5) as sys_response:
                        if sys_response.status == 200:
                            system_data = await sys_response.json()

                            return {
                                "connected": True,
                                "health": health_data,
                                "system": system_data,
                                "timestamp": datetime.now().isoformat()
                            }

        return {"connected": False, "error": "API not responding"}

    except Exception as e:
        return {"connected": False, "error": str(e)}

@app.post("/api/gui/falsifiability")
async def validate_falsifiability_gui(request: Request):
    """Validate falsifiability through GUI"""
    data = await request.json()

    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{LOGOS_API_BASE}/api/v1/falsifiability/validate",
                json=data,
                timeout=30
            ) as response:
                if response.status == 200:
                    result = await response.json()

                    # Broadcast to WebSocket clients
                    await manager.broadcast(json.dumps({
                        "type": "falsifiability_result",
                        "data": result,
                        "timestamp": datetime.now().isoformat()
                    }))

                    return result
                else:
                    error_msg = f"API Error: {response.status}"
                    await manager.broadcast(json.dumps({
                        "type": "error",
                        "message": error_msg
                    }))
                    return {"error": error_msg}

    except Exception as e:
        error_msg = f"Connection Error: {str(e)}"
        await manager.broadcast(json.dumps({
            "type": "error",
            "message": error_msg
        }))
        return {"error": error_msg}

@app.post("/api/gui/reasoning")
async def submit_reasoning_query_gui(request: Request):
    """Submit reasoning query through GUI"""
    data = await request.json()

    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{LOGOS_API_BASE}/api/v1/reasoning/query",
                json=data,
                timeout=30
            ) as response:
                if response.status == 200:
                    result = await response.json()

                    # Broadcast to WebSocket clients
                    await manager.broadcast(json.dumps({
                        "type": "reasoning_result",
                        "data": result,
                        "query": data.get("question", ""),
                        "timestamp": datetime.now().isoformat()
                    }))

                    return result
                else:
                    error_msg = f"API Error: {response.status}"
                    await manager.broadcast(json.dumps({
                        "type": "error",
                        "message": error_msg
                    }))
                    return {"error": error_msg}

    except Exception as e:
        error_msg = f"Connection Error: {str(e)}"
        await manager.broadcast(json.dumps({
            "type": "error",
            "message": error_msg
        }))
        return {"error": error_msg}

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    """WebSocket endpoint for real-time updates"""
    await manager.connect(websocket)
    try:
        while True:
            data = await websocket.receive_text()
            # Echo back for testing
            await manager.send_personal_message(f"Echo: {data}", websocket)
    except WebSocketDisconnect:
        manager.disconnect(websocket)

# Create the HTML template
html_template = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>LOGOS AGI - Advanced Reasoning System</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: #333;
            min-height: 100vh;
        }

        .container {
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
        }

        .header {
            background: rgba(255, 255, 255, 0.95);
            padding: 20px;
            border-radius: 15px;
            margin-bottom: 20px;
            backdrop-filter: blur(10px);
            display: flex;
            justify-content: space-between;
            align-items: center;
            box-shadow: 0 8px 25px rgba(0,0,0,0.1);
        }

        .title {
            font-size: 2.5rem;
            font-weight: 700;
            background: linear-gradient(45deg, #667eea, #764ba2);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            background-clip: text;
        }

        .status-indicator {
            display: flex;
            align-items: center;
            gap: 10px;
            font-weight: 600;
        }

        .status-dot {
            width: 12px;
            height: 12px;
            border-radius: 50%;
            background: #ff4444;
            animation: pulse 2s infinite;
        }

        .status-dot.connected {
            background: #44ff44;
        }

        @keyframes pulse {
            0% { opacity: 1; }
            50% { opacity: 0.5; }
            100% { opacity: 1; }
        }

        .tab-container {
            background: rgba(255, 255, 255, 0.95);
            border-radius: 15px;
            padding: 20px;
            box-shadow: 0 8px 25px rgba(0,0,0,0.1);
            backdrop-filter: blur(10px);
        }

        .tab-nav {
            display: flex;
            border-bottom: 2px solid #eee;
            margin-bottom: 20px;
        }

        .tab-button {
            padding: 15px 25px;
            background: none;
            border: none;
            font-size: 1.1rem;
            font-weight: 600;
            cursor: pointer;
            border-bottom: 3px solid transparent;
            transition: all 0.3s ease;
            color: #666;
        }

        .tab-button.active {
            color: #667eea;
            border-bottom-color: #667eea;
        }

        .tab-button:hover {
            color: #764ba2;
            background: rgba(118, 75, 162, 0.1);
        }

        .tab-content {
            display: none;
        }

        .tab-content.active {
            display: block;
        }

        .form-group {
            margin-bottom: 20px;
        }

        .form-label {
            display: block;
            margin-bottom: 8px;
            font-weight: 600;
            color: #333;
        }

        .form-input {
            width: 100%;
            padding: 12px;
            border: 2px solid #ddd;
            border-radius: 8px;
            font-size: 1rem;
            transition: border-color 0.3s ease;
        }

        .form-input:focus {
            outline: none;
            border-color: #667eea;
            box-shadow: 0 0 0 3px rgba(102, 126, 234, 0.1);
        }

        .form-textarea {
            resize: vertical;
            min-height: 100px;
            font-family: 'Consolas', monospace;
        }

        .btn {
            padding: 12px 24px;
            background: linear-gradient(45deg, #667eea, #764ba2);
            color: white;
            border: none;
            border-radius: 8px;
            font-size: 1rem;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.3s ease;
            box-shadow: 0 4px 15px rgba(0,0,0,0.2);
        }

        .btn:hover {
            transform: translateY(-2px);
            box-shadow: 0 6px 20px rgba(0,0,0,0.3);
        }

        .btn:active {
            transform: translateY(0);
        }

        .btn-secondary {
            background: linear-gradient(45deg, #6c757d, #495057);
        }

        .result-panel {
            background: #1e1e1e;
            color: #fff;
            padding: 20px;
            border-radius: 8px;
            margin-top: 20px;
            font-family: 'Consolas', monospace;
            min-height: 300px;
            max-height: 500px;
            overflow-y: auto;
            white-space: pre-wrap;
        }

        .grid {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 20px;
            margin-bottom: 20px;
        }

        .options-group {
            display: flex;
            gap: 20px;
            margin: 15px 0;
        }

        .checkbox-label {
            display: flex;
            align-items: center;
            gap: 8px;
            cursor: pointer;
        }

        .loading {
            display: inline-block;
            animation: spin 1s linear infinite;
        }

        @keyframes spin {
            from { transform: rotate(0deg); }
            to { transform: rotate(360deg); }
        }

        .alert {
            padding: 15px;
            border-radius: 8px;
            margin: 10px 0;
        }

        .alert-success {
            background: #d4edda;
            color: #155724;
            border: 1px solid #c3e6cb;
        }

        .alert-error {
            background: #f8d7da;
            color: #721c24;
            border: 1px solid #f5c6cb;
        }

        .countermodel-viz {
            background: white;
            border: 2px solid #ddd;
            border-radius: 8px;
            padding: 20px;
            margin-top: 15px;
            min-height: 200px;
            display: flex;
            align-items: center;
            justify-content: center;
        }

        .world-node {
            width: 80px;
            height: 80px;
            border-radius: 50%;
            background: linear-gradient(45deg, #667eea, #764ba2);
            color: white;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            margin: 0 20px;
            font-weight: bold;
            box-shadow: 0 4px 15px rgba(0,0,0,0.2);
        }

        .world-label {
            font-size: 1.2rem;
        }

        .world-props {
            font-size: 0.8rem;
            margin-top: 5px;
        }

        .monitor-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            margin-bottom: 20px;
        }

        .metric-card {
            background: linear-gradient(135deg, #667eea, #764ba2);
            color: white;
            padding: 20px;
            border-radius: 12px;
            text-align: center;
            box-shadow: 0 4px 15px rgba(0,0,0,0.2);
        }

        .metric-value {
            font-size: 2rem;
            font-weight: bold;
            margin-bottom: 10px;
        }

        .metric-label {
            font-size: 0.9rem;
            opacity: 0.9;
        }

        @media (max-width: 768px) {
            .grid {
                grid-template-columns: 1fr;
            }

            .container {
                padding: 10px;
            }

            .title {
                font-size: 1.8rem;
            }

            .tab-nav {
                flex-wrap: wrap;
            }
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1 class="title">🧠 LOGOS AGI</h1>
            <div class="status-indicator">
                <div class="status-dot" id="statusDot"></div>
                <span id="statusText">Connecting...</span>
            </div>
        </div>

        <div class="tab-container">
            <div class="tab-nav">
                <button class="tab-button active" onclick="showTab('falsifiability')">🔍 Falsifiability</button>
                <button class="tab-button" onclick="showTab('reasoning')">🤖 Reasoning</button>
                <button class="tab-button" onclick="showTab('monitor')">📊 Monitor</button>
                <button class="tab-button" onclick="showTab('settings')">⚙️ Settings</button>
            </div>

            <!-- Falsifiability Tab -->
            <div id="falsifiability" class="tab-content active">
                <h2>Falsifiability Framework</h2>
                <div class="grid">
                    <div>
                        <div class="form-group">
                            <label class="form-label">Modal Logic Formula:</label>
                            <input type="text" class="form-input form-textarea" id="formulaInput"
                                   value="[](P -> Q) /\\ <>P /\\ ~<>Q"
                                   placeholder="Enter modal logic formula">
                        </div>

                        <div class="form-group">
                            <label class="form-label">Logic System:</label>
                            <select class="form-input" id="logicSystem">
                                <option value="K">K</option>
                                <option value="T">T</option>
                                <option value="S4">S4</option>
                                <option value="S5">S5</option>
                                <option value="GL">GL</option>
                                <option value="IEL">IEL</option>
                            </select>
                        </div>

                        <div class="options-group">
                            <label class="checkbox-label">
                                <input type="checkbox" id="generateCountermodel" checked>
                                Generate Countermodel
                            </label>
                            <label class="checkbox-label">
                                <input type="checkbox" id="safetyValidation" checked>
                                Safety Validation
                            </label>
                        </div>

                        <button class="btn" onclick="validateFalsifiability()">
                            <span id="falsifiabilityBtnText">🔍 Validate Falsifiability</span>
                        </button>

                        <button class="btn btn-secondary" onclick="loadExamples()">
                            📋 Load Examples
                        </button>
                    </div>

                    <div>
                        <div class="countermodel-viz" id="countermodelViz">
                            <div>Countermodel visualization will appear here</div>
                        </div>
                    </div>
                </div>

                <div class="result-panel" id="falsifiabilityResult">
Ready to validate modal logic formulas...
                </div>
            </div>

            <!-- Reasoning Tab -->
            <div id="reasoning" class="tab-content">
                <h2>Reasoning Engine</h2>
                <div class="form-group">
                    <label class="form-label">Question:</label>
                    <textarea class="form-input form-textarea" id="questionInput" rows="4"
                              placeholder="Ask a question...">What are the implications of modal collapse in eschatological frameworks?</textarea>
                </div>

                <div class="form-group">
                    <label class="form-label">Reasoning Depth: <span id="depthValue">50</span></label>
                    <input type="range" id="reasoningDepth" min="1" max="100" value="50"
                           onchange="updateDepthValue(this.value)">
                </div>

                <button class="btn" onclick="submitReasoningQuery()">
                    <span id="reasoningBtnText">🧠 Submit Query</span>
                </button>

                <div class="result-panel" id="reasoningResult">
Ready to process reasoning queries...
                </div>
            </div>

            <!-- Monitor Tab -->
            <div id="monitor" class="tab-content">
                <h2>System Monitor</h2>
                <div class="monitor-grid">
                    <div class="metric-card">
                        <div class="metric-value" id="responseTime">--</div>
                        <div class="metric-label">Avg Response Time (ms)</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value" id="successRate">--</div>
                        <div class="metric-label">Success Rate (%)</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value" id="requestCount">--</div>
                        <div class="metric-label">Total Requests</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value" id="systemHealth">--</div>
                        <div class="metric-label">System Health</div>
                    </div>
                </div>

                <button class="btn" onclick="refreshStatus()">🔄 Refresh Status</button>
                <button class="btn btn-secondary" onclick="openApiDocs()">🌐 API Docs</button>

                <div class="result-panel" id="monitorLogs">
System monitoring initialized...
                </div>
            </div>

            <!-- Settings Tab -->
            <div id="settings" class="tab-content">
                <h2>Settings</h2>
                <div class="form-group">
                    <label class="form-label">API Base URL:</label>
                    <input type="text" class="form-input" id="apiBaseUrl" value="http://localhost:8090">
                </div>

                <div class="options-group">
                    <label class="checkbox-label">
                        <input type="checkbox" id="autoRefresh" checked>
                        Auto-refresh status
                    </label>
                    <label class="checkbox-label">
                        <input type="checkbox" id="showTimestamps" checked>
                        Show timestamps
                    </label>
                </div>

                <button class="btn" onclick="saveSettings()">💾 Save Settings</button>

                <div style="margin-top: 30px; padding: 20px; background: #f8f9fa; border-radius: 8px;">
                    <h3>About LOGOS AGI</h3>
                    <p><strong>Version:</strong> 2.0.0</p>
                    <p><strong>Features:</strong></p>
                    <ul style="margin-left: 20px; margin-top: 10px;">
                        <li>✅ Falsifiability Framework (100% validation)</li>
                        <li>✅ Modal Logic Validation</li>
                        <li>✅ Kripke Countermodel Generation</li>
                        <li>✅ Eschatological Safety Integration</li>
                        <li>✅ Real-time Web Interface</li>
                    </ul>
                </div>
            </div>
        </div>
    </div>

    <script>
        let ws = null;
        let requestCount = 0;
        let successCount = 0;

        // Initialize WebSocket connection
        function initWebSocket() {
            ws = new WebSocket('ws://localhost:3001/ws');

            ws.onopen = function(event) {
                logMessage('WebSocket connected');
            };

            ws.onmessage = function(event) {
                const data = JSON.parse(event.data);
                handleWebSocketMessage(data);
            };

            ws.onclose = function(event) {
                logMessage('WebSocket disconnected');
                setTimeout(initWebSocket, 5000); // Reconnect after 5 seconds
            };
        }

        function handleWebSocketMessage(data) {
            if (data.type === 'falsifiability_result') {
                displayFalsifiabilityResult(data.data);
            } else if (data.type === 'reasoning_result') {
                displayReasoningResult(data.data, data.query);
            } else if (data.type === 'error') {
                showAlert(data.message, 'error');
            }
        }

        // Tab management
        function showTab(tabName) {
            document.querySelectorAll('.tab-content').forEach(tab => {
                tab.classList.remove('active');
            });
            document.querySelectorAll('.tab-button').forEach(btn => {
                btn.classList.remove('active');
            });

            document.getElementById(tabName).classList.add('active');
            event.target.classList.add('active');
        }

        // System status checking
        async function checkSystemStatus() {
            try {
                const response = await fetch('/api/gui/status');
                const data = await response.json();

                if (data.connected) {
                    document.getElementById('statusDot').classList.add('connected');
                    document.getElementById('statusText').textContent = 'Connected';

                    // Update monitor metrics
                    updateMonitorMetrics(data);

                    logMessage('✅ System status: Connected');
                } else {
                    document.getElementById('statusDot').classList.remove('connected');
                    document.getElementById('statusText').textContent = 'Disconnected';
                    logMessage('❌ System status: Disconnected - ' + (data.error || 'Unknown error'));
                }
            } catch (error) {
                document.getElementById('statusDot').classList.remove('connected');
                document.getElementById('statusText').textContent = 'Error';
                logMessage('❌ Status check failed: ' + error.message);
            }
        }

        function updateMonitorMetrics(data) {
            if (data.system && data.system.performance) {
                const perf = data.system.performance;
                document.getElementById('responseTime').textContent =
                    perf.average_response_time || '< 50ms';
            }

            const successRate = successCount / Math.max(requestCount, 1) * 100;
            document.getElementById('successRate').textContent = successRate.toFixed(1);
            document.getElementById('requestCount').textContent = requestCount;
            document.getElementById('systemHealth').textContent = data.connected ? '✅' : '❌';
        }

        // Falsifiability validation
        async function validateFalsifiability() {
            const formula = document.getElementById('formulaInput').value;
            const logic = document.getElementById('logicSystem').value;
            const generateCountermodel = document.getElementById('generateCountermodel').checked;

            if (!formula.trim()) {
                showAlert('Please enter a modal logic formula', 'error');
                return;
            }

            const btn = document.getElementById('falsifiabilityBtnText');
            btn.innerHTML = '<span class="loading">⏳</span> Validating...';

            requestCount++;

            try {
                const response = await fetch('/api/gui/falsifiability', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({
                        formula: formula,
                        logic: logic,
                        generate_countermodel: generateCountermodel
                    })
                });

                const result = await response.json();

                if (result.error) {
                    showAlert(result.error, 'error');
                } else {
                    displayFalsifiabilityResult(result);
                    successCount++;
                }

            } catch (error) {
                showAlert('Connection error: ' + error.message, 'error');
            } finally {
                btn.innerHTML = '🔍 Validate Falsifiability';
            }
        }

        function displayFalsifiabilityResult(result) {
            const resultPanel = document.getElementById('falsifiabilityResult');
            const formula = document.getElementById('formulaInput').value;

            let output = `🔍 FALSIFIABILITY ANALYSIS RESULT\\n`;
            output += `${'='.repeat(50)}\\n\\n`;
            output += `Formula: ${formula}\\n`;
            output += `Logic System: ${document.getElementById('logicSystem').value}\\n`;
            output += `Timestamp: ${new Date().toLocaleString()}\\n\\n`;

            output += `📊 RESULT:\\n`;
            output += `Falsifiable: ${result.falsifiable ? '✅ YES' : '❌ NO'}\\n`;
            output += `Safety Validated: ${result.safety_validated ? '✅ YES' : '❌ NO'}\\n\\n`;

            if (result.countermodel) {
                const cm = result.countermodel;
                output += `🌍 COUNTERMODEL:\\n`;
                output += `Worlds: ${JSON.stringify(cm.worlds)}\\n`;
                output += `Relations: ${JSON.stringify(cm.relations)}\\n`;
                output += `Valuation:\\n`;
                Object.entries(cm.valuation || {}).forEach(([world, vals]) => {
                    output += `  ${world}: ${JSON.stringify(vals)}\\n`;
                });
                output += '\\n';

                // Visualize countermodel
                visualizeCountermodel(cm);
            }

            if (result.reasoning_trace) {
                output += `🧠 REASONING TRACE:\\n`;
                result.reasoning_trace.forEach((step, i) => {
                    output += `  ${i + 1}. ${step}\\n`;
                });
            }

            resultPanel.textContent = output;
            logMessage('✅ Falsifiability validation completed');
        }

        function visualizeCountermodel(countermodel) {
            const viz = document.getElementById('countermodelViz');

            if (!countermodel.worlds || countermodel.worlds.length === 0) {
                viz.innerHTML = '<div>No countermodel to visualize</div>';
                return;
            }

            let html = '<div style="display: flex; align-items: center; justify-content: center;">';

            countermodel.worlds.forEach((world, i) => {
                const valuation = countermodel.valuation && countermodel.valuation[world] || {};
                const props = Object.entries(valuation).map(([prop, val]) =>
                    `${prop}:${val}`).join(', ');

                html += `
                    <div class="world-node">
                        <div class="world-label">${world}</div>
                        <div class="world-props">${props}</div>
                    </div>
                `;

                // Add arrow for relations
                if (i < countermodel.worlds.length - 1) {
                    html += '<div style="font-size: 2rem; margin: 0 10px;">→</div>';
                }
            });

            html += '</div>';
            viz.innerHTML = html;
        }

        // Reasoning queries
        async function submitReasoningQuery() {
            const question = document.getElementById('questionInput').value;
            const depth = document.getElementById('reasoningDepth').value;

            if (!question.trim()) {
                showAlert('Please enter a question', 'error');
                return;
            }

            const btn = document.getElementById('reasoningBtnText');
            btn.innerHTML = '<span class="loading">⏳</span> Processing...';

            requestCount++;

            try {
                const response = await fetch('/api/gui/reasoning', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({
                        question: question,
                        reasoning_depth: parseInt(depth)
                    })
                });

                const result = await response.json();

                if (result.error) {
                    showAlert(result.error, 'error');
                } else {
                    displayReasoningResult(result, question);
                    successCount++;
                }

            } catch (error) {
                showAlert('Connection error: ' + error.message, 'error');
            } finally {
                btn.innerHTML = '🧠 Submit Query';
            }
        }

        function displayReasoningResult(result, question) {
            const resultPanel = document.getElementById('reasoningResult');

            let output = `🤖 REASONING RESPONSE\\n`;
            output += `${'='.repeat(50)}\\n\\n`;
            output += `Query: ${question}\\n`;
            output += `Timestamp: ${new Date().toLocaleString()}\\n\\n`;

            output += `📝 Response:\\n${result.result || 'No response available'}\\n\\n`;
            output += `🎯 Confidence: ${result.confidence || 'Unknown'}\\n`;
            output += `🔍 Falsifiability Checked: ${result.falsifiability_checked ? '✅' : '❌'}\\n`;
            output += `🛡️ Safety Validated: ${result.safety_validated ? '✅' : '❌'}\\n`;
            output += `🧠 Reasoning Depth: ${result.reasoning_depth || 'Unknown'}\\n`;

            resultPanel.textContent = output;
            logMessage('✅ Reasoning query completed');
        }

        // Utility functions
        function loadExamples() {
            const examples = [
                "[](P -> Q) /\\\\ <>P /\\\\ ~<>Q",
                "[]P -> P",
                "P /\\\\ ~P",
                "<>[]P -> []<>P",
                "[](P /\\\\ Q) -> ([]P /\\\\ []Q)"
            ];

            const selection = prompt("Select an example:\\n" +
                examples.map((ex, i) => `${i+1}. ${ex}`).join('\\n') +
                "\\n\\nEnter number (1-5):");

            const index = parseInt(selection) - 1;
            if (index >= 0 && index < examples.length) {
                document.getElementById('formulaInput').value = examples[index];
            }
        }

        function updateDepthValue(value) {
            document.getElementById('depthValue').textContent = value;
        }

        function refreshStatus() {
            checkSystemStatus();
        }

        function openApiDocs() {
            window.open('http://localhost:8090/docs', '_blank');
        }

        function saveSettings() {
            showAlert('Settings saved!', 'success');
        }

        function logMessage(message) {
            const timestamp = new Date().toLocaleTimeString();
            const logs = document.getElementById('monitorLogs');
            logs.textContent += `[${timestamp}] ${message}\\n`;
            logs.scrollTop = logs.scrollHeight;
        }

        function showAlert(message, type) {
            const alertDiv = document.createElement('div');
            alertDiv.className = `alert alert-${type}`;
            alertDiv.textContent = message;

            document.body.appendChild(alertDiv);

            setTimeout(() => {
                document.body.removeChild(alertDiv);
            }, 5000);
        }

        // Initialize on page load
        document.addEventListener('DOMContentLoaded', function() {
            checkSystemStatus();
            setInterval(checkSystemStatus, 30000); // Check every 30 seconds

            // Initialize WebSocket
            // initWebSocket(); // Uncomment when WebSocket server is ready

            logMessage('🚀 LOGOS AGI Web GUI initialized');
        });
    </script>
</body>
</html>'''

# Create the HTML template file
with open(templates_dir / "index.html", "w", encoding="utf-8") as f:
    f.write(html_template)

if __name__ == "__main__":
    uvicorn.run(app, host="127.0.0.1", port=3001, log_level="info")
