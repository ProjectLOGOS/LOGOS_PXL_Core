// LOGOS Trinity Knot GUI - JavaScript
// Phase 2: WebSocket communication, state management, graph visualization

// Configuration
const WS_URL = `ws://${window.location.host}/ws/`;
let websocket = null;
let sessionId = null;
let currentState = 'stasis';

// Initialize on page load
document.addEventListener('DOMContentLoaded', function() {
    // Generate session ID
    sessionId = generateUUID();
    document.getElementById('session-id').textContent = sessionId;

    // Connect WebSocket
    connectWebSocket();

    // Setup event listeners
    setupEventListeners();

    // Fetch system status
    fetchSystemStatus();
});

function generateUUID() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
        const r = Math.random() * 16 | 0;
        const v = c === 'x' ? r : (r & 0x3 | 0x8);
        return v.toString(16);
    });
}

function connectWebSocket() {
    websocket = new WebSocket(WS_URL + sessionId);

    websocket.onopen = function() {
        console.log('WebSocket connected');
        addSystemMessage('Connected to LOGOS Trinity Knot');
    };

    websocket.onmessage = function(event) {
        const data = JSON.parse(event.data);
        handleWebSocketMessage(data);
    };

    websocket.onerror = function(error) {
        console.error('WebSocket error:', error);
        addSystemMessage('Connection error', true);
    };

    websocket.onclose = function() {
        console.log('WebSocket closed');
        addSystemMessage('Connection closed', true);
        // Attempt reconnect after 3 seconds
        setTimeout(connectWebSocket, 3000);
    };
}

function handleWebSocketMessage(data) {
    switch(data.type) {
        case 'state_change':
            updateSystemState(data.state);
            break;
        case 'processing':
            addSystemMessage(data.message);
            break;
        case 'response':
            addAssistantMessage(data.content);
            break;
        case 'graph_visualization':
            renderGraph(data.data);
            break;
        case 'voice_listening':
            showVoiceDialog();
            break;
        case 'voice_transcribed':
            hideVoiceDialog();
            addUserMessage(`🎤 ${data.text}`);
            break;
        case 'voice_error':
            hideVoiceDialog();
            addSystemMessage(data.message, true);
            break;
        case 'file_processed':
            hideFileDialog();
            addAssistantMessage(data.analysis);
            break;
        case 'error':
            addSystemMessage(data.message, true);
            break;
        case 'pong':
            // Keep-alive response
            break;
    }
}

function updateSystemState(state) {
    currentState = state;
    const statusEl = document.getElementById('system-status');
    const knotEl = document.getElementById('trinity-knot');
    const labelEl = document.getElementById('state-label');

    // Update status indicator
    statusEl.className = `status-indicator ${state}`;
    statusEl.textContent = state.charAt(0).toUpperCase() + state.slice(1);

    // Update knot animation
    knotEl.className = `trinity-knot knot-${state}`;

    // Update state label
    const labels = {
        'listening': 'Listening for voice input...',
        'processing': 'Processing your request...',
        'speaking': 'Delivering response...',
        'stasis': 'Awaiting input'
    };
    labelEl.textContent = labels[state] || 'Unknown State';
}

function setupEventListeners() {
    // Send button
    document.getElementById('send-btn').addEventListener('click', sendMessage);

    // Enter key to send
    document.getElementById('chat-input').addEventListener('keydown', function(e) {
        if (e.key === 'Enter' && !e.shiftKey) {
            e.preventDefault();
            sendMessage();
        }
    });

    // Voice button
    document.getElementById('voice-btn').addEventListener('click', startVoiceInput);
    document.getElementById('voice-cancel-btn').addEventListener('click', hideVoiceDialog);

    // File upload button
    document.getElementById('file-btn').addEventListener('click', showFileDialog);
    document.getElementById('upload-cancel-btn').addEventListener('click', hideFileDialog);
    document.getElementById('upload-confirm-btn').addEventListener('click', uploadFile);

    // File drop zone
    const dropZone = document.getElementById('file-drop-zone');
    dropZone.addEventListener('click', () => document.getElementById('file-input').click());
    dropZone.addEventListener('dragover', (e) => {
        e.preventDefault();
        dropZone.style.background = 'rgba(127, 219, 255, 0.2)';
    });
    dropZone.addEventListener('dragleave', () => {
        dropZone.style.background = '';
    });
    dropZone.addEventListener('drop', handleFileDrop);

    // Audit log link
    document.getElementById('view-audit').addEventListener('click', viewAuditLog);

    // Keep-alive ping
    setInterval(() => {
        if (websocket && websocket.readyState === WebSocket.OPEN) {
            websocket.send(JSON.stringify({type: 'ping'}));
        }
    }, 30000);
}

function sendMessage() {
    const input = document.getElementById('chat-input');
    const query = input.value.trim();

    if (!query || !websocket) return;

    // Add user message to chat
    addUserMessage(query);

    // Send to server
    websocket.send(JSON.stringify({
        type: 'query',
        query: query
    }));

    // Clear input
    input.value = '';
}

function startVoiceInput() {
    if (!websocket) return;

    websocket.send(JSON.stringify({
        type: 'voice_start',
        duration: 5
    }));
}

function showFileDialog() {
    document.getElementById('file-dialog').classList.remove('hidden');
}

function hideFileDialog() {
    document.getElementById('file-dialog').classList.add('hidden');
}

function showVoiceDialog() {
    document.getElementById('voice-dialog').classList.remove('hidden');
}

function hideVoiceDialog() {
    document.getElementById('voice-dialog').classList.add('hidden');
}

function handleFileDrop(e) {
    e.preventDefault();
    const files = e.dataTransfer.files;
    if (files.length > 0) {
        document.getElementById('file-input').files = files;
    }
}

async function uploadFile() {
    const fileInput = document.getElementById('file-input');
    const file = fileInput.files[0];

    if (!file) {
        alert('Please select a file');
        return;
    }

    // Check file size (10MB)
    if (file.size > 10 * 1024 * 1024) {
        alert(`File too large: ${(file.size / (1024*1024)).toFixed(2)}MB > 10MB`);
        return;
    }

    // Upload via HTTP POST
    const formData = new FormData();
    formData.append('file', file);

    try {
        const response = await fetch('/api/upload', {
            method: 'POST',
            body: formData
        });

        if (response.ok) {
            const result = await response.json();
            hideFileDialog();

            // Send file path via WebSocket for processing
            websocket.send(JSON.stringify({
                type: 'file_upload',
                file_path: result.path
            }));
        } else {
            const error = await response.json();
            alert(`Upload failed: ${error.detail}`);
        }
    } catch (error) {
        alert(`Upload error: ${error.message}`);
    }
}

function addUserMessage(content) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message user';
    messageEl.textContent = content;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function addAssistantMessage(content) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message assistant';
    messageEl.textContent = content;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function addSystemMessage(content, isError = false) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message assistant';
    messageEl.style.opacity = '0.7';
    messageEl.style.fontStyle = 'italic';
    if (isError) messageEl.style.color = '#ff4136';
    messageEl.textContent = `[System] ${content}`;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function renderGraph(graphData) {
    const container = document.getElementById('graph-container');
    container.innerHTML = ''; // Clear previous graph

    if (!graphData || !graphData.nodes) {
        container.textContent = 'No graph data available';
        return;
    }

    // Use D3.js to render graph
    const width = container.clientWidth;
    const height = container.clientHeight || 350;

    const svg = d3.select('#graph-container')
        .append('svg')
        .attr('width', width)
        .attr('height', height);

    // Create force simulation
    const simulation = d3.forceSimulation(graphData.nodes)
        .force('link', d3.forceLink(graphData.edges).id(d => d.id).distance(100))
        .force('charge', d3.forceManyBody().strength(-300))
        .force('center', d3.forceCenter(width / 2, height / 2));

    // Draw edges
    const link = svg.append('g')
        .selectAll('line')
        .data(graphData.edges)
        .enter().append('line')
        .attr('stroke', '#7fdbff')
        .attr('stroke-width', 2);

    // Draw nodes
    const node = svg.append('g')
        .selectAll('circle')
        .data(graphData.nodes)
        .enter().append('circle')
        .attr('r', 20)
        .attr('fill', '#001f3f')
        .attr('stroke', '#7fdbff')
        .attr('stroke-width', 3)
        .call(d3.drag()
            .on('start', dragstarted)
            .on('drag', dragged)
            .on('end', dragended));

    // Add labels
    const label = svg.append('g')
        .selectAll('text')
        .data(graphData.nodes)
        .enter().append('text')
        .text(d => d.label || d.id)
        .attr('font-size', 12)
        .attr('fill', '#ffffff')
        .attr('text-anchor', 'middle')
        .attr('dy', 4);

    // Update positions on tick
    simulation.on('tick', () => {
        link
            .attr('x1', d => d.source.x)
            .attr('y1', d => d.source.y)
            .attr('x2', d => d.target.x)
            .attr('y2', d => d.target.y);

        node
            .attr('cx', d => d.x)
            .attr('cy', d => d.y);

        label
            .attr('x', d => d.x)
            .attr('y', d => d.y);
    });

    function dragstarted(event, d) {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        d.fx = d.x;
        d.fy = d.y;
    }

    function dragged(event, d) {
        d.fx = event.x;
        d.fy = event.y;
    }

    function dragended(event, d) {
        if (!event.active) simulation.alphaTarget(0);
        d.fx = null;
        d.fy = null;
    }

    // Display graph analysis
    if (graphData.analysis) {
        const analysisDiv = document.getElementById('graph-analysis');
        analysisDiv.innerHTML = `
            <strong>Graph Analysis:</strong><br>
            Nodes: ${graphData.analysis.num_nodes}<br>
            Edges: ${graphData.analysis.num_edges}<br>
            Density: ${(graphData.analysis.density || 0).toFixed(3)}<br>
            Connected: ${graphData.analysis.is_connected ? 'Yes' : 'No'}
        `;
    }
}

async function fetchSystemStatus() {
    try {
        const response = await fetch('/health');
        const data = await response.json();

        document.getElementById('library-count').textContent =
            `Libraries: ${data.libraries_loaded}/${data.total_libraries}`;
    } catch (error) {
        console.error('Failed to fetch system status:', error);
    }
}

async function viewAuditLog(e) {
    e.preventDefault();

    try {
        const response = await fetch(`/api/audit/log/${sessionId}`);
        const data = await response.json();

        const logWindow = window.open('', 'Audit Log', 'width=800,height=600');
        logWindow.document.write('<html><head><title>Audit Log</title></head><body>');
        logWindow.document.write('<h2>Session Audit Log</h2>');
        logWindow.document.write(`<p>Session ID: ${data.session_id}</p>`);
        logWindow.document.write(`<p>Created: ${data.created}</p>`);
        logWindow.document.write('<pre>' + JSON.stringify(data.audit_log, null, 2) + '</pre>');
        logWindow.document.write('</body></html>');
    } catch (error) {
        alert(`Failed to load audit log: ${error.message}`);
    }
}
