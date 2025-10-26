// LOGOS AGI - Trinity Knot Interface JavaScript

let ws = null;
let currentState = 'listening';
const canvas = document.getElementById('trinity-knot');
const ctx = canvas.getContext('2d');

// Initialize
document.addEventListener('DOMContentLoaded', () => {
    connectWebSocket();
    setupEventListeners();
    drawTrinityKnot();
    animateTrinityKnot();
});

// WebSocket Connection
function connectWebSocket() {
    const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const wsUrl = `${protocol}//${window.location.host}/ws`;

    ws = new WebSocket(wsUrl);

    ws.onopen = () => {
        console.log('WebSocket connected');
        updateConnectionStatus(true);
        addSystemMessage('Connected to LOGOS AGI');
    };

    ws.onmessage = (event) => {
        const data = JSON.parse(event.data);
        handleWebSocketMessage(data);
    };

    ws.onerror = (error) => {
        console.error('WebSocket error:', error);
        updateConnectionStatus(false);
    };

    ws.onclose = () => {
        console.log('WebSocket disconnected');
        updateConnectionStatus(false);
        addSystemMessage('Disconnected. Reconnecting...');
        setTimeout(connectWebSocket, 3000);
    };
}

function handleWebSocketMessage(data) {
    switch (data.type) {
        case 'state_change':
            updateState(data.state);
            if (data.libraries) {
                updateLibraryCount(data.libraries);
            }
            break;

        case 'response':
            addLogosMessage(data.data.response);
            break;

        case 'voice_ack':
            addSystemMessage(data.message);
            break;
    }
}

function updateConnectionStatus(connected) {
    const statusEl = document.getElementById('connection-status');
    statusEl.textContent = connected ? 'Connected' : 'Disconnected';
    statusEl.className = connected ? 'connected' : 'disconnected';
}

function updateLibraryCount(libraries) {
    const loaded = Object.values(libraries).filter(v => v).length;
    const total = Object.keys(libraries).length;
    document.getElementById('library-count').textContent = `Libraries: ${loaded}/${total}`;
}

// Event Listeners
function setupEventListeners() {
    const input = document.getElementById('query-input');
    const sendBtn = document.getElementById('send-btn');
    const voiceBtn = document.getElementById('voice-btn');
    const fileUpload = document.getElementById('file-upload');

    // Send message
    sendBtn.addEventListener('click', sendMessage);
    input.addEventListener('keypress', (e) => {
        if (e.key === 'Enter') sendMessage();
    });

    // Voice input
    voiceBtn.addEventListener('click', toggleVoiceInput);

    // File upload
    fileUpload.addEventListener('change', handleFileUpload);
}

function sendMessage() {
    const input = document.getElementById('query-input');
    const text = input.value.trim();

    if (!text || !ws || ws.readyState !== WebSocket.OPEN) return;

    addUserMessage(text);

    ws.send(JSON.stringify({
        type: 'query',
        text: text
    }));

    input.value = '';
}

function toggleVoiceInput() {
    const voiceBtn = document.getElementById('voice-btn');
    const isActive = voiceBtn.classList.contains('active');

    if (isActive) {
        voiceBtn.classList.remove('active');
        addSystemMessage('Voice input stopped');
    } else {
        voiceBtn.classList.add('active');
        addSystemMessage('Voice input active (push-to-talk)');

        if (ws && ws.readyState === WebSocket.OPEN) {
            ws.send(JSON.stringify({
                type: 'voice',
                action: 'start'
            }));
        }
    }
}

async function handleFileUpload(event) {
    const file = event.target.files[0];
    if (!file) return;

    const sizeMB = file.size / (1024 * 1024);
    if (sizeMB > 10) {
        addSystemMessage('File too large (max 10MB)');
        return;
    }

    const formData = new FormData();
    formData.append('file', file);

    try {
        addSystemMessage(`Uploading ${file.name}...`);

        const response = await fetch('/upload', {
            method: 'POST',
            body: formData
        });

        if (response.ok) {
            const data = await response.json();
            addSystemMessage(`File uploaded: ${data.filename} (${data.size_mb}MB)`);
        } else {
            const error = await response.json();
            addSystemMessage(`Upload failed: ${error.detail}`);
        }
    } catch (error) {
        console.error('Upload error:', error);
        addSystemMessage('Upload failed');
    }

    event.target.value = '';
}

// Chat Messages
function addUserMessage(text) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message user';
    messageEl.innerHTML = `
        <div class="message-header">You</div>
        <div class="message-content">${escapeHtml(text)}</div>
    `;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function addLogosMessage(text) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message logos';
    messageEl.innerHTML = `
        <div class="message-header">LOGOS</div>
        <div class="message-content">${escapeHtml(text)}</div>
    `;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function addSystemMessage(text) {
    const messagesDiv = document.getElementById('chat-messages');
    const messageEl = document.createElement('div');
    messageEl.className = 'message system';
    messageEl.innerHTML = `
        <div class="message-content">${escapeHtml(text)}</div>
    `;
    messagesDiv.appendChild(messageEl);
    messagesDiv.scrollTop = messagesDiv.scrollHeight;
}

function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

// State Management
function updateState(state) {
    currentState = state;

    // Update canvas class
    canvas.className = state;

    // Update label
    const stateLabel = document.getElementById('state-label');
    stateLabel.textContent = state.charAt(0).toUpperCase() + state.slice(1);
}

// Trinity Knot Drawing
function drawTrinityKnot() {
    const centerX = canvas.width / 2;
    const centerY = canvas.height / 2;
    const radius = 40;

    ctx.clearRect(0, 0, canvas.width, canvas.height);

    // Draw three interlocking circles
    const angles = [0, 120, 240];

    ctx.lineWidth = 3;
    ctx.strokeStyle = getStateColor();

    angles.forEach(angle => {
        const radian = (angle * Math.PI) / 180;
        const x = centerX + Math.cos(radian) * 20;
        const y = centerY + Math.sin(radian) * 20;

        ctx.beginPath();
        ctx.arc(x, y, radius, 0, 2 * Math.PI);
        ctx.stroke();
    });

    // Draw center point
    ctx.fillStyle = getStateColor();
    ctx.beginPath();
    ctx.arc(centerX, centerY, 5, 0, 2 * Math.PI);
    ctx.fill();
}

function getStateColor() {
    switch (currentState) {
        case 'listening':
            return '#0066cc';  // Deep blue
        case 'processing':
            return '#e0f7ff';  // Ice white
        case 'responding':
            return '#00bfff';  // Electric blue
        case 'stasis':
            return '#00bfff';  // Electric blue
        default:
            return '#00bfff';
    }
}

function animateTrinityKnot() {
    drawTrinityKnot();
    requestAnimationFrame(animateTrinityKnot);
}
