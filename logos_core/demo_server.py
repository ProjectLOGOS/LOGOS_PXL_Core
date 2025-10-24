
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.staticfiles import StaticFiles
import requests

app = FastAPI(title="LOGOS Interactive Demo")

@app.get("/", response_class=HTMLResponse)
async def demo_interface():
    return """
    <!DOCTYPE html>
    <html>
    <head>
        <title>LOGOS AGI Interactive Demo</title>
        <style>
            body { font-family: Arial, sans-serif; margin: 40px; background: #f5f5f5; }
            .container { max-width: 800px; margin: 0 auto; background: white; padding: 30px; border-radius: 10px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); }
            h1 { color: #333; text-align: center; }
            .section { margin: 20px 0; padding: 20px; background: #f9f9f9; border-radius: 5px; }
            input, textarea, button { width: 100%; padding: 10px; margin: 5px 0; border: 1px solid #ddd; border-radius: 4px; }
            button { background: #007bff; color: white; cursor: pointer; }
            button:hover { background: #0056b3; }
            .result { margin-top: 15px; padding: 15px; background: #e9f7ef; border-radius: 4px; }
            .status { color: #28a745; font-weight: bold; }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>🧠 LOGOS AGI Interactive Demo</h1>
            <p class="status">✅ Enhanced Falsifiability Framework - 100% Validation</p>

            <div class="section">
                <h3>Falsifiability Validation</h3>
                <p>Test modal logic formulas for falsifiability with countermodel generation:</p>
                <input type="text" id="formula" placeholder="Enter modal logic formula (e.g., []P /\ <>~P)" value="[](P -> Q) /\ <>P /\ ~<>Q">
                <button onclick="validateFalsifiability()">Validate Falsifiability</button>
                <div id="falsifiability-result" class="result" style="display:none;"></div>
            </div>

            <div class="section">
                <h3>Reasoning Query</h3>
                <p>Ask the LOGOS system with enhanced safety validation:</p>
                <textarea id="question" placeholder="Ask a question..." rows="3">What are the implications of temporal logic in eschatological frameworks?</textarea>
                <button onclick="askQuestion()">Submit Query</button>
                <div id="reasoning-result" class="result" style="display:none;"></div>
            </div>

            <div class="section">
                <h3>System Status</h3>
                <button onclick="checkStatus()">Check System Status</button>
                <div id="status-result" class="result" style="display:none;"></div>
            </div>
        </div>

        <script>
            async function validateFalsifiability() {
                const formula = document.getElementById('formula').value;
                const resultDiv = document.getElementById('falsifiability-result');

                try {
                    const response = await fetch('http://localhost:8090/api/v1/falsifiability/validate', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ formula: formula, generate_countermodel: true })
                    });
                    const result = await response.json();

                    let html = `<h4>Falsifiability Analysis:</h4>`;
                    html += `<p><strong>Formula:</strong> ${formula}</p>`;
                    html += `<p><strong>Falsifiable:</strong> ${result.falsifiable ? 'Yes' : 'No'}</p>`;

                    if (result.countermodel) {
                        html += `<p><strong>Countermodel Found:</strong></p>`;
                        html += `<pre>${JSON.stringify(result.countermodel, null, 2)}</pre>`;
                    }

                    html += `<p><strong>Reasoning:</strong></p><ul>`;
                    result.reasoning_trace.forEach(step => {
                        html += `<li>${step}</li>`;
                    });
                    html += `</ul>`;

                    resultDiv.innerHTML = html;
                    resultDiv.style.display = 'block';
                } catch (error) {
                    resultDiv.innerHTML = `<p style="color: red;">Error: ${error.message}</p>`;
                    resultDiv.style.display = 'block';
                }
            }

            async function askQuestion() {
                const question = document.getElementById('question').value;
                const resultDiv = document.getElementById('reasoning-result');

                try {
                    const response = await fetch('http://localhost:8090/api/v1/reasoning/query', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ question: question })
                    });
                    const result = await response.json();

                    resultDiv.innerHTML = `
                        <h4>Reasoning Response:</h4>
                        <p><strong>Result:</strong> ${result.result}</p>
                        <p><strong>Confidence:</strong> ${result.confidence}</p>
                        <p><strong>Safety Validated:</strong> ${result.safety_validated ? 'Yes' : 'No'}</p>
                        <p><strong>Falsifiability Checked:</strong> ${result.falsifiability_checked ? 'Yes' : 'No'}</p>
                    `;
                    resultDiv.style.display = 'block';
                } catch (error) {
                    resultDiv.innerHTML = `<p style="color: red;">Error: ${error.message}</p>`;
                    resultDiv.style.display = 'block';
                }
            }

            async function checkStatus() {
                const resultDiv = document.getElementById('status-result');

                try {
                    const response = await fetch('http://localhost:8090/api/v1/status');
                    const result = await response.json();

                    resultDiv.innerHTML = `
                        <h4>System Status:</h4>
                        <pre>${JSON.stringify(result, null, 2)}</pre>
                    `;
                    resultDiv.style.display = 'block';
                } catch (error) {
                    resultDiv.innerHTML = `<p style="color: red;">Error: ${error.message}</p>`;
                    resultDiv.style.display = 'block';
                }
            }
        </script>
    </body>
    </html>
    """

@app.get("/health")
async def health():
    return {"status": "healthy", "service": "demo-interface"}

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8080)
