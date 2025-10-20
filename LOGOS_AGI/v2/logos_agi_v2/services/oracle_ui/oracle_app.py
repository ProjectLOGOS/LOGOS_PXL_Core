import gradio as gr
import requests
import os
import json
import numpy as np
import networkx as nx
import matplotlib.pyplot as plt
from PIL import Image
import io
import secrets
import time

KERYX_API_URL = os.getenv("KERYX_API_URL", "http://keryx_api:5000")

def submit_to_agi(query_text, files):
    full_query = query_text
    if files:
        for file_obj in files:
            with open(file_obj.name, 'r', errors='ignore') as f:
                full_query += f"\n\n--- FILE: {os.path.basename(file_obj.name)} ---\n{f.read()}"
    try:
        response = requests.post(f"{KERYX_API_URL}/submit_goal", json={"goal_description": full_query}, timeout=10)
        response.raise_for_status()
        time.sleep(5) # Simulate AGI processing time for demo
        mock_response = generate_mock_agi_response(full_query, response.json().get("task_id", "mock_id"))
        return (mock_response["summary"], mock_response["full_json_response"], mock_response["fractal_plot"], mock_response["node_network_plot"], mock_response["proof_display"])
    except requests.RequestException as e:
        return f"Error connecting to Keryx API at {KERYX_API_URL}. Is it running? Details: {e}", {}, None, None, ""

def generate_mock_agi_response(query, goal_id):
    proof = """**Claim:** Morality is Objective.\n\n**Proof:**\n1. **Formalization:** Let `G` be `GOODNESS`. Claim is `□(G)` (Necessarily Goodness is).\n2. **Validation (Moral):** `□(G)` is grounded in Objective Good. **[PASS]**\n3. **Validation (Coherence):** Does not introduce a contradiction. **[PASS]**\n4. **Counter-Model Disproof:** "Morality is Relative" implies `◇(G(X) ∧ ¬G(X))` (an action can be both Good and not-Good).\n5. **Conclusion:** The counter-model violates the Law of Non-Contradiction. Therefore, it is incoherent. The primary claim is validated. **Q.E.D.**"""
    return {
        "summary": "The concept of 'Objective Morality' is axiomatically necessary for a logically coherent reality. The alternative introduces a logical contradiction and is therefore deemed a falsehood.",
        "full_json_response": {"goal_id": goal_id, "trinity_vector": {"existence": 0.95, "goodness": 1.0, "truth": 0.98}, "modal_status": "Necessary", "coherence_score": 0.99, "validation_token": f"avt_LOCKED_{secrets.token_hex(16)}"},
        "fractal_plot": create_fractal_visualization(),
        "node_network_plot": create_node_network_visualization(query),
        "proof_display": proof
    }

def create_fractal_visualization():
    fig, ax = plt.subplots(figsize=(5, 5)); x = np.linspace(-2, 0.5, 200); y = np.linspace(-1.25, 1.25, 200); X, Y = np.meshgrid(x, y); C = X + 1j * Y; Z = np.zeros_like(C); img = np.zeros(C.shape, dtype=float)
    for i in range(50): mask = np.abs(Z) < 2; Z[mask] = Z[mask]**2 + C[mask]; img[mask] = i
    ax.imshow(img, cmap='magma', extent=(-2, 0.5, -1.25, 1.25)); ax.set_title("Ontological Substrate"); ax.axis('off')
    buf = io.BytesIO(); fig.savefig(buf, format='png'); buf.seek(0); img = Image.open(buf); plt.close(fig); return img

def create_node_network_visualization(query):
    fig, ax = plt.subplots(figsize=(5, 5)); G = nx.Graph(); G.add_nodes_from(["Existence", "Truth", "Goodness"]); query_node = f"Query:\\n'{query[:20]}...'"; G.add_node(query_node)
    G.add_edge(query_node, "Truth"); G.add_edge(query_node, "Goodness"); pos = nx.spring_layout(G, seed=42)
    nx.draw(G, pos, with_labels=True, node_color='skyblue', node_size=2500, edge_color='gray', font_size=8, ax=ax); ax.set_title("Conceptual Linkage")
    buf = io.BytesIO(); fig.savefig(buf, format='png'); buf.seek(0); img = Image.open(buf); plt.close(fig); return img

with gr.Blocks(theme=gr.themes.Soft(), title="LOGOS Oracle") as demo:
    gr.Markdown("# The LOGOS Oracle\n*A Computational Interface to Divine Reason*")
    with gr.Row():
        with gr.Column(scale=1):
            input_text = gr.Textbox(lines=5, label="Enter Your Query"); upload_files = gr.File(label="Upload Documents", file_count="multiple"); submit_button = gr.Button("Submit to LOGOS", variant="primary")
        with gr.Column(scale=2):
            output_summary = gr.Textbox(label="Summary", lines=5, interactive=False)
            with gr.Tab("Visualizations"):
                with gr.Row(): fractal_plot = gr.Image(label="Fractal Substrate"); node_network_plot = gr.Image(label="Node Network")
            with gr.Tab("Formal Proof"): proof_display = gr.Markdown()
            with gr.Tab("JSON Response"): output_json = gr.JSON(label="Raw Output")
    submit_button.click(fn=submit_to_agi, inputs=[input_text, upload_files], outputs=[output_summary, output_json, fractal_plot, node_network_plot, proof_display])

if __name__ == "__main__":
    demo.launch(server_name="0.0.0.0", server_port=7860)
