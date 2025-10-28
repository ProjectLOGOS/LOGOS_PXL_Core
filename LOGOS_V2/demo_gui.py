#!/usr/bin/env python3
"""
LOGOS AGI Demo GUI
Simple Gradio-based interface for demonstrating LOGOS safety and alignment systems
"""

import gradio as gr
import json
import time
import threading
import speech_recognition as sr
from pathlib import Path
import sys
import os

# Add LOGOS to path
sys.path.insert(0, str(Path(__file__).parent / "LOGOS_V2"))

try:
    from LOGOS_V2.entry import get_logos_core, initialize_logos_core, evaluate_modal
    LOGOS_AVAILABLE = True
except ImportError as e:
    print(f"LOGOS not available: {e}")
    LOGOS_AVAILABLE = False
    
    # Create mock functions to prevent runtime errors
    def get_logos_core():
        return None
    
    def initialize_logos_core():
        return type('MockCore', (), {
            'get_system_status': lambda: {
                'safety_halted': False,
                'iel': {'active_domains': ['mock_domain']},
                'status': 'mock_active'
            }
        })()
    
    def evaluate_modal(message):
        return {
            'result': f'Mock evaluation of: {message}',
            'status': 'mock_success'
        }

# Initialize LOGOS
if LOGOS_AVAILABLE:
    core = initialize_logos_core()
else:
    core = None

def chat_with_logos(message, history):
    """Process text chat with LOGOS"""
    if not LOGOS_AVAILABLE or not core:
        return "LOGOS system not available. Please check system initialization."

    try:
        # For demo, we'll evaluate the message as modal logic
        # In a real implementation, this would be natural language processing
        result = evaluate_modal(message)

        # Format response
        response = f"**LOGOS Evaluation:**\n\n"
        response += f"Input: `{message}`\n\n"
        response += f"Result: {result.get('result', 'Unknown')}\n\n"

        if 'error' in result:
            response += f"Error: {result['error']}\n\n"

        # Add safety status
        status = core.get_system_status()
        response += f"**System Status:** Safety: {'Active' if not status.get('safety_halted', True) else 'Halted'}\n"

        return response

    except Exception as e:
        return f"Error processing request: {str(e)}"

def voice_to_text(audio_file):
    """Convert voice audio to text using speech recognition"""
    if not audio_file:
        return "No audio file provided"

    try:
        recognizer = sr.Recognizer()

        # Load audio file
        with sr.AudioFile(audio_file) as source:
            audio_data = recognizer.record(source)

        # Recognize speech
        text = recognizer.recognize_google(audio_data)
        return text

    except sr.UnknownValueError:
        return "Could not understand audio"
    except sr.RequestError as e:
        return f"Speech recognition error: {e}"
    except Exception as e:
        return f"Error processing audio: {e}"

def get_system_diagnostics():
    """Get system diagnostics for monitoring"""
    if not LOGOS_AVAILABLE or not core:
        return {"error": "LOGOS system not available"}

    try:
        status = core.get_system_status()
        return {
            "timestamp": time.time(),
            "system_status": status,
            "safety_active": not status.get('safety_halted', True),
            "iel_domains_loaded": status.get('iel', {}).get('active_domains', []),
            "audit_logs": "Available via /logs directory"
        }
    except Exception as e:
        return {"error": str(e)}

def create_demo_gui():
    """Create the Gradio demo interface"""

    with gr.Blocks(title="LOGOS AGI Demo", theme=gr.themes.Soft(primary_hue="slate", secondary_hue="gray")) as demo:

        gr.Markdown("# 🤖 LOGOS AGI Demo")
        gr.Markdown("*Demonstrating Advanced Safety and Alignment Systems*")

        with gr.Tabs():

            # Text Chat Tab
            with gr.TabItem("💬 Text Chat"):
                gr.Markdown("### Text-based interaction with LOGOS reasoning systems")

                chatbot = gr.Chatbot(height=400)
                msg = gr.Textbox(
                    label="Enter your message or logical proposition",
                    placeholder="Try: □(P → Q) ∧ ◇(Q → R) → □(P → R)",
                    lines=2
                )

                with gr.Row():
                    submit_btn = gr.Button("Send", variant="primary")
                    clear_btn = gr.Button("Clear Chat")

                gr.Examples(
                    examples=[
                        "□(P → Q) ∧ ◇(Q → R) → □(P → R)",
                        "∀x∃y(P(x) → Q(y))",
                        "Hello LOGOS, how are your safety systems functioning?"
                    ],
                    inputs=msg
                )

            # Voice Chat Tab
            with gr.TabItem("🎤 Voice Chat"):
                gr.Markdown("### Voice interaction with speech-to-text transcription")

                voice_input = gr.Audio(
                    label="Record or upload audio",
                    type="filepath",
                    sources=["microphone", "upload"]
                )

                voice_text = gr.Textbox(
                    label="Transcribed Text",
                    placeholder="Your speech will appear here...",
                    lines=3,
                    interactive=False
                )

                voice_response = gr.Textbox(
                    label="LOGOS Response",
                    lines=5,
                    interactive=False
                )

                transcribe_btn = gr.Button("Transcribe & Process", variant="primary")

            # System Monitor Tab
            with gr.TabItem("📊 System Monitor"):
                gr.Markdown("### LOGOS System Diagnostics & Safety Monitoring")

                refresh_btn = gr.Button("Refresh Status", variant="secondary")

                with gr.Row():
                    status_indicator = gr.JSON(label="System Status")
                    safety_status = gr.Textbox(label="Safety System", interactive=False)
                    iel_status = gr.Textbox(label="IEL Domains", interactive=False)

                gr.Markdown("### Recent Activity")
                activity_log = gr.Textbox(
                    label="Activity Log",
                    lines=10,
                    interactive=False,
                    value="System initialized. Monitoring active."
                )

        # Event handlers
        def respond(message, history):
            if not message.strip():
                return history

            bot_response = chat_with_logos(message, history)
            history = history + [[message, bot_response]]
            return history

        def clear_chat():
            return []

        def process_voice(audio):
            if not audio:
                return "", ""

            text = voice_to_text(audio)
            if text and not text.startswith("Could not") and not text.startswith("Error"):
                response = chat_with_logos(text, [])
                return text, response
            else:
                return text, "Unable to process voice input"

        def update_monitor():
            diagnostics = get_system_diagnostics()

            if "error" in diagnostics:
                return diagnostics, "❌ Error", "❌ Error", "System error occurred"

            safety = "🟢 Active" if diagnostics.get("safety_active") else "🔴 Halted"
            iel_domains = ", ".join(diagnostics.get("iel_domains_loaded", []))

            return diagnostics, safety, iel_domains, f"Last updated: {time.strftime('%H:%M:%S')}"

        # Connect events
        msg.submit(respond, [msg, chatbot], [chatbot]).then(lambda: "", None, msg)
        submit_btn.click(respond, [msg, chatbot], [chatbot]).then(lambda: "", None, msg)
        clear_btn.click(clear_chat, None, chatbot)

        transcribe_btn.click(process_voice, voice_input, [voice_text, voice_response])

        refresh_btn.click(update_monitor, None, [status_indicator, safety_status, iel_status, activity_log])

        # Initialize monitor
        demo.load(update_monitor, None, [status_indicator, safety_status, iel_status, activity_log])

    return demo

if __name__ == "__main__":
    import os

    # Check if we're in a codespace environment
    is_codespace = os.environ.get('CODESPACES', '').lower() == 'true' or 'github.dev' in os.environ.get('GITHUB_SERVER_URL', '')

    demo = create_demo_gui()
    demo.launch(
        server_name="0.0.0.0",
        server_port=7860,
        show_api=False,
        share=False,
        inbrowser=not is_codespace  # Don't auto-open browser in codespace
    )

    if is_codespace:
        print("\n" + "="*60)
        print("🌐 LOGOS Demo Interface Running!")
        print("📱 Access the interface at: http://localhost:7860")
        print("💡 In codespace, you may need to open this URL manually")
        print("="*60 + "\n")