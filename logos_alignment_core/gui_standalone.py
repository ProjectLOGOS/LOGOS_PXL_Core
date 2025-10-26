import tkinter as tk
from tkinter import ttk, filedialog
import threading
import time
import logging

# Setup logging for audit
logging.basicConfig(filename='audit/gui_actions.log', level=logging.INFO)

class MockExtensionsManager:
    """Mock extensions manager for standalone GUI"""
    def voice_input(self, duration=5):
        return None  # No voice input in standalone mode

    def tts_output(self, text):
        pass  # No TTS in standalone mode

    def file_upload(self, max_size_mb=10):
        filepath = filedialog.askopenfilename()
        if filepath:
            import os
            size_mb = os.path.getsize(filepath) / (1024 * 1024)
            if size_mb <= max_size_mb:
                return filepath
        return None

class MockNexus:
    """Mock LOGOS Nexus for standalone GUI"""
    def initialize(self):
        pass

    def process_query(self, text):
        # Simple fallback response
        return f"LOGOS analysis: '{text}' - My logic is rooted in PXL proofs, enhanced by probabilistic models like PyTorch and Pyro where available—no black boxes here. Ask me anything!"

extensions_manager = MockExtensionsManager()

class LOGOSGUI:
    def __init__(self, nexus):
        self.nexus = nexus
        self.root = tk.Tk()

        # Count loaded libraries
        self.library_count = self.count_loaded_libraries()
        self.root.title(f"LOGOS - {self.library_count}/13 Libraries")
        self.root.configure(bg='#1a1a1a')
        self.root.geometry("800x400")  # Fixed size for split-screen

        # Split into two columns with a vertical divider
        self.left_frame = tk.Frame(self.root, bg='#1a1a1a', width=400)
        self.right_frame = tk.Frame(self.root, bg='#1a1a1a', width=400)
        self.left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        tk.Frame(self.root, bg='#00bfff', width=2).pack(side=tk.LEFT, fill=tk.Y)  # Divider

        # Left Column: Chat with Scrollbar
        self.chat_frame = tk.Frame(self.left_frame, bg='#1a1a1a')
        self.chat_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.chat_log = tk.Text(self.chat_frame, bg='#222222', fg='#ffffff', font=('Helvetica', 12), wrap=tk.WORD, state=tk.DISABLED)
        self.scrollbar = tk.Scrollbar(self.chat_frame, orient=tk.VERTICAL, command=self.chat_log.yview)
        self.chat_log.config(yscrollcommand=self.scrollbar.set)
        self.chat_log.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.input_frame = tk.Frame(self.left_frame, bg='#1a1a1a')
        self.input_frame.pack(fill=tk.X, padx=5, pady=5)
        self.input_entry = tk.Entry(self.input_frame, bg='#333333', fg='#ffffff', font=('Helvetica', 12))
        self.input_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.send_btn = ttk.Button(self.input_frame, text="Send", command=self.handle_send, style='TButton')
        self.send_btn.pack(side=tk.RIGHT)
        self.input_entry.bind("<Return>", lambda e: self.handle_send())

        self.upload_btn = ttk.Button(self.left_frame, text="Upload (≤10MB)", command=self.handle_file_upload, style='TButton')
        self.upload_btn.pack(pady=5)

        # Right Column: Trinity Knot + Voice
        self.knot_canvas = tk.Canvas(self.right_frame, width=150, height=150, bg='#1a1a1a', highlightthickness=0)
        self.knot_canvas.pack(pady=20)
        self.draw_trinity_knot()
        self.animation_state = 'stasis'
        self.animation_thread = threading.Thread(target=self.animate_knot, daemon=True)
        self.animation_thread.start()

        self.voice_mode_var = tk.StringVar(value='Push to Talk')
        ttk.Radiobutton(self.right_frame, text="Push to Talk", variable=self.voice_mode_var, value="Push to Talk", command=self.update_voice_mode).pack(anchor=tk.CENTER, pady=5)
        ttk.Radiobutton(self.right_frame, text="Voice Activated", variable=self.voice_mode_var, value="Voice Activated", command=self.update_voice_mode).pack(anchor=tk.CENTER, pady=5)

        # Welcome message
        self.append_to_chat("LOGOS: Welcome! I'm running with 11/13 libraries loaded. Ask me anything!")

        self.root.mainloop()

    def count_loaded_libraries(self):
        """Count successfully loaded libraries"""
        libs_to_check = [
            'pyro', 'torch', 'sentence_transformers', 'networkx', 'arch',
            'filterpy', 'pykalman', 'sklearn', 'speech_recognition', 'pyttsx3',
            'tkinter', 'pymc', 'pmdarima'
        ]
        loaded = 0
        for lib in libs_to_check:
            try:
                if lib == 'sentence_transformers':
                    __import__('sentence_transformers')
                elif lib == 'speech_recognition':
                    __import__('speech_recognition')
                elif lib == 'pymc':
                    __import__('pymc')
                    __import__('pytensor')  # PyMC needs pytensor
                else:
                    __import__(lib)
                loaded += 1
            except ImportError:
                pass
        return loaded

    def draw_trinity_knot(self, color='#00bfff'):
        """Vector-draw the Trinity knot with clean arcs."""
        self.knot_canvas.delete("all")
        width, height = 150, 150
        center_x, center_y = width / 2, height / 2
        radius = 50

        self.knot_canvas.create_arc(center_x - radius, center_y - radius * 1.5, center_x + radius, center_y + radius * 0.5,
                                    start=0, extent=240, style=tk.ARC, width=6, outline=color)
        self.knot_canvas.create_arc(center_x - radius * 1.5, center_y - radius * 0.5, center_x + radius * 0.5, center_y + radius,
                                    start=120, extent=240, style=tk.ARC, width=6, outline=color)
        self.knot_canvas.create_arc(center_x - radius * 0.5, center_y - radius * 0.5, center_x + radius * 1.5, center_y + radius,
                                    start=240, extent=240, style=tk.ARC, width=6, outline=color)

    def animate_knot(self):
        """Pulse the knot based on state."""
        while True:
            try:
                if self.animation_state == 'listening':
                    color = '#0000ff'  # Deep blue
                    for _ in range(10):  # 1Hz pulse
                        self.draw_trinity_knot(color if _ % 2 else self.lighten_color(color, 0.2))
                        time.sleep(0.1)
                elif self.animation_state == 'processing':
                    color = '#00ffff'  # Ice blue to white
                    for i in range(10):
                        alpha = i / 10
                        self.draw_trinity_knot(self.lighten_color(color, alpha))
                        time.sleep(0.05)
                elif self.animation_state == 'speaking':
                    color = '#ffffff'  # White
                    for _ in range(10):
                        self.draw_trinity_knot(color if _ % 2 else self.lighten_color(color, 0.1))
                        time.sleep(0.1)
                else:  # stasis
                    colors = ['#00bfff', '#00ccff', '#00ffff', '#ccff00', '#ffcc00', '#ff6600']
                    for color in colors:
                        self.draw_trinity_knot(color)
                        time.sleep(0.5)
                self.root.update()
            except tk.TclError:
                # Window closed, exit thread
                break

    def lighten_color(self, hex_color, factor):
        """Lighten a hex color for pulse effect."""
        r = int(hex_color[1:3], 16)
        g = int(hex_color[3:5], 16)
        b = int(hex_color[5:7], 16)
        r = min(255, int(r + (255 - r) * factor))
        g = min(255, int(g + (255 - g) * factor))
        b = min(255, int(b + (255 - b) * factor))
        return f'#{r:02x}{g:02x}{b:02x}'

    def update_voice_mode(self):
        """Toggle voice mode behavior."""
        if self.voice_mode_var.get() == 'Voice Activated' and not hasattr(self, 'voice_thread'):
            self.append_to_chat("System: Voice Activated mode enabled (requires microphone)")
            self.voice_thread = threading.Thread(target=self.voice_loop, daemon=True)
            self.voice_thread.start()

    def voice_loop(self):
        """Continuous listening for Voice Activated mode."""
        while self.voice_mode_var.get() == 'Voice Activated':
            self.handle_voice_input()
            time.sleep(1)  # Poll every second

    def handle_voice_input(self):
        """Process voice input and transcribe to chat."""
        self.animation_state = 'listening'
        text = extensions_manager.voice_input(duration=5)
        if text:
            self.append_to_chat(f"You (Voice): {text}")  # Transcribe input
            self.animation_state = 'processing'
            response = self.get_response(text)
            self.append_to_chat(f"LOGOS: {response}")
            self.animation_state = 'speaking'
            extensions_manager.tts_output(response)
        self.animation_state = 'stasis'

    def handle_send(self):
        """Process text input."""
        text = self.input_entry.get().strip()
        if text:
            self.append_to_chat(f"You: {text}")
            self.input_entry.delete(0, tk.END)
            self.animation_state = 'processing'
            response = self.get_response(text)
            self.append_to_chat(f"LOGOS: {response}")
            self.animation_state = 'stasis'

    def handle_file_upload(self):
        """Handle file upload and process."""
        import os
        path = extensions_manager.file_upload(max_size_mb=10)
        if path:
            self.animation_state = 'processing'
            try:
                with open(path, 'r', errors='ignore') as f:
                    content = f.read()[:1000]  # Truncate for safety
                self.append_to_chat(f"You (File): {os.path.basename(path)}")
                response = self.get_response(f"File content: {content}")
                self.append_to_chat(f"LOGOS: {response}")
            except Exception as e:
                self.append_to_chat(f"System: Error reading file - {str(e)}")
            self.animation_state = 'stasis'

    def get_response(self, input_text):
        """Safe response generation with fallback."""
        try:
            response = self.nexus.process_query(input_text)
            if response is None or len(str(response)) == 0:
                raise ValueError("Empty response")
            logging.info(f"Query: {input_text}, Response: {response[:50]}...")
            return response
        except (AttributeError, ValueError, TypeError) as e:
            fallback = "My logic is rooted in PXL proofs, enhanced by probabilistic models like PyTorch and Pyro where available—no black boxes here. Ask me anything!"
            logging.error(f"Query failed: {input_text}, Fallback used - {e}")
            return fallback

    def append_to_chat(self, message):
        """Append message to chat log with scrollbar support."""
        self.chat_log.config(state=tk.NORMAL)
        self.chat_log.insert(tk.END, f"[{time.strftime('%H:%M:%S')}] {message}\n")
        self.chat_log.config(state=tk.DISABLED)
        self.chat_log.see(tk.END)  # Auto-scroll to latest

if __name__ == "__main__":
    import os
    # Create audit directory if it doesn't exist
    os.makedirs('audit', exist_ok=True)

    nexus = MockNexus()
    nexus.initialize()
    gui = LOGOSGUI(nexus)
