"""
GPT Integration Example for LOGOS Interactive Chat
==================================================

This shows how easy it would be to replace the current pattern matching
with GPT-powered conversational AI.

Installation: pip install openai

Time to implement: 2-3 hours for basic version
"""

import json
from datetime import datetime

import openai


class GPTConversationEngine:
    def __init__(self, api_key: str):
        self.client = openai.OpenAI(api_key=api_key)
        self.conversation_history: dict[str, list[dict]] = {}

        # System prompt that understands LOGOS capabilities
        self.system_prompt = """You are the LOGOS Interactive Assistant, powered by a proof-gated AI system with advanced capabilities:

AVAILABLE TOOLS:
• TETRAGNOS: Text analysis and semantic clustering
• TELOS: Time series forecasting and prediction  
• THONOC: Automated theorem proving
• Proof-gated security with cryptographic verification

CAPABILITIES:
• Text analysis: "analyze this text: [content]" 
• Forecasting: "predict trends for: 1, 2, 3, 4, 5"
• Logic: "prove that P and Q"
• System commands: /status, /capabilities, /help

BEHAVIOR:
- Be conversational and helpful
- Detect when user wants to use specific tools
- Explain LOGOS system capabilities clearly
- Maintain context across conversations
- Use emojis appropriately for a friendly interface

TOOL ROUTING:
When users ask for text analysis, forecasting, or theorem proving, 
indicate which tool should be used and format the request appropriately.
"""

    async def process_message(self, user_message: str, session_id: str) -> tuple[str, str | None]:
        """
        Process user message with GPT and return (response, tool_request)

        Returns:
        - response: GPT-generated response to user
        - tool_request: JSON string if a tool should be called, None otherwise
        """

        # Initialize conversation history for new sessions
        if session_id not in self.conversation_history:
            self.conversation_history[session_id] = []

        # Add user message to history
        self.conversation_history[session_id].append(
            {"role": "user", "content": user_message, "timestamp": datetime.now().isoformat()}
        )

        # Keep conversation history manageable (last 10 exchanges)
        history = self.conversation_history[session_id][-20:]

        try:
            # Call GPT with conversation context
            response = self.client.chat.completions.create(
                model="gpt-4",
                messages=[
                    {"role": "system", "content": self.system_prompt},
                    *[{"role": msg["role"], "content": msg["content"]} for msg in history],
                ],
                temperature=0.7,
                max_tokens=500,
                functions=[
                    {
                        "name": "route_to_tool",
                        "description": "Route request to appropriate LOGOS tool",
                        "parameters": {
                            "type": "object",
                            "properties": {
                                "tool": {
                                    "type": "string",
                                    "enum": ["tetragnos", "telos", "thonoc"],
                                },
                                "operation": {"type": "string"},
                                "data": {"type": "object"},
                            },
                            "required": ["tool", "operation", "data"],
                        },
                    }
                ],
                function_call="auto",
            )

            message = response.choices[0].message

            # Add GPT response to history
            self.conversation_history[session_id].append(
                {
                    "role": "assistant",
                    "content": message.content or "",
                    "timestamp": datetime.now().isoformat(),
                }
            )

            # Check if GPT wants to call a tool
            if message.function_call:
                function_args = json.loads(message.function_call.arguments)
                return message.content or "Let me process that for you...", json.dumps(
                    function_args
                )

            return message.content, None

        except Exception as e:
            return f"I'm having trouble processing that right now. Error: {str(e)}", None

    def clear_conversation(self, session_id: str):
        """Clear conversation history for a session"""
        if session_id in self.conversation_history:
            del self.conversation_history[session_id]


# Integration with existing LOGOS chat system
class EnhancedLOGOSChatEngine:
    def __init__(self):
        # Initialize GPT engine (would need API key from environment)
        api_key = os.getenv("OPENAI_API_KEY")  # Set in environment
        if api_key:
            self.gpt_engine = GPTConversationEngine(api_key)
            self.gpt_enabled = True
        else:
            self.gpt_enabled = False
            print("⚠️ OpenAI API key not found - falling back to pattern matching")

    async def process_message(self, message: str, session_id: str) -> str:
        """Enhanced message processing with GPT"""

        # Handle system commands first (keep existing functionality)
        if message.startswith("/"):
            return await self.handle_command(message, session_id)

        # Use GPT for conversation if available
        if self.gpt_enabled:
            response, tool_request = await self.gpt_engine.process_message(message, session_id)

            # If GPT wants to use a tool, execute it
            if tool_request:
                tool_data = json.loads(tool_request)
                tool_result = await self.execute_tool(tool_data, session_id)
                return f"{response}\n\n{tool_result}"

            return response

        # Fallback to original pattern matching
        return await self.handle_pattern_matching(message, session_id)

    async def execute_tool(self, tool_data: dict, session_id: str) -> str:
        """Execute the appropriate LOGOS tool based on GPT's request"""
        tool = tool_data["tool"]
        operation = tool_data["operation"]
        data = tool_data["data"]

        # Route to existing tool handlers
        if tool == "tetragnos":
            return await self.handle_text_analysis_gpt(data, session_id)
        elif tool == "telos":
            return await self.handle_forecasting_gpt(data, session_id)
        elif tool == "thonoc":
            return await self.handle_theorem_proving_gpt(data, session_id)

        return "Tool execution not implemented yet."


"""
BENEFITS OF THIS APPROACH:

1. ✅ EASY INTEGRATION: Uses existing service architecture
2. ✅ INTELLIGENT ROUTING: GPT understands user intent naturally
3. ✅ CONVERSATIONAL: Real back-and-forth dialogue 
4. ✅ CONTEXT AWARE: Remembers conversation history
5. ✅ TOOL INTEGRATION: Seamlessly calls TETRAGNOS/TELOS/THONOC
6. ✅ FALLBACK SAFE: Falls back to pattern matching if GPT unavailable
7. ✅ COST EFFECTIVE: Only pays for actual conversations

IMPLEMENTATION STEPS:
1. pip install openai
2. Get OpenAI API key (free tier available)
3. Replace handle_general_chat() method
4. Add GPT conversation engine
5. Test and refine prompts

TOTAL TIME: 2-3 hours for basic version, 1-2 days for advanced features
"""
