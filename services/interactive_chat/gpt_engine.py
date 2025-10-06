"""
GPT-Enhanced LOGOS Chat Engine
==============================

This replaces the pattern-matching system with GPT-powered conversations
while maintaining all existing LOGOS functionality and security.
"""

import openai
import os
import json
import asyncio
from typing import Dict, List, Optional, Tuple
from datetime import datetime
import requests

class GPTLOGOSEngine:
    def __init__(self):
        # Try to get OpenAI API key from environment
        self.api_key = os.getenv("OPENAI_API_KEY")
        if self.api_key:
            self.client = openai.OpenAI(api_key=self.api_key)
            self.gpt_enabled = True
            print("✅ GPT integration enabled")
        else:
            self.gpt_enabled = False
            print("⚠️ No OpenAI API key found - set OPENAI_API_KEY environment variable")
            print("   Falling back to enhanced pattern matching")
        
        # Conversation memory
        self.conversation_history: Dict[str, List[Dict]] = {}
        
        # LOGOS system prompt
        self.system_prompt = """You are the LOGOS Interactive Assistant, an advanced AI system with proof-gated architecture and specialized toolkits.

AVAILABLE CAPABILITIES:
• TETRAGNOS: Semantic text analysis and clustering
• TELOS: Time series forecasting and prediction  
• THONOC: Automated theorem proving and logical reasoning
• Proof-gated security with cryptographic verification

BEHAVIOR GUIDELINES:
- Be conversational, helpful, and engaging
- Detect user intent for tool usage naturally
- Explain LOGOS system capabilities when relevant
- Maintain context across conversations
- Use appropriate emojis for friendly interaction
- When users want text analysis, forecasting, or theorem proving, route to appropriate tools

TOOL DETECTION:
- Text analysis requests: "analyze this text", "understand this", "what does this mean", etc.
- Forecasting requests: "predict", "forecast", "trends", "what happens next", etc.  
- Logic requests: "prove", "logic", "theorem", "is this true", etc.

RESPONSE FORMAT:
- For general chat: Respond naturally and conversationally
- For tool requests: Be helpful and explain what you're doing
- Always maintain the LOGOS branding and advanced AI persona"""

    async def process_message(self, user_message: str, session_id: str) -> Tuple[str, Optional[Dict]]:
        """
        Process user message with GPT intelligence
        Returns: (response_text, tool_request_dict)
        """
        
        if not self.gpt_enabled:
            return await self._fallback_processing(user_message, session_id)
        
        # Initialize conversation history
        if session_id not in self.conversation_history:
            self.conversation_history[session_id] = []
        
        # Add user message to history
        self.conversation_history[session_id].append({
            "role": "user",
            "content": user_message,
            "timestamp": datetime.now().isoformat()
        })
        
        # Keep conversation manageable (last 10 exchanges)
        recent_history = self.conversation_history[session_id][-20:]
        
        try:
            # Call GPT with function calling for tool detection
            response = self.client.chat.completions.create(
                model="gpt-4",
                messages=[
                    {"role": "system", "content": self.system_prompt},
                    *[{"role": msg["role"], "content": msg["content"]} 
                      for msg in recent_history if msg.get("role")]
                ],
                temperature=0.7,
                max_tokens=500,
                functions=[
                    {
                        "name": "use_logos_tool",
                        "description": "Use a specialized LOGOS AI tool",
                        "parameters": {
                            "type": "object",
                            "properties": {
                                "tool": {
                                    "type": "string", 
                                    "enum": ["tetragnos", "telos", "thonoc"],
                                    "description": "Which LOGOS tool to use"
                                },
                                "operation": {
                                    "type": "string",
                                    "description": "What operation to perform"
                                },
                                "data": {
                                    "type": "object",
                                    "description": "Data needed for the operation"
                                },
                                "explanation": {
                                    "type": "string",
                                    "description": "Brief explanation of what the tool will do"
                                }
                            },
                            "required": ["tool", "operation", "data", "explanation"]
                        }
                    }
                ],
                function_call="auto"
            )
            
            message = response.choices[0].message
            
            # Add GPT response to history
            self.conversation_history[session_id].append({
                "role": "assistant",
                "content": message.content or "",
                "timestamp": datetime.now().isoformat()
            })
            
            # Check if GPT wants to use a tool
            if message.function_call:
                try:
                    tool_request = json.loads(message.function_call.arguments)
                    response_text = message.content or f"🔧 {tool_request.get('explanation', 'Processing your request...')}"
                    return response_text, tool_request
                except json.JSONDecodeError:
                    return message.content or "Let me help you with that...", None
            
            return message.content or "I'm here to help! What would you like to explore?", None
            
        except Exception as e:
            error_msg = f"🤖 I'm having a brief technical moment. Let me try a different approach.\n\nError: {str(e)}"
            return error_msg, None

    async def _fallback_processing(self, message: str, session_id: str) -> Tuple[str, Optional[Dict]]:
        """Enhanced fallback when GPT is unavailable"""
        message_lower = message.lower()
        
        # Enhanced pattern matching with more intelligence
        if any(word in message_lower for word in ["analyze", "understand", "explain", "meaning", "semantic"]):
            # Extract text after common prefixes
            text_to_analyze = message
            for prefix in ["analyze this text:", "analyze text:", "analyze this:", "analyze", "understand this:", "explain this:"]:
                if prefix in message_lower:
                    text_to_analyze = message[message.lower().find(prefix) + len(prefix):].strip()
                    break
            
            if text_to_analyze and text_to_analyze != message:
                tool_request = {
                    "tool": "tetragnos",
                    "operation": "cluster_texts",
                    "data": {"texts": [text_to_analyze], "k": 1},
                    "explanation": "I'll analyze this text using semantic clustering"
                }
                return "🔍 I'll analyze that text for you using advanced semantic understanding...", tool_request
        
        elif any(word in message_lower for word in ["predict", "forecast", "trend", "future", "next"]):
            # Try to extract numbers
            import re
            numbers = re.findall(r'-?\d+\.?\d*', message)
            if len(numbers) >= 3:
                series = [float(num) for num in numbers[:10]]
                tool_request = {
                    "tool": "telos", 
                    "operation": "forecast_series",
                    "data": {"series": series, "horizon": 4},
                    "explanation": f"I'll forecast the next values in this series: {', '.join(numbers[:5])}"
                }
                return "📈 I'll analyze those trends and make predictions...", tool_request
        
        elif any(word in message_lower for word in ["prove", "logic", "theorem", "true", "false"]):
            # Extract logical statement
            statement = message
            tool_request = {
                "tool": "thonoc",
                "operation": "construct_proof", 
                "data": {"formula": statement},
                "explanation": "I'll attempt to prove this logical statement"
            }
            return "🔬 I'll work on proving that logical statement...", tool_request
        
        # General conversation fallback
        if any(word in message_lower for word in ["hello", "hi", "hey"]):
            return """👋 Hello! I'm the LOGOS Interactive Assistant powered by advanced AI.

I can help you with:
• 📝 Text analysis and semantic understanding
• 📈 Data forecasting and trend prediction
• 🔬 Logical reasoning and theorem proving
• 🛡️ All secured through proof-gated architecture

What would you like to explore today?""", None
        
        else:
            return f"""🤖 I understand you're asking about: "{message[:100]}{'...' if len(message) > 100 else ''}"

I'm here to help with:
• 📝 Text analysis - Try: "analyze this text: [your content]"
• 📈 Predictions - Try: "predict trends for: 1, 2, 3, 4, 5" 
• 🔬 Logic - Try: "prove that P and Q"
• ❓ Commands - Type /help for more options

How can I assist you?""", None

# Example usage showing how this integrates with existing system
if __name__ == "__main__":
    async def test_gpt_engine():
        engine = GPTLOGOSEngine()
        
        test_messages = [
            "Hello, what can you do?",
            "analyze this text: Machine learning is revolutionizing technology",
            "predict trends for: 10, 12, 15, 18, 22",
            "prove that true and true equals true"
        ]
        
        for msg in test_messages:
            print(f"\n👤 User: {msg}")
            response, tool_request = await engine.process_message(msg, "test_session")
            print(f"🤖 Assistant: {response}")
            if tool_request:
                print(f"🔧 Tool Request: {tool_request}")
    
    asyncio.run(test_gpt_engine())