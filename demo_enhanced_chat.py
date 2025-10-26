#!/usr/bin/env python3
"""
LOGOS Enhanced Chat Interface Demo
Test script demonstrating GPT-like natural language interactions
"""

import asyncio
import aiohttp
import json
from logos_core.natural_language_processor import NaturalLanguageProcessor

async def test_chat_interface():
    """Test the enhanced chat interface with various queries"""

    print("🧠 LOGOS Enhanced Chat Interface Demo")
    print("=" * 50)

    # Initialize the natural language processor
    nlp = NaturalLanguageProcessor()
    session_id = "demo_session"

    # Test cases for different types of interactions
    test_cases = [
        {
            "type": "greeting",
            "input": "Hello! What can you help me with?",
            "description": "Testing conversational greeting"
        },
        {
            "type": "falsifiability",
            "input": "Is the statement □(P → Q) ∧ ◊P ∧ ¬◊Q falsifiable?",
            "description": "Testing modal logic falsifiability analysis"
        },
        {
            "type": "reasoning",
            "input": "What is the relationship between necessity and possibility in modal logic?",
            "description": "Testing philosophical reasoning question"
        },
        {
            "type": "explanation",
            "input": "Can you explain how countermodels work?",
            "description": "Testing explanation request"
        },
        {
            "type": "follow_up",
            "input": "Why is that formula falsifiable?",
            "description": "Testing contextual follow-up question"
        }
    ]

    # Create session
    nlp.create_session(session_id)

    for i, test_case in enumerate(test_cases, 1):
        print(f"\n🔍 Test {i}: {test_case['description']}")
        print(f"👤 User: {test_case['input']}")

        # Generate response based on type
        if test_case['type'] == 'falsifiability':
            # Simulate falsifiability result
            mock_result = {
                'formula': '□(P → Q) ∧ ◊P ∧ ¬◊Q',
                'falsifiable': True,
                'countermodel': {
                    'worlds': ['w0', 'w1'],
                    'relations': [['w0', 'w1']],
                    'valuation': {
                        'w0': {'P': True, 'Q': False},
                        'w1': {'P': False, 'Q': False}
                    }
                },
                'reasoning_trace': [
                    'Parsing modal formula',
                    'Analyzing necessity and possibility operators',
                    'Constructing Kripke model',
                    'Found countermodel in world w0'
                ]
            }
            response = nlp.process_falsifiability_result(mock_result, session_id)

        elif test_case['type'] == 'reasoning':
            # Simulate reasoning result
            mock_result = {
                'query': test_case['input'],
                'result': 'Necessity (□) and possibility (◊) are dual modal operators where □P means P is necessarily true and ◊P means P is possibly true',
                'confidence': 0.95,
                'reasoning_depth': 25,
                'safety_validated': True
            }
            response = nlp.process_reasoning_result(mock_result, session_id)

        else:
            # Use contextual response generation
            response = nlp.generate_contextual_response(test_case['input'], session_id)

        print(f"🧠 LOGOS: {response}")
        print("-" * 50)

    print("\n✅ Demo completed! The enhanced chat interface can:")
    print("   • Translate formal logic to natural language")
    print("   • Maintain conversation context")
    print("   • Provide GPT-like interactive responses")
    print("   • Handle various query types intelligently")

async def test_live_api_integration():
    """Test integration with live LOGOS API"""
    print("\n🔗 Testing Live API Integration")
    print("=" * 30)

    try:
        # Test falsifiability API
        async with aiohttp.ClientSession() as session:
            async with session.post(
                "http://localhost:8090/api/v1/falsifiability/validate",
                json={
                    "formula": "P ∧ ¬P",
                    "logic": "K",
                    "generate_countermodel": True
                }
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    print("✅ Falsifiability API working")

                    # Process with NLP
                    nlp = NaturalLanguageProcessor()
                    session_id = "api_test"
                    nlp.create_session(session_id)

                    result['formula'] = "P ∧ ¬P"
                    natural_response = nlp.process_falsifiability_result(result, session_id)
                    print(f"🧠 Natural Language Response: {natural_response}")
                else:
                    print("❌ Falsifiability API not responding")

    except Exception as e:
        print(f"❌ API Integration test failed: {e}")
        print("💡 Make sure LOGOS core API is running on localhost:8090")

if __name__ == "__main__":
    print("Starting LOGOS Enhanced Chat Interface Demo...")

    # Run the demo
    asyncio.run(test_chat_interface())

    # Test API integration if available
    asyncio.run(test_live_api_integration())
