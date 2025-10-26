#!/usr/bin/env python3
"""
LOGOS Natural Language Processor
Converts formal logic, modal formulas, and Coq proof outputs into conversational English
"""

import re
import json
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime

@dataclass
class ConversationContext:
    """Maintains context for natural language conversations"""
    session_id: str
    history: List[Dict[str, Any]]
    current_topic: Optional[str] = None
    reasoning_depth: int = 0
    last_query_type: Optional[str] = None

class LogicTranslator:
    """Translates formal logic expressions into natural language"""

    def __init__(self):
        self.modal_operators = {
            '□': 'necessarily',
            '◊': 'possibly',
            '→': 'implies',
            '∧': 'and',
            '∨': 'or',
            '¬': 'not',
            '~': 'not',
            '∀': 'for all',
            '∃': 'there exists',
            '⊥': 'contradiction',
            '⊤': 'always true'
        }

        self.logic_patterns = {
            r'□\(([^)]+)\)': r'it is necessarily the case that \1',
            r'◊\(([^)]+)\)': r'it is possible that \1',
            r'(\w+)\s*→\s*(\w+)': r'if \1 then \2',
            r'(\w+)\s*∧\s*(\w+)': r'\1 and \2',
            r'(\w+)\s*∨\s*(\w+)': r'\1 or \2',
            r'¬(\w+)': r'not \1',
            r'~(\w+)': r'not \1',
        }

    def translate_formula(self, formula: str) -> str:
        """Convert a modal logic formula to natural language"""
        result = formula

        # Apply pattern-based translations
        for pattern, replacement in self.logic_patterns.items():
            result = re.sub(pattern, replacement, result)

        # Replace remaining operators
        for operator, english in self.modal_operators.items():
            result = result.replace(operator, f' {english} ')

        # Clean up spacing and formatting
        result = re.sub(r'\s+', ' ', result).strip()
        result = result.replace('( ', '(').replace(' )', ')')

        return result

class CoqTranslator:
    """Translates Coq proof outputs into natural language"""

    def __init__(self):
        self.proof_keywords = {
            'Theorem': 'I proved the theorem',
            'Lemma': 'I established the lemma',
            'Definition': 'I defined',
            'Proof': 'Here\'s the proof',
            'Qed': 'The proof is complete',
            'intros': 'I introduced the assumptions',
            'apply': 'I applied',
            'rewrite': 'I rewrote using',
            'reflexivity': 'by reflexivity',
            'assumption': 'using the assumption',
            'split': 'I split this into two parts',
            'left': 'I chose the left branch',
            'right': 'I chose the right branch',
            'exists': 'there exists'
        }

    def translate_proof(self, proof_text: str) -> str:
        """Convert Coq proof output to natural language explanation"""
        lines = proof_text.split('\n')
        translated_lines = []

        for line in lines:
            line = line.strip()
            if not line or line.startswith('(*') or line.startswith('//'):
                continue

            # Translate proof steps
            translated = line
            for coq_term, english in self.proof_keywords.items():
                if coq_term in translated:
                    translated = translated.replace(coq_term, english)

            # Handle specific patterns
            if 'falsifiable' in translated.lower():
                translated = f"I found that {translated.lower()}"
            elif 'countermodel' in translated.lower():
                translated = f"I generated a countermodel showing {translated.lower()}"
            elif 'valid' in translated.lower():
                translated = f"I verified that {translated.lower()}"

            if translated != line:
                translated_lines.append(translated)

        if translated_lines:
            return '. '.join(translated_lines) + '.'
        else:
            return "I completed the formal verification successfully."

class NaturalLanguageProcessor:
    """Main processor for converting LOGOS backend outputs to conversational responses"""

    def __init__(self):
        self.logic_translator = LogicTranslator()
        self.coq_translator = CoqTranslator()
        self.contexts: Dict[str, ConversationContext] = {}

    def create_session(self, session_id: str) -> ConversationContext:
        """Create a new conversation session"""
        context = ConversationContext(
            session_id=session_id,
            history=[],
            current_topic=None
        )
        self.contexts[session_id] = context
        return context

    def get_context(self, session_id: str) -> Optional[ConversationContext]:
        """Get existing conversation context"""
        return self.contexts.get(session_id)

    def process_falsifiability_result(self, result: Dict[str, Any], session_id: str) -> str:
        """Convert falsifiability result to natural language"""
        context = self.get_context(session_id)
        if not context:
            context = self.create_session(session_id)

        formula = result.get('formula', 'the formula')
        falsifiable = result.get('falsifiable', False)
        countermodel = result.get('countermodel')
        reasoning_trace = result.get('reasoning_trace', [])

        # Translate the formula
        translated_formula = self.logic_translator.translate_formula(formula)

        # Build conversational response
        if falsifiable:
            response = f"I analyzed the statement '{translated_formula}' and found that it's falsifiable. "

            if countermodel:
                worlds = countermodel.get('worlds', [])
                response += f"I constructed a countermodel with {len(worlds)} possible worlds "
                response += f"({', '.join(worlds)}) that demonstrates why this statement can be false."

                # Explain the valuation if available
                valuation = countermodel.get('valuation', {})
                if valuation:
                    response += " In this countermodel, "
                    val_explanations = []
                    for world, props in valuation.items():
                        prop_list = []
                        for prop, value in props.items():
                            prop_list.append(f"{prop} is {'true' if value else 'false'}")
                        if prop_list:
                            val_explanations.append(f"in world {world}, {', '.join(prop_list)}")
                    response += '; '.join(val_explanations) + "."

            response += " This means the original statement is not necessarily true in all possible circumstances."

        else:
            response = f"I analyzed the statement '{translated_formula}' and determined that it's valid. "
            response += "This means it holds true in all possible worlds and cannot be falsified. "
            response += "The statement represents a logical truth within the modal framework."

        # Add reasoning process if requested
        if reasoning_trace and len(reasoning_trace) > 2:
            response += f"\n\nHere's how I reasoned through this: {' → '.join(reasoning_trace[1:3])}"

        # Update context
        context.history.append({
            'type': 'falsifiability',
            'input': formula,
            'output': response,
            'timestamp': datetime.now().isoformat()
        })
        context.last_query_type = 'falsifiability'

        return response

    def process_reasoning_result(self, result: Dict[str, Any], session_id: str) -> str:
        """Convert reasoning query result to natural language"""
        context = self.get_context(session_id)
        if not context:
            context = self.create_session(session_id)

        query = result.get('query', 'your question')
        processed_result = result.get('result', '')
        confidence = result.get('confidence', 0.0)
        reasoning_depth = result.get('reasoning_depth', 0)

        # Generate natural, contextual response based on query content
        response = self._generate_natural_reasoning_response(query, processed_result, confidence)

        # Update context
        context.history.append({
            'type': 'reasoning',
            'input': query,
            'output': response,
            'confidence': confidence,
            'timestamp': datetime.now().isoformat()
        })
        context.current_topic = self._extract_topic(query)
        context.reasoning_depth = reasoning_depth
        context.last_query_type = 'reasoning'

        return response

    def _generate_natural_reasoning_response(self, query: str, result: str, confidence: float) -> str:
        """Generate natural, conversational responses based on query content"""
        query_lower = query.lower()

        # Handle specific types of questions naturally
        if any(word in query_lower for word in ['describe', 'what is', 'tell me about']):
            if 'logic core' in query_lower or 'core' in query_lower:
                return self._describe_logic_core()
            elif 'modal logic' in query_lower:
                return self._explain_modal_logic()
            elif 'proof' in query_lower:
                return self._explain_proofs()
            elif 'falsifiable' in query_lower or 'falsification' in query_lower:
                return self._explain_falsifiability()

        elif any(word in query_lower for word in ['how', 'how do', 'how does']):
            if 'work' in query_lower:
                if 'proof' in query_lower:
                    return self._explain_how_proofs_work()
                elif 'logic' in query_lower:
                    return self._explain_how_logic_works()
                elif 'countermodel' in query_lower:
                    return self._explain_countermodels()

        elif any(word in query_lower for word in ['why', 'reason', 'because']):
            return self._explain_reasoning_behind(query_lower)

        elif 'relationship' in query_lower or 'difference' in query_lower:
            if 'necessity' in query_lower and 'possibility' in query_lower:
                return self._explain_necessity_possibility_relationship()
            elif 'truth' in query_lower and 'falsifiability' in query_lower:
                return self._explain_truth_falsifiability_relationship()

        # Default to more natural response
        return f"That's a great question! {result} Let me know if you'd like me to elaborate on any particular aspect."

    def _describe_logic_core(self) -> str:
        """Describe the LOGOS logic core in natural language"""
        return """My logic core is built around several key components:

**Modal Logic Engine**: I can reason with necessity (□) and possibility (◊) operators, understanding what must be true versus what could be true in different possible worlds.

**Falsifiability Framework**: I can test whether logical statements can be proven false by constructing countermodels - specific scenarios that demonstrate when a statement doesn't hold.

**Formal Verification**: I use mathematical proofs (including Coq theorem prover integration) to verify that logical arguments are sound and complete.

**Safety Validation**: Every reasoning step is checked against safety constraints to ensure reliable and trustworthy conclusions.

**Natural Language Processing**: I translate between formal logical expressions and conversational explanations, making complex reasoning accessible.

The core operates on rigorous mathematical foundations while being designed for natural human interaction. Would you like me to dive deeper into any of these capabilities?"""

    def _explain_modal_logic(self) -> str:
        """Explain modal logic naturally"""
        return """Modal logic is fascinating! It's a way of reasoning about what's necessarily true, what's possibly true, and what's impossible.

Think of it like this: Regular logic deals with statements that are simply true or false. But modal logic asks deeper questions - *could* this be true? *must* this be true?

The key operators are:
- **□P** (necessarily P): P is true in all possible worlds
- **◊P** (possibly P): P is true in at least one possible world

For example, "□(all bachelors are unmarried)" - this is necessarily true by definition. But "◊(it will rain tomorrow)" - this is possibly true, depending on weather conditions.

I use this to analyze complex logical relationships and test whether statements hold up under all possible circumstances. Want to try testing a modal statement?"""

    def _explain_proofs(self) -> str:
        """Explain logical proofs naturally"""
        return """Logical proofs are like building a bridge from what we know to what we want to prove, using only valid logical steps.

Think of it as a conversation where every statement must be justified:
1. **Premises**: What we start with (our assumptions)
2. **Rules of inference**: Valid ways to draw conclusions
3. **Steps**: Each logical move from one statement to the next
4. **Conclusion**: What we've proven

For example, if I know "All philosophers love wisdom" and "Socrates is a philosopher," I can prove "Socrates loves wisdom."

I specialize in formal proofs that are mathematically rigorous - every step is verified to be logically sound. I can also work with modal proofs that reason about necessity and possibility.

Would you like me to walk through a specific proof example?"""

    def _explain_falsifiability(self) -> str:
        """Explain falsifiability naturally"""
        return """Falsifiability is about testing whether a statement *could* be proven wrong. It's a crucial concept because statements that can never be falsified aren't really informative.

Here's how I approach it:

**For a statement to be falsifiable**, I need to be able to construct a scenario (called a countermodel) where the statement is false.

**Example**: "All swans are white" is falsifiable - I could potentially find a black swan that proves it wrong.

**Modal example**: The statement "□P → P" (if P is necessary, then P is true) is actually *not* falsifiable in normal modal logic - it's a valid principle.

When I test falsifiability, I systematically construct possible worlds and check if any of them make the statement false. If I find one, the statement is falsifiable. If not, it might be a logical truth.

This helps distinguish between statements that are necessarily true versus those that just happen to be true. Want to test a specific statement?"""

    def process_system_status(self, status: Dict[str, Any], session_id: str) -> str:
        """Convert system status to natural language"""
        context = self.get_context(session_id)
        if not context:
            context = self.create_session(session_id)

        health = status.get('status', 'unknown')
        services = status.get('services', {})

        if health == 'healthy':
            response = "All systems are running smoothly! "
        else:
            response = f"System status is currently: {health}. "

        # Explain service status
        operational_services = []
        issues = []

        for service, state in services.items():
            service_name = service.replace('_', ' ').title()
            if state == 'operational':
                operational_services.append(service_name)
            else:
                issues.append(f"{service_name} is {state}")

        if operational_services:
            response += f"The {', '.join(operational_services)} {'are' if len(operational_services) > 1 else 'is'} fully operational. "

        if issues:
            response += f"However, {'; '.join(issues)}. "

        response += "I'm ready to help with logical reasoning, falsifiability testing, and formal verification tasks."

        return response

    def _explain_how_proofs_work(self) -> str:
        """Explain how proofs work"""
        return """Proofs work by taking you step-by-step from what you already know to what you want to prove, using only logically valid moves.

It's like giving directions - each step must be clearly justified and lead logically to the next. Here's the process:

1. **Start with assumptions** (premises you're given)
2. **Apply logical rules** (like "if A implies B, and A is true, then B is true")
3. **Build up conclusions** step by step
4. **Reach your target** (what you wanted to prove)

I verify each step mathematically, so you can trust that if the premises are true, the conclusion must be true too. Think of it as a logical guarantee!

Want to see a proof in action?"""

    def _explain_how_logic_works(self) -> str:
        """Explain how logic works"""
        return """Logic is the study of valid reasoning - the rules for drawing reliable conclusions from information.

At its core, logic helps us:
- **Distinguish** good arguments from bad ones
- **Preserve truth** - if we start with true premises and use valid reasoning, we get true conclusions
- **Avoid contradictions** and logical fallacies
- **Build knowledge** systematically

I work with formal logic, which uses mathematical precision. This means I can mechanically verify that reasoning steps are correct, eliminating human error.

Modal logic adds another layer - reasoning about what's possible, necessary, or impossible across different scenarios.

What aspect of logical reasoning interests you most?"""

    def _explain_countermodels(self) -> str:
        """Explain countermodels"""
        return """Countermodels are specific scenarios I construct to show when a logical statement fails. Think of them as "what if" examples that break a claim.

Here's how it works:
- **Possible worlds**: I create different scenarios or "worlds"
- **Relations**: How these worlds connect to each other
- **Truth assignments**: What's true or false in each world

**Example**: To test "□P" (P is necessarily true), I'd try to build a world where P is false. If I succeed, then □P is falsifiable.

It's like being a logical detective - I'm looking for the scenario that breaks the case! These countermodels help distinguish between statements that are always true versus those that just happen to be true in some circumstances.

Would you like me to construct a countermodel for a specific statement?"""

    def _explain_reasoning_behind(self, query: str) -> str:
        """Explain reasoning behind concepts"""
        if 'important' in query:
            return """Logic and reasoning are important because they help us think clearly and avoid errors. In a world full of information, logic gives us tools to evaluate what's reliable, build knowledge systematically, and make sound decisions. It's like having a quality control system for thinking!"""
        elif 'modal' in query:
            return """Modal logic matters because the world isn't just about what happens to be true right now - we need to reason about possibilities, necessities, and what could have been different. It helps us understand concepts like knowledge, belief, time, obligation, and ability."""
        else:
            return """The reasoning behind this involves understanding how logical structures work and why certain principles hold universally. Would you like me to elaborate on any specific aspect?"""

    def _explain_necessity_possibility_relationship(self) -> str:
        """Explain necessity and possibility relationship"""
        return """Necessity and possibility are like two sides of the same coin - they're dual concepts in modal logic!

**The key relationship**: Something is necessarily true if and only if its negation is not possibly true.
- □P ↔ ¬◊¬P (P is necessary iff it's not possible for P to be false)

**Think of it this way**:
- **Necessary**: Must be true in all possible scenarios
- **Possible**: Could be true in at least one scenario
- **Impossible**: Can't be true in any scenario

**Example**:
- "2+2=4" is necessary (true in all possible worlds)
- "It will rain tomorrow" is possible (true in some possible worlds)
- "A square circle exists" is impossible (true in no possible worlds)

This duality helps us analyze complex logical relationships. If something is necessarily false, then it's impossible. If something is possibly true, then it's not necessarily false.

Does this relationship make sense? Want to explore it with specific examples?"""

    def _explain_truth_falsifiability_relationship(self) -> str:
        """Explain truth and falsifiability relationship"""
        return """Truth and falsifiability have a fascinating relationship! Here's the key insight:

**Truth** is about what actually holds in reality.
**Falsifiability** is about what *could potentially* be shown false.

**The relationship**:
- A statement can be **true but falsifiable** (like "All observed ravens are black" - true so far, but a white raven could prove it false)
- A statement can be **necessarily true and unfalsifiable** (like "All bachelors are unmarried" - true by definition)
- A statement that's **unfalsifiable might not be informative** (if nothing could ever prove it wrong, what does it really tell us?)

**In modal logic**: I test falsifiability by trying to construct countermodels. If I can build a scenario where the statement is false, then it's falsifiable. If not, it might be a necessary truth.

This helps distinguish between contingent truths (could be otherwise) and necessary truths (couldn't be otherwise).

Want to test the falsifiability of a specific statement?"""

    def _extract_topic(self, query: str) -> str:
        """Extract the main topic from a query"""
        # Simple topic extraction - could be enhanced with NLP
        keywords = ['logic', 'proof', 'modal', 'necessity', 'possibility', 'truth', 'falsification', 'reasoning']
        query_lower = query.lower()

        for keyword in keywords:
            if keyword in query_lower:
                return keyword

        # Default topic based on key words
        if any(word in query_lower for word in ['true', 'false', 'valid']):
            return 'truth_evaluation'
        elif any(word in query_lower for word in ['prove', 'proof', 'demonstrate']):
            return 'formal_proof'
        else:
            return 'general_reasoning'

    def generate_contextual_response(self, user_input: str, session_id: str) -> str:
        """Generate a response based on conversation context"""
        context = self.get_context(session_id)
        if not context:
            context = self.create_session(session_id)

        user_lower = user_input.lower()

        # Handle specific questions about LOGOS directly
        if any(word in user_lower for word in ['describe', 'what is', 'tell me about']):
            if 'logic core' in user_lower or 'your core' in user_lower:
                return self._describe_logic_core()
            elif 'yourself' in user_lower or 'you are' in user_lower:
                return self._describe_logos_capabilities()
            elif 'modal logic' in user_lower:
                return self._explain_modal_logic()
            elif 'proof' in user_lower or 'proofs' in user_lower:
                return self._explain_proofs()
            elif 'falsifiable' in user_lower or 'falsification' in user_lower:
                return self._explain_falsifiability()

        # Handle how/why questions
        elif any(word in user_lower for word in ['how', 'why']):
            if 'work' in user_lower:
                if 'proof' in user_lower:
                    return self._explain_how_proofs_work()
                elif 'logic' in user_lower:
                    return self._explain_how_logic_works()
                elif 'countermodel' in user_lower:
                    return self._explain_countermodels()
                else:
                    return "I work by applying formal logical principles and mathematical reasoning. I can analyze statements, construct proofs, test falsifiability, and translate complex logical concepts into natural language. What specific aspect would you like to understand?"

        # Handle follow-up questions based on context
        elif context.history and any(word in user_lower for word in ['explain', 'elaborate', 'more detail', 'what does']):
            last_entry = context.history[-1]
            if last_entry['type'] == 'falsifiability':
                return "I'd be happy to elaborate on that falsifiability analysis! Which part would you like me to explain further - how I constructed the countermodel, what it means for the statement, or the logical principles involved?"
            elif last_entry['type'] == 'reasoning':
                return "I can definitely explain more about that reasoning! What specific aspect interests you - the logical principles I used, the steps in my analysis, or how it connects to broader logical concepts?"

        # Handle greetings
        elif any(greeting in user_lower for greeting in ['hello', 'hi', 'hey', 'greetings']):
            return "Hello! I'm LOGOS, your AI reasoning assistant. I love exploring logical questions, testing whether statements can be falsified, and explaining complex reasoning in natural language. What's on your mind today?"

        # Handle capability questions
        elif any(word in user_lower for word in ['can you', 'what can', 'help', 'able', 'capabilities']):
            return self._describe_logos_capabilities()

        # Handle relationship questions
        elif 'relationship' in user_lower or 'difference' in user_lower or 'connection' in user_lower:
            if 'necessity' in user_lower and 'possibility' in user_lower:
                return self._explain_necessity_possibility_relationship()
            elif 'truth' in user_lower and 'falsifiability' in user_lower:
                return self._explain_truth_falsifiability_relationship()
            else:
                return "That's an interesting question about relationships between concepts! Could you be more specific about which logical concepts you'd like me to compare or connect?"

        # Handle thank you
        elif any(word in user_lower for word in ['thank', 'thanks', 'appreciate']):
            return "You're very welcome! I enjoy exploring logical questions and making complex reasoning accessible. Feel free to ask me anything else about logic, proofs, modal reasoning, or falsifiability!"

        # Default response for natural conversation
        else:
            return "That's an interesting question! I'd love to help you explore it. Could you tell me a bit more about what specific aspect of logic or reasoning you're curious about? I'm particularly good at explaining modal logic, testing falsifiability, and breaking down complex proofs into understandable steps."

    def _describe_logos_capabilities(self) -> str:
        """Describe LOGOS capabilities naturally"""
        return """I'm LOGOS, an AI reasoning system built for logical analysis and formal verification. Here's what I can do:

**🧠 Logical Reasoning**: I can analyze complex arguments, identify logical fallacies, and verify that reasoning is sound.

**🔍 Falsifiability Testing**: Give me any statement and I'll test whether it can be proven false by constructing countermodels - specific scenarios that would make it fail.

**📐 Modal Logic**: I work with necessity (□) and possibility (◊) to analyze what must be true, what could be true, and what's impossible.

**✓ Formal Verification**: I can verify mathematical proofs and explain them in plain language, using tools like Coq for rigorous checking.

**💬 Natural Explanation**: I translate complex logical concepts into conversational language, making formal reasoning accessible.

**🛡️ Safety Validation**: Every conclusion I reach is checked against safety constraints to ensure reliability.

I'm here to make logic and formal reasoning feel like a natural conversation. What would you like to explore?"""
