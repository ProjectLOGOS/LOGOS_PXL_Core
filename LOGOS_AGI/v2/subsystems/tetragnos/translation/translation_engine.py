"""Translation Engine

Natural language processing component for THŌNOC system.
Provides semantic analysis, sentence decomposition, and ontological mapping
using the SIGN→MIND→BRIDGE translation pipeline.

Dependencies: nltk, spacy, typing
"""

from typing import Dict, List, Tuple, Optional, Union, Any, Set
import re
import logging
import json

try:
    import nltk
    from nltk.tokenize import word_tokenize
    from nltk.corpus import stopwords
    from nltk.stem import WordNetLemmatizer
    NLTK_AVAILABLE = True
except ImportError:
    NLTK_AVAILABLE = False
    
try:
    import spacy
    SPACY_AVAILABLE = True
except ImportError:
    SPACY_AVAILABLE = False

# Import from other modules (adjust paths as needed)
from .pdn_bridge import TranslationResult, PDNBridge
from ..ontology.trinity_vector import TrinityVector
from ..utils.data_structures import OntologicalType

logger = logging.getLogger(__name__)

class TranslationEngine:
    """Main translation engine for natural language processing."""
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        """Initialize translation engine.
        
        Args:
            config: Engine configuration
        """
        self.config = config or {}
        self.semantic_depth = self.config.get("semantic_depth", 3)
        
        # Setup NLP tools if available
        self.nlp = None
        self.lemmatizer = None
        self.stop_words = set()
        
        if SPACY_AVAILABLE:
            try:
                self.nlp = spacy.load("en_core_web_sm")
                logger.info("Loaded spaCy NLP model")
            except:
                logger.warning("Failed to load spaCy model")
        
        if NLTK_AVAILABLE:
            try:
                self.lemmatizer = WordNetLemmatizer()
                self.stop_words = set(stopwords.words('english'))
                logger.info("Loaded NLTK components")
            except:
                logger.warning("Failed to load NLTK components")
        
        # Ontological keyword mappings
        self.ontological_keywords = self._load_ontological_keywords()
        
        # Bridge connection (will be set by PDN bridge)
        self.pdn_bridge = None
        
        logger.info("Translation Engine initialized")
    
    def _load_ontological_keywords(self) -> Dict[str, List[str]]:
        """Load ontological keyword mappings.
        
        Returns:
            Dictionary mapping dimensions to keywords
        """
        # Default keyword mappings
        return {
            "existence": [
                "exist", "being", "reality", "substance", "exists", "real",
                "actual", "physical", "concrete", "material", "presence",
                "manifestation", "occurrence", "phenomenon", "emerge"
            ],
            "goodness": [
                "good", "moral", "ethical", "right", "virtue", "justice",
                "fair", "beneficial", "valuable", "worthy", "excellent",
                "noble", "honorable", "righteous", "benevolent"
            ],
            "truth": [
                "true", "truth", "knowledge", "fact", "correct", "accurate",
                "valid", "genuine", "authentic", "legitimate", "verifiable",
                "provable", "evident", "certain", "definite"
            ]
        }
    
    def set_pdn_bridge(self, bridge: PDNBridge) -> None:
        """Set PDN bridge for lambda integration.
        
        Args:
            bridge: PDN bridge instance
        """
        self.pdn_bridge = bridge
    
    def translate(self, query: str) -> TranslationResult:
        """Translate natural language query to ontological representation.
        
        Args:
            query: Natural language query
            
        Returns:
            Translation result
        """
        # Process query with NLP pipeline
        processed_data = self._process_query(query)
        
        # Extract SIGN layer
        sign_layer = self._extract_sign_layer(processed_data)
        
        # Extract MIND layer
        mind_layer = self._extract_mind_layer(sign_layer, processed_data)
        
        # Extract BRIDGE layer
        bridge_layer = self._extract_bridge_layer(mind_layer)
        
        # Create trinity vector
        trinity_vector = TrinityVector(
            existence=bridge_layer.get("existence", 0.5),
            goodness=bridge_layer.get("goodness", 0.5),
            truth=bridge_layer.get("truth", 0.5)
        )
        
        # Create layers dictionary
        layers = {
            "SIGN": sign_layer,
            "MIND": mind_layer,
            "BRIDGE": bridge_layer
        }
        
        return TranslationResult(query, trinity_vector, layers)
    
    def _process_query(self, query: str) -> Dict[str, Any]:
        """Process query with NLP pipeline.
        
        Args:
            query: Natural language query
            
        Returns:
            Processed data
        """
        processed = {
            "raw_query": query,
            "tokens": [],
            "lemmas": [],
            "pos_tags": [],
            "entities": [],
            "dependencies": []
        }
        
        # Use spaCy if available
        if self.nlp:
            doc = self.nlp(query)
            
            processed["tokens"] = [token.text for token in doc]
            processed["lemmas"] = [token.lemma_ for token in doc]
            processed["pos_tags"] = [(token.text, token.pos_) for token in doc]
            processed["entities"] = [(ent.text, ent.label_) for ent in doc.ents]
            processed["dependencies"] = [(token.text, token.dep_, token.head.text) for token in doc]
            
            return processed
        
        # Fallback to NLTK if available
        if NLTK_AVAILABLE:
            tokens = word_tokenize(query)
            processed["tokens"] = tokens
            
            if self.lemmatizer:
                processed["lemmas"] = [self.lemmatizer.lemmatize(token) for token in tokens]
            
            return processed
        
        # Simple fallback if no NLP tools available
        tokens = query.split()
        processed["tokens"] = tokens
        processed["lemmas"] = tokens
        
        return processed
    
    def _extract_sign_layer(self, processed_data: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Extract SIGN layer from processed data.
        
        Args:
            processed_data: Processed query data
            
        Returns:
            SIGN layer representation
        """
        sign_items = []
        
        # Use lemmas if available, otherwise tokens
        lemmas = processed_data.get("lemmas", processed_data.get("tokens", []))
        tokens = processed_data.get("tokens", [])
        pos_tags = dict(processed_data.get("pos_tags", []))
        
        for i, (token, lemma) in enumerate(zip(tokens, lemmas)):
            # Skip stop words
            if token.lower() in self.stop_words:
                continue
                
            # Create sign item
            sign_item = {
                "token": token,
                "lemma": lemma,
                "pos": pos_tags.get(token, "")
            }
            
            # Add ontological dimensions
            sign_item["dimensions"] = self._get_token_dimensions(lemma.lower())
            
            sign_items.append(sign_item)
        
        return sign_items
    
    def _get_token_dimensions(self, lemma: str) -> Dict[str, float]:
        """Get ontological dimension scores for token.
        
        Args:
            lemma: Lemmatized token
            
        Returns:
            Dimension scores
        """
        dimensions = {
            "existence": 0.0,
            "goodness": 0.0,
            "truth": 0.0
        }
        
        # Check each dimension
        for dim, keywords in self.ontological_keywords.items():
            for keyword in keywords:
                if lemma == keyword or lemma.startswith(keyword):
                    dimensions[dim] = 1.0
                    break
        
        return dimensions
    
    def _extract_mind_layer(self, sign_layer: List[Dict[str, Any]], processed_data: Dict[str, Any]) -> Dict[str, Any]:
        """Extract MIND layer from SIGN layer.
        
        Args:
            sign_layer: SIGN layer data
            processed_data: Processed query data
            
        Returns:
            MIND layer representation
        """
        # Initialize categories
        categories = {
            "ontological": 0.0,
            "moral": 0.0,
            "epistemic": 0.0,
            "causal": 0.0,
            "modal": 0.0,
            "logical": 0.0
        }
        
        # Calculate dimension aggregates
        dim_totals = {
            "existence": 0.0,
            "goodness": 0.0,
            "truth": 0.0
        }
        
        for item in sign_layer:
            for dim, score in item["dimensions"].items():
                dim_totals[dim] += score
        
        # Map dimensions to categories
        dim_sum = sum(dim_totals.values())
        if dim_sum > 0:
            # Normalize
            dim_totals = {k: v / dim_sum for k, v in dim_totals.items()}
            
            # Map to categories
            categories["ontological"] = dim_totals["existence"]
            categories["moral"] = dim_totals["goodness"]
            categories["epistemic"] = dim_totals["truth"]
        else:
            # Default bias if no clear dimension
            categories["ontological"] = 0.4
            categories["epistemic"] = 0.3
            categories["moral"] = 0.3
        
        # Enhance with linguistic features (if available)
        self._enhance_with_linguistic_features(categories, processed_data)
        
        return categories
    
    def _enhance_with_linguistic_features(self, categories: Dict[str, float], processed_data: Dict[str, Any]) -> None:
        """Enhance mind categories with linguistic features.
        
        Args:
            categories: Mind categories
            processed_data: Processed query data
        """
        # Extract entity types (if available)
        entities = processed_data.get("entities", [])
        for entity, label in entities:
            if label in ["PERSON", "ORG", "GPE"]:
                # Increase ontological for named entities
                categories["ontological"] += 0.1
            elif label in ["DATE", "TIME", "EVENT"]:
                # Increase causal for temporal entities
                categories["causal"] += 0.1
        
        # Extract dependency relations (if available)
        dependencies = processed_data.get("dependencies", [])
        for token, dep, head in dependencies:
            if dep in ["nsubj", "dobj", "pobj"]:
                # Subject/object relations strengthen ontological
                categories["ontological"] += 0.05
            elif dep in ["acomp", "advmod"]:
                # Qualifiers strengthen moral/evaluative
                categories["moral"] += 0.05
            elif dep in ["conj", "cc"]:
                # Conjunctions strengthen logical
                categories["logical"] += 0.05
            elif dep in ["aux"] and token.lower() in ["must", "should", "could", "may"]:
                # Modal auxiliaries strengthen modal
                categories["modal"] += 0.1
        
        # Normalize categories to ensure they sum to ~1.0
        cat_sum = sum(categories.values())
        if cat_sum > 0:
            factor = 1.0 / cat_sum
            for key in categories:
                categories[key] *= factor
    
    def _extract_bridge_layer(self, mind_layer: Dict[str, float]) -> Dict[str, float]:
        """Extract BRIDGE layer from MIND layer.
        
        Args:
            mind_layer: MIND layer data
            
        Returns:
            BRIDGE layer representation (ontological dimensions)
        """
        # Initialize dimensions with neutral values
        dimensions = {
            "existence": 0.5,
            "goodness": 0.5,
            "truth": 0.5
        }
        
        # Primary mappings
        dimensions["existence"] += 0.4 * mind_layer.get("ontological", 0)
        dimensions["goodness"] += 0.4 * mind_layer.get("moral", 0)
        dimensions["truth"] += 0.4 * mind_layer.get("epistemic", 0)
        
        # Secondary effects
        dimensions["existence"] += 0.2 * mind_layer.get("causal", 0)
        dimensions["truth"] += 0.2 * mind_layer.get("logical", 0)
        
        # Modal affects all dimensions
        modal_factor = 0.1 * mind_layer.get("modal", 0)
        dimensions["existence"] += modal_factor
        dimensions["goodness"] += modal_factor
        dimensions["truth"] += modal_factor
        
        # Ensure values are in range [0,1]
        for dim in dimensions:
            dimensions[dim] = max(0.0, min(1.0, dimensions[dim]))
        
        return dimensions
    
    def get_keywords_dimensions(self, keywords: List[str]) -> Dict[str, Dict[str, float]]:
        """Get ontological dimensions for keywords.
        
        Args:
            keywords: List of keywords
            
        Returns:
            Dictionary mapping keywords to dimension scores
        """
        result = {}
        
        for keyword in keywords:
            dimensions = self._get_token_dimensions(keyword.lower())
            result[keyword] = dimensions
        
        return result
    
    def analyze_query_structure(self, query: str) -> Dict[str, Any]:
        """Analyze query structure for advanced translation.
        
        Args:
            query: Natural language query
            
        Returns:
            Query structure analysis
        """
        # Basic query classification
        is_question = query.endswith("?")
        has_modal = any(word in query.lower() for word in 
                        ["can", "could", "may", "might", "must", "should", "would"])
        has_negation = any(word in query.lower() for word in 
                          ["not", "no", "never", "nothing", "nowhere", "none"])
        
        # Identify query focus
        focus = self._identify_query_focus(query)
        
        return {
            "is_question": is_question,
            "has_modal": has_modal,
            "has_negation": has_negation,
            "focus": focus
        }
    
    def _identify_query_focus(self, query: str) -> str:
        """Identify the focus dimension of query.
        
        Args:
            query: Natural language query
            
        Returns:
            Focus dimension ("existence", "goodness", "truth", or "unknown")
        """
        lower_query = query.lower()
        
        # Check for existence focus
        if any(word in lower_query for word in 
              ["exist", "exists", "existing", "existed", "real", "reality"]):
            return "existence"
        
        # Check for moral/goodness focus
        if any(word in lower_query for word in 
              ["good", "bad", "right", "wrong", "moral", "ethical", "just"]):
            return "goodness"
        
        # Check for truth/knowledge focus
        if any(word in lower_query for word in 
              ["true", "truth", "know", "knowledge", "fact", "correct"]):
            return "truth"
        
        # Default is unknown
        return "unknown"
    
    def translate_to_lambda(self, query: str) -> Tuple[Any, TranslationResult]:
        """Translate query to Lambda expression.
        
        Args:
            query: Natural language query
            
        Returns:
            (Lambda expression, Translation result) tuple
        """
        if not self.pdn_bridge:
            logger.warning("PDN bridge not set, cannot translate to Lambda")
            return None, None
        
        # Translate query to 3PDN/trinity representation
        translation = self.translate(query)
        
        # Use PDN bridge to convert to Lambda
        lambda_expr, _ = self.pdn_bridge.natural_to_lambda(query, translation.to_dict())
        
        return lambda_expr, translation