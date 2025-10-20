"""Lambda Logos Parser

Implements parsing of Lambda Logos expressions from string representations.
Provides lexical analysis, syntax parsing, and expression construction for
the Lambda Logos calculus.

Dependencies: re, typing, lambda_logos_core
"""

import re
from typing import Dict, List, Tuple, Optional, Union, Any, Iterator
from enum import Enum

# Import from Lambda Logos core (adjust imports as needed)
try:
    from lambda_logos_core import (
        LogosExpr, Variable, Value, Abstraction, Application, 
        SufficientReason, Constant, OntologicalType
    )
except ImportError:
    # Mock classes for standalone development
    class OntologicalType(Enum):
        EXISTENCE = "𝔼"
        GOODNESS = "𝔾"
        TRUTH = "𝕋"
        PROP = "Prop"
    
    class LogosExpr:
        pass
    
    class Variable(LogosExpr):
        def __init__(self, name, ont_type): 
            self.name = name
            self.ont_type = ont_type
    
    class Value(LogosExpr):
        def __init__(self, value, ont_type): 
            self.value = value
            self.ont_type = ont_type
    
    class Constant(LogosExpr):
        def __init__(self, name, const_type): 
            self.name = name
            self.const_type = const_type
    
    class Application(LogosExpr):
        def __init__(self, func, arg): 
            self.func = func
            self.arg = arg
    
    class Abstraction(LogosExpr):
        def __init__(self, var_name, var_type, body): 
            self.var_name = var_name
            self.var_type = var_type
            self.body = body

    class SufficientReason(LogosExpr):
        def __init__(self, source_type, target_type, value): 
            self.source_type = source_type
            self.target_type = target_type
            self.value = value

class TokenType(Enum):
    """Token types for lexical analysis."""
    LAMBDA = "lambda"
    DOT = "dot"
    LPAREN = "lparen"
    RPAREN = "rparen"
    COLON = "colon"
    COMMA = "comma"
    EQUALS = "equals"
    IDENTIFIER = "identifier"
    TYPE = "type"
    NUMBER = "number"
    SR = "sr"
    EOF = "eof"

class Token:
    """Token for lexical analysis."""
    
    def __init__(self, token_type: TokenType, value: str, position: int):
        """Initialize token.
        
        Args:
            token_type: Token type
            value: Token value
            position: Position in input string
        """
        self.token_type = token_type
        self.value = value
        self.position = position
    
    def __str__(self) -> str:
        """Return string representation."""
        return f"{self.token_type.value}({self.value})"

class Lexer:
    """Lexical analyzer for Lambda Logos."""
    
    def __init__(self, input_str: str):
        """Initialize lexer.
        
        Args:
            input_str: Input string to tokenize
        """
        self.input = input_str
        self.position = 0
        self.tokens = []
    
    def tokenize(self) -> List[Token]:
        """Tokenize input string.
        
        Returns:
            List of tokens
        """
        self.tokens = []
        
        while self.position < len(self.input):
            # Skip whitespace
            if self.input[self.position].isspace():
                self.position += 1
                continue
            
            # Check for lambda symbol
            if self.input[self.position] == 'λ' or self.input[self.position:self.position+6] == "lambda":
                if self.input[self.position] == 'λ':
                    self.tokens.append(Token(TokenType.LAMBDA, "λ", self.position))
                    self.position += 1
                else:
                    self.tokens.append(Token(TokenType.LAMBDA, "lambda", self.position))
                    self.position += 6
                continue
            
            # Check for punctuation
            if self.input[self.position] == '.':
                self.tokens.append(Token(TokenType.DOT, ".", self.position))
                self.position += 1
                continue
            
            if self.input[self.position] == '(':
                self.tokens.append(Token(TokenType.LPAREN, "(", self.position))
                self.position += 1
                continue
            
            if self.input[self.position] == ')':
                self.tokens.append(Token(TokenType.RPAREN, ")", self.position))
                self.position += 1
                continue
            
            if self.input[self.position] == ':':
                self.tokens.append(Token(TokenType.COLON, ":", self.position))
                self.position += 1
                continue
            
            if self.input[self.position] == ',':
                self.tokens.append(Token(TokenType.COMMA, ",", self.position))
                self.position += 1
                continue
            
            if self.input[self.position] == '=':
                self.tokens.append(Token(TokenType.EQUALS, "=", self.position))
                self.position += 1
                continue
            
            # Check for SR operator
            if self.input[self.position:self.position+2] == "SR":
                self.tokens.append(Token(TokenType.SR, "SR", self.position))
                self.position += 2
                continue
            
            # Check for type
            if self.input[self.position] in "𝔼𝔾𝕋":
                type_str = self.input[self.position]
                self.tokens.append(Token(TokenType.TYPE, type_str, self.position))
                self.position += 1
                continue
            
            if self.input[self.position:self.position+4] == "Prop":
                self.tokens.append(Token(TokenType.TYPE, "Prop", self.position))
                self.position += 4
                continue
            
            # Check for number
            if self.input[self.position].isdigit():
                start = self.position
                while self.position < len(self.input) and self.input[self.position].isdigit():
                    self.position += 1
                value = self.input[start:self.position]
                self.tokens.append(Token(TokenType.NUMBER, value, start))
                continue
            
            # Check for identifier
            if self.input[self.position].isalnum() or self.input[self.position] == '_':
                start = self.position
                while self.position < len(self.input) and (self.input[self.position].isalnum() or self.input[self.position] == '_'):
                    self.position += 1
                value = self.input[start:self.position]
                self.tokens.append(Token(TokenType.IDENTIFIER, value, start))
                continue
            
            # Skip unknown character
            self.position += 1
        
        # Add EOF token
        self.tokens.append(Token(TokenType.EOF, "", self.position))
        
        return self.tokens

class Parser:
    """Parser for Lambda Logos expressions."""
    
    def __init__(self, lexer: Lexer, env: Optional[Dict[str, Any]] = None):
        """Initialize parser.
        
        Args:
            lexer: Lexer instance
            env: Environment with predefined constants and values
        """
        self.lexer = lexer
        self.tokens = lexer.tokenize()
        self.position = 0
        self.current_token = self.tokens[self.position]
        self.env = env or {}
    
    def parse(self) -> LogosExpr:
        """Parse input string into Lambda Logos expression.
        
        Returns:
            Parsed expression
        """
        expr = self.parse_expr()
        
        # Ensure end of input
        if self.current_token.token_type != TokenType.EOF:
            self._error(f"Expected end of input, got {self.current_token}")
        
        return expr
    
    def parse_expr(self) -> LogosExpr:
        """Parse expression.
        
        Returns:
            Parsed expression
        """
        # Parse abstraction
        if self.current_token.token_type == TokenType.LAMBDA:
            return self.parse_abstraction()
        
        # Parse application or atomic
        return self.parse_application()
    
    def parse_abstraction(self) -> Abstraction:
        """Parse lambda abstraction.
        
        Returns:
            Parsed abstraction
        """
        # Consume lambda
        self._consume(TokenType.LAMBDA)
        
        # Parse variable name
        if self.current_token.token_type != TokenType.IDENTIFIER:
            self._error(f"Expected variable name, got {self.current_token}")
        
        var_name = self.current_token.value
        self._advance()
        
        # Parse type annotation
        self._consume(TokenType.COLON)
        
        if self.current_token.token_type != TokenType.TYPE:
            self._error(f"Expected type, got {self.current_token}")
        
        var_type = self._parse_type()
        
        # Parse body
        self._consume(TokenType.DOT)
        body = self.parse_expr()
        
        return Abstraction(var_name, var_type, body)
    
    def parse_application(self) -> LogosExpr:
        """Parse function application.
        
        Returns:
            Parsed application or atomic expression
        """
        # Parse atomic expression
        left = self.parse_atomic()
        
        # Parse application chain
        while self.current_token.token_type not in [TokenType.RPAREN, TokenType.DOT, TokenType.EOF]:
            right = self.parse_atomic()
            left = Application(left, right)
        
        return left
    
    def parse_atomic(self) -> LogosExpr:
        """Parse atomic expression.
        
        Returns:
            Parsed atomic expression
        """
        # Parse parenthesized expression
        if self.current_token.token_type == TokenType.LPAREN:
            self._consume(TokenType.LPAREN)
            expr = self.parse_expr()
            self._consume(TokenType.RPAREN)
            return expr
        
        # Parse SR operator
        if self.current_token.token_type == TokenType.SR:
            return self.parse_sr()
        
        # Parse variable or constant
        if self.current_token.token_type == TokenType.IDENTIFIER:
            name = self.current_token.value
            self._advance()
            
            # Check for predefined constant or value
            if name in self.env:
                return self.env[name]
            
            # Check for special values
            if name in ["ei", "og", "at"]:
                if name == "ei":
                    return Value(name, OntologicalType.EXISTENCE)
                elif name == "og":
                    return Value(name, OntologicalType.GOODNESS)
                elif name == "at":
                    return Value(name, OntologicalType.TRUTH)
            
            # Default to variable with Prop type
            return Variable(name, OntologicalType.PROP)
        
        self._error(f"Unexpected token: {self.current_token}")
    
    def parse_sr(self) -> SufficientReason:
        """Parse SR operator.
        
        Returns:
            Parsed SR operator
        """
        # Consume SR
        self._consume(TokenType.SR)
        
        # Parse arguments
        self._consume(TokenType.LPAREN)
        
        # Parse source type
        if self.current_token.token_type != TokenType.TYPE:
            self._error(f"Expected type, got {self.current_token}")
        
        source_type = self._parse_type()
        
        self._consume(TokenType.COMMA)
        
        # Parse target type
        if self.current_token.token_type != TokenType.TYPE:
            self._error(f"Expected type, got {self.current_token}")
        
        target_type = self._parse_type()
        
        self._consume(TokenType.COMMA)
        
        # Parse value
        if self.current_token.token_type != TokenType.NUMBER:
            self._error(f"Expected number, got {self.current_token}")
        
        value = int(self.current_token.value)
        self._advance()
        
        self._consume(TokenType.RPAREN)
        
        return SufficientReason(source_type, target_type, value)
    
    def _parse_type(self) -> OntologicalType:
        """Parse type.
        
        Returns:
            Parsed ontological type
        """
        if self.current_token.token_type != TokenType.TYPE:
            self._error(f"Expected type, got {self.current_token}")
        
        type_str = self.current_token.value
        self._advance()
        
        if type_str == "𝔼":
            return OntologicalType.EXISTENCE
        elif type_str == "𝔾":
            return OntologicalType.GOODNESS
        elif type_str == "𝕋":
            return OntologicalType.TRUTH
        elif type_str == "Prop":
            return OntologicalType.PROP
        
        self._error(f"Unknown type: {type_str}")
    
    def _advance(self) -> None:
        """Advance to next token."""
        self.position += 1
        if self.position < len(self.tokens):
            self.current_token = self.tokens[self.position]
    
    def _consume(self, token_type: TokenType) -> None:
        """Consume token of expected type.
        
        Args:
            token_type: Expected token type
            
        Raises:
            ValueError: If current token doesn't match expected type
        """
        if self.current_token.token_type == token_type:
            self._advance()
        else:
            self._error(f"Expected {token_type.value}, got {self.current_token.token_type.value}")
    
    def _error(self, message: str) -> None:
        """Raise parser error.
        
        Args:
            message: Error message
            
        Raises:
            ValueError: With position information
        """
        raise ValueError(f"Parser error at position {self.current_token.position}: {message}")

def parse_expr(input_str: str, env: Optional[Dict[str, Any]] = None) -> LogosExpr:
    """Parse Lambda Logos expression from string.
    
    Args:
        input_str: Input string
        env: Optional environment with predefined constants and values
        
    Returns:
        Parsed expression
        
    Raises:
        ValueError: If parsing fails
    """
    lexer = Lexer(input_str)
    parser = Parser(lexer, env)
    return parser.parse()

# Example usage
if __name__ == "__main__":
    # Test basic parsing
    expr_strs = [
        "λx:𝔼.x",
        "(λx:𝔼.x) ei",
        "SR(𝔼,𝔾,3)",
        "SR(𝔼,𝔾,3) ei",
        "λp:Prop.λq:Prop.(p q)"
    ]
    
    for expr_str in expr_strs:
        try:
            expr = parse_expr(expr_str)
            print(f"Parsed '{expr_str}' as: {expr}")
        except ValueError as e:
            print(f"Error parsing '{expr_str}': {e}")