"""
Arithmetic Computation Engine

Provides high-precision arithmetic operations, number theory functions,
and computational mathematics capabilities.
"""

class ArithmeticEngine:
    """
    Engine for performing various arithmetic computations.

    Supports arbitrary precision arithmetic, number theory operations,
    and mathematical function evaluation.
    """

    def __init__(self, precision: int = 50):
        """
        Initialize the arithmetic engine.

        Args:
            precision: Decimal precision for computations
        """
        self.precision = precision
        self.computation_history = []

    def compute_expression(self, expression: str, variables: dict = None) -> dict:
        """
        Compute the value of a mathematical expression.

        Args:
            expression: Mathematical expression string
            variables: Dictionary of variable values

        Returns:
            Computation result with value and metadata
        """
        # Placeholder - in practice would use sympy or similar
        try:
            # Very basic evaluation (unsafe for production)
            if variables:
                safe_dict = {k: v for k, v in variables.items() if isinstance(v, (int, float))}
                result = eval(expression, {"__builtins__": {}}, safe_dict)
            else:
                result = eval(expression, {"__builtins__": {}})

            computation = {
                'expression': expression,
                'result': result,
                'variables': variables or {},
                'precision': self.precision,
                'success': True
            }

        except Exception as e:
            computation = {
                'expression': expression,
                'error': str(e),
                'success': False
            }

        self.computation_history.append(computation)
        return computation

    def factorize(self, number: int) -> dict:
        """
        Factorize an integer into its prime factors.

        Args:
            number: Integer to factorize

        Returns:
            Dictionary containing prime factors and their exponents
        """
        if number < 2:
            return {'factors': {}, 'original': number}

        factors = {}
        n = number

        # Check for 2
        while n % 2 == 0:
            factors[2] = factors.get(2, 0) + 1
            n //= 2

        # Check for odd factors
        i = 3
        while i * i <= n:
            while n % i == 0:
                factors[i] = factors.get(i, 0) + 1
                n //= i
            i += 2

        if n > 1:
            factors[n] = factors.get(n, 0) + 1

        return {
            'factors': factors,
            'original': number,
            'prime_factors': list(factors.keys())
        }

    def compute_gcd(self, a: int, b: int) -> int:
        """
        Compute the greatest common divisor of two integers.

        Args:
            a: First integer
            b: Second integer

        Returns:
            GCD of a and b
        """
        while b:
            a, b = b, a % b
        return a

    def compute_lcm(self, a: int, b: int) -> int:
        """
        Compute the least common multiple of two integers.

        Args:
            a: First integer
            b: Second integer

        Returns:
            LCM of a and b
        """
        if a == 0 or b == 0:
            return 0
        return abs(a * b) // self.compute_gcd(a, b)

    def is_prime(self, number: int) -> bool:
        """
        Check if a number is prime.

        Args:
            number: Number to check

        Returns:
            True if prime, False otherwise
        """
        if number < 2:
            return False
        if number == 2:
            return True
        if number % 2 == 0:
            return False

        for i in range(3, int(number**0.5) + 1, 2):
            if number % i == 0:
                return False

        return True

    def generate_primes(self, limit: int) -> list:
        """
        Generate all prime numbers up to a limit using sieve.

        Args:
            limit: Upper limit for prime generation

        Returns:
            List of prime numbers
        """
        if limit < 2:
            return []

        sieve = [True] * (limit + 1)
        sieve[0] = sieve[1] = False

        for i in range(2, int(limit**0.5) + 1):
            if sieve[i]:
                for j in range(i*i, limit + 1, i):
                    sieve[j] = False

        return [i for i in range(2, limit + 1) if sieve[i]]

    def compute_modular_exponentiation(self, base: int, exponent: int, modulus: int) -> int:
        """
        Compute (base^exponent) mod modulus efficiently.

        Args:
            base: Base number
            exponent: Exponent
            modulus: Modulus

        Returns:
            Result of modular exponentiation
        """
        result = 1
        base = base % modulus

        while exponent > 0:
            if exponent % 2 == 1:
                result = (result * base) % modulus
            exponent = exponent >> 1
            base = (base * base) % modulus

        return result