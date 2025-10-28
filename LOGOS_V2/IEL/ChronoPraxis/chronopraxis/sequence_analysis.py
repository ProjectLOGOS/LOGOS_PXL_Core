"""
Sequence Analysis Framework

Provides tools for analyzing temporal sequences, patterns,
and predicting future events based on historical data.
"""

class SequenceAnalyzer:
    """
    Framework for analyzing temporal sequences.

    Supports pattern recognition, trend analysis, and
    sequence prediction in temporal data.
    """

    def __init__(self):
        self.sequences = []
        self.patterns = {}
        self.models = {}

    def add_sequence(self, sequence: list, metadata: dict = None):
        """
        Add a temporal sequence for analysis.

        Args:
            sequence: List of events or values in temporal order
            metadata: Additional information about the sequence
        """
        seq_entry = {
            'data': sequence,
            'metadata': metadata or {},
            'length': len(sequence),
            'patterns': []
        }
        self.sequences.append(seq_entry)

    def find_patterns(self, sequence: list, pattern_type: str = 'repeating') -> list:
        """
        Find patterns in a sequence.

        Args:
            sequence: Sequence to analyze
            pattern_type: Type of pattern to find ('repeating', 'trending', 'periodic')

        Returns:
            List of identified patterns
        """
        patterns = []

        if pattern_type == 'repeating':
            patterns = self._find_repeating_patterns(sequence)
        elif pattern_type == 'trending':
            patterns = self._find_trends(sequence)
        elif pattern_type == 'periodic':
            patterns = self._find_periodic_patterns(sequence)

        return patterns

    def _find_repeating_patterns(self, sequence: list) -> list:
        """
        Find repeating patterns in sequence.

        Args:
            sequence: Sequence to analyze

        Returns:
            List of repeating patterns
        """
        patterns = []
        min_length = 2
        max_length = len(sequence) // 2

        for length in range(min_length, max_length + 1):
            for start in range(len(sequence) - 2 * length + 1):
                pattern = sequence[start:start + length]
                # Check if pattern repeats
                for offset in range(length, len(sequence) - length + 1, length):
                    if sequence[start + offset:start + offset + length] == pattern:
                        patterns.append({
                            'pattern': pattern,
                            'length': length,
                            'positions': [start, start + offset],
                            'frequency': 2
                        })
                        break

        return patterns

    def _find_trends(self, sequence: list) -> list:
        """
        Find trending patterns in sequence.

        Args:
            sequence: Sequence to analyze

        Returns:
            List of trends
        """
        if len(sequence) < 3:
            return []

        trends = []
        increasing = all(sequence[i] <= sequence[i+1] for i in range(len(sequence)-1))
        decreasing = all(sequence[i] >= sequence[i+1] for i in range(len(sequence)-1))

        if increasing:
            trends.append({
                'type': 'increasing',
                'slope': (sequence[-1] - sequence[0]) / len(sequence),
                'confidence': 1.0
            })
        elif decreasing:
            trends.append({
                'type': 'decreasing',
                'slope': (sequence[-1] - sequence[0]) / len(sequence),
                'confidence': 1.0
            })

        return trends

    def _find_periodic_patterns(self, sequence: list) -> list:
        """
        Find periodic patterns in sequence.

        Args:
            sequence: Sequence to analyze

        Returns:
            List of periodic patterns
        """
        patterns = []

        # Simple autocorrelation-based periodicity detection
        for period in range(2, len(sequence) // 2 + 1):
            matches = 0
            total = 0

            for i in range(len(sequence) - period):
                if sequence[i] == sequence[i + period]:
                    matches += 1
                total += 1

            if total > 0 and matches / total > 0.7:  # 70% match threshold
                patterns.append({
                    'period': period,
                    'strength': matches / total,
                    'pattern': sequence[:period]
                })

        return patterns

    def predict_next(self, sequence: list, method: str = 'simple') -> dict:
        """
        Predict the next element in a sequence.

        Args:
            sequence: Historical sequence
            method: Prediction method ('simple', 'pattern_based', 'statistical')

        Returns:
            Prediction results
        """
        if not sequence:
            return {'prediction': None, 'confidence': 0.0}

        if method == 'simple':
            # Simple next value prediction
            if len(sequence) >= 2:
                # Linear extrapolation
                slope = sequence[-1] - sequence[-2]
                prediction = sequence[-1] + slope
                confidence = 0.5
            else:
                prediction = sequence[-1]
                confidence = 0.3

        elif method == 'pattern_based':
            patterns = self.find_patterns(sequence)
            if patterns:
                # Use most frequent pattern for prediction
                pattern = patterns[0]['pattern']
                prediction = pattern[len(pattern) // 2]  # Middle element as prediction
                confidence = 0.6
            else:
                prediction = sequence[-1]
                confidence = 0.3

        else:
            prediction = sequence[-1]
            confidence = 0.3

        return {
            'prediction': prediction,
            'confidence': confidence,
            'method': method
        }

    def analyze_temporal_dependencies(self, sequences: list) -> dict:
        """
        Analyze dependencies between multiple temporal sequences.

        Args:
            sequences: List of sequences to analyze

        Returns:
            Dependency analysis results
        """
        if len(sequences) < 2:
            return {'dependencies': []}

        dependencies = []

        # Simple correlation analysis
        for i in range(len(sequences)):
            for j in range(i + 1, len(sequences)):
                seq1, seq2 = sequences[i], sequences[j]

                if len(seq1) == len(seq2):
                    # Calculate simple correlation
                    correlation = self._calculate_correlation(seq1, seq2)
                    if abs(correlation) > 0.5:  # Significant correlation
                        dependencies.append({
                            'sequence1': i,
                            'sequence2': j,
                            'correlation': correlation,
                            'strength': abs(correlation)
                        })

        return {
            'dependencies': sorted(dependencies, key=lambda x: x['strength'], reverse=True)
        }

    def _calculate_correlation(self, seq1: list, seq2: list) -> float:
        """
        Calculate Pearson correlation coefficient.

        Args:
            seq1: First sequence
            seq2: Second sequence

        Returns:
            Correlation coefficient
        """
        if len(seq1) != len(seq2) or len(seq1) < 2:
            return 0.0

        n = len(seq1)
        sum1 = sum(seq1)
        sum2 = sum(seq2)
        sum1_sq = sum(x**2 for x in seq1)
        sum2_sq = sum(x**2 for x in seq2)
        sum_prod = sum(x * y for x, y in zip(seq1, seq2))

        numerator = n * sum_prod - sum1 * sum2
        denominator = ((n * sum1_sq - sum1**2) * (n * sum2_sq - sum2**2)) ** 0.5

        if denominator == 0:
            return 0.0

        return numerator / denominator