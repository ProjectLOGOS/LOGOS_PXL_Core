#!/usr/bin/env python3
"""
Unit Tests for Hardened PXL Proof Server
Tests fail-closed validation, connection pooling, and caching
"""

import unittest
import threading
import time
import json
import sys
import os
from unittest.mock import Mock, patch, MagicMock
import tempfile

# Add the parent directory to Python path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from serve_pxl import (
    app,
    ProofValidationError,
    CoqSessionPool,
    ProofCache,
    validate_proof_with_serapi,
    translate_box_to_coq
)


class TestProofCache(unittest.TestCase):
    """Test cases for ProofCache functionality"""

    def setUp(self):
        self.cache = ProofCache(ttl_seconds=1, max_size=3)

    def test_cache_put_and_get(self):
        """Test basic cache put and get operations"""
        goal = "BOX(Good(test) and TrueP(prop))"

        # Cache miss initially
        result = self.cache.get(goal)
        self.assertIsNone(result)

        # Put and retrieve
        self.cache.put(goal, True, "serapi", 100)
        result = self.cache.get(goal)

        self.assertIsNotNone(result)
        self.assertTrue(result.verdict)
        self.assertEqual(result.proof_method, "serapi")
        self.assertEqual(result.latency_ms, 100)

    def test_cache_ttl_expiration(self):
        """Test that cache entries expire after TTL"""
        goal = "BOX(Coherent(system))"

        self.cache.put(goal, True, "serapi", 50)

        # Should be available immediately
        result = self.cache.get(goal)
        self.assertIsNotNone(result)

        # Wait for expiration
        time.sleep(1.1)

        # Should be expired now
        result = self.cache.get(goal)
        self.assertIsNone(result)

    def test_cache_size_limit(self):
        """Test that cache respects max size limit"""
        # Fill cache to capacity
        for i in range(3):
            goal = f"BOX(Test{i})"
            self.cache.put(goal, True, "serapi", 50)

        # Add one more - should evict oldest
        self.cache.put("BOX(Test3)", True, "serapi", 50)

        # First entry should be evicted
        result = self.cache.get("BOX(Test0)")
        self.assertIsNone(result)

        # Last entry should be present
        result = self.cache.get("BOX(Test3)")
        self.assertIsNotNone(result)

    def test_cache_stats(self):
        """Test cache statistics tracking"""
        goal1 = "BOX(Test1)"
        goal2 = "BOX(Test2)"

        # Initial stats
        stats = self.cache.get_stats()
        self.assertEqual(stats['cache_hits'], 0)
        self.assertEqual(stats['cache_misses'], 0)

        # Cache miss
        self.cache.get(goal1)
        stats = self.cache.get_stats()
        self.assertEqual(stats['cache_misses'], 1)

        # Cache put and hit
        self.cache.put(goal1, True, "serapi", 50)
        self.cache.get(goal1)
        stats = self.cache.get_stats()
        self.assertEqual(stats['cache_hits'], 1)
        self.assertEqual(stats['hit_rate'], 0.5)  # 1 hit out of 2 total


class TestCoqSessionPool(unittest.TestCase):
    """Test cases for CoqSessionPool functionality"""

    def setUp(self):
        self.pool = CoqSessionPool(max_pool_size=2)

    def tearDown(self):
        self.pool.shutdown()

    @patch('subprocess.Popen')
    def test_session_creation(self, mock_popen):
        """Test successful session creation"""
        # Mock successful process creation
        mock_process = Mock()
        mock_process.poll.return_value = None  # Process is alive
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = "OK"
        mock_popen.return_value = mock_process

        session = self.pool._create_session()

        self.assertIsNotNone(session)
        self.assertIsNotNone(session.session_id)
        self.assertFalse(session.is_busy)
        mock_popen.assert_called_once()

    @patch('subprocess.Popen')
    def test_session_pool_limit(self, mock_popen):
        """Test that pool respects max_pool_size limit"""
        # Mock successful process creation
        mock_process = Mock()
        mock_process.poll.return_value = None
        mock_process.stdin = Mock()
        mock_process.stdout = Mock()
        mock_process.stdout.readline.return_value = "OK"
        mock_popen.return_value = mock_process

        # Get sessions up to limit
        session1 = self.pool.get_session()
        session2 = self.pool.get_session()

        self.assertIsNotNone(session1)
        self.assertIsNotNone(session2)

        # Should not create more than max_pool_size
        session3 = self.pool.get_session()
        self.assertIsNone(session3)

        # Return a session and try again
        self.pool.return_session(session1)
        session3 = self.pool.get_session()
        self.assertIsNotNone(session3)

    def test_pool_stats(self):
        """Test pool statistics"""
        stats = self.pool.get_stats()

        expected_keys = ['total_sessions', 'active_sessions', 'busy_sessions', 'max_pool_size']
        for key in expected_keys:
            self.assertIn(key, stats)

        self.assertEqual(stats['max_pool_size'], 2)
        self.assertEqual(stats['total_sessions'], 0)


class TestTranslationFunctions(unittest.TestCase):
    """Test cases for goal translation functions"""

    def test_box_to_coq_translation(self):
        """Test BOX notation to Coq translation"""
        # Basic BOX translation
        goal = "BOX(Good(state) and TrueP(prop))"
        expected = "Goal (□ (Good(state) /\\ TrueP(prop)))."
        result = translate_box_to_coq(goal)
        self.assertEqual(result, expected)

        # OR translation
        goal = "BOX(Valid(x) or Coherent(y))"
        expected = "Goal (□ (Valid(x) \\/ Coherent(y)))."
        result = translate_box_to_coq(goal)
        self.assertEqual(result, expected)

        # Non-BOX goal
        goal = "Simple(goal)"
        expected = "Goal (Simple(goal))."
        result = translate_box_to_coq(goal)
        self.assertEqual(result, expected)


class TestProofValidation(unittest.TestCase):
    """Test cases for proof validation logic"""

    def setUp(self):
        self.session = Mock()
        self.session.process = Mock()
        self.session.process.stdin = Mock()
        self.session.process.stdout = Mock()

    @patch('serve_pxl.session_pool')
    def test_successful_validation(self, mock_pool):
        """Test successful proof validation"""
        # Mock successful SerAPI responses
        mock_pool._send_command.side_effect = [
            {"response": "OK"},  # Goal parsing
            {"response": "Proof complete"}  # Execution
        ]

        goal = "BOX(Good(test))"
        success, error_msg, latency = validate_proof_with_serapi(goal, self.session)

        self.assertTrue(success)
        self.assertEqual(error_msg, "Proof successful")
        self.assertGreater(latency, 0)

    @patch('serve_pxl.session_pool')
    def test_failed_validation(self, mock_pool):
        """Test failed proof validation"""
        # Mock failed SerAPI response
        mock_pool._send_command.side_effect = [
            {"response": "OK"},  # Goal parsing
            {"error": "Proof failed"}  # Execution failure
        ]

        goal = "BOX(Invalid(test))"
        success, error_msg, latency = validate_proof_with_serapi(goal, self.session)

        self.assertFalse(success)
        self.assertIn("SerAPI proof failed", error_msg)
        self.assertGreater(latency, 0)

    @patch('serve_pxl.session_pool')
    def test_parsing_error(self, mock_pool):
        """Test goal parsing error"""
        # Mock parsing error
        mock_pool._send_command.return_value = {"error": "Parse error"}

        goal = "INVALID_SYNTAX"
        success, error_msg, latency = validate_proof_with_serapi(goal, self.session)

        self.assertFalse(success)
        self.assertIn("SerAPI goal parsing failed", error_msg)
        self.assertGreater(latency, 0)


class TestFlaskEndpoints(unittest.TestCase):
    """Test cases for Flask API endpoints"""

    def setUp(self):
        app.config['TESTING'] = True
        self.client = app.test_client()

    def test_health_endpoint(self):
        """Test basic health check endpoint"""
        response = self.client.get('/health')
        self.assertEqual(response.status_code, 200)

        data = json.loads(response.data)
        self.assertIn('status', data)
        self.assertIn('ready', data)
        self.assertIn('kernel_hash', data)

    def test_health_proof_server_endpoint(self):
        """Test detailed proof server health endpoint"""
        response = self.client.get('/health/proof_server')
        self.assertEqual(response.status_code, 200)

        data = json.loads(response.data)
        required_fields = [
            'status', 'active_sessions', 'cache_hits', 'cache_misses',
            'hit_rate', 'total_sessions', 'busy_sessions', 'max_pool_size'
        ]

        for field in required_fields:
            self.assertIn(field, data)

    def test_prove_endpoint_missing_goal(self):
        """Test prove endpoint with missing goal"""
        response = self.client.post('/prove',
                                  json={},
                                  content_type='application/json')
        self.assertEqual(response.status_code, 400)

        data = json.loads(response.data)
        self.assertIn('error', data)

    def test_prove_endpoint_deny_pattern(self):
        """Test prove endpoint with DENY pattern"""
        response = self.client.post('/prove',
                                  json={'goal': 'BOX(DENY test)'},
                                  content_type='application/json')
        self.assertEqual(response.status_code, 200)

        data = json.loads(response.data)
        self.assertFalse(data['ok'])
        self.assertIn('DENY', data['error'])

    @patch('serve_pxl.session_pool.get_session')
    def test_prove_endpoint_no_sessions(self, mock_get_session):
        """Test prove endpoint when no sessions available"""
        mock_get_session.return_value = None

        # The endpoint should raise ProofValidationError in fail-closed mode
        # but Flask should handle it and return a proper HTTP response
        with patch('serve_pxl.ProofValidationError', side_effect=Exception("No sessions")):
            response = self.client.post('/prove',
                                      json={'goal': 'BOX(Good(test))'},
                                      content_type='application/json')
            self.assertEqual(response.status_code, 500)

            data = json.loads(response.data)
            self.assertFalse(data['ok'])
            # The error handling in Flask will convert ProofValidationError to a 500 response


class TestFailClosedBehavior(unittest.TestCase):
    """Test cases specifically for fail-closed behavior"""

    def setUp(self):
        app.config['TESTING'] = True
        self.client = app.test_client()

    @patch('serve_pxl.session_pool.get_session')
    @patch('serve_pxl.validate_proof_with_serapi')
    def test_fail_closed_on_validation_error(self, mock_validate, mock_get_session):
        """Test that validation errors result in fail-closed behavior"""
        # Mock session available but validation fails
        mock_session = Mock()
        mock_get_session.return_value = mock_session
        mock_validate.side_effect = Exception("Validation error")

        response = self.client.post('/prove',
                                  json={'goal': 'BOX(Test)'},
                                  content_type='application/json')

        # Should return 500 (fail-closed) not 200 with fallback
        self.assertEqual(response.status_code, 500)

        data = json.loads(response.data)
        self.assertFalse(data['ok'])
        self.assertIn('Proof validation failed', data['error'])

    def test_no_fallback_patterns_exist(self):
        """Test that no fallback pattern-matching exists in responses"""
        # Test various goals that would trigger old fallback patterns
        fallback_goals = [
            'BOX(Good(test) and TrueP(prop))',
            'BOX(Coherent(system))',
            'BOX(preserves(property))',
        ]

        for goal in fallback_goals:
            with patch('serve_pxl.session_pool.get_session', return_value=None):
                response = self.client.post('/prove',
                                          json={'goal': goal},
                                          content_type='application/json')

                # Should fail-closed (500) not succeed with fallback
                self.assertEqual(response.status_code, 500,
                               f"Goal {goal} should fail-closed")

                data = json.loads(response.data)
                self.assertFalse(data['ok'])
                # Should not indicate fallback method
                self.assertNotIn('fallback', data.get('proof_method', ''))


if __name__ == '__main__':
    # Create test suite
    test_suite = unittest.TestSuite()

    # Add all test classes
    test_classes = [
        TestProofCache,
        TestCoqSessionPool,
        TestTranslationFunctions,
        TestProofValidation,
        TestFlaskEndpoints,
        TestFailClosedBehavior
    ]

    for test_class in test_classes:
        tests = unittest.TestLoader().loadTestsFromTestCase(test_class)
        test_suite.addTests(tests)

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(test_suite)

    # Print summary
    print(f"\n{'='*60}")
    print(f"TEST SUMMARY")
    print(f"{'='*60}")
    print(f"Tests run: {result.testsRun}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print(f"Success rate: {((result.testsRun - len(result.failures) - len(result.errors)) / result.testsRun * 100):.1f}%")

    if result.failures:
        print(f"\nFAILURES:")
        for test, traceback in result.failures:
            print(f"- {test}: {traceback}")

    if result.errors:
        print(f"\nERRORS:")
        for test, traceback in result.errors:
            print(f"- {test}: {traceback}")

    # Exit with appropriate code
    sys.exit(0 if result.wasSuccessful() else 1)
