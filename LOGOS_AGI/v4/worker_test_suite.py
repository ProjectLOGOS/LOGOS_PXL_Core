# logos_agi_v1/tests/test_workers.py

"""
Comprehensive test suite for LOGOS AGI worker subsystems.

Tests the functionality of TETRAGNOS, TELOS, and THONOC workers
including RabbitMQ communication, task processing, and result validation.
"""

import json
import time
import uuid
import asyncio
import logging
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed

try:
    import pika
    PIKA_AVAILABLE = True
except ImportError:
    PIKA_AVAILABLE = False
    print("Warning: pika not available, RabbitMQ tests will be skipped")

# Test configuration
TEST_CONFIG = {
    'rabbitmq_host': 'localhost',
    'rabbitmq_port': 5672,
    'test_timeout': 30,  # seconds
    'max_workers': 3,
    'log_level': 'INFO'
}

# Setup logging
logging.basicConfig(
    level=getattr(logging, TEST_CONFIG['log_level']),
    format='%(asctime)s - %(levelname)s - TEST - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class TestResult:
    """Test result data structure."""
    test_name: str
    subsystem: str
    task_type: str
    success: bool
    response_time: float
    error_message: Optional[str] = None
    result_data: Optional[Dict[str, Any]] = None

class WorkerTestSuite:
    """Comprehensive test suite for worker subsystems."""
    
    def __init__(self):
        self.connection = None
        self.channel = None
        self.test_results: List[TestResult] = []
        self.response_queue = f"test_responses_{uuid.uuid4().hex[:8]}"
        
    def setup_rabbitmq(self) -> bool:
        """Setup RabbitMQ connection for testing."""
        if not PIKA_AVAILABLE:
            logger.error("RabbitMQ testing requires pika library")
            return False
            
        try:
            credentials = pika.PlainCredentials('guest', 'guest')
            parameters = pika.ConnectionParameters(
                host=TEST_CONFIG['rabbitmq_host'],
                port=TEST_CONFIG['rabbitmq_port'],
                credentials=credentials,
                heartbeat=300
            )
            
            self.connection = pika.BlockingConnection(parameters)
            self.channel = self.connection.channel()
            
            # Declare test response queue
            self.channel.queue_declare(queue=self.response_queue, auto_delete=True)
            
            logger.info("RabbitMQ connection established for testing")
            return True
            
        except Exception as e:
            logger.error(f"Failed to setup RabbitMQ: {e}")
            return False
    
    def teardown_rabbitmq(self):
        """Cleanup RabbitMQ connection."""
        try:
            if self.channel and self.channel.is_open:
                self.channel.queue_delete(queue=self.response_queue)
                self.channel.close()
            if self.connection and self.connection.is_open:
                self.connection.close()
            logger.info("RabbitMQ connection cleaned up")
        except Exception as e:
            logger.error(f"Error during RabbitMQ cleanup: {e}")
    
    def send_task_message(self, queue_name: str, task_message: Dict[str, Any]) -> bool:
        """Send a task message to a worker queue."""
        try:
            self.channel.basic_publish(
                exchange='',
                routing_key=queue_name,
                body=json.dumps(task_message),
                properties=pika.BasicProperties(
                    delivery_mode=2,  # Persistent
                    reply_to=self.response_queue,
                    correlation_id=task_message['task_id']
                )
            )
            return True
        except Exception as e:
            logger.error(f"Failed to send task message: {e}")
            return False
    
    def wait_for_response(self, task_id: str, timeout: int = 30) -> Optional[Dict[str, Any]]:
        """Wait for a response message with the given task ID."""
        start_time = time.time()
        
        while time.time() - start_time < timeout:
            try:
                method, properties, body = self.channel.basic_get(
                    queue=self.response_queue,
                    auto_ack=True
                )
                
                if method is None:
                    time.sleep(0.1)
                    continue
                
                response = json.loads(body.decode('utf-8'))
                if response.get('task_id') == task_id:
                    return response
                    
            except Exception as e:
                logger.error(f"Error waiting for response: {e}")
                break
        
        return None
    
    def test_tetragnos_cluster_texts(self) -> TestResult:
        """Test TETRAGNOS text clustering functionality."""
        task_id = f"test_tetragnos_cluster_{uuid.uuid4().hex[:8]}"
        start_time = time.time()
        
        task_message = {
            'task_id': task_id,
            'type': 'cluster_texts',
            'payload': {
                'texts': [
                    "Machine learning is a subset of artificial intelligence",
                    "Deep learning uses neural networks with multiple layers",
                    "Natural language processing helps computers understand text",
                    "Computer vision enables machines to interpret images",
                    "Reinforcement learning trains agents through rewards"
                ],
                'method': 'kmeans',
                'n_clusters': 3
            }
        }
        
        try:
            if not self.send_task_message('tetragnos_task_queue', task_message):
                return TestResult(
                    test_name="tetragnos_cluster_texts",
                    subsystem="TETRAGNOS",
                    task_type="cluster_texts",
                    success=False,
                    response_time=0.0,
                    error_message="Failed to send task message"
                )
            
            response = self.wait_for_response(task_id, TEST_CONFIG['test_timeout'])
            response_time = time.time() - start_time
            
            if response is None:
                return TestResult(
                    test_name="tetragnos_cluster_texts",
                    subsystem="TETRAGNOS",
                    task_type="cluster_texts",
                    success=False,
                    response_time=response_time,
                    error_message="No response received within timeout"
                )
            
            success = (response.get('status') == 'success' and 
                      'clusters' in response.get('result', {}))
            
            return TestResult(
                test_name="tetragnos_cluster_texts",
                subsystem="TETRAGNOS",
                task_type="cluster_texts",
                success=success,
                response_time=response_time,
                result_data=response.get('result'),
                error_message=None if success else response.get('result', {}).get('error')
            )
            
        except Exception as e:
            return TestResult(
                test_name="tetragnos_cluster_texts",
                subsystem="TETRAGNOS", 
                task_type="cluster_texts",
                success=False,
                response_time=time.time() - start_time,
                error_message=str(e)
            )
    
    def test_telos_predict_outcomes(self) -> TestResult:
        """Test TELOS outcome prediction functionality."""
        task_id = f"test_telos_predict_{uuid.uuid4().hex[:8]}"
        start_time = time.time()
        
        task_message = {
            'task_id': task_id,
            'type': 'predict_outcomes',
            'payload': {
                'current_state': {
                    'temperature': 25.0,
                    'humidity': 60.0,
                    'pressure': 1013.25
                },
                'interventions': [
                    {
                        'id': 'increase_temperature',
                        'parameters': {'temperature': 30.0}
                    }
                ],
                'target_variables': ['humidity', 'pressure'],
                'horizon': 1
            }
        }
        
        try:
            if not self.send_task_message('telos_task_queue', task_message):
                return TestResult(
                    test_name="telos_predict_outcomes",
                    subsystem="TELOS",
                    task_type="predict_outcomes",
                    success=False,
                    response_time=0.0,
                    error_message="Failed to send task message"
                )
            
            response = self.wait_for_response(task_id, TEST_CONFIG['test_timeout'])
            response_time = time.time() - start_time
            
            if response is None:
                return TestResult(
                    test_name="telos_predict_outcomes",
                    subsystem="TELOS",
                    task_type="predict_outcomes",
                    success=False,
                    response_time=response_time,
                    error_message="No response received within timeout"
                )
            
            success = (response.get('status') == 'success' and 
                      'predictions' in response.get('result', {}))
            
            return TestResult(
                test_name="telos_predict_outcomes",
                subsystem="TELOS",
                task_type="predict_outcomes",
                success=success,
                response_time=response_time,
                result_data=response.get('result'),
                error_message=None if success else response.get('result', {}).get('error')
            )
            
        except Exception as e:
            return TestResult(
                test_name="telos_predict_outcomes",
                subsystem="TELOS",
                task_type="predict_outcomes",
                success=False,
                response_time=time.time() - start_time,
                error_message=str(e)
            )
    
    def test_thonoc_construct_proof(self) -> TestResult:
        """Test THONOC proof construction functionality."""
        task_id = f"test_thonoc_proof_{uuid.uuid4().hex[:8]}"
        start_time = time.time()
        
        task_message = {
            'task_id': task_id,
            'type': 'construct_proof',
            'payload': {
                'claim': '(p ∨ ¬p)',  # Law of excluded middle - should be provable
                'counter_claims': ['¬(p ∨ ¬p)'],  # Contradiction
                'method': 'axiomatic'
            }
        }
        
        try:
            if not self.send_task_message('thonoc_task_queue', task_message):
                return TestResult(
                    test_name="thonoc_construct_proof",
                    subsystem="THONOC",
                    task_type="construct_proof",
                    success=False,
                    response_time=0.0,
                    error_message="Failed to send task message"
                )
            
            response = self.wait_for_response(task_id, TEST_CONFIG['test_timeout'])
            response_time = time.time() - start_time
            
            if response is None:
                return TestResult(
                    test_name="thonoc_construct_proof",
                    subsystem="THONOC",
                    task_type="construct_proof",
                    success=False,
                    response_time=response_time,
                    error_message="No response received within timeout"
                )
            
            success = (response.get('status') == 'success' and 
                      'proof_result' in response.get('result', {}))
            
            return TestResult(
                test_name="thonoc_construct_proof",
                subsystem="THONOC",
                task_type="construct_proof",
                success=success,
                response_time=response_time,
                result_data=response.get('result'),
                error_message=None if success else response.get('result', {}).get('error')
            )
            
        except Exception as e:
            return TestResult(
                test_name="thonoc_construct_proof",
                subsystem="THONOC",
                task_type="construct_proof", 
                success=False,
                response_time=time.time() - start_time,
                error_message=str(e)
            )
    
    def test_thonoc_assign_consequence(self) -> TestResult:
        """Test THONOC consequence assignment functionality."""
        task_id = f"test_thonoc_consequence_{uuid.uuid4().hex[:8]}"
        start_time = time.time()
        
        task_message = {
            'task_id': task_id,
            'type': 'assign_consequence',
            'payload': {
                'outcome': {
                    'description': 'Implementing new safety protocols',
                    'probability': 0.85,
                    'type': 'policy_change',
                    'alignment': 'positive'
                },
                'context': {
                    'domain': 'workplace_safety',
                    'stakeholders': ['employees', 'management']
                }
            }
        }
        
        try:
            if not self.send_task_message('thonoc_task_queue', task_message):
                return TestResult(
                    test_name="thonoc_assign_consequence",
                    subsystem="THONOC",
                    task_type="assign_consequence",
                    success=False,
                    response_time=0.0,
                    error_message="Failed to send task message"
                )
            
            response = self.wait_for_response(task_id, TEST_CONFIG['test_timeout'])
            response_time = time.time() - start_time
            
            if response is None:
                return TestResult(
                    test_name="thonoc_assign_consequence",
                    subsystem="THONOC",
                    task_type="assign_consequence",
                    success=False,
                    response_time=response_time,
                    error_message="No response received within timeout"
                )
            
            success = (response.get('status') == 'success' and 
                      'consequence_assignment' in response.get('result', {}))
            
            return TestResult(
                test_name="thonoc_assign_consequence",
                subsystem="THONOC",
                task_type="assign_consequence",
                success=success,
                response_time=response_time,
                result_data=response.get('result'),
                error_message=None if success else response.get('result', {}).get('error')
            )
            
        except Exception as e:
            return TestResult(
                test_name="thonoc_assign_consequence",
                subsystem="THONOC",
                task_type="assign_consequence",
                success=False,
                response_time=time.time() - start_time,
                error_message=str(e)
            )
    
    def run_unit_tests(self) -> List[TestResult]:
        """Run unit tests that don't require RabbitMQ."""
        logger.info("Running unit tests...")
        unit_results = []
        
        # Test 1: Configuration validation
        try:
            from shared.worker_config import validate_config, WorkerType
            config_valid = validate_config()
            
            unit_results.append(TestResult(
                test_name="config_validation",
                subsystem="SHARED",
                task_type="validation",
                success=config_valid,
                response_time=0.0,
                error_message=None if config_valid else "Configuration validation failed"
            ))
            
        except Exception as e:
            unit_results.append(TestResult(
                test_name="config_validation",
                subsystem="SHARED",
                task_type="validation",
                success=False,
                response_time=0.0,
                error_message=str(e)
            ))
        
        # Test 2: Worker imports
        for subsystem, module_name in [
            ("TETRAGNOS", "subsystems.tetragnos"),
            ("TELOS", "subsystems.telos"),
            ("THONOC", "subsystems.thonoc")
        ]:
            try:
                __import__(module_name)
                unit_results.append(TestResult(
                    test_name=f"{subsystem.lower()}_import",
                    subsystem=subsystem,
                    task_type="import",
                    success=True,
                    response_time=0.0
                ))
            except Exception as e:
                unit_results.append(TestResult(
                    test_name=f"{subsystem.lower()}_import",
                    subsystem=subsystem,
                    task_type="import",
                    success=False,
                    response_time=0.0,
                    error_message=str(e)
                ))
        
        return unit_results
    
    def run_integration_tests(self) -> List[TestResult]:
        """Run integration tests with RabbitMQ communication."""
        if not PIKA_AVAILABLE:
            logger.warning("Skipping integration tests - pika not available")
            return []
        
        logger.info("Running integration tests...")
        
        if not self.setup_rabbitmq():
            logger.error("Failed to setup RabbitMQ for integration tests")
            return []
        
        try:
            # Run tests concurrently for better performance
            integration_tests = [
                self.test_tetragnos_cluster_texts,
                self.test_telos_predict_outcomes,
                self.test_thonoc_construct_proof,
                self.test_thonoc_assign_consequence
            ]
            
            results = []
            with ThreadPoolExecutor(max_workers=TEST_CONFIG['max_workers']) as executor:
                future_to_test = {executor.submit(test): test.__name__ for test in integration_tests}
                
                for future in as_completed(future_to_test):
                    test_name = future_to_test[future]
                    try:
                        result = future.result()
                        results.append(result)
                        logger.info(f"Completed test: {test_name} - {'PASS' if result.success else 'FAIL'}")
                    except Exception as e:
                        logger.error(f"Test {test_name} raised exception: {e}")
                        results.append(TestResult(
                            test_name=test_name,
                            subsystem="UNKNOWN",
                            task_type="unknown",
                            success=False,
                            response_time=0.0,
                            error_message=str(e)
                        ))
            
            return results
            
        finally:
            self.teardown_rabbitmq()
    
    def run_all_tests(self) -> Dict[str, Any]:
        """Run complete test suite and return summary."""
        logger.info("Starting LOGOS AGI Worker Test Suite...")
        
        start_time = time.time()
        
        # Run unit tests
        unit_results = self.run_unit_tests()
        
        # Run integration tests
        integration_results = self.run_integration_tests()
        
        # Combine results
        all_results = unit_results + integration_results
        total_time = time.time() - start_time
        
        # Generate summary
        total_tests = len(all_results)
        passed_tests = sum(1 for r in all_results if r.success)
        failed_tests = total_tests - passed_tests
        
        summary = {
            'total_tests': total_tests,
            'passed': passed_tests,
            'failed': failed_tests,
            'success_rate': (passed_tests / total_tests * 100) if total_tests > 0 else 0,
            'total_time': total_time,
            'average_response_time': sum(r.response_time for r in all_results) / len(all_results) if all_results else 0,
            'test_results': all_results
        }
        
        # Log summary
        logger.info(f"Test Suite Complete:")
        logger.info(f"  Total Tests: {total_tests}")
        logger.info(f"  Passed: {passed_tests}")
        logger.info(f"  Failed: {failed_tests}")
        logger.info(f"  Success Rate: {summary['success_rate']:.1f}%")
        logger.info(f"  Total Time: {total_time:.2f}s")
        
        # Log failed tests
        for result in all_results:
            if not result.success:
                logger.error(f"FAILED: {result.test_name} ({result.subsystem}) - {result.error_message}")
        
        return summary

def main():
    """Main test runner."""
    test_suite = WorkerTestSuite()
    summary = test_suite.run_all_tests()
    
    # Exit with appropriate code
    exit_code = 0 if summary['failed'] == 0 else 1
    return exit_code

if __name__ == '__main__':
    exit(main())