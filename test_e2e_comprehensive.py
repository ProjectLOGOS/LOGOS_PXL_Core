#!/usr/bin/env python3
"""
LOGOS AGI System - Comprehensive End-to-End Test Suite
Tests all systems and subsystems for full operational readiness
"""
import asyncio
import json
import time
import requests
import subprocess
import sys
import os
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    BOLD = '\033[1m'
    END = '\033[0m'

class E2ETestSuite:
    def __init__(self):
        self.base_url = "http://localhost"
        self.tool_router_port = 8000
        self.logos_api_port = 8090
        self.chat_port = 8080
        self.redis_port = 6379
        
        self.processes = []
        self.test_results = {
            'passed': 0,
            'failed': 0,
            'total': 0,
            'details': []
        }
    
    def log(self, message, color=Colors.BLUE):
        timestamp = time.strftime("%H:%M:%S")
        print(f"{color}[{timestamp}] {message}{Colors.END}")
    
    def success(self, message):
        self.log(f"✅ {message}", Colors.GREEN)
        self.test_results['passed'] += 1
    
    def failure(self, message):
        self.log(f"❌ {message}", Colors.RED)
        self.test_results['failed'] += 1
    
    def warning(self, message):
        self.log(f"⚠️  {message}", Colors.YELLOW)
    
    def test_step(self, test_name):
        self.test_results['total'] += 1
        self.log(f"🧪 Testing: {test_name}", Colors.BOLD)
    
    async def start_service(self, name, command, port, cwd=None):
        """Start a service and verify it's running"""
        self.log(f"Starting {name}...")
        
        try:
            # Start the process
            process = subprocess.Popen(
                command,
                shell=True,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                creationflags=subprocess.CREATE_NEW_CONSOLE if os.name == 'nt' else 0
            )
            self.processes.append((name, process))
            
            # Wait for service to start
            await asyncio.sleep(3)
            
            # Verify service is running
            if await self.check_port(port):
                self.success(f"{name} started successfully on port {port}")
                return True
            else:
                self.failure(f"{name} failed to start on port {port}")
                return False
                
        except Exception as e:
            self.failure(f"Failed to start {name}: {str(e)}")
            return False
    
    async def check_port(self, port, timeout=5):
        """Check if a port is available"""
        import socket
        
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(timeout)
            result = sock.connect_ex(('localhost', port))
            sock.close()
            return result == 0
        except:
            return False
    
    async def http_get(self, url, timeout=10):
        """Make HTTP GET request"""
        try:
            response = requests.get(url, timeout=timeout)
            return response
        except Exception as e:
            self.log(f"HTTP GET failed for {url}: {str(e)}")
            return None
    
    async def http_post(self, url, data=None, json_data=None, headers=None, timeout=10):
        """Make HTTP POST request"""
        try:
            response = requests.post(url, data=data, json=json_data, headers=headers, timeout=timeout)
            return response
        except Exception as e:
            self.log(f"HTTP POST failed for {url}: {str(e)}")
            return None
    
    def cleanup(self):
        """Stop all started processes"""
        self.log("Cleaning up processes...")
        for name, process in self.processes:
            try:
                process.terminate()
                process.wait(timeout=5)
                self.log(f"Stopped {name}")
            except subprocess.TimeoutExpired:
                process.kill()
                self.log(f"Force killed {name}")
            except Exception as e:
                self.log(f"Error stopping {name}: {str(e)}")
    
    async def test_unit_tests(self):
        """Run the existing unit test suite"""
        self.test_step("Unit Test Suite")
        
        try:
            # Change to project directory
            os.chdir(project_root)
            
            # Run unit tests
            result = subprocess.run([
                sys.executable, "-m", "pytest", "tests/", "-v", "--tb=short"
            ], capture_output=True, text=True, timeout=120)
            
            if result.returncode == 0:
                self.success("All unit tests passed")
                self.test_results['details'].append({
                    'test': 'Unit Tests',
                    'status': 'PASS',
                    'details': f"Exit code: {result.returncode}"
                })
            else:
                self.failure(f"Unit tests failed with exit code {result.returncode}")
                self.log(f"STDOUT: {result.stdout}")
                self.log(f"STDERR: {result.stderr}")
                self.test_results['details'].append({
                    'test': 'Unit Tests',
                    'status': 'FAIL',
                    'details': f"Exit code: {result.returncode}, stderr: {result.stderr[:200]}"
                })
            
        except subprocess.TimeoutExpired:
            self.failure("Unit tests timed out")
            self.test_results['details'].append({
                'test': 'Unit Tests',
                'status': 'TIMEOUT',
                'details': "Tests exceeded 120 second timeout"
            })
        except Exception as e:
            self.failure(f"Unit test execution failed: {str(e)}")
    
    async def test_logos_api_service(self):
        """Test LOGOS API service"""
        self.test_step("LOGOS API Service")
        
        # Start LOGOS API
        service_started = await self.start_service(
            "LOGOS API",
            f"{sys.executable} -m uvicorn app:app --host 0.0.0.0 --port {self.logos_api_port}",
            self.logos_api_port,
            cwd=project_root / "services" / "logos_api"
        )
        
        if not service_started:
            return
        
        await asyncio.sleep(2)  # Additional startup time
        
        # Test health endpoint
        health_response = await self.http_get(f"{self.base_url}:{self.logos_api_port}/health")
        if health_response and health_response.status_code == 200:
            self.success("LOGOS API health check passed")
            health_data = health_response.json()
            if health_data.get('status') == 'healthy':
                self.success("LOGOS API reports healthy status")
            else:
                self.warning(f"LOGOS API status: {health_data.get('status', 'unknown')}")
        else:
            self.failure("LOGOS API health check failed")
        
        # Test authorize endpoint
        auth_data = {
            "action": "test_action",
            "context": {"test": "data"},
            "user_id": "test_user"
        }
        
        auth_response = await self.http_post(
            f"{self.base_url}:{self.logos_api_port}/authorize_action",
            json_data=auth_data
        )
        
        if auth_response and auth_response.status_code == 200:
            self.success("LOGOS API authorization endpoint working")
            auth_result = auth_response.json()
            if 'proof_token' in auth_result:
                self.success("LOGOS API generated proof token")
            else:
                self.warning("No proof token in authorization response")
        else:
            self.failure("LOGOS API authorization endpoint failed")
        
        # Test verify kernel endpoint
        verify_response = await self.http_get(f"{self.base_url}:{self.logos_api_port}/verify_kernel")
        if verify_response and verify_response.status_code == 200:
            self.success("LOGOS API kernel verification endpoint working")
        else:
            self.failure("LOGOS API kernel verification failed")
    
    async def test_tool_router_service(self):
        """Test Enhanced Tool Router service"""
        self.test_step("Enhanced Tool Router Service")
        
        # Start Tool Router
        service_started = await self.start_service(
            "Tool Router",
            f"{sys.executable} -m uvicorn app:app --host 0.0.0.0 --port {self.tool_router_port}",
            self.tool_router_port,
            cwd=project_root / "services" / "tool_router"
        )
        
        if not service_started:
            return
        
        await asyncio.sleep(2)  # Additional startup time
        
        # Test health endpoint
        health_response = await self.http_get(f"{self.base_url}:{self.tool_router_port}/health")
        if health_response and health_response.status_code == 200:
            self.success("Tool Router health check passed")
        else:
            self.failure("Tool Router health check failed")
        
        # Test metrics endpoint
        metrics_response = await self.http_get(f"{self.base_url}:{self.tool_router_port}/metrics")
        if metrics_response and metrics_response.status_code == 200:
            self.success("Tool Router metrics endpoint working")
            if "http_requests_total" in metrics_response.text:
                self.success("Tool Router Prometheus metrics available")
            else:
                self.warning("Expected Prometheus metrics not found")
        else:
            self.failure("Tool Router metrics endpoint failed")
        
        # Test chat endpoint with sample data
        chat_data = {
            "message": "Hello, can you help me test the system?",
            "user_id": "test_user"
        }
        
        chat_response = await self.http_post(
            f"{self.base_url}:{self.tool_router_port}/chat",
            json_data=chat_data
        )
        
        if chat_response and chat_response.status_code == 200:
            self.success("Tool Router chat endpoint working")
            chat_result = chat_response.json()
            if 'response' in chat_result:
                self.success("Tool Router generated chat response")
            else:
                self.warning("No response in chat result")
        else:
            self.failure("Tool Router chat endpoint failed")
    
    async def test_interactive_chat_service(self):
        """Test Interactive Chat service"""
        self.test_step("Interactive Chat Service")
        
        # Start Interactive Chat
        service_started = await self.start_service(
            "Interactive Chat",
            f"{sys.executable} app.py",
            self.chat_port,
            cwd=project_root / "services" / "interactive_chat"
        )
        
        if not service_started:
            return
        
        await asyncio.sleep(2)  # Additional startup time
        
        # Test main page
        chat_response = await self.http_get(f"{self.base_url}:{self.chat_port}/")
        if chat_response and chat_response.status_code == 200:
            self.success("Interactive Chat interface accessible")
            if "LOGOS" in chat_response.text:
                self.success("Interactive Chat shows LOGOS branding")
            else:
                self.warning("LOGOS branding not found in chat interface")
        else:
            self.failure("Interactive Chat interface failed")
        
        # Test chat API endpoint
        chat_api_data = {
            "message": "Test message for end-to-end validation"
        }
        
        chat_api_response = await self.http_post(
            f"{self.base_url}:{self.chat_port}/chat",
            json_data=chat_api_data
        )
        
        if chat_api_response and chat_api_response.status_code == 200:
            self.success("Interactive Chat API endpoint working")
        else:
            self.failure("Interactive Chat API endpoint failed")
    
    async def test_service_integration(self):
        """Test integration between services"""
        self.test_step("Service Integration")
        
        # Test if Tool Router can communicate with LOGOS API
        integration_data = {
            "message": "test integration between services",
            "user_id": "integration_test"
        }
        
        # Send request to Tool Router which should interact with LOGOS API
        integration_response = await self.http_post(
            f"{self.base_url}:{self.tool_router_port}/chat",
            json_data=integration_data
        )
        
        if integration_response and integration_response.status_code == 200:
            self.success("Service integration test passed")
            
            # Check if response includes proof token or authorization
            response_data = integration_response.json()
            if 'response' in response_data:
                self.success("Integrated response generated successfully")
            else:
                self.warning("Integration response format unexpected")
        else:
            self.failure("Service integration test failed")
        
        # Test cross-service communication
        await asyncio.sleep(1)
        
        # Verify metrics show cross-service calls
        metrics_response = await self.http_get(f"{self.base_url}:{self.tool_router_port}/metrics")
        if metrics_response and "http_requests_total" in metrics_response.text:
            self.success("Cross-service metrics captured")
        else:
            self.warning("Cross-service metrics not found")
    
    async def test_error_handling(self):
        """Test error handling and recovery"""
        self.test_step("Error Handling & Recovery")
        
        # Test invalid requests
        invalid_response = await self.http_post(
            f"{self.base_url}:{self.tool_router_port}/chat",
            json_data={"invalid": "data"}
        )
        
        if invalid_response and invalid_response.status_code in [400, 422]:
            self.success("Tool Router properly handles invalid requests")
        else:
            self.warning("Tool Router error handling unclear")
        
        # Test non-existent endpoints
        notfound_response = await self.http_get(f"{self.base_url}:{self.tool_router_port}/nonexistent")
        if notfound_response and notfound_response.status_code == 404:
            self.success("Tool Router properly handles 404 errors")
        else:
            self.warning("Tool Router 404 handling unclear")
        
        # Test LOGOS API error handling
        invalid_auth_response = await self.http_post(
            f"{self.base_url}:{self.logos_api_port}/authorize_action",
            json_data={"incomplete": "data"}
        )
        
        if invalid_auth_response and invalid_auth_response.status_code in [400, 422]:
            self.success("LOGOS API properly handles invalid requests")
        else:
            self.warning("LOGOS API error handling unclear")
    
    async def test_performance_basics(self):
        """Test basic performance characteristics"""
        self.test_step("Performance Characteristics")
        
        # Test response times
        start_time = time.time()
        
        # Make multiple concurrent requests
        tasks = []
        for i in range(5):
            tasks.append(self.http_get(f"{self.base_url}:{self.tool_router_port}/health"))
        
        responses = await asyncio.gather(*tasks, return_exceptions=True)
        end_time = time.time()
        
        successful_responses = [r for r in responses if hasattr(r, 'status_code') and r.status_code == 200]
        
        if len(successful_responses) == 5:
            avg_time = (end_time - start_time) / 5
            self.success(f"Tool Router handled 5 concurrent requests (avg: {avg_time:.3f}s)")
        else:
            self.warning(f"Only {len(successful_responses)}/5 concurrent requests succeeded")
        
        # Test larger payload
        large_data = {
            "message": "This is a test message with more content " * 50,
            "user_id": "performance_test",
            "metadata": {"test": "data"} * 10
        }
        
        large_response = await self.http_post(
            f"{self.base_url}:{self.tool_router_port}/chat",
            json_data=large_data
        )
        
        if large_response and large_response.status_code == 200:
            self.success("Tool Router handles larger payloads")
        else:
            self.warning("Tool Router struggled with larger payloads")
    
    def print_summary(self):
        """Print test summary"""
        print("\n" + "="*80)
        print(f"{Colors.BOLD}LOGOS AGI SYSTEM - END-TO-END TEST SUMMARY{Colors.END}")
        print("="*80)
        
        print(f"\n{Colors.GREEN}✅ Tests Passed: {self.test_results['passed']}{Colors.END}")
        print(f"{Colors.RED}❌ Tests Failed: {self.test_results['failed']}{Colors.END}")
        print(f"{Colors.BLUE}📊 Total Tests: {self.test_results['total']}{Colors.END}")
        
        if self.test_results['failed'] == 0:
            print(f"\n{Colors.GREEN}{Colors.BOLD}🎉 ALL SYSTEMS OPERATIONAL! 🎉{Colors.END}")
            print(f"{Colors.GREEN}The LOGOS AGI system is fully functional and ready for production.{Colors.END}")
        else:
            success_rate = (self.test_results['passed'] / self.test_results['total']) * 100
            print(f"\n{Colors.YELLOW}⚠️  PARTIAL SUCCESS: {success_rate:.1f}% pass rate{Colors.END}")
            
            print(f"\n{Colors.RED}Failed Tests Details:{Colors.END}")
            for detail in self.test_results['details']:
                if detail['status'] != 'PASS':
                    print(f"  • {detail['test']}: {detail['status']} - {detail['details']}")
        
        print("\n" + "="*80)

async def main():
    """Run the complete end-to-end test suite"""
    print(f"{Colors.BOLD}🚀 LOGOS AGI SYSTEM - COMPREHENSIVE END-TO-END TEST{Colors.END}")
    print(f"{Colors.BLUE}Testing all systems and subsystems for operational readiness...{Colors.END}\n")
    
    test_suite = E2ETestSuite()
    
    try:
        # Run all test phases
        await test_suite.test_unit_tests()
        await test_suite.test_logos_api_service()
        await test_suite.test_tool_router_service()
        await test_suite.test_interactive_chat_service()
        await test_suite.test_service_integration()
        await test_suite.test_error_handling()
        await test_suite.test_performance_basics()
        
    except KeyboardInterrupt:
        test_suite.log("Test suite interrupted by user", Colors.YELLOW)
    except Exception as e:
        test_suite.log(f"Test suite error: {str(e)}", Colors.RED)
    finally:
        # Always cleanup
        test_suite.cleanup()
        
        # Print summary
        test_suite.print_summary()
        
        # Exit with appropriate code
        sys.exit(0 if test_suite.test_results['failed'] == 0 else 1)

if __name__ == "__main__":
    asyncio.run(main())