"""
Test Multi-Agent LOGOS System - Comprehensive validation

This module tests the multi-agent communication, IEL synchronization, and
distributed reasoning capabilities of the LOGOS AGI system.

Test Coverage:
1. Agent discovery and handshake validation
2. IEL exchange and synchronization protocols
3. Trust score adjustments and reputation management
4. Degraded agent simulation and recovery behavior
5. Conflict resolution and consensus mechanisms
6. Security validation and cryptographic verification

Part of the LOGOS AGI v1.0 multi-agent reasoning framework.
"""

import unittest
import json
import time
import threading
import tempfile
import socket
from datetime import datetime, timedelta
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
import sys
import os

# Add parent directory to path for imports
current_dir = Path(__file__).parent
sys.path.insert(0, str(current_dir))

from logos_core.multi_agent.agent_communication import (
    AgentCommunicationManager,
    AgentNode,
    AgentCapabilities,
    TrustMetrics
)

from logos_core.multi_agent.iel_sync_protocol import (
    IELSyncProtocol,
    SignedIEL,
    IELSignature,
    SyncMode,
    ConflictResolution,
    SyncRequest,
    SyncResponse
)

class TestAgentCommunication(unittest.TestCase):
    """Test agent communication and discovery"""

    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()

        # Create test agent managers on different ports
        self.agent1 = AgentCommunicationManager(
            agent_id="test-agent-1",
            host="localhost",
            port=8751
        )

        self.agent2 = AgentCommunicationManager(
            agent_id="test-agent-2",
            host="localhost",
            port=8752
        )

        # Override capabilities for testing
        self.agent1.capabilities.specializations = ["modal_logic", "autonomous_learning"]
        self.agent2.capabilities.specializations = ["temporal_logic", "coherence_optimization"]

    def tearDown(self):
        """Clean up test fixtures"""
        try:
            self.agent1.stop_server()
            self.agent2.stop_server()
        except Exception:
            pass

    def test_agent_node_creation(self):
        """Test agent node creation and serialization"""
        capabilities = AgentCapabilities(
            domains=["modal_logic", "temporal_logic"],
            evaluators=["ModalLogicEvaluator"],
            generators=["IELGenerator"],
            max_concurrent_requests=5,
            specializations=["test_spec"],
            version="1.0.0"
        )

        agent = AgentNode(
            agent_id="test-agent",
            host="localhost",
            port=8750,
            capabilities=capabilities
        )

        # Test serialization
        agent_dict = agent.to_dict()
        self.assertEqual(agent_dict['agent_id'], "test-agent")
        self.assertEqual(agent_dict['port'], 8750)
        self.assertIn('capabilities', agent_dict)

        # Test deserialization
        restored_agent = AgentNode.from_dict(agent_dict)
        self.assertEqual(restored_agent.agent_id, agent.agent_id)
        self.assertEqual(restored_agent.capabilities.version, "1.0.0")

    def test_trust_metrics(self):
        """Test trust metric calculations and updates"""
        trust = TrustMetrics(
            trust_score=0.5,
            successful_exchanges=0,
            failed_exchanges=0,
            invalid_iels_sent=0,
            response_time_avg=0.0,
            last_successful_contact=datetime.now()
        )

        # Test successful exchange
        trust.update_success(1.5)
        self.assertEqual(trust.successful_exchanges, 1)
        self.assertEqual(trust.response_time_avg, 1.5)
        self.assertGreater(trust.trust_score, 0.5)

        # Test failed exchange
        original_score = trust.trust_score
        trust.update_failure("timeout")
        self.assertEqual(trust.failed_exchanges, 1)
        self.assertLess(trust.trust_score, original_score)

        # Test reliability calculation
        reliability = trust.calculate_reliability()
        self.assertEqual(reliability, 0.5)  # 1 success, 1 failure

    def test_server_startup_and_shutdown(self):
        """Test agent server lifecycle"""
        # Test startup
        success = self.agent1.start_server()
        self.assertTrue(success)
        self.assertTrue(self.agent1.running)

        # Test connection
        time.sleep(0.5)  # Allow server to start

        # Test shutdown
        self.agent1.stop_server()
        self.assertFalse(self.agent1.running)

    def test_agent_handshake(self):
        """Test agent discovery and handshake"""
        # Start both agents
        self.assertTrue(self.agent1.start_server())
        self.assertTrue(self.agent2.start_server())

        time.sleep(0.5)  # Allow servers to start

        # Create agent node for agent2
        agent2_node = AgentNode(
            agent_id=self.agent2.agent_id,
            host="localhost",
            port=8752,
            capabilities=self.agent2.capabilities
        )

        # Register agent2 with agent1
        self.agent1.register_agent(agent2_node)

        # Test ping
        response = self.agent1._send_request(agent2_node, "ping", {"timestamp": time.time()})
        self.assertIsNotNone(response)
        self.assertEqual(response.get("status"), "ok")
        self.assertEqual(response.get("agent_id"), self.agent2.agent_id)

        # Test capabilities request
        response = self.agent1._send_request(agent2_node, "get_capabilities", {})
        self.assertIsNotNone(response)
        self.assertEqual(response.get("agent_id"), self.agent2.agent_id)
        self.assertIn("capabilities", response)

    def test_static_agent_discovery(self):
        """Test static agent configuration discovery"""
        # Create test agent configuration
        agents_config = {
            "agents": [
                {
                    "agent_id": "test-remote-agent",
                    "host": "localhost",
                    "port": 8753,
                    "capabilities": {
                        "domains": ["modal_logic"],
                        "evaluators": ["ModalLogicEvaluator"],
                        "generators": ["IELGenerator"],
                        "max_concurrent_requests": 10,
                        "specializations": ["remote_reasoning"],
                        "version": "1.0.0"
                    }
                }
            ]
        }

        config_file = Path(self.temp_dir) / "test_agents.json"
        with open(config_file, 'w') as f:
            json.dump(agents_config, f)

        # Test discovery
        self.agent1.discover_agents(str(config_file))

        # Check if agent was discovered
        self.assertIn("test-remote-agent", self.agent1.agents)
        discovered_agent = self.agent1.agents["test-remote-agent"]
        self.assertEqual(discovered_agent.port, 8753)
        self.assertIsNotNone(discovered_agent.capabilities)

class TestIELSynchronization(unittest.TestCase):
    """Test IEL synchronization protocol"""

    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()

        # Create mock communication manager
        self.comm_manager = Mock(spec=AgentCommunicationManager)
        self.comm_manager.agent_id = "test-sync-agent"
        self.comm_manager.get_public_key_pem.return_value = "mock-public-key"
        self.comm_manager.private_key = None  # Use mock signatures

        # Create mock registry
        self.registry = Mock()
        self.registry.list_candidates.return_value = []
        self.registry.register_iel.return_value = True

        # Create sync protocol
        self.sync_protocol = IELSyncProtocol(self.comm_manager, self.registry)

    def test_signed_iel_creation(self):
        """Test creation and validation of signed IELs"""
        # Create mock IEL candidate
        iel_candidate = Mock()
        iel_candidate.id = "test-iel-1"
        iel_candidate.rule_content = "[]p -> p"
        iel_candidate.domain = "modal_logic"
        iel_candidate.confidence = 0.8
        iel_candidate.metadata = {}

        # Create signed IEL
        signed_iel = self.sync_protocol.create_signed_iel(iel_candidate)

        # Verify signed IEL properties
        self.assertEqual(signed_iel.iel_id, "test-iel-1")
        self.assertEqual(signed_iel.iel_content, "[]p -> p")
        self.assertEqual(signed_iel.domain, "modal_logic")
        self.assertEqual(signed_iel.origin_agent, "test-sync-agent")
        self.assertIsNotNone(signed_iel.signature)

        # Test serialization
        iel_dict = signed_iel.to_dict()
        self.assertIn('signature', iel_dict)
        self.assertIn('created_at', iel_dict)

        # Test deserialization
        restored_iel = SignedIEL.from_dict(iel_dict)
        self.assertEqual(restored_iel.iel_id, signed_iel.iel_id)
        self.assertEqual(restored_iel.iel_content, signed_iel.iel_content)

    def test_sync_request_response(self):
        """Test sync request and response handling"""
        # Create sync request
        request = SyncRequest(
            request_id="test-sync-1",
            requesting_agent="requester-agent",
            mode=SyncMode.PULL,
            iel_filters={"min_coherence": 0.6},
            max_iels=10
        )

        # Test serialization
        request_dict = request.to_dict()
        self.assertEqual(request_dict['mode'], 'pull')

        # Test deserialization
        restored_request = SyncRequest.from_dict(request_dict)
        self.assertEqual(restored_request.mode, SyncMode.PULL)

        # Create sync response
        response = SyncResponse(
            request_id="test-sync-1",
            responding_agent="responder-agent",
            status="success",
            iels=[],
            conflicts=[],
            sync_timestamp=time.time(),
            total_available=0
        )

        # Test serialization
        response_dict = response.to_dict()
        self.assertEqual(response_dict['status'], 'success')

    def test_conflict_detection(self):
        """Test IEL conflict detection"""
        # Create existing IEL
        existing_iel = Mock()
        existing_iel.rule_content = "[]p -> p"
        existing_iel.domain = "modal_logic"

        # Create new IEL with same content
        new_iel = SignedIEL(
            iel_id="new-iel",
            iel_content="[]p -> p",  # Same content
            domain="modal_logic",
            origin_agent="other-agent",
            version=1,
            coherence_score=0.8,
            evaluation_context={},
            dependencies=[],
            signature=IELSignature("mock", "MOCK", "hash", time.time()),
            created_at=datetime.now(),
            sync_metadata={}
        )

        # Test conflict detection
        conflict = self.sync_protocol._detect_conflict(new_iel, [existing_iel])
        self.assertIsNotNone(conflict)
        self.assertEqual(conflict['type'], 'duplicate_content')

    def test_conflict_resolution_strategies(self):
        """Test different conflict resolution strategies"""
        # Create mock conflict
        existing_iel = Mock()
        existing_iel.rule_content = "[]p -> p"
        existing_iel.confidence = 0.7

        new_iel = Mock()
        new_iel.iel_content = "[]p -> p"
        new_iel.coherence_score = 0.9

        conflict = {
            "type": "duplicate_content",
            "existing_iel": existing_iel,
            "new_iel": new_iel
        }

        source_agent = Mock()
        source_agent.agent_id = "source"
        source_agent.trust_metrics = Mock()
        source_agent.trust_metrics.trust_score = 0.8

        # Test coherence-based resolution
        self.sync_protocol.config["conflict_resolution"] = ConflictResolution.COHERENCE_SCORE
        # This would normally make a decision, but we're just testing it doesn't crash
        self.sync_protocol._handle_conflict(conflict, source_agent)

        # Test trust-based resolution
        self.sync_protocol.config["conflict_resolution"] = ConflictResolution.TRUST_WEIGHTED
        self.sync_protocol._handle_conflict(conflict, source_agent)

class TestMultiAgentIntegration(unittest.TestCase):
    """Test multi-agent system integration"""

    def setUp(self):
        """Set up integration test environment"""
        self.temp_dir = tempfile.mkdtemp()

        # Create multiple agents for testing
        self.agents = []
        for i in range(3):
            agent = AgentCommunicationManager(
                agent_id=f"test-agent-{i+1}",
                host="localhost",
                port=8750 + i
            )
            self.agents.append(agent)

    def tearDown(self):
        """Clean up integration test environment"""
        for agent in self.agents:
            try:
                agent.stop_server()
            except Exception:
                pass

    def test_multi_agent_network_formation(self):
        """Test formation of multi-agent network"""
        # Start all agents
        for agent in self.agents:
            success = agent.start_server()
            self.assertTrue(success, f"Failed to start {agent.agent_id}")

        time.sleep(0.5)  # Allow servers to start

        # Connect agents to each other
        for i, agent in enumerate(self.agents):
            for j, other_agent in enumerate(self.agents):
                if i != j:
                    other_node = AgentNode(
                        agent_id=other_agent.agent_id,
                        host="localhost",
                        port=8750 + j,
                        capabilities=other_agent.capabilities
                    )
                    agent.register_agent(other_node)

        # Verify network formation
        for agent in self.agents:
            self.assertEqual(len(agent.agents), len(self.agents) - 1)

            # Test network status
            status = agent.get_network_status()
            self.assertEqual(status["total_agents"], len(self.agents) - 1)

    def test_distributed_handshake(self):
        """Test handshake across multiple agents"""
        # Start agents
        for agent in self.agents[:2]:  # Use first two agents
            agent.start_server()

        time.sleep(0.5)

        # Create agent nodes
        agent1_node = AgentNode(
            agent_id=self.agents[0].agent_id,
            host="localhost",
            port=8750,
            capabilities=self.agents[0].capabilities
        )

        agent2_node = AgentNode(
            agent_id=self.agents[1].agent_id,
            host="localhost",
            port=8751,
            capabilities=self.agents[1].capabilities
        )

        # Register agents with each other
        self.agents[0].register_agent(agent2_node)
        self.agents[1].register_agent(agent1_node)

        # Test bidirectional communication
        response1 = self.agents[0]._send_request(agent2_node, "ping", {"timestamp": time.time()})
        response2 = self.agents[1]._send_request(agent1_node, "ping", {"timestamp": time.time()})

        self.assertIsNotNone(response1)
        self.assertIsNotNone(response2)
        self.assertEqual(response1.get("status"), "ok")
        self.assertEqual(response2.get("status"), "ok")

class TestDegradedAgentScenarios(unittest.TestCase):
    """Test degraded agent behavior and recovery"""

    def setUp(self):
        """Set up degraded agent test scenarios"""
        self.healthy_agent = AgentCommunicationManager(
            agent_id="healthy-agent",
            host="localhost",
            port=8760
        )

        self.degraded_node = AgentNode(
            agent_id="degraded-agent",
            host="localhost",
            port=9999,  # Non-existent port
            capabilities=AgentCapabilities(
                domains=["modal_logic"],
                evaluators=["ModalLogicEvaluator"],
                generators=["IELGenerator"],
                max_concurrent_requests=5,
                specializations=["test"],
                version="1.0.0"
            )
        )

    def tearDown(self):
        """Clean up degraded agent tests"""
        try:
            self.healthy_agent.stop_server()
        except Exception:
            pass

    def test_unresponsive_agent_detection(self):
        """Test detection of unresponsive agents"""
        # Start healthy agent
        self.healthy_agent.start_server()
        time.sleep(0.5)

        # Register degraded agent
        self.healthy_agent.register_agent(self.degraded_node)

        # Try to communicate with degraded agent
        response = self.healthy_agent._send_request(
            self.degraded_node,
            "ping",
            {"timestamp": time.time()}
        )

        # Should fail to connect
        self.assertIsNone(response)

        # Check trust metrics were updated
        self.assertEqual(self.degraded_node.trust_metrics.failed_exchanges, 1)
        self.assertLess(self.degraded_node.trust_metrics.trust_score, 0.5)

    def test_agent_recovery_behavior(self):
        """Test agent recovery after temporary failure"""
        # Start healthy agent
        self.healthy_agent.start_server()
        time.sleep(0.5)

        # Create a temporarily offline agent
        temp_agent = AgentCommunicationManager(
            agent_id="temp-agent",
            host="localhost",
            port=8761
        )

        temp_node = AgentNode(
            agent_id="temp-agent",
            host="localhost",
            port=8761,
            capabilities=temp_agent.capabilities
        )

        # Register but don't start temp agent yet
        self.healthy_agent.register_agent(temp_node)

        # Communication should fail
        response = self.healthy_agent._send_request(temp_node, "ping", {"timestamp": time.time()})
        self.assertIsNone(response)

        # Now start temp agent
        temp_agent.start_server()
        time.sleep(0.5)

        # Communication should now succeed
        response = self.healthy_agent._send_request(temp_node, "ping", {"timestamp": time.time()})
        self.assertIsNotNone(response)

        # Clean up
        temp_agent.stop_server()

class TestSecurityAndValidation(unittest.TestCase):
    """Test security features and validation"""

    def setUp(self):
        """Set up security test environment"""
        self.comm_manager = Mock(spec=AgentCommunicationManager)
        self.comm_manager.agent_id = "secure-agent"
        self.comm_manager.get_public_key_pem.return_value = "mock-public-key"
        self.comm_manager.private_key = None

        self.registry = Mock()
        self.sync_protocol = IELSyncProtocol(self.comm_manager, self.registry)

    def test_signature_validation(self):
        """Test IEL signature validation"""
        # Create signed IEL with mock signature
        signed_iel = SignedIEL(
            iel_id="secure-iel",
            iel_content="[]p -> p",
            domain="modal_logic",
            origin_agent="trusted-agent",
            version=1,
            coherence_score=0.8,
            evaluation_context={},
            dependencies=[],
            signature=IELSignature(
                signature="mock_signature",
                algorithm="MOCK-RSA-PSS",
                public_key_hash="mock_hash",
                timestamp=time.time()
            ),
            created_at=datetime.now(),
            sync_metadata={}
        )

        # Test signature verification (should pass with mock)
        is_valid = signed_iel.verify_signature("mock-public-key")
        self.assertTrue(is_valid)  # Mock always returns True

    def test_trust_threshold_enforcement(self):
        """Test enforcement of trust thresholds"""
        # Create low-trust agent
        low_trust_agent = AgentNode(
            agent_id="low-trust",
            host="localhost",
            port=8765
        )
        low_trust_agent.trust_metrics.trust_score = 0.1  # Below threshold

        # Create high-trust agent
        high_trust_agent = AgentNode(
            agent_id="high-trust",
            host="localhost",
            port=8766
        )
        high_trust_agent.trust_metrics.trust_score = 0.9  # Above threshold

        # Test trust checks
        self.assertFalse(low_trust_agent.is_trusted)
        self.assertTrue(high_trust_agent.is_trusted)

def run_multi_agent_tests():
    """Run all multi-agent tests"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Add all test classes
    test_classes = [
        TestAgentCommunication,
        TestIELSynchronization,
        TestMultiAgentIntegration,
        TestDegradedAgentScenarios,
        TestSecurityAndValidation
    ]

    for test_class in test_classes:
        tests = loader.loadTestsFromTestCase(test_class)
        suite.addTests(tests)

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stdout)
    result = runner.run(suite)

    # Return summary
    return {
        "tests_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "success": result.wasSuccessful(),
        "failure_details": result.failures + result.errors
    }

if __name__ == "__main__":
    print("LOGOS AGI Multi-Agent System - Test Suite")
    print("=" * 50)

    # Run comprehensive tests
    summary = run_multi_agent_tests()

    print(f"\nMulti-Agent Test Summary:")
    print(f"Tests Run: {summary['tests_run']}")
    print(f"Failures: {summary['failures']}")
    print(f"Errors: {summary['errors']}")
    print(f"Overall Success: {summary['success']}")

    if not summary['success']:
        print(f"\nFailure Details:")
        for failure in summary['failure_details']:
            print(f"- {failure[0]}: {failure[1]}")

    # Exit with appropriate code
    sys.exit(0 if summary['success'] else 1)
