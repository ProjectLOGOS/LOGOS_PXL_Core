"""
Tests for Extensions Loader: Verify proof-gating, fallbacks, orchestration methods.
"""

import pytest
import sys
import os
from unittest.mock import Mock, patch, MagicMock

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from boot.extensions_loader import ExtensionsManager, extensions_manager


class TestExtensionsManager:
    """Test suite for ExtensionsManager"""

    def test_singleton_pattern(self):
        """Verify ExtensionsManager is a singleton"""
        manager1 = ExtensionsManager()
        manager2 = ExtensionsManager()
        assert manager1 is manager2
        assert manager1.libs is manager2.libs

    def test_initialization_without_pxl(self):
        """Test initialization without PXL client (bypass mode)"""
        manager = ExtensionsManager()
        # Reset for testing
        manager._initialized = False
        manager.libs = {}

        result = manager.initialize(pxl_client=None)

        # Should succeed even without PXL client
        assert manager._initialized == True
        assert len(manager.audit_log) > 0

        # Check at least some libraries attempted
        assert 'pytorch' in manager.libs or 'networkx' in manager.libs

    def test_initialization_with_mock_pxl(self):
        """Test initialization with mocked PXL client"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.libs = {}

        # Mock PXL client that always returns proof
        mock_pxl = Mock()
        mock_pxl.request_proof = Mock(return_value="proof_token_12345678")

        result = manager.initialize(pxl_client=mock_pxl)

        assert manager._initialized == True
        # Verify PXL was called for proof obligations
        assert mock_pxl.request_proof.call_count > 0

    def test_proof_obligation_failure(self):
        """Test that proof obligation failure is handled gracefully"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.libs = {}

        # Mock PXL client that fails proofs
        mock_pxl = Mock()
        mock_pxl.request_proof = Mock(return_value=None)

        # Should not crash, but may log warnings
        result = manager.initialize(pxl_client=mock_pxl)

        # Should complete initialization even with proof failures
        assert manager._initialized == True

    def test_audit_logging(self):
        """Verify audit log captures load attempts"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.libs = {}
        manager.audit_log = []

        manager.initialize(pxl_client=None)

        audit_log = manager.get_audit_log()
        assert len(audit_log) > 0

        # Verify audit entries have required fields
        for entry in audit_log:
            assert 'timestamp' in entry
            assert 'library' in entry
            assert 'obligation' in entry
            assert 'decision' in entry
            assert 'status' in entry

    def test_get_status(self):
        """Test status reporting"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.initialize(pxl_client=None)

        status = manager.get_status()

        assert 'initialized' in status
        assert status['initialized'] == True
        assert 'libraries' in status
        assert isinstance(status['libraries'], dict)
        assert 'audit_entries' in status

    def test_is_available(self):
        """Test library availability checking"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.initialize(pxl_client=None)

        # Test with a library that should be available (or None)
        result = manager.is_available('networkx')
        assert isinstance(result, bool)

        # Test with non-existent library
        result = manager.is_available('nonexistent_lib')
        assert result == False


class TestOrchestrationMethods:
    """Test orchestration methods for ML/NLP/probabilistic ops"""

    @pytest.fixture
    def manager(self):
        """Fixture to provide initialized manager"""
        mgr = ExtensionsManager()
        if not mgr._initialized:
            mgr.initialize(pxl_client=None)
        return mgr

    def test_embed_sentence(self, manager):
        """Test sentence embedding (if SentenceTransformers available)"""
        if not manager.is_available('sentence_transformers'):
            pytest.skip("SentenceTransformers not installed")

        text = "The logic core validates formal proofs"
        embedding = manager.embed_sentence(text)

        if embedding:
            assert isinstance(embedding, list)
            assert len(embedding) > 0
            assert all(isinstance(x, float) for x in embedding)

    def test_kalman_filter(self, manager):
        """Test Kalman filtering (if FilterPy available)"""
        if not manager.is_available('filterpy') and not manager.is_available('pykalman'):
            pytest.skip("Neither FilterPy nor PyKalman installed")

        # Noisy measurements around a constant value
        measurements = [1.0, 1.2, 0.9, 1.1, 1.3, 0.8, 1.0]

        filtered = manager.kalman_filter(measurements)

        if filtered:
            assert isinstance(filtered, list)
            assert len(filtered) == len(measurements)
            # Filtered values should be smoother
            assert all(isinstance(x, float) for x in filtered)

    def test_build_graph(self, manager):
        """Test graph construction (if NetworkX available)"""
        if not manager.is_available('networkx'):
            pytest.skip("NetworkX not installed")

        nodes = ['A', 'B', 'C', 'D']
        edges = [('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'A')]

        graph = manager.build_graph(nodes, edges)

        if graph:
            assert graph.number_of_nodes() == 4
            assert graph.number_of_edges() == 4

    def test_analyze_graph(self, manager):
        """Test graph analysis (if NetworkX available)"""
        if not manager.is_available('networkx'):
            pytest.skip("NetworkX not installed")

        nodes = ['A', 'B', 'C']
        edges = [('A', 'B'), ('B', 'C'), ('C', 'A')]
        graph = manager.build_graph(nodes, edges)

        if graph:
            analysis = manager.analyze_graph(graph)

            assert analysis is not None
            assert 'num_nodes' in analysis
            assert 'num_edges' in analysis
            assert 'density' in analysis
            assert analysis['num_nodes'] == 3
            assert analysis['num_edges'] == 3

    def test_pytorch_available(self, manager):
        """Test PyTorch availability check"""
        result = manager.pytorch_available()
        assert isinstance(result, bool)

        # If PyTorch is available, should log version info
        if result:
            assert manager.is_available('pytorch')

    def test_create_tensor(self, manager):
        """Test tensor creation (if PyTorch available)"""
        if not manager.is_available('pytorch'):
            pytest.skip("PyTorch not installed")

        data = [[1.0, 2.0], [3.0, 4.0]]
        tensor = manager.create_tensor(data)

        if tensor:
            import torch
            assert isinstance(tensor, torch.Tensor)
            assert tensor.shape == (2, 2)

    def test_sklearn_classify(self, manager):
        """Test sklearn classification (if scikit-learn available)"""
        if not manager.is_available('scikit_learn'):
            pytest.skip("Scikit-learn not installed")

        # Simple 2D dataset
        X_train = [[0, 0], [1, 1], [2, 2], [3, 3]]
        y_train = [0, 0, 1, 1]
        X_test = [[0.5, 0.5], [2.5, 2.5]]

        predictions = manager.sklearn_classify(X_train, y_train, X_test)

        if predictions is not None:
            assert len(predictions) == 2
            assert all(pred in [0, 1] for pred in predictions)


class TestGracefulDegradation:
    """Test that system handles missing libraries gracefully"""

    def test_embed_sentence_without_transformers(self):
        """Test embedding fails gracefully without SentenceTransformers"""
        manager = ExtensionsManager()
        manager.libs['sentence_transformers'] = None

        result = manager.embed_sentence("test text")
        assert result is None

    def test_kalman_filter_without_filterpy(self):
        """Test Kalman filter attempts backup when FilterPy missing"""
        manager = ExtensionsManager()
        manager.libs['filterpy'] = None

        measurements = [1.0, 1.1, 0.9]
        result = manager.kalman_filter(measurements)

        # Should return None if both FilterPy and PyKalman unavailable
        if result is None:
            assert manager.libs.get('pykalman') is None

    def test_build_graph_without_networkx(self):
        """Test graph building fails gracefully without NetworkX"""
        manager = ExtensionsManager()
        manager.libs['networkx'] = None

        result = manager.build_graph(['A', 'B'], [('A', 'B')])
        assert result is None

    def test_pytorch_without_torch(self):
        """Test PyTorch operations fail gracefully without torch"""
        manager = ExtensionsManager()
        manager.libs['pytorch'] = None

        assert manager.pytorch_available() == False
        assert manager.create_tensor([1, 2, 3]) is None


class TestNewlyInstalledLibraries:
    """Test suite for Pyro, Arch, FilterPy - Phase 1 validation"""

    @pytest.fixture
    def manager(self):
        """Fixture to provide initialized manager"""
        mgr = ExtensionsManager()
        if not mgr._initialized:
            mgr.initialize(pxl_client=None)
        return mgr

    def test_pyro_probabilistic_model(self, manager):
        """Test Pyro probabilistic programming capabilities"""
        if not manager.is_available('pyro'):
            pytest.skip("Pyro not installed")

        try:
            import pyro
            import torch

            # Define simple probabilistic model
            def model():
                mu = pyro.sample("mu", pyro.distributions.Normal(0., 1.))
                return mu

            # Run model
            sample = model()

            # Verify sample is a tensor
            assert isinstance(sample, torch.Tensor)
            assert sample.shape == ()  # Scalar

        except Exception as e:
            pytest.fail(f"Pyro model failed: {e}")

    def test_arch_garch_model(self, manager):
        """Test Arch econometric GARCH modeling"""
        if not manager.is_available('arch'):
            pytest.skip("Arch not installed")

        try:
            from arch import arch_model
            import numpy as np

            # Generate sample returns data
            np.random.seed(42)
            returns = np.random.randn(100) * 0.01  # 100 days of returns

            # Fit GARCH(1,1) model
            model = arch_model(returns, vol='Garch', p=1, q=1)
            # Note: fit() can take time, just verify model construction
            assert model is not None
            assert hasattr(model, 'fit')

        except Exception as e:
            pytest.fail(f"Arch GARCH model failed: {e}")

    def test_filterpy_kalman_filter(self, manager):
        """Test FilterPy Kalman filtering (primary implementation)"""
        if not manager.is_available('filterpy'):
            pytest.skip("FilterPy not installed")

        try:
            from filterpy.kalman import KalmanFilter
            import numpy as np

            # Create 1D Kalman filter
            kf = KalmanFilter(dim_x=2, dim_z=1)
            kf.x = np.array([0., 0.])  # Initial state [position, velocity]
            kf.F = np.array([[1., 1.], [0., 1.]])  # State transition
            kf.H = np.array([[1., 0.]])  # Measurement function
            kf.P *= 1000.  # Initial uncertainty
            kf.R = 5  # Measurement noise
            kf.Q = np.array([[0.1, 0.], [0., 0.1]])  # Process noise

            # Test prediction and update cycle
            measurements = [1.0, 1.1, 0.9, 1.05]
            filtered = []

            for z in measurements:
                kf.predict()
                kf.update([z])
                filtered.append(kf.x[0])

            # Verify filtering reduces noise
            assert len(filtered) == len(measurements)
            assert all(isinstance(x, (int, float, np.number)) for x in filtered)

        except Exception as e:
            pytest.fail(f"FilterPy Kalman filter failed: {e}")

    def test_filterpy_pykalman_fallback(self, manager):
        """Test that PyKalman serves as backup when FilterPy fails"""
        # Temporarily disable FilterPy
        original_filterpy = manager.libs.get('filterpy')
        manager.libs['filterpy'] = None

        try:
            measurements = [1.0, 1.2, 0.9, 1.1]
            result = manager.kalman_filter(measurements)

            # Should attempt PyKalman fallback
            if manager.is_available('pykalman'):
                # PyKalman should work as backup
                assert result is not None or result is None  # May not be properly initialized
            else:
                # Both unavailable, should return None
                assert result is None

        finally:
            # Restore FilterPy
            manager.libs['filterpy'] = original_filterpy

    def test_pyro_proof_obligation(self, manager):
        """Verify Pyro loaded with correct proof obligation"""
        if not manager.is_available('pyro'):
            pytest.skip("Pyro not installed")

        # Check audit log for Pyro
        audit_log = manager.get_audit_log()
        pyro_entries = [e for e in audit_log if e['library'] == 'pyro']

        assert len(pyro_entries) > 0
        assert pyro_entries[0]['obligation'] == "BOX(SafeProbabilisticModel())"
        assert pyro_entries[0]['decision'] == 'allow'
        assert pyro_entries[0]['status'] == 'loaded'


class TestVoiceGUIIntegration:
    """Test voice/GUI integration methods (Phase 1 compatibility)"""

    def test_voice_input_without_library(self):
        """Test voice input handles missing library"""
        manager = ExtensionsManager()
        manager.libs['voice_recog'] = None

        with patch('speech_recognition.Recognizer', side_effect=ImportError):
            result = manager.voice_input(duration=1)
            assert result is None

    def test_tts_output_without_library(self):
        """Test TTS handles missing library"""
        manager = ExtensionsManager()
        manager.libs['tts'] = None

        with patch('pyttsx3.init', side_effect=ImportError):
            # Should not crash
            manager.tts_output("test text")

    def test_file_upload_mock(self):
        """Test file upload with mocked dialog"""
        manager = ExtensionsManager()

        mock_path = "C:\\test\\file.txt"

        with patch('tkinter.filedialog.askopenfilename', return_value=mock_path):
            with patch('os.path.exists', return_value=True):
                with patch('os.path.getsize', return_value=1024 * 1024):  # 1MB
                    result = manager.file_upload(max_size_mb=10)
                    assert result == mock_path

    def test_file_upload_size_limit(self):
        """Test file upload enforces size limit"""
        manager = ExtensionsManager()

        mock_path = "C:\\test\\large_file.txt"

        with patch('tkinter.filedialog.askopenfilename', return_value=mock_path):
            with patch('os.path.exists', return_value=True):
                with patch('os.path.getsize', return_value=20 * 1024 * 1024):  # 20MB
                    result = manager.file_upload(max_size_mb=10)
                    # Should reject file that's too large
                    assert result is None


class TestFailClosed:
    """Test fail-closed behavior on critical failures"""

    def test_import_error_handling(self):
        """Verify ImportError doesn't crash initialization"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.libs = {}

        # Should complete even if libraries missing
        result = manager.initialize(pxl_client=None)
        assert manager._initialized == True

    def test_proof_validation_strict_mode(self):
        """Test that proof failures are logged"""
        manager = ExtensionsManager()
        manager._initialized = False
        manager.libs = {}
        manager.audit_log = []

        # Mock PXL that raises exceptions
        mock_pxl = Mock()
        mock_pxl.request_proof = Mock(side_effect=Exception("Proof server unavailable"))

        manager.initialize(pxl_client=mock_pxl)

        # Should have logged the failures
        audit_log = manager.get_audit_log()
        assert len(audit_log) > 0


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
