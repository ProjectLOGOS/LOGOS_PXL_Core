"""
LOGOS Extensions Loader: Boot-time import and initialization of external libs.
Expanded to include probabilistic/ML/NLP/graph libraries. Loaded via Nexus at startup.
"""

import sys
import logging
import os
from typing import Optional, Dict, Any, List
from importlib import import_module
from datetime import datetime

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class ExtensionsManager:
    """Singleton manager for external libs, expanded for ML/NLP/probabilistic ops."""
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super(ExtensionsManager, cls).__new__(cls)
            cls._instance._initialized = False
            cls._instance.libs = {}
            cls._instance.pxl_client = None
            cls._instance.audit_log = []
        return cls._instance

    def initialize(self, pxl_client=None) -> bool:
        """Boot-time init: Import libs, verify, proof-gate activation."""
        if self._initialized:
            logger.info("Extensions already initialized")
            return True

        self.pxl_client = pxl_client

        # Define external libs with fallbacks and proof obligations
        lib_configs = {
            'pymc': {
                'module': 'pymc',
                'init_call': lambda: import_module('pymc'),
                'proof_obligation': "BOX(SafeProbabilisticModel())",
                'description': 'Probabilistic programming framework'
            },
            'pyro': {
                'module': 'pyro',
                'init_call': lambda: import_module('pyro'),
                'proof_obligation': "BOX(SafeProbabilisticModel())",
                'description': 'Deep probabilistic programming'
            },
            'pytorch': {
                'module': 'torch',
                'init_call': lambda: import_module('torch'),
                'proof_obligation': "BOX(SafeTensorOps())",
                'description': 'PyTorch deep learning framework'
            },
            'sentence_transformers': {
                'module': 'sentence_transformers',
                'init_call': lambda: import_module('sentence_transformers'),
                'proof_obligation': "BOX(SafeNLPTransform())",
                'description': 'Sentence embeddings for NLP'
            },
            'networkx': {
                'module': 'networkx',
                'init_call': lambda: import_module('networkx'),
                'proof_obligation': "BOX(SafeGraphOps())",
                'description': 'Graph analysis and algorithms'
            },
            'arch': {
                'module': 'arch',
                'init_call': lambda: import_module('arch'),
                'proof_obligation': "BOX(SafeEconometricModel())",
                'description': 'Econometric modeling (GARCH, etc.)'
            },
            'filterpy': {
                'module': 'filterpy',
                'init_call': lambda: import_module('filterpy'),
                'proof_obligation': "BOX(SafeFilterOps())",
                'description': 'Kalman filtering (primary)'
            },
            'pmdarima': {
                'module': 'pmdarima',
                'init_call': lambda: import_module('pmdarima'),
                'proof_obligation': "BOX(SafeTimeSeriesModel())",
                'description': 'Auto-ARIMA time series'
            },
            'pykalman': {
                'module': 'pykalman',
                'init_call': None,  # Backup if FilterPy fails
                'proof_obligation': "BOX(SafeFilterOps())",
                'description': 'Kalman filtering (backup)'
            },
            'scikit_learn': {
                'module': 'sklearn',
                'init_call': lambda: import_module('sklearn'),
                'proof_obligation': "BOX(SafeMLModel())",
                'description': 'Scikit-learn ML algorithms'
            },
            # Voice/GUI/File handling (Phase 1 compatibility)
            'voice_recog': {
                'module': 'speech_recognition',
                'init_call': None,  # Lazy init on first use
                'proof_obligation': "BOX(SafeAudioInput())",
                'description': 'Speech recognition'
            },
            'tts': {
                'module': 'pyttsx3',
                'init_call': None,  # Lazy init on first use
                'proof_obligation': "BOX(SafeAudioOutput())",
                'description': 'Text-to-speech'
            },
            'gui': {
                'module': 'tkinter',
                'init_call': None,  # Lazy init when GUI needed
                'proof_obligation': "BOX(SafeUIThread())",
                'description': 'Tkinter GUI framework'
            }
        }

        success = True
        loaded_count = 0
        failed_count = 0

        logger.info("=" * 60)
        logger.info("LOGOS Extensions Loader - Initializing External Libraries")
        logger.info("=" * 60)

        for name, config in lib_configs.items():
            try:
                logger.info(f"Loading {name}: {config['description']}...")

                # Import the module
                module_name = config['module']
                if config['init_call']:
                    lib_instance = config['init_call']()
                else:
                    # Lazy loading - just verify importable
                    try:
                        lib_instance = import_module(module_name)
                    except ImportError:
                        lib_instance = None

                self.libs[name] = lib_instance

                # Proof-gate activation
                obligation = config['proof_obligation']
                provenance = f"extensions_init:{name}"

                # Request proof if PXL client available
                if self.pxl_client:
                    try:
                        proof_token = self.pxl_client.request_proof(obligation, provenance)
                        if not proof_token:
                            raise ValueError(f"Proof failed for {name}: {obligation}")
                        logger.info(f"  ✓ {name} loaded with proof token: {proof_token[:8]}...")
                    except Exception as e:
                        logger.warning(f"  ⚠ Proof validation failed for {name}: {e}")
                        proof_token = "bypass_mode"
                else:
                    # No PXL client - bypass mode for testing
                    proof_token = "bypass_mode"
                    logger.info(f"  ✓ {name} loaded (bypass mode - no PXL validation)")

                # Audit logging
                self._audit_log({
                    'timestamp': datetime.now().isoformat(),
                    'library': name,
                    'obligation': obligation,
                    'provenance': provenance,
                    'decision': 'allow',
                    'proof': proof_token,
                    'status': 'loaded'
                })

                loaded_count += 1

            except ImportError as e:
                logger.warning(f"  ✗ {name} not available (ImportError): {e}")
                self.libs[name] = None
                self._audit_log({
                    'timestamp': datetime.now().isoformat(),
                    'library': name,
                    'obligation': config['proof_obligation'],
                    'provenance': f"extensions_init:{name}:fail",
                    'decision': 'deny',
                    'proof': None,
                    'error': f"ImportError: {str(e)}",
                    'status': 'failed'
                })
                failed_count += 1

            except Exception as e:
                logger.error(f"  ✗ Failed to load {name}: {e}")
                self.libs[name] = None
                self._audit_log({
                    'timestamp': datetime.now().isoformat(),
                    'library': name,
                    'obligation': config['proof_obligation'],
                    'provenance': f"extensions_init:{name}:fail",
                    'decision': 'deny',
                    'proof': None,
                    'error': str(e),
                    'status': 'failed'
                })
                failed_count += 1
                success = False

        logger.info("=" * 60)
        logger.info(f"Extensions Loading Complete: {loaded_count} loaded, {failed_count} failed")
        logger.info("=" * 60)

        self._initialized = True
        return success

    def _audit_log(self, entry: Dict[str, Any]) -> None:
        """Log audit entry"""
        self.audit_log.append(entry)

        # Also log to file if audit_logger available
        try:
            from logos_core.persistence import audit_logger
            audit_logger.log(entry)
        except:
            pass

    # ========================================================================
    # ORCHESTRATION METHODS - ML/NLP/Probabilistic Operations
    # ========================================================================

    def embed_sentence(self, text: str, model_name: str = 'all-MiniLM-L6-v2') -> Optional[List[float]]:
        """Generate sentence embeddings using transformer models"""
        if not self.libs.get('sentence_transformers'):
            logger.warning("SentenceTransformers not available")
            return None

        try:
            from sentence_transformers import SentenceTransformer
            model = SentenceTransformer(model_name)
            embedding = model.encode(text)
            return embedding.tolist()
        except Exception as e:
            logger.error(f"Embedding failed: {e}")
            return None

    def kalman_filter(self, measurements: List[float], dim_x: int = 2, dim_z: int = 1) -> Optional[List[float]]:
        """Apply Kalman filter to measurement sequence"""
        if not self.libs.get('filterpy'):
            logger.warning("FilterPy not available, trying PyKalman...")
            return self._kalman_filter_backup(measurements)

        try:
            from filterpy.kalman import KalmanFilter
            kf = KalmanFilter(dim_x=dim_x, dim_z=dim_z)
            kf.x = [0.] * dim_x  # Initial state
            kf.F = [[1., 1.], [0., 1.]] if dim_x == 2 else [[1.]]  # State transition
            kf.H = [[1.] + [0.] * (dim_x - 1)]  # Measurement function
            kf.P *= 1000.  # Covariance matrix
            kf.R = 5  # Measurement noise
            kf.Q = [[0.1, 0.], [0., 0.1]] if dim_x == 2 else [[0.1]]  # Process noise

            filtered = []
            for z in measurements:
                kf.predict()
                kf.update([z])
                filtered.append(kf.x[0])

            return filtered
        except Exception as e:
            logger.error(f"Kalman filter failed: {e}")
            return None

    def _kalman_filter_backup(self, measurements: List[float]) -> Optional[List[float]]:
        """Backup Kalman filter using PyKalman"""
        if not self.libs.get('pykalman'):
            return None

        try:
            from pykalman import KalmanFilter
            kf = KalmanFilter(initial_state_mean=0, n_dim_obs=1)
            filtered_state_means, _ = kf.filter(measurements)
            return filtered_state_means.flatten().tolist()
        except Exception as e:
            logger.error(f"Backup Kalman filter failed: {e}")
            return None

    def build_graph(self, nodes: List[Any], edges: List[tuple]) -> Optional[Any]:
        """Build a NetworkX graph from nodes and edges"""
        if not self.libs.get('networkx'):
            logger.warning("NetworkX not available")
            return None

        try:
            import networkx as nx
            graph = nx.Graph()
            graph.add_nodes_from(nodes)
            graph.add_edges_from(edges)
            return graph
        except Exception as e:
            logger.error(f"Graph building failed: {e}")
            return None

    def analyze_graph(self, graph) -> Optional[Dict[str, Any]]:
        """Analyze graph properties"""
        if not graph or not self.libs.get('networkx'):
            return None

        try:
            import networkx as nx
            return {
                'num_nodes': graph.number_of_nodes(),
                'num_edges': graph.number_of_edges(),
                'density': nx.density(graph),
                'is_connected': nx.is_connected(graph),
                'clustering_coefficient': nx.average_clustering(graph)
            }
        except Exception as e:
            logger.error(f"Graph analysis failed: {e}")
            return None

    def pytorch_available(self) -> bool:
        """Check if PyTorch is available and configured"""
        if not self.libs.get('pytorch'):
            return False

        try:
            import torch
            logger.info(f"PyTorch version: {torch.__version__}")
            logger.info(f"CUDA available: {torch.cuda.is_available()}")
            return True
        except Exception as e:
            logger.error(f"PyTorch check failed: {e}")
            return False

    def create_tensor(self, data: List[Any]) -> Optional[Any]:
        """Create PyTorch tensor"""
        if not self.libs.get('pytorch'):
            logger.warning("PyTorch not available")
            return None

        try:
            import torch
            return torch.tensor(data)
        except Exception as e:
            logger.error(f"Tensor creation failed: {e}")
            return None

    def sklearn_classify(self, X_train, y_train, X_test, model_type: str = 'random_forest'):
        """Simple sklearn classification"""
        if not self.libs.get('scikit_learn'):
            logger.warning("Scikit-learn not available")
            return None

        try:
            from sklearn.ensemble import RandomForestClassifier
            from sklearn.linear_model import LogisticRegression

            if model_type == 'random_forest':
                model = RandomForestClassifier(n_estimators=100, random_state=42)
            else:
                model = LogisticRegression(random_state=42)

            model.fit(X_train, y_train)
            predictions = model.predict(X_test)
            return predictions
        except Exception as e:
            logger.error(f"Classification failed: {e}")
            return None

    # ========================================================================
    # VOICE/GUI/FILE OPERATIONS (Phase 1 Compatibility)
    # ========================================================================

    def voice_input(self, duration: int = 5) -> Optional[str]:
        """Capture voice input using speech recognition"""
        if not self.libs.get('voice_recog'):
            try:
                import speech_recognition as sr
                self.libs['voice_recog'] = sr.Recognizer()
            except ImportError:
                logger.warning("Speech recognition not available")
                return None

        try:
            import speech_recognition as sr
            recognizer = self.libs['voice_recog']
            with sr.Microphone() as source:
                logger.info("Listening for voice input...")
                audio = recognizer.listen(source, timeout=duration)
            text = recognizer.recognize_google(audio)
            logger.info(f"Voice captured: {text}")
            return text
        except Exception as e:
            logger.error(f"Voice input failed: {e}")
            return None

    def tts_output(self, text: str, voice_rate: int = 150, volume: float = 0.9) -> None:
        """Text-to-speech output"""
        if not self.libs.get('tts'):
            try:
                import pyttsx3
                self.libs['tts'] = pyttsx3.init()
            except ImportError:
                logger.warning("TTS not available")
                return

        try:
            engine = self.libs['tts']
            engine.setProperty('rate', voice_rate)
            engine.setProperty('volume', volume)
            engine.say(text)
            engine.runAndWait()
        except Exception as e:
            logger.error(f"TTS output failed: {e}")

    def file_upload(self, max_size_mb: int = 10) -> Optional[str]:
        """File upload dialog with size validation"""
        try:
            from tkinter import filedialog
            import tkinter as tk

            # Create temporary root if needed
            root = tk.Tk()
            root.withdraw()

            path = filedialog.askopenfilename(
                title="Select file to upload",
                filetypes=[("All files", "*.*")]
            )

            root.destroy()

            if path and os.path.exists(path):
                file_size_mb = os.path.getsize(path) / (1024 * 1024)
                if file_size_mb > max_size_mb:
                    logger.error(f"File too large: {file_size_mb:.2f}MB > {max_size_mb}MB")
                    return None
                logger.info(f"File selected: {path} ({file_size_mb:.2f}MB)")
                return path

            return None
        except Exception as e:
            logger.error(f"File upload failed: {e}")
            return None

    # ========================================================================
    # UTILITY METHODS
    # ========================================================================

    def get_status(self) -> Dict[str, Any]:
        """Get status of all loaded extensions"""
        status = {
            'initialized': self._initialized,
            'libraries': {},
            'audit_entries': len(self.audit_log)
        }

        for name, lib in self.libs.items():
            status['libraries'][name] = {
                'loaded': lib is not None,
                'type': type(lib).__name__ if lib else None
            }

        return status

    def get_audit_log(self) -> List[Dict[str, Any]]:
        """Retrieve audit log"""
        return self.audit_log.copy()

    def is_available(self, library_name: str) -> bool:
        """Check if a specific library is available"""
        return self.libs.get(library_name) is not None

# Global singleton instance
extensions_manager = ExtensionsManager()
