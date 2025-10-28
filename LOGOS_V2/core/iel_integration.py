"""
IEL Integration Module

Integrates Internal Extension Libraries (IELs) into the LOGOS core system.
Provides unified access to all praxis domains and their capabilities.
"""

from typing import Dict, List, Any, Optional, Type
import sys
import os

# Add IEL directory to path
current_dir = os.path.dirname(os.path.dirname(__file__))
iel_path = os.path.join(current_dir, 'IEL')
if iel_path not in sys.path:
    sys.path.insert(0, iel_path)
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

try:
    import iel_registry
    from iel_registry import get_iel_registry, IELRegistry
    _iel_available = True
except ImportError as e:
    print(f"IEL registry import failed: {e}")
    _iel_available = False
    IELRegistry = None

    class MockIELRegistry:
        """Mock registry for when IEL is not available."""
        def get_domain_description(self, domain_name: str) -> str:
            return "Domain not available"

    def get_iel_registry():
        return None

class IELIntegration:
    """
    Integration layer for Internal Extension Libraries.

    Provides access to all IEL domains and manages their lifecycle
    within the LOGOS AGI system.
    """

    def __init__(self):
        self.registry = None
        self.active_domains: Dict[str, Any] = {}
        self.domain_instances: Dict[str, Any] = {}

        if _iel_available:
            self.registry = get_iel_registry()
        else:
            print("Warning: IEL registry not available")

    def initialize_domain(self, domain_name: str) -> bool:
        """Initialize a specific IEL domain."""
        if not self.registry:
            return False

        success = self.registry.load_domain(domain_name)
        if success:
            domain_info = self.registry.get_domain(domain_name)
            if domain_info:
                self.active_domains[domain_name] = domain_info.get('components', [])

        return success

    def get_domain_components(self, domain_name: str) -> List[str]:
        """Get available components for a domain."""
        return self.active_domains.get(domain_name, [])

    def get_component(self, domain_name: str, component_name: str) -> Optional[Type]:
        """Get a specific component from a domain."""
        if not self.registry:
            return None

        full_name = f"{domain_name}.{component_name}"
        return self.registry.get_component(full_name)

    def create_domain_instance(self, domain_name: str, component_name: str, *args, **kwargs) -> Optional[Any]:
        """Create an instance of a domain component."""
        component_class = self.get_component(domain_name, component_name)
        if component_class:
            try:
                instance = component_class(*args, **kwargs)
                instance_key = f"{domain_name}.{component_name}"
                self.domain_instances[instance_key] = instance
                return instance
            except Exception as e:
                print(f"Failed to create instance of {domain_name}.{component_name}: {e}")
                return None
        return None

    def get_domain_instance(self, domain_name: str, component_name: str) -> Optional[Any]:
        """Get an existing instance of a domain component."""
        instance_key = f"{domain_name}.{component_name}"
        return self.domain_instances.get(instance_key)

    def list_available_domains(self) -> List[str]:
        """List all available IEL domains."""
        if not self.registry:
            return []
        return self.registry.list_domains()

    def get_domain_description(self, domain_name: str) -> str:
        """Get description of a domain."""
        if not self.registry:
            return "IEL registry not available"
        return self.registry.get_domain_description(domain_name)

    def initialize_all_domains(self) -> Dict[str, bool]:
        """Initialize all available IEL domains for complete system activation."""
        available_domains = self.list_available_domains()
        results = {}

        for domain in available_domains:
            results[domain] = self.initialize_domain(domain)

        return results

    def get_system_status(self) -> Dict[str, Any]:
        """Get overall IEL system status."""
        return {
            "iel_available": _iel_available,
            "registry_loaded": self.registry is not None,
            "active_domains": list(self.active_domains.keys()),
            "domain_instances": len(self.domain_instances),
            "available_domains": self.list_available_domains() if self.registry else []
        }

# Global IEL integration instance
_iel_integration = None

def get_iel_integration() -> IELIntegration:
    """Get the global IEL integration instance."""
    global _iel_integration
    if _iel_integration is None:
        _iel_integration = IELIntegration()
    return _iel_integration

def initialize_iel_system() -> bool:
    """Initialize the complete IEL system."""
    integration = get_iel_integration()
    results = integration.initialize_all_domains()

    success_count = sum(results.values())
    total_count = len(results)

    print(f"IEL System Initialization: {success_count}/{total_count} domains initialized and active")

    return success_count == total_count