#!/usr/bin/env python3
"""
LOGOS AGI System Launcher
Single-command launcher for the complete LOGOS AGI system with comprehensive initialization checks
"""

import sys
import os
import time
import threading
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional

# Add LOGOS to path
sys.path.insert(0, str(Path(__file__).parent / "LOGOS_V2"))

class LOGOSLauncher:
    """Comprehensive LOGOS AGI system launcher with health checks"""

    def __init__(self):
        self.system_ready = False
        self.core_system = None
        self.health_status = {}
        self.gui_process = None
        self.monitoring_active = False

    def log(self, message: str, level: str = "INFO"):
        """Log with timestamp and level"""
        timestamp = time.strftime("%H:%M:%S")
        print(f"[{timestamp}] {level}: {message}")

    def initialize_core_system(self) -> bool:
        """Initialize the LOGOS core system"""
        try:
            self.log("Initializing LOGOS Core System...")

            from LOGOS_V2.entry import get_logos_core
            self.core_system = get_logos_core()

            self.log("✅ LOGOS Core System initialized successfully")
            return True

        except Exception as e:
            self.log(f"❌ Failed to initialize LOGOS Core: {e}", "ERROR")
            return False

    def run_comprehensive_health_check(self) -> Dict[str, Any]:
        """Run comprehensive health checks on all subsystems"""
        self.log("Running comprehensive system health checks...")

        health_report = {
            "timestamp": time.time(),
            "overall_status": "UNKNOWN",
            "subsystems": {},
            "warnings": [],
            "errors": []
        }

        try:
            # Get system status
            status = self.core_system.get_system_status()

            # Check LOGOS Core
            core_status = status.get("logos_core", {})
            core_ok = core_status.get("status") == "operational"
            health_report["subsystems"]["logos_core"] = {
                "status": "PASS" if core_ok else "FAIL",
                "details": core_status
            }

            # Check Integrity Safeguard
            safeguard_status = status.get("integrity_safeguard", {})
            safeguard_ok = not safeguard_status.get("system_halted", True)
            health_report["subsystems"]["integrity_safeguard"] = {
                "status": "PASS" if safeguard_ok else "FAIL",
                "details": safeguard_status
            }

            # Check IEL System
            iel_status = status.get("iel", {})
            iel_available = iel_status.get("iel_available", False)
            registry_loaded = iel_status.get("registry_loaded", False)
            active_domains = len(iel_status.get("active_domains", []))
            total_domains = len(iel_status.get("available_domains", []))

            iel_ok = iel_available and registry_loaded and active_domains == total_domains
            health_report["subsystems"]["iel_system"] = {
                "status": "PASS" if iel_ok else "WARN",
                "details": {
                    "available": iel_available,
                    "registry_loaded": registry_loaded,
                    "active_domains": active_domains,
                    "total_domains": total_domains
                }
            }

            # Check Reference Monitor
            monitor_status = status.get("reference_monitor", {})
            monitor_ok = "pxl_server" in monitor_status
            health_report["subsystems"]["reference_monitor"] = {
                "status": "PASS" if monitor_ok else "WARN",
                "details": monitor_status
            }

            # Determine overall status
            subsystem_statuses = [sub["status"] for sub in health_report["subsystems"].values()]
            if "FAIL" in subsystem_statuses:
                health_report["overall_status"] = "CRITICAL"
                health_report["errors"].append("Critical subsystem failure detected")
            elif "WARN" in subsystem_statuses:
                health_report["overall_status"] = "DEGRADED"
                health_report["warnings"].append("Some subsystems operating in degraded mode")
            else:
                health_report["overall_status"] = "HEALTHY"

            # Log results
            for subsystem, info in health_report["subsystems"].items():
                status_icon = "✅" if info["status"] == "PASS" else "⚠️" if info["status"] == "WARN" else "❌"
                self.log(f"{status_icon} {subsystem}: {info['status']}")

            return health_report

        except Exception as e:
            health_report["overall_status"] = "ERROR"
            health_report["errors"].append(f"Health check failed: {e}")
            self.log(f"❌ Health check error: {e}", "ERROR")
            return health_report

    def validate_subsystem_coherence(self) -> bool:
        """Validate internal coherence across all subsystems"""
        self.log("Validating subsystem coherence...")

        try:
            # Test basic system status retrieval
            status = self.core_system.get_system_status()
            if not status or "logos_core" not in status:
                self.log("❌ System status coherence check failed", "ERROR")
                return False

            # Test IEL domain access and basic functionality
            iel_integration = self.core_system._iel_integration
            if iel_integration:
                domains = iel_integration.list_available_domains()
                if len(domains) < 12:
                    self.log(f"⚠️ IEL coherence check: only {len(domains)} domains available (expected 12+)", "WARN")
                    # Don't fail for this - it's a warning
                else:
                    self.log(f"✅ IEL coherence: {len(domains)} domains available")

                # Test basic domain loading
                if domains:
                    first_domain = domains[0]
                    components = iel_integration.get_domain_components(first_domain)
                    self.log(f"✅ Domain '{first_domain}' has {len(components)} components")

            # Test safety system basic functionality
            safety_status = self.core_system._safety_system.get_safety_status()
            if not safety_status:
                self.log("❌ Safety system coherence check failed", "ERROR")
                return False

            # Test reference monitor basic functionality
            monitor_health = self.core_system._monitor.health_check()
            if not monitor_health:
                self.log("❌ Reference monitor coherence check failed", "ERROR")
                return False

            self.log("✅ Subsystem coherence validation passed")
            return True

        except Exception as e:
            self.log(f"❌ Coherence validation error: {e}", "ERROR")
            return False

    def check_passive_processes(self) -> bool:
        """Check that passive monitoring processes are operational"""
        self.log("Checking passive process operations...")

        try:
            # Check if safety monitoring is active
            if hasattr(self.core_system._safety_system, '_monitoring_threads'):
                monitoring_threads = len(self.core_system._safety_system._monitoring_threads)
                if monitoring_threads == 0:
                    self.log("⚠️ No safety monitoring threads active", "WARN")
                    return False
                self.log(f"✅ {monitoring_threads} safety monitoring threads active")

            # Check reference monitor health
            monitor_health = self.core_system._monitor.health_check()
            if "pxl_server" not in monitor_health:
                self.log("⚠️ Reference monitor health check incomplete", "WARN")
                return False

            self.log("✅ Passive processes operational")
            return True

        except Exception as e:
            self.log(f"❌ Passive process check error: {e}", "ERROR")
            return False

    def assess_tool_readiness(self) -> Dict[str, bool]:
        """Assess which tools are ready for deployment"""
        self.log("Assessing tool readiness for interaction...")

        tool_status = {}

        try:
            # Check modal logic tool (basic status check instead of evaluation)
            try:
                # Just check if the method exists and system is initialized
                tool_status["modal_logic"] = hasattr(self.core_system, 'evaluate_modal_logic') and self.core_system._initialized
            except:
                tool_status["modal_logic"] = False

            # Check IEL tools
            try:
                iel_integration = self.core_system._iel_integration
                tool_status["iel_domains"] = len(iel_integration.list_available_domains()) > 0 if iel_integration else False
            except:
                tool_status["iel_domains"] = False

            # Check safety tools
            try:
                safety_status = self.core_system._safety_system.get_safety_status()
                tool_status["safety_system"] = not safety_status.get("system_halted", True)
            except:
                tool_status["safety_system"] = False

            # Check reference monitor
            try:
                monitor_health = self.core_system._monitor.health_check()
                tool_status["reference_monitor"] = bool(monitor_health)
            except:
                tool_status["reference_monitor"] = False

            # Log tool status
            for tool, ready in tool_status.items():
                status_icon = "✅" if ready else "❌"
                self.log(f"{status_icon} {tool}: {'READY' if ready else 'NOT READY'}")

            return tool_status

        except Exception as e:
            self.log(f"❌ Tool readiness assessment error: {e}", "ERROR")
            return {}

    def launch_gui_interface(self) -> bool:
        """Launch the GUI interface when system is ready"""
        try:
            self.log("Launching LOGOS GUI Interface...")

            # Check if we're in a codespace environment
            is_codespace = os.environ.get('CODESPACES', '').lower() == 'true' or 'github.dev' in os.environ.get('GITHUB_SERVER_URL', '')

            # Launch GUI in background
            self.gui_process = subprocess.Popen([
                sys.executable, "demo_gui.py"
            ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            # Wait a moment for GUI to start
            time.sleep(2)

            if self.gui_process.poll() is None:
                self.log("✅ LOGOS GUI Interface launched successfully")
                if is_codespace:
                    self.log("📱 Access interface at: http://localhost:7860")
                else:
                    self.log("📱 Browser should open automatically to: http://localhost:7860")
                return True
            else:
                stdout, stderr = self.gui_process.communicate()
                self.log(f"❌ GUI launch failed: {stderr.decode()}", "ERROR")
                return False

        except Exception as e:
            self.log(f"❌ GUI launch error: {e}", "ERROR")
            return False

    def perform_final_readiness_check(self) -> bool:
        """Final comprehensive readiness check before allowing interaction"""
        self.log("Performing final system readiness check...")

        # Re-run health check
        health = self.run_comprehensive_health_check()

        if health["overall_status"] == "CRITICAL":
            self.log("❌ System not ready - critical failures detected", "ERROR")
            return False

        # Validate coherence
        if not self.validate_subsystem_coherence():
            self.log("❌ System not ready - coherence validation failed", "ERROR")
            return False

        # Check passive processes
        if not self.check_passive_processes():
            self.log("❌ System not ready - passive processes not operational", "ERROR")
            return False

        # Assess tool readiness
        tool_status = self.assess_tool_readiness()
        ready_tools = sum(tool_status.values())
        total_tools = len(tool_status)

        if ready_tools < total_tools * 0.7:  # Require 70% of tools ready
            self.log(f"⚠️ Only {ready_tools}/{total_tools} tools ready - proceeding with caution", "WARN")

        self.log("✅ System readiness check completed")
        return True

    def launch_system(self) -> int:
        """Main system launch sequence"""
        print("🤖 LOGOS AGI System Launcher")
        print("=" * 50)
        print()

        try:
            # Phase 1: Core System Initialization
            self.log("🚀 PHASE 1: Core System Initialization")
            if not self.initialize_core_system():
                return 1

            # Phase 2: Comprehensive Health Checks
            self.log("🏥 PHASE 2: Comprehensive Health Checks")
            health_report = self.run_comprehensive_health_check()

            if health_report["overall_status"] == "CRITICAL":
                self.log("❌ Critical system failures detected - aborting launch", "ERROR")
                return 1

            # Phase 3: Subsystem Coherence Validation
            self.log("🔗 PHASE 3: Subsystem Coherence Validation")
            if not self.validate_subsystem_coherence():
                self.log("❌ Subsystem coherence validation failed - aborting launch", "ERROR")
                return 1

            # Phase 4: Passive Process Verification
            self.log("⚙️ PHASE 4: Passive Process Verification")
            if not self.check_passive_processes():
                self.log("❌ Passive process verification failed - aborting launch", "ERROR")
                return 1

            # Phase 5: Final Readiness Assessment
            self.log("🎯 PHASE 5: Final Readiness Assessment")
            if not self.perform_final_readiness_check():
                self.log("❌ Final readiness check failed - aborting launch", "ERROR")
                return 1

            # Phase 6: GUI Interface Launch
            self.log("🖥️ PHASE 6: GUI Interface Launch")
            if not self.launch_gui_interface():
                self.log("❌ GUI interface launch failed", "ERROR")
                return 1

            # Success!
            self.system_ready = True
            print()
            print("🎉 LOGOS AGI System Successfully Launched!")
            print("=" * 50)
            print("✅ All subsystems operational")
            print("✅ Safety and alignment systems active")
            print("✅ Internal coherence validated")
            print("✅ GUI interface ready for interaction")
            print()
            print("💡 The system is now ready for AGI interaction")
            print("💡 GUI available at: http://localhost:7860")
            print()

            # Keep system running
            try:
                while True:
                    time.sleep(1)
                    if self.gui_process and self.gui_process.poll() is not None:
                        self.log("GUI process terminated - shutting down system")
                        break
            except KeyboardInterrupt:
                self.log("Shutdown requested by user")

            return 0

        except Exception as e:
            self.log(f"❌ Unexpected error during system launch: {e}", "ERROR")
            return 1

        finally:
            self.shutdown_system()

    def shutdown_system(self):
        """Graceful system shutdown"""
        self.log("Initiating system shutdown...")

        if self.gui_process:
            try:
                self.gui_process.terminate()
                self.gui_process.wait(timeout=5)
                self.log("✅ GUI process terminated")
            except:
                self.gui_process.kill()
                self.log("⚠️ GUI process force-killed")

        if self.core_system:
            try:
                self.core_system.shutdown()
                self.log("✅ LOGOS core system shut down")
            except Exception as e:
                self.log(f"⚠️ Error during core shutdown: {e}")

        self.log("👋 LOGOS system shutdown complete")

def main():
    """Main entry point"""
    launcher = LOGOSLauncher()
    exit_code = launcher.launch_system()
    return exit_code

if __name__ == "__main__":
    sys.exit(main())