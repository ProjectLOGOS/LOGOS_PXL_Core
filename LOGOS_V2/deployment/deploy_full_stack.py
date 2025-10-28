#!/usr/bin/env python3
"""
LOGOS AGI Full Stack Deployment Manager
Comprehensive deployment, health monitoring, and management system
"""

import json
import time
import subprocess
import threading
import logging
import signal
import sys
import os
import psutil
import requests
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, asdict
import yaml

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class ServiceConfig:
    """Configuration for a LOGOS service"""
    name: str
    port: int
    module_path: str
    working_dir: str
    environment: Dict[str, str]
    health_endpoint: str = "/health"
    startup_delay: int = 2
    health_timeout: int = 30
    required: bool = True
    dependencies: List[str] = None

@dataclass
class DeploymentStatus:
    """Status of the deployment"""
    started_at: datetime
    services: Dict[str, Any]
    overall_health: str
    metrics: Dict[str, Any]

class LogosFullStackDeployment:
    """
    Complete LOGOS AGI full stack deployment manager

    Handles Docker Compose orchestration, service health monitoring,
    fallback to local processes, and comprehensive system management.
    """

    def __init__(self, config_path: Optional[str] = None):
        self.config_path = config_path or "deployment_config.yaml"
        self.deployment_status = None
        self.running_processes = {}
        self.docker_mode = True
        self.root_dir = Path(__file__).parent
        self.logs_dir = self.root_dir / "logs" / "deployment"
        self.logs_dir.mkdir(parents=True, exist_ok=True)

        # Load configuration
        self.config = self._load_config()

        # Service definitions
        self.services = self._define_services()

        # Shutdown handler
        signal.signal(signal.SIGINT, self._shutdown_handler)
        signal.signal(signal.SIGTERM, self._shutdown_handler)

    def _load_config(self) -> Dict[str, Any]:
        """Load deployment configuration"""
        default_config = {
            "deployment": {
                "mode": "docker",  # "docker" or "local"
                "health_check_interval": 30,
                "max_startup_time": 300,
                "enable_monitoring": True,
                "log_level": "INFO"
            },
            "docker": {
                "compose_file": "docker-compose.yml",
                "project_name": "logos-agi",
                "build_timeout": 600
            },
            "networking": {
                "base_port": 8000,
                "health_timeout": 10,
                "startup_delay": 2
            },
            "monitoring": {
                "metrics_port": 9090,
                "dashboard_port": 3000,
                "enable_telemetry": True
            }
        }

        if Path(self.config_path).exists():
            with open(self.config_path, 'r') as f:
                user_config = yaml.safe_load(f)
                # Merge with defaults
                for key, value in user_config.items():
                    if isinstance(value, dict) and key in default_config:
                        default_config[key].update(value)
                    else:
                        default_config[key] = value

        return default_config

    def _define_services(self) -> Dict[str, ServiceConfig]:
        """Define all LOGOS services"""
        return {
            # Core Proof Service
            "pxl-prover": ServiceConfig(
                name="pxl-prover",
                port=8088,
                module_path="pxl_prover.server:app",
                working_dir="pxl-prover",
                environment={"FLASK_ENV": "production"},
                required=True
            ),

            # Core LOGOS Services
            "logos-core": ServiceConfig(
                name="logos-core",
                port=5000,
                module_path="logos_core.server:app",
                working_dir="",
                environment={
                    "PXL_PROVER_URL": "http://localhost:8088",
                    "PYTHONPATH": str(self.root_dir)
                },
                dependencies=["pxl-prover"],
                required=True
            ),

            "logos-api": ServiceConfig(
                name="logos-api",
                port=8090,
                module_path="logos_core.server:app",
                working_dir="",
                environment={},
                required=True
            ),

            # Worker Services
            "archon": ServiceConfig(
                name="archon",
                port=8075,
                module_path="services.archon.app:app",
                working_dir="services/archon",
                environment={
                    "RABBIT_URL": "amqp://logos:trinity@localhost:5672/logos",
                    "LOGOS_API_URL": "http://localhost:8090"
                },
                dependencies=["logos-core", "rabbitmq"],
                required=True
            ),

            "telos": ServiceConfig(
                name="telos",
                port=8066,
                module_path="telos_worker:app",
                working_dir="subsystems/telos",
                environment={
                    "RABBIT_URL": "amqp://logos:trinity@localhost:5672/logos",
                    "SUBSYS": "TELOS"
                },
                dependencies=["rabbitmq"]
            ),

            "tetragnos": ServiceConfig(
                name="tetragnos",
                port=8065,
                module_path="app:app",
                working_dir="subsystems/tetragnos",
                environment={
                    "RABBIT_URL": "amqp://logos:trinity@localhost:5672/logos",
                    "SUBSYS": "TETRAGNOS"
                },
                dependencies=["rabbitmq"]
            ),

            "thonoc": ServiceConfig(
                name="thonoc",
                port=8067,
                module_path="app:app",
                working_dir="subsystems/thonoc",
                environment={
                    "RABBIT_URL": "amqp://logos:trinity@localhost:5672/logos",
                    "SUBSYS": "THONOC"
                },
                dependencies=["rabbitmq"]
            ),

            # Tool Services
            "tool-router": ServiceConfig(
                name="tool-router",
                port=8071,
                module_path="services.tool_router.app:app",
                working_dir="",
                environment={
                    "TELOS_URL": "http://localhost:8066",
                    "THONOC_URL": "http://localhost:8067",
                    "TETRAGNOS_URL": "http://localhost:8065",
                    "CRAWL_URL": "http://localhost:8064"
                },
                dependencies=["telos", "tetragnos", "thonoc"]
            ),

            "executor": ServiceConfig(
                name="executor",
                port=8072,
                module_path="services.executor.app:app",
                working_dir="",
                environment={
                    "TOOL_ROUTER_URL": "http://localhost:8071"
                },
                dependencies=["tool-router"]
            ),

            # User Interfaces
            "interactive-chat": ServiceConfig(
                name="interactive-chat",
                port=8080,
                module_path="main:chat_app",
                working_dir="services/interactive_chat",
                environment={
                    "LOGOS_API_URL": "http://localhost:8090",
                    "TOOL_ROUTER_URL": "http://localhost:8071"
                },
                dependencies=["logos-api", "tool-router"]
            ),

            "probe-console": ServiceConfig(
                name="probe-console",
                port=8081,
                module_path="app:app",
                working_dir="services/probe_console",
                environment={
                    "ARCHON_URL": "http://localhost:8075",
                    "LOGOS_URL": "http://localhost:8090"
                },
                dependencies=["archon", "logos-api"]
            ),

            # Infrastructure Services
            "crawl": ServiceConfig(
                name="crawl",
                port=8064,
                module_path="services.toolkits.crawl.app:app",
                working_dir="",
                environment={}
            )
        }

    def deploy_docker_stack(self) -> bool:
        """Deploy using Docker Compose"""
        logger.info("🐳 Starting Docker deployment...")

        try:
            # Check if Docker is available
            subprocess.run(["docker", "--version"], check=True, capture_output=True)
            subprocess.run(["docker-compose", "--version"], check=True, capture_output=True)
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("Docker or Docker Compose not available")
            return False

        try:
            compose_file = self.config["docker"]["compose_file"]
            project_name = self.config["docker"]["project_name"]

            # Pull and build images
            logger.info("Building Docker images...")
            subprocess.run([
                "docker-compose", "-f", compose_file, "-p", project_name,
                "build"
            ], check=True, cwd=self.root_dir)

            # Start services
            logger.info("Starting Docker services...")
            subprocess.run([
                "docker-compose", "-f", compose_file, "-p", project_name,
                "up", "-d"
            ], check=True, cwd=self.root_dir)

            logger.info("✅ Docker stack deployed successfully")
            return True

        except subprocess.CalledProcessError as e:
            logger.error(f"Docker deployment failed: {e}")
            return False

    def deploy_local_stack(self) -> bool:
        """Deploy using local Python processes"""
        logger.info("🔧 Starting local deployment...")

        # Start services in dependency order
        started_services = set()

        def can_start_service(service_name: str) -> bool:
            """Check if service dependencies are met"""
            service = self.services[service_name]
            if not service.dependencies:
                return True
            return all(dep in started_services for dep in service.dependencies)

        # Start services with dependency resolution
        max_attempts = len(self.services) * 2
        attempt = 0

        while len(started_services) < len(self.services) and attempt < max_attempts:
            attempt += 1

            for service_name, service_config in self.services.items():
                if service_name in started_services:
                    continue

                if not can_start_service(service_name):
                    continue

                if self._start_local_service(service_name, service_config):
                    started_services.add(service_name)
                    time.sleep(service_config.startup_delay)

        # Check if all required services started
        required_services = {name for name, svc in self.services.items() if svc.required}
        missing_required = required_services - started_services

        if missing_required:
            logger.error(f"Failed to start required services: {missing_required}")
            return False

        logger.info(f"✅ Local stack deployed: {len(started_services)} services started")
        return True

    def _start_local_service(self, service_name: str, config: ServiceConfig) -> bool:
        """Start a single local service"""
        logger.info(f"🔧 Starting {service_name} on port {config.port}...")

        try:
            # Set environment variables
            env = os.environ.copy()
            env.update(config.environment)

            # Determine working directory
            work_dir = self.root_dir / config.working_dir if config.working_dir else self.root_dir

            # Start process
            cmd = [
                sys.executable, "-m", "uvicorn", config.module_path,
                "--host", "127.0.0.1",
                "--port", str(config.port),
                "--log-level", "warning"
            ]

            process = subprocess.Popen(
                cmd,
                cwd=work_dir,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE
            )

            self.running_processes[service_name] = {
                "process": process,
                "config": config,
                "started_at": datetime.now()
            }

            logger.info(f"   ✅ {service_name} started (PID: {process.pid})")
            return True

        except Exception as e:
            logger.error(f"   ❌ Failed to start {service_name}: {e}")
            return False

    def check_health(self) -> Dict[str, Any]:
        """Check health of all services"""
        health_status = {
            "timestamp": datetime.now().isoformat(),
            "services": {},
            "overall_healthy": True
        }

        for service_name, service_config in self.services.items():
            url = f"http://localhost:{service_config.port}{service_config.health_endpoint}"

            try:
                response = requests.get(url, timeout=self.config["networking"]["health_timeout"])
                status = "healthy" if response.status_code == 200 else "unhealthy"
                health_status["services"][service_name] = {
                    "status": status,
                    "port": service_config.port,
                    "response_time_ms": response.elapsed.total_seconds() * 1000,
                    "status_code": response.status_code
                }

                if status != "healthy":
                    health_status["overall_healthy"] = False

            except Exception as e:
                health_status["services"][service_name] = {
                    "status": "unreachable",
                    "port": service_config.port,
                    "error": str(e)
                }
                health_status["overall_healthy"] = False

        return health_status

    def monitor_services(self):
        """Continuous service monitoring"""
        logger.info("🔍 Starting service monitoring...")

        while True:
            try:
                health = self.check_health()

                # Log health status
                log_file = self.logs_dir / f"health_{datetime.now().strftime('%Y%m%d')}.jsonl"
                with open(log_file, 'a') as f:
                    f.write(json.dumps(health) + '\n')

                # Check for failures and restart if needed
                for service_name, status in health["services"].items():
                    if status["status"] in ["unhealthy", "unreachable"]:
                        logger.warning(f"⚠️ Service {service_name} is {status['status']}")

                        # Attempt restart for local services
                        if service_name in self.running_processes:
                            self._restart_local_service(service_name)

                # Overall status
                if health["overall_healthy"]:
                    logger.info("✅ All services healthy")
                else:
                    unhealthy = [name for name, status in health["services"].items()
                               if status["status"] != "healthy"]
                    logger.warning(f"⚠️ Unhealthy services: {unhealthy}")

                time.sleep(self.config["deployment"]["health_check_interval"])

            except KeyboardInterrupt:
                logger.info("Stopping monitoring...")
                break
            except Exception as e:
                logger.error(f"Monitoring error: {e}")
                time.sleep(30)

    def _restart_local_service(self, service_name: str):
        """Restart a failed local service"""
        logger.info(f"🔄 Restarting {service_name}...")

        # Stop existing process
        if service_name in self.running_processes:
            process_info = self.running_processes[service_name]
            try:
                process_info["process"].terminate()
                process_info["process"].wait(timeout=10)
            except:
                process_info["process"].kill()

            del self.running_processes[service_name]

        # Restart service
        config = self.services[service_name]
        if self._start_local_service(service_name, config):
            logger.info(f"✅ {service_name} restarted successfully")
        else:
            logger.error(f"❌ Failed to restart {service_name}")

    def deploy(self) -> bool:
        """Deploy the full LOGOS stack"""
        logger.info("🚀 LOGOS AGI Full Stack Deployment Starting...")
        logger.info("=" * 60)

        # Try Docker first, fallback to local
        deployment_mode = self.config["deployment"]["mode"]

        if deployment_mode == "docker" or deployment_mode == "auto":
            if self.deploy_docker_stack():
                self.docker_mode = True
                logger.info("🐳 Docker deployment successful")
            elif deployment_mode == "auto":
                logger.info("🔧 Falling back to local deployment...")
                if self.deploy_local_stack():
                    self.docker_mode = False
                    logger.info("🔧 Local deployment successful")
                else:
                    logger.error("❌ Both Docker and local deployment failed")
                    return False
            else:
                logger.error("❌ Docker deployment failed")
                return False
        else:
            if self.deploy_local_stack():
                self.docker_mode = False
                logger.info("🔧 Local deployment successful")
            else:
                logger.error("❌ Local deployment failed")
                return False

        # Wait for services to stabilize
        logger.info("⏳ Waiting for services to stabilize...")
        time.sleep(15)

        # Check initial health
        health = self.check_health()
        if health["overall_healthy"]:
            logger.info("✅ All services are healthy!")
        else:
            logger.warning("⚠️ Some services may need more time to start")

        # Start monitoring if enabled
        if self.config["deployment"]["enable_monitoring"]:
            monitoring_thread = threading.Thread(target=self.monitor_services, daemon=True)
            monitoring_thread.start()

        # Create deployment status
        self.deployment_status = DeploymentStatus(
            started_at=datetime.now(),
            services=health["services"],
            overall_health="healthy" if health["overall_healthy"] else "degraded",
            metrics={}
        )

        # Save deployment info
        deployment_info = {
            "status": asdict(self.deployment_status),
            "config": self.config,
            "docker_mode": self.docker_mode
        }

        with open(self.logs_dir / "deployment_info.json", 'w') as f:
            json.dump(deployment_info, f, indent=2, default=str)

        return True

    def status(self) -> Dict[str, Any]:
        """Get current deployment status"""
        health = self.check_health()

        return {
            "deployment_active": self.deployment_status is not None,
            "mode": "docker" if self.docker_mode else "local",
            "started_at": self.deployment_status.started_at if self.deployment_status else None,
            "health": health,
            "services_count": len(self.services),
            "healthy_count": len([s for s in health["services"].values() if s["status"] == "healthy"]),
            "endpoints": {
                name: f"http://localhost:{config.port}"
                for name, config in self.services.items()
            }
        }

    def shutdown(self):
        """Shutdown the deployment"""
        logger.info("🛑 Shutting down LOGOS deployment...")

        if self.docker_mode:
            # Stop Docker services
            try:
                compose_file = self.config["docker"]["compose_file"]
                project_name = self.config["docker"]["project_name"]

                subprocess.run([
                    "docker-compose", "-f", compose_file, "-p", project_name,
                    "down"
                ], cwd=self.root_dir)

                logger.info("✅ Docker services stopped")
            except Exception as e:
                logger.error(f"Error stopping Docker services: {e}")

        else:
            # Stop local processes
            for service_name, process_info in self.running_processes.items():
                try:
                    process_info["process"].terminate()
                    process_info["process"].wait(timeout=10)
                    logger.info(f"✅ Stopped {service_name}")
                except:
                    process_info["process"].kill()
                    logger.info(f"🔪 Killed {service_name}")

            self.running_processes.clear()

        logger.info("🛑 Deployment shutdown complete")

    def _shutdown_handler(self, signum, frame):
        """Handle shutdown signals"""
        logger.info(f"Received signal {signum}, shutting down...")
        self.shutdown()
        sys.exit(0)

def main():
    """Main deployment function"""
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS AGI Full Stack Deployment")
    parser.add_argument("--config", help="Configuration file path")
    parser.add_argument("--mode", choices=["docker", "local", "auto"], default="auto",
                       help="Deployment mode")
    parser.add_argument("--status", action="store_true", help="Show deployment status")
    parser.add_argument("--shutdown", action="store_true", help="Shutdown deployment")
    parser.add_argument("--monitor", action="store_true", help="Monitor services only")

    args = parser.parse_args()

    # Create deployment manager
    deployment = LogosFullStackDeployment(args.config)

    # Override mode if specified
    if args.mode:
        deployment.config["deployment"]["mode"] = args.mode

    if args.status:
        # Show status
        status = deployment.status()
        print(json.dumps(status, indent=2, default=str))
        return

    if args.shutdown:
        # Shutdown deployment
        deployment.shutdown()
        return

    if args.monitor:
        # Monitor only
        deployment.monitor_services()
        return

    # Deploy the stack
    try:
        if deployment.deploy():
            logger.info("🎉 LOGOS AGI deployment successful!")
            logger.info("\n" + "="*60)
            logger.info("DEPLOYMENT SUMMARY")
            logger.info("="*60)

            status = deployment.status()
            logger.info(f"Mode: {status['mode'].upper()}")
            logger.info(f"Services: {status['healthy_count']}/{status['services_count']} healthy")

            logger.info("\nKey Endpoints:")
            key_endpoints = {
                "LOGOS Core API": "http://localhost:8090",
                "Interactive Chat": "http://localhost:8080",
                "Probe Console": "http://localhost:8081",
                "Archon Gateway": "http://localhost:8075"
            }

            for name, url in key_endpoints.items():
                logger.info(f"  {name}: {url}")

            logger.info("\n🔍 Monitoring enabled - services will be auto-restarted on failure")
            logger.info("Press Ctrl+C to shutdown")

            # Keep main thread alive
            try:
                while True:
                    time.sleep(60)
            except KeyboardInterrupt:
                pass

        else:
            logger.error("❌ Deployment failed")
            sys.exit(1)

    except Exception as e:
        logger.error(f"Deployment error: {e}")
        deployment.shutdown()
        sys.exit(1)

if __name__ == "__main__":
    main()
