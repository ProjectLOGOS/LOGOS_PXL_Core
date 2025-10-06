"""
LOGOS PXL Core - Pilot Alert System
Monitoring and alerting for production deployment
"""
import time
import json
import requests
from typing import Dict, Any, List, Optional
from enum import Enum
from dataclasses import dataclass
from pathlib import Path

class AlertLevel(Enum):
    INFO = "info"
    WARNING = "warning"
    CRITICAL = "critical"
    EMERGENCY = "emergency"

@dataclass
class Alert:
    id: str
    level: AlertLevel
    title: str
    message: str
    timestamp: int
    component: str
    metric_value: Optional[float] = None
    threshold: Optional[float] = None
    resolved: bool = False

class AlertManager:
    """Pilot deployment alert management"""
    
    def __init__(self, config_path: str = "configs/config.json"):
        self.config_path = Path(config_path)
        self.alerts: List[Alert] = []
        self.alert_rules = self._init_alert_rules()
        
    def _init_alert_rules(self) -> Dict[str, Dict[str, Any]]:
        """Initialize pilot alert rules"""
        return {
            "prover_down": {
                "level": AlertLevel.CRITICAL,
                "title": "PXL Prover Unavailable",
                "check_interval": 30,
                "component": "pxl_prover"
            },
            "kernel_drift": {
                "level": AlertLevel.EMERGENCY,
                "title": "Kernel Hash Drift Detected",
                "check_interval": 60,
                "component": "kernel_validation"
            },
            "denial_spike": {
                "level": AlertLevel.WARNING,
                "title": "High Denial Rate",
                "threshold": 0.05,  # 5% denial rate
                "check_interval": 300,  # 5 minutes
                "component": "authorization"
            },
            "audit_chain_break": {
                "level": AlertLevel.CRITICAL,
                "title": "Audit Chain Integrity Failure",
                "check_interval": 3600,  # 1 hour
                "component": "audit_system"
            },
            "queue_backlog": {
                "level": AlertLevel.WARNING,
                "title": "Request Queue Backlog",
                "threshold": 100,  # 100 queued requests
                "check_interval": 60,
                "component": "executor"
            },
            "response_time_p95": {
                "level": AlertLevel.WARNING,
                "title": "High Response Time P95",
                "threshold": 1500,  # 1.5 seconds
                "check_interval": 300,
                "component": "performance"
            }
        }
    
    def check_prover_health(self) -> Optional[Alert]:
        """Check if PXL prover is responding"""
        try:
            with open(self.config_path, 'r') as f:
                config = json.load(f)
            
            prover_url = config.get("pxl_prover_url", "http://127.0.0.1:8088")
            response = requests.get(f"{prover_url}/health", timeout=5)
            
            if response.status_code != 200:
                return Alert(
                    id="prover_down_001",
                    level=AlertLevel.CRITICAL,
                    title="PXL Prover Unavailable",
                    message=f"Prover returned {response.status_code}",
                    timestamp=int(time.time() * 1000),
                    component="pxl_prover"
                )
        except Exception as e:
            return Alert(
                id="prover_down_002", 
                level=AlertLevel.CRITICAL,
                title="PXL Prover Connection Failed",
                message=f"Unable to connect to prover: {str(e)}",
                timestamp=int(time.time() * 1000),
                component="pxl_prover"
            )
        
        return None
    
    def check_kernel_drift(self) -> Optional[Alert]:
        """Check for kernel hash drift"""
        try:
            from pilot.pilot_guard import pilot_guard
            
            kernel_ok, kernel_msg = pilot_guard.validate_kernel_freeze()
            if not kernel_ok:
                return Alert(
                    id="kernel_drift_001",
                    level=AlertLevel.EMERGENCY,
                    title="Kernel Hash Drift Detected",
                    message=kernel_msg,
                    timestamp=int(time.time() * 1000),
                    component="kernel_validation"
                )
        except Exception as e:
            return Alert(
                id="kernel_drift_002",
                level=AlertLevel.CRITICAL,
                title="Kernel Validation Failed",
                message=f"Unable to validate kernel: {str(e)}",
                timestamp=int(time.time() * 1000),
                component="kernel_validation"
            )
        
        return None
    
    def check_service_health(self, service_name: str, url: str) -> Optional[Alert]:
        """Check if a service is healthy"""
        try:
            response = requests.get(f"{url}/health", timeout=3)
            if response.status_code != 200:
                return Alert(
                    id=f"service_down_{service_name}",
                    level=AlertLevel.WARNING,
                    title=f"Service {service_name} Unhealthy",
                    message=f"Service returned {response.status_code}",
                    timestamp=int(time.time() * 1000),
                    component=service_name
                )
        except Exception as e:
            return Alert(
                id=f"service_down_{service_name}",
                level=AlertLevel.WARNING,
                title=f"Service {service_name} Unavailable",
                message=f"Connection failed: {str(e)}",
                timestamp=int(time.time() * 1000),
                component=service_name
            )
        
        return None
    
    def check_audit_integrity(self) -> Optional[Alert]:
        """Check audit trail integrity"""
        try:
            from audit.audit_system import audit
            
            integrity_result = audit.verify_integrity()
            if not integrity_result.get("verified", False):
                return Alert(
                    id="audit_integrity_001",
                    level=AlertLevel.CRITICAL,
                    title="Audit Chain Integrity Failure",
                    message=integrity_result.get("error", "Unknown integrity error"),
                    timestamp=int(time.time() * 1000),
                    component="audit_system"
                )
        except Exception as e:
            return Alert(
                id="audit_integrity_002",
                level=AlertLevel.WARNING,
                title="Audit Integrity Check Failed",
                message=f"Unable to verify audit integrity: {str(e)}",
                timestamp=int(time.time() * 1000),
                component="audit_system"
            )
        
        return None
    
    def run_all_checks(self) -> List[Alert]:
        """Run all alert checks and return new alerts"""
        new_alerts = []
        
        # Check prover health
        prover_alert = self.check_prover_health()
        if prover_alert:
            new_alerts.append(prover_alert)
        
        # Check kernel drift
        kernel_alert = self.check_kernel_drift()
        if kernel_alert:
            new_alerts.append(kernel_alert)
        
        # Check core services
        services = [
            ("logos_api", "http://127.0.0.1:8090"),
            ("executor", "http://127.0.0.1:8072"),
            ("tool_router", "http://127.0.0.1:8071"),
            ("crawl_toolkit", "http://127.0.0.1:8064")
        ]
        
        for service_name, service_url in services:
            service_alert = self.check_service_health(service_name, service_url)
            if service_alert:
                new_alerts.append(service_alert)
        
        # Check audit integrity
        audit_alert = self.check_audit_integrity()
        if audit_alert:
            new_alerts.append(audit_alert)
        
        # Add to alerts list
        self.alerts.extend(new_alerts)
        
        return new_alerts
    
    def get_active_alerts(self) -> List[Alert]:
        """Get all unresolved alerts"""
        return [alert for alert in self.alerts if not alert.resolved]
    
    def get_alerts_by_level(self, level: AlertLevel) -> List[Alert]:
        """Get alerts by severity level"""
        return [alert for alert in self.alerts if alert.level == level and not alert.resolved]
    
    def resolve_alert(self, alert_id: str) -> bool:
        """Mark alert as resolved"""
        for alert in self.alerts:
            if alert.id == alert_id:
                alert.resolved = True
                return True
        return False
    
    def get_alert_summary(self) -> Dict[str, Any]:
        """Get summary of current alert status"""
        active_alerts = self.get_active_alerts()
        
        summary = {
            "total_active": len(active_alerts),
            "by_level": {
                "emergency": len(self.get_alerts_by_level(AlertLevel.EMERGENCY)),
                "critical": len(self.get_alerts_by_level(AlertLevel.CRITICAL)),
                "warning": len(self.get_alerts_by_level(AlertLevel.WARNING)),
                "info": len(self.get_alerts_by_level(AlertLevel.INFO))
            },
            "latest_alerts": [
                {
                    "id": alert.id,
                    "level": alert.level.value,
                    "title": alert.title,
                    "component": alert.component,
                    "timestamp": alert.timestamp
                }
                for alert in sorted(active_alerts, key=lambda x: x.timestamp, reverse=True)[:5]
            ]
        }
        
        return summary

# Global alert manager
alert_manager = AlertManager()

if __name__ == "__main__":
    print("🚨 LOGOS Alert System - Pilot Deployment")
    print("=" * 45)
    
    # Run all checks
    new_alerts = alert_manager.run_all_checks()
    
    if new_alerts:
        print(f"\n⚠️  {len(new_alerts)} NEW ALERTS:")
        for alert in new_alerts:
            level_emoji = {
                AlertLevel.INFO: "ℹ️",
                AlertLevel.WARNING: "⚠️",
                AlertLevel.CRITICAL: "🚨",
                AlertLevel.EMERGENCY: "🔥"
            }[alert.level]
            
            print(f"   {level_emoji} {alert.title}")
            print(f"      Component: {alert.component}")
            print(f"      Message: {alert.message}")
            print()
    else:
        print("\n✅ All systems nominal - no alerts")
    
    # Display summary
    summary = alert_manager.get_alert_summary()
    print(f"📊 ALERT SUMMARY:")
    print(f"   Total Active: {summary['total_active']}")
    print(f"   Emergency: {summary['by_level']['emergency']}")
    print(f"   Critical: {summary['by_level']['critical']}")
    print(f"   Warning: {summary['by_level']['warning']}")
    print(f"   Info: {summary['by_level']['info']}")