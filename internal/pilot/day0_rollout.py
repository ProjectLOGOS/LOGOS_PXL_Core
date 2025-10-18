"""
LOGOS PXL Core - Day-0 Rollout Configuration
Tenant management, SLOs, and initial deployment setup
"""

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


@dataclass
class TenantConfig:
    """Tenant/project configuration for pilot"""

    tenant_id: str
    project_name: str
    allowlist_domains: set[str]
    safe_actions: set[str]
    denial_budget_percent: float
    created_at: int
    active: bool = True


@dataclass
class SLO:
    """Service Level Objective definition"""

    name: str
    description: str
    metric: str
    target_value: float
    unit: str
    measurement_window_minutes: int
    alert_threshold: float


class Day0Rollout:
    """Day-0 rollout configuration and management"""

    def __init__(self, config_dir: str = "pilot/config"):
        self.config_dir = Path(config_dir)
        self.config_dir.mkdir(exist_ok=True)

    def create_pilot_tenant(self, tenant_id: str, project_name: str) -> TenantConfig:
        """Create a new pilot tenant configuration"""
        tenant = TenantConfig(
            tenant_id=tenant_id,
            project_name=project_name,
            allowlist_domains={"example.org", "arxiv.org", "acm.org", "ieee.org", "ietf.org"},
            safe_actions={
                "task:predict_outcomes",
                "task:cluster_texts",
                "task:construct_proof",
                "task:analyze_data",
                "task:generate_summary",
            },
            denial_budget_percent=2.0,
            created_at=int(time.time() * 1000),
        )

        # Save tenant config
        tenant_file = self.config_dir / f"tenant_{tenant_id}.json"
        with open(tenant_file, "w") as f:
            # Convert set to list for JSON serialization
            tenant_dict = asdict(tenant)
            tenant_dict["allowlist_domains"] = list(tenant.allowlist_domains)
            tenant_dict["safe_actions"] = list(tenant.safe_actions)
            json.dump(tenant_dict, f, indent=2)

        return tenant

    def get_pilot_slos(self) -> list[SLO]:
        """Define pilot SLOs as per requirements"""
        return [
            SLO(
                name="proof_p50",
                description="Proof generation 50th percentile response time",
                metric="response_time_ms",
                target_value=300.0,
                unit="ms",
                measurement_window_minutes=5,
                alert_threshold=350.0,
            ),
            SLO(
                name="proof_p95",
                description="Proof generation 95th percentile response time",
                metric="response_time_ms",
                target_value=1500.0,
                unit="ms",
                measurement_window_minutes=5,
                alert_threshold=1800.0,
            ),
            SLO(
                name="denial_budget",
                description="Maximum allowable denial rate",
                metric="denial_rate_percent",
                target_value=2.0,
                unit="percent",
                measurement_window_minutes=15,
                alert_threshold=2.5,
            ),
            SLO(
                name="service_availability",
                description="Core service uptime",
                metric="uptime_percent",
                target_value=99.5,
                unit="percent",
                measurement_window_minutes=60,
                alert_threshold=99.0,
            ),
            SLO(
                name="audit_integrity",
                description="Audit chain integrity verification success rate",
                metric="integrity_success_percent",
                target_value=100.0,
                unit="percent",
                measurement_window_minutes=1440,  # Daily
                alert_threshold=99.9,
            ),
        ]

    def create_nightly_verification_config(self) -> dict[str, Any]:
        """Create nightly verification configuration"""
        return {
            "enabled": True,
            "schedule": "02:00",  # 2 AM daily
            "proof_replay": {
                "enabled": True,
                "sample_percent": 1.0,  # 1% of all proofs
                "max_replays_per_night": 1000,
                "timeout_ms": 5000,
            },
            "audit_chain_verification": {
                "enabled": True,
                "full_chain_check": True,
                "hash_integrity_check": True,
                "backup_verification": True,
            },
            "performance_analysis": {
                "enabled": True,
                "slo_compliance_check": True,
                "trend_analysis": True,
                "anomaly_detection": True,
            },
            "reporting": {
                "enabled": True,
                "email_recipients": ["pilot-ops@logos.dev"],
                "slack_webhook": None,  # Configure in production
                "report_format": "json",
            },
        }

    def create_data_governance_config(self) -> dict[str, Any]:
        """Create data governance configuration"""
        return {
            "file_upload_attestation": {
                "enabled": True,
                "required_fields": ["source", "classification", "retention_period"],
                "attestation_signature_required": True,
                "virus_scanning": True,
                "content_type_validation": True,
            },
            "cache_policy": {
                "strategy": "hash_ttl",
                "default_ttl_hours": 24,
                "max_cache_size_mb": 1024,
                "eviction_policy": "lru",
                "integrity_check_interval_hours": 6,
            },
            "crawled_page_snapshots": {
                "enabled": True,
                "retention_days": 30,
                "compression_enabled": True,
                "deduplication_enabled": True,
                "storage_path": "data/snapshots",
                "metadata_tracking": True,
            },
            "data_retention": {
                "audit_logs_days": 2555,  # 7 years
                "performance_metrics_days": 365,
                "cached_content_days": 90,
                "user_sessions_days": 30,
            },
            "privacy_compliance": {
                "anonymize_logs": True,
                "pii_detection": True,
                "gdpr_compliance": True,
                "data_subject_requests": True,
            },
        }

    def generate_pilot_deployment_manifest(self) -> dict[str, Any]:
        """Generate complete pilot deployment manifest"""
        timestamp = int(time.time() * 1000)

        manifest = {
            "deployment_info": {
                "version": "1.0.0-pilot",
                "deployment_id": f"pilot_{timestamp}",
                "deployment_date": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
                "environment": "pilot",
                "frozen_kernel_hash": "c54592b5bc637d1bdb650bcc614a3c5de09dda1eabef6cced2e74fd5c53ca49c",
            },
            "slos": [asdict(slo) for slo in self.get_pilot_slos()],
            "nightly_verification": self.create_nightly_verification_config(),
            "data_governance": self.create_data_governance_config(),
            "service_endpoints": {
                "logos_api": "http://127.0.0.1:8090",
                "executor": "http://127.0.0.1:8072",
                "tool_router": "http://127.0.0.1:8071",
                "crawl_toolkit": "http://127.0.0.1:8064",
                "gui_dashboard": "http://127.0.0.1:8095",
                "pxl_prover": "http://127.0.0.1:8088",
            },
            "security_policies": {
                "rbac_enabled": True,
                "deny_by_default": True,
                "audit_all_decisions": True,
                "kernel_drift_protection": True,
                "tls_required": False,  # Enable after certificate setup
                "session_timeout_minutes": 480,  # 8 hours
            },
            "monitoring": {
                "alerts_enabled": True,
                "metrics_collection": True,
                "health_check_interval_seconds": 30,
                "performance_monitoring": True,
                "audit_monitoring": True,
            },
        }

        return manifest

    def save_deployment_manifest(self, manifest: dict[str, Any]) -> str:
        """Save deployment manifest to file"""
        manifest_file = self.config_dir / "pilot_deployment_manifest.json"
        with open(manifest_file, "w") as f:
            json.dump(manifest, f, indent=2)

        return str(manifest_file)

    def validate_slo_compliance(self, metrics: dict[str, float]) -> dict[str, Any]:
        """Validate current metrics against SLOs"""
        slos = self.get_pilot_slos()
        compliance_results = {}

        for slo in slos:
            metric_value = metrics.get(slo.metric, None)
            if metric_value is None:
                compliance_results[slo.name] = {
                    "status": "unknown",
                    "message": f"Metric {slo.metric} not available",
                }
                continue

            # Check compliance based on SLO type
            if slo.name in ["proof_p50", "proof_p95"] or slo.name == "denial_budget":
                # Lower is better
                compliant = metric_value <= slo.target_value
                breach = metric_value > slo.alert_threshold
            else:
                # Higher is better (availability, integrity)
                compliant = metric_value >= slo.target_value
                breach = metric_value < slo.alert_threshold

            status = "compliant" if compliant else ("breach" if breach else "warning")

            compliance_results[slo.name] = {
                "status": status,
                "current_value": metric_value,
                "target_value": slo.target_value,
                "alert_threshold": slo.alert_threshold,
                "unit": slo.unit,
            }

        return compliance_results


# Global rollout manager
day0_rollout = Day0Rollout()

if __name__ == "__main__":
    print("🚀 LOGOS Day-0 Rollout Configuration")
    print("=" * 40)

    # Create pilot tenant
    pilot_tenant = day0_rollout.create_pilot_tenant("pilot_001", "LOGOS Pilot Deployment")
    print(f"✅ Created pilot tenant: {pilot_tenant.project_name}")
    print(f"   Tenant ID: {pilot_tenant.tenant_id}")
    print(f"   Allowlist domains: {len(pilot_tenant.allowlist_domains)}")
    print(f"   Safe actions: {len(pilot_tenant.safe_actions)}")
    print(f"   Denial budget: {pilot_tenant.denial_budget_percent}%")

    # Display SLOs
    slos = day0_rollout.get_pilot_slos()
    print(f"\n📊 PILOT SLOs ({len(slos)} defined):")
    for slo in slos:
        print(
            f"   • {slo.name}: ≤{slo.target_value}{slo.unit} (alert at {slo.alert_threshold}{slo.unit})"
        )
        print(f"     {slo.description}")

    # Generate and save manifest
    manifest = day0_rollout.generate_pilot_deployment_manifest()
    manifest_file = day0_rollout.save_deployment_manifest(manifest)
    print(f"\n📋 Deployment manifest saved: {manifest_file}")

    # Show key configurations
    print("\n🔧 KEY CONFIGURATIONS:")
    print(
        f"   Nightly verification: {manifest['nightly_verification']['proof_replay']['sample_percent']}% replay"
    )
    print(
        f"   File upload attestation: {manifest['data_governance']['file_upload_attestation']['enabled']}"
    )
    print(f"   Cache strategy: {manifest['data_governance']['cache_policy']['strategy']}")
    print(
        f"   Audit retention: {manifest['data_governance']['data_retention']['audit_logs_days']} days"
    )

    print("\n🛡️ SECURITY STATUS:")
    print(f"   RBAC: {manifest['security_policies']['rbac_enabled']}")
    print(f"   Deny-by-default: {manifest['security_policies']['deny_by_default']}")
    print(f"   Kernel protection: {manifest['security_policies']['kernel_drift_protection']}")
    print(f"   Audit all decisions: {manifest['security_policies']['audit_all_decisions']}")
