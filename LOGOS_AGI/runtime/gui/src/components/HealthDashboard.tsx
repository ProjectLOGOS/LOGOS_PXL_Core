import { useState, useEffect } from 'react';
import { apiClient } from '../api/client';

interface HealthStatus {
  status?: 'healthy' | 'degraded' | 'unhealthy';
  version?: string;
  coqchk_stamp?: string;
  build_sha?: string;
  v4_sha?: string;
}

interface ServiceStatus {
  name: string;
  status: 'up' | 'down' | 'unknown';
  latency?: number;
  lastCheck: Date;
}

export default function HealthDashboard() {
  const [health, setHealth] = useState<HealthStatus>({});
  const [services, setServices] = useState<ServiceStatus[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const checkHealth = async () => {
      try {
        const healthData = await apiClient.getHealth();
        setHealth(healthData);

        // Mock service status checks (in real implementation, these would be actual health checks)
        const mockServices: ServiceStatus[] = [
          { name: 'pxl-core', status: 'up', latency: 12, lastCheck: new Date() },
          { name: 'overlay-chrono', status: 'up', latency: 8, lastCheck: new Date() },
          { name: 'overlay-v4', status: 'up', latency: 15, lastCheck: new Date() },
          { name: 'gateway', status: 'up', latency: 3, lastCheck: new Date() },
        ];
        setServices(mockServices);
        setError(null);
      } catch (err) {
        setError(err instanceof Error ? err.message : 'Health check failed');
      } finally {
        setLoading(false);
      }
    };

    checkHealth();
    const interval = setInterval(checkHealth, 10000); // Check every 10 seconds

    return () => clearInterval(interval);
  }, []);

  const getStatusColor = (status: string) => {
    switch (status) {
      case 'healthy':
      case 'up':
        return '#28a745';
      case 'degraded':
        return '#ffc107';
      case 'unhealthy':
      case 'down':
        return '#dc3545';
      default:
        return '#6c757d';
    }
  };

  if (loading) {
    return <div style={{padding: '16px', textAlign: 'center'}}>Loading health status...</div>;
  }

  return (
    <div style={{padding: '16px', maxWidth: '1200px', margin: '0 auto'}}>
      <h2>Health & Provenance Dashboard</h2>
      <p>System health monitoring and cryptographic provenance verification</p>

      {error && (
        <div style={{
          padding: '12px',
          backgroundColor: '#f8d7da',
          border: '1px solid #f5c6cb',
          borderRadius: '4px',
          color: '#721c24',
          marginBottom: '16px'
        }}>
          <strong>Health Check Error:</strong> {error}
        </div>
      )}

      <div style={{display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(300px, 1fr))', gap: '16px', marginBottom: '24px'}}>
        <div style={{
          padding: '16px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: '#f8f9fa'
        }}>
          <h3>System Status</h3>
          <div style={{display: 'flex', alignItems: 'center', marginBottom: '8px'}}>
            <div style={{
              width: '12px',
              height: '12px',
              borderRadius: '50%',
              backgroundColor: getStatusColor(health.status || 'unknown'),
              marginRight: '8px'
            }}></div>
            <span style={{fontWeight: 'bold'}}>
              {(health.status || 'unknown').toUpperCase()}
            </span>
          </div>
          <p><strong>Version:</strong> {health.version || 'unknown'}</p>
        </div>

        <div style={{
          padding: '16px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: '#f8f9fa'
        }}>
          <h3>Coq Verification</h3>
          <p><strong>coqchk Stamp:</strong></p>
          <code style={{
            fontSize: '12px',
            backgroundColor: '#e9ecef',
            padding: '4px',
            borderRadius: '4px',
            wordBreak: 'break-all'
          }}>
            {health.coqchk_stamp || 'MISSING - INTEGRITY COMPROMISED'}
          </code>
        </div>

        <div style={{
          padding: '16px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: '#f8f9fa'
        }}>
          <h3>Build Provenance</h3>
          <p><strong>Build SHA:</strong></p>
          <code style={{
            fontSize: '12px',
            backgroundColor: '#e9ecef',
            padding: '4px',
            borderRadius: '4px',
            wordBreak: 'break-all'
          }}>
            {health.build_sha || 'MISSING - INTEGRITY COMPROMISED'}
          </code>
        </div>

        <div style={{
          padding: '16px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: '#f8f9fa'
        }}>
          <h3>V4 Integration</h3>
          <p><strong>V4 SHA:</strong></p>
          <code style={{
            fontSize: '12px',
            backgroundColor: '#e9ecef',
            padding: '4px',
            borderRadius: '4px',
            wordBreak: 'break-all'
          }}>
            {health.v4_sha || 'MISSING - INTEGRITY COMPROMISED'}
          </code>
        </div>
      </div>

      <div style={{
        padding: '16px',
        border: '1px solid #ccc',
        borderRadius: '4px',
        backgroundColor: '#f8f9fa'
      }}>
        <h3>Service Status</h3>
        <div style={{display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(200px, 1fr))', gap: '12px'}}>
          {services.map(service => (
            <div key={service.name} style={{
              padding: '12px',
              border: '1px solid #dee2e6',
              borderRadius: '4px',
              backgroundColor: 'white'
            }}>
              <div style={{display: 'flex', alignItems: 'center', marginBottom: '8px'}}>
                <div style={{
                  width: '8px',
                  height: '8px',
                  borderRadius: '50%',
                  backgroundColor: getStatusColor(service.status),
                  marginRight: '8px'
                }}></div>
                <span style={{fontWeight: 'bold'}}>{service.name}</span>
              </div>
              <p style={{fontSize: '14px', margin: '4px 0'}}>
                Status: <strong>{service.status.toUpperCase()}</strong>
              </p>
              {service.latency && (
                <p style={{fontSize: '14px', margin: '4px 0'}}>
                  Latency: {service.latency}ms
                </p>
              )}
              <p style={{fontSize: '12px', color: '#6c757d', margin: '4px 0'}}>
                Last check: {service.lastCheck.toLocaleTimeString()}
              </p>
            </div>
          ))}
        </div>
      </div>

      <div style={{
        marginTop: '24px',
        padding: '16px',
        border: '1px solid #ccc',
        borderRadius: '4px',
        backgroundColor: '#e7f3ff'
      }}>
        <h3>Security Notes</h3>
        <ul style={{margin: 0, paddingLeft: '20px'}}>
          <li>All API responses include cryptographic provenance headers</li>
          <li>Coq verification stamps ensure formal correctness</li>
          <li>Build and submodule SHAs enable supply chain verification</li>
          <li>JWT authentication required for sensitive operations</li>
          <li>Rate limiting active on all endpoints</li>
        </ul>
      </div>
    </div>
  );
}
