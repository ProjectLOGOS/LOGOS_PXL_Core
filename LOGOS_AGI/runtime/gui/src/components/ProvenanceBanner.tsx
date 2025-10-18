import { useState, useEffect } from 'react';
import { apiClient } from '../api/client';

interface ProvenanceData {
  coqchk_stamp?: string;
  build_sha?: string;
  v4_sha?: string;
}

export default function ProvenanceBanner() {
  const [provenance, setProvenance] = useState<ProvenanceData>({});
  const [isValid, setIsValid] = useState(true);

  useEffect(() => {
    const checkProvenance = async () => {
      try {
        const health = await apiClient.getHealth();
        const newProvenance = {
          coqchk_stamp: health.coqchk_stamp,
          build_sha: health.build_sha,
          v4_sha: health.v4_sha,
        };
        setProvenance(newProvenance);

        // Check if all required provenance data is present
        const requiredFields = ['coqchk_stamp', 'build_sha', 'v4_sha'];
        const hasAllFields = requiredFields.every(field =>
          newProvenance[field as keyof ProvenanceData]
        );
        setIsValid(hasAllFields);
      } catch (error) {
        console.error('Failed to fetch provenance:', error);
        setIsValid(false);
      }
    };

    checkProvenance();
    const interval = setInterval(checkProvenance, 30000); // Check every 30 seconds

    return () => clearInterval(interval);
  }, []);

  if (isValid) {
    return null; // Don't show banner if provenance is valid
  }

  return (
    <div style={{
      backgroundColor: '#ff4444',
      color: 'white',
      padding: '8px 16px',
      textAlign: 'center',
      fontSize: '14px',
      fontWeight: 'bold'
    }}>
      ⚠️ CRITICAL: Missing cryptographic provenance headers. System integrity cannot be verified.
      {Object.entries(provenance).map(([key, value]) => (
        <span key={key} style={{marginLeft: '16px'}}>
          {key}: {value || 'MISSING'}
        </span>
      ))}
    </div>
  );
}
