import { useState } from 'react';
import { apiClient } from '../api/client';

interface ProofResult {
  verdict?: 'valid' | 'invalid' | 'unknown';
  trace?: string[];
  certificate?: string;
  proof_id?: string;
  elapsed_ms?: number;
}

export default function ProofConsole() {
  const [formula, setFormula] = useState('{"type": "implies", "left": "A", "right": "B"}');
  const [overlay, setOverlay] = useState<'chrono' | 'v4' | 'modal'>('chrono');
  const [timeout, setTimeout] = useState(30);
  const [result, setResult] = useState<ProofResult | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    setLoading(true);
    setError(null);

    try {
      let parsedFormula;
      try {
        parsedFormula = JSON.parse(formula);
      } catch {
        throw new Error('Invalid JSON formula');
      }

      const response = await apiClient.submitProof({
        formula: parsedFormula,
        overlay,
        timeout,
      });

      setResult(response);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Unknown error');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div style={{padding: '16px', maxWidth: '800px', margin: '0 auto'}}>
      <h2>Proof Console</h2>
      <p>Submit logical goals for Coq-verified proof</p>

      <form onSubmit={handleSubmit} style={{marginBottom: '24px'}}>
        <div style={{marginBottom: '16px'}}>
          <label style={{display: 'block', marginBottom: '4px', fontWeight: 'bold'}}>
            Formula (JSON):
          </label>
          <textarea
            value={formula}
            onChange={(e) => setFormula(e.target.value)}
            style={{
              width: '100%',
              height: '100px',
              padding: '8px',
              border: '1px solid #ccc',
              borderRadius: '4px',
              fontFamily: 'monospace'
            }}
            placeholder='{"type": "implies", "left": "A", "right": "B"}'
          />
        </div>

        <div style={{marginBottom: '16px'}}>
          <label style={{display: 'block', marginBottom: '4px', fontWeight: 'bold'}}>
            Overlay:
          </label>
          <select
            value={overlay}
            onChange={(e) => setOverlay(e.target.value as typeof overlay)}
            style={{padding: '8px', border: '1px solid #ccc', borderRadius: '4px'}}
          >
            <option value="chrono">Chrono (Constructive)</option>
            <option value="v4">V4 (Conservative)</option>
            <option value="modal">Modal</option>
          </select>
        </div>

        <div style={{marginBottom: '16px'}}>
          <label style={{display: 'block', marginBottom: '4px', fontWeight: 'bold'}}>
            Timeout (seconds):
          </label>
          <input
            type="number"
            value={timeout}
            onChange={(e) => setTimeout(Number(e.target.value))}
            min="1"
            max="300"
            style={{padding: '8px', border: '1px solid #ccc', borderRadius: '4px'}}
          />
        </div>

        <button
          type="submit"
          disabled={loading}
          style={{
            padding: '12px 24px',
            backgroundColor: loading ? '#ccc' : '#007bff',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: loading ? 'not-allowed' : 'pointer'
          }}
        >
          {loading ? 'Proving...' : 'Submit Proof'}
        </button>
      </form>

      {error && (
        <div style={{
          padding: '12px',
          backgroundColor: '#f8d7da',
          border: '1px solid #f5c6cb',
          borderRadius: '4px',
          color: '#721c24',
          marginBottom: '16px'
        }}>
          <strong>Error:</strong> {error}
        </div>
      )}

      {result && (
        <div style={{
          padding: '16px',
          border: '1px solid #ccc',
          borderRadius: '4px',
          backgroundColor: '#f8f9fa'
        }}>
          <h3>Proof Result</h3>
          <p><strong>Verdict:</strong>
            <span style={{
              color: result.verdict === 'valid' ? '#28a745' :
                     result.verdict === 'invalid' ? '#dc3545' : '#ffc107',
              fontWeight: 'bold',
              marginLeft: '8px'
            }}>
              {(result.verdict || 'unknown').toUpperCase()}
            </span>
          </p>

          {result.elapsed_ms && (
            <p><strong>Elapsed:</strong> {result.elapsed_ms}ms</p>
          )}

          {result.proof_id && (
            <p><strong>Proof ID:</strong> {result.proof_id}</p>
          )}

          <div style={{marginTop: '16px'}}>
            <strong>Trace:</strong>
            <pre style={{
              backgroundColor: '#f1f1f1',
              padding: '8px',
              borderRadius: '4px',
              marginTop: '8px',
              fontSize: '12px',
              overflow: 'auto'
            }}>
              {(result.trace || []).join('\n')}
            </pre>
          </div>

          {result.certificate && (
            <div style={{marginTop: '16px'}}>
              <strong>Certificate:</strong>
              <pre style={{
                backgroundColor: '#f1f1f1',
                padding: '8px',
                borderRadius: '4px',
                marginTop: '8px',
                fontSize: '10px',
                overflow: 'auto',
                wordBreak: 'break-all'
              }}>
                {result.certificate}
              </pre>
            </div>
          )}
        </div>
      )}
    </div>
  );
}
