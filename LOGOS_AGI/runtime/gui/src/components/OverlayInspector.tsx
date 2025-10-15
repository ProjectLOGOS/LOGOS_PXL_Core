import { useState } from 'react';
import { apiClient } from '../api/client';

interface OverlayResult {
  result?: Record<string, unknown>;
  chrono_trace?: string[];
  v4_trace?: string[];
}

export default function OverlayInspector() {
  const [formula, setFormula] = useState('{"type": "implies", "left": "A", "right": "B"}');
  const [overlayType, setOverlayType] = useState<'chrono' | 'v4'>('chrono');
  const [operation, setOperation] = useState<'normalize' | 'validate' | 'transform' | 'translate' | 'adapt'>('normalize');
  const [result, setResult] = useState<OverlayResult | null>(null);
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

      let response;
      if (overlayType === 'chrono') {
        response = await apiClient.chronoOverlay({
          operation: operation as 'normalize' | 'validate' | 'transform',
          formula: parsedFormula,
        });
      } else {
        response = await apiClient.v4Overlay({
          operation: operation as 'translate' | 'validate' | 'adapt',
          formula: parsedFormula,
        });
      }

      setResult(response);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Unknown error');
    } finally {
      setLoading(false);
    }
  };

  const getOperationOptions = () => {
    if (overlayType === 'chrono') {
      return [
        { value: 'normalize', label: 'Normalize - Apply constructive normalization' },
        { value: 'validate', label: 'Validate - Check constructive validity' },
        { value: 'transform', label: 'Transform - Apply constructive transformation' },
      ];
    } else {
      return [
        { value: 'translate', label: 'Translate - Map to V4 types' },
        { value: 'validate', label: 'Validate - Check V4 consistency' },
        { value: 'adapt', label: 'Adapt - Apply V4 adapter logic' },
      ];
    }
  };

  return (
    <div style={{padding: '16px', maxWidth: '1000px', margin: '0 auto'}}>
      <h2>Overlay Inspector</h2>
      <p>Inspect Chrono and V4 adapter operations with I/O diffs</p>

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

        <div style={{display: 'flex', gap: '16px', marginBottom: '16px'}}>
          <div style={{flex: 1}}>
            <label style={{display: 'block', marginBottom: '4px', fontWeight: 'bold'}}>
              Overlay Type:
            </label>
            <select
              value={overlayType}
              onChange={(e) => {
                setOverlayType(e.target.value as typeof overlayType);
                setOperation(e.target.value === 'chrono' ? 'normalize' : 'translate');
              }}
              style={{width: '100%', padding: '8px', border: '1px solid #ccc', borderRadius: '4px'}}
            >
              <option value="chrono">Chrono (Constructive IEL)</option>
              <option value="v4">V4 (Conservative Integration)</option>
            </select>
          </div>

          <div style={{flex: 1}}>
            <label style={{display: 'block', marginBottom: '4px', fontWeight: 'bold'}}>
              Operation:
            </label>
            <select
              value={operation}
              onChange={(e) => setOperation(e.target.value as typeof operation)}
              style={{width: '100%', padding: '8px', border: '1px solid #ccc', borderRadius: '4px'}}
            >
              {getOperationOptions().map(option => (
                <option key={option.value} value={option.value}>
                  {option.label}
                </option>
              ))}
            </select>
          </div>
        </div>

        <button
          type="submit"
          disabled={loading}
          style={{
            padding: '12px 24px',
            backgroundColor: loading ? '#ccc' : '#28a745',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: loading ? 'not-allowed' : 'pointer'
          }}
        >
          {loading ? 'Processing...' : 'Execute Overlay'}
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
        <div style={{display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '16px'}}>
          <div style={{
            padding: '16px',
            border: '1px solid #ccc',
            borderRadius: '4px',
            backgroundColor: '#f8f9fa'
          }}>
            <h3>Input Formula</h3>
            <pre style={{
              backgroundColor: '#f1f1f1',
              padding: '8px',
              borderRadius: '4px',
              fontSize: '12px',
              overflow: 'auto'
            }}>
              {JSON.stringify(JSON.parse(formula), null, 2)}
            </pre>
          </div>

          <div style={{
            padding: '16px',
            border: '1px solid #ccc',
            borderRadius: '4px',
            backgroundColor: '#f8f9fa'
          }}>
            <h3>Overlay Result</h3>
            <pre style={{
              backgroundColor: '#f1f1f1',
              padding: '8px',
              borderRadius: '4px',
              fontSize: '12px',
              overflow: 'auto'
            }}>
              {JSON.stringify(result.result || {}, null, 2)}
            </pre>
          </div>

          <div style={{
            padding: '16px',
            border: '1px solid #ccc',
            borderRadius: '4px',
            backgroundColor: '#f8f9fa',
            gridColumn: 'span 2'
          }}>
            <h3>Execution Trace</h3>
            <pre style={{
              backgroundColor: '#f1f1f1',
              padding: '8px',
              borderRadius: '4px',
              fontSize: '12px',
              overflow: 'auto',
              maxHeight: '300px'
            }}>
              {(result.chrono_trace || result.v4_trace || []).join('\n')}
            </pre>
          </div>
        </div>
      )}
    </div>
  );
}