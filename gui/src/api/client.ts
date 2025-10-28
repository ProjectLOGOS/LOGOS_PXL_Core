import type { paths } from './types.js';

type HttpMethod = 'GET' | 'POST' | 'PUT' | 'DELETE';

interface ApiConfig {
  baseUrl: string;
  token?: string;
}

class ApiClient {
  private config: ApiConfig;

  constructor(config: ApiConfig) {
    this.config = config;
  }

  private async request<T>(
    method: HttpMethod,
    path: string,
    body?: unknown
  ): Promise<T> {
    const url = `${this.config.baseUrl}${path}`;
    const headers: Record<string, string> = {
      'Content-Type': 'application/json',
    };

    if (this.config.token) {
      headers['Authorization'] = `Bearer ${this.config.token}`;
    }

    const response = await fetch(url, {
      method,
      headers,
      body: body ? JSON.stringify(body) : undefined,
    });

    if (!response.ok) {
      throw new Error(`API Error: ${response.status} ${response.statusText}`);
    }

    return response.json();
  }

  // Health check
  async getHealth() {
    return this.request<paths['/v1/health']['get']['responses']['200']['content']['application/json']>(
      'GET',
      '/v1/health'
    );
  }

  // Proof submission
  async submitProof(params: {
    formula: Record<string, unknown>;
    context?: Record<string, unknown>;
    overlay?: 'chrono' | 'v4' | 'modal';
    timeout?: number;
  }) {
    return this.request<paths['/v1/proofs']['post']['responses']['200']['content']['application/json']>(
      'POST',
      '/v1/proofs',
      params
    );
  }

  // Get proof status
  async getProofStatus(proofId: string) {
    return this.request<paths['/v1/proofs/{proof_id}']['get']['responses']['200']['content']['application/json']>(
      'GET',
      `/v1/proofs/${proofId}`
    );
  }

  // Chrono overlay
  async chronoOverlay(params: {
    operation: 'normalize' | 'validate' | 'transform';
    formula: Record<string, unknown>;
  }) {
    return this.request<paths['/v1/overlays/chrono']['post']['responses']['200']['content']['application/json']>(
      'POST',
      '/v1/overlays/chrono',
      params
    );
  }

  // V4 overlay
  async v4Overlay(params: {
    operation: 'translate' | 'validate' | 'adapt';
    formula: Record<string, unknown>;
  }) {
    return this.request<paths['/v1/overlays/v4']['post']['responses']['200']['content']['application/json']>(
      'POST',
      '/v1/overlays/v4',
      params
    );
  }
}

// Create default client
const apiClient = new ApiClient({
  baseUrl: import.meta.env.VITE_API_BASE || 'http://localhost:8080',
});

export { ApiClient, apiClient };
export type { ApiConfig };