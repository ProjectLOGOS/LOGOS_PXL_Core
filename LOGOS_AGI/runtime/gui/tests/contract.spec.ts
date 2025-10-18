import { test, expect } from '@playwright/test';

test.describe('GUI Contract Tests', () => {
  test.beforeEach(async ({ page }) => {
    // Mock API responses
    await page.route('**/v1/health', async route => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          status: 'healthy',
          version: '1.0.0',
          coqchk_stamp: 'test-stamp-123',
          build_sha: 'abcd1234',
          v4_sha: 'efgh5678'
        })
      });
    });
  });

  test('should load homepage with navigation', async ({ page }) => {
    await page.goto('/');

    // Check title
    await expect(page).toHaveTitle(/LOGOS PXL Core/);

    // Check navigation links
    await expect(page.locator('nav a:has-text("Home")')).toBeVisible();
    await expect(page.locator('nav a:has-text("Proof Console")')).toBeVisible();
    await expect(page.locator('nav a:has-text("Overlay Inspector")')).toBeVisible();
    await expect(page.locator('nav a:has-text("Health & Provenance")')).toBeVisible();

    // Check main content
    await expect(page.locator('h2:has-text("LOGOS PXL Core - Production GUI")')).toBeVisible();
  });

  test('should navigate to proof console', async ({ page }) => {
    await page.goto('/');
    await page.click('text=Proof Console');

    await expect(page.locator('h2:has-text("Proof Console")')).toBeVisible();
    await expect(page.locator('textarea[placeholder*="implies"]')).toBeVisible();
    await expect(page.locator('select')).toContainText('Chrono');
    await expect(page.locator('button:has-text("Submit Proof")')).toBeVisible();
  });

  test('should submit proof request', async ({ page }) => {
    // Mock proof submission
    await page.route('**/v1/proofs', async route => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          verdict: 'valid',
          trace: ['Applied chrono normalization', 'Verified constructive proof'],
          certificate: 'proof_certificate_data',
          proof_id: 'proof-123',
          elapsed_ms: 150
        })
      });
    });

    await page.goto('/proofs');

    // Fill formula
    await page.fill('textarea', '{"type": "implies", "left": "A", "right": "B"}');

    // Submit proof
    await page.click('button:has-text("Submit Proof")');

    // Check result
    await expect(page.locator('text=Verdict:')).toBeVisible();
    await expect(page.locator('text=VALID')).toBeVisible();
    await expect(page.locator('text=proof-123')).toBeVisible();
  });

  test('should navigate to overlay inspector', async ({ page }) => {
    await page.goto('/');
    await page.click('text=Overlay Inspector');

    await expect(page.locator('h2:has-text("Overlay Inspector")')).toBeVisible();
    await expect(page.locator('select')).toContainText('Chrono');
    await expect(page.locator('select')).toContainText('V4');
    await expect(page.locator('button:has-text("Execute Overlay")')).toBeVisible();
  });

  test('should execute chrono overlay', async ({ page }) => {
    // Mock overlay execution
    await page.route('**/v1/overlays/chrono', async route => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          result: { normalized: true, constructive: true },
          chrono_trace: ['Parsed formula', 'Applied normalization', 'Verified constructivity']
        })
      });
    });

    await page.goto('/overlays');

    // Fill formula
    await page.fill('textarea', '{"type": "implies", "left": "A", "right": "B"}');

    // Execute overlay
    await page.click('button:has-text("Execute Overlay")');

    // Check result
    await expect(page.locator('text=chrono_trace')).toBeVisible();
    await expect(page.locator('text=Parsed formula')).toBeVisible();
  });

  test('should display health dashboard', async ({ page }) => {
    await page.goto('/');
    await page.click('text=Health & Provenance');

    await expect(page.locator('h2:has-text("Health & Provenance Dashboard")')).toBeVisible();
    await expect(page.locator('text=System Status')).toBeVisible();
    await expect(page.locator('text=Coq Verification')).toBeVisible();
    await expect(page.locator('text=Build Provenance')).toBeVisible();
    await expect(page.locator('text=V4 Integration')).toBeVisible();
  });

  test('should show provenance data', async ({ page }) => {
    await page.goto('/health');

    // Check provenance headers are displayed
    await expect(page.locator('text=test-stamp-123')).toBeVisible();
    await expect(page.locator('text=abcd1234')).toBeVisible();
    await expect(page.locator('text=efgh5678')).toBeVisible();
  });

  test('should show red banner when provenance missing', async ({ page }) => {
    // Mock missing provenance
    await page.route('**/v1/health', async route => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          status: 'healthy',
          version: '1.0.0'
          // Missing provenance fields
        })
      });
    });

    await page.goto('/');
    await page.reload();

    // Check red banner appears
    await expect(page.locator('text=CRITICAL: Missing cryptographic provenance')).toBeVisible();
  });
});
