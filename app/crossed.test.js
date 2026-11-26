// Tests for app/crossed.js: the Lean results of Crossed.lean and CrossedEstimation.lean, checked
// numerically (exact expectations, not simulation). Run: node --test app/crossed.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { execFileSync } = require('node:child_process');
const C = require('./crossed.js');
const E = require('./engine.js');

const close = (a, b, tol, msg) =>
  assert.ok(Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b)), `${msg}: ${a} vs ${b}`);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);

test('K = L + Σ is positive definite for any table and noise correlation (Crossed.K_posDef)', () => {
  for (const par of [{}, { nr: 2, nc: 2 }, { nr: 6, nc: 4, rho: 0.8, spread: 1 }, { missing: true, gamma: 0 }]) {
    const ex = C.exact(C.makeWorld(par));
    assert.ok(E.cholesky(ex.K), JSON.stringify(par));
  }
});

test('Balanced table: the blend\'s excess per layer (Crossed.sum_linMse_blendρ) and the three factors (Crossed.blup_balancedρ)', () => {
  for (const par of [{}, { rho: 0.5 }, { nr: 2, nc: 5, alpha: 0.1, beta: 0.02, gamma: 0.05, rho: 0.3 }, { nr: 3, nc: 3, gamma: 0 }]) {
    const w = C.makeWorld(par), ex = C.exact(w), ly = ex.layers;
    assert.ok(ly, 'balanced');
    close(ex.blend - ex.full, ly.excess, 1e-9, 'excess = Σₖ mₖ(λₖ + s)(z̄ − zₖ)²');
    ex.cells.forEach((c) => close(c.z, ly.zbar, 1e-9, 'best z is z̄ in every cell (Crossed.bestZ_KBal)'));
    // the full predictor is the layer formula, for any data x
    const r = E.rng(3), x = Array.from({ length: w.J }, () => r.normal());
    const [zr, zc, zi] = ly.layers.map((l) => l.z), grand = sum(x) / w.J;
    for (let j = 0; j < w.J; j++) {
      const rm = sum(x.filter((_, i) => w.row[i] === w.row[j])) / w.nc, cm = sum(x.filter((_, i) => w.col[i] === w.col[j])) / w.nr;
      close(dot(ex.cells[j].full, x), grand + zr * (rm - grand) + zc * (cm - grand) + zi * (x[j] - rm - cm + grand), 1e-9, `cell ${j}`);
    }
  }
});

test('Unbalanced table: the excess equals the Pythagoras gap Σⱼ (d_blend − d)ᵀK(d_blend − d) (Core.blup_optimal)', () => {
  const ex = C.exact(C.makeWorld({ spread: 1, rho: 0.4, missing: true }));
  assert.equal(ex.layers, null);
  let gap = 0;
  for (const c of ex.cells.filter((c) => c.observed)) { const e = c.blend.map((x, i) => x - c.full[i]); gap += dot(e, ex.K.map((row) => dot(row, e))); }
  close(ex.blend - ex.full, gap, 1e-9, 'gap');
});

test('2×2 without its first cell: the weights and MSE of Crossed.missing_blup / missing_predMse (notes: 3.575)', () => {
  const a2 = 1, b2 = 4, g2 = 0.5, s2 = 2, row = [0, 0, 1, 1], col = [0, 1, 0, 1], obs = [1, 2, 3];
  const L = C.levelCov(obs.map((j) => row[j]), obs.map((j) => col[j]), a2, b2, g2);
  const K = L.map((r, i) => r.map((x, j) => x + (i === j ? s2 : 0)));
  const P = C.predictors(K, row, col, obs, a2, b2, g2), c0 = P.cells[0];
  const s = g2 + s2, D = 4 * a2 * b2 + 4 * (a2 + b2) * s + 3 * s * s;
  const want = [(4 * a2 * b2 + 4 * a2 * s + s * s) / D, (4 * a2 * b2 + 4 * b2 * s + s * s) / D, (s * s - 4 * a2 * b2) / D];
  c0.full.forEach((x, i) => close(x, want[i], 1e-12, `weight ${i}`));
  const mse = C.predMse(K, c0.ell, c0.v, c0.full);
  close(mse, g2 + s * (12 * a2 * b2 + 4 * (a2 + b2) * s + s * s) / D, 1e-12, 'MSE');
  close(mse, 3.575, 1e-3, 'note value');
  close(C.predMse(K, c0.ell, c0.v, c0.blend), 4.814, 1e-3, 'collective mean alone');
});

test('No row or column effects: the full predictor is the thesis BLUP (Core.blupWeight with L = γ²I)', () => {
  const w = C.makeWorld({ alpha: 0, beta: 0, rho: 0.4, spread: 1 }), ex = C.exact(w);
  for (let j = 0; j < w.J; j++) E.blupWeight(ex.K, w.truth.gamma2, j).forEach((x, i) => close(ex.cells[j].full[i], x, 1e-9, `cell ${j}`));
});

/**
 * The exact expectation of a quadratic estimator f of the data: with cov(X) = VVᵀ (Cholesky) and
 * f(constant table) = 0, E f(X) = Σₖ f(V eₖ) (Expectation.integral_quad_of_cov).
 */
function exactMean(world, f) {
  const { obs, T, w, row, col, truth: t } = world, n = obs.length * T;
  const sd = t.sigma2 ** 0.5, V = [];
  for (let a = 0; a < n; a++) {
    V.push([]);
    const i = obs[Math.floor(a / T)], ta = a % T;
    for (let b = 0; b < n; b++) {
      const j = obs[Math.floor(b / T)], tb = b % T;
      const noise = ta === tb ? sd * sd * (i === j ? 1 : t.rho) / Math.sqrt(w[i][ta] * w[j][tb]) : 0;
      V[a].push(noise + (row[i] === row[j] ? t.alpha2 : 0) + (col[i] === col[j] ? t.beta2 : 0) + (i === j ? t.gamma2 : 0));
    }
  }
  const Lc = E.cholesky(V);
  let acc = null;
  for (let k = 0; k < n; k++) {
    const cells = world.row.map((r, j) => ({ row: r, col: col[j], w: obs.includes(j) ? w[j] : null, X: obs.includes(j) ? Array.from({ length: T }, (_, s) => Lc[obs.indexOf(j) * T + s][k]) : null }));
    const v = f({ nr: world.nr, nc: world.nc, cells });
    acc = acc ? acc.map((x, i) => x + v[i]) : v;
  }
  return acc;
}

test('The pair pools are unbiased for α², β², γ², any weights, any noise correlation (Model.crossed_unbiasedX)', () => {
  for (const par of [{ rho: 0.5, spread: 1, T: 5 }, { nr: 3, nc: 2, rho: 0.3, missing: true, T: 4 }]) {
    const w = C.makeWorld(par), t = w.truth;
    for (const wt of ['equal', 'vol']) {
      const m = exactMean(w, (d) => C.pairPools(d, wt).raw);
      [t.alpha2, t.beta2, t.gamma2].forEach((x, k) => close(m[k], x, 1e-9, `${wt} θ${k}`));
    }
  }
});

test('Finding 42: the ANOVA statistics (noise cross term omitted) are biased under correlated noise; in a balanced table all of it lands on γ̂²', () => {
  const w = C.makeWorld({ rho: 0.5, T: 5 }), t = w.truth, m = exactMean(w, (d) => C.pairPools(d, 'anova').raw);
  const c = t.Sigma[0][1]; // the common noise covariance of two cell means
  close(m[0], t.alpha2, 1e-9, 'α̂² unbiased'); close(m[1], t.beta2, 1e-9, 'β̂² unbiased');
  close(m[2], t.gamma2 - c, 1e-9, 'γ̂² biased by −σ²ρ/w*');
  const m0 = exactMean(C.makeWorld({ rho: 0, T: 5 }), (d) => C.pairPools(d, 'anova').raw);
  close(m0[2], t.gamma2, 1e-9, 'unbiased when ρ = 0');
});

test('Fit: K̂ ≻ 0 in every draw; both truncations are projections, never further from the truth in their metric (ConeProjection.hsq_proj_le)', () => {
  const w = C.makeWorld({ nr: 3, nc: 2, alpha: 0.02, beta: 0.03, gamma: 0.02, rho: 0.5 }), r = E.rng(7), t = w.truth;
  const th = [t.alpha2, t.beta2, t.gamma2], M = [[0, 1, 1], [1, 0, 1], [1, 1, 1]];
  const eu = (x) => sum(x.map((v, k) => (v - th[k]) ** 2)), mm = (x) => sum(M.map((row) => dot(row, x.map((v, k) => v - th[k])) ** 2));
  let neg = 0;
  for (let s = 0; s < 200; s++) {
    const { data } = C.draw(w, r);
    const fc = C.fit(data, { trunc: 'clip' }), fn = C.fit(data, { trunc: 'nnls' });
    assert.ok(E.cholesky(fc.K) && E.cholesky(fn.K), 'K̂ ≻ 0');
    assert.ok(fc.theta.every((x) => x >= 0) && fn.theta.every((x) => x >= 0));
    assert.ok(eu(fc.theta) <= eu(fc.raw) + 1e-18, 'clip: Euclidean');
    assert.ok(mm(fn.theta) <= mm(fn.raw) + 1e-18, 'least squares: in the pool metric');
    if (fc.raw.some((x) => x < 0)) neg++;
  }
  assert.ok(neg > 20, `truncation was exercised (${neg} draws)`);
});

test('Fit: the weights sum to 1 for every cell, observed or not; rates and the missing cell', () => {
  const w = C.makeWorld({ missing: true, spread: 1 }), { data } = C.draw(w, E.rng(4)), f = C.fit(data);
  f.cells.forEach((c) => { close(sum(c.full), 1, 1e-12, 'full'); close(sum(c.blend), 1, 1e-12, 'blend'); });
  assert.equal(f.rates.length, w.J);
  assert.equal(f.cells[0].observed, false);
  const th = C.thesisFit(data);
  close(th.rates[0], th.mu, 1e-14, 'thesis fit: the cell without data gets μ̂');
});

test('Every step marked proved names a proved Lean declaration; the others say why', () => {
  const proved = new Set(execFileSync('python3', [path.join(__dirname, '..', 'scripts', 'progress.py'), '--proved'], { encoding: 'utf8' }).split(/\s+/).filter(Boolean));
  const { data } = C.draw(C.makeWorld({ missing: true }), E.rng(1));
  for (const v of C.VARIANTS) for (const s of C.fit(data, v).steps) {
    if (s.badge === 'proved') assert.ok(proved.has('Credibility.' + s.lean), `${v.id}/${s.name}: ${s.lean}`);
    else assert.ok(s.note, `${v.id}/${s.name}: no note`);
  }
});
