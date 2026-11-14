/*
 * Credibility app engine (studies/PLAN.md, steps 1–2).
 *
 * One file, run by the page (app/index.html) and by the tests under Node
 * (app/engine.test.js). No dependencies.
 *
 * Three parts, kept apart on purpose (PLAN.md §1, principle 1):
 *   world  — makeWorld(params) and draw(world, rng): the truth and one data set.
 *   fits   — MODELS[id].fit(data): get the data table { w, X } and nothing else.
 *   floor  — floorBlend(world): the best blend if the parameters were known.
 *            A benchmark, never a fit; it alone reads world.truth.
 *
 * Notation follows the thesis: cohorts j (regions), periods t (years),
 * volumes w[j][t] (vehicle-years), key ratios X[j][t] (claim cost per
 * vehicle-year relative to the tariff), levels μⱼ, portfolio level μ = 1.
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Engine = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // ---------------------------------------------------------------- random

  /** Seeded generator (mulberry32): the same seed gives the same draws. */
  function rng(seed) {
    let a = seed >>> 0;
    const u = function () {
      a = (a + 0x6d2b79f5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    let spare = null;
    u.normal = function () {
      if (spare !== null) { const s = spare; spare = null; return s; }
      let x, y, r;
      do { x = 2 * u() - 1; y = 2 * u() - 1; r = x * x + y * y; } while (r >= 1 || r === 0);
      const f = Math.sqrt(-2 * Math.log(r) / r);
      spare = y * f;
      return x * f;
    };
    u.gamma = function (k) { // Marsaglia–Tsang, k ≥ 1
      const d = k - 1 / 3, c = 1 / Math.sqrt(9 * d);
      for (;;) {
        let x, v;
        do { x = u.normal(); v = 1 + c * x; } while (v <= 0);
        v = v * v * v;
        const U = u();
        if (U < 1 - 0.0331 * x * x * x * x) return d * v;
        if (Math.log(U) < 0.5 * x * x + d * (1 - v + Math.log(v))) return d * v;
      }
    };
    /** Mean 0, variance 1, skewness 2/√k: the model only fixes two moments. */
    u.skewed = function (k) { return (u.gamma(k) - k) / Math.sqrt(k); };
    return u;
  }

  // ---------------------------------------------------------------- linear algebra (small, dense)

  /** Solve A x = b by Gaussian elimination with partial pivoting. */
  function solve(A, b) {
    const n = b.length;
    const M = A.map((row, i) => row.slice().concat([b[i]]));
    for (let c = 0; c < n; c++) {
      let p = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
      if (Math.abs(M[p][c]) < 1e-300) throw new Error('singular matrix');
      [M[c], M[p]] = [M[p], M[c]];
      for (let r = c + 1; r < n; r++) {
        const f = M[r][c] / M[c][c];
        if (f !== 0) for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
      }
    }
    const x = new Array(n);
    for (let r = n - 1; r >= 0; r--) {
      let s = M[r][n];
      for (let k = r + 1; k < n; k++) s -= M[r][k] * x[k];
      x[r] = s / M[r][r];
    }
    return x;
  }

  /** Cholesky factor (lower); null if A is not positive definite. */
  function cholesky(A) {
    const n = A.length, L = A.map(() => new Array(n).fill(0));
    for (let i = 0; i < n; i++) {
      for (let j = 0; j <= i; j++) {
        let s = A[i][j];
        for (let k = 0; k < j; k++) s -= L[i][k] * L[j][k];
        if (i === j) { if (!(s > 0)) return null; L[i][i] = Math.sqrt(s); }
        else L[i][j] = s / L[j][j];
      }
    }
    return L;
  }

  const sum = (a) => a.reduce((s, x) => s + x, 0);

  // ---------------------------------------------------------------- the world

  /**
   * World parameters (the truth). Defaults are the motor-by-region story:
   * 8 regions, 10 years, levels around the tariff with spread τ, noise σ²/w.
   */
  const DEFAULTS = {
    J: 8,            // regions (cohorts)
    T: 10,           // years
    tau: 0.10,       // spread of the region levels μⱼ around μ = 1
    sigma: 6.0,      // noise of one vehicle-year: Var(Xⱼₜ | μⱼ) = σ²/wⱼₜ
    rho: 0,          // correlation between regions within a year (common winters)
    volume: 500,     // vehicle-years per region and year, middle region
    spread: 1.0,     // how unequal the volumes are (log scale)
    growth: 0.03,    // yearly growth of every region's volume
    levelShape: 4,   // gamma shape of the level draws (skewness 2/√k)
    noiseShape: 2,   // gamma shape of the noise draws
  };

  /** Inverse normal CDF (Acklam), for evenly spread volumes. */
  function qnorm(p) {
    const a = [-39.69683028665376, 220.9460984245205, -275.9285104469687, 138.357751867269, -30.66479806614716, 2.506628277459239];
    const b = [-54.47609879822406, 161.5858368580409, -155.6989798598866, 66.80131188771972, -13.28068155288572];
    const c = [-0.007784894002430293, -0.3223964580411365, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
    const d = [0.007784695709041462, 0.3224671290700398, 2.445134137142996, 3.754408661907416];
    const q = p < 0.5 ? p : 1 - p;
    let x;
    if (q < 0.02425) {
      const r = Math.sqrt(-2 * Math.log(q));
      x = (((((c[0] * r + c[1]) * r + c[2]) * r + c[3]) * r + c[4]) * r + c[5]) / ((((d[0] * r + d[1]) * r + d[2]) * r + d[3]) * r + 1);
    } else {
      const r = q - 0.5, s = r * r;
      x = (((((a[0] * s + a[1]) * s + a[2]) * s + a[3]) * s + a[4]) * s + a[5]) * r / (((((b[0] * s + b[1]) * s + b[2]) * s + b[3]) * s + b[4]) * s + 1);
      return p < 0.5 ? x : -x;
    }
    return p < 0.5 ? -x : x;
  }

  /**
   * Build a world: the fixed volumes and the true second moments. Volumes are
   * deterministic (known to the insurer); levels and noise are drawn per data set.
   */
  function makeWorld(params) {
    const p = Object.assign({}, DEFAULTS, params || {});
    const { J, T } = p;
    const w = [];
    for (let j = 0; j < J; j++) {
      const size = p.volume * Math.exp(p.spread * qnorm((j + 0.5) / J));
      const row = [];
      for (let t = 0; t < T; t++) row.push(size * Math.pow(1 + p.growth, t - (T - 1) / 2));
      w.push(row);
    }
    // ρᵢⱼ: one common coefficient for now (a country structure comes with group levels).
    const rho = [];
    for (let i = 0; i < J; i++) { rho.push([]); for (let j = 0; j < J; j++) rho[i].push(i === j ? 1 : p.rho); }
    const truth = { mu: 1, tau2: p.tau * p.tau, sigma2: p.sigma * p.sigma, rho };
    return { params: p, J, T, w, truth };
  }

  /** The level covariance K of the cohort means (thesis eq. (21), σⱼₜ² = σ²/wⱼₜ). */
  function trueK(world) {
    const { J, T, w, truth } = world;
    const wt = w.map(sum), K = [];
    for (let i = 0; i < J; i++) {
      K.push([]);
      for (let j = 0; j < J; j++) {
        let r = 0;
        for (let t = 0; t < T; t++) r += Math.sqrt(w[i][t] * w[j][t]);
        K[i].push(truth.sigma2 * truth.rho[i][j] * r / (wt[i] * wt[j]) + (i === j ? truth.tau2 : 0));
      }
    }
    return K;
  }

  /**
   * One data set from the world: the levels μⱼ (truth) and the table { w, X }.
   * Noise εⱼₜ = √ρ·ηₜ + √(1-ρ)·ξⱼₜ, so corr(εᵢₜ, εⱼₜ) = ρ; all draws skewed.
   */
  function draw(world, r) {
    const { J, T, w, truth, params } = world;
    const rho = params.rho, a = Math.sqrt(Math.max(rho, 0)), b = Math.sqrt(1 - Math.max(rho, 0));
    const tau = Math.sqrt(truth.tau2), sig = Math.sqrt(truth.sigma2);
    const levels = [], X = [];
    for (let j = 0; j < J; j++) levels.push(truth.mu + tau * r.skewed(params.levelShape));
    const eta = [];
    for (let t = 0; t < T; t++) eta.push(r.skewed(params.noiseShape));
    for (let j = 0; j < J; j++) {
      const row = [];
      for (let t = 0; t < T; t++) {
        const eps = a * eta[t] + b * r.skewed(params.noiseShape);
        row.push(levels[j] + sig / Math.sqrt(w[j][t]) * eps);
      }
      X.push(row);
    }
    const data = Object.freeze({ w: w.map((row) => Object.freeze(row.slice())), X });
    return { levels, data };
  }

  // ---------------------------------------------------------------- shared building blocks

  /** Cohort means μ̂ⱼ = Σₜ wⱼₜXⱼₜ / wⱼ* (eq. (29): a = w/w*). */
  function cohortMeans(data) {
    const wt = data.w.map(sum);
    const m = data.X.map((row, j) => sum(row.map((x, t) => data.w[j][t] * x)) / wt[j]);
    return { wt, m };
  }

  /** The blend μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 - zⱼ) μ̂ with μ̂ = Σ bⱼ μ̂ⱼ. */
  function blend(m, z, b) {
    const mu = sum(m.map((x, j) => b[j] * x));
    return { mu, rates: m.map((x, j) => z[j] * x + (1 - z[j]) * mu) };
  }

  /**
   * The Core recipe for a known K and τ² (eq. (26)): GLS weights b = K⁻¹1 / 1ᵀK⁻¹1,
   * s² = 1/1ᵀK⁻¹1, zⱼ = (1 - bⱼ)τ² / (Kⱼⱼ - s²).
   */
  function bestBlendWeights(K, tau2) {
    const J = K.length, u = solve(K, new Array(J).fill(1)), tot = sum(u);
    const b = u.map((x) => x / tot), s2 = 1 / tot;
    const z = b.map((bj, j) => (1 - bj) * tau2 / (K[j][j] - s2));
    return { b, z, s2 };
  }

  /**
   * True MSE of the blend of cohort j for a given z and GLS weights b, when the
   * level covariance is τ²I (thesis model): E[(zμ̂ⱼ + (1-z)μ̂ - μⱼ)²].
   */
  function blendMSE(K, tau2, b, s2, j, z) {
    const A = K[j][j] - tau2;                 // Var(μ̂ⱼ - μⱼ)
    const B = s2 - 2 * b[j] * tau2 + tau2;    // Var(μ̂ - μⱼ)
    const C = s2 - b[j] * tau2;               // cov(μ̂ⱼ - μⱼ, μ̂ - μⱼ), using Kb = s²1
    return z * z * A + (1 - z) * (1 - z) * B + 2 * z * (1 - z) * C;
  }

  // ---------------------------------------------------------------- fitted models (data only)

  /**
   * Bühlmann–Straub from data (thesis eq. (13), with the 1/J fix of
   * FINDINGS.md: σ̂² averages the J cohort estimates).
   */
  function fitBS(data) {
    const J = data.X.length, T = data.X[0].length;
    const { wt, m } = cohortMeans(data);
    const sj2 = m.map((mj, j) => sum(data.X[j].map((x, t) => data.w[j][t] * (x - mj) * (x - mj))) / (T - 1));
    const sigma2 = sum(sj2) / J;
    const wall = sum(wt), mw = sum(m.map((x, j) => wt[j] * x)) / wall;
    const tauRaw = (sum(m.map((x, j) => wt[j] * (x - mw) * (x - mw))) - (J - 1) * sigma2) /
      (wall - sum(wt.map((x) => x * x)) / wall);
    const warnings = [];
    let tau2 = tauRaw;
    if (tauRaw <= 0) { tau2 = 0; warnings.push('τ̂² ≤ 0, set to 0 (Bühlmann’s truncation): no credibility, every region gets the portfolio level'); }
    const z = wt.map((x) => tau2 > 0 ? x / (x + sigma2 / tau2) : 0);
    const zs = sum(z);
    const b = zs > 0 ? z.map((x) => x / zs) : wt.map((x) => x / wall);
    const res = blend(m, z, b);
    return {
      means: m, z, b, mu: res.mu, rates: res.rates, warnings,
      steps: [
        { name: 'cohort means', formula: 'μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', values: m, badge: 'proved', lean: 'Credibility.bs_a' },
        { name: 'σ̂²', formula: 'σ̂² = (1/J) Σⱼ Σₜ wⱼₜ (Xⱼₜ − μ̂ⱼ)² / (T−1)', values: [sigma2], badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
        { name: 'τ̂²', formula: 'τ̂² = (Σⱼ wⱼ*(μ̂ⱼ − μ̄)² − (J−1)σ̂²) / (w** − Σⱼ wⱼ*²/w**)', values: [tauRaw], badge: 'not proved yet', note: 'classical eq. (13); the Lean τ̂² is the thesis estimator (39)–(41)' },
        { name: 'z', formula: 'zⱼ = wⱼ* / (wⱼ* + σ̂²/τ̂²)', values: z, badge: 'proved', lean: 'Credibility.bs_z' },
        { name: 'b', formula: 'bⱼ = zⱼ / z*', values: b, badge: 'proved', lean: 'Credibility.bs_b' },
        { name: 'rates', formula: 'μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 − zⱼ) μ̂', values: res.rates, badge: 'proved', lean: 'Credibility.bs_balance' },
      ],
    };
  }

  /** Each region on its own: z = 1. */
  function fitOwn(data) {
    const { m } = cohortMeans(data);
    return { means: m, z: m.map(() => 1), b: null, mu: null, rates: m.slice(), warnings: [], steps: [] };
  }

  /** One tariff for all: z = 0, the volume-weighted portfolio mean. */
  function fitPool(data) {
    const { wt, m } = cohortMeans(data);
    const wall = sum(wt), mu = sum(m.map((x, j) => wt[j] * x)) / wall;
    return { means: m, z: m.map(() => 0), b: wt.map((x) => x / wall), mu, rates: m.map(() => mu), warnings: [], steps: [] };
  }

  /**
   * The registry the page is drawn from (PLAN.md §6). Every fit takes the data
   * table and nothing else. `ready: false` entries are listed but disabled.
   */
  const MODELS = {
    bs: { name: 'Bühlmann–Straub', short: 'BS', fit: fitBS, ready: true },
    own: { name: 'Own mean only (z = 1)', short: 'own', fit: fitOwn, ready: true },
    pool: { name: 'One tariff for all (z = 0)', short: 'pool', fit: fitPool, ready: true },
    corr: { name: 'Thesis model with correlation', short: 'corr', fit: null, ready: false, note: 'step 3' },
  };

  /**
   * World and fit features (PLAN.md §2, §6). `world` / `fit` say whether that
   * side is built yet; the page greys out the rest.
   */
  const FEATURES = [
    { id: 'rho', name: 'Correlation between regions within a year', world: true, fit: false, fitNote: 'step 3' },
    { id: 'unequal', name: 'Unequal lengths (regions entered recently)', world: false, fit: false, fitNote: 'step 4' },
    { id: 'groups', name: 'Group levels (regions of one country)', world: false, fit: false, fitNote: 'step 4' },
  ];

  // ---------------------------------------------------------------- the floor (known parameters)

  /** The best blend if K and τ² were known: eq. (26) on the true K. Reads the truth. */
  function floorBlend(world) {
    const K = trueK(world);
    const { b, z, s2 } = bestBlendWeights(K, world.truth.tau2);
    return { K, b, z, s2, apply: (data) => blend(cohortMeans(data).m, z, b) };
  }

  // ---------------------------------------------------------------- scoring

  /** Exposure-weighted squared error of the rates: Σⱼ wⱼ*(rateⱼ − μⱼ)² / w**. */
  function weightedSE(data, rates, levels) {
    const wt = data.w.map(sum), wall = sum(wt);
    return sum(rates.map((r, j) => wt[j] * (r - levels[j]) * (r - levels[j]))) / wall;
  }

  /**
   * Many draws of one world: mean and standard error of the weighted squared
   * error for each model id, and for the floor. Returns root-scale numbers too.
   */
  function simulate(world, ids, n, seed) {
    const r = rng(seed), fl = floorBlend(world);
    const acc = {};
    for (const id of ids.concat(['floor'])) acc[id] = { s: 0, ss: 0, warn: 0 };
    for (let k = 0; k < n; k++) {
      const { levels, data } = draw(world, r);
      for (const id of ids) {
        const f = MODELS[id].fit(data), e = weightedSE(data, f.rates, levels);
        acc[id].s += e; acc[id].ss += e * e; if (f.warnings.length) acc[id].warn++;
      }
      const e = weightedSE(data, fl.apply(data).rates, levels);
      acc.floor.s += e; acc.floor.ss += e * e;
    }
    const out = {};
    for (const id in acc) {
      const mean = acc[id].s / n, v = Math.max(acc[id].ss / n - mean * mean, 0);
      out[id] = { mse: mean, se: Math.sqrt(v / n), warnShare: acc[id].warn / n };
    }
    return out;
  }

  return {
    DEFAULTS, MODELS, FEATURES,
    rng, solve, cholesky, makeWorld, trueK, draw,
    cohortMeans, blend, bestBlendWeights, blendMSE,
    fitBS, fitOwn, fitPool, floorBlend, weightedSE, simulate,
  };
});
