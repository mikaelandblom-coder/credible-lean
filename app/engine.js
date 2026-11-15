/*
 * Credibility app engine (studies/PLAN.md, steps 1–3, and the premium step of G6).
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
    noiseSpread: 0,  // region-specific σⱼ = σ·4^(s((j mod 4)/3 − ½)): 0 equal, 1 = ×0.5–2 (studies' spread worlds)
  };

  /** Factor of region j's noise: σⱼ = σ·noiseFactor(j, s); cycles over 4 regions, so not tied to volume. */
  const noiseFactor = (j, s) => Math.pow(4, s * ((j % 4) / 3 - 0.5));

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
    // σⱼ²: region-specific noise; σ² stays the base (σⱼ = σ when noiseSpread = 0).
    const sigmaj2 = Array.from({ length: J }, (_, j) => (p.sigma * noiseFactor(j, p.noiseSpread)) ** 2);
    const truth = { mu: 1, tau2: p.tau * p.tau, sigma2: p.sigma * p.sigma, sigmaj2, rho };
    return { params: p, J, T, w, truth };
  }

  /** The level covariance K of the cohort means (thesis eq. (21), σⱼₜ² = σⱼ²/wⱼₜ). */
  function trueK(world) {
    const { J, T, w, truth } = world;
    const wt = w.map(sum), K = [];
    for (let i = 0; i < J; i++) {
      K.push([]);
      for (let j = 0; j < J; j++) {
        let r = 0;
        for (let t = 0; t < T; t++) r += Math.sqrt(w[i][t] * w[j][t]);
        K[i].push(Math.sqrt(truth.sigmaj2[i] * truth.sigmaj2[j]) * truth.rho[i][j] * r / (wt[i] * wt[j]) + (i === j ? truth.tau2 : 0));
      }
    }
    return K;
  }

  /**
   * One data set from the world: the levels μⱼ (truth) and the table { w, X }.
   * Xⱼₜ = μⱼ + σⱼ/√wⱼₜ · εⱼₜ with εⱼₜ = √ρ·ηₜ + √(1-ρ)·ξⱼₜ, so corr(εᵢₜ, εⱼₜ) = ρ; all draws skewed.
   */
  function draw(world, r) {
    const { J, T, w, truth, params } = world;
    const rho = params.rho, a = Math.sqrt(Math.max(rho, 0)), b = Math.sqrt(1 - Math.max(rho, 0));
    const tau = Math.sqrt(truth.tau2), sig = truth.sigmaj2.map(Math.sqrt);
    const levels = [], X = [];
    for (let j = 0; j < J; j++) levels.push(truth.mu + tau * r.skewed(params.levelShape));
    const eta = [];
    for (let t = 0; t < T; t++) eta.push(r.skewed(params.noiseShape));
    for (let j = 0; j < J; j++) {
      const row = [];
      for (let t = 0; t < T; t++) {
        const eps = a * eta[t] + b * r.skewed(params.noiseShape);
        row.push(levels[j] + sig[j] / Math.sqrt(w[j][t]) * eps);
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

  // ---------------------------------------------------------------- next year (G6)

  /** Next year's volumes: this year's mean wⱼ* / T, times a factor (default 1). */
  function nextVolumes(data, factor) {
    const T = data.w[0].length, f = factor == null ? 1 : factor;
    return data.w.map((row) => f * sum(row) / T);
  }

  /**
   * Next year's outcome from the world: Yⱼ = μⱼ + σⱼ/√wⱼ,next · εⱼ, the same levels μⱼ and
   * fresh noise of one new year (corr ρ between regions, as in draw), so uncorrelated with
   * this data set and with the levels (the assumptions of Core.Estimates.mse_forecast).
   */
  function drawNext(world, levels, wNext, r) {
    const { params, truth } = world, a = Math.sqrt(Math.max(params.rho, 0)), b = Math.sqrt(1 - Math.max(params.rho, 0));
    const eta = r.skewed(params.noiseShape);
    return levels.map((mu, j) => mu + Math.sqrt(truth.sigmaj2[j] / wNext[j]) * (a * eta + b * r.skewed(params.noiseShape)));
  }

  /**
   * The premium step (PLAN G6, Core.Estimates.mse_forecast): premium = μ̂ⱼᵇ (z unchanged),
   * forecast error = level MSE + σ̂ⱼ²/wⱼ,next. The level MSE is the plug-in g₁₂ⱼ on the fit's
   * K̂, τ̂² (or `levelMSE`, e.g. the jackknife MSEP); σ̂ⱼ² = (K̂ⱼⱼ − τ̂²)·wⱼ*. Null for a fit
   * without parameters (own, pool).
   */
  function premium(fit, data, wNext, levelMSE) {
    if (!fit.K) return null;
    const wt = data.w.map(sum), J = wt.length, tau2 = fit.tau2;
    const { b, s2 } = bestBlendWeights(fit.K, tau2);
    const level = levelMSE || Array.from({ length: J }, (_, j) => blendMSE(fit.K, tau2, b, s2, j, fit.z[j]));
    const noise = wt.map((x, j) => (fit.K[j][j] - tau2) * x / wNext[j]);
    const mse = level.map((g, j) => g + noise[j]);
    const step = {
      name: 'premium', formula: 'premium = μ̂ⱼᵇ;  forecast error² = MSEⱼ + σ̂ⱼ²/wⱼ,next', values: mse.map(Math.sqrt),
      badge: 'proved', lean: 'Credibility.Core.Estimates.mse_forecast',
      note: `values: forecast error (root) for next year; the same z is optimal for next year (bestZ_forecast_optimal); MSEⱼ ${levelMSE ? 'by the jackknife' : 'plug-in, on K̂ and τ̂²'}`,
    };
    return { premium: fit.rates.slice(), level, noise, mse, typical: mse.map(Math.sqrt), step };
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
      means: m, z, b, mu: res.mu, rates: res.rates, warnings, flags: { tauNeg: tauRaw <= 0 },
      sigma2, tau2, K: wt.map((x, i) => wt.map((_, j) => (i === j ? sigma2 / x + tau2 : 0))),
      steps: [
        { name: 'cohort means', formula: 'μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', values: m, badge: 'proved', lean: 'Credibility.bs_a' },
        { name: 'σ̂²', formula: 'σ̂² = (1/J) Σⱼ Σₜ wⱼₜ (Xⱼₜ − μ̂ⱼ)² / (T−1)', values: [sigma2], badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
        { name: 'τ̂²', formula: 'τ̂² = (Σⱼ wⱼ*(μ̂ⱼ − μ̄)² − (J−1)σ̂²) / (w** − Σⱼ wⱼ*²/w**)', values: [tauRaw], badge: 'proved', lean: 'Credibility.Model.tauHatBS_unbiased', note: 'classical eq. (13): unbiased when the regions are uncorrelated with a common σ (G0)' },
        { name: 'z', formula: 'zⱼ = wⱼ* / (wⱼ* + σ̂²/τ̂²)', values: z, badge: 'proved', lean: 'Credibility.bs_z' },
        { name: 'b', formula: 'bⱼ = zⱼ / z*', values: b, badge: 'proved', lean: 'Credibility.bs_b' },
        { name: 'rates', formula: 'μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 − zⱼ) μ̂', values: res.rates, badge: 'proved', lean: 'Credibility.bs_balance' },
      ],
    };
  }

  /** Each region on its own: z = 1. */
  function fitOwn(data) {
    const { m } = cohortMeans(data);
    return { means: m, z: m.map(() => 1), b: null, mu: null, rates: m.slice(), warnings: [], flags: {}, steps: [] };
  }

  /** One tariff for all: z = 0, the volume-weighted portfolio mean. */
  function fitPool(data) {
    const { wt, m } = cohortMeans(data);
    const wall = sum(wt), mu = sum(m.map((x, j) => wt[j] * x)) / wall;
    return { means: m, z: m.map(() => 0), b: wt.map((x) => x / wall), mu, rates: m.map(() => mu), warnings: [], flags: {}, steps: [] };
  }

  /**
   * The thesis estimators from data, eq. (39) (the display summarising §2.8):
   * Σ̂ᵢⱼ = σ²ᵢⱼρᵢⱼ^ = Σₜ √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ) / (Sᵢⱼ + (T−2)wᵢ* wⱼ* / Sᵢⱼ),
   * Sᵢⱼ = Σₜ √(wᵢₜwⱼₜ). On the diagonal this is σ̂ⱼ²/wⱼ* (eq. (41)).
   */
  function sigmaHat(data) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data);
    const S = [], Sig = [];
    for (let i = 0; i < J; i++) {
      S.push([]); Sig.push([]);
      for (let j = 0; j < J; j++) {
        let s = 0, q = 0;
        for (let t = 0; t < T; t++) {
          const r = Math.sqrt(data.w[i][t] * data.w[j][t]);
          s += r; q += r * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]);
        }
        S[i].push(s); Sig[i].push(q / (s + (T - 2) * wt[i] * wt[j] / s));
      }
    }
    return { wt, m, S, Sig };
  }

  /**
   * ĉⱼ = Σᵢ (δᵢⱼ − wᵢ* / w**) Σ̂ᵢⱼ and τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ) / (w** − Σᵢ wᵢ*² / w**),
   * eq. (39), for any table Σ̂ (the full one, or the common-covariance one).
   */
  function thesisTau(m, wt, Sig) {
    const J = m.length, wall = sum(wt), mw = sum(m.map((x, i) => wt[i] * x)) / wall;
    const c = [];
    for (let j = 0; j < J; j++) {
      let s = 0;
      for (let i = 0; i < J; i++) s += ((i === j ? 1 : 0) - wt[i] / wall) * Sig[i][j];
      c.push(s);
    }
    const num = sum(m.map((x, j) => wt[j] * ((x - mw) * (x - mw) - c[j])));
    return { c, tau2: num / (wall - sum(wt.map((x) => x * x)) / wall) };
  }

  /** A with its off-diagonal entries multiplied by θ (Lean: shrinkOffDiag). */
  function shrinkOffDiag(theta, A) {
    return A.map((row, i) => row.map((x, j) => (i === j ? x : theta * x)));
  }
  const addDiag = (A, d) => A.map((row, i) => row.map((x, j) => (i === j ? x + d : x)));
  /** Positive semidefinite, numerically: Cholesky of A + ε·tr(A)/n·I. */
  function isPSD(A) {
    const n = A.length, tr = A.reduce((s, row, i) => s + row[i], 0);
    return cholesky(addDiag(A, 1e-12 * Math.abs(tr) / n + 1e-300)) !== null;
  }

  /** The damping factors tried, largest first: θ = 0.95 by default (handbook), lowered if needed. */
  const THETAS = [0.95, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1, 0];

  /**
   * The thesis model with correlation, fitted from data (eqs. (37)–(41), §2.8).
   * opts.common: replace the off-diagonal Σ̂ᵢⱼ by their average c̄ (one common
   *   covariance; then zⱼ = τ²/(τ² + vⱼ − c), Core.bestZ_of_equalCov).
   * opts.theta: force a damping factor (tests); otherwise the largest of THETAS
   *   with K̂ ≻ 0.
   */
  function fitCorr(data, opts) {
    const o = opts || {};
    const J = data.X.length;
    const est = sigmaHat(data), { wt, m } = est;
    let Sig = est.Sig, cbar = null;
    if (o.common) {
      let s = 0, n = 0;
      for (let i = 0; i < J; i++) for (let j = 0; j < J; j++) if (i !== j) { s += Sig[i][j]; n++; }
      cbar = s / n;
      Sig = Sig.map((row, i) => row.map((x, j) => (i === j ? x : cbar)));
    }
    const { c, tau2: tauRaw } = thesisTau(m, wt, Sig);
    const tau2 = Math.max(tauRaw, 0);
    const psd = isPSD(Sig);
    let theta = null, K = null;
    for (const th of (o.theta != null ? [o.theta] : THETAS)) {
      const Kt = addDiag(shrinkOffDiag(th, Sig), tau2);
      if (cholesky(Kt)) { theta = th; K = Kt; break; }
    }
    if (!K) throw new Error('K̂ not positive definite even at θ = 0');
    const v = Sig.map((row, j) => row[j]);
    let { b, z, s2 } = bestBlendWeights(K, tau2);
    const cDamped = o.common ? theta * cbar : null;
    if (o.common && tau2 > 0) {   // the proved closed form (equals the GLS route above)
      z = v.map((vj) => tau2 / (tau2 + vj - cDamped));
      const zs = sum(z);
      b = z.map((x) => x / zs);
    }
    const res = blend(m, z, b);
    const offBal = sum(wt.map((x, j) => x * (m[j] - res.rates[j]))) / sum(wt.map((x, j) => x * m[j]));
    const flags = {
      tauNeg: tauRaw <= 0, zOver1: z.some((x) => x > 1), bNeg: b.some((x) => x < 0),
      thetaLow: theta < THETAS[0], offBalance: Math.abs(offBal) > 0.01,
    };
    const warnings = [];
    if (flags.tauNeg) warnings.push('τ̂² ≤ 0, set to 0 (eq. (40)): no credibility, every region gets the portfolio level μ̂');
    if (flags.zOver1) warnings.push(`z > 1 for ${z.filter((x) => x > 1).length} region(s): the rate moves past the region's own mean, away from μ̂ (thesis eq. (34) would clip it)`);
    if (flags.bNeg) warnings.push(`negative portfolio weight b for ${b.filter((x) => x < 0).length} region(s): GLS uses it as a hedge against correlated noise`);
    if (flags.thetaLow) warnings.push(`K̂ was not positive definite at θ = ${THETAS[0]}; damping lowered to θ = ${theta}`);
    if (flags.offBalance) warnings.push(`off-balance: Σ wⱼ*(μ̂ⱼ − μ̂ⱼᵇ) is ${(100 * offBal).toFixed(1)}% of the premium volume`);
    const offs = [];
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) offs.push(Sig[i][j]);
    const steps = [
      { name: 'cohort means', formula: 'μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', values: m, badge: 'proved', lean: 'Credibility.Model.a_special', note: 'aⱼₜ = wⱼₜ/wⱼ* (eq. (29))' },
      { name: 'Σ̂ diagonal', formula: 'σ²ⱼⱼ^ = σ̂ⱼ²/wⱼ*,  σ̂ⱼ² = Σₜ wⱼₜ(Xⱼₜ − μ̂ⱼ)²/(T−1)  (eq. (41))', values: v, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
      { name: 'Σ̂ off-diagonal', formula: 'σ²ᵢⱼρᵢⱼ^ = Σₜ √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ) / (Sᵢⱼ + (T−2)wᵢ*wⱼ*/Sᵢⱼ)  (eq. (39))', values: offs, summary: true, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_unbiased', note: 'unbiased; J(J−1)/2 pairs' },
    ];
    if (o.common) {
      steps.push({ name: 'common covariance', formula: 'ĉ = average of σ²ᵢⱼρᵢⱼ^ over the pairs i ≠ j', values: [cbar], badge: 'not proved yet', gap: 'G1', note: 'unbiased for a common c: not proved yet (G1)' });
    }
    steps.push(
      { name: 'ĉⱼ', formula: 'ĉⱼ = Σᵢ (δᵢⱼ − wᵢ*/w**) Σ̂ᵢⱼ', values: c, badge: o.common ? 'not proved yet' : 'proved', lean: o.common ? null : 'Credibility.Model.cHat_unbiased', gap: o.common ? 'G1' : null, note: o.common ? 'with the common ĉ: unbiased if ĉ is (G1)' : null },
      { name: 'τ̂²', formula: 'τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ) / (w** − Σᵢ wᵢ*²/w**)  (eq. (39))', values: [tauRaw], badge: o.common ? 'not proved yet' : 'proved', lean: o.common ? null : 'Credibility.Model.tauHat_unbiased', gap: o.common ? 'G1' : null, note: tauRaw <= 0 ? 'negative: truncated to 0 (eq. (40))' : null },
      { name: 'damped K̂', formula: `K̂ = Σ̂ with off-diagonal × θ, + τ̂²⁺ I;  θ = ${theta}`, values: [theta], badge: psd && theta < 1 ? 'proved' : 'not proved yet', lean: psd && theta < 1 ? 'Credibility.posDef_shrinkOffDiag' : null, gap: 'G2', note: psd ? `Σ̂ ⪰ 0, so K̂ ≻ 0 for any θ < 1; the choice θ = ${theta} is a heuristic (G2)` : `Σ̂ is not positive semidefinite: K̂ ≻ 0 checked numerically at θ = ${theta}, not by a theorem (G2)` },
    );
    if (o.common && tau2 > 0) {
      steps.push(
        { name: 'z', formula: 'zⱼ = τ̂² / (τ̂² + v̂ⱼ − θĉ)', values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_of_equalCov' },
        { name: 'b', formula: 'bⱼ = zⱼ / z*', values: b, badge: 'proved', lean: 'Credibility.Core.b_eq_of_equalCov' },
      );
    } else {
      steps.push(
        { name: 'b', formula: 'b = K̂⁻¹1 / 1ᵀK̂⁻¹1  (GLS, eq. (25))', values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
        { name: 'z', formula: 'zⱼ = (1 − bⱼ)τ̂² / (K̂ⱼⱼ − s²),  s² = 1/1ᵀK̂⁻¹1  (eq. (26))', values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
      );
    }
    steps.push({ name: 'rates', formula: 'μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 − zⱼ) μ̂,  μ̂ = Σ bⱼ μ̂ⱼ', values: res.rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: `the parameters are plugged in: the formulas are optimal for the true K, τ²; off-balance ${(100 * offBal).toFixed(2)}%` });
    return { means: m, z, b, mu: res.mu, rates: res.rates, warnings, flags, K, theta, tauRaw, tau2, cbar, steps };
  }

  /**
   * Correlated Bühlmann–Straub with credibility-weighted variances
   * (studies/damping-theta.md, findings 15–17 and the Ansatz; studies/variance-credibility.js,
   * mode 'cred'). Every parameter by a moment equation, nothing to tune, no damping:
   *   σ̂ⱼ² = Qⱼⱼ/(T−1), σ̂² = mean of the σ̂ⱼ²,
   *   Wⱼ = estimated Var(σ̂ⱼ²) from the yearly terms, β² = between-region variance of the σⱼ²,
   *   σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂², ζⱼ = β²/(β² + Wⱼ)   (Bühlmann–Straub one level up),
   *   ρ̂ = Σᵢ<ⱼ Qᵢⱼ / Σᵢ<ⱼ σ̃ᵢσ̃ⱼ((T − 2) + Sᵢⱼ²/(wᵢ*wⱼ*)), clipped to [0, 1),
   *   Σ̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) (i ≠ j), σ̃ⱼ²/wⱼ* (i = j); τ̂² by eq. (39) on Σ̂, truncated at 0.
   * K̂ = Σ̂ + τ̂²I ≻ 0 by Model.K_posDef (the ρ-table 1 / ρ̂ is PSD for ρ̂ ∈ [0, 1)).
   */
  function vcEstimate(data) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data);
    const S = [], Q = [];
    for (let i = 0; i < J; i++) {
      S.push([]); Q.push([]);
      for (let j = 0; j < J; j++) {
        let s = 0, q = 0;
        for (let t = 0; t < T; t++) { const c = Math.sqrt(data.w[i][t] * data.w[j][t]); s += c; q += c * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]); }
        S[i].push(s); Q[i].push(q);
      }
    }
    const own = Q.map((row, j) => row[j] / (T - 1)), pooled = sum(own) / J;
    const W = own.map((sj, j) => {
      const u = data.X[j].map((x, t) => data.w[j][t] * (x - m[j]) ** 2 * T / (T - 1));
      return sum(u.map((x) => (x - sj) ** 2)) / (T * (T - 1));
    });
    const betweenRaw = sum(own.map((x) => (x - pooled) ** 2)) / (J - 1) - sum(W) / J;
    const between = Math.max(0, betweenRaw);
    const zeta = W.map((Wj) => (between > 0 ? between / (between + Wj) : 0));
    const s2 = own.map((x, j) => zeta[j] * x + (1 - zeta[j]) * pooled);
    const sd = s2.map(Math.sqrt);
    let qn = 0, qa = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { qn += Q[i][j]; qa += sd[i] * sd[j] * ((T - 2) + S[i][j] ** 2 / (wt[i] * wt[j])); }
    const rhoRaw = qn / qa, rho = Math.min(Math.max(rhoRaw, 0), 1 - 1e-9);
    const Sig = S.map((row, i) => row.map((x, j) => (i === j ? s2[i] / wt[i] : rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
    const tt = thesisTau(m, wt, Sig);
    return { m, wt, S, own, pooled, W, betweenRaw, between, zeta, s2, rhoRaw, rho, Sig, c: tt.c, tauRaw: tt.tau2, t2: Math.max(tt.tau2, 0) };
  }

  /** K̂, the GLS blend and its known-parameter MSE g₁₂ⱼ for parameters p, on the design (wt, S) and means m. */
  function vcBlend(p, wt, S, m) {
    const J = m.length, sd = p.s2.map(Math.sqrt);
    const K = S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / wt[i] + p.t2 : p.rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
    const { b, z: z0, s2 } = bestBlendWeights(K, p.t2);
    const z = p.t2 > 0 ? z0 : z0.map(() => 0);
    const res = blend(m, z, b);
    const g = Array.from({ length: J }, (_, j) => blendMSE(K, p.t2, b, s2, j, z[j]));
    return { K, b, z, s2, mu: res.mu, rates: res.rates, g };
  }

  function fitVC(data) {
    const p = vcEstimate(data), { m, wt, S } = p, J = m.length;
    const { K, b, z, mu, rates } = vcBlend(p, wt, S, m);
    const offBal = sum(wt.map((x, j) => x * (m[j] - rates[j]))) / sum(wt.map((x, j) => x * m[j]));
    const flags = { tauNeg: p.tauRaw <= 0, zOver1: z.some((x) => x > 1), bNeg: b.some((x) => x < 0), offBalance: Math.abs(offBal) > 0.01 };
    // Flags the optimum itself shows (studies/vc-balance.js, damping-theta.md findings 27–29): with ρ̂ > 0
    // the true-K blend has negative b and z near 1 (so ẑ > 1 by noise); with ρ̂ > 0 or unequal σ̃ⱼ it is
    // balanced for the weights bⱼ/(1 − zⱼ), not for the exposures. These go to `notes`, not `warnings`.
    const expected = { zOver1: p.rho > 0, bNeg: p.rho > 0, offBalance: p.rho > 0 || p.between > 0 };
    const why = p.rho > 0 ? 'expected under correlation' : 'expected with region-specific σⱼ';
    const msg = {
      tauNeg: 'τ̂² ≤ 0, set to 0 (eq. (40)): no credibility, every region gets the portfolio level μ̂',
      zOver1: `z > 1 for ${z.filter((x) => x > 1).length} region(s): the rate moves past the region's own mean, away from μ̂` +
        (expected.zOver1 ? '; the best z of a large region is close to 1 here, so the estimate can land above 1 (capping it at 1 changes nothing measurable)' : ''),
      bNeg: `negative portfolio weight b for ${b.filter((x) => x < 0).length} region(s): GLS uses it as a hedge against correlated noise` +
        (expected.bNeg ? '; the best weights for the true K have negative entries too' : ''),
      offBalance: `off-balance: Σ wⱼ*(μ̂ⱼ − μ̂ⱼᵇ) is ${(100 * offBal).toFixed(1)}% of the premium volume` +
        (expected.offBalance ? '; the best blend balances the weights bⱼ/(1 − zⱼ), not the exposures, and forcing exposure balance costs up to about 30% more error' : ''),
    };
    const warnings = [], notes = [];
    for (const k in flags) if (flags[k]) {
      if (expected[k]) notes.push(`${why[0].toUpperCase()}${why.slice(1)}: ${msg[k]}`); else warnings.push(msg[k]);
    }
    const steps = [
      { name: 'cohort means', formula: 'μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', values: m, badge: 'proved', lean: 'Credibility.Model.a_special', note: 'aⱼₜ = wⱼₜ/wⱼ* (eq. (29))' },
      { name: 'σ̂ⱼ²', formula: 'σ̂ⱼ² = Σₜ wⱼₜ(Xⱼₜ − μ̂ⱼ)²/(T−1),  σ̂² = (1/J) Σⱼ σ̂ⱼ²', values: p.own, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self', note: `pooled σ̂² = ${p.pooled.toPrecision(4)}` },
      { name: 'Wⱼ, β²', formula: 'Wⱼ = Σₜ (uⱼₜ − σ̂ⱼ²)²/(T(T−1)), uⱼₜ = wⱼₜ(Xⱼₜ − μ̂ⱼ)²T/(T−1);  β² = Σⱼ(σ̂ⱼ² − σ̂²)²/(J−1) − (1/J)Σⱼ Wⱼ', values: [p.betweenRaw], badge: 'not proved yet', gap: 'G1', note: `β² (between-region variance of the σⱼ²)${p.betweenRaw <= 0 ? ': ≤ 0, set to 0, so every σ̃ⱼ² is the pooled σ̂²' : ''}; unbiased for independent years, not proved yet` },
      { name: 'σ̃ⱼ²', formula: 'σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂²,  ζⱼ = β²/(β² + Wⱼ)', values: p.s2, badge: 'not proved yet', gap: 'G1', note: 'credibility for the variances (the form of bs_z, with estimated fourth moments)' },
      { name: 'ρ̂', formula: 'ρ̂ = Σᵢ<ⱼ Qᵢⱼ / Σᵢ<ⱼ σ̃ᵢσ̃ⱼ((T−2) + Sᵢⱼ²/(wᵢ*wⱼ*)),  Qᵢⱼ = Σₜ √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ)', values: [p.rhoRaw], badge: 'not proved yet', gap: 'G1', note: `one common correlation by a moment equation${p.rhoRaw < 0 ? '; negative, set to 0' : p.rhoRaw >= 1 ? '; ≥ 1, set just below 1' : ''}` },
      { name: 'τ̂²', formula: 'τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ) / (w** − Σᵢ wᵢ*²/w**),  ĉⱼ = Σᵢ (δᵢⱼ − wᵢ*/w**) Σ̂ᵢⱼ  (eq. (39))', values: [p.tauRaw], badge: 'not proved yet', gap: 'G1', note: `on the common-ρ Σ̂: unbiased if Σ̂ is${p.tauRaw <= 0 ? '; negative: truncated to 0 (eq. (40))' : ''}` },
      { name: 'K̂', formula: 'K̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) (i ≠ j),  σ̃ⱼ²/wⱼ* + τ̂² (i = j)', values: [p.rho], badge: 'proved', lean: 'Credibility.Model.K_posDef', note: `K̂ ≻ 0 for any ρ̂ ∈ [0, 1): no damping, no θ; ρ̂ = ${p.rho.toFixed(3)}` },
      { name: 'b', formula: 'b = K̂⁻¹1 / 1ᵀK̂⁻¹1  (GLS, eq. (25))', values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
      { name: 'z', formula: 'zⱼ = (1 − bⱼ)τ̂² / (K̂ⱼⱼ − s²),  s² = 1/1ᵀK̂⁻¹1  (eq. (26))', values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
      { name: 'rates', formula: 'μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 − zⱼ) μ̂,  μ̂ = Σ bⱼ μ̂ⱼ', values: rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: `the parameters are plugged in: the formulas are optimal for the true K, τ²; off-balance ${(100 * offBal).toFixed(2)}%` },
    ];
    return { means: m, z, b, mu, rates, warnings, notes, flags, expected, K, tauRaw: p.tauRaw, tau2: p.t2, rho: p.rho, rhoRaw: p.rhoRaw, sigma2: p.s2, between: p.between, steps };
  }

  /**
   * Jackknife MSEP of the variance-credibility fit (Jiang, Lahiri & Wan 2002, Ann. Stat. 30;
   * studies/msep.js), deleting one year at a time (independent years), region means kept:
   *   MSEPⱼ = g₁₂ⱼ(θ̂) − (T−1)/T Σₜ (g₁₂ⱼ(θ̂₋ₜ) − g₁₂ⱼ(θ̂)) + (T−1)/T Σₜ (rateⱼ(θ̂₋ₜ) − rateⱼ(θ̂))².
   * An average-case error over data sets like this one, not an interval for this data set
   * (damping-theta.md, findings 19 and 26). Data only, no tuning.
   */
  function jackknifeMSEP(data) {
    const T = data.X[0].length, p = vcEstimate(data), { m, wt, S } = p, J = m.length;
    const full = vcBlend(p, wt, S, m);
    const gDel = new Array(J).fill(0), rDel = new Array(J).fill(0);
    for (let t = 0; t < T; t++) {
      const d = { w: data.w.map((r) => r.filter((_, u) => u !== t)), X: data.X.map((r) => r.filter((_, u) => u !== t)) };
      const o = vcBlend(vcEstimate(d), wt, S, m);
      for (let j = 0; j < J; j++) { gDel[j] += o.g[j] - full.g[j]; rDel[j] += (o.rates[j] - full.rates[j]) ** 2; }
    }
    const c = (T - 1) / T;
    const msep = full.g.map((g, j) => Math.max(g - c * gDel[j] + c * rDel[j], 0));
    return { rates: full.rates, naive: full.g, msep, g3: rDel.map((x) => c * x), typical: msep.map(Math.sqrt) };
  }

  /**
   * The registry the page is drawn from (PLAN.md §6). Every fit takes the data
   * table and nothing else. `ready: false` entries are listed but disabled.
   */
  const MODELS = {
    bs: { name: 'Bühlmann–Straub', short: 'BS', fit: fitBS, ready: true },
    vc: { name: 'Correlated BS, credibility-weighted variances (recommended)', short: 'corrBS', fit: fitVC, ready: true, msep: jackknifeMSEP },
    corr: { name: 'Thesis model with correlation (full K̂, damped)', short: 'corr', fit: (data) => fitCorr(data), ready: true },
    corrC: { name: 'One common covariance — not recommended (unequal volumes)', short: 'common', fit: (data) => fitCorr(data, { common: true }), ready: true, notRecommended: 'finding 4: with unequal volumes one common covariance exceeds the large regions’ noise variance and z explodes' },
    own: { name: 'Own mean only (z = 1)', short: 'own', fit: fitOwn, ready: true },
    pool: { name: 'One tariff for all (z = 0)', short: 'pool', fit: fitPool, ready: true },
  };

  /**
   * World and fit features (PLAN.md §2, §6). `world` / `fit` say whether that
   * side is built yet; the page greys out the rest.
   */
  const FEATURES = [
    { id: 'rho', name: 'Correlation between regions within a year', world: true, fit: true },
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

  /** The floor's true forecast MSE (Core.Estimates.mse_forecast): level MSE + σⱼ²/wⱼ,next. Reads the truth. */
  function floorForecast(world, wNext) {
    const fl = floorBlend(world), { tau2, sigmaj2 } = world.truth;
    const level = fl.z.map((z, j) => blendMSE(fl.K, tau2, fl.b, fl.s2, j, z));
    return { level, mse: level.map((g, j) => g + sigmaj2[j] / wNext[j]) };
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
   * `flags[k]`: share of draws with flag k; `expected[k]`: share where it was raised and expected
   * (the fit's `notes`, e.g. negative b under correlation), so not a warning.
   * `fmse`, `fse`: the same for the premium against the world's next-year outcome Yⱼ (G6), with
   * next year's volumes wⱼ* / T × `nextFactor` (default 1); `floor.ftheory`: the floor's true
   * forecast MSE, weighted alike. Next year is drawn from its own stream, so the rest is
   * unchanged draw for draw.
   */
  function simulate(world, ids, n, seed, nextFactor) {
    const r = rng(seed), rn = rng((seed ^ 0x5bd1e995) >>> 0), fl = floorBlend(world);
    const wt = world.w.map(sum), wall = sum(wt);
    const wNext = wt.map((x) => (nextFactor == null ? 1 : nextFactor) * x / world.T);
    const ftheory = sum(floorForecast(world, wNext).mse.map((m, j) => wt[j] * m)) / wall;
    const acc = {};
    for (const id of ids.concat(['floor'])) acc[id] = { s: 0, ss: 0, f: 0, ff: 0, warn: 0, flags: {}, expected: {} };
    const fe = (rates, Y) => sum(rates.map((x, j) => wt[j] * (x - Y[j]) * (x - Y[j]))) / wall;
    for (let k = 0; k < n; k++) {
      const { levels, data } = draw(world, r), Y = drawNext(world, levels, wNext, rn);
      for (const id of ids) {
        const f = MODELS[id].fit(data), e = weightedSE(data, f.rates, levels), g = fe(f.rates, Y);
        acc[id].s += e; acc[id].ss += e * e; acc[id].f += g; acc[id].ff += g * g; if (f.warnings.length) acc[id].warn++;
        for (const k in f.flags) if (f.flags[k]) {
          acc[id].flags[k] = (acc[id].flags[k] || 0) + 1;
          if (f.expected && f.expected[k]) acc[id].expected[k] = (acc[id].expected[k] || 0) + 1;
        }
      }
      const fr = fl.apply(data).rates, e = weightedSE(data, fr, levels), g = fe(fr, Y);
      acc.floor.s += e; acc.floor.ss += e * e; acc.floor.f += g; acc.floor.ff += g * g;
    }
    const out = {};
    for (const id in acc) {
      const mean = acc[id].s / n, v = Math.max(acc[id].ss / n - mean * mean, 0);
      const fm = acc[id].f / n, fv = Math.max(acc[id].ff / n - fm * fm, 0);
      const flags = {}, expected = {};
      for (const k in acc[id].flags) flags[k] = acc[id].flags[k] / n;
      for (const k in acc[id].expected) expected[k] = acc[id].expected[k] / n;
      out[id] = { mse: mean, se: Math.sqrt(v / n), fmse: fm, fse: Math.sqrt(fv / n), warnShare: acc[id].warn / n, flags, expected };
    }
    out.floor.ftheory = ftheory;
    return out;
  }

  return {
    DEFAULTS, MODELS, FEATURES,
    rng, solve, cholesky, makeWorld, noiseFactor, trueK, draw,
    cohortMeans, blend, bestBlendWeights, blendMSE,
    fitBS, fitOwn, fitPool, fitCorr, fitVC, vcEstimate, jackknifeMSEP, sigmaHat, thesisTau, shrinkOffDiag, isPSD, THETAS,
    floorBlend, weightedSE, simulate,
    nextVolumes, drawNext, premium, floorForecast,
  };
});
