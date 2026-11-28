/*
 * Credibility app engine (studies/PLAN.md, steps 1–3, the premium step of G6, and Findings 17–20).
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
    /** The world's standardized draw: normal when `normal`, else skewed with shape k. */
    u.unit = function (k, normal) { return normal ? u.normal() : u.skewed(k); };
    /** Poisson(m): Knuth's product method, in pieces of mean ≤ 30 (a sum of Poissons is Poisson). */
    u.poisson = function (m) {
      let n = 0;
      while (m > 0) {
        const c = Math.min(m, 30), L = Math.exp(-c);
        let p = u();
        while (p > L) { n++; p *= u(); }
        m -= c;
      }
      return n;
    };
    /** Lomax (Pareto II) claim with scale 1 and tail index α: P(Y > y) = (1 + y)^(−α). */
    u.lomax = function (alpha) { return Math.pow(1 - u(), -1 / alpha) - 1; };
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

  /** Eigen-decomposition of a symmetric matrix (cyclic Jacobi; the matrices here are at most 20 × 20):
   * values ascending, vectors[k] the unit eigenvector of values[k]. */
  function eigenSym(A) {
    const n = A.length, M = A.map((row) => row.slice());
    const V = A.map((_, i) => A.map((__, j) => (i === j ? 1 : 0)));
    for (let sweep = 0; sweep < 100; sweep++) {
      let off = 0;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += M[p][q] * M[p][q];
      if (off < 1e-30) break;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
        if (Math.abs(M[p][q]) < 1e-300) continue;
        const th = (M[q][q] - M[p][p]) / (2 * M[p][q]);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), sn = t * c;
        for (let k = 0; k < n; k++) { const a = M[k][p], b = M[k][q]; M[k][p] = c * a - sn * b; M[k][q] = sn * a + c * b; }
        for (let k = 0; k < n; k++) { const a = M[p][k], b = M[q][k]; M[p][k] = c * a - sn * b; M[q][k] = sn * a + c * b; }
        for (let k = 0; k < n; k++) { const a = V[k][p], b = V[k][q]; V[k][p] = c * a - sn * b; V[k][q] = sn * a + c * b; }
      }
    }
    const order = M.map((_, i) => i).sort((a, b) => M[a][a] - M[b][b]);
    return { values: order.map((i) => M[i][i]), vectors: order.map((i) => V.map((row) => row[i])) };
  }
  /** Eigenvalues of a symmetric matrix, ascending. */
  const eigSym = (A) => eigenSym(A).values;

  /**
   * The nearest positive semidefinite table in the Frobenius norm: negative eigenvalues set to 0
   * (Higham 1988). The Frobenius norm is the H-norm of ConeProjection on the table's distinct
   * entries (weight 1 on the diagonal, 2 off it), and the PSD tables are a closed convex set that
   * contains the true covariance table, so the projection is never further from it, for every draw
   * (ConeProjection.existsUnique_proj_posSemidef). Returns the table, the number of eigenvalues
   * clipped and the Frobenius distance moved.
   */
  function projectPSD(A) {
    const { values, vectors } = eigenSym(A), n = A.length;
    const tol = 1e-12 * Math.max(1e-300, ...values.map(Math.abs));
    const clipped = values.filter((x) => x < -tol).length;
    if (!clipped) return { P: A.map((row) => row.slice()), clipped: 0, moved: 0 };
    const P = A.map(() => new Array(n).fill(0));
    values.forEach((lam, k) => {
      if (lam <= 0) return;
      const u = vectors[k];
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) P[i][j] += lam * u[i] * u[j];
    });
    for (let i = 0; i < n; i++) for (let j = 0; j < i; j++) { const x = (P[i][j] + P[j][i]) / 2; P[i][j] = x; P[j][i] = x; }
    let d = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) d += (P[i][j] - A[i][j]) ** 2;
    return { P, clipped, moved: Math.sqrt(d) };
  }

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
    ordered: false,  // regions in an order (age bands, neighbours): corr ρ^|i−j| instead of one common ρ
    volume: 500,     // vehicle-years per region and year, middle region
    spread: 1.0,     // how unequal the volumes are (log scale)
    growth: 0.03,    // yearly growth of every region's volume
    volNoise: 0,     // 0: off; > 0: log-SD of each region-year's volume around its region's trend (volumes of different shapes, S79)
    volTrend: 0,     // 0: off; > 0: SD of each region's own yearly growth around `growth` (S79)
    volSeed: 1,      // seed of the volume pattern: fixed per world, so every draw of a world sees the same volumes
    levelShape: 4,   // gamma shape of the level draws (skewness 2/√k)
    noiseShape: 2,   // gamma shape of the noise draws
    normal: false,   // normal levels and noise instead of gamma (the plug-in cross term vanishes: plugIn_mse_of_normal)
    lomax: 0,        // 0: off; α > 2: the region part of the noise is a sum of Lomax claims with tail index α (literature §10l)
    shrink: false,   // the gamma region part of a cell's noise has shape k·w/500 (a sum of claims; SHRINK_W0): skewness ∝ 1/√w, excess kurtosis ∝ 1/w; the year shock keeps shape k
    noiseSpread: 0,  // region-specific σⱼ = σ·4^(s((j mod 4)/3 − ½)): 0 equal, 1 = ×0.5–2 (studies' spread worlds)
    groups: 0,       // 0: off; G ≥ 2: regions in G groups (countries), region j in group j mod G, which share a level
    phi: 0.5,        // with groups: the shared share φ of the level variance, cov(μᵢ, μⱼ) = φτ² within a group (Hierarchical.lean)
  };

  /**
   * Raw moments of the Lomax claim (scale 1, tail index α > 2): E Y = 1/(α−1),
   * E Y² = 2/((α−1)(α−2)), E Y³ = 6/((α−1)(α−2)(α−3)) (∞ for α ≤ 3); in general
   * E Yⁿ⁺¹ / E Yⁿ = (n+1)/(α−n−1) for n + 1 < α (literature §10l).
   */
  function lomaxMoments(alpha) {
    const m1 = 1 / (alpha - 1), m2 = 2 / ((alpha - 1) * (alpha - 2));
    const m3 = alpha > 3 ? 6 / ((alpha - 1) * (alpha - 2) * (alpha - 3)) : Infinity;
    const m4 = alpha > 4 ? 24 / ((alpha - 1) * (alpha - 2) * (alpha - 3) * (alpha - 4)) : Infinity;
    return { m1, m2, m3, m4 };
  }

  /** E[Yᵏ; Y ≤ u] for the Lomax claim, k = 1, 2 (substitute x = 1 + y). */
  function lomaxTruncated(alpha, uTop) {
    const x = 1 + uTop, I = (e) => (Math.pow(x, e) - 1) / e; // ∫₁ˣ tᵉ⁻¹ dt
    const a1 = alpha * (I(1 - alpha) - I(-alpha));
    const a2 = alpha * (I(2 - alpha) - 2 * I(1 - alpha) + I(-alpha));
    return { a1, a2 };
  }

  /**
   * The standardized noise of one cell in the Lomax claims world (literature §10l): the total
   * S of N ~ Poisson(n) Lomax claims with tail index α, as (S − n E Y)/√(n E Y²), so mean 0 and
   * variance 1 exactly, skewness E Y³/(√n (E Y²)^(3/2)) (∞ for α ≤ 3), excess kurtosis
   * E Y⁴/(n (E Y²)²) (∞ for α ≤ 4). Exact for n ≤ 200 expected claims. Above, claims beyond the
   * level u that n·P(Y > u) = 50 expected claims exceed are drawn exactly (Y | Y > u is
   * (1 + u)·Pareto(α) − 1), and the claims below u are summed as a gamma with their exact mean
   * n E[Y; Y ≤ u] and variance n E[Y²; Y ≤ u]: the first two moments stay exact and the tail
   * is exact, only the small claims' shape is approximate.
   */
  function claimNoise(r, n, alpha) {
    const M = lomaxMoments(alpha);
    let S = 0;
    if (n <= 200) {
      const N = r.poisson(n);
      for (let i = 0; i < N; i++) S += r.lomax(alpha);
    } else {
      const big = 50, uTop = Math.pow(n / big, 1 / alpha) - 1;
      const N = r.poisson(big);
      for (let i = 0; i < N; i++) S += (1 + uTop) * Math.pow(1 - r(), -1 / alpha) - 1;
      const t = lomaxTruncated(alpha, uTop), mean = n * t.a1, v = n * t.a2;
      S += r.gamma(mean * mean / v) * v / mean;
    }
    return (S - n * M.m1) / Math.sqrt(n * M.m2);
  }

  /**
   * Claims per vehicle-year in region j of the Lomax world: λⱼ = μ²(E Y²/(E Y)²)/σⱼ², with mean
   * claim σⱼ²(E Y/E Y²)/μ, so that at the tariff μ = 1 a vehicle-year has mean μ and variance
   * σⱼ² (λ E Y = μ, λ E Y² = σⱼ²), as in the other worlds. σ = 6, α = 3: λ ≈ 0.11, mean claim ≈ 9.
   */
  function claimRate(world, j) {
    const M = lomaxMoments(world.params.lomax), mu = world.truth.mu;
    return mu * mu * (M.m2 / (M.m1 * M.m1)) / world.truth.sigmaj2[j];
  }

  /** Reference volume of the shrinking noise shape (params.shrink): a cell of w₀ vehicle-years has shape k. */
  const SHRINK_W0 = 500;

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
    // Volumes: the size of region j by its quantile, times a yearly trend. With volNoise or volTrend each
    // region gets its own trend and year-to-year noise (fixed by volSeed), so the regions' volumes no longer
    // share one shape over the years (wⱼₜ ≠ aⱼgₜ): the case of real portfolios (S79).
    const vr = p.volNoise > 0 || p.volTrend > 0 ? rng(p.volSeed) : null;
    for (let j = 0; j < J; j++) {
      const size = p.volume * Math.exp(p.spread * qnorm((j + 0.5) / J));
      const g = p.growth + (vr ? p.volTrend * vr.normal() : 0);
      const row = [];
      for (let t = 0; t < T; t++) row.push(size * Math.pow(Math.max(1 + g, 0.5), t - (T - 1) / 2) * (vr ? Math.exp(p.volNoise * vr.normal() - p.volNoise * p.volNoise / 2) : 1));
      w.push(row);
    }
    // ρᵢⱼ: one common coefficient, or ρ^|i−j| for ordered regions (a country structure comes with group levels).
    const rho = [], r0 = Math.max(p.rho, 0);
    for (let i = 0; i < J; i++) { rho.push([]); for (let j = 0; j < J; j++) rho[i].push(i === j ? 1 : p.ordered ? Math.pow(r0, Math.abs(i - j)) : p.rho); }
    // σⱼ²: region-specific noise; σ² stays the base (σⱼ = σ when noiseSpread = 0).
    const sigmaj2 = Array.from({ length: J }, (_, j) => (p.sigma * noiseFactor(j, p.noiseSpread)) ** 2);
    // Group levels (Hierarchical.lean, Bridge 4): L = τ²[(1 − φ)I + φ·same group], else τ²I.
    const G = p.groups >= 2 ? Math.min(p.groups, J) : 0, phi = G ? Math.min(Math.max(p.phi, 0), 0.999) : 0;
    const grp = G ? Array.from({ length: J }, (_, j) => j % G) : null, tau2 = p.tau * p.tau;
    const L = Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, j) =>
      i === j ? tau2 : grp && grp[i] === grp[j] ? phi * tau2 : 0));
    const truth = { mu: 1, tau2, sigma2: p.sigma * p.sigma, sigmaj2, rho, L, grp, phi };
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
        K[i].push(Math.sqrt(truth.sigmaj2[i] * truth.sigmaj2[j]) * truth.rho[i][j] * r / (wt[i] * wt[j]) + truth.L[i][j]);
      }
    }
    return K;
  }

  /**
   * One year's noise vector ε over the J regions, unit variances, for ordered regions:
   * ε₀ = ξ₀, εⱼ = ρεⱼ₋₁ + √(1−ρ²)ξⱼ (an AR(1) along the order), so corr(εᵢ, εⱼ) = ρ^|i−j|.
   */
  function orderedNoise(J, rho, r, ns, nz, xi) {
    const x = xi || (() => r.unit(ns, nz));
    const c = Math.sqrt(1 - rho * rho), e = [x(0)];
    for (let j = 1; j < J; j++) e.push(rho * e[j - 1] + c * x(j));
    return e;
  }

  /**
   * The region part ξ of region j's noise in a cell of volume w: a standardized sum of Lomax
   * claims when `params.lomax` (expected claims λⱼw), else the world's gamma or normal draw. With
   * `params.shrink` the gamma shape is k·w/w₀ (w₀ = SHRINK_W0 = 500 vehicle-years, the default middle
   * volume), as for a sum of claims in proportion to w: the cell's cumulants then scale as
   * κₙ ∝ w^−(n−1) (skewness 2/√(kw/w₀), excess kurtosis 6/(kw/w₀)), so the noise turns normal as the
   * volume grows (the central limit theorem in cumulant form; literature §10m).
   */
  function regionDraw(world, r, j, w) {
    const p = world.params;
    if (p.lomax) return claimNoise(r, claimRate(world, j) * w, p.lomax);
    return r.unit(p.shrink ? p.noiseShape * w / SHRINK_W0 : p.noiseShape, p.normal);
  }

  /**
   * One data set from the world: the levels μⱼ (truth) and the table { w, X }.
   * Xⱼₜ = μⱼ + σⱼ/√wⱼₜ · εⱼₜ with εⱼₜ = √ρ·ηₜ + √(1-ρ)·ξⱼₜ, so corr(εᵢₜ, εⱼₜ) = ρ; with
   * `params.ordered` εₜ = orderedNoise (corr ρ^|i−j|). All draws skewed (gamma), or normal with
   * `params.normal`. With `params.shrink` the region part's gamma shape grows with the volume
   * (regionDraw). With `params.lomax` the region part ξⱼₜ (the AR(1) innovations when
   * ordered) is a standardized sum of Lomax claims (claimNoise); the year shock ηₜ is not.
   */
  function draw(world, r) {
    const { J, T, w, truth, params } = world;
    const rho = params.rho, a = Math.sqrt(Math.max(rho, 0)), b = Math.sqrt(1 - Math.max(rho, 0));
    const tau = Math.sqrt(truth.tau2), sig = truth.sigmaj2.map(Math.sqrt);
    const levels = [], X = [];
    let groupEff = null;
    const nz = params.normal, ns = params.noiseShape;
    if (truth.grp) {
      // μⱼ = μ + τ(√φ γ_g + √(1 − φ) ηⱼ): group effects γ_g and region effects ηⱼ, unit variance (HierarchicalMoments.lean).
      const G = Math.max(...truth.grp) + 1, gam = Array.from({ length: G }, () => r.unit(params.levelShape, nz));
      for (let j = 0; j < J; j++) levels.push(truth.mu + tau * (Math.sqrt(truth.phi) * gam[truth.grp[j]] + Math.sqrt(1 - truth.phi) * r.unit(params.levelShape, nz)));
      groupEff = gam.map((x) => tau * Math.sqrt(truth.phi) * x);
    } else for (let j = 0; j < J; j++) levels.push(truth.mu + tau * r.unit(params.levelShape, nz));
    const withGrp = (d) => (truth.grp ? Object.assign(d, { grp: Object.freeze(truth.grp.slice()) }) : d);
    if (params.ordered) {
      const E = [];
      for (let t = 0; t < T; t++) E.push(orderedNoise(J, Math.max(rho, 0), r, ns, nz, (j) => regionDraw(world, r, j, w[j][t])));
      for (let j = 0; j < J; j++) X.push(E.map((e, t) => levels[j] + sig[j] / Math.sqrt(w[j][t]) * e[j]));
      return { levels, groupEffects: groupEff, data: Object.freeze(withGrp({ w: w.map((row) => Object.freeze(row.slice())), X })) };
    }
    const eta = [];
    for (let t = 0; t < T; t++) eta.push(r.unit(ns, nz));
    for (let j = 0; j < J; j++) {
      const row = [];
      for (let t = 0; t < T; t++) {
        const eps = a * eta[t] + b * regionDraw(world, r, j, w[j][t]);
        row.push(levels[j] + sig[j] / Math.sqrt(w[j][t]) * eps);
      }
      X.push(row);
    }
    const data = Object.freeze(withGrp({ w: w.map((row) => Object.freeze(row.slice())), X }));
    return { levels, groupEffects: groupEff, data };
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

  // ---------------------------------------------------------------- the best linear predictor (Findings 18–20)

  /** The blend as weights on the cohort estimates: z eⱼ + (1 − z) b (Core.linMse_blendWeight). */
  function blendWeight(z, b, j) {
    return b.map((bi, i) => (i === j ? z : 0) + (1 - z) * bi);
  }

  /**
   * Best linear unbiased predictor of μⱼ from all cohort estimates, levels L = τ²I (Finding 18,
   * Core.blupWeight): d* = K⁻¹ℓ + (1 − 1ᵀK⁻¹ℓ) b with ℓ = τ²eⱼ and the GLS weights b.
   */
  function blupWeight(K, tau2, j) {
    const J = K.length, u = solve(K, new Array(J).fill(1)), tot = sum(u), b = u.map((x) => x / tot);
    const l = solve(K, K.map((_, i) => (i === j ? tau2 : 0))), s = sum(l);
    return l.map((x, i) => x + (1 - s) * b[i]);
  }

  /** True MSE of Σᵢ dᵢμ̂ᵢ for μⱼ when cov(μ̂) = K and L = τ²I (Core.linMse): dᵀKd − 2τ²dⱼ + τ². */
  function linMse(K, tau2, j, d) {
    let q = 0;
    for (let i = 0; i < d.length; i++) for (let k = 0; k < d.length; k++) q += d[i] * K[i][k] * d[k];
    return q - 2 * tau2 * d[j] + tau2;
  }

  /**
   * The same with a general level covariance L (group levels): the best z for the GLS weights b,
   * zⱼ = (Bⱼ − Cⱼ)/(Aⱼ + Bⱼ − 2Cⱼ) with Aⱼ = Var(μ̂ⱼ − μⱼ) = Kⱼⱼ − Lⱼⱼ, Bⱼ = Var(μ̂ − μⱼ) = bᵀKb − 2(Lb)ⱼ + Lⱼⱼ,
   * Cⱼ = cov(μ̂ⱼ − μⱼ, μ̂ − μⱼ) = (Kb)ⱼ − (Lb)ⱼ (eq. (7) on these moments; Hierarchical.bestZ_G_eq).
   */
  function blendMomentsL(K, L, b, j) {
    const J = K.length, Kb = K.map((row) => sum(row.map((x, i) => x * b[i]))), Lb = L.map((row) => sum(row.map((x, i) => x * b[i])));
    const bKb = sum(b.map((x, i) => x * Kb[i]));
    return { A: K[j][j] - L[j][j], B: bKb - 2 * Lb[j] + L[j][j], C: Kb[j] - Lb[j], J };
  }
  function bestBlendWeightsL(K, L) {
    const J = K.length, u = solve(K, new Array(J).fill(1)), tot = sum(u), b = u.map((x) => x / tot);
    const z = b.map((_, j) => { const { A, B, C } = blendMomentsL(K, L, b, j), g = A + B - 2 * C; return g > 0 ? (B - C) / g : 0; });
    return { b, z, s2: 1 / tot };
  }
  function blendMSEL(K, L, b, j, z) {
    const { A, B, C } = blendMomentsL(K, L, b, j);
    return z * z * A + (1 - z) * (1 - z) * B + 2 * z * (1 - z) * C;
  }
  /** BLUP of μⱼ with level covariance L (universal kriging, Core.blup_optimal): d* = K⁻¹ℓ + (1 − 1ᵀK⁻¹ℓ)b, ℓ = L eⱼ. */
  function blupWeightL(K, L, j) {
    const J = K.length, u = solve(K, new Array(J).fill(1)), tot = sum(u), b = u.map((x) => x / tot);
    const l = solve(K, L.map((row) => row[j])), s = sum(l);
    return l.map((x, i) => x + (1 - s) * b[i]);
  }
  /** True MSE of Σᵢ dᵢμ̂ᵢ for μⱼ with level covariance L: dᵀKd − 2dᵀLeⱼ + Lⱼⱼ. */
  function linMseL(K, L, j, d) {
    let q = 0;
    for (let i = 0; i < d.length; i++) for (let k = 0; k < d.length; k++) q += d[i] * K[i][k] * d[k];
    return q - 2 * sum(d.map((x, i) => x * L[i][j])) + L[j][j];
  }
  const hasGroups = (world) => !!world.truth.grp;

  /**
   * The noise correlation's spread around I (Finding 20): with R = D^(−½)VD^(−½) the correlation
   * matrix of the noise V = K − τ²I, δ₋ = 1 − λmin(R) and δ₊ = λmax(R) − 1, so that
   * −δ₋ Σvᵢyᵢ² ≤ yᵀVy − Σvᵢyᵢ² ≤ δ₊ Σvᵢyᵢ² (the hypothesis of Core.linMse_damped_le).
   */
  function noiseDeltas(V) {
    const R = V.map((row, i) => row.map((x, k) => (i === k ? 1 : x / Math.sqrt(V[i][i] * V[k][k]))));
    const ev = eigSym(R);
    return { dm: Math.max(0, 1 - ev[0]), dp: Math.max(0, ev[ev.length - 1] - 1) };
  }

  /**
   * Worst-case MSE ratio of a working model that damps the noise correlations by θ, against the
   * best predictor (Core.linMse_damped_le, Kantorovich): (a + A)²/(4aA) with
   * a = (1 − δ₋)/(1 − θδ₋), A = (1 + δ₊)/(1 + θδ₊). θ = 0 ignores the correlation
   * (Core.linMse_ignoreCorr_le_two_sided), θ = 1 is the true model (ratio 1). Infinite if δ₋ ≥ 1.
   */
  function dampedBound(dm, dp, theta) {
    if (!(dm < 1)) return Infinity;
    const a = (1 - dm) / (1 - theta * dm), A = (1 + dp) / (1 + theta * dp);
    return (a + A) * (a + A) / (4 * a * A);
  }

  /**
   * The prices in a world with known parameters (Findings 18–19), per region j, in true MSE:
   *   best   — the best linear unbiased predictor d* (Core.blupWeight_optimal);
   *   blend  — the best blend, eq. (26) (the floor): pays (w − d*)ᵀK(w − d*) (Core.errVar_eq_blupWeight_add);
   *   ignore — Bühlmann–Straub with the true variances, i.e. the predictor of K̃ = diag(τ² + vᵢ)
   *            (Core.blupWeight_diag_eq_blendWeight), at most `bound` × best (Core.linMse_ignoreCorr_le_two_sided).
   * Weighted: Σ wⱼ* MSEⱼ / w**, as the app's error. Reads the truth.
   */
  function correlationPrice(K, tau2, wt, L) {
    // With group levels L (optional): the same prices with ℓ = L eⱼ; "ignore" drops the noise correlation only.
    const J = K.length, Lm = L || K.map((row, i) => row.map((_, k) => (i === k ? tau2 : 0)));
    const V = K.map((row, i) => row.map((x, k) => x - Lm[i][k]));
    const Kd = K.map((row, i) => row.map((x, k) => (i === k ? V[i][i] : 0) + Lm[i][k]));
    const { b, z } = L ? bestBlendWeightsL(K, L) : bestBlendWeights(K, tau2);
    const best = [], blendM = [], ignore = [];
    for (let j = 0; j < J; j++) {
      best.push(linMseL(K, Lm, j, blupWeightL(K, Lm, j)));
      blendM.push(linMseL(K, Lm, j, blendWeight(z[j], b, j)));
      ignore.push(linMseL(K, Lm, j, blupWeightL(Kd, Lm, j)));
    }
    const { dm, dp } = noiseDeltas(V);
    const wall = sum(wt), agg = (a) => sum(a.map((x, j) => wt[j] * x)) / wall;
    return { best, blend: blendM, ignore, dm, dp, bound: dampedBound(dm, dp, 0), weighted: { best: agg(best), blend: agg(blendM), ignore: agg(ignore) } };
  }

  /** correlationPrice of a world: the true K. Reads the truth. */
  function worldPrice(world) {
    return correlationPrice(trueK(world), world.truth.tau2, world.w.map(sum), hasGroups(world) ? world.truth.L : undefined);
  }

  /**
   * "Is correlation worth modelling?" from data only (Findings 19–20): δ̂₋, δ̂₊ of corrBS's noise
   * table Σ̂ (one ρ̂, credibility-weighted σ̃ⱼ), and the bounds for ignoring it (θ = 0) and for a
   * fit that keeps a share θ of it (θ = 1: none).
   */
  function correlationIndicator(data, theta) {
    const p = vcEstimate(data), { dm, dp } = noiseDeltas(p.Sig);
    return { rho: p.rho, dm, dp, ignore: dampedBound(dm, dp, 0), damped: theta == null ? null : dampedBound(dm, dp, theta) };
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
    if (params.ordered) {
      const e = orderedNoise(levels.length, Math.max(params.rho, 0), r, params.noiseShape, params.normal, (j) => regionDraw(world, r, j, wNext[j]));
      return levels.map((mu, j) => mu + Math.sqrt(truth.sigmaj2[j] / wNext[j]) * e[j]);
    }
    const eta = r.unit(params.noiseShape, params.normal);
    return levels.map((mu, j) => mu + Math.sqrt(truth.sigmaj2[j] / wNext[j]) * (a * eta + b * regionDraw(world, r, j, wNext[j])));
  }

  /**
   * The formulas, written once: the fits' steps (this draw) and RECIPES (the page's Recipe
   * section) both read them, so the recipe is always what the fit computes.
   */
  const F = {
    means: 'μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*',
    bsSigma: 'σ̂² = (1/J) Σⱼ Σₜ wⱼₜ (Xⱼₜ − μ̂ⱼ)² / (T−1)',
    bsTau: 'τ̂² = (Σⱼ wⱼ*(μ̂ⱼ − μ̄)² − (J−1)σ̂²) / (w** − Σⱼ wⱼ*²/w**)',
    bsZ: 'zⱼ = wⱼ* / (wⱼ* + σ̂²/τ̂²)',
    bOfZ: 'bⱼ = zⱼ / z*',
    rates: 'μ̂ⱼᵇ = zⱼ μ̂ⱼ + (1 − zⱼ) μ̂,  μ̂ = Σⱼ bⱼ μ̂ⱼ',
    sigDiag: 'σ²ⱼⱼ^ = σ̂ⱼ²/wⱼ*,  σ̂ⱼ² = Σₜ wⱼₜ(Xⱼₜ − μ̂ⱼ)²/(T−1)  (eq. (41))',
    sigOff: 'σ²ᵢⱼρᵢⱼ^ = Qᵢⱼ / (Sᵢⱼ + (T−2)wᵢ*wⱼ*/Sᵢⱼ)  (eq. (39))',
    common: 'ĉ = average of σ²ᵢⱼρᵢⱼ^ over the pairs i ≠ j',
    cj: 'ĉⱼ = Σᵢ (δᵢⱼ − wᵢ*/w**) Σ̂ᵢⱼ',
    tau: 'τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ) / (w** − Σᵢ wᵢ*²/w**)  (eq. (39))',
    damped: 'K̂ = Σ̂ with off-diagonal × θ, + τ̂²⁺ I',
    dampedP: 'K̂ = Σ̂⁺ with off-diagonal × θ, + τ̂²⁺ I',
    psdProj: 'Σ̂⁺ = Σₖ max(λₖ, 0) uₖuₖᵀ  (λₖ, uₖ the eigenvalues and eigenvectors of Σ̂)',
    dampRule: 'θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T−1)), r̄ the average estimated correlation Σ̂ᵢⱼ/√(Σ̂ᵢᵢΣ̂ⱼⱼ) over the pairs',
    taper: 'K̂ᵢⱼ = ρ^|i−j| (Σ̂ + τ̂²⁺ I)ᵢⱼ  (regions in their order)',
    taperP: 'K̂ᵢⱼ = ρ^|i−j| (Σ̂⁺ + τ̂²⁺ I)ᵢⱼ  (regions in their order)',
    taperRule: 'ρ̂ minimises Σ_d n_d [ρ^2d (r̄_d² + (1 − r̄_d²)²/(T−1)) − 2ρ^d r̄_d²], r̄_d the average estimated correlation of the n_d pairs at distance d',
    zEq: 'zⱼ = τ̂² / (τ̂² + v̂ⱼ − θĉ)',
    gls: 'b = K̂⁻¹1 / 1ᵀK̂⁻¹1  (GLS, eq. (25))',
    z26: 'zⱼ = (1 − bⱼ)τ̂² / (K̂ⱼⱼ − s²),  s² = 1/1ᵀK̂⁻¹1  (eq. (26))',
    vcSigma: 'σ̂ⱼ² = Σₜ wⱼₜ(Xⱼₜ − μ̂ⱼ)²/(T−1),  σ̂² = (1/J) Σⱼ σ̂ⱼ²',
    vcW: 'Wⱼ = Σₜ (uⱼₜ − σ̂ⱼ²)²/(T(T−1)), uⱼₜ = wⱼₜ(Xⱼₜ − μ̂ⱼ)²T/(T−1);  β² = Σⱼ(σ̂ⱼ² − σ̂²)²/(J−1) − (1/J)Σⱼ Wⱼ',
    vcTilde: 'σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂²,  ζⱼ = β²/(β² + Wⱼ)',
    vcRho: 'ρ̂ = Σᵢ<ⱼ Qᵢⱼ / Σᵢ<ⱼ σ̃ᵢσ̃ⱼ((T−2) + Sᵢⱼ²/(wᵢ*wⱼ*))',
    vcTau: 'τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ) / (w** − Σᵢ wᵢ*²/w**),  ĉⱼ = Σᵢ (δᵢⱼ − wᵢ*/w**) Σ̂ᵢⱼ  (eq. (39))',
    vcK: 'K̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) (i ≠ j),  σ̃ⱼ²/wⱼ* + τ̂² (i = j)',
    blupD: 'd̂ = K̂⁻¹ℓ + (1 − 1ᵀK̂⁻¹ℓ) b,  ℓ = τ̂² eⱼ;  shown: own-data weight d̂ⱼⱼ',
    blupRates: 'rateⱼ = Σᵢ d̂ᵢ μ̂ᵢ',
    vcPooled: 'σ̃ⱼ² = σ̂² for every region (pooled)',
    taperSignal: 'taper when Σ_d n_d [R²(r̄_d² + V_d) − 2R r̄_d² + r̄_d²] < Σ_d n_d [(r̄ − r̄_d)² − V_d/n_d]⁺, R = ρ̂^d, V_d = (1 − r̄_d²)²/(T − 1)',
    gainPrice: 'region variances when (MSE on K̂ with one pooled σ̂² − MSE on K̂) / MSE on K̂ > Σⱼ wⱼ* ẑⱼ(1 − ẑⱼ)·2/(T − 1)·MSEⱼ / Σⱼ wⱼ* MSEⱼ',
    balance: 'rateⱼ + D,  D = Σᵢ wᵢ*(μ̂ᵢ − rateᵢ)/w**, the same D for every region',
    balanceAuto: 'balance iff cost̂ = m(g_cf) − m(g_r̄) < 0 on the yearly cells:  m(g) = (G − u)ᵀL̂(G − u) + Σₛ gₛᵀD̂ₛgₛ,  Gᵢ = Σₛ gₛᵢ,  g_cf,ₛ = πₛc̄⁽ˢ⁾ (the cross-fit\'s weights),  g_r̄,ₛᵢ = cᵢwᵢₛ/wᵢ*,  c = Σⱼ uⱼ d̂⁽ʲ⁾,  D̂ₛᵢₖ = (K̂ − L̂)ᵢₖwᵢ*wₖ*/(Sᵢₖ√(wᵢₛwₖₛ)),  uⱼ = wⱼ*/w** (on one volume shape: mse(c̄) − mse(c) on K̂);  bias readout D = L̂cf − Σⱼ uⱼ rateⱼ ± 2·SD on the cells',
    balanceCf: 'rateⱼ + D,  D = L̂cf − Σᵢ wᵢ* rateᵢ/w**,  L̂cf = Σₛ πₛ Σᵢ c̄ᵢ⁽ˢ⁾ Xᵢₛ,  c̄⁽ˢ⁾ = Σⱼ (wⱼ*/w**) d̂⁽ʲ⁾ from the pooled BLUP fitted without year s',
    premium: 'premium = μ̂ⱼᵇ;  forecast error² = MSEⱼ + σ̂ⱼ²/wⱼ,next',
    grpPairs: 'P̂ᵢⱼ = (μ̂ᵢ − μ̂ⱼ)² − (σ²ᵢᵢρᵢᵢ^ + σ²ⱼⱼρⱼⱼ^ − 2σ²ᵢⱼρᵢⱼ^) for i < j (eq. (39) estimates), E P̂ᵢⱼ = 2λ + 2φτ²·[different groups], λ = (1 − φ)τ²',
    grpFirst: 'first pass: W̄, Ā = the averages of P̂ᵢⱼ within and across groups with weights wᵢ*wⱼ*;  λ̂₀ = W̄/2, φτ²₀ = (Ā − W̄)/2',
    grpGLS: '(λ̂, φτ²^) = (XᵀV̂⁻¹X)⁻¹XᵀV̂⁻¹P̂,  rows of X: (2, 2·[different groups]),  V̂ₚq = 2 ĉ(Dₚ, D_q)² + N̂ₚN̂_q·2/(J(T−1))',
    grpK: 'K̂ = Σ̂ + L̂,  L̂ᵢⱼ = λ̂⁺δᵢⱼ + φτ²^⁺·[same group]  (⁺: negative set to 0)',
    grpBlupD: 'd̂ = K̂⁻¹ℓⱼ + (1 − 1ᵀK̂⁻¹ℓⱼ) b,  ℓⱼ = L̂eⱼ (column j of L̂);  shown: own-data weight d̂ⱼⱼ',
    grpChoice: 'groups when Σₛ Σⱼ wⱼₛ(rateⱼ⁽⁻ˢ⁾ − Xⱼₛ)² is smaller with groups than without, rateⱼ⁽⁻ˢ⁾ fitted without year s',
  };

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
    const level = levelMSE || fit.levelMSE || Array.from({ length: J }, (_, j) => blendMSE(fit.K, tau2, b, s2, j, fit.z[j]));
    const noise = wt.map((x, j) => (fit.K[j][j] - tau2) * x / wNext[j]);
    const mse = level.map((g, j) => g + noise[j]);
    const step = {
      name: 'premium', formula: F.premium, values: mse.map(Math.sqrt),
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
      means: m, z, b, mu: res.mu, rates: res.rates, warnings, flags: { tauNeg: tauRaw <= 0 }, theta: 0,
      sigma2, tau2, K: wt.map((x, i) => wt.map((_, j) => (i === j ? sigma2 / x + tau2 : 0))),
      steps: [
        { name: 'cohort means', formula: F.means, values: m, badge: 'proved', lean: 'Credibility.bs_a' },
        { name: 'σ̂²', formula: F.bsSigma, values: [sigma2], badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
        { name: 'τ̂²', formula: F.bsTau, values: [tauRaw], badge: 'proved', lean: 'Credibility.Model.tauHatBS_unbiased', note: 'classical eq. (13): unbiased when the regions are uncorrelated with a common σ (G0)' },
        { name: 'z', formula: F.bsZ, values: z, badge: 'proved', lean: 'Credibility.bs_z' },
        { name: 'b', formula: F.bOfZ, values: b, badge: 'proved', lean: 'Credibility.bs_b' },
        { name: 'rates', formula: F.rates, values: res.rates, badge: 'proved', lean: 'Credibility.bs_balance' },
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

  /** The distance taper ρ^|tᵢ − tⱼ| for cohorts at positions t (Lean: distTaper); t = 0…J−1 by default. */
  function distTaper(rho, J, t) {
    const pos = t || Array.from({ length: J }, (_, j) => j);
    return pos.map((ti) => pos.map((tj) => Math.pow(rho, Math.abs(ti - tj))));
  }
  const hadamard = (R, A) => A.map((row, i) => row.map((x, j) => R[i][j] * x));

  /**
   * The taper's ρ by the plug-in criterion of the damping study (studies/LOG.md S3 and
   * "What a distribution-free theorem can say"): on the correlation scale, a taper Rᵢⱼ = ρ^dᵢⱼ
   * turns the estimate r̂ᵢⱼ into Rᵢⱼr̂ᵢⱼ, with expected loss Σᵢ<ⱼ E(Rᵢⱼr̂ᵢⱼ − rᵢⱼ)²
   *   = Σᵢ<ⱼ [Rᵢⱼ²(rᵢⱼ² + Vᵢⱼ) − 2Rᵢⱼ rᵢⱼ²] + const.
   * Plug-ins: rᵢⱼ² by r̄_d², the average estimated correlation over the pairs at distance d (as S3
   * uses ρ̄ over all pairs), and Vᵢⱼ by (1 − r̄_d²)²/(T − 1). Minimised over ρ ∈ [0, 1] on a grid
   * of 0.001. With every pair at distance 1 (the damping taper) the minimiser is S3's
   * θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T − 1)). Data only, nothing to tune.
   * Returns { rho, lags: [{ d, n, r }] }.
   */
  function taperRho(Sig, T, dist) {
    const J = Sig.length, by = new Map();
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) {
      const d = dist(i, j), r = Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]);
      if (!by.has(d)) by.set(d, { d, n: 0, s: 0 });
      const g = by.get(d); g.n++; g.s += r;
    }
    const lags = [...by.values()].sort((a, b) => a.d - b.d).map((g) => ({ d: g.d, n: g.n, r: Math.max(-1, Math.min(1, g.s / g.n)) }));
    const terms = lags.map((g) => { const S = g.r * g.r; return { d: g.d, n: g.n, S, V: (1 - S) ** 2 / (T - 1) }; });
    const loss = (rho) => sum(terms.map((g) => { const R = Math.pow(rho, g.d); return g.n * (R * R * (g.S + g.V) - 2 * R * g.S); }));
    let best = 0, bl = loss(0);
    for (let k = 1; k <= 1000; k++) { const x = k / 1000, l = loss(x); if (l < bl - 1e-15) { bl = l; best = x; } }
    return { rho: best, lags };
  }

  /**
   * Data-side signal for the BLUP taper (studies/runs/taper-signal.js): does the estimated correlation
   * fall with distance? Both candidate tables are judged by S3's plug-in loss per pair of the
   * correlation table, with the same two parameters per lag (r̄_d, V_d = (1 − r̄_d²)²/(T − 1)):
   *   taper  (each r̂ᵢⱼ times ρ̂^d, ρ̂ = taperRho):  Σ_d n_d [R²(r̄_d² + V_d) − 2R r̄_d² + r̄_d²], R = ρ̂^d;
   *   common (each r̂ᵢⱼ replaced by r̄, as corrBS):  Σ_d n_d [(r̄ − r̄_d)² − V_d/n_d]₊,
   * r̄ the mean over all pairs (the noise of r̄_d removed from the squared gap, pairs taken as
   * independent). Prefers the taper when its loss is smaller. No tuning constant.
   */
  function taperSignal(data) {
    const est = sigmaHat(data), Sig = est.Sig, T = data.X[0].length;
    const tr = taperRho(Sig, T, (i, j) => Math.abs(i - j)), lags = tr.lags;
    const np = sum(lags.map((g) => g.n)), rbar = sum(lags.map((g) => g.n * g.r)) / np;
    const V = (r) => (1 - r * r) ** 2 / (T - 1);
    const lossTaper = sum(lags.map((g) => { const R = Math.pow(tr.rho, g.d), S = g.r * g.r; return g.n * (R * R * (S + V(g.r)) - 2 * R * S + S); }));
    const lossCommon = sum(lags.map((g) => g.n * Math.max((rbar - g.r) ** 2 - V(g.r) / g.n, 0)));
    return { rho: tr.rho, rbar, lags, lossTaper, lossCommon, preferTaper: lossTaper < lossCommon };
  }

  /**
   * Law (a), the first-order price of fitting Bühlmann–Straub's z, relative to (1 − z)τ², exact in the
   * balanced world with fourth cumulants (Cumulants.bsPrice_of_balanced_cumulants):
   *   (1 − 1/J)(1 − z)/z · [2/(J(T − 1)) + 2/(J − 1) + γL z²/J + γN z²/(JT)],
   * γN = κN/σ⁴ the excess kurtosis of the noise, γL = κL/τ⁴ that of the levels (κL/(Js²) = γL z²/J,
   * s = τ² + σ²/(wT) = τ²/z). With γL = γN = 0 it is (2/J)(1 + (J − 1)/(J(T − 1)))(1 − z)/z
   * (bsPrice_of_balanced), below the old bound (2/J)·T/(T − 1)·(1 − z)/z (bsPrice_le_of_balanced).
   */
  function bsPriceLaw(z, J, T, gammaL, gammaN) {
    return (1 - 1 / J) * (1 - z) / z * (2 / (J * (T - 1)) + 2 / (J - 1) + (gammaL || 0) * z * z / J + (gammaN || 0) * z * z / (J * T));
  }

  /**
   * The first-order cross term 2E[AB] of the Bühlmann–Straub plug-in for region j, any volumes
   * (Cumulants.crossTerm_bs_of_cumulants, Finding 38): one noise variance σ², level variance τ², fourth
   * cumulants κL of a level and κN/wᵢₜ² of a cell's noise (κN = γN σ⁴, κL = γL τ⁴), D = σ² estimated.
   * With Wᵢ = Σₜwᵢₜ, k = σ²/τ², zᵢ = Wᵢ/(Wᵢ + k), bᵢ = zᵢ/Σz, S = Σz(1 − z), hᵢ = Σₜ(wᵢₜ/Wᵢ)², c = W − ΣWᵢ²/W:
   *   αᵢ = zⱼδᵢⱼ + (1 − zⱼ)bᵢ,  λᵢ = −(zⱼ(1 − zⱼ)(δᵢⱼ − bᵢ) + (1 − zⱼ)(zᵢ(1 − zᵢ) − Sbᵢ)/Σz),
   *   T_P = κN/(J(T − 1)) Σᵢ αᵢλᵢ(1 − hᵢ)/Wᵢ,  T_B = Σᵢ λᵢ(1 − Wᵢ/W)(κL Wᵢ(αᵢ − δᵢⱼ) + κN hᵢαᵢ/Wᵢ),
   *   2E[AB] = 2((1/σ² + (J − 1)/(cτ²)) T_P − T_B/(cτ²)).
   * Returns { level, noise } per unit κL and κN (the term is linear in both): 2E[AB] = κL·level + κN·noise.
   */
  function crossTermBS(w, sigma2, tau2, j) {
    const J = w.length, T = w[0].length, W = w.map(sum), Wt = sum(W), k = sigma2 / tau2;
    const z = W.map((x) => x / (x + k)), Z = sum(z), b = z.map((x) => x / Z), S = sum(z.map((x) => x * (1 - x)));
    const h = w.map((row, i) => sum(row.map((x) => (x / W[i]) ** 2)));
    const c = Wt - sum(W.map((x) => x * x)) / Wt, d = (i) => (i === j ? 1 : 0);
    const al = b.map((bi, i) => z[j] * d(i) + (1 - z[j]) * bi);
    const la = b.map((bi, i) => -(z[j] * (1 - z[j]) * (d(i) - bi) + (1 - z[j]) * (z[i] * (1 - z[i]) - S * bi) / Z));
    const tP = sum(al.map((a, i) => a * la[i] * (1 - h[i]) / W[i])) / (J * (T - 1)); // per unit κN
    const tBL = sum(la.map((l, i) => l * (1 - W[i] / Wt) * W[i] * (al[i] - d(i))));     // per unit κL
    const tBN = sum(la.map((l, i) => l * (1 - W[i] / Wt) * h[i] * al[i] / W[i]));       // per unit κN
    const f = 1 / sigma2 + (J - 1) / (c * tau2);
    return { level: -2 * tBL / (c * tau2), noise: 2 * (f * tP - tBN / (c * tau2)) };
  }

  /**
   * Noise shape from the pooled within-region residuals scaled by √w: rⱼₜ = √wⱼₜ(Xⱼₜ − μ̂ⱼ) = (Mε)ₜ with
   * εₜ = √wⱼₜ·noise (variance σⱼ², third and fourth cumulants κ₃ⱼ, κ₄ⱼ) and M = I − vvᵀ, vₜ = √aₜ,
   * aₜ = wⱼₜ/wⱼ*. For independent years (Cumulants: moments of quadratic forms)
   *   E Σₜ rₜ⁴ = 3σ⁴ Σₜ Mₜₜ² + κ₄ Σₜₛ Mₜₛ⁴,  E (Σₜ rₜ²)² = σ⁴((T − 1)² + 2(T − 1)) + κ₄ Σₜ Mₜₜ²,
   *   E Σₜ rₜ³ = κ₃ Σₜₛ Mₜₛ³,
   * solved per region for unbiased σ⁴ⱼ, κ₄ⱼ (and κ₃ⱼ, σ̂ⱼ² = Σrₜ²/(T − 1)); pooled as ratios of sums:
   *   skew = Σⱼ κ̂₃ⱼ / Σⱼ σ̂ⱼ³,  kurt (excess, γ̂N) = Σⱼ κ̂₄ⱼ / Σⱼ σ̂⁴ⱼ.
   * Standard errors of the normal case √(6/N), √(24/N), N = JT residuals: under skewed noise one draw's
   * γ̂N spreads far wider (gamma noise with kurtosis 3, J = 8, T = 10: mean 2.8, median 1.5, SD ≈ 4.5;
   * T = 5: mean 5.3), and the skewness reads about 20% low (σ̂ⱼ rises with a skewed draw). Year shocks shared across
   * regions are part of each region's noise here (they make the residuals of different regions
   * dependent, so the SEs are then too small). Null when T < 3 or the pooled σ⁴ is not positive.
   */
  function noiseShape(data) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data);
    if (T < 3) return null;
    let k3 = 0, s3 = 0, k4 = 0, s4 = 0;
    for (let j = 0; j < J; j++) {
      const a = data.w[j].map((x) => x / wt[j]), r = data.X[j].map((x, t) => Math.sqrt(data.w[j][t]) * (x - m[j]));
      const M = (t, s) => (t === s ? 1 : 0) - Math.sqrt(a[t] * a[s]);
      let mm = 0, c4 = 0, c3 = 0;
      for (let t = 0; t < T; t++) { mm += M(t, t) ** 2; for (let s = 0; s < T; s++) { c4 += M(t, s) ** 4; c3 += M(t, s) ** 3; } }
      const A = sum(r.map((x) => x ** 4)), R2 = sum(r.map((x) => x * x)), B = R2 * R2, n2 = (T - 1) * (T - 1) + 2 * (T - 1);
      const det = 3 * mm * mm - c4 * n2;
      s4 += (A * mm - c4 * B) / det;
      k4 += (3 * mm * B - n2 * A) / det;
      k3 += sum(r.map((x) => x ** 3)) / c3;
      s3 += Math.pow(R2 / (T - 1), 1.5);
    }
    if (!(s4 > 0) || !(s3 > 0)) return null;
    const N = J * T;
    return { N, skew: k3 / s3, skewSE: Math.sqrt(6 / N), kurt: k4 / s4, kurtSE: Math.sqrt(24 / N) };
  }

  /**
   * Gain against price (studies/PLAN.md Pending; studies/LOG.md S53–S56), from the data only. On
   * corrBS's fitted table K̂, τ̂² (taken as the truth), the exact oracle gains in MSE, as fractions of the
   * best blend's MSE (`floor`):
   *   corrBS over BS (BS's weights at its limiting σ², τ² under K̂), BLUP over the blend, and region
   *   variances σ̃ⱼ² over one pooled σ̄² (the same K̂ with σ̄² in every region);
   * and the first-order prices of S56 (relative to the floor, per region, floor-weighted):
   *   fitting BS at all: law (a) in its exact balanced form, bsPriceLaw (with the noise kurtosis γ̂N of
   *   noiseShape and the level kurtosis `opts.gammaL`, a sensitivity, default 0); `fitBSNormal` without
   *   the kurtosis terms;  own variances ≈ zⱼ(1 − zⱼ)·2/(T − 1) (law (b): the proved upper bound,
   *   Cumulants.ownPrice_sub_pooled_le_of_balanced; the exact balanced form is (1 − 1/J)² times it,
   *   Cumulants.ownPrice_sub_pooled_of_balanced, `opts.lawB = 'exact'`; S57 kept the bound: same mean
   *   regret, worst case 3.3 against 4.9, the slack offsetting the law's understatement at low z).
   * Estimating one ρ is nearly free (S54), and the BLUP uses the same K̂ as the blend, so the only real
   * trade-off is the variances: verdict 'region' when their gain exceeds their price, else 'pooled'.
   * `valid`: share of the volume in regions with ẑⱼ ≥ 0.5, where the price laws hold (S56).
   * Returns null when τ̂² = 0 (no credibility to trade).
   */
  function gainPrice(data, opts) {
    const gammaL = (opts && opts.gammaL) || 0;
    const f = fitVC(data), J = f.means.length, T = data.X[0].length, wt = data.w.map(sum), wall = sum(wt);
    const K = f.K, t2 = f.tau2;
    if (!(t2 > 0)) return null;
    const blendRows = (Kx) => { const { b, z } = bestBlendWeights(Kx, t2); return z.map((zj, j) => b.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi)); };
    const avg = (D) => sum(D.map((d, j) => wt[j] * linMse(K, t2, j, d))) / wall;
    const floorJ = blendRows(K).map((d, j) => linMse(K, t2, j, d)), floor = sum(floorJ.map((x, j) => wt[j] * x)) / wall;
    const blup = avg(K.map((_, j) => blupWeight(K, t2, j)));
    // BS at its limits under K̂: σ²_BS = mean σ̃ⱼ² (within-region residuals are unbiased for each σⱼ²),
    // τ²_BS = (E B − (J − 1)σ²_BS)/c₀ with E B = Σ wⱼ* Kⱼⱼ − wᵀKw/w**.
    const s2BS = sum(f.sigma2) / J, c0 = wall - sum(wt.map((x) => x * x)) / wall;
    const EB = sum(wt.map((x, j) => x * K[j][j])) - sum(wt.map((x, i) => sum(wt.map((y, j) => x * y * K[i][j])))) / wall;
    const t2BS = (EB - (J - 1) * s2BS) / c0;
    const zBS = wt.map((x) => (t2BS > 0 ? x / (x + s2BS / t2BS) : 0)), zs = sum(zBS);
    const bBS = zs > 0 ? zBS.map((x) => x / zs) : wt.map((x) => x / wall);
    const bs = avg(zBS.map((zj, j) => bBS.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi)));
    // One pooled variance in the same table: diagonal σ̄²/wⱼ* + τ̂², off-diagonal scaled by σ̄²/(σ̃ᵢσ̃ⱼ).
    const sd = f.sigma2.map(Math.sqrt), sbar = sum(f.sigma2) / J;
    const Kp = K.map((row, i) => row.map((x, j) => (i === j ? sbar / wt[i] + t2 : x * sbar / (sd[i] * sd[j]))));
    const pooled = avg(blendRows(Kp));
    const z = f.z.map((x) => Math.min(Math.max(x, 1e-6), 1 - 1e-6));
    const pf = (g) => sum(z.map((zj, j) => wt[j] * g(zj) * floorJ[j])) / wall / floor;
    const shape = noiseShape(data), gN = shape ? shape.kurt : 0;
    const priceFit = pf((zj) => bsPriceLaw(zj, J, T, gammaL, gN)), lawB = opts && opts.lawB === 'exact' ? (1 - 1 / J) ** 2 : 1,
      priceVar = pf((zj) => lawB * zj * (1 - zj) * 2 / (T - 1));
    const priceNormal = pf((zj) => bsPriceLaw(zj, J, T, 0, 0));
    // The kurtosis terms are linear in γL and γN: their parts, and the price per unit of γL.
    const perGammaL = pf((zj) => bsPriceLaw(zj, J, T, 1, 0)) - priceNormal;
    const gainVar = (pooled - floor) / floor;
    // The cross term 2E[AB] of BS (Finding 38: law (a) alone has the noise kurtosis with the wrong sign), at BS's
    // limits under K̂, floor-weighted; per unit γN (κN = γN σ⁴) and γL (κL = γL τ⁴). Null when τ²_BS ≤ 0.
    let cross = null;
    if (t2BS > 0) {
      const ct = wt.map((_, j) => crossTermBS(data.w, s2BS, t2BS, j));
      const agg = (key, scale) => sum(ct.map((x, j) => wt[j] * x[key] * scale)) / wall / floor;
      const perGN = agg('noise', s2BS * s2BS), perGL = agg('level', t2BS * t2BS);
      cross = { perGammaN: perGN, perGammaL: perGL, noise: gN * perGN, total: gN * perGN + gammaL * perGL };
    }
    return {
      cross,
      floor, gain: { corrBSoverBS: (bs - floor) / floor, blupOverBlend: (floor - blup) / floor, regionVariances: gainVar },
      price: { fitBS: priceFit, fitBSNormal: priceNormal, fitBSNoiseKurt: priceFit - priceNormal - gammaL * perGammaL, fitBSPerGammaL: perGammaL, gammaL, regionVariances: priceVar },
      noiseShape: shape,
      valid: sum(f.z.map((zj, j) => (zj >= 0.5 ? wt[j] : 0))) / wall,
      verdict: gainVar > priceVar ? 'region' : 'pooled',
    };
  }

  /**
   * corrBS with the variance step chosen by gain against price (studies S57): corrBS up to K̂, then
   * Engine.gainPrice on that K̂; if its verdict is 'pooled', σ̃ⱼ², ρ̂, τ̂² and K̂ are redone with one pooled
   * σ̂² (fitVC pooled). b, z and the rates come from the chosen table.
   */
  function fitVCGP(data) {
    const full = fitVC(data), g = gainPrice(data), branch = g && g.verdict === 'pooled' ? 'pooled' : 'region';
    const f = branch === 'pooled' ? fitVC(data, { pooled: true }) : full;
    const upto = full.steps.findIndex((x) => x.name === 'K̂') + 1;
    const choice = { name: 'variances: gain against price', formula: F.gainPrice, values: g ? [g.gain.regionVariances, g.price.regionVariances] : [0, 0], badge: 'not proved yet', gap: 'G1',
      note: `the gain is exact on K̂ (mse_blend_eq_blup_add form), the price a first-order law, proved in the balanced world as an upper bound (Cumulants.ownPrice_sub_pooled_le_of_balanced; studies S56, holds for ẑ ≥ 0.6)${g ? `; ${branch === 'pooled' ? 'gain below price: one pooled σ̂²' : 'gain above price: region variances'}` : '; τ̂² = 0: nothing to trade, region variances kept'}` };
    const redo = branch === 'pooled'
      ? f.steps.filter((x) => ['σ̃ⱼ²', 'ρ̂', 'τ̂²', 'K̂'].includes(x.name)).map((x) => Object.assign({}, x, { name: `${x.name} (pooled)`, branch }))
      : [];
    const steps = full.steps.slice(0, upto).concat([choice], redo, f.steps.filter((x) => ['b', 'z', 'rates'].includes(x.name)));
    return Object.assign({}, f, { steps, branch, gainPrice: g });
  }

  /**
   * Leave-one-year-out loss of a fit (studies/runs/taper-signal.js, S49): for each year s, refit on the
   * other T − 1 years and score the rates against the held-out cell rates, volume-weighted:
   *   L = Σₛ Σⱼ wⱼₛ (rateⱼ⁽⁻ˢ⁾ − Xⱼₛ)² / Σₛⱼ wⱼₛ.
   * Years are independent, so E L = (MSE of the rates from T − 1 years) + (noise of the held-out
   * cell), the second term the same for every fit: the difference of two fits' L estimates the
   * difference of their MSEs, with no tuning. A refit that throws counts as the pooled mean.
   */
  function loyoLoss(data, fitFn) {
    const T = data.X[0].length, J = data.X.length;
    let num = 0, den = 0;
    for (let s = 0; s < T; s++) {
      const sub = { w: data.w.map((row) => row.filter((_, t) => t !== s)), X: data.X.map((row) => row.filter((_, t) => t !== s)) };
      if (data.grp) sub.grp = data.grp;
      let rates;
      try { rates = fitFn(sub).rates; } catch (e) { const m = cohortMeans(sub).m; rates = m.map(() => sum(m) / J); }
      for (let j = 0; j < J; j++) { num += data.w[j][s] * (rates[j] - data.X[j][s]) ** 2; den += data.w[j][s]; }
    }
    return num / den;
  }

  /** The BLUP chosen by leave-one-year-out loss between BLUP taper and BLUP on corrBS's K̂ (S49). */
  function fitBLUPLoyo(data) {
    const lt = loyoLoss(data, fitBLUPTaper), lb = loyoLoss(data, fitBLUP), taper = lt < lb;
    const f = taper ? fitBLUPTaper(data) : fitBLUP(data);
    f.notes = (f.notes || []).concat([`Leave-one-year-out loss: taper ${lt.toPrecision(3)}, corrBS ${lb.toPrecision(3)}: ${taper ? 'BLUP taper' : 'BLUP on corrBS’s K̂'}.`]);
    return Object.assign(f, { loyo: { taper: lt, corrBS: lb, preferTaper: taper } });
  }

  /**
   * BLUP with group levels (PLAN G4, S69): corrBS's noise table Σ̂, the pair estimators P̂ᵢⱼ with
   * mean 2λ + 2φτ²[across] (Model.pairHat_unbiasedG), a volume-weighted first pass
   * (Model.phiTauPooled_unbiasedG), then Gauss–Markov on the pair table V̂ from that pass under the
   * normal formulas (Model.phiTauPool_blue_optimal: best for the true V; here V̂ is plugged in, so
   * only nearly unbiased). Then the BLUP of each μⱼ with L̂ (Core.blup_optimal with ℓⱼ = L̂eⱼ).
   * Null when the groups are missing or a class of pairs is empty (φτ² not identified).
   */
  function fitGroupLevels(data) {
    const grp = data.grp, J = data.X.length, T = data.X[0].length;
    if (!grp) return null;
    const p = vcEstimate(data), { m, wt, Sig } = p;
    const pairs = [];
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) pairs.push([i, j, grp[i] === grp[j] ? 0 : 1]);
    if (!pairs.some((x) => x[2] === 0) || !pairs.some((x) => x[2] === 1)) return null;
    // P̂ᵢⱼ with the thesis's pairwise noise estimates, eq. (39) (unbiased: Model.pairHat_unbiasedG);
    // corrBS's smoother table Σ̂ (clipped ρ̂, shrunk σ̃ⱼ²) only builds V̂ and K̂.
    const Sh = sigmaHat(data).Sig;
    const N = pairs.map(([i, j]) => Sig[i][i] + Sig[j][j] - 2 * Sig[i][j]);
    const P = pairs.map(([i, j]) => (m[i] - m[j]) ** 2 - (Sh[i][i] + Sh[j][j] - 2 * Sh[i][j]));
    const sw = [0, 0], sp = [0, 0];
    pairs.forEach(([i, j, x], k) => { sw[x] += wt[i] * wt[j]; sp[x] += wt[i] * wt[j] * P[k]; });
    const Wb = sp[0] / sw[0], Ab = sp[1] / sw[1], lam0 = Wb / 2, th0 = (Ab - Wb) / 2;
    const Lmat = (l, t) => Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, j) => (i === j ? l + t : grp[i] === grp[j] ? t : 0)));
    const K0 = Sig.map((row, i) => row.map((x, j) => x + Lmat(Math.max(lam0, 1e-12), Math.max(th0, 0))[i][j]));
    const cD = (a, b, c, d) => K0[a][c] - K0[a][d] - K0[b][c] + K0[b][d], rel = 2 / (J * (T - 1));
    const V = pairs.map(([a, b], k) => pairs.map(([c, d], q) => 2 * cD(a, b, c, d) ** 2 + N[k] * N[q] * rel));
    const X = pairs.map(([, , x]) => [2, 2 * x]);
    let lamRaw = lam0, thRaw = th0;
    try {
      const VX0 = solve(V, X.map((x) => x[0])), VX1 = solve(V, X.map((x) => x[1])), VP = solve(V, P);
      const A00 = sum(X.map((x, k) => x[0] * VX0[k])), A01 = sum(X.map((x, k) => x[0] * VX1[k])), A11 = sum(X.map((x, k) => x[1] * VX1[k]));
      const r0 = sum(X.map((x, k) => x[0] * VP[k])), r1 = sum(X.map((x, k) => x[1] * VP[k])), det = A00 * A11 - A01 * A01;
      if (Math.abs(det) > 0) { lamRaw = (A11 * r0 - A01 * r1) / det; thRaw = (A00 * r1 - A01 * r0) / det; }
    } catch (e) { /* V̂ singular: keep the first pass */ }
    const lam = Math.max(lamRaw, 0), th = Math.max(thRaw, 0), L = Lmat(lam, th);
    const K = Sig.map((row, i) => row.map((x, j) => x + L[i][j]));
    const u = solve(K, new Array(J).fill(1)), tot = sum(u), b = u.map((x) => x / tot);
    const D = m.map((_, j) => blupWeightL(K, L, j));
    const rates = D.map((d) => sum(d.map((x, i) => x * m[i]))), c = D.map((d, j) => d[j]);
    const levelMSE = D.map((d, j) => linMseL(K, L, j, d)), mu = sum(b.map((x, i) => x * m[i]));
    const warnings = lam + th <= 0 ? ['λ̂ and φτ²^ ≤ 0, set to 0: every region gets the portfolio level'] : [];
    const notes = [`λ̂ = ${lamRaw.toPrecision(3)}, φτ²^ = ${thRaw.toPrecision(3)}${thRaw <= 0 ? ' (≤ 0: no shared level, set to 0)' : ''}; φ̂ = ${lam + th > 0 ? (th / (lam + th)).toFixed(2) : '—'}.`];
    const vcSteps = fitVC(data).steps.filter((x) => !['τ̂²', 'K̂', 'b', 'z', 'rates'].includes(x.name));
    const steps = vcSteps.concat([
      { name: 'pairs P̂ᵢⱼ', formula: F.grpPairs, values: [P.length], badge: 'proved', lean: 'Credibility.Model.pairHat_unbiasedG', note: `${pairs.filter((x) => !x[2]).length} pairs within groups, ${pairs.filter((x) => x[2]).length} across; the noise estimates of eq. (39), unbiased for any correlation` },
      { name: 'first pass', formula: F.grpFirst, values: [lam0, th0], badge: 'proved', lean: 'Credibility.Model.phiTauPooled_unbiasedG', note: 'unbiased for any weights summing to one on each side' },
      { name: 'λ̂, φτ²^', formula: F.grpGLS, values: [lamRaw, thRaw], badge: 'proved', lean: 'Credibility.Model.phiTauPool_blue_optimal', note: 'least variance among unbiased pools for the true V; V̂ from the first pass under normal formulas, Dₚ = μ̂ᵢ − μ̂ⱼ, N̂ₚ the pair’s noise on Σ̂. With V̂ from the same data it is not exactly unbiased: λ̂ runs 20–40% high in 12-region worlds, the first pass does not (S69: still the slightly better blend)' },
      { name: 'K̂ (groups)', formula: F.grpK, values: [lam, th], badge: 'proved', lean: 'Credibility.Unequal.KG_posDef' },
      { name: 'b (groups)', formula: F.gls, values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
      { name: 'BLUP weights (groups)', formula: F.grpBlupD, values: c, badge: 'proved', lean: 'Credibility.Core.blup_optimal', note: 'for each region j a weight vector over all regions, summing to 1; regions of j’s group get more weight' },
      { name: 'rates (groups)', formula: F.blupRates, values: rates, badge: 'proved', lean: 'Credibility.Core.blup_optimal', note: 'the parameters are plugged in: optimal among unbiased linear predictors for the true K and L' },
    ]);
    return { means: m, z: null, b, c, weights: D, mu, rates, warnings, notes, flags: { tauNeg: lam + th <= 0 }, K, L, tau2: lam + th, lam, phiTau: th, groupEffects: groupEffects(K, grp, th, m), lamRaw, phiTauRaw: thRaw, rho: p.rho, theta: 1, levelMSE, steps };
  }

  /**
   * The best linear unbiased predictor of each group effect b_g (variance φτ², covariance φτ² with the
   * cohort means of its group): d = K⁻¹ℓ − (1ᵀK⁻¹ℓ)b (Unequal.groupEffect_eq_blup: Henderson's b̂_g), and its
   * exact MSE φτ² − ℓᵀK⁻¹ℓ + (1ᵀK⁻¹ℓ)²/1ᵀK⁻¹1 (NoiseG.mse_groupEffect_blup), for the K, φτ² given.
   * m: cohort means, or null for the MSE only.
   */
  function groupEffects(K, grp, phiTau, m) {
    const J = K.length, G = Math.max(...grp) + 1, u = solve(K, new Array(J).fill(1)), s = sum(u);
    return Array.from({ length: G }, (_, g) => {
      const ell = grp.map((x) => (x === g ? phiTau : 0)), k = solve(K, ell), c = sum(k);
      const d = k.map((x, i) => x - c * u[i] / s);
      return { g, est: m ? sum(d.map((x, i) => x * m[i])) : null, mse: Math.max(phiTau - sum(ell.map((x, i) => x * k[i])) + c * c / s, 0), d };
    });
  }

  /**
   * Group levels or none, chosen on held-out years (CrossFit.integral_heldOutScore_sub: the difference
   * of the two held-out scores is unbiased for the difference of their true errors, for the rules fitted
   * on the other years, any distribution). Without groups in the data: the BLUP on corrBS's K̂.
   */
  function fitGroups(data) {
    const g = fitGroupLevels(data);
    let useG = false, lg = null, ln = null;
    if (g) {
      lg = loyoLoss(data, (d) => fitGroupLevels(d) || fitBLUP(d)); ln = loyoLoss(data, fitBLUP); useG = lg < ln;
    }
    const f = useG ? g : fitBLUP(data), branch = useG ? 'groups' : 'none';
    const choice = { name: 'groups or none', formula: F.grpChoice, values: g ? [lg, ln] : [], badge: 'proved', lean: 'Credibility.CrossFit.integral_heldOutScore_sub',
      note: g ? `leave-one-year-out score: groups ${lg.toPrecision(3)}, none ${ln.toPrecision(3)}: ${useG ? 'group levels' : 'no groups'}; the winner’s score is optimistic (CrossFit.integral_min_score_le)` : 'no groups in the data, or a kind of pair missing: no groups' };
    f.steps = f.steps.concat([choice]);
    f.branch = branch;
    f.notes = (f.notes || []).concat([g ? `Held-out score with groups ${lg.toPrecision(3)}, without ${ln.toPrecision(3)}: ${useG ? 'group levels' : 'no groups'}.` : 'No groups in the data: BLUP on corrBS’s K̂.']);
    return Object.assign(f, { loyoGroups: g ? { groups: lg, none: ln, useGroups: useG } : null, groupFit: g });
  }

  /** The BLUP on the table the signal prefers: fitBLUPTaper or fitBLUP (studies/runs/taper-signal.js). */
  function fitBLUPAuto(data) {
    const sig = taperSignal(data), branch = sig.preferTaper ? 'taper' : 'corrBS', f = sig.preferTaper ? fitBLUPTaper(data) : fitBLUP(data);
    const choice = { name: 'taper signal', formula: F.taperSignal, values: [sig.lossTaper, sig.lossCommon], badge: 'not proved yet', gap: 'G2',
      note: `r̄_d: the average estimated correlation (thesis Σ̂) of the pairs at distance d, n_d of them, r̄ over all pairs; ${sig.preferTaper ? 'falls with distance: BLUP taper' : 'no clear fall: BLUP on corrBS’s K̂'} (studies S46)` };
    const tail = new Set(['b', 'BLUP weights', 'rates']);
    f.steps = [f.steps[0], choice].concat(f.steps.slice(1).map((x) => (tail.has(x.name) ? x : Object.assign({}, x, { branch }))));
    f.branch = branch;
    f.notes = (f.notes || []).concat([sig.preferTaper
      ? `The estimated correlation falls with distance (taper loss ${sig.lossTaper.toFixed(2)} < common ${sig.lossCommon.toFixed(2)}): BLUP taper, ρ̂ = ${sig.rho.toFixed(2)}.`
      : `No clear fall of the correlation with distance (taper loss ${sig.lossTaper.toFixed(2)} ≥ common ${sig.lossCommon.toFixed(2)}): BLUP on corrBS’s K̂.`]);
    return Object.assign(f, { signal: sig });
  }

  /**
   * Exact variance of the off-diagonal Σ̂ᵢⱼ of eq. (39) (sigmaHat) when the years are independent,
   * from given second and fourth moments (Cumulants.variance_sum_mul_lin with the residual
   * coefficients uᵢₜ(s) = cᵢₜ(δₜₛ − aᵢₛ), cᵢₜ = √wᵢₜ, aᵢₛ = wᵢₛ/wᵢ*; with every cᵢₜ = 1 it is
   * Cumulants.variance_crossResid, the numerator of Shock.crossHat). Inputs, per vehicle-year:
   * cov the J×J noise covariance (cell covariance in year s: covᵢⱼ/√(wᵢₛwⱼₛ)), and kappa the
   * excess kurtosis of the common year shock, so that the within-year fourth cumulant of the pair
   * is kₛᵢⱼᵢⱼ = κ·covᵢⱼ²/(wᵢₛwⱼₛ) (one shock ηₜ shared by all regions, the region parts independent
   * across regions: their own kurtosis, e.g. the Lomax claims, does not enter for i ≠ j).
   *   Var Σ̂ᵢⱼ = (Σₜₜ' [GⁱⁱGʲʲ + GⁱʲGʲⁱ]ₜₜ' + Σₛ (Σₜ uᵢₜ(s)uⱼₜ(s))² kₛᵢⱼᵢⱼ) / Dᵢⱼ²,
   *   Gᵇᶜₜₜ' = Σₛ uᵦₜ(s) u꜀ₜ'(s) covᵦ꜀/√(wᵦₛw꜀ₛ),  Dᵢⱼ = Sᵢⱼ + (T−2)wᵢ* wⱼ* / Sᵢⱼ.
   * Returns the J×J table (diagonal left 0).
   */
  function sigmaHatVar(w, cov, kappa, unit) {
    const J = w.length, T = w[0].length, wt = w.map(sum);
    const c = (i, t) => (unit ? 1 : Math.sqrt(w[i][t]));
    const u = (i, t, s) => c(i, t) * ((t === s ? 1 : 0) - w[i][s] / wt[i]);
    const G = (b, d) => {
      const g = [];
      for (let t = 0; t < T; t++) {
        g.push([]);
        for (let t2 = 0; t2 < T; t2++) {
          let x = 0;
          for (let s = 0; s < T; s++) x += u(b, t, s) * u(d, t2, s) * cov[b][d] / Math.sqrt(w[b][s] * w[d][s]);
          g[t].push(x);
        }
      }
      return g;
    };
    const Gd = w.map((_, i) => G(i, i)), V = w.map(() => new Array(J).fill(0));
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) {
      const Gij = G(i, j);
      let q = 0;
      for (let t = 0; t < T; t++) for (let t2 = 0; t2 < T; t2++) q += Gd[i][t][t2] * Gd[j][t][t2] + Gij[t][t2] * Gij[t2][t];
      if (kappa) for (let s = 0; s < T; s++) {
        let m = 0;
        for (let t = 0; t < T; t++) m += u(i, t, s) * u(j, t, s);
        q += m * m * kappa * cov[i][j] ** 2 / (w[i][s] * w[j][s]);
      }
      let S = 0;
      for (let t = 0; t < T; t++) S += unit ? 1 : Math.sqrt(w[i][t] * w[j][t]);
      const D = unit ? 1 : S + (T - 2) * wt[i] * wt[j] / S;
      V[i][j] = V[j][i] = q / (D * D);
    }
    return V;
  }

  /**
   * θ̂ in covariance form (PLAN G2, Damping.bestTheta): θ̂ = Σᵢ<ⱼ sᵢⱼ² / Σᵢ<ⱼ (sᵢⱼ² + Vᵢⱼ), with sᵢⱼ the
   * mean of Σ̂ᵢⱼ and Vᵢⱼ its exact variance (sigmaHatVar). Plug-ins as in S3: one common correlation
   * r̄ (the average estimated one), so covᵢⱼ = r̄σ̂ᵢσ̂ⱼ (σ̂ⱼ² = wⱼ*Σ̂ⱼⱼ) and sᵢⱼ = covᵢⱼSᵢⱼ/(wᵢ*wⱼ*);
   * kappa the shock's excess kurtosis (0: normal theory). opts.cov, opts.s: force the tables (tests,
   * the oracle). Returns { theta, rbar }.
   */
  function covTheta(data, kappa, opts) {
    const o = opts || {}, { wt, S, Sig } = sigmaHat(data), J = Sig.length;
    let s = 0, n = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
    const rbar = Math.max(-1, Math.min(1, s / n)), sd = Sig.map((row, j) => Math.sqrt(row[j] * wt[j]));
    const cov = o.cov || sd.map((a, i) => sd.map((b, j) => (i === j ? a * a : rbar * a * b)));
    const V = sigmaHatVar(data.w, cov, kappa || 0);
    let num = 0, den = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) {
      const m = cov[i][j] * S[i][j] / (wt[i] * wt[j]);
      num += m * m; den += m * m + V[i][j];
    }
    return { theta: den > 0 ? num / den : 0, rbar };
  }

  /**
   * Exact covariances of the entries of Σ̂ (eq. (39)) over independent years, for a noise with one
   * common correlation r: eₐₛ = σₐ/√wₐₛ (√r ηₛ + √(1−r) ξₐₛ), shock ηₛ shared, region parts ξ
   * independent. Fourth cumulants: kShock (excess kurtosis of η) and kRegion(a, s) (of ξₐₛ; may
   * depend on the cell, e.g. the Lomax claims, ∞ for α ≤ 4). Cumulants.variance_sum_mul_lin in its
   * covariance form: cov(Σₜ UᵃUᵇ, Σₜ UᶜUᵈ) = Σₜₜ' [GᵃᶜGᵇᵈ + GᵃᵈGᵇᶜ]ₜₜ' + Σₛ mₐᵦ(s) m꜀ᵈ(s) kₛ(a, b, c, d),
   * mₐᵦ(s) = Σₜ uₐₜ(s)uᵦₜ(s), divided by DₐᵦD꜀ᵈ. Returns { cv(a, b, c, d), mean(a, b) }.
   */
  function sigmaHatMoments(w, sd, r, kShock, kRegion) {
    const J = w.length, T = w[0].length, wt = w.map(sum);
    const cov = (a, b) => sd[a] * sd[b] * (a === b ? 1 : r);
    const u = (i, t, s) => Math.sqrt(w[i][t]) * ((t === s ? 1 : 0) - w[i][s] / wt[i]);
    const key = (a, b) => a * J + b, Gs = new Map(), Ms = new Map();
    const G = (a, b) => {
      if (!Gs.has(key(a, b))) {
        const g = [];
        for (let t = 0; t < T; t++) {
          g.push(new Float64Array(T));
          for (let t2 = 0; t2 < T; t2++) {
            let x = 0;
            for (let s = 0; s < T; s++) x += u(a, t, s) * u(b, t2, s) / Math.sqrt(w[a][s] * w[b][s]);
            g[t][t2] = x * cov(a, b);
          }
        }
        Gs.set(key(a, b), g);
      }
      return Gs.get(key(a, b));
    };
    const m = (a, b) => {
      if (!Ms.has(key(a, b))) Ms.set(key(a, b), Array.from({ length: T }, (_, s) => { let x = 0; for (let t = 0; t < T; t++) x += u(a, t, s) * u(b, t, s); return x; }));
      return Ms.get(key(a, b));
    };
    const S = (a, b) => { let x = 0; for (let t = 0; t < T; t++) x += Math.sqrt(w[a][t] * w[b][t]); return x; };
    const D = (a, b) => { const x = S(a, b); return x + (T - 2) * wt[a] * wt[b] / x; };
    const k4 = (s, a, b, c, d) => {
      let k = kShock ? kShock * r * r * sd[a] * sd[b] * sd[c] * sd[d] / Math.sqrt(w[a][s] * w[b][s] * w[c][s] * w[d][s]) : 0;
      if (kRegion && a === b && b === c && c === d) k += kRegion(a, s) * (1 - r) ** 2 * sd[a] ** 4 / (w[a][s] ** 2);
      return k;
    };
    const cv = (a, b, c, d) => {
      const Gac = G(a, c), Gbd = G(b, d), Gad = G(a, d), Gbc = G(b, c);
      let q = 0;
      for (let t = 0; t < T; t++) for (let t2 = 0; t2 < T; t2++) q += Gac[t][t2] * Gbd[t][t2] + Gad[t][t2] * Gbc[t][t2];
      if (kShock || kRegion) { const mab = m(a, b), mcd = m(c, d); for (let s = 0; s < T; s++) q += mab[s] * mcd[s] * k4(s, a, b, c, d); }
      return q / (D(a, b) * D(c, d));
    };
    const mean = (a, b) => cov(a, b) * S(a, b) / (wt[a] * wt[b]);
    return { cv, mean };
  }

  /**
   * Var r̂ᵢⱼ of the estimated correlation r̂ = Σ̂ᵢⱼ/√(Σ̂ᵢᵢΣ̂ⱼⱼ) by the delta method from the exact
   * covariances of (Σ̂ᵢⱼ, Σ̂ᵢᵢ, Σ̂ⱼⱼ) (sigmaHatMoments): gᵀCg with g = (1, −x/2y, −x/2z)/√(yz) at the
   * means. Balanced, normal: (1 − r²)²/(T − 1) to first order, S3's variance.
   */
  function corrVar(M, i, j) {
    const x = M.mean(i, j), y = M.mean(i, i), z = M.mean(j, j), q = 1 / Math.sqrt(y * z);
    const g = [q, -x * q / (2 * y), -x * q / (2 * z)], P = [[i, j], [i, i], [j, j]];
    let v = 0;
    for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) v += g[a] * g[b] * M.cv(P[a][0], P[a][1], P[b][0], P[b][1]);
    return v;
  }

  /**
   * S3 with the exact variance: θ̂ = r̄²/(r̄² + V̄), V̄ the average of corrVar over the pairs at the
   * plug-ins r̄, σ̂ⱼ (or opts.r, opts.sd: the truth, for the studies); opts.kShock, opts.kRegion the
   * fourth cumulants (default 0: normal theory). Returns { theta, rbar, V }.
   */
  function corrTheta(data, opts) {
    const o = opts || {}, { wt, Sig } = sigmaHat(data), J = Sig.length;
    let s = 0, n = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
    const rbar = Math.max(-1, Math.min(1, s / n));
    const r = o.r != null ? o.r : Math.max(0, rbar), sd = o.sd || Sig.map((row, j) => Math.sqrt(row[j] * wt[j]));
    const M = sigmaHatMoments(data.w, sd, r, o.kShock || 0, o.kRegion || null);
    let V = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) V += corrVar(M, i, j);
    V /= n;
    const r2 = rbar * rbar;
    return { theta: r2 + V > 0 && isFinite(V) ? r2 / (r2 + V) : 0, rbar, V };
  }

  /** The old grid rule (opts.thetaRule = 'grid', kept for the studies): the largest of these with K̂ ≻ 0. */
  const THETAS = [0.95, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1, 0];

  /**
   * The thesis model with correlation, fitted from data (eqs. (37)–(41), §2.8).
   * opts.common: replace the off-diagonal Σ̂ᵢⱼ by their average c̄ (one common
   *   covariance; then zⱼ = τ²/(τ² + vⱼ − c), Core.bestZ_of_equalCov).
   * opts.theta: force a damping factor (tests). Otherwise θ̂ by the damping study's rule S3,
   *   θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T − 1)) with r̄ the average estimated correlation over the pairs
   *   (taperRho with every pair at distance 1; studies/runs/taper.js: up to 12 points better than the
   *   old fixed θ = 0.95), lowered in steps of 0.05 only if K̂ is not positive definite.
   *   opts.thetaRule = 'grid': the old rule, the largest of THETAS with K̂ ≻ 0.
   *   opts.thetaRule = 'cov': θ̂ in covariance form with the exact variance (covTheta), opts.kappa the
   *   shock's excess kurtosis (default 0; studies only, the app does not estimate it yet).
   *   opts.thetaRule = 'corr': S3 with the exact delta-method Var r̂ᵢⱼ (corrTheta; opts.kShock,
   *   opts.kRegion; studies only).
   * opts.taper = 'distance': instead of damping, taper by ρ^|i−j| over the region order
   *   (K̂ = R ⊙ (Σ̂ + τ̂²I), Lean: posDef_distTaper_hadamard), ρ̂ by taperRho (opts.rho forces it);
   *   lowered in steps of 0.05 only if K̂ is not positive definite.
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
    // G2a: K̂ is built on the nearest PSD Σ̂ (ConeProjection), so the K̂ ≻ 0 theorems apply to every
    // draw. τ̂², ĉⱼ and the plug-in rules for θ̂, ρ̂ keep the raw (unbiased) Σ̂. Not for one common
    // covariance, whose closed form z needs the common structure; opts.project = false is the old fit.
    const project = !o.common && o.project !== false;
    const proj = project ? projectPSD(Sig) : null, SigK = proj ? proj.P : Sig;
    const psd = isPSD(SigK), diagPos = SigK.every((row, j) => row[j] > 0);
    const T = data.X[0].length, dist = o.taper === 'distance';
    let theta = null, thetaFit = null, K = null, rhoT = null, rhoFit = null, lags = null;
    if (dist) {
      const tr = o.rho != null ? { rho: o.rho, lags: null } : taperRho(Sig, T, (i, j) => Math.abs(i - j));
      rhoFit = tr.rho; lags = tr.lags;
      const Kraw = addDiag(SigK, tau2);
      for (let x = rhoFit; ; x = Math.max(0, Math.round((x - 0.05) * 1000) / 1000)) {
        const Kt = hadamard(distTaper(x, J), Kraw);
        if (cholesky(Kt)) { rhoT = x; K = Kt; break; }
        if (x === 0) break;
      }
    } else if (o.theta != null || o.thetaRule === 'grid') {
      for (const th of (o.theta != null ? [o.theta] : THETAS)) {
        const Kt = addDiag(shrinkOffDiag(th, SigK), tau2);
        if (cholesky(Kt)) { theta = th; K = Kt; break; }
      }
      thetaFit = o.theta != null ? o.theta : THETAS[0];
    } else {
      thetaFit = Math.min(o.thetaRule === 'cov' ? Math.round(covTheta(data, o.kappa || 0).theta * 1000) / 1000 : o.thetaRule === 'corr' ? Math.round(corrTheta(data, o).theta * 1000) / 1000 : taperRho(Sig, T, () => 1).rho, 0.999);   // below 1 so posDef_shrinkOffDiag applies (θ̂ = 1 iff r̄ = ±1, e.g. T = 2)
      for (let x = thetaFit; ; x = Math.max(0, Math.round((x - 0.05) * 1000) / 1000)) {
        const Kt = addDiag(shrinkOffDiag(x, SigK), tau2);
        if (cholesky(Kt)) { theta = x; K = Kt; break; }
        if (x === 0) break;
      }
    }
    if (!K) throw new Error(`K̂ not positive definite even at ${dist ? 'ρ' : 'θ'} = 0`);
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
      tauNeg: tauRaw <= 0, zOver1: z.some((x) => x > 1), zNeg: z.some((x) => x < 0), bNeg: b.some((x) => x < 0),
      thetaLow: dist ? rhoT < rhoFit : theta < thetaFit, offBalance: Math.abs(offBal) > 0.01,
    };
    const warnings = [];
    if (flags.tauNeg) warnings.push('τ̂² ≤ 0, set to 0 (eq. (40)): no credibility, every region gets the portfolio level μ̂');
    if (flags.zOver1) warnings.push(`z > 1 for ${z.filter((x) => x > 1).length} region(s): the rate moves past the region's own mean, away from μ̂ (thesis eq. (34) would clip it; clipping cannot hurt only if the true z is in [0, 1], Finding 36; for corrBS's in-sample ẑ it changes the error by under 0.2 points of the floor, S83)`);
    if (flags.zNeg) warnings.push(`z < 0 for ${z.filter((x) => x < 0).length} region(s): with the true parameters a negative z can be the best blend (Finding 17: past a singularity the gap μ̂ⱼ − μ̂ flips sign together with z, and the own-data weight cⱼ = bⱼ + zⱼ(1 − bⱼ) stays bounded), so clipping z to 0 is not the fix; in a fit it more likely means K̂ is nearly singular: look at ρ̂ and τ̂²`);
    if (flags.bNeg) warnings.push(`negative portfolio weight b for ${b.filter((x) => x < 0).length} region(s): GLS uses it as a hedge against correlated noise`);
    if (flags.thetaLow) warnings.push(dist ? `K̂ was not positive definite at the fitted ρ̂ = ${rhoFit}; taper lowered to ρ = ${rhoT}` : `K̂ was not positive definite at θ̂ = ${thetaFit}; damping lowered to θ = ${theta}`);
    if (flags.offBalance) warnings.push(`off-balance: Σ wⱼ*(μ̂ⱼ − μ̂ⱼᵇ) is ${(100 * offBal).toFixed(1)}% of the premium volume`);
    const offs = [];
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) offs.push(Sig[i][j]);
    const steps = [
      { name: 'cohort means', formula: F.means, values: m, badge: 'proved', lean: 'Credibility.Model.a_special', note: 'aⱼₜ = wⱼₜ/wⱼ* (eq. (29))' },
      { name: 'Σ̂ diagonal', formula: F.sigDiag, values: v, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
      { name: 'Σ̂ off-diagonal', formula: F.sigOff, values: offs, summary: true, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_unbiased', note: 'unbiased; J(J−1)/2 pairs' },
    ];
    if (o.common) {
      steps.push({ name: 'common covariance', formula: F.common, values: [cbar], badge: 'proved', lean: 'Credibility.Model.commonCovHat_unbiased', note: 'unbiased when every off-diagonal covariance is the same c' });
    }
    steps.push(
      { name: 'ĉⱼ', formula: F.cj, values: c, badge: 'proved', lean: o.common ? 'Credibility.Model.cHatCommon_unbiased' : 'Credibility.Model.cHat_unbiased', note: o.common ? 'with the common ĉ: unbiased under a common covariance' : null },
      { name: 'τ̂²', formula: F.tau, values: [tauRaw], badge: 'proved', lean: o.common ? 'Credibility.Model.tauHatCommon_unbiased' : 'Credibility.Model.tauHat_unbiased', note: tauRaw <= 0 ? 'negative: truncated to 0 (eq. (40))' : null },
    );
    if (proj) steps.push(projStep(proj));
    const dampProved = psd && diagPos && theta < 1, sigK = proj ? 'Σ̂⁺' : 'Σ̂';
    steps.push(
      dist ? taperStep(rhoT, lags, psd && tau2 > 0, !!proj)
        : { name: 'damped K̂', formula: `${proj ? F.dampedP : F.damped};  θ = ${theta}`, values: [theta], badge: dampProved ? 'proved' : 'not proved yet', lean: dampProved ? 'Credibility.posDef_shrinkOffDiag' : null, gap: 'G2', note: (dampProved ? `${sigK} ⪰ 0 with a positive diagonal, so K̂ ≻ 0 for any θ < 1` : `${sigK} is not positive semidefinite with a positive diagonal: K̂ ≻ 0 checked numerically at θ = ${theta}, not by a theorem`) + `; θ̂ = ${thetaFit} by the plug-in rule S3 (${F.dampRule}): the plug-in of the table-optimal θ* = s²/(s² + V) (Damping.bestTheta_optimal); optimal for the rates not proved (G2)` },
    );
    if (o.common && tau2 > 0) {
      steps.push(
        { name: 'z', formula: F.zEq, values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_of_equalCov' },
        { name: 'b', formula: F.bOfZ, values: b, badge: 'proved', lean: 'Credibility.Core.b_eq_of_equalCov' },
      );
    } else {
      steps.push(
        { name: 'b', formula: F.gls, values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
        { name: 'z', formula: F.z26, values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
      );
    }
    steps.push({ name: 'rates', formula: F.rates, values: res.rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: `the parameters are plugged in: the formulas are optimal for the true K, τ²; off-balance ${(100 * offBal).toFixed(2)}%` });
    return { means: m, z, b, mu: res.mu, rates: res.rates, warnings, flags, K, theta, thetaFit, tauRaw, tau2, cbar, steps, rhoTaper: rhoT, rhoFit, lags };
  }

  /** The projection step of fitCorr (this draw): Σ̂⁺, the nearest PSD table (G2a). */
  function projStep(proj) {
    return {
      name: 'Σ̂⁺ (nearest PSD)', formula: F.psdProj, values: [proj.clipped, proj.moved], badge: 'proved',
      lean: 'Credibility.ConeProjection.existsUnique_proj_posSemidef',
      note: (proj.clipped ? `Σ̂ was not positive semidefinite: ${proj.clipped} eigenvalue(s) set to 0, Frobenius distance moved ${proj.moved.toPrecision(3)}` : 'Σ̂ is positive semidefinite: Σ̂⁺ = Σ̂') +
        '; never further from the true Σ than Σ̂ (Frobenius norm, every draw); biased, unlike Σ̂, so τ̂² and ĉⱼ use Σ̂',
    };
  }

  /** The taper step of fitCorr (this draw). `proved`: Σ̂(⁺) ⪰ 0 and τ̂² > 0, so Σ̂(⁺) + τ̂²I ≻ 0. */
  function taperStep(rho, lags, proved, projected) {
    const lagText = lags ? '; r̄_d by distance: ' + lags.slice(0, 4).map((g) => `d=${g.d}: ${g.r.toFixed(2)}`).join(', ') + (lags.length > 4 ? ', …' : '') : '';
    return {
      name: 'tapered K̂', formula: `${projected ? F.taperP : F.taper};  ρ̂ = ${rho}`, values: [rho], badge: proved ? 'proved' : 'not proved yet',
      lean: proved ? 'Credibility.posDef_distTaper_hadamard' : null, gap: 'G2',
      note: (proved ? `${projected ? 'Σ̂⁺' : 'Σ̂'} ⪰ 0 and τ̂² > 0, so K̂ ≻ 0 for every ρ ∈ [0, 1]` : `${projected ? 'Σ̂⁺' : 'Σ̂'} + τ̂²I is not positive definite: K̂ ≻ 0 checked numerically at ρ = ${rho}, not by a theorem`) +
        `; ρ̂ by the plug-in criterion (${F.taperRule}), the damping study’s rule S3 (studies/LOG.md)${lagText}`,
    };
  }

  /**
   * Coefficients (λ, μ) of the corrected Wⱼ = λ·W + μ·σ̂ⱼ⁴ for one region's volumes w (Finding 47,
   * VcW.integral_vcWCorr): E W, E σ̂⁴ and Var σ̂² are exact sums over the forms of uₜ − σ̂² and σ̂²,
   * linear in σ⁴ and in the fourth cumulant k when Var ξₜ = σ²/wₜ and κ₄(ξₜ) = k/wₜ² (noise of a
   * fixed shape); (λ, μ) match both parts, so λW + μσ̂⁴ is unbiased for Var σ̂² for every σ², k.
   * Equal volumes: λ = (T−1)³/(T(T−2)(T−3)), μ = −2/(T(T−3)) (VcW.integral_vcWCorr_equal). T ≤ 3
   * (no solution): λ matches the σ⁴ part only, μ = 0 (unbiased under normal noise, low under skew).
   */
  function vcWCoef(w) {
    const T = w.length, ws = sum(w), a = w.map((x) => x / ws), c = T / (T - 1);
    const D = (t, s) => (t === s ? 1 : 0) - a[s];
    const v1 = w.map((x) => 1 / x), k1 = w.map((x) => 1 / (x * x));
    const Ab = [];
    for (let s = 0; s < T; s++) { Ab.push([]); for (let r = 0; r < T; r++) { let z = 0; for (let t = 0; t < T; t++) z += w[t] * D(t, s) * D(t, r); Ab[s].push(z / (T - 1)); } }
    const parts = (G) => { // [σ⁴ part with the mean, its mean² part, k part]
      let m1 = 0, q = 0, kk = 0;
      for (let s = 0; s < T; s++) { m1 += G(s, s) * v1[s]; kk += k1[s] * G(s, s) ** 2; for (let r = 0; r < T; r++) q += G(s, r) ** 2 * v1[s] * v1[r]; }
      return { m2: m1 * m1, g: m1 * m1 + 2 * q, k: kk };
    };
    let EWs = 0, EWk = 0;
    for (let t = 0; t < T; t++) {
      const p = parts((s, r) => c * w[t] * D(t, s) * D(t, r) - Ab[s][r]);
      EWs += p.g / (T * (T - 1)); EWk += p.k / (T * (T - 1));
    }
    const sp = parts((s, r) => Ab[s][r]), Vs = sp.g - sp.m2, Vk = sp.k;
    const det = EWs * sp.k - EWk * sp.g;
    if (T >= 4 && Math.abs(det) > 1e-12 * Math.abs(EWs * sp.k)) return { lam: (Vs * sp.k - Vk * sp.g) / det, mu: (EWs * Vk - EWk * Vs) / det };
    return { lam: Vs / EWs, mu: 0 };
  }

  /**
   * Correlated Bühlmann–Straub with credibility-weighted variances
   * (studies/LOG.md, findings S15–S17 and the Ansatz; studies/runs/variance-credibility.js,
   * mode 'cred'). Every parameter by a moment equation, nothing to tune, no damping:
   *   σ̂ⱼ² = Qⱼⱼ/(T−1), σ̂² = mean of the σ̂ⱼ²,
   *   Wⱼ = estimated Var(σ̂ⱼ²) from the yearly terms, β² = between-region variance of the σⱼ²,
   *   σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂², ζⱼ = β²/(β² + Wⱼ)   (Bühlmann–Straub one level up),
   *   ρ̂ = Σᵢ<ⱼ Qᵢⱼ / Σᵢ<ⱼ σ̃ᵢσ̃ⱼ((T − 2) + Sᵢⱼ²/(wᵢ*wⱼ*)), clipped to [0, 1),
   *   Σ̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) (i ≠ j), σ̃ⱼ²/wⱼ* (i = j); τ̂² by eq. (39) on Σ̂, truncated at 0.
   * K̂ = Σ̂ + τ̂²I ≻ 0 by Model.K_posDef (the ρ-table 1 / ρ̂ is PSD for ρ̂ ∈ [0, 1)).
   */
  function vcEstimate(data, opts) {
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
    const own = Q.map((row, j) => row[j] / (T - 1));
    const W = own.map((sj, j) => {
      const u = data.X[j].map((x, t) => data.w[j][t] * (x - m[j]) ** 2 * T / (T - 1));
      const raw = sum(u.map((x) => (x - sj) ** 2)) / (T * (T - 1));
      // opts.corrW: the corrected Wⱼ, unbiased (Finding 47); off by default: it worsens the rates (S80).
      if (!(opts && opts.corrW)) return raw;
      const { lam, mu } = vcWCoef(data.w[j]);
      return Math.max(lam * raw + mu * sj * sj, 0);
    });
    // opts.perturb (skewBias, derivatives only): { own: [k, f] } scales σ̂ₖ² by f (and Wₖ by f², as scaling
    // region k's residuals would) without touching the cross-products; { q: x } shifts ρ̂'s numerator by x·(its denominator);
    // { tau: x } adds x to τ̂².
    const P = opts && opts.perturb;
    if (P && P.own) { own[P.own[0]] *= P.own[1]; W[P.own[0]] *= P.own[1] ** 2; }
    const pooled = sum(own) / J;
    const betweenRaw = sum(own.map((x) => (x - pooled) ** 2)) / (J - 1) - sum(W) / J;
    const between = Math.max(0, betweenRaw);
    // opts.pooled: one noise variance for all regions (ζⱼ = 0), the Finding 35 remedy.
    const zeta = W.map((Wj) => (between > 0 && !(opts && opts.pooled) ? between / (between + Wj) : 0));
    const s2raw = own.map((x, j) => zeta[j] * x + (1 - zeta[j]) * pooled);
    // opts.sigLevel (G1c, Finding 48, S81: not a default): rescale the σ̃ⱼ² to the σ̂ⱼ²'s average (VcW.sum_shrink_le_iff: it is low).
    const lev = opts && opts.sigLevel ? pooled / (sum(s2raw) / J) : 1;
    const s2 = s2raw.map((x) => x * lev);
    const sd = s2.map(Math.sqrt);
    // opts.rhoOwn (G1c, Finding 48, S81: not a default): ρ̂'s denominator from the own σ̂ⱼ instead of the σ̃ⱼ.
    const sdr = opts && opts.rhoOwn ? own.map(Math.sqrt) : sd;
    let qn = 0, qa = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { qn += Q[i][j]; qa += sdr[i] * sdr[j] * ((T - 2) + S[i][j] ** 2 / (wt[i] * wt[j])); }
    if (P && P.q) qn += P.q * qa;
    const rhoRaw = qn / qa, rho = Math.min(Math.max(rhoRaw, 0), 1 - 1e-9);
    const Sig = S.map((row, i) => row.map((x, j) => (i === j ? s2[i] / wt[i] : rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
    const tt = thesisTau(m, wt, Sig), tauRaw = tt.tau2 + (P && P.tau ? P.tau : 0);
    return { m, wt, S, own, pooled, W, betweenRaw, between, zeta, s2, qa, rhoRaw, rho, Sig, c: tt.c, tauRaw, t2: Math.max(tauRaw, 0) };
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

  function fitVC(data, opts) {
    const pooled = !!(opts && opts.pooled), p = vcEstimate(data, opts), { m, wt, S } = p, J = m.length;
    const { K, b, z, mu, rates } = vcBlend(p, wt, S, m);
    const offBal = sum(wt.map((x, j) => x * (m[j] - rates[j]))) / sum(wt.map((x, j) => x * m[j]));
    const flags = { tauNeg: p.tauRaw <= 0, zOver1: z.some((x) => x > 1), zNeg: z.some((x) => x < 0), bNeg: b.some((x) => x < 0), offBalance: Math.abs(offBal) > 0.01 };
    // Flags the optimum itself shows (studies/runs/vc-balance.js, studies/LOG.md findings S27–S29): with ρ̂ > 0
    // the true-K blend has negative b and z near 1 (so ẑ > 1 by noise); with ρ̂ > 0 or unequal σ̃ⱼ it is
    // balanced for the weights bⱼ/(1 − zⱼ), not for the exposures. These go to `notes`, not `warnings`.
    const expected = { zOver1: p.rho > 0, zNeg: false, bNeg: p.rho > 0, offBalance: p.rho > 0 || (!pooled && p.between > 0) };
    const why = p.rho > 0 ? 'expected under correlation' : 'expected with region-specific σⱼ';
    const msg = {
      tauNeg: 'τ̂² ≤ 0, set to 0 (eq. (40)): no credibility, every region gets the portfolio level μ̂',
      zOver1: `z > 1 for ${z.filter((x) => x > 1).length} region(s): the rate moves past the region's own mean, away from μ̂` +
        (expected.zOver1 ? '; the best z of a large region is close to 1 here, so the estimate can land above 1 (capping it at 1 changes nothing measurable)' : ''),
      zNeg: `z < 0 for ${z.filter((x) => x < 0).length} region(s): with the true parameters a negative z can be the best blend (Finding 17: past a singularity the gap μ̂ⱼ − μ̂ flips sign together with z, and the own-data weight cⱼ = bⱼ + zⱼ(1 − bⱼ) stays bounded), so clipping z to 0 is not the fix; in a fit it more likely means K̂ is nearly singular: look at ρ̂ and τ̂²`,
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
      { name: 'cohort means', formula: F.means, values: m, badge: 'proved', lean: 'Credibility.Model.a_special', note: 'aⱼₜ = wⱼₜ/wⱼ* (eq. (29))' },
      { name: 'σ̂ⱼ²', formula: F.vcSigma, values: p.own, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self', note: `pooled σ̂² = ${p.pooled.toPrecision(4)}` },
      ...(pooled ? [
        { name: 'σ̃ⱼ²', formula: F.vcPooled, values: p.s2, badge: 'not proved yet', gap: 'G1', note: 'one noise variance for all regions: a region with high draws does not get less weight for its high σ̂ⱼ² (Finding 35)' },
      ] : [
      { name: 'Wⱼ, β²', formula: F.vcW, values: [p.betweenRaw], badge: 'not proved yet', gap: 'G1', note: `β² (between-region variance of the σⱼ²)${p.betweenRaw <= 0 ? ': ≤ 0, set to 0, so every σ̃ⱼ² is the pooled σ̂²' : ''}; Wⱼ is low by a relative O(1/T) (Finding 47: 25% at T = 5, normal noise); kept, as the unbiased Wⱼ worsens the rates (S80)` },
      { name: 'σ̃ⱼ²', formula: F.vcTilde, values: p.s2, badge: 'not proved yet', gap: 'G1', note: 'credibility for the variances (the form of bs_z, with estimated fourth moments)' },
      ]),
      { name: 'ρ̂', formula: F.vcRho, values: [p.rhoRaw], badge: 'proved', lean: 'Credibility.Model.rhoPooled_unbiased', note: `one common correlation by a moment equation, E Qᵢⱼ = σᵢσⱼρ((T−2) + Sᵢⱼ²/(wᵢ*wⱼ*)); unbiased with the true σⱼ in the denominator, not with σ̃ⱼ plugged in (a ratio)${p.rhoRaw < 0 ? '; negative, set to 0' : p.rhoRaw >= 1 ? '; ≥ 1, set just below 1' : ''}` },
      { name: 'τ̂²', formula: F.vcTau, values: [p.tauRaw], badge: 'not proved yet', gap: 'G1', note: `on the common-ρ Σ̂: unbiased if Σ̂ is${p.tauRaw <= 0 ? '; negative: truncated to 0 (eq. (40))' : ''}` },
      { name: 'K̂', formula: F.vcK, values: [p.rho], badge: 'proved', lean: 'Credibility.Model.K_posDef', note: `K̂ ≻ 0 for any ρ̂ ∈ [0, 1): no damping, no θ; ρ̂ = ${p.rho.toFixed(3)}` },
      { name: 'b', formula: F.gls, values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
      { name: 'z', formula: F.z26, values: z, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
      { name: 'rates', formula: F.rates, values: rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: `the parameters are plugged in: the formulas are optimal for the true K, τ²; off-balance ${(100 * offBal).toFixed(2)}%` },
    ];
    return { means: m, z, b, mu, rates, warnings, notes, flags, expected, K, tauRaw: p.tauRaw, tau2: p.t2, rho: p.rho, rhoRaw: p.rhoRaw, sigma2: p.s2, between: p.between, theta: 1, steps };
  }

  /**
   * Plug-in best linear unbiased predictor (Finding 18) on corrBS's K̂ and τ̂²: each region's rate
   * Σᵢ d̂ᵢμ̂ᵢ with d̂ = blupWeight(K̂, τ̂², j), using every other region individually rather than
   * through μ̂. Optimal for the true K (Core.blupWeight_optimal); whether it survives estimating
   * every K̂ᵢⱼ is what the app shows. `c` holds the own-data weights d̂ⱼⱼ; `levelMSE` the plug-in MSE.
   */
  function fitBLUP(data, opts) {
    return blupOn(fitVC(data, opts));
  }

  /**
   * The plug-in BLUP on the thesis's full K̂ tapered by ρ̂^|i−j| (fitCorr with taper 'distance'):
   * for ordered regions with many pairs (studies/runs/taper-blup.js, studies/LOG.md S36–S37).
   */
  function fitBLUPTaper(data) {
    const base = fitCorr(data, { taper: 'distance' });
    return Object.assign(blupOn(base), { rhoTaper: base.rhoTaper, rhoFit: base.rhoFit });
  }

  /** The BLUP's rates, weights and plug-in level MSE on a fitted base's K̂ and τ̂² (Core.blupWeight_optimal). */
  function blupOn(base) {
    const { K, tau2, means: m, b } = base, J = m.length;
    const D = m.map((_, j) => blupWeight(K, tau2, j));
    const rates = D.map((d) => sum(d.map((x, i) => x * m[i])));
    const c = D.map((d, j) => d[j]);
    const levelMSE = D.map((d, j) => linMse(K, tau2, j, d));
    const negOther = D.filter((d, j) => d.some((x, i) => i !== j && x < 0)).length;
    const warnings = base.flags.tauNeg ? [base.warnings.find((w) => w.startsWith('τ̂²')) || 'τ̂² ≤ 0, set to 0: every region gets the portfolio level'] : [];
    const steps = base.steps.filter((s) => !['b', 'z', 'rates'].includes(s.name)).concat([
      { name: 'b', formula: F.gls, values: b, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
      { name: 'BLUP weights', formula: F.blupD, values: c, badge: 'proved', lean: 'Credibility.Core.blupWeight_optimal', note: `the weights sum to 1 and use every region individually; ${negOther} region(s) give some other region a negative weight` },
      { name: 'rates', formula: F.blupRates, values: rates, badge: 'proved', lean: 'Credibility.Core.Estimates.blup_mse_optimal', note: 'the parameters are plugged in: optimal among all unbiased linear predictors for the true K, τ²' },
    ]);
    return { means: m, z: null, b, c, weights: D, mu: base.mu, rates, warnings, notes: [], flags: { tauNeg: base.flags.tauNeg }, K, tau2, rho: base.rho, theta: base.rhoTaper == null ? 1 : null, levelMSE, steps };
  }

  /**
   * Balance a fit on exposures (the page's "Balance the total premium" switch, Finding 35): every
   * rate + D with D = Σᵢ wᵢ*(μ̂ᵢ − rateᵢ)/w**, so Σⱼ wⱼ* rateⱼ = Σⱼ wⱼ* μ̂ⱼ in every draw and the
   * portfolio level is unbiased in every world (Core.Estimates.integral_portfolio_sub_of_balanced).
   * For rates linear in μ̂ (weightsOf) the shifted weights d̂ⱼ' = d̂ⱼ + (w − Σₖ wₖ* d̂⁽ᵏ⁾)/w** still sum
   * to 1, so the plug-in MSE stays exact on K̂. The common shift is the best balanced correction when
   * cov(rateⱼ − μⱼ, D) is the same for every region (Core.commonShift_optimal).
   */
  /**
   * The cross-fitted portfolio level (Finding 35, S63): for each year s, the pooled BLUP's weights from
   * corrBS's parameters fitted without year s (ρ̂, σ̂² from residuals, τ̂² from the other years' means),
   * on the full design; their exposure-weighted row c̄⁽ˢ⁾ applied to year s's cells, summed with the year
   * shares πₛ. With year shares common to the regions its bias is the level channel Σₛ πₛ Σᵢ cov(c̄ᵢ⁽ˢ⁾, μᵢ)
   * only, any distribution (Core.Estimates.integral_crossFit_sub), 0 when the weights are uncorrelated
   * with the levels (integral_crossFit_sub_eq_zero). The year shares πₛ are the portfolio's, common to the
   * regions, so this holds for any volumes (one shape is not needed); null when T < 3. `cbar` is Σₛ πₛ c̄⁽ˢ⁾
   * (sums to 1), for the first-order weights; `cs` the c̄⁽ˢ⁾, for the exact cell pricing (balanceAuto).
   */
  const cfCache = new WeakMap();
  function crossFitLevel(data) {
    if (cfCache.has(data)) return cfCache.get(data);
    const J = data.X.length, T = data.X[0].length, wt = data.w.map(sum), wall = sum(wt);
    const pi = Array.from({ length: T }, (_, t) => sum(data.w.map((row) => row[t])) / wall);
    let res = null;
    if (T >= 3) {
      const S = data.w.map((ri) => data.w.map((rj) => sum(ri.map((x, t) => Math.sqrt(x * rj[t])))));
      let level = 0; const cbar = new Array(J).fill(0), cs = [];
      for (let s = 0; s < T; s++) {
        const sub = { w: data.w.map((row) => row.filter((_, t) => t !== s)), X: data.X.map((row) => row.filter((_, t) => t !== s)) };
        const p = vcEstimate(sub, { pooled: true }), sd = p.s2.map(Math.sqrt);
        const K = S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / wt[i] + p.t2 : p.rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
        const c = new Array(J).fill(0);
        for (let j = 0; j < J; j++) blupWeight(K, p.t2, j).forEach((x, i) => { c[i] += wt[j] / wall * x; });
        level += pi[s] * sum(c.map((x, i) => x * data.X[i][s]));
        c.forEach((x, i) => { cbar[i] += pi[s] * x; });
        cs.push(c);
      }
      res = { level, cbar, pi, cs };
    }
    cfCache.set(data, res);
    return res;
  }

  /**
   * opts.target 'crossFit' (the page's switch since 2026-11-27, owner's decision on S63): shift to the
   * cross-fitted level L̂cf instead of the exposures; falls back to exposure balance when crossFitLevel is
   * null. Then the portfolio level is L̂cf in every draw, so its bias is the cross-fit's level channel
   * whatever the fit. The weights shown are first order (c̄ in place of the year-specific c̄⁽ˢ⁾).
   */
  function balanceFit(f, data, opts) {
    const { wt, m } = cohortMeans(data), wall = sum(wt);
    const cf = opts && opts.target === 'crossFit' ? crossFitLevel(data) : null;
    const D = cf ? cf.level - sum(wt.map((x, j) => x * f.rates[j])) / wall : sum(wt.map((x, j) => x * (m[j] - f.rates[j]))) / wall;
    const out = Object.assign({}, f, { rates: f.rates.map((x) => x + D), shift: D, balanced: true, balanceTarget: cf ? 'crossFit' : 'exposure' });
    const W = weightsOf(f);
    if (W) {
      const g = wt.map((x, i) => ((cf ? cf.cbar[i] * wall : x) - sum(W.map((d, k) => wt[k] * d[i]))) / wall);
      out.weights = W.map((d) => d.map((x, i) => x + g[i]));
      out.c = out.weights.map((d, j) => d[j]);
      if (f.K) out.levelMSE = out.weights.map((d, j) => linMse(f.K, f.tau2, j, d));
    }
    const off = (t) => !/off-balance/.test(t);
    out.flags = Object.assign({}, f.flags, { offBalance: false });
    out.warnings = (f.warnings || []).filter(off);
    out.notes = (f.notes || []).filter(off);
    if (cf) out.weightsApprox = true;
    const st = cf ? BALANCE_CF_STEP : BALANCE_STEP, fb = opts && opts.target === 'crossFit' && !cf ? 'cross-fitted level not available (T < 3): exposure balance instead; ' : '';
    out.steps = (f.steps || []).concat([Object.assign({}, st, { values: [D], note: `D = ${D >= 0 ? '+' : '−'}${(100 * Math.abs(D)).toFixed(2)}% of the tariff; ` + fb + st.note })]);
    return out;
  }

  /**
   * The balance switch by its plug-in cost (owner, 2026-11-27; Finding 46, studies S76): shift to the
   * cross-fitted level only when that level is the better estimate of the portfolio level on the fitted
   * moments. The cost of a common shift is exactly E(T − μ̄)² − E(r̄ − μ̄)² (BalanceCost.integral_sum_sq_shift);
   * for fixed weights it is m(g_T) − m(g_r̄) on the yearly cells (BalanceCost.balance_cost_cellLin, any volumes; on one
   * shape the fit's own term is mse(c) on K̂), on K̂ and L̂ (τ̂²I, or the fit's L for group levels), the cross-fit's
   * per-year weights c̄⁽ˢ⁾ held fixed (S82). S76: regret at most 6.9 points of the floor
   * (always on: 205.6). `errTarget`, `errFit`: the plug-in typical errors √mse of the two estimates of the
   * portfolio level (on K̂ both read low, about ×0.7 in S76's app worlds, their difference much less). The readout: D = L̂cf − Σⱼ uⱼ rateⱼ, the raw fit's gap to the cross-fitted level
   * (which is unbiased when the weights are blind to the levels, Core.Estimates.integral_crossFit_sub_eq_zero),
   * so −D estimates the raw fit's portfolio bias; its SE from K̂, √((c̄ − c)ᵀK̂(c̄ − c)) (first order, fixed
   * weights). Falls back to balanceFit(…, crossFit) when the fit has no linear weights or K̂, or the
   * cross-fitted level is not available (then exposure balance, as balanceFit).
   */
  function balanceAuto(f, data) {
    const cf = crossFitLevel(data), W = weightsOf(f);
    if (!W || !f.K || !(f.tau2 >= 0)) {
      const b = balanceFit(f, data, { target: 'crossFit' });
      return Object.assign(b, { balanceAuto: { on: true, available: false } });
    }
    const { wt, m } = cohortMeans(data), wall = sum(wt), u = wt.map((x) => x / wall), J = u.length, K = f.K;
    // The target: the cross-fitted level (crossFitLevel, any volumes, T ≥ 3), priced on the yearly cells; else
    // the exposure-weighted level uᵀμ̂, priced on K̂ (balance_cost_portLin).
    const tgt = cf ? { a: cf.cbar, level: cf.level, name: 'cross-fitted level', opts: { target: 'crossFit' } }
      : { a: u, level: sum(m.map((x, j) => u[j] * x)), name: 'exposure-weighted level', opts: { target: 'exposure' } };
    const L = f.L || K.map((row, i) => row.map((_, k) => (i === k ? f.tau2 : 0)));
    const Ltu = u.map((_, i) => sum(u.map((x, j) => x * L[j][i]))), uLu = sum(u.map((x, i) => x * Ltu[i]));
    const quad = (d) => { let q = 0; for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += d[i] * K[i][k] * d[k]; return q; };
    const mse = (d) => quad(d) - 2 * sum(d.map((x, i) => x * Ltu[i])) + uLu;
    const c = new Array(J).fill(0);
    W.forEach((d, j) => d.forEach((x, i) => { c[i] += u[j] * x; }));
    // With the cross-fitted level: price both estimates of μ̄ on the yearly cells (BalanceCost.balance_cost_cellLin,
    // any volumes): target gₛ = πₛc̄⁽ˢ⁾, the fit's r̄ gₛᵢ = cᵢaᵢₛ (aᵢₛ = wᵢₛ/wᵢ*); m(g) = (G − u)ᵀL̂(G − u) + Σₛ gₛᵀD̂ₛgₛ with the
    // cells' noise D̂ₛᵢₖ = Cᵢₖ/√(wᵢₛwₖₛ), Cᵢₖ = (K̂ − L̂)ᵢₖ wᵢ*wₖ*/Sᵢₖ (so Σₛ aᵢₛaₖₛD̂ₛᵢₖ = (K̂ − L̂)ᵢₖ: on one shape this is mse on K̂).
    let mc, cost, seD;
    if (cf) {
      const T = data.w[0].length, Sx = data.w.map((ri) => data.w.map((rj) => sum(ri.map((x, t) => Math.sqrt(x * rj[t])))));
      const C = K.map((row, i) => row.map((x, k) => (x - L[i][k]) * wt[i] * wt[k] / Sx[i][k]));
      const cellQuad = (G, g) => {   // GᵀL̂G + Σₛ gₛᵀD̂ₛgₛ
        let q = 0;
        for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += G[i] * L[i][k] * G[k];
        for (let t = 0; t < T; t++) for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += g[t][i] * g[t][k] * C[i][k] / Math.sqrt(data.w[i][t] * data.w[k][t]);
        return q;
      };
      const tot = (g) => u.map((_, i) => sum(g.map((gs) => gs[i])));
      const gT = cf.cs.map((cs, t) => cs.map((x) => cf.pi[t] * x));
      const gR = Array.from({ length: T }, (_, t) => c.map((x, i) => x * data.w[i][t] / wt[i]));
      const mCell = (g) => cellQuad(tot(g).map((x, i) => x - u[i]), g);
      mc = mCell(gR); cost = mCell(gT) - mc;
      const gd = gT.map((gs, t) => gs.map((x, i) => x - gR[t][i]));
      seD = Math.sqrt(Math.max(cellQuad(tot(gd), gd), 0));
    } else {
      mc = mse(c); cost = mse(u) - mc; seD = Math.sqrt(Math.max(quad(u.map((x, i) => x - c[i])), 0));
    }
    const D = tgt.level - sum(f.rates.map((x, j) => u[j] * x));
    const fitMse = sum(W.map((d, j) => u[j] * linMseL(K, L, j, d)));
    const on = cost < -1e-9 * Math.max(mc, 1e-300), rel = fitMse > 0 ? cost / fitMse : 0;   // a tie (c = a, e.g. a blend balanced on exposures by construction) is left as fitted
    const info = { on, available: true, target: cf ? 'crossFit' : 'exposure', cost, rel, D, seD, portMse: mc };
    const pc = (x) => `${x >= 0 ? '+' : '−'}${(100 * Math.abs(x)).toFixed(2)}%`, rt = (x) => `${(100 * Math.sqrt(Math.max(x, 0))).toFixed(2)}%`;
    info.errTarget = Math.sqrt(Math.max(mc + cost, 0)); info.errFit = Math.sqrt(Math.max(mc, 0));
    const note = `typical error for the portfolio level on K̂: ${tgt.name} ${rt(mc + cost)}, the fit's own ${rt(mc)} of the tariff, so ${on ? `balanced (the ${tgt.name} is the better estimate)` : 'left unbalanced (its own level is the better estimate)'}; `
      + (cf ? '' : 'no cross-fitted level (fewer than 3 years); ')
      + `bias readout: the unbalanced rates sit ${(100 * Math.abs(D)).toFixed(2)}% ${D > 0 ? 'below' : 'above'} the ${tgt.name}, ± ${(200 * seD).toFixed(2)}% (2 SE), `
      + `an estimate of the raw portfolio's ${D > 0 ? 'under' : 'over'}-pricing${on ? ' (removed by the shift)' : ' (kept: removing it would add more error than it saves)'}. Studies S76: regret at most 6.9 points of the floor against 205.6 for always balancing`;
    const base = on ? balanceFit(f, data, tgt.opts) : Object.assign({}, f);
    const step = Object.assign({}, BALANCE_AUTO_STEP, { values: [rel, D], note: note + '. ' + BALANCE_AUTO_STEP.note });
    const steps = (on ? base.steps.slice(0, -1) : (f.steps || [])).concat([step]);
    return Object.assign(base, { steps, balanceAuto: info });
  }

  /** The BLUP on corrBS's K̂, balanced (kept for the tests; on the page it is BLUP with the switch on). */
  function fitBLUPBal(data) { return balanceFit(fitBLUP(data), data); }

  /** opts.balance: true (exposures), 'crossFit' or 'auto' (balanceAuto). */
  const applyBal = (f, data, opts) => (opts && opts.balance === 'auto' ? balanceAuto(f, data) : balanceFit(f, data, balOpts(opts)));
  /** opts.balance: true (exposures) or 'crossFit' → balanceFit's target. */
  const balOpts = (opts) => ({ target: opts && opts.balance === 'crossFit' ? 'crossFit' : 'exposure' });
  /**
   * A model's fit, balanced when opts.balance. Models already balanced on exposures (BS, own, pool) are
   * left alone under either target: their portfolio level is unbiased in every world already.
   */
  const needsBal = (id, opts) => !!(opts && opts.balance) && !MODELS[id].balanced;
  function fitWith(id, data, opts) {
    const f = MODELS[id].fit(data);
    return needsBal(id, opts) ? applyBal(f, data, opts) : f;
  }

  /**
   * Jackknife MSEP of the variance-credibility fit (Jiang, Lahiri & Wan 2002, Ann. Stat. 30;
   * studies/runs/msep.js), deleting one year at a time (independent years), region means kept:
   *   MSEPⱼ = g₁₂ⱼ(θ̂) − (T−1)/T Σₜ (g₁₂ⱼ(θ̂₋ₜ) − g₁₂ⱼ(θ̂)) + (T−1)/T Σₜ (rateⱼ(θ̂₋ₜ) − rateⱼ(θ̂))².
   * An average-case error over data sets like this one, not an interval for this data set
   * (studies/LOG.md, findings S19 and S26). Data only, no tuning.
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
    bs: { name: 'Bühlmann–Straub', short: 'BS', fit: fitBS, ready: true, balanced: true },
    vc: { name: 'Correlated BS, credibility-weighted variances (recommended)', short: 'corrBS', fit: (data) => fitVC(data), ready: true, msep: jackknifeMSEP },
    blup: { name: 'Best linear predictor on corrBS’s K̂ (plug-in BLUP)', short: 'BLUP', fit: (data) => fitBLUP(data), ready: true },
    blupPool: { name: 'BLUP, one pooled noise variance (no under-pricing by skew)', short: 'BLUP pooled', fit: (data) => fitBLUP(data, { pooled: true }), ready: true },
    blupT: { name: 'BLUP on the full K̂ tapered by ρ̂^|i−j| (ordered regions, many of them)', short: 'BLUP taper', fit: (data) => fitBLUPTaper(data), ready: true },
    blupA: { name: 'BLUP, tapered only when the data show the correlation falling with distance (ordered regions)', short: 'BLUP auto', fit: (data) => fitBLUPAuto(data), ready: true },
    vcGP: { name: 'Correlated BS, variances chosen by gain against price', short: 'corrBS g/p', fit: (data) => fitVCGP(data), ready: true },
    corr: { name: 'Thesis model with correlation (full K̂, damped)', short: 'corr', fit: (data) => fitCorr(data), ready: true },
    corrT: { name: 'Thesis model with correlation, distance taper ρ̂^|i−j| (ordered regions)', short: 'corr taper', fit: (data) => fitCorr(data, { taper: 'distance' }), ready: true },
    corrC: { name: 'One common covariance — not recommended (unequal volumes)', short: 'common', fit: (data) => fitCorr(data, { common: true }), ready: true, notRecommended: 'finding S4: with unequal volumes one common covariance exceeds the large regions’ noise variance and z explodes' },
    own: { name: 'Own mean only (z = 1)', short: 'own', fit: fitOwn, ready: true, balanced: true },
    pool: { name: 'One tariff for all (z = 0)', short: 'pool', fit: fitPool, ready: true, balanced: true },
    grp: { name: 'BLUP with group levels, groups or none chosen on held-out years', short: 'BLUP groups', fit: (data) => fitGroups(data), ready: true },
  };

  /**
   * Notation for the recipes. `match` decides whether a recipe needs the entry (it is listed
   * only if some step's formula or rule contains it); `always` entries are always listed.
   */
  const NOTATION = [
    { sym: 'Xⱼₜ, wⱼₜ', text: 'the data: observed ratio (claim cost per vehicle-year ÷ tariff) and volume (vehicle-years) of region j = 1…J in year t = 1…T', always: true },
    { sym: 'wⱼ*, w**', text: 'wⱼ* = Σₜ wⱼₜ, the region’s total volume; w** = Σⱼ wⱼ*, the portfolio’s', always: true },
    { sym: 'μ̄', text: 'μ̄ = Σⱼ wⱼ* μ̂ⱼ / w**, the volume-weighted mean of the region means', match: 'μ̄' },
    { sym: 'Sᵢⱼ', text: 'Sᵢⱼ = Σₜ √(wᵢₜwⱼₜ) (so Sⱼⱼ = wⱼ*)', match: 'Sᵢⱼ' },
    { sym: 'Qᵢⱼ', text: 'Qᵢⱼ = Σₜ √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ), the weighted cross-products of the deviations', match: 'Q' },
    { sym: 'Σ̂ᵢⱼ, v̂ⱼ', text: 'Σ̂ᵢⱼ: the estimated noise covariance of μ̂ᵢ and μ̂ⱼ (the table built in the steps above); v̂ⱼ = Σ̂ⱼⱼ', match: 'Σ̂' },
    { sym: 'δᵢⱼ', text: 'δᵢⱼ = 1 if i = j, else 0', match: 'δᵢⱼ' },
    { sym: '1, eⱼ, K̂⁻¹', text: '1: the vector of ones; eⱼ: the j-th unit vector; K̂⁻¹v: the solution x of K̂x = v (a linear solve, e.g. Cholesky)', match: 'K̂⁻¹' },
    { sym: 'z*', text: 'z* = Σⱼ zⱼ', match: 'z*' },
    { sym: 'τ̂²⁺', text: 'τ̂²⁺ = max(τ̂², 0)', match: 'τ̂²⁺' },
    { sym: 'wⱼ,next', text: 'next year’s volume of region j', match: 'wⱼ,next' },
  ];

  /** The plug-in level MSE of a blend, used by the premium step (blendMSE). */
  const BLEND_MSE = 'MSEⱼ = zⱼ²Aⱼ + (1 − zⱼ)²Bⱼ + 2zⱼ(1 − zⱼ)Cⱼ with Aⱼ = K̂ⱼⱼ − τ̂², Bⱼ = s² − 2bⱼτ̂² + τ̂², Cⱼ = s² − bⱼτ̂², s² = 1/1ᵀK̂⁻¹1';
  const premiumStep = (mse) => ({
    name: 'premium', formula: F.premium, badge: 'proved', lean: 'Credibility.Core.Estimates.mse_forecast',
    rule: `σ̂ⱼ² = (K̂ⱼⱼ − τ̂²)·wⱼ*, the noise of one vehicle-year; ${mse}`,
    note: 'the premium is the rate (the same z is optimal for next year); the error is an average over data sets like this one, not an interval',
  });
  const TAU_ZERO = 'if τ̂² ≤ 0, use τ̂² = 0 from here on (eq. (40)): then z = 0 and every region gets the portfolio level μ̂';

  /**
   * The recipe of each model (the page's Recipe section): the fit's steps with formulas and the
   * rules the code applies (truncations, the choice of θ), without numbers, so the model can be
   * applied outside the app. Names, formulas and badges must match MODELS[id].fit's steps (tested).
   */
  const RECIPES = {
    bs: {
      intro: 'Bühlmann–Straub: regions uncorrelated, one common noise variance σ².',
      steps: [
        { name: 'cohort means', formula: F.means, badge: 'proved', lean: 'Credibility.bs_a' },
        { name: 'σ̂²', formula: F.bsSigma, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
        { name: 'τ̂²', formula: F.bsTau, badge: 'proved', lean: 'Credibility.Model.tauHatBS_unbiased', rule: 'if τ̂² ≤ 0, set τ̂² = 0: then z = 0 and b = wⱼ*/w**, every region gets μ̄', note: 'unbiased when the regions are uncorrelated with a common σ' },
        { name: 'z', formula: F.bsZ, badge: 'proved', lean: 'Credibility.bs_z' },
        { name: 'b', formula: F.bOfZ, badge: 'proved', lean: 'Credibility.bs_b' },
        { name: 'rates', formula: F.rates, badge: 'proved', lean: 'Credibility.bs_balance', note: 'balanced: Σⱼ wⱼ* μ̂ⱼᵇ = Σⱼ wⱼ* μ̂ⱼ' },
        premiumStep(`K̂ is diagonal with K̂ⱼⱼ = σ̂²/wⱼ* + τ̂²; ${BLEND_MSE}`),
      ],
    },
    vc: {
      intro: 'Correlated Bühlmann–Straub: one correlation ρ between regions within a year, region variances shrunk towards the pooled one by their own credibility. Nothing to tune.',
      steps: [
        { name: 'cohort means', formula: F.means, badge: 'proved', lean: 'Credibility.Model.a_special' },
        { name: 'σ̂ⱼ²', formula: F.vcSigma, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
        { name: 'Wⱼ, β²', formula: F.vcW, badge: 'not proved yet', gap: 'G1', rule: 'if β² ≤ 0, set β² = 0 (then every σ̃ⱼ² below is the pooled σ̂²)', note: 'Wⱼ estimates Var(σ̂ⱼ²) from the yearly terms, low by a relative O(1/T) (Finding 47; the unbiased one worsens the rates, S80); β² is the between-region variance of the σⱼ²' },
        { name: 'σ̃ⱼ²', formula: F.vcTilde, badge: 'not proved yet', gap: 'G1', rule: 'ζⱼ = 0 when β² = 0' },
        { name: 'ρ̂', formula: F.vcRho, badge: 'proved', lean: 'Credibility.Model.rhoPooled_unbiased', rule: 'clip ρ̂ to [0, 1) (a value ≥ 1 is set just below 1)', note: 'unbiased for a common ρ with the true σⱼ in the denominator; with σ̃ⱼ plugged in it is biased up when the σⱼ differ, since the σ̃ⱼ² average below the σ̂ⱼ² (Finding 48); K̂’s off-diagonal does not see that level' },
        { name: 'τ̂²', formula: F.vcTau, badge: 'not proved yet', gap: 'G1', rule: `Σ̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) for i ≠ j and σ̃ⱼ²/wⱼ* for i = j; ${TAU_ZERO}` },
        { name: 'K̂', formula: F.vcK, badge: 'proved', lean: 'Credibility.Model.K_posDef', note: 'positive definite for any ρ̂ in [0, 1): no damping needed' },
        { name: 'b', formula: F.gls, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
        { name: 'z', formula: F.z26, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
        { name: 'rates', formula: F.rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: 'optimal for the true K and τ²; with estimates plugged in, not exactly balanced' },
        premiumStep('MSEⱼ by the jackknife over years: MSEⱼ = gⱼ − (T−1)/T Σₜ (gⱼ,₋ₜ − gⱼ) + (T−1)/T Σₜ (rateⱼ,₋ₜ − rateⱼ)², where gⱼ = ' +
          BLEND_MSE.replace('MSEⱼ = ', '') + ', and “−t” means: redo steps 1–6 on the data without year t (its own region means included) to get σ̃ⱼ², ρ̂, τ̂²; then build K̂, b, z with the full-data wⱼ*, Sᵢⱼ and apply them to the full-data μ̂ⱼ; set MSEⱼ to 0 if negative'),
      ],
    },
    blup: {
      intro: 'Best linear unbiased predictor on corrBS’s K̂ and τ̂²: each region’s rate uses every other region individually, not only through μ̂.',
      steps: null,   // corrBS's steps up to K̂, then these (filled below)
      tail: [
        { name: 'b', formula: F.gls, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
        { name: 'BLUP weights', formula: F.blupD, badge: 'proved', lean: 'Credibility.Core.blupWeight_optimal', note: 'for each region j a weight vector d̂ over all regions, summing to 1' },
        { name: 'rates', formula: F.blupRates, badge: 'proved', lean: 'Credibility.Core.Estimates.blup_mse_optimal' },
        premiumStep('MSEⱼ = d̂ᵀK̂d̂ − 2τ̂²d̂ⱼ + τ̂², with d̂ region j’s BLUP weights'),
      ],
    },
    corr: {
      intro: 'The thesis model with correlation: the estimators (37)–(41) for every pair of regions, then a damped K̂.',
      steps: null,   // filled below (corrSteps)
    },
    corrT: {
      intro: 'The thesis model with correlation, for regions with an order (age bands, neighbours): the estimators (37)–(41) for every pair, then K̂ tapered by ρ̂^|i−j| instead of damped, so far-apart pairs are shrunk more than neighbours. ρ̂ from the data by the damping study’s plug-in criterion (rule S3).',
      steps: null,
    },
    corrC: {
      intro: 'One common covariance for all pairs of regions. Not recommended with unequal volumes (its z can explode).',
      steps: null,
    },
    own: {
      intro: 'Each region on its own data: z = 1.',
      steps: [{ name: 'rates', formula: 'rateⱼ = μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', badge: 'proved', lean: 'Credibility.bs_a' }],
    },
    pool: {
      intro: 'One tariff for all: z = 0.',
      steps: [{ name: 'rates', formula: 'rateⱼ = μ̄ for every region, μ̂ⱼ = Σₜ wⱼₜ Xⱼₜ / wⱼ*', badge: 'proved', lean: 'Credibility.bs_a' }],
    },
  };
  RECIPES.blup.steps = RECIPES.vc.steps.filter((s) => !['b', 'z', 'rates', 'premium'].includes(s.name)).concat(RECIPES.blup.tail);
  const BLUP_TAIL = RECIPES.blup.tail;
  delete RECIPES.blup.tail;
  RECIPES.blupPool = {
    intro: 'The plug-in BLUP with one pooled noise variance σ̂² for all regions instead of corrBS’s credibility-weighted σ̃ⱼ². Under skewed claims the region-specific variances make the premium too low on average (Finding 35); the pooled one does not.',
    steps: RECIPES.blup.steps.filter((s) => s.name !== 'Wⱼ, β²').map((s) => (s.name === 'σ̃ⱼ²'
      ? { name: 'σ̃ⱼ²', formula: F.vcPooled, badge: 'not proved yet', gap: 'G1', note: 'one noise variance: no region gets less weight for its own high σ̂ⱼ²' } : s)),
  };
  /** The balance step the switch appends (any model not already balanced). */
  const BALANCE_STEP = { name: 'balance', formula: F.balance, badge: 'proved', lean: 'Credibility.Core.Estimates.integral_portfolio_sub_of_balanced', note: 'balanced: Σⱼ wⱼ* rateⱼ = Σⱼ wⱼ* μ̂ⱼ in every draw, so the portfolio level is unbiased in every world (Finding 35); with skewed claims the unbalanced rates are too low on average. The best balanced correction by a common term when cov(rateⱼ − μⱼ, D) is equal for all regions (Core.commonShift_optimal); under strong correlation it costs accuracy' };

  const BALANCE_AUTO_STEP = { name: 'balance (auto)', formula: F.balanceAuto, badge: 'proved', lean: 'Credibility.balance_cost_cellLin', note: 'a common shift trades the fit\'s portfolio level for the target\'s: it changes the exposure-weighted MSE by exactly E(T − μ̄)² − E(r̄ − μ̄)², any distribution (BalanceCost.integral_sum_sq_shift); for fixed weights in closed form on the yearly cells, any volumes (balance_cost_cellLin), applied on the fitted K̂ (plug-in, first order, the bias of the raw fit not counted). With unequal noise variances the cross-fitted level is usually the worse estimate (Finding 46)' };

  /** The cross-fitted balance step (the switch's target since 2026-11-27). */
  const BALANCE_CF_STEP = { name: 'balance', formula: F.balanceCf, badge: 'proved', lean: 'Credibility.Core.Estimates.integral_crossFit_sub_eq_zero', note: 'one common shift to the cross-fitted portfolio level: each year priced with weights fitted without it, so its noise cannot steer its own weight (Finding 35). With year shares common to the regions the level\'s bias is only the levels\' channel, any distribution (Core.Estimates.integral_crossFit_sub), 0 when the weights are uncorrelated with the levels (ρ̂, σ̂² from residuals); τ̂² from the means keeps a small part. Studies S63: unbiased in ten worlds, at most 1 MSE point dearer than exposure balance without correlation and 2–46 points cheaper under ρ = 0.6. Not balanced on exposures; plug-in MSE first order (year weights averaged)' };

  {
    const shared = RECIPES.vc.steps.filter((x) => ['cohort means', 'σ̂ⱼ²', 'Wⱼ, β²', 'σ̃ⱼ²', 'ρ̂'].includes(x.name));
    const none = RECIPES.blup.steps.filter((x) => ['τ̂²', 'K̂'].includes(x.name)).concat(BLUP_TAIL.filter((x) => x.name !== 'premium')).map((x) => Object.assign({}, x, { branch: 'none' }));
    const g = (name, formula, lean, note) => Object.assign({ name, formula, badge: 'proved', lean, branch: 'groups' }, note ? { note } : {});
    RECIPES.grp = {
      intro: 'Regions in groups (countries) share a level. The variance is split into the shared part φτ² and the regional part λ = (1 − φ)τ², from pairs of regions within and across groups, and every region is priced by the BLUP with that level table; whether groups pay is decided on held-out years (lowest regret of the rules tried, at most 4 points of the floor, though one portfolio’s score is noisy). Nothing to tune (studies S69, S77).',
      branches: { groups: 'the held-out score is smaller with groups', none: 'the held-out score is not smaller with groups' },
      steps: shared.concat([
        g('pairs P̂ᵢⱼ', F.grpPairs, 'Credibility.Model.pairHat_unbiasedG', 'the noise estimates of eq. (39), unbiased for any correlation; Σ̂ᵢⱼ = ρ̂σ̃ᵢσ̃ⱼSᵢⱼ/(wᵢ*wⱼ*) for i ≠ j and σ̃ⱼ²/wⱼ* for i = j (corrBS’s noise table) builds V̂ and K̂'),
        g('first pass', F.grpFirst, 'Credibility.Model.phiTauPooled_unbiasedG', 'unbiased for any weights summing to one on each side'),
        g('λ̂, φτ²^', F.grpGLS, 'Credibility.Model.phiTauPool_blue_optimal', 'least variance for the true V; V̂ from the first pass under normal formulas, Dₚ = μ̂ᵢ − μ̂ⱼ, N̂ₚ = Σ̂ᵢᵢ + Σ̂ⱼⱼ − 2Σ̂ᵢⱼ; ĉ the covariance on K̂₀ = Σ̂ + L̂₀'),
        g('K̂ (groups)', F.grpK, 'Credibility.Unequal.KG_posDef'),
        g('b (groups)', F.gls, 'Credibility.glsWeight_optimal'),
        g('BLUP weights (groups)', F.grpBlupD, 'Credibility.Core.blup_optimal'),
        g('rates (groups)', F.blupRates, 'Credibility.Core.blup_optimal'),
      ], none, [
        { name: 'groups or none', formula: F.grpChoice, badge: 'proved', lean: 'Credibility.CrossFit.integral_heldOutScore_sub', note: 'the difference of the held-out scores is unbiased for the difference of the true errors (rules fitted without year s), any distribution' },
        premiumStep('MSEⱼ = d̂ᵀK̂d̂ − 2d̂ᵀℓⱼ + L̂ⱼⱼ (groups) or d̂ᵀK̂d̂ − 2τ̂²d̂ⱼ + τ̂² (none), with d̂ region j’s BLUP weights'),
      ]),
    };
  }

  /** A recipe's steps, with the balance step before the premium when opts.balance. */
  function recipeSteps(id, opts) {
    const br = opts && opts.branch, st = br ? RECIPES[id].steps.filter((x) => !x.branch || x.branch === br) : RECIPES[id].steps;
    if (!needsBal(id, opts)) return st;
    const B = opts.balance === 'auto' ? BALANCE_AUTO_STEP : opts.balance === 'crossFit' ? BALANCE_CF_STEP : BALANCE_STEP;
    const k = st.findIndex((x) => x.name === 'premium');
    return k < 0 ? st.concat([B]) : st.slice(0, k).concat([B], st.slice(k));
  }
  function corrSteps(common, taper) {
    const steps = [
      { name: 'cohort means', formula: F.means, badge: 'proved', lean: 'Credibility.Model.a_special' },
      { name: 'Σ̂ diagonal', formula: F.sigDiag, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_self' },
      { name: 'Σ̂ off-diagonal', formula: F.sigOff, badge: 'proved', lean: 'Credibility.Model.sigRhoHat_unbiased', note: 'unbiased; one value per pair of regions' },
    ];
    if (common) steps.push({ name: 'common covariance', formula: F.common, badge: 'proved', lean: 'Credibility.Model.commonCovHat_unbiased', rule: 'use ĉ in place of every off-diagonal Σ̂ᵢⱼ below' });
    steps.push(
      { name: 'ĉⱼ', formula: F.cj, badge: 'proved', lean: common ? 'Credibility.Model.cHatCommon_unbiased' : 'Credibility.Model.cHat_unbiased' },
      { name: 'τ̂²', formula: F.tau, badge: 'proved', lean: common ? 'Credibility.Model.tauHatCommon_unbiased' : 'Credibility.Model.tauHat_unbiased', rule: TAU_ZERO },
    );
    if (!common) steps.push({ name: 'Σ̂⁺ (nearest PSD)', formula: F.psdProj, badge: 'proved', lean: 'Credibility.ConeProjection.existsUnique_proj_posSemidef',
      rule: 'Σ̂⁺ = Σ̂ when Σ̂ is positive semidefinite; τ̂², ĉⱼ and the damping or taper rule keep Σ̂',
      note: 'the nearest positive semidefinite table in the Frobenius norm (Higham 1988): never further from the true Σ than Σ̂, for every draw; biased, unlike Σ̂' });
    steps.push(
      taper
        ? { name: 'tapered K̂', formula: F.taperP, badge: 'proved', lean: 'Credibility.posDef_distTaper_hadamard', gap: 'G2', varies: true,
          rule: `${F.taperRule}; lowered in steps of 0.05 only if K̂ is not positive definite (possible only when τ̂² = 0)`,
          note: 'K̂ ≻ 0 for every ρ ∈ [0, 1] when τ̂² > 0, since Σ̂⁺ ⪰ 0 (posDef_distTaper_hadamard, ties allowed); with τ̂² = 0 a numerical check; the criterion for ρ̂ is a plug-in (G2), with every pair at distance 1 it is the damping study’s rule S3 for the damping factor' }
        : { name: 'damped K̂', formula: common ? F.damped : F.dampedP, badge: common ? 'not proved yet' : 'proved', lean: common ? null : 'Credibility.posDef_shrinkOffDiag', gap: 'G2', varies: true,
          rule: `${F.dampRule}; at most 0.999; lowered in steps of 0.05 only if K̂ is not positive definite (a Cholesky factorisation fails)`,
          note: common
            ? 'K̂ ≻ 0 for every θ < 1 is proved when Σ̂ is positive semidefinite (posDef_shrinkOffDiag); θ̂ is a plug-in of the best shrinkage of the correlations, signal r̄² against their sampling variance (damping study S3), a heuristic for the rates (G2)'
            : 'K̂ ≻ 0 for every θ < 1, since Σ̂⁺ ⪰ 0 with a positive diagonal (posDef_shrinkOffDiag), so θ̂ is never lowered; θ̂ is a plug-in of the best shrinkage of the correlations, signal r̄² against their sampling variance (damping study S3), a heuristic for the rates (G2)' },
    );
    if (common) {
      steps.push(
        { name: 'z', formula: F.zEq, badge: 'proved', lean: 'Credibility.Core.bestZ_of_equalCov', rule: 'if τ̂² = 0: z = 0 and b by GLS, b = K̂⁻¹1 / 1ᵀK̂⁻¹1' },
        { name: 'b', formula: F.bOfZ, badge: 'proved', lean: 'Credibility.Core.b_eq_of_equalCov' },
      );
    } else {
      steps.push(
        { name: 'b', formula: F.gls, badge: 'proved', lean: 'Credibility.glsWeight_optimal' },
        { name: 'z', formula: F.z26, badge: 'proved', lean: 'Credibility.Core.bestZ_eq' },
      );
    }
    steps.push(
      { name: 'rates', formula: F.rates, badge: 'proved', lean: 'Credibility.BlendMoments.bestZ_optimal', note: 'optimal for the true K and τ²; with estimates plugged in, not exactly balanced' },
      premiumStep(BLEND_MSE),
    );
    return steps;
  }
  RECIPES.corr.steps = corrSteps(false);
  RECIPES.corrC.steps = corrSteps(true);
  RECIPES.corrT.steps = corrSteps(false, true);
  RECIPES.blupT = {
    intro: 'The best linear unbiased predictor on the thesis’s full K̂ (every pair estimated, eqs. (37)–(41)), tapered by ρ̂^|i−j| for regions in an order. Pays with many regions whose correlation fades with distance (J = 20, ordered: 9–28 points of the blend floor better than BLUP on corrBS’s one-ρ̂ K̂); with few regions or one common correlation, BLUP is better.',
    steps: RECIPES.corrT.steps.filter((x) => !['b', 'z', 'rates', 'premium'].includes(x.name)).concat(BLUP_TAIL),
  };

  RECIPES.blupA = {
    intro: 'The plug-in BLUP on a table chosen by the data: tapered by ρ̂^|i−j| when the estimated correlation falls with distance (BLUP taper), else corrBS’s one-ρ̂ K̂ (BLUP). The choice compares the two tables’ plug-in losses, no tuning (studies S46–S47: never more than 4 points worse than BLUP, keeps part of the taper’s gain).',
    branches: { taper: 'the correlation falls with distance', corrBS: 'no clear fall with distance' },
    steps: [RECIPES.blupT.steps[0],
      { name: 'taper signal', formula: F.taperSignal, badge: 'not proved yet', gap: 'G2', note: 'r̄_d: the average estimated correlation (thesis Σ̂) of the pairs at distance d, n_d of them, r̄ over all pairs' }]
      .concat(RECIPES.blupT.steps.slice(1).filter((x) => !['b', 'BLUP weights', 'rates', 'premium'].includes(x.name)).map((x) => Object.assign({}, x, { branch: 'taper' })))
      .concat(RECIPES.blup.steps.slice(1).filter((x) => !['b', 'BLUP weights', 'rates', 'premium'].includes(x.name)).map((x) => Object.assign({}, x, { branch: 'corrBS' })))
      .concat(BLUP_TAIL),
  };
  {
    const upto = RECIPES.vc.steps.findIndex((x) => x.name === 'K̂') + 1;
    const pooledRedo = RECIPES.blupPool.steps.filter((x) => ['σ̃ⱼ²', 'ρ̂', 'τ̂²', 'K̂'].includes(x.name)).map((x) => Object.assign({}, x, { name: `${x.name} (pooled)`, branch: 'pooled' }));
    RECIPES.vcGP = {
      intro: 'Correlated Bühlmann–Straub, with the variance step decided by the data: region variances σ̃ⱼ² when their exact gain on K̂ exceeds their first-order price, else one pooled σ̂² (studies S56–S57: regret at most 3 points against the better of the two, 1.2 points better than corrBS on average). Nothing to tune.',
      branches: { pooled: 'the gain of region variances is below their price' },
      steps: RECIPES.vc.steps.slice(0, upto).concat(
        [{ name: 'variances: gain against price', formula: F.gainPrice, badge: 'not proved yet', gap: 'G1', note: 'the gain is exact for the fitted K̂ (CoreMoments.mse_blend_eq_blup_add); the price is a first-order law, studies S56 (holds for ẑ ≥ 0.6), proved in the balanced world as an upper bound (Cumulants.ownPrice_sub_pooled_le_of_balanced)' }],
        pooledRedo,
        RECIPES.vc.steps.filter((x) => ['b', 'z', 'rates'].includes(x.name)),
        [premiumStep(`K̂ from the chosen branch; ${BLEND_MSE}`)]),
    };
  }

  /** The notation a recipe needs: entries marked always, and those its text mentions. */
  function recipeNotation(id) {
    const text = RECIPES[id].steps.map((s) => [s.formula, s.rule || '', s.note || ''].join(' ')).join(' ');
    return NOTATION.filter((n) => n.always || text.includes(n.match));
  }

  /** The recipe as plain text, for copying. */
  function recipeText(id, opts) {
    const r = RECIPES[id], out = [MODELS[id].name, r.intro, '', 'Notation'];
    for (const n of recipeNotation(id)) out.push(`  ${n.sym}: ${n.text}`);
    out.push('', 'Steps');
    recipeSteps(id, opts).forEach((s, k) => {
      out.push(`${k + 1}. ${s.name}${s.branch && r.branches ? ` (only if ${r.branches[s.branch]})` : ''}: ${s.formula}`);
      if (s.rule) out.push(`   rule: ${s.rule}`);
      if (s.note) out.push(`   note: ${s.note}`);
      out.push(`   ${s.badge === 'proved' ? 'proved: ' + s.lean.replace(/^Credibility\./, '') : 'not proved yet' + (s.gap ? ' (' + s.gap + ')' : '')}`);
    });
    return out.join('\n');
  }

  /**
   * World and fit features (PLAN.md §2, §6). `world` / `fit` say whether that
   * side is built yet; the page greys out the rest.
   */
  const FEATURES = [
    { id: 'rho', name: 'Correlation between regions within a year', world: true, fit: true },
    { id: 'unequal', name: 'Unequal lengths (regions entered recently)', world: false, fit: false, fitNote: 'step 4' },
    { id: 'groups', name: 'Group levels (regions of one country)', world: true, fit: true },
  ];

  // ---------------------------------------------------------------- the floor (known parameters)

  /** The best blend if K and τ² were known: eq. (26) on the true K. Reads the truth. */
  function floorBlend(world) {
    const K = trueK(world);
    const { b, z, s2 } = hasGroups(world) ? bestBlendWeightsL(K, world.truth.L) : bestBlendWeights(K, world.truth.tau2);
    return { K, b, z, s2, apply: (data) => blend(cohortMeans(data).m, z, b) };
  }

  /** The floor's true forecast MSE (Core.Estimates.mse_forecast): level MSE + σⱼ²/wⱼ,next. Reads the truth. */
  function floorForecast(world, wNext) {
    const fl = floorBlend(world), { tau2, sigmaj2 } = world.truth;
    const level = fl.z.map((z, j) => (hasGroups(world) ? blendMSEL(fl.K, world.truth.L, fl.b, j, z) : blendMSE(fl.K, tau2, fl.b, fl.s2, j, z)));
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
   * `split` (each fit): its excess over the oracle (the BLUP with true K, `floorBlup`) split as in
   * Core.Target.integral_sq_plugIn: with A = oracle rate − μⱼ and B = fit rate − oracle rate,
   * exposure-weighted, error = oracle error + E B² + 2E[AB] draw for draw. `b2`, `cross` (= 2E[AB])
   * and their standard errors; under normal noise and an even, translation-invariant fit (BLUP on
   * corrBS's K̂) the cross term is 0 (Core.Target.plugIn_mse_of_normal).
   * `bias` (each fit and the oracle): mean error of the rates, rateⱼ − μⱼ, exposure-weighted
   * (`mean`, `se`) and per region (`region`, `regionSe`). The oracle is unbiased in every world; a
   * plug-in fit that is even and translation invariant is unbiased under symmetric noise
   * (Core.Target.blup_plugIn_unbiased_of_symmetric), not necessarily under skewed noise.
   * `covDiag` (fits with weights, `weightsOf`): the sample covariances over the draws behind that
   * bias, Σᵢ cov(d̂ᵢ⁽ʲ⁾, μ̂ᵢ) (Core.Estimates.integral_randomLin_sub: it equals the bias in
   * expectation), split into the own-weight term cov(d̂ⱼ⁽ʲ⁾, μ̂ⱼ) and the other regions' terms, per
   * region and exposure-weighted (`own`, `other`, `ownW`, `otherW`).
   */
  function simulate(world, ids, n, seed, nextFactor, opts) {
    const bal = !!(opts && opts.balance), bo = balOpts(opts);
    const r = rng(seed), rn = rng((seed ^ 0x5bd1e995) >>> 0), fl = floorBlend(world);
    const Dstar = fl.K.map((_, j) => (hasGroups(world) ? blupWeightL(fl.K, world.truth.L, j) : blupWeight(fl.K, world.truth.tau2, j)));
    const wt = world.w.map(sum), wall = sum(wt);
    const wNext = wt.map((x) => (nextFactor == null ? 1 : nextFactor) * x / world.T);
    const ftheory = sum(floorForecast(world, wNext).mse.map((m, j) => wt[j] * m)) / wall;
    const acc = {};
    for (const id of ids.concat(['floor', 'floorBlup'])) acc[id] = { s: 0, ss: 0, f: 0, ff: 0, b: 0, bb: 0, c: 0, cc: 0, rs: 0, rss: 0, m: 0, mm: 0, rm: wt.map(() => 0), rmm: wt.map(() => 0), warn: 0, flags: {}, expected: {} };
    const addBias = (a, rates, levels) => {
      const e = rates.map((x, j) => x - levels[j]), q = wsum(e);
      a.m += q; a.mm += q * q; e.forEach((x, j) => { a.rm[j] += x; a.rmm[j] += x * x; });
    };
    const wsum = (v) => sum(v.map((x, j) => wt[j] * x)) / wall;
    const J = wt.length, zeros = () => Array.from({ length: J }, () => new Array(J).fill(0));
    const cd = {}, mSum = new Array(J).fill(0);
    for (const id of ids) cd[id] = { d: zeros(), dm: zeros(), n: 0 };
    const fe = (rates, Y) => sum(rates.map((x, j) => wt[j] * (x - Y[j]) * (x - Y[j]))) / wall;
    for (let k = 0; k < n; k++) {
      const { levels, data } = draw(world, r), Y = drawNext(world, levels, wNext, rn);
      const mm = cohortMeans(data).m, br = Dstar.map((d) => sum(d.map((x, i) => x * mm[i])));
      const A = br.map((x, j) => x - levels[j]);
      mm.forEach((x, i) => { mSum[i] += x; });
      for (const id of ids) {
        const raw = MODELS[id].fit(data), f = needsBal(id, opts) ? applyBal(raw, data, opts) : raw;
        if (f.balanceAuto) { acc[id].on = (acc[id].on || 0) + (f.balanceAuto.on ? 1 : 0); }
        if (f !== raw) { const q = wsum(raw.rates.map((x, j) => x - levels[j])); acc[id].rb = (acc[id].rb || 0) + q; acc[id].rbb = (acc[id].rbb || 0) + q * q; }
        const e = weightedSE(data, f.rates, levels), g = fe(f.rates, Y), er = weightedSE(data, raw.rates, levels);
        acc[id].rs += er; acc[id].rss += er * er;
        acc[id].s += e; acc[id].ss += e * e; acc[id].f += g; acc[id].ff += g * g; if (f.warnings.length) acc[id].warn++;
        const B = f.rates.map((x, j) => x - br[j]), b2 = wsum(B.map((x) => x * x)), c2 = 2 * wsum(B.map((x, j) => A[j] * x));
        acc[id].b += b2; acc[id].bb += b2 * b2; acc[id].c += c2; acc[id].cc += c2 * c2;
        addBias(acc[id], f.rates, levels);
        const W = f.weightsApprox ? null : weightsOf(f);
        if (W) { cd[id].n++; W.forEach((d, j) => d.forEach((x, i) => { cd[id].d[j][i] += x; cd[id].dm[j][i] += x * mm[i]; })); }
        for (const k in f.flags) if (f.flags[k]) {
          acc[id].flags[k] = (acc[id].flags[k] || 0) + 1;
          if (f.expected && f.expected[k]) acc[id].expected[k] = (acc[id].expected[k] || 0) + 1;
        }
      }
      const fr = fl.apply(data).rates, e = weightedSE(data, fr, levels), g = fe(fr, Y);
      acc.floor.s += e; acc.floor.ss += e * e; acc.floor.f += g; acc.floor.ff += g * g;
      const eb = weightedSE(data, br, levels), gb = fe(br, Y);
      addBias(acc.floorBlup, br, levels);
      acc.floorBlup.s += eb; acc.floorBlup.ss += eb * eb; acc.floorBlup.f += gb; acc.floorBlup.ff += gb * gb;
    }
    const out = {};
    for (const id in acc) {
      const mean = acc[id].s / n, v = Math.max(acc[id].ss / n - mean * mean, 0);
      const fm = acc[id].f / n, fv = Math.max(acc[id].ff / n - fm * fm, 0);
      const flags = {}, expected = {};
      for (const k in acc[id].flags) flags[k] = acc[id].flags[k] / n;
      for (const k in acc[id].expected) expected[k] = acc[id].expected[k] / n;
      out[id] = { mse: mean, se: Math.sqrt(v / n), fmse: fm, fse: Math.sqrt(fv / n), warnShare: acc[id].warn / n, flags, expected };
      const se = (x, xx) => Math.sqrt(Math.max(xx / n - (x / n) ** 2, 0) / n);
      if (bal && ids.includes(id) && needsBal(id, opts)) {
        out[id].raw = { mse: acc[id].rs / n, se: se(acc[id].rs, acc[id].rss), bias: { mean: (acc[id].rb || 0) / n, se: se(acc[id].rb || 0, acc[id].rbb || 0) } };
        if (acc[id].on != null) out[id].balancedShare = acc[id].on / n;
      }
      if (id !== 'floor') out[id].bias = { mean: acc[id].m / n, se: se(acc[id].m, acc[id].mm), region: acc[id].rm.map((x) => x / n), regionSe: acc[id].rm.map((x, j) => se(x, acc[id].rmm[j])) };
      if (ids.includes(id)) {
        const bm = acc[id].b / n, cm = acc[id].c / n;
        out[id].split = { b2: bm, b2se: Math.sqrt(Math.max(acc[id].bb / n - bm * bm, 0) / n), cross: cm, crossSe: Math.sqrt(Math.max(acc[id].cc / n - cm * cm, 0) / n) };
      }
    }
    for (const id of ids) if (cd[id].n === n) {
      const cv = cd[id].d.map((row, j) => row.map((x, i) => cd[id].dm[j][i] / n - (x / n) * (mSum[i] / n)));
      const own = cv.map((row, j) => row[j]), other = cv.map((row, j) => sum(row) - row[j]);
      out[id].covDiag = { own, other, ownW: wsum(own), otherW: wsum(other) };
    }
    out.floor.ftheory = ftheory;
    return out;
  }

  /** A fit's weights d̂⁽ʲ⁾ on the cohort means (rows j), when its rates are linear in them: the BLUP's own, or a blend's zⱼeⱼ + (1 − zⱼ)b. */
  function weightsOf(f) {
    if (f.weights) return f.weights;
    if (f.z && f.b) return f.z.map((z, j) => blendWeight(z, f.b, j));
    return null;
  }

  /**
   * The pooled cross-region third moment γ̂ of the standardized cells (a year shock shared by the
   * regions: γ = ρ^(3/2)·skew(η) in the app's world, 0 without one). For triples of regions (a, b, c),
   * not all equal, Mₐᵦ꜀ = Σₜ cₜ rₐₜrᵦₜr꜀ₜ with cₜ = √(wₐₜwᵦₜw꜀ₜ) has, for noise independent over years
   * with third moments Kₐᵦ꜀/√(wₐₛwᵦₛw꜀ₛ), E M = Kₐᵦ꜀ Σₜ cₜ Σₛ uₐ(t, s)uᵦ(t, s)u꜀(t, s)/√(wₐₛwᵦₛw꜀ₛ),
   * uₐ(t, s) = δₜₛ − aₐₛ (k-statistic style, as κ̂ⱼ). Pooled as Σ M / Σ σ̂ₐσ̂ᵦσ̂꜀·coef over the triples
   * a < b < c and the pairs (a, a, b), a ≠ b. Data only.
   */
  function crossSkew(data) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data), w = data.w;
    const r = data.X.map((row, j) => row.map((x) => x - m[j]));
    const sd0 = r.map((row, j) => Math.sqrt(sum(row.map((x, t) => w[j][t] * x * x)) / (T - 1)));
    const sd = sd0.map((x) => new Array(T).fill(x));
    const u = (a, t, s) => (t === s ? 1 : 0) - w[a][s] / wt[a];
    let num = 0, den = 0;
    const add = (a, b, c) => {
      for (let t = 0; t < T; t++) {
        const ct = Math.sqrt(w[a][t] * w[b][t] * w[c][t]);
        let e = 0;
        for (let s2 = 0; s2 < T; s2++) e += u(a, t, s2) * u(b, t, s2) * u(c, t, s2) / Math.sqrt(w[a][s2] * w[b][s2] * w[c][s2]);
        num += ct * r[a][t] * r[b][t] * r[c][t]; den += sd[a][t] * sd[b][t] * sd[c][t] * ct * e;
      }
    };
    for (let a = 0; a < J; a++) for (let b = 0; b < J; b++) if (a !== b) {
      add(a, a, b);
      for (let c = b + 1; c < J; c++) if (a < b) add(a, b, c);
    }
    return den !== 0 ? num / den : 0;
  }

  /**
   * Unbiased third moments Kₐᵦ꜀ of the standardized cells across regions, one per triple not all equal:
   * K̂ₐᵦ꜀ = Mₐᵦ꜀ / Σₜ cₜ Σₛ uₐ(t, s)uᵦ(t, s)u꜀(t, s)/√(wₐₛwᵦₛw꜀ₛ) (the k-statistic of crossSkew, without the
   * σ̂ that make the pooled γ̂ read low: E σ̂ₐσ̂ᵦσ̂꜀ > σₐσᵦσ꜀ when a shared shock inflates them together).
   * Noisy one by one; skewBias sums many of them. Returns K(a, b, c), symmetric.
   */
  function crossThird(data) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data), w = data.w;
    const r = data.X.map((row, j) => row.map((x) => x - m[j]));
    const u = (a, t, s) => (t === s ? 1 : 0) - w[a][s] / wt[a];
    const tab = new Map(), key = (a, b, c) => [a, b, c].sort((x, y) => x - y).join(',');
    const est = (a, b, c) => {
      let M = 0, coef = 0;
      for (let t = 0; t < T; t++) {
        const ct = Math.sqrt(w[a][t] * w[b][t] * w[c][t]);
        let e = 0;
        for (let s2 = 0; s2 < T; s2++) e += u(a, t, s2) * u(b, t, s2) * u(c, t, s2) / Math.sqrt(w[a][s2] * w[b][s2] * w[c][s2]);
        M += ct * r[a][t] * r[b][t] * r[c][t]; coef += ct * e;
      }
      return M / coef;
    };
    return (a, b, c) => { const k = key(a, b, c); if (!tab.has(k)) tab.set(k, est(a, b, c)); return tab.get(k); };
  }

  /**
   * The plug-in bias of a fit from the skew of the noise (Finding 35 (a) + (c)), predicted from one
   * data set. Exactly, E(rateⱼ − μⱼ) = Σₗ cov(d̂ⱼₗ, μ̂ₗ) (Core.Estimates.integral_randomLin_sub). To first
   * order in the fit's variance statistics q (level-free quadratic forms of the residuals),
   * cov(d̂ⱼₗ, μ̂ₗ) ≈ Σ_q ∂d̂ⱼₗ/∂q · cov(q, μ̂ₗ), and cov(q, μ̂ₗ) = Σ Aᵢⱼ bₖ κ₃ᵢⱼₖ
   * (Cumulants.covariance_quad_lin_of_cumulants; Am = 0 for residuals) from the third moments.
   * Third moments: ĝσ̂ₖ³ per standardized cell within a region (pooled ĝ, noiseDiagnostics) and
   * γ̂σ̂ₐσ̂ᵦσ̂꜀ across regions (crossSkew, a shared year shock).
   * For corrBS and its BLUPs (ids vc, blup, blupPool) the statistics are the σ̂ₖ² (with their Wₖ) and
   * ρ̂'s numerator Σᵢ<ⱼ Qᵢⱼ, each perturbed alone (vcEstimate's perturb hook): both channels.
   * For other fits: the own-variance channel only, the derivative by refitting with region k's
   * residuals scaled by √(1 ± h) (which also moves its cross-products).
   * Leaves out the dependence through the means (τ̂²). Returns { region, portfolio, own, cross }
   * (exposure-weighted portfolio; own/cross: the portfolio parts through the σ̂ₖ² and through ρ̂), rate units.
   */
  function skewBias(id, data, opts) {
    const o = opts || {}, h = o.h || 0.05;
    const D = o.diag || noiseDiagnostics(data), J = data.X.length, T = data.X[0].length, wt = data.w.map(sum), w = data.w;
    const VC = { vc: (d, p) => fitVC(d, p), blup: (d, p) => fitBLUP(d, p), blupPool: (d, p) => fitBLUP(d, Object.assign({ pooled: true }, p)) }[id];
    const fit = o.fit || ((d, p) => (VC ? VC(d, p) : MODELS[id].fit(d)));
    if (!weightsOf(fit(data))) return null;
    const gamma = o.gamma != null ? o.gamma : J > 2 ? crossSkew(data) : 0;
    const sd = D.regions.map((r) => Math.sqrt(r.s2));
    // Cross-region third moments: o.third === 'pooled' uses γ̂σ̂ₐσ̂ᵦσ̂꜀ (reads low); default: the unbiased K̂ₐᵦ꜀ per triple.
    const KX = o.third === 'pooled' ? null : crossThird(data);
    const K3 = (a, b, c) => (a === b && b === c ? D.skew * sd[a] ** 3 : KX ? KX(a, b, c) : gamma * sd[a] * sd[b] * sd[c]);
    const u = (a, t, s) => (t === s ? 1 : 0) - w[a][s] / wt[a];
    // cov(Σₜ cₜ rₐₜrᵦₜ, μ̂ₗ) = Σₜ cₜ Σₛ uₐ(t, s)uᵦ(t, s) aₗₛ Kₐᵦₗ/√(wₐₛwᵦₛwₗₛ)
    const covQ = (a, b, c, l) => {
      let x = 0;
      for (let t = 0; t < T; t++) for (let s = 0; s < T; s++) x += c(t) * u(a, t, s) * u(b, t, s) * (w[l][s] / wt[l]) / Math.sqrt(w[a][s] * w[b][s] * w[l][s]);
      return x * K3(a, b, l);
    };
    const region = new Array(J).fill(0), part = { own: new Array(J).fill(0), cross: new Array(J).fill(0) };
    const ownCov = (k, l) => (VC || l === k ? covQ(k, k, (t) => w[k][t] / (T - 1), l) : 0);
    for (let k = 0; k < J; k++) {
      let Wp, Wm;
      if (VC) {
        Wp = weightsOf(fit(data, { perturb: { own: [k, 1 + h] } })); Wm = weightsOf(fit(data, { perturb: { own: [k, 1 - h] } }));
      } else {
        const r = D.regions[k], sc = (sg) => ({ w: data.w, X: data.X.map((row, i) => (i === k ? row.map((x) => r.mu + Math.sqrt(1 + sg * h) * (x - r.mu)) : row)) });
        Wp = weightsOf(fit(sc(1))); Wm = weightsOf(fit(sc(-1)));
      }
      const ds = 2 * h * D.regions[k].s2;
      for (let l = 0; l < J; l++) {
        const c = ownCov(k, l);
        if (c) for (let j = 0; j < J; j++) part.own[j] += (Wp[j][l] - Wm[j][l]) / ds * c;
      }
    }
    if (VC && gamma) {
      const base = vcEstimate(data, id === 'blupPool' ? { pooled: true } : {}), dq = 2e-3 * base.qa;
      if (base.rhoRaw > 0 && base.rhoRaw < 1) {
        const Wp = weightsOf(fit(data, { perturb: { q: 1e-3 } })), Wm = weightsOf(fit(data, { perturb: { q: -1e-3 } }));
        for (let l = 0; l < J; l++) {
          let c = 0;
          for (let a = 0; a < J; a++) for (let b = a + 1; b < J; b++) c += covQ(a, b, (t) => Math.sqrt(w[a][t] * w[b][t]), l);
          for (let j = 0; j < J; j++) part.cross[j] += (Wp[j][l] - Wm[j][l]) / dq * c;
        }
      }
    }
    // τ̂² channel (corrBS and its BLUPs): τ̂² = Σⱼ wⱼ*((μ̂ⱼ − μ̄)² − ĉⱼ)/n₀ is quadratic in the means, so
    // cov(τ̂², μ̂ₗ) = Σⱼ (wⱼ*/n₀) Σᵢₖ gⱼᵢgⱼₖ κ(μ̂ᵢ, μ̂ₖ, μ̂ₗ) (covariance_quad_lin_of_cumulants; g annihilates
    // the common mean), with the third cumulants of the means: δᵢₖₗκ_L (skewed levels) plus the noise part
    // Σₛ aᵢₛaₖₛaₗₛ Kᵢₖₗ/√(wᵢₛwₖₛwₗₛ). κ̂_L by its moment equation (levelThird). The ĉⱼ move with the
    // variance statistics, already counted above.
    part.tau = new Array(J).fill(0);
    let kL = 0;
    if (VC) {
      const base = vcEstimate(data, id === 'blupPool' ? { pooled: true } : {});
      if (base.tauRaw > 0) {
        const L3 = levelThird(data, K3);
        kL = L3.kappa;
        const dt = 1e-3 * base.tauRaw, Wp = weightsOf(fit(data, { perturb: { tau: dt } })), Wm = weightsOf(fit(data, { perturb: { tau: -dt } }));
        const wall = sum(wt), n0 = wall - sum(wt.map((x) => x * x)) / wall;
        for (let l = 0; l < J; l++) {
          let c = 0;
          for (let j = 0; j < J; j++) for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) c += wt[j] / n0 * L3.g[j][i] * L3.g[j][k] * L3.kmean(i, k, l);
          for (let j = 0; j < J; j++) part.tau[j] += (Wp[j][l] - Wm[j][l]) / (2 * dt) * c;
        }
      }
    }
    for (let j = 0; j < J; j++) region[j] = part.own[j] + part.cross[j] + part.tau[j];
    const pw = (v) => sum(v.map((x, j) => wt[j] * x)) / sum(wt);
    return { region, portfolio: pw(region), own: pw(part.own), cross: pw(part.cross), tau: pw(part.tau), gamma, kappaLevel: kL };
  }

  /**
   * The third cumulant κ_L of the levels (iid over regions), by a moment equation on the means:
   * dⱼ = μ̂ⱼ − μ̄ = Σᵢ gⱼᵢμ̂ᵢ (gⱼᵢ = δⱼᵢ − vᵢ, vᵢ = wᵢ* / w**, Σᵢ gⱼᵢ = 0), Z = Σⱼ vⱼdⱼ³,
   * E Z = κ_L Σⱼ vⱼ Σᵢ gⱼᵢ³ + Σⱼ vⱼ Σᵢₖₗ gⱼᵢgⱼₖgⱼₗ κ(ēᵢ, ēₖ, ēₗ), with the noise part of the means
   * κ(ēᵢ, ēₖ, ēₗ) = Σₛ aᵢₛaₖₛaₗₛ Kᵢₖₗ/√(wᵢₛwₖₛwₗₛ) from the cell third moments K (given). Unbiased if K is.
   * Returns { kappa, g, kmean(i, k, l) } with kmean the third cumulants of the means (levels + noise).
   */
  function levelThird(data, K) {
    const J = data.X.length, T = data.X[0].length, { wt, m } = cohortMeans(data), w = data.w, wall = sum(wt);
    const v = wt.map((x) => x / wall), g = v.map((_, j) => v.map((vi, i) => (i === j ? 1 : 0) - vi));
    const memo = new Map();
    const knoise = (i, k, l) => {
      const key = [i, k, l].sort((x, y) => x - y).join(',');
      if (!memo.has(key)) {
        let x = 0;
        for (let s2 = 0; s2 < T; s2++) x += (w[i][s2] / wt[i]) * (w[k][s2] / wt[k]) * (w[l][s2] / wt[l]) / Math.sqrt(w[i][s2] * w[k][s2] * w[l][s2]);
        memo.set(key, x * K(i, k, l));
      }
      return memo.get(key);
    };
    const mbar = sum(m.map((x, j) => v[j] * x));
    let Z = 0, cL = 0, nz = 0;
    for (let j = 0; j < J; j++) {
      Z += v[j] * (m[j] - mbar) ** 3;
      for (let i = 0; i < J; i++) {
        cL += v[j] * g[j][i] ** 3;
        for (let k = 0; k < J; k++) for (let l = 0; l < J; l++) nz += v[j] * g[j][i] * g[j][k] * g[j][l] * knoise(i, k, l);
      }
    }
    const kappa = (Z - nz) / cL;
    return { kappa, g, kmean: (i, k, l) => (i === k && k === l ? kappa : 0) + knoise(i, k, l) };
  }

  // ---------------------------------------------------------------- noise shape (moments only)

  /**
   * Third-moment and variance–mean checks of the noise, per region, from the data alone (PLAN
   * "Noise shape" step 1; no distribution is fitted). Within region j, rₜ = Xⱼₜ − μ̂ⱼ with
   * μ̂ⱼ = Σ aₜXⱼₜ, aₜ = wⱼₜ/wⱼ*. Assumed: noise independent over years with variance σⱼ²/wⱼₜ and
   * third cumulant κⱼ/wⱼₜ^q (q = 3/2: a standardized cell √w(X − μ)/σ has a fixed skewness, as in
   * the app's world; q = 2: the ratio is a mean over wⱼₜ independent units, as in real portfolios).
   * Then, exactly (k-statistic style):
   *   E Σₜ wₜ rₜ² = (T − 1)σⱼ²,   E Σₜ cₜ rₜ³ = κⱼ Σₜ cₜ Σₛ (δₜₛ − aₛ)³ wₛ^(−q),   cₜ = wₜ^q,
   * so σ̂ⱼ² and κ̂ⱼ are unbiased (κ̂ⱼ proved: Cumulants.kappaHat_unbiased); the skewness gⱼ = κⱼ/σⱼ³ (of one unit of volume) is estimated by
   * the ratio κ̂ⱼ/σ̂ⱼ³ (not unbiased), and pooled as Σκ̂ⱼ / Σσ̂ⱼ³ with SE from the spread over regions.
   * Common year shocks (ρ > 0) stay in rₜ and count as noise.
   *
   * Variance against mean: log σ̂ⱼ² = a + p log μ̂ⱼ over regions (Taylor's power law; p = 1 Poisson,
   * 2 gamma). Under skew μ̂ⱼ and σ̂ⱼ² from the same years move together (the Finding 35 channel), so
   * p from them is biased upwards even when σⱼ does not follow μⱼ; `power` is therefore cross-fitted:
   * σ̂² from the even years against μ̂ from the odd ones and vice versa (independent given the
   * levels). `powerSame` is the naive slope, for comparison. Needs T ≥ 4 and μ̂ > 0.
   */
  /**
   * The skew channel of Finding 35 (c) for one region with volumes w over the years:
   * Cumulants.covariance_resVar_mean with aₛ = wₛ/w*, cₜ = wₜ/(n − 1) (σ̂², eq. (41)) and third
   * moments kₛ = κ wₛ^(−q): cov(σ̂², μ̂) = Σₛ aₛkₛ Σₜ cₜ(δₜₛ − aₛ)². link: % rise of σ̂² per +1% of μ̂ from
   * the noise alone, cov·μ / (σ²·Var(μ̂ | level)), Var(μ̂ | level) = σ² Σₛ aₛ²/wₛ.
   */
  function skewLink(w, kappa, q, s2, mu) {
    const n = w.length, ws = sum(w), a = w.map((v) => v / ws);
    let cov = 0;
    for (let s = 0; s < n; s++) {
      let e = 0;
      for (let t = 0; t < n; t++) e += w[t] / (n - 1) * ((t === s ? 1 : 0) - a[s]) ** 2;
      cov += a[s] * kappa * Math.pow(w[s], -q) * e;
    }
    const vMu = s2 * sum(a.map((v, k) => v * v / w[k]));
    return { cov, link: cov * mu / (s2 * vMu) };
  }

  function noiseDiagnostics(data, opts) {
    const q = (opts && opts.q) || 1.5;
    const J = data.X.length, T = data.X[0].length;
    const part = (j, ts) => {
      const w = ts.map((t) => data.w[j][t]), x = ts.map((t) => data.X[j][t]), ws = sum(w);
      const a = w.map((v) => v / ws), mu = sum(x.map((v, k) => a[k] * v)), r = x.map((v) => v - mu);
      const n = ts.length, s2 = sum(r.map((v, k) => w[k] * v * v)) / (n - 1);
      let m3 = 0, c3 = 0;
      for (let t = 0; t < n; t++) {
        const c = Math.pow(w[t], q);
        m3 += c * r[t] ** 3;
        let e = 0;
        for (let u = 0; u < n; u++) e += ((t === u ? 1 : 0) - a[u]) ** 3 * Math.pow(w[u], -q);
        c3 += c * e;
      }
      // The skew channel of Finding 35 (c), Cumulants.covariance_resVar_mean with cₜ = wₜ/(n − 1) and the
      // fitted third moments kₛ = κ̂ wₛ^(−q): cov(σ̂², μ̂) = Σₛ aₛkₛ Σₜ cₜ(δₜₛ − aₛ)².
      return { mu, s2, kappa: m3 / c3 };
    };
    const all = Array.from({ length: T }, (_, t) => t);
    const regions = Array.from({ length: J }, (_, j) => {
      const p = part(j, all);
      return { mu: p.mu, s2: p.s2, kappa: p.kappa, skew: p.kappa / Math.pow(p.s2, 1.5) };
    });
    const sk = regions.map((r) => r.skew), mSk = sum(sk) / J;
    // Pooled skewness g (one value for all regions): mean κ̂ⱼ over (mean σ̂ⱼ²)^(3/2). A ratio of
    // averages, so its bias from the κ̂–σ̂ dependence and from the 3/2 power is O(1/J); with equal σⱼ
    // it targets g, with unequal σⱼ the skewness of a region with the average variance (below g).
    const kBar = sum(regions.map((r) => r.kappa)) / J, sBar = sum(regions.map((r) => r.s2)) / J;
    const skew = kBar / Math.pow(sBar, 1.5);
    // SE: jackknife over regions (leave one region out).
    const jk = regions.map((r) => (kBar * J - r.kappa) / (J - 1) / Math.pow((sBar * J - r.s2) / (J - 1), 1.5));
    const jkBar = sum(jk) / J, skewSE = J > 1 ? Math.sqrt((J - 1) / J * sum(jk.map((v) => (v - jkBar) ** 2))) : NaN;
    const evenT = all.filter((t) => t % 2 === 0), oddT = all.filter((t) => t % 2 === 1);
    const slope = (xs, ys) => {
      const n = xs.length, mx = sum(xs) / n, my = sum(ys) / n;
      const sxx = sum(xs.map((v) => (v - mx) ** 2)), b = sum(xs.map((v, k) => (v - mx) * (ys[k] - my))) / sxx;
      const res = ys.map((v, k) => v - my - b * (xs[k] - mx));
      return { b, se: n > 2 ? Math.sqrt(sum(res.map((v) => v * v)) / (n - 2) / sxx) : NaN };
    };
    const ok = (v) => Number.isFinite(v) && v > 0;
    let power = null, powerSame = null;
    if (regions.every((r) => ok(r.mu) && ok(r.s2)) && J > 2) powerSame = slope(regions.map((r) => Math.log(r.mu)), regions.map((r) => Math.log(r.s2)));
    if (T >= 4 && J > 2) {
      // Two directions (σ̂² even / μ̂ odd, and the reverse), each centred on its own means: points of
      // different directions share years (same region, or a common year shock), so a joint centring
      // would correlate them. Pooled slope Σ Sxy / Σ Sxx; SE from the J region-level contributions.
      const even = evenT, odd = oddT;
      const pe = Array.from({ length: J }, (_, j) => part(j, even)), po = Array.from({ length: J }, (_, j) => part(j, odd));
      const dirs = [[po, pe], [pe, po]].map(([X, Y]) => ({ x: X.map((r) => Math.log(r.mu)), y: Y.map((r) => Math.log(r.s2)) }));
      if (dirs.every((d) => d.x.concat(d.y).every(Number.isFinite))) {
        const c = dirs.map((d) => { const mx = sum(d.x) / J, my = sum(d.y) / J; return { dx: d.x.map((v) => v - mx), dy: d.y.map((v) => v - my) }; });
        const sxx = sum(c.map((d) => sum(d.dx.map((v) => v * v))));
        const b = sum(c.map((d) => sum(d.dx.map((v, j) => v * d.dy[j])))) / sxx;
        // Influence of region j: Σ_dir dx(dy − b dx); its spread over regions gives the SE.
        const inf = Array.from({ length: J }, (_, j) => sum(c.map((d) => d.dx[j] * (d.dy[j] - b * d.dx[j]))));
        power = { b, se: Math.sqrt(J / (J - 2) * sum(inf.map((v) => v * v))) / sxx };
      }
    }
    // The skew channel per region with the pooled ĝ (κ̂ⱼ alone is too noisy, and κ̂ⱼ/σ̂ⱼ⁴ reads low because
    // σ̂ⱼ² rises with κ̂ⱼ under skew): third moment of a cell ĝσ̂ⱼ³ wₛ^(−3/2), as the standardized cell √w(X − μ)/σ.
    regions.forEach((r, j) => { const sl = skewLink(data.w[j], skew * Math.pow(r.s2, 1.5), 1.5, r.s2, r.mu); r.covMu = sl.cov; r.link = sl.link; });
    // Predicted skew bias of the same-years power: log σ̂ⱼ² and log μ̂ⱼ covary by ≈ cov(σ̂ⱼ², μ̂ⱼ)/(σ̂ⱼ²μ̂ⱼ)
    // within a region (first order), against the spread of log μ̂ⱼ over the regions; the centring
    // over regions keeps (1 − 1/J) of it. Data only; 0 under symmetric noise.
    let powerSkewBias = null;
    if (powerSame) {
      const lx = regions.map((r) => Math.log(r.mu)), mx = sum(lx) / J, sxx = sum(lx.map((v) => (v - mx) ** 2));
      powerSkewBias = (1 - 1 / J) * sum(regions.map((r) => r.covMu / (r.s2 * r.mu))) / sxx;
    }
    // Pooled skew link: the mean over regions; proportional to ĝ, so its SE is ĝ's scaled.
    const link = sum(regions.map((r) => r.link)) / J, linkSE = Math.abs(link * skewSE / skew);
    // The skewness a variance function V(μ) = μᵖ would imply (cumulant layer, PLAN Pending; VarianceFunction.lean):
    // κ₃ = (φ/w)²VV' = pφ²μ^(2p−1)/w², so a standardized cell √w(X − μ)/σⱼ has skewness p·σⱼ/(μⱼ√w) = p × its CV.
    // With the cross-fitted p̂, σ̂ⱼ, μ̂ⱼ and the region's mean volume w̄ⱼ per year, pooled as ĝ is (mean κ over
    // (mean σ̂ⱼ²)^(3/2)). A check before relying on the layer: far from ĝ means the noise is not such a family.
    let tweedieSkew = null;
    if (power) {
      const kT = regions.map((r, j) => power.b * r.s2 * r.s2 / (r.mu * Math.sqrt(sum(data.w[j]) / T)));
      tweedieSkew = sum(kT) / J / Math.pow(sBar, 1.5);
    }
    return { q, regions, skew, skewSE, power, powerSame, powerSkewBias, link, linkSE, tweedieSkew };
  }

  /** One draw's data as CSV: one row per region and year, the columns the fit sees. */
  function toCSV(data) {
    const lines = ['region,year,volume,ratio'];
    data.X.forEach((row, j) => row.forEach((x, t) => lines.push(`${j + 1},${t + 1},${+data.w[j][t].toPrecision(10)},${+x.toPrecision(10)}`)));
    return lines.join('\n') + '\n';
  }

  return {
    taperSignal, fitBLUPAuto, fitVCGP, loyoLoss, fitBLUPLoyo, gainPrice, bsPriceLaw, crossTermBS, noiseShape,
    DEFAULTS, MODELS, FEATURES, F, NOTATION, RECIPES, recipeNotation, recipeText,
    rng, solve, cholesky, makeWorld, noiseFactor, trueK, draw,
    cohortMeans, blend, bestBlendWeights, blendMSE,
    eigSym, blendWeight, blupWeight, linMse, noiseDeltas, dampedBound, correlationPrice, worldPrice, correlationIndicator,
    projectPSD, eigenSym,
    fitBS, fitOwn, fitPool, fitCorr, fitVC, fitBLUP, fitBLUPTaper, fitBLUPBal, balanceFit, balanceAuto, crossFitLevel, BALANCE_CF_STEP, BALANCE_AUTO_STEP, fitWith, recipeSteps, BALANCE_STEP, vcEstimate, vcWCoef, jackknifeMSEP, sigmaHat, sigmaHatVar, covTheta, sigmaHatMoments, corrVar, corrTheta, thesisTau, shrinkOffDiag, isPSD, THETAS, distTaper, taperRho, orderedNoise,
    floorBlend, weightedSE, simulate, weightsOf,
    fitGroupLevels, fitGroups, groupEffects, bestBlendWeightsL, blendMSEL, blupWeightL, linMseL,
    nextVolumes, drawNext, premium, floorForecast, toCSV, noiseDiagnostics, skewLink, skewBias, crossSkew, crossThird, levelThird, lomaxMoments, claimNoise, claimRate, SHRINK_W0,
  };
});
