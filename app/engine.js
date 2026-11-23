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

  /** Eigenvalues of a symmetric matrix, ascending (cyclic Jacobi; the matrices here are at most 20 × 20). */
  function eigSym(A) {
    const n = A.length, M = A.map((row) => row.slice());
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
      }
    }
    return M.map((row, i) => row[i]).sort((a, b) => a - b);
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
    levelShape: 4,   // gamma shape of the level draws (skewness 2/√k)
    noiseShape: 2,   // gamma shape of the noise draws
    normal: false,   // normal levels and noise instead of gamma (the plug-in cross term vanishes: plugIn_mse_of_normal)
    lomax: 0,        // 0: off; α > 2: the region part of the noise is a sum of Lomax claims with tail index α (literature §10l)
    noiseSpread: 0,  // region-specific σⱼ = σ·4^(s((j mod 4)/3 − ½)): 0 equal, 1 = ×0.5–2 (studies' spread worlds)
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
    // ρᵢⱼ: one common coefficient, or ρ^|i−j| for ordered regions (a country structure comes with group levels).
    const rho = [], r0 = Math.max(p.rho, 0);
    for (let i = 0; i < J; i++) { rho.push([]); for (let j = 0; j < J; j++) rho[i].push(i === j ? 1 : p.ordered ? Math.pow(r0, Math.abs(i - j)) : p.rho); }
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
   * claims when `params.lomax` (expected claims λⱼw), else the world's gamma or normal draw.
   */
  function regionDraw(world, r, j, w) {
    const p = world.params;
    return p.lomax ? claimNoise(r, claimRate(world, j) * w, p.lomax) : r.unit(p.noiseShape, p.normal);
  }

  /**
   * One data set from the world: the levels μⱼ (truth) and the table { w, X }.
   * Xⱼₜ = μⱼ + σⱼ/√wⱼₜ · εⱼₜ with εⱼₜ = √ρ·ηₜ + √(1-ρ)·ξⱼₜ, so corr(εᵢₜ, εⱼₜ) = ρ; with
   * `params.ordered` εₜ = orderedNoise (corr ρ^|i−j|). All draws skewed (gamma), or normal with
   * `params.normal`. With `params.lomax` the region part ξⱼₜ (the AR(1) innovations when
   * ordered) is a standardized sum of Lomax claims (claimNoise); the year shock ηₜ is not.
   */
  function draw(world, r) {
    const { J, T, w, truth, params } = world;
    const rho = params.rho, a = Math.sqrt(Math.max(rho, 0)), b = Math.sqrt(1 - Math.max(rho, 0));
    const tau = Math.sqrt(truth.tau2), sig = truth.sigmaj2.map(Math.sqrt);
    const levels = [], X = [];
    const nz = params.normal, ns = params.noiseShape;
    for (let j = 0; j < J; j++) levels.push(truth.mu + tau * r.unit(params.levelShape, nz));
    if (params.ordered) {
      const E = [];
      for (let t = 0; t < T; t++) E.push(orderedNoise(J, Math.max(rho, 0), r, ns, nz, (j) => regionDraw(world, r, j, w[j][t])));
      for (let j = 0; j < J; j++) X.push(E.map((e, t) => levels[j] + sig[j] / Math.sqrt(w[j][t]) * e[j]));
      return { levels, data: Object.freeze({ w: w.map((row) => Object.freeze(row.slice())), X }) };
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
  function correlationPrice(K, tau2, wt) {
    const J = K.length, Kd = K.map((row, i) => row.map((x, k) => (i === k ? x : 0)));
    const { b, z } = bestBlendWeights(K, tau2);
    const best = [], blendM = [], ignore = [];
    for (let j = 0; j < J; j++) {
      best.push(linMse(K, tau2, j, blupWeight(K, tau2, j)));
      blendM.push(linMse(K, tau2, j, blendWeight(z[j], b, j)));
      ignore.push(linMse(K, tau2, j, blupWeight(Kd, tau2, j)));
    }
    const { dm, dp } = noiseDeltas(K.map((row, i) => row.map((x, k) => (i === k ? x - tau2 : x))));
    const wall = sum(wt), agg = (a) => sum(a.map((x, j) => wt[j] * x)) / wall;
    return { best, blend: blendM, ignore, dm, dp, bound: dampedBound(dm, dp, 0), weighted: { best: agg(best), blend: agg(blendM), ignore: agg(ignore) } };
  }

  /** correlationPrice of a world: the true K. Reads the truth. */
  function worldPrice(world) {
    return correlationPrice(trueK(world), world.truth.tau2, world.w.map(sum));
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
    dampRule: 'θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T−1)), r̄ the average estimated correlation Σ̂ᵢⱼ/√(Σ̂ᵢᵢΣ̂ⱼⱼ) over the pairs',
    taper: 'K̂ᵢⱼ = ρ^|i−j| (Σ̂ + τ̂²⁺ I)ᵢⱼ  (regions in their order)',
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
    balance: 'rateⱼ + D,  D = Σᵢ wᵢ*(μ̂ᵢ − rateᵢ)/w**, the same D for every region',
    premium: 'premium = μ̂ⱼᵇ;  forecast error² = MSEⱼ + σ̂ⱼ²/wⱼ,next',
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
   * The taper's ρ by the plug-in criterion of the damping study (studies/damping-theta.md S3 and
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
   *   (taperRho with every pair at distance 1; studies/taper.js: up to 12 points better than the
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
    const psd = isPSD(Sig);
    const T = data.X[0].length, dist = o.taper === 'distance';
    let theta = null, thetaFit = null, K = null, rhoT = null, rhoFit = null, lags = null;
    if (dist) {
      const tr = o.rho != null ? { rho: o.rho, lags: null } : taperRho(Sig, T, (i, j) => Math.abs(i - j));
      rhoFit = tr.rho; lags = tr.lags;
      const Kraw = addDiag(Sig, tau2);
      for (let x = rhoFit; ; x = Math.max(0, Math.round((x - 0.05) * 1000) / 1000)) {
        const Kt = hadamard(distTaper(x, J), Kraw);
        if (cholesky(Kt)) { rhoT = x; K = Kt; break; }
        if (x === 0) break;
      }
    } else if (o.theta != null || o.thetaRule === 'grid') {
      for (const th of (o.theta != null ? [o.theta] : THETAS)) {
        const Kt = addDiag(shrinkOffDiag(th, Sig), tau2);
        if (cholesky(Kt)) { theta = th; K = Kt; break; }
      }
      thetaFit = o.theta != null ? o.theta : THETAS[0];
    } else {
      thetaFit = Math.min(o.thetaRule === 'cov' ? Math.round(covTheta(data, o.kappa || 0).theta * 1000) / 1000 : o.thetaRule === 'corr' ? Math.round(corrTheta(data, o).theta * 1000) / 1000 : taperRho(Sig, T, () => 1).rho, 0.999);   // below 1 so posDef_shrinkOffDiag applies (θ̂ = 1 iff r̄ = ±1, e.g. T = 2)
      for (let x = thetaFit; ; x = Math.max(0, Math.round((x - 0.05) * 1000) / 1000)) {
        const Kt = addDiag(shrinkOffDiag(x, Sig), tau2);
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
    if (flags.zOver1) warnings.push(`z > 1 for ${z.filter((x) => x > 1).length} region(s): the rate moves past the region's own mean, away from μ̂ (thesis eq. (34) would clip it; clipping cannot hurt only if the true z is in [0, 1], Finding 36)`);
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
      dist ? taperStep(rhoT, lags, psd && tau2 > 0)
        : { name: 'damped K̂', formula: `${F.damped};  θ = ${theta}`, values: [theta], badge: psd && theta < 1 ? 'proved' : 'not proved yet', lean: psd && theta < 1 ? 'Credibility.posDef_shrinkOffDiag' : null, gap: 'G2', note: (psd ? `Σ̂ ⪰ 0, so K̂ ≻ 0 for any θ < 1` : `Σ̂ is not positive semidefinite: K̂ ≻ 0 checked numerically at θ = ${theta}, not by a theorem`) + `; θ̂ = ${thetaFit} by the plug-in rule S3 (${F.dampRule}): the plug-in of the table-optimal θ* = s²/(s² + V) (Damping.bestTheta_optimal); optimal for the rates not proved (G2)` },
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

  /** The taper step of fitCorr (this draw). `proved`: Σ̂ ⪰ 0 and τ̂² > 0, so Σ̂ + τ̂²I ≻ 0. */
  function taperStep(rho, lags, proved) {
    const lagText = lags ? '; r̄_d by distance: ' + lags.slice(0, 4).map((g) => `d=${g.d}: ${g.r.toFixed(2)}`).join(', ') + (lags.length > 4 ? ', …' : '') : '';
    return {
      name: 'tapered K̂', formula: `${F.taper};  ρ̂ = ${rho}`, values: [rho], badge: proved ? 'proved' : 'not proved yet',
      lean: proved ? 'Credibility.posDef_distTaper_hadamard' : null, gap: 'G2',
      note: (proved ? 'Σ̂ ⪰ 0 and τ̂² > 0, so K̂ ≻ 0 for every ρ ∈ [0, 1]' : `Σ̂ + τ̂²I is not positive definite: K̂ ≻ 0 checked numerically at ρ = ${rho}, not by a theorem`) +
        `; ρ̂ by the plug-in criterion (${F.taperRule}), the damping study’s rule S3 (studies/damping-theta.md)${lagText}`,
    };
  }

  /**
   * Correlated Bühlmann–Straub with credibility-weighted variances
   * (studies/damping-theta.md, findings S15–S17 and the Ansatz; studies/variance-credibility.js,
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
    const own = Q.map((row, j) => row[j] / (T - 1)), pooled = sum(own) / J;
    const W = own.map((sj, j) => {
      const u = data.X[j].map((x, t) => data.w[j][t] * (x - m[j]) ** 2 * T / (T - 1));
      return sum(u.map((x) => (x - sj) ** 2)) / (T * (T - 1));
    });
    const betweenRaw = sum(own.map((x) => (x - pooled) ** 2)) / (J - 1) - sum(W) / J;
    const between = Math.max(0, betweenRaw);
    // opts.pooled: one noise variance for all regions (ζⱼ = 0), the Finding 35 remedy.
    const zeta = W.map((Wj) => (between > 0 && !(opts && opts.pooled) ? between / (between + Wj) : 0));
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

  function fitVC(data, opts) {
    const pooled = !!(opts && opts.pooled), p = vcEstimate(data, opts), { m, wt, S } = p, J = m.length;
    const { K, b, z, mu, rates } = vcBlend(p, wt, S, m);
    const offBal = sum(wt.map((x, j) => x * (m[j] - rates[j]))) / sum(wt.map((x, j) => x * m[j]));
    const flags = { tauNeg: p.tauRaw <= 0, zOver1: z.some((x) => x > 1), zNeg: z.some((x) => x < 0), bNeg: b.some((x) => x < 0), offBalance: Math.abs(offBal) > 0.01 };
    // Flags the optimum itself shows (studies/vc-balance.js, damping-theta.md findings S27–S29): with ρ̂ > 0
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
      { name: 'Wⱼ, β²', formula: F.vcW, values: [p.betweenRaw], badge: 'not proved yet', gap: 'G1', note: `β² (between-region variance of the σⱼ²)${p.betweenRaw <= 0 ? ': ≤ 0, set to 0, so every σ̃ⱼ² is the pooled σ̂²' : ''}; unbiased for independent years, not proved yet` },
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
   * for ordered regions with many pairs (studies/taper-blup.js, damping-theta.md S36–S37).
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
  function balanceFit(f, data) {
    const { wt, m } = cohortMeans(data), wall = sum(wt);
    const D = sum(wt.map((x, j) => x * (m[j] - f.rates[j]))) / wall;
    const out = Object.assign({}, f, { rates: f.rates.map((x) => x + D), shift: D, balanced: true });
    const W = weightsOf(f);
    if (W) {
      const g = wt.map((x, i) => (x - sum(W.map((d, k) => wt[k] * d[i]))) / wall);
      out.weights = W.map((d) => d.map((x, i) => x + g[i]));
      out.c = out.weights.map((d, j) => d[j]);
      if (f.K) out.levelMSE = out.weights.map((d, j) => linMse(f.K, f.tau2, j, d));
    }
    const off = (t) => !/off-balance/.test(t);
    out.flags = Object.assign({}, f.flags, { offBalance: false });
    out.warnings = (f.warnings || []).filter(off);
    out.notes = (f.notes || []).filter(off);
    out.steps = (f.steps || []).concat([Object.assign({}, BALANCE_STEP, { values: [D], note: `D = ${D >= 0 ? '+' : '−'}${(100 * Math.abs(D)).toFixed(2)}% of the tariff; ` + BALANCE_STEP.note })]);
    return out;
  }

  /** The BLUP on corrBS's K̂, balanced (kept for the tests; on the page it is BLUP with the switch on). */
  function fitBLUPBal(data) { return balanceFit(fitBLUP(data), data); }

  /** A model's fit, balanced when opts.balance (models already balanced on exposures are left alone). */
  function fitWith(id, data, opts) {
    const f = MODELS[id].fit(data);
    return opts && opts.balance && !MODELS[id].balanced ? balanceFit(f, data) : f;
  }

  /**
   * Jackknife MSEP of the variance-credibility fit (Jiang, Lahiri & Wan 2002, Ann. Stat. 30;
   * studies/msep.js), deleting one year at a time (independent years), region means kept:
   *   MSEPⱼ = g₁₂ⱼ(θ̂) − (T−1)/T Σₜ (g₁₂ⱼ(θ̂₋ₜ) − g₁₂ⱼ(θ̂)) + (T−1)/T Σₜ (rateⱼ(θ̂₋ₜ) − rateⱼ(θ̂))².
   * An average-case error over data sets like this one, not an interval for this data set
   * (damping-theta.md, findings S19 and S26). Data only, no tuning.
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
    corr: { name: 'Thesis model with correlation (full K̂, damped)', short: 'corr', fit: (data) => fitCorr(data), ready: true },
    corrT: { name: 'Thesis model with correlation, distance taper ρ̂^|i−j| (ordered regions)', short: 'corr taper', fit: (data) => fitCorr(data, { taper: 'distance' }), ready: true },
    corrC: { name: 'One common covariance — not recommended (unequal volumes)', short: 'common', fit: (data) => fitCorr(data, { common: true }), ready: true, notRecommended: 'finding S4: with unequal volumes one common covariance exceeds the large regions’ noise variance and z explodes' },
    own: { name: 'Own mean only (z = 1)', short: 'own', fit: fitOwn, ready: true, balanced: true },
    pool: { name: 'One tariff for all (z = 0)', short: 'pool', fit: fitPool, ready: true, balanced: true },
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
        { name: 'Wⱼ, β²', formula: F.vcW, badge: 'not proved yet', gap: 'G1', rule: 'if β² ≤ 0, set β² = 0 (then every σ̃ⱼ² below is the pooled σ̂²)', note: 'Wⱼ estimates Var(σ̂ⱼ²) from the yearly terms; β² is the between-region variance of the σⱼ²' },
        { name: 'σ̃ⱼ²', formula: F.vcTilde, badge: 'not proved yet', gap: 'G1', rule: 'ζⱼ = 0 when β² = 0' },
        { name: 'ρ̂', formula: F.vcRho, badge: 'proved', lean: 'Credibility.Model.rhoPooled_unbiased', rule: 'clip ρ̂ to [0, 1) (a value ≥ 1 is set just below 1)', note: 'unbiased for a common ρ with the true σⱼ in the denominator; with σ̃ⱼ plugged in (a ratio), not proved' },
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

  /** A recipe's steps, with the balance step before the premium when opts.balance. */
  function recipeSteps(id, opts) {
    const st = RECIPES[id].steps;
    if (!(opts && opts.balance) || MODELS[id].balanced) return st;
    const k = st.findIndex((x) => x.name === 'premium');
    return k < 0 ? st.concat([BALANCE_STEP]) : st.slice(0, k).concat([BALANCE_STEP], st.slice(k));
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
      taper
        ? { name: 'tapered K̂', formula: F.taper, badge: 'not proved yet', gap: 'G2', varies: true,
          rule: `${F.taperRule}; lowered in steps of 0.05 only if K̂ is not positive definite`,
          note: 'K̂ ≻ 0 for every ρ ∈ [0, 1] is proved when Σ̂ + τ̂²I ≻ 0 (posDef_distTaper_hadamard, ties allowed); the criterion for ρ̂ is a plug-in (G2), with every pair at distance 1 it is the damping study’s rule S3 for the damping factor' }
        : { name: 'damped K̂', formula: F.damped, badge: 'not proved yet', gap: 'G2', varies: true,
          rule: `${F.dampRule}; at most 0.999; lowered in steps of 0.05 only if K̂ is not positive definite (a Cholesky factorisation fails)`,
          note: 'K̂ ≻ 0 for every θ < 1 is proved when Σ̂ is positive semidefinite (posDef_shrinkOffDiag); θ̂ is a plug-in of the best shrinkage of the correlations, signal r̄² against their sampling variance (damping study S3), a heuristic for the rates (G2)' },
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
      out.push(`${k + 1}. ${s.name}: ${s.formula}`);
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
    const bal = !!(opts && opts.balance);
    const r = rng(seed), rn = rng((seed ^ 0x5bd1e995) >>> 0), fl = floorBlend(world);
    const Dstar = fl.K.map((_, j) => blupWeight(fl.K, world.truth.tau2, j));
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
        const raw = MODELS[id].fit(data), f = bal && !MODELS[id].balanced ? balanceFit(raw, data) : raw;
        const e = weightedSE(data, f.rates, levels), g = fe(f.rates, Y), er = weightedSE(data, raw.rates, levels);
        acc[id].rs += er; acc[id].rss += er * er;
        acc[id].s += e; acc[id].ss += e * e; acc[id].f += g; acc[id].ff += g * g; if (f.warnings.length) acc[id].warn++;
        const B = f.rates.map((x, j) => x - br[j]), b2 = wsum(B.map((x) => x * x)), c2 = 2 * wsum(B.map((x, j) => A[j] * x));
        acc[id].b += b2; acc[id].bb += b2 * b2; acc[id].c += c2; acc[id].cc += c2 * c2;
        addBias(acc[id], f.rates, levels);
        const W = weightsOf(f);
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
      if (bal && ids.includes(id) && !MODELS[id].balanced) out[id].raw = { mse: acc[id].rs / n, se: se(acc[id].rs, acc[id].rss) };
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
    return { q, regions, skew, skewSE, power, powerSame, powerSkewBias, link, linkSE };
  }

  /** One draw's data as CSV: one row per region and year, the columns the fit sees. */
  function toCSV(data) {
    const lines = ['region,year,volume,ratio'];
    data.X.forEach((row, j) => row.forEach((x, t) => lines.push(`${j + 1},${t + 1},${+data.w[j][t].toPrecision(10)},${+x.toPrecision(10)}`)));
    return lines.join('\n') + '\n';
  }

  return {
    DEFAULTS, MODELS, FEATURES, F, NOTATION, RECIPES, recipeNotation, recipeText,
    rng, solve, cholesky, makeWorld, noiseFactor, trueK, draw,
    cohortMeans, blend, bestBlendWeights, blendMSE,
    eigSym, blendWeight, blupWeight, linMse, noiseDeltas, dampedBound, correlationPrice, worldPrice, correlationIndicator,
    fitBS, fitOwn, fitPool, fitCorr, fitVC, fitBLUP, fitBLUPTaper, fitBLUPBal, balanceFit, fitWith, recipeSteps, BALANCE_STEP, vcEstimate, jackknifeMSEP, sigmaHat, sigmaHatVar, covTheta, sigmaHatMoments, corrVar, corrTheta, thesisTau, shrinkOffDiag, isPSD, THETAS, distTaper, taperRho, orderedNoise,
    floorBlend, weightedSE, simulate, weightsOf,
    nextVolumes, drawNext, premium, floorForecast, toCSV, noiseDiagnostics, skewLink, lomaxMoments, claimNoise, claimRate,
  };
});
