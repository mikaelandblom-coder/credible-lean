/*
 * Monthly cohort world with a common AR(1) factor, and its MINQUE fit
 * (notes/card-data.md Steps 5 and 7; studies/PLAN.md, Pending: Henderson III fit).
 *
 * One file, run by the page and by the tests under Node (app/monthly.test.js).
 * No dependencies. Kept apart as in engine.js (PLAN.md §1, principle 1):
 *   world — makeWorld(params), covTable(world), draw(world, rng): the truth and one data set.
 *   fit   — fit(data): gets { J, Y, w, X } and nothing else; φ̂ from the data, then MINQUE.
 *
 * Cells are (j, t), cohort j, month t = 12y + m (year y, calendar month m), index p = j·12Y + t.
 * The table (Lean `Factor.shapeTable`, `Factor.covG_zero_eq_shapeTable`):
 *   cov(X_{i t}, X_{j s}) = A_{ij} φ^|t−s| + δ_{ts}(C_{ij} + δ_{ij} s²_i / w_{i t}) + τ² δ_{ij},
 * with A = γλλᵀ. Fixed effects: one mean per cohort and calendar month (`Factor.cohortSeason`).
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Monthly = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // ---------------------------------------------------------------- small helpers

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
    /** Mean 0, variance 1, skewed: the model fixes only two moments. */
    u.skewed = function (k) { return (u.gamma(k) - k) / Math.sqrt(k); };
    return u;
  }

  function solve(A, b) {
    const n = b.length, M = A.map((row, i) => row.slice().concat([b[i]]));
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

  function cholesky(A) {
    const n = A.length, L = A.map(() => new Array(n).fill(0));
    for (let i = 0; i < n; i++) for (let j = 0; j <= i; j++) {
      let s = A[i][j];
      for (let k = 0; k < j; k++) s -= L[i][k] * L[j][k];
      if (i === j) { if (!(s > 0)) return null; L[i][i] = Math.sqrt(s); } else L[i][j] = s / L[j][j];
    }
    return L;
  }

  /** Eigenvalues of a symmetric matrix, ascending (cyclic Jacobi). */
  function eigSym(A) {
    const n = A.length, M = A.map((row) => row.slice());
    for (let sweep = 0; sweep < 100; sweep++) {
      let off = 0;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += M[p][q] * M[p][q];
      if (off < 1e-30) break;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
        if (Math.abs(M[p][q]) < 1e-300) continue;
        const th = (M[q][q] - M[p][p]) / (2 * M[p][q]);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1));
        const c = 1 / Math.sqrt(t * t + 1), s = t * c;
        for (let k = 0; k < n; k++) {
          const a = M[k][p], b = M[k][q];
          M[k][p] = c * a - s * b; M[k][q] = s * a + c * b;
        }
        for (let k = 0; k < n; k++) {
          const a = M[p][k], b = M[q][k];
          M[p][k] = c * a - s * b; M[q][k] = s * a + c * b;
        }
      }
    }
    return M.map((row, i) => row[i]).sort((a, b) => a - b);
  }

  // ---------------------------------------------------------------- world

  const DEFAULTS = {
    J: 4,            // cohorts
    Y: 2,            // years of monthly data
    phi: 0.6,        // AR(1) of the factor
    gamma: 0.02,     // factor variance
    loadSpread: 0.5, // loadings 1 ± spread (cohort pattern)
    c: 0.01,         // shock variance C_jj; correlation cRho off the diagonal
    cRho: 0.3,
    s2: 40,          // process noise per unit volume: s²/w
    tau2: 0.01,      // cohort level
    volume: 'seasonal', // 'seasonal' | 'yearOnly' | 'flat'
    w0: 1000,
    skew: 4,
  };

  function makeWorld(params) {
    const p = Object.assign({}, DEFAULTS, params || {});
    const { J, Y } = p, T = 12 * Y;
    const load = Array.from({ length: J }, (_, j) => 1 + p.loadSpread * (J > 1 ? 2 * j / (J - 1) - 1 : 0));
    const C = Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, j) => (i === j ? p.c : p.c * p.cRho)));
    const s2 = Array.from({ length: J }, (_, j) => p.s2 * (1 + 0.5 * (j % 2)));
    const w = Array.from({ length: J }, (_, j) => Array.from({ length: T }, (_, t) => {
      const m = t % 12, y = Math.floor(t / 12), size = p.w0 * (1 + j);
      if (p.volume === 'flat') return size;
      if (p.volume === 'yearOnly') return size * Math.pow(1.3, y);
      return size * (1 + 0.6 * Math.sin(2 * Math.PI * (m + 3 * j) / 12)) * Math.pow(1.1, y);
    }));
    const season = Array.from({ length: J }, (_, j) => Array.from({ length: 12 }, (_, m) => 1 + 0.2 * Math.cos(2 * Math.PI * (m - j) / 12)));
    const A = load.map((li) => load.map((lj) => p.gamma * li * lj));
    return { J, Y, w, truth: { phi: p.phi, gamma: p.gamma, load, A, C, s2, tau2: p.tau2, season }, skew: p.skew };
  }

  /** The covariance table over the cells (Lean `Factor.shapeTable` with Γ₀ = `Factor.ar1Cal`). */
  function covTable(world) {
    const { J, Y, w } = world, { phi, A, C, s2, tau2 } = world.truth, T = 12 * Y, n = J * T;
    const V = Array.from({ length: n }, () => new Array(n).fill(0));
    for (let i = 0; i < J; i++) for (let t = 0; t < T; t++) for (let j = 0; j < J; j++) for (let s = 0; s < T; s++) {
      let v = A[i][j] * Math.pow(phi, Math.abs(t - s));
      if (t === s) v += C[i][j] + (i === j ? s2[i] / w[i][t] : 0);
      if (i === j) v += tau2;
      V[i * T + t][j * T + s] = v;
    }
    return V;
  }

  /** One data set: season mean plus noise with the table's covariance (skewed innovations). */
  function draw(world, r) {
    const { J, Y, w } = world, T = 12 * Y, V = covTable(world), L = cholesky(V);
    if (!L) throw new Error('table not positive definite');
    const e = V.map(() => r.skewed(world.skew)), X = Array.from({ length: J }, () => new Array(T));
    for (let i = 0; i < J; i++) for (let t = 0; t < T; t++) {
      const p = i * T + t;
      let x = world.truth.season[i][t % 12];
      for (let k = 0; k <= p; k++) x += L[p][k] * e[k];
      X[i][t] = x;
    }
    return { J, Y, w: w.map((row) => row.slice()), X };
  }

  // ---------------------------------------------------------------- fit

  /** The basis tables of `Factor.seasonBasis` (τ² dropped, Finding 27): A_{ij}, C_{ij} (i ≤ j), s²_j. */
  function basis(J, Y, w, phi) {
    const T = 12 * Y, out = [];
    for (let i = 0; i < J; i++) for (let j = i; j < J; j++) out.push({ kind: 'A', i, j });
    for (let i = 0; i < J; i++) for (let j = i; j < J; j++) out.push({ kind: 'C', i, j });
    for (let j = 0; j < J; j++) out.push({ kind: 's', i: j, j });
    // Entry of basis table b at cells (i, t), (j, s).
    const entry = (b, i, t, j, s) => {
      if (b.kind === 's') return i === b.i && j === b.i && t === s ? 1 / w[i][t] : 0;
      if (!((i === b.i && j === b.j) || (i === b.j && j === b.i))) return 0;
      if (b.kind === 'A') return Math.pow(phi, Math.abs(t - s));
      return t === s ? 1 : 0;
    };
    return { list: out, entry, T };
  }

  /**
   * MINQUE with prior W = I given φ (Lean `Model.minqueForms`, `Factor.henderson_season_unbiased`):
   * R = I − D(DᵀD)⁻¹Dᵀ centres each cohort × calendar month class; forms Q_k = R V_k R,
   * H_kl = tr(R V_k R V_l), q_k = (RX)ᵀ V_k (RX); θ̂ = H⁻¹q. Unbiased for A = γλλᵀ, C, s² whatever
   * τ² and the season, when H is nonsingular (`Factor.minque_ar1_two_years_unbiased`).
   */
  function minque(data, phi) {
    const { J, Y, w, X } = data, { list, entry, T } = basis(J, Y, w, phi), n = J * T, K = list.length;
    // Classes (j, m): the months of cohort j with calendar month m.
    const cls = (p) => Math.floor(p / T) * 12 + ((p % T) % 12);
    const size = new Array(J * 12).fill(0);
    for (let p = 0; p < n; p++) size[cls(p)]++;
    const centre = (v) => { // R v
      const s = new Array(J * 12).fill(0);
      for (let p = 0; p < n; p++) s[cls(p)] += v[p];
      return v.map((x, p) => x - s[cls(p)] / size[cls(p)]);
    };
    const x = new Array(n);
    for (let i = 0; i < J; i++) for (let t = 0; t < T; t++) x[i * T + t] = X[i][t];
    const r = centre(x);
    const tables = list.map((b) => {
      const M = Array.from({ length: n }, (_, p) => Array.from({ length: n }, (_, q) =>
        entry(b, Math.floor(p / T), p % T, Math.floor(q / T), q % T)));
      return M;
    });
    // R V R: centre rows, then columns (V and R symmetric).
    const proj = tables.map((M) => {
      const rows = M.map(centre), out = Array.from({ length: n }, () => new Array(n));
      for (let q = 0; q < n; q++) {
        const col = centre(rows.map((row) => row[q]));
        for (let p = 0; p < n; p++) out[p][q] = col[p];
      }
      return out;
    });
    const H = Array.from({ length: K }, () => new Array(K).fill(0)), qv = new Array(K).fill(0);
    for (let k = 0; k < K; k++) {
      for (let l = k; l < K; l++) {
        let s = 0;
        for (let p = 0; p < n; p++) for (let q = 0; q < n; q++) s += proj[k][p][q] * tables[l][p][q];
        H[k][l] = s; H[l][k] = s;
      }
      let s = 0;
      for (let p = 0; p < n; p++) for (let q = 0; q < n; q++) s += r[p] * tables[k][p][q] * r[q];
      qv[k] = s;
    }
    // Rank check on the scaled system H_kl / √(H_kk H_ll): the tables differ in scale (1/w ≪ 1).
    const d = H.map((row, k) => Math.sqrt(Math.max(row[k], 0)));
    const ev = d.some((x) => !(x > 0)) ? [0, 1]
      : eigSym(H.map((row, k) => row.map((x, l) => x / (d[k] * d[l]))));
    const cond = ev[0] / ev[ev.length - 1], singular = !(cond > 1e-10);
    let theta = null;
    if (!singular) theta = solve(H, qv);
    return { list, H, q: qv, cond, singular, theta };
  }

  /** Pooled year-on-year cross-products at lag h over cohort pairs i ≠ j (Lean `Factor.yoy_unbiased_factor`). */
  function yoyPooled(data, h) {
    const { J, Y, X } = data, T = 12 * Y;
    let s = 0, n = 0;
    for (let i = 0; i < J; i++) for (let j = 0; j < J; j++) if (i !== j)
      for (let t = 12; t + h < T; t++) {
        s += (X[i][t] - X[i][t - 12]) * (X[j][t + h] - X[j][t + h - 12]);
        n++;
      }
    return n ? s / n : NaN;
  }

  /** E yoy(h) ∝ 2φʰ − φ^|h−12| − φ^(h+12) under AR(1) (lag h within the year). */
  const yoyShape = (phi, h) => 2 * Math.pow(phi, h) - Math.pow(phi, Math.abs(h - 12)) - Math.pow(phi, h + 12);

  /**
   * φ̂: fit the pooled year-on-year cross-products S(h), h = 1..H, by c·g(φ, h) with
   * g(φ, h) = 2φʰ − φ^|h−12| − φ^(h+12): least squares in c for each φ on a grid, then the best φ.
   * Each S(h) is unbiased for c·g(φ, h) (c = mean λᵢλⱼγ over pairs); φ̂ is a nonlinear function of
   * them, so consistent, not unbiased: not proved.
   */
  function phiHat(data, H) {
    const lags = H || 6, S = [];
    for (let h = 1; h <= lags; h++) S.push(yoyPooled(data, h));
    let best = { phi: NaN, loss: Infinity, c: NaN };
    for (let k = 1; k < 100; k++) {
      const phi = k / 100, g = S.map((_, i) => yoyShape(phi, i + 1));
      const gg = g.reduce((a, x) => a + x * x, 0), gs = g.reduce((a, x, i) => a + x * S[i], 0);
      const c = Math.max(gs / gg, 0), loss = S.reduce((a, x, i) => a + (x - c * g[i]) ** 2, 0);
      if (loss < best.loss) best = { phi, loss, c };
    }
    return { phi: best.phi, c: best.c, S };
  }

  /** Data-side checks named after the Lean results (warnings before solving). */
  function diagnose(data, phi) {
    const { J, Y, w } = data, out = [];
    if (Y < 2) out.push({ code: 'oneYear', text: 'One year of data: under a cohort season no second moment is estimable (Finding 28).', lean: 'Factor.unbiasedMean_cohortSeason_eq_zero' });
    if (Y === 2) for (let j = 0; j < J; j++) {
      const h = Array.from({ length: 12 }, (_, m) => 1 / w[j][m] + 1 / w[j][m + 12]);
      const spread = Math.max(...h) - Math.min(...h);
      if (spread <= 1e-9 * Math.max(...h)) out.push({ code: 'flatVolume', cohort: j, text: `Cohort ${j + 1}: 1/w in year 1 + 1/w in year 2 is the same in every month, so s² trades against C (Finding 29). Report C + s²h/2 for this cohort.`, lean: 'Factor.minque_cohortSeason_det_eq_zero_of_volume' });
    }
    if (phi < 0.05 || phi > 0.95) out.push({ code: 'phiEdge', text: `φ̂ = ${phi.toFixed(2)} is near 0 or 1: the factor repeats with the calendar or is white noise, and is not separated from the season or the shock (Finding 28).`, lean: 'Factor.hendersonMat_cohortSeason_det_eq_zero_of_shape' });
    return out;
  }

  /** The fit: φ̂ from the data, then MINQUE given φ̂. Gets the data table and nothing else. */
  function fit(data, opts) {
    const o = opts || {};
    const ph = o.phi !== undefined ? { phi: o.phi } : phiHat(data);
    const warnings = diagnose(data, ph.phi), mq = minque(data, ph.phi);
    const J = data.J, A = J ? Array.from({ length: J }, () => new Array(J).fill(NaN)) : [];
    const C = A.map((row) => row.slice()), s2 = new Array(J).fill(NaN);
    if (mq.singular) warnings.push({ code: 'singular', text: 'The MINQUE system is singular: the parameters are not all estimable from these data.', lean: 'Model.minque_det_ne_zero_iff' });
    else mq.list.forEach((b, k) => {
      const v = mq.theta[k];
      if (b.kind === 's') s2[b.i] = v;
      else { const M = b.kind === 'A' ? A : C; M[b.i][b.j] = v; M[b.j][b.i] = v; }
    });
    const steps = [
      { name: 'φ̂ from year-on-year cross-products', value: ph.phi, badge: 'not proved yet', lean: 'Factor.yoy_unbiased_factor' },
      { name: 'MINQUE for (γλλᵀ, C, s²) given φ̂, τ² dropped', badge: 'proved', lean: 'Factor.minque_ar1_two_years_unbiased' },
    ];
    return { phi: ph.phi, A, C, s2, singular: mq.singular, cond: mq.cond, warnings, steps };
  }

  return { DEFAULTS, rng, solve, cholesky, eigSym, makeWorld, covTable, draw, basis, minque, yoyPooled, yoyShape, phiHat, diagnose, fit };
});
