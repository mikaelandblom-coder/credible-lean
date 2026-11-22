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

  /** Eigen-decomposition of a symmetric matrix (cyclic Jacobi): values and unit vectors (columns of V). */
  function eigSymVec(A) {
    const n = A.length, M = A.map((row) => row.slice()), V = A.map((_, i) => A.map((__, j) => (i === j ? 1 : 0)));
    for (let sweep = 0; sweep < 100; sweep++) {
      let off = 0;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += M[p][q] * M[p][q];
      if (off < 1e-30) break;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
        if (Math.abs(M[p][q]) < 1e-300) continue;
        const th = (M[q][q] - M[p][p]) / (2 * M[p][q]);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1));
        const c = 1 / Math.sqrt(t * t + 1), sn = t * c;
        for (let k = 0; k < n; k++) { const a = M[k][p], b = M[k][q]; M[k][p] = c * a - sn * b; M[k][q] = sn * a + c * b; }
        for (let k = 0; k < n; k++) { const a = M[p][k], b = M[q][k]; M[p][k] = c * a - sn * b; M[q][k] = sn * a + c * b; }
        for (let k = 0; k < n; k++) { const a = V[k][p], b = V[k][q]; V[k][p] = c * a - sn * b; V[k][q] = sn * a + c * b; }
      }
    }
    return { values: M.map((row, i) => row[i]), V };
  }

  /** The nearest PSD matrix in the Frobenius norm: negative eigenvalues set to 0. */
  function clipPSD(T) {
    const { values, V } = eigSymVec(T), n = T.length;
    return T.map((_, i) => T.map((__, j) => {
      let s = 0;
      for (let k = 0; k < n; k++) if (values[k] > 0) s += values[k] * V[i][k] * V[j][k];
      return s;
    }));
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
    indexYears: 0,   // years of an external index of the factor before the data (0 = no index)
    indexNoise: 1,   // the index's own noise variance, as a multiple of γ
  };

  function makeWorld(params) {
    const p = Object.assign({}, DEFAULTS, params || {});
    const { J, Y } = p, T = 12 * Y;
    const load = Array.from({ length: J }, (_, j) => 1 + p.loadSpread * (J > 1 ? 2 * j / (J - 1) - 1 : 0));
    const C = Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, j) => (i === j ? p.c : p.c * p.cRho)));
    const s2 = Array.from({ length: J }, (_, j) => p.s2 * (1 + 0.5 * (j % 2)));
    // Volumes over the data and the 12 months after (the target's months, unseen by the fit).
    const wAll = Array.from({ length: J }, (_, j) => Array.from({ length: T + 12 }, (_, t) => {
      const m = t % 12, y = Math.floor(t / 12), size = p.w0 * (1 + j);
      if (p.volume === 'flat') return size;
      if (p.volume === 'yearOnly') return size * Math.pow(1.3, y);
      return size * (1 + 0.6 * Math.sin(2 * Math.PI * (m + 3 * j) / 12)) * Math.pow(1.1, y);
    }));
    const w = wAll.map((row) => row.slice(0, T)), wFuture = wAll.map((row) => row.slice(T));
    const season = Array.from({ length: J }, (_, j) => Array.from({ length: 12 }, (_, m) => 1 + 0.2 * Math.cos(2 * Math.PI * (m - j) / 12)));
    const A = load.map((li) => load.map((lj) => p.gamma * li * lj));
    const index = p.indexYears > 0
      ? { years: p.indexYears, noise: p.indexNoise * p.gamma, season: Array.from({ length: 12 }, (_, m) => 1 + 0.3 * Math.cos(2 * Math.PI * (m - 6) / 12)) }
      : null;
    return { J, Y, w, wFuture, truth: { phi: p.phi, gamma: p.gamma, load, A, C, s2, tau2: p.tau2, season }, index, skew: p.skew };
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
  /**
   * One data set: season mean plus noise with the table's covariance, built from its parts
   * (skewed innovations: the model fixes only two moments): the factor path f with
   * cov(f_t, f_s) = γφ^|t−s| (stationary AR(1)), λᵢf_t, the month's shock with covariance C,
   * process noise s²ᵢ/wᵢₜ and the cohort level τ². With an index (world.index), also
   * I_t = season + f_t + noise over indexYears + Y years ending with the data, the same path f:
   * an external series that follows the factor (e.g. travel demand), longer than the data.
   */
  const cholCache = new WeakMap();
  function draw(world, r) { return drawCells(world, r, 0).data; }

  /**
   * One data set and what the fit must predict: the next 12 months of every cohort (same factor
   * path, shock, noise and level), with their volumes `world.wFuture`. The target of cohort j is
   * Y_j = Σₜ bₜX_{jt}, bₜ = 1/12 on those months (Lean `Factor.ell`, `Factor.var`). The fit
   * gets `data` only.
   */
  function drawFuture(world, r) {
    const { data, future } = drawCells(world, r, 12);
    return { data, future, target: future.map((row) => row.reduce((a, x) => a + x, 0) / 12) };
  }

  function drawCells(world, r, h) {
    const { J, Y, truth, index } = world, T = 12 * Y, k = world.skew;
    const w = world.w.map((row, j) => row.concat(world.wFuture[j].slice(0, h)));
    let LC = cholCache.get(world);
    if (!LC) { LC = cholesky(truth.C); if (LC) cholCache.set(world, LC); }
    if (!LC) throw new Error('C not positive definite');
    const pre = index ? 12 * index.years : 0, n = pre + T + h, g = Math.sqrt(truth.gamma), phi = truth.phi;
    const f = new Array(n);
    f[0] = g * r.skewed(k);
    for (let t = 1; t < n; t++) f[t] = phi * f[t - 1] + g * Math.sqrt(1 - phi * phi) * r.skewed(k);
    const level = truth.season.map(() => Math.sqrt(truth.tau2) * r.skewed(k));
    const X = Array.from({ length: J }, () => new Array(T + h));
    for (let t = 0; t < T + h; t++) {
      const e = LC.map(() => r.skewed(k));
      for (let i = 0; i < J; i++) {
        let shock = 0;
        for (let m = 0; m <= i; m++) shock += LC[i][m] * e[m];
        X[i][t] = truth.season[i][t % 12] + truth.load[i] * f[pre + t] + shock
          + Math.sqrt(truth.s2[i] / w[i][t]) * r.skewed(k) + level[i];
      }
    }
    const data = { J, Y, w: world.w.map((row) => row.slice()), X: X.map((row) => row.slice(0, T)) };
    if (index) data.index = f.slice(0, pre + T).map((x, t) => index.season[t % 12] + x + Math.sqrt(index.noise) * r.skewed(k));
    return { data, future: X.map((row) => row.slice(T)) };
  }


  // ---------------------------------------------------------------- fit

  /** The basis tables of `Factor.seasonBasis` (τ² dropped, Finding 27): A_{ij}, C_{ij} (i ≤ j), s²_j. */
  function basis(J, Y, w, phi) {
    const T = w[0].length, out = [];
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
   * Computed in Kronecker form: every basis table is E_ab ⊗ M (M = Φ, I or diag(1/w_j), T × T) and
   * R = I_J ⊗ P, so H_kl = tr(E_ab E_cd)·tr(PMPN) and q_k = r_aᵀ M r_b (twice off the diagonal).
   * Same numbers as `minqueDense`, at T × T cost; `prepare` caches the φ-free part for the profile.
   */
  function prepare(data) {
    // T need not be a multiple of 12 (a rolling origin cuts the data at any month): each calendar
    // month m is centred on its own count of months.
    const { J, Y, w, X } = data, T = X[0].length, cnt = new Array(12).fill(0);
    for (let t = 0; t < T; t++) cnt[t % 12]++;
    const P = Array.from({ length: T }, (_, t) => Array.from({ length: T }, (_, s) => (t === s ? 1 : 0) - (t % 12 === s % 12 ? 1 / cnt[t % 12] : 0)));
    const r = X.map((row) => {
      const s = new Array(12).fill(0);
      row.forEach((x, t) => { s[t % 12] += x; });
      return row.map((x, t) => x - s[t % 12] / cnt[t % 12]);
    });
    // Diagonal factors (I for C, diag(1/w_j) for s²_j): tr(P D_a P D_b) = Σ_tv P_tv² a_v b_t.
    const diag = [new Array(T).fill(1)].concat(w.map((row) => row.map((x) => 1 / x)));
    const pdp = diag.map((d) => P.map((row) => row.reduce((s, x, v) => s + x * x * d[v], 0)));
    const trDD = diag.map((_, a) => diag.map((d) => d.reduce((s, x, t) => s + pdp[a][t] * x, 0)));
    const qd = (d, a, b) => { let s = 0; for (let t = 0; t < T; t++) s += r[a][t] * d[t] * r[b][t]; return s; };
    return { J, Y, T, w, P, r, diag, trDD, qd };
  }

  function minque(data, phi, prep) {
    const pr = prep || prepare(data), { J, Y, T, w, r, diag, trDD, qd } = pr, { list } = basis(J, Y, w, phi);
    const F = Array.from({ length: T }, (_, t) => Array.from({ length: T }, (_, s) => Math.pow(phi, Math.abs(t - s))));
    // PFP and the traces with F.
    const PF = pr.P.map((row) => F[0].map((_, u) => { let s = 0; for (let v = 0; v < T; v++) s += row[v] * F[v][u]; return s; }));
    const PFP = PF.map((row) => pr.P[0].map((_, u) => { let s = 0; for (let v = 0; v < T; v++) s += row[v] * pr.P[v][u]; return s; }));
    let trFF = 0;
    for (let t = 0; t < T; t++) for (let u = 0; u < T; u++) trFF += PFP[t][u] * F[u][t];
    const trFD = diag.map((d) => { let s = 0; for (let t = 0; t < T; t++) s += PFP[t][t] * d[t]; return s; });
    // Index of a table's T × T factor: 'F', or a diagonal (0 = I for C, 1 + j for s²_j).
    const fac = (b) => (b.kind === 'A' ? -1 : b.kind === 'C' ? 0 : 1 + b.i);
    const tr2 = (a, b) => (a < 0 ? (b < 0 ? trFF : trFD[b]) : b < 0 ? trFD[a] : trDD[a][b]);
    const pair = (b, c) => (b.i === b.j ? (c.i === c.j && b.i === c.i ? 1 : 0) : (c.i !== c.j && b.i === c.i && b.j === c.j ? 2 : 0));
    const H = list.map((b) => list.map((c) => { const f = pair(b, c); return f ? f * tr2(fac(b), fac(c)) : 0; }));
    const qv = list.map((b) => {
      let s;
      if (b.kind === 'A') { s = 0; for (let t = 0; t < T; t++) for (let u = 0; u < T; u++) s += r[b.i][t] * F[t][u] * r[b.j][u]; }
      else s = qd(diag[fac(b)], b.i, b.j);
      return b.i === b.j ? s : 2 * s;
    });
    return finish(list, H, qv);
  }

  /** Rank check and solve, shared by both MINQUE versions. */
  function finish(list, H, qv) {
    // Rank check on the scaled system H_kl / √(H_kk H_ll): the tables differ in scale (1/w ≪ 1).
    const d = H.map((row, k) => Math.sqrt(Math.max(row[k], 0)));
    const ev = d.some((x) => !(x > 0)) ? [0, 1]
      : eigSym(H.map((row, k) => row.map((x, l) => x / (d[k] * d[l]))));
    const cond = ev[0] / ev[ev.length - 1], singular = !(cond > 1e-10);
    let theta = null;
    if (!singular) theta = solve(H, qv);
    return { list, H, q: qv, cond, singular, theta };
  }

  /**
   * Dense reference MINQUE (n × n tables), kept for the test of `minque`. MINQUE with prior W = I given φ (Lean `Model.minqueForms`, `Factor.henderson_season_unbiased`):
   * R = I − D(DᵀD)⁻¹Dᵀ centres each cohort × calendar month class; forms Q_k = R V_k R,
   * H_kl = tr(R V_k R V_l), q_k = (RX)ᵀ V_k (RX); θ̂ = H⁻¹q. Unbiased for A = γλλᵀ, C, s² whatever
   * τ² and the season, when H is nonsingular (`Factor.minque_ar1_two_years_unbiased`).
   */
  function minqueDense(data, phi) {
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
    return finish(list, H, qv);
  }

  /**
   * MINQUE constrained to valid tables: γλλᵀ ⪰ 0, C ⪰ 0, s² ≥ 0. MINQUE given φ minimises
   * θᵀHθ − 2qᵀθ (least squares of rrᵀ on the RVₖR), so the constrained fit minimises the same over
   * the cone, i.e. projects the unbiased θ̂ onto the cone in the H-metric (Pukelsheim 1981: a
   * projection in parameter space; Hartung 1981). Within one block (A, C or s²) H is a constant
   * times the Frobenius weights (1 on the diagonal, 2 off it), so a block update is the nearest
   * PSD matrix to the block's unconstrained target (eigenvalues clipped at 0), and for s² a clip at
   * 0. Cycling the blocks converges to the minimum (a convex quadratic over a product of convex
   * sets). Biased (unbiased nonnegative estimators do not exist in general, LaMotte 1973); not proved.
   */
  function constrainPSD(mq, J) {
    const { list, H, q } = mq, K = list.length;
    const blocks = ['A', 'C', 's'].map((kind) => list.map((b, k) => (b.kind === kind ? k : -1)).filter((k) => k >= 0));
    const theta = mq.theta ? mq.theta.slice() : new Array(K).fill(0);
    const obj = (th) => { let v = 0; for (let k = 0; k < K; k++) { let h = 0; for (let l = 0; l < K; l++) h += H[k][l] * th[l]; v += th[k] * h - 2 * q[k] * th[k]; } return v; };
    let prev = Infinity, sweeps = 0;
    for (; sweeps < 5000; sweeps++) {
      blocks.forEach((ks, bi) => {
        const inB = new Set(ks);
        const T = ks.map((k) => { let g = q[k]; for (let l = 0; l < K; l++) if (!inB.has(l)) g -= H[k][l] * theta[l]; return g / H[k][k]; });
        if (bi === 2) { ks.forEach((k, a) => { theta[k] = Math.max(T[a], 0); }); return; }
        const M = Array.from({ length: J }, () => new Array(J).fill(0));
        ks.forEach((k, a) => { const b = list[k]; M[b.i][b.j] = T[a]; M[b.j][b.i] = T[a]; });
        const P = clipPSD(M);
        ks.forEach((k) => { const b = list[k]; theta[k] = P[b.i][b.j]; });
      });
      const v = obj(theta);
      if (prev - v <= 1e-12 * Math.abs(v)) break;
      prev = v;
    }
    return { theta, sweeps, objective: obj(theta) };
  }

  /** Pooled year-on-year cross-products at lag h over cohort pairs i ≠ j (Lean `Factor.yoy_unbiased_factor`). */
  function yoyPooled(data, h) {
    const { J, X } = data, T = X[0].length;
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

  /**
   * φ̂ by profiling the MINQUE fit: for each φ, MINQUE given φ is the least-squares fit of the
   * centred cross-products rrᵀ by Σ θ_k R V_k(φ) R (normal equations Hθ = q), so its residual is
   * ‖rrᵀ‖² − qᵀθ̂(φ). φ̂ minimises it: the grid 0.02, …, 0.98, then golden section around the best.
   * Returns φ̂ and the curve of the explained share qᵀθ̂ / (rᵀr)² (1 = perfect fit). Not proved;
   * distribution-free (no likelihood). A plug-in REML profile was tried and fails: θ̂(φ) is
   * unbiased, so the fitted table is often not positive definite.
   */
  function phiProfile(data) {
    const pr = prepare(data);
    let rr = 0;
    pr.r.forEach((row) => row.forEach((x) => { rr += x * x; }));
    const share = (phi) => {
      const mq = minque(data, phi, pr);
      return mq.singular ? NaN : mq.q.reduce((a, x, k) => a + x * mq.theta[k], 0) / (rr * rr);
    };
    const curve = [];
    for (let k = 1; k < 50; k++) curve.push({ phi: k / 50, share: share(k / 50) });
    const ok = curve.filter((c) => Number.isFinite(c.share));
    if (!ok.length) return { phi: NaN, curve };
    let best = ok.reduce((a, c) => (c.share > a.share ? c : a));
    let lo = Math.max(best.phi - 0.02, 0.001), hi = Math.min(best.phi + 0.02, 0.999);
    const g = (Math.sqrt(5) - 1) / 2;
    let x1 = hi - g * (hi - lo), x2 = lo + g * (hi - lo), f1 = share(x1), f2 = share(x2);
    for (let it = 0; it < 20; it++) {
      if (!(f1 <= f2)) { hi = x2; x2 = x1; f2 = f1; x1 = hi - g * (hi - lo); f1 = share(x1); }
      else { lo = x1; x1 = x2; f1 = f2; x2 = lo + g * (hi - lo); f2 = share(x2); }
    }
    const xm = (lo + hi) / 2, fm = share(xm);
    if (fm > best.share) best = { phi: xm, share: fm };
    return { phi: best.phi, share: best.share, curve };
  }

  /**
   * φ̂ from the external index alone. Remove its calendar-month means, then fit I_t = f_t + e_t
   * (f AR(1) with variance γ, e white noise with variance qγ) by the Gaussian quasi-likelihood
   * (Kalman filter, γ concentrated out, grid over φ and q). Gaussian only as an estimating
   * equation: it uses second moments and stays consistent for φ whatever the distribution, so
   * the model keeps its two-moment assumption. Not proved. Tried first: the least-squares fit
   * of the autocovariances S(h) ≈ γφʰ (the idea of `Factor.ar1_identified`); with index noise
   * the lag ratio is noisy (RMSE 0.25 against 0.19 here at 10 years, φ = 0.6).
   */
  function phiIndex(data) {
    const x = data.index, n = x.length, mean = new Array(12).fill(0), cnt = new Array(12).fill(0);
    x.forEach((v, t) => { mean[t % 12] += v; cnt[t % 12]++; });
    const d = x.map((v, t) => v - mean[t % 12] / cnt[t % 12]);
    const ll = (phi, q) => {
      let a = 0, P = 1, ss = 0, ldet = 0;
      for (let t = 0; t < n; t++) {
        const F = P + q, v = d[t] - a, K = P / F;
        ss += v * v / F; ldet += Math.log(F);
        a = phi * (a + K * v); P = phi * phi * P * (1 - K) + 1 - phi * phi;
      }
      return -0.5 * (n * Math.log(ss / n) + ldet);
    };
    let best = { phi: NaN, q: NaN, ll: -Infinity };
    for (let k = 1; k < 100; k++) for (let j = -12; j <= 12; j++) {
      const phi = k / 100, q = Math.pow(2, j / 2), v = ll(phi, q);
      if (v > best.ll) best = { phi, q, ll: v };
    }
    return best;
  }

  /** The data as CSV: one row per cohort and month (then the index, if any), the columns the fit sees. */
  function toCSV(data) {
    const { J, Y, w, X } = data, lines = ['cohort,year,month,volume,ratio'];
    for (let j = 0; j < J; j++) for (let t = 0; t < 12 * Y; t++)
      lines.push(`${j + 1},${Math.floor(t / 12) + 1},${(t % 12) + 1},${+w[j][t].toPrecision(10)},${+X[j][t].toPrecision(10)}`);
    if (data.index) { // the external index: rows with cohort "index", no volume; years ≤ 0 precede the data
      const pre = data.index.length - 12 * Y;
      data.index.forEach((x, t) => lines.push(`index,${Math.floor((t - pre) / 12) + 1},${(t % 12) + 1},,${+x.toPrecision(10)}`));
    }
    return lines.join('\n') + '\n';
  }

  // ---------------------------------------------------------------- the H-norm check (world side)

  /** The true parameters in the order of a basis list: A_ij, C_ij (i ≤ j), s²_j. Uses the truth. */
  function truthTheta(world, list) {
    const t = world.truth;
    return list.map((b) => (b.kind === 's' ? t.s2[b.i] : t[b.kind][b.i][b.j]));
  }

  /**
   * `Credibility.ConeProjection.hsq_proj_add_le` for one draw: with p the H-projection of the
   * unbiased θ̂ onto the valid tables (a convex set containing the true θ),
   *   ‖p − θ‖²_H + ‖θ̂ − p‖²_H ≤ ‖θ̂ − θ‖²_H,   ‖v‖²_H = vᵀHv, H the MINQUE matrix.
   * Returns the three terms and the slack ‖θ̂ − θ‖²_H − ‖p − θ‖²_H − ‖θ̂ − p‖²_H (≥ 0 up to the
   * solver's tolerance). Needs a fit with `psd: true`. Holds for any φ̂ and any estimate.
   */
  function hNormCheck(world, f) {
    if (!f.minq || !f.minq.proj) return null;
    const { list, H, thetaHat, proj } = f.minq, th = truthTheta(world, list);
    const hsq = (v) => v.reduce((a, x, k) => a + x * H[k].reduce((b, y, l) => b + y * v[l], 0), 0);
    const unbiased = hsq(thetaHat.map((x, k) => x - th[k])), projected = hsq(proj.map((x, k) => x - th[k]));
    const moved = hsq(thetaHat.map((x, k) => x - proj[k]));
    return { unbiased, projected, moved, slack: unbiased - projected - moved };
  }

  // ---------------------------------------------------------------- the premium: next 12 months

  /**
   * The best linear unbiased predictor of every cohort's next-12-month mean, Y_j = Σₜ bₜX_{jt}
   * with bₜ = 1/12 (Lean `Factor.blup_season_optimal`, `Core.blup`), for the tables
   * { phi, A, C, s2 } (fitted or true) and the cohort × calendar month season as fixed effects:
   *   d* = K⁻¹ℓ + K⁻¹X(XᵀK⁻¹X)⁻¹(x₀ − XᵀK⁻¹ℓ),  x₀ = 1/12 on cohort j's twelve month columns,
   *   ℓ_(i,t) = A_ij Σ_{t'} b_{t'} φ^(t'−t) over the future months (`Factor.ell_apply_of_future`).
   * τ² is left out: the cohort level lies in the span of the season columns, so the predictor
   * does not depend on it (tested). With `wFuture` it also returns the exact MSE of each weight
   * vector under these tables, dᵀKd − 2dᵀℓ + v (`Factor.predMse_blup`). Returns null when K is not
   * positive definite (possible for unbiased tables).
   */
  function predictor(J, Y, w, tab, wFuture) {
    const T = w[0].length, n = J * T, q = 12 * J, { phi, A, C, s2 } = tab;
    const pw = Array.from({ length: T + 12 }, (_, k) => Math.pow(phi, k));
    const cl = Int32Array.from({ length: n }, (_, p) => Math.floor(p / T) * 12 + ((p % T) % 12)); // season column of cell p
    const K = Array.from({ length: n }, () => new Array(n).fill(0));
    for (let i = 0; i < J; i++) for (let t = 0; t < T; t++) for (let j = 0; j < J; j++) for (let s = 0; s < T; s++) {
      let v = A[i][j] * pw[Math.abs(t - s)];
      if (t === s) v += C[i][j] + (i === j ? s2[i] / w[i][t] : 0);
      K[i * T + t][j * T + s] = v;
    }
    // Cholesky K = LLᵀ, L stored by rows in one flat array (speed: the rolling origin calls this often).
    const L = new Float64Array(n * n);
    for (let i = 0; i < n; i++) {
      const Ki = K[i], ri = i * n;
      for (let j = 0; j <= i; j++) {
        let sum = Ki[j];
        const rj = j * n;
        for (let k = 0; k < j; k++) sum -= L[ri + k] * L[rj + k];
        if (i === j) { if (!(sum > 0)) return null; L[ri + i] = Math.sqrt(sum); } else L[ri + j] = sum / L[rj + j];
      }
    }
    const sol = (b) => { // K⁻¹b by the Cholesky factor
      const y = Float64Array.from(b);
      for (let i = 0; i < n; i++) { const ri = i * n; let v = y[i]; for (let k = 0; k < i; k++) v -= L[ri + k] * y[k]; y[i] = v / L[ri + i]; }
      for (let i = n - 1; i >= 0; i--) { let v = y[i]; for (let k = i + 1; k < n; k++) v -= L[k * n + i] * y[k]; y[i] = v / L[i * n + i]; }
      return y;
    };
    const Xt = (v) => { const out = new Array(q).fill(0); for (let p = 0; p < n; p++) out[cl[p]] += v[p]; return out; };
    const KiX = Array.from({ length: q }, (_, c) => sol(Array.from({ length: n }, (__, p) => (cl[p] === c ? 1 : 0)))); // columns of K⁻¹X
    const G = KiX.map(Xt); // XᵀK⁻¹X
    const futB = (t) => { let s = 0; for (let u = T; u < T + 12; u++) s += pw[u - t] / 12; return s; };
    const weights = [], mse = [];
    for (let j0 = 0; j0 < J; j0++) {
      const ell = Array.from({ length: n }, (_, p) => A[Math.floor(p / T)][j0] * futB(p % T));
      const Kl = sol(ell), x0 = Array.from({ length: q }, (_, c) => (Math.floor(c / 12) === j0 ? 1 / 12 : 0));
      const rv = Xt(Kl).map((x, c) => x0[c] - x), g = solve(G, rv);
      const d = Kl.map((x, p) => x + KiX.reduce((s, a, c) => s + a[p] * g[c], 0));
      weights.push(d);
      if (wFuture) {
        let v = 0;
        for (let u = 0; u < 12; u++) for (let u2 = 0; u2 < 12; u2++) v += A[j0][j0] * Math.pow(phi, Math.abs(u - u2)) / 144;
        for (let u = 0; u < 12; u++) v += (C[j0][j0] + s2[j0] / wFuture[j0][u]) / 144;
        let dKd = 0;
        for (let p = 0; p < n; p++) { let s = 0; for (let p2 = 0; p2 < n; p2++) s += K[p][p2] * d[p2]; dKd += d[p] * s; }
        mse.push(dKd - 2 * d.reduce((s, x, p) => s + x * ell[p], 0) + v);
      }
    }
    const predict = (X) => weights.map((d) => { let s = 0; for (let p = 0; p < n; p++) s += d[p] * X[Math.floor(p / T)][p % T]; return s; });
    return { weights, mse, predict };
  }

  /**
   * Cohorts whose fitted ŝⱼ² is 0 (clipped by `constrainPSD`). With every ŝⱼ² > 0 the fitted
   * table K̂ is positive definite for any valid Â, Ĉ (`Factor.tableK_posDef`); with some ŝⱼ² = 0
   * that guarantee is gone (Finding 30), and K̂ is singular for sure when also Âⱼⱼ = Ĉⱼⱼ = 0
   * (`Factor.tableK_not_posDef`: a cell of variance zero). Data side: uses the fit only.
   */
  function sZeroCohorts(f) { return f.s2.map((x, j) => (x === 0 ? j : -1)).filter((j) => j >= 0); }
  function zeroVarianceCohorts(f) { return sZeroCohorts(f).filter((j) => f.A[j][j] === 0 && f.C[j][j] === 0); }

  /** The naive premium: each cohort's mean over its last 12 months (the season is then whole). */
  const lastYear = (data) => data.X.map((row) => row.slice(-12).reduce((a, x) => a + x, 0) / 12);

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

  /**
   * The fit: φ̂ from the data, then MINQUE given φ̂. Gets the data table and nothing else.
   * opts.phiMethod: 'profile' (default), 'moment' (year-on-year cross-products) or 'index' (the
   * external index, when the data carry one); opts.phi fixes φ (the oracle, for comparison only).
   * opts.psd: constrain the tables to be valid covariances (`constrainPSD`); default unbiased.
   */
  function fit(data, opts) {
    const o = opts || {};
    let method = o.phi !== undefined ? 'given' : o.phiMethod || 'profile';
    const noIndex = method === 'index' && !data.index;
    if (noIndex) method = 'profile';
    const ph = method === 'given' ? { phi: o.phi } : method === 'moment' ? phiHat(data)
      : method === 'index' ? phiIndex(data) : phiProfile(data);
    const warnings = diagnose(data, ph.phi);
    if (noIndex) warnings.unshift({ code: 'noIndex', text: 'No index in the data: φ̂ by profiling instead.' });
    const mq = Number.isFinite(ph.phi) ? minque(data, ph.phi) : { singular: true, cond: NaN };
    const J = data.J, A = J ? Array.from({ length: J }, () => new Array(J).fill(NaN)) : [];
    const C = A.map((row) => row.slice()), s2 = new Array(J).fill(NaN);
    if (mq.singular) warnings.push({ code: 'singular', text: 'The MINQUE system is singular: the parameters are not all estimable from these data.', lean: 'Model.minque_det_ne_zero_iff' });
    let proj = null;
    if (!mq.singular) {
      const th = o.psd ? constrainPSD(mq, J).theta : mq.theta;
      if (o.psd) proj = th;
      mq.list.forEach((b, k) => {
      const v = th[k];
      if (b.kind === 's') s2[b.i] = v;
      else { const M = b.kind === 'A' ? A : C; M[b.i][b.j] = v; M[b.j][b.i] = v; }
      });
    }
    const phiStep = method === 'given'
      ? { name: 'φ given (oracle: the true value, not a fit)', value: ph.phi, badge: 'not proved yet' }
      : method === 'index'
        ? { name: `φ̂ from the external index (${data.index.length} months)`, value: ph.phi, badge: 'not proved yet' }
      : method === 'moment'
        ? { name: 'φ̂ from year-on-year cross-products', value: ph.phi, badge: 'not proved yet', lean: 'Factor.yoy_unbiased_factor' }
        : { name: 'φ̂ by profiling the MINQUE fit (least squares over φ)', value: ph.phi, badge: 'not proved yet' };
    const steps = [
      phiStep,
      { name: 'MINQUE for (γλλᵀ, C, s²) given φ̂, τ² dropped', badge: 'proved', lean: 'Factor.minque_ar1_two_years_unbiased' },
    ];
    if (o.psd) steps.push({ name: 'Constrained to valid tables (γλλᵀ ⪰ 0, C ⪰ 0, s² ≥ 0): projection in the MINQUE metric', badge: 'proved', lean: 'ConeProjection.integral_hsq_proj_le' });
    // The MINQUE system and both parameter vectors, for the H-norm check (`hNormCheck`).
    const minq = mq.singular ? null : { list: mq.list, H: mq.H, thetaHat: mq.theta, proj };
    return { phi: ph.phi, phiMethod: method, curve: ph.curve, A, C, s2, singular: mq.singular, cond: mq.cond, warnings, steps, minq };
  }


  // ---------------------------------------------------------------- comparing fits on data (card-data Step 7b)

  /** The data up to month t0 (exclusive): what a fit made at origin t0 may see. Index cut at the same month. */
  function truncate(data, t0) {
    const T = data.X[0].length, out = { J: data.J, Y: t0 / 12, w: data.w.map((row) => row.slice(0, t0)), X: data.X.map((row) => row.slice(0, t0)) };
    if (data.index) out.index = data.index.slice(0, data.index.length - (T - t0));
    return out;
  }

  /**
   * The fits a rolling origin can compare (each gets the truncated data only, except the oracle):
   *   last     — each cohort's mean over its last 12 months (no model);
   *   moment   — φ̂ from year-on-year cross-products, valid MINQUE tables, the BLUP (`predictor`);
   *   profile  — the same with φ̂ by profiling (slow: about 70 MINQUE solves per origin);
   *   index    — φ̂ from the external index (needs one);
   *   oracle   — the BLUP with the true tables (a reference, not a fit: it uses the truth).
   */
  const ROLL_FITS = {
    last: 'Last-12-month mean',
    moment: 'BLUP, φ by year-on-year',
    profile: 'BLUP, φ by profile',
    index: 'BLUP, φ from the index',
    oracle: 'BLUP, true tables (oracle)',
  };

  /**
   * Whether a valid fitted table (Â, Ĉ ⪰ 0, ŝ² ≥ 0) gives a singular K̂ = Â⊗Φ + Ĉ⊗I + diag(ŝ²/w).
   * With Z the cohorts whose ŝⱼ² = 0: a combination of cells with variance zero lives on Z, and
   * each month's slice lies in null(Â_ZZ) ∩ null(Ĉ_ZZ) (Φ ≻ 0), so K̂ is singular iff Â_ZZ + Ĉ_ZZ
   * is (argued here, not proved in Lean; `Factor.tableK_posDef` is Z = ∅, `Factor.tableK_not_posDef`
   * a one-cohort Z with Âⱼⱼ = Ĉⱼⱼ = 0; Finding 30). Rounding can let the Cholesky of a singular
   * K̂ pass, and the BLUP then explodes, so the rolling origin checks this first (relative
   * tolerance 1e-10 on the eigenvalues of Â_ZZ + Ĉ_ZZ: a numerical zero, not a tuning knob).
   */
  function degenerateTable(tab) {
    const Z = tab.s2.map((x, j) => (x === 0 ? j : -1)).filter((j) => j >= 0);
    if (!Z.length) return false;
    const M = Z.map((i) => Z.map((j) => tab.A[i][j] + tab.C[i][j]));
    const ev = eigSym(M), top = Math.max(...tab.A.map((row, j) => row[j] + tab.C[j][j]), 0);
    return !(ev[0] > 1e-10 * top);
  }

  /**
   * One fit's predictions of every cohort's next-12-month mean from `sub`; falls back to `last`
   * (flagged) when the fit is singular, some ŝⱼ² is clipped to 0, or K̂ is not positive definite.
   */
  function rollPredict(key, sub, world) {
    const last = () => ({ pred: lastYear(sub), fallback: key !== 'last' });
    if (key === 'last') return { pred: lastYear(sub), fallback: false };
    let tab;
    if (key === 'oracle') {
      const t = world.truth;
      tab = { phi: t.phi, A: t.A, C: t.C, s2: t.s2 };
    } else {
      const f = fit(sub, { phiMethod: key, psd: true });
      if (f.singular || f.phiMethod !== key) return last();
      tab = { phi: f.phi, A: f.A, C: f.C, s2: f.s2 };
      if (degenerateTable(tab)) return last();
    }
    const P = predictor(sub.J, sub.Y, sub.w, tab);
    return P ? { pred: P.predict(sub.X), fallback: false } : last();
  }

  /**
   * Rolling origin, no look-ahead (card-data Step 7b; Tashman 2000). For every origin t0 = burn,
   * burn + step, …, T − 12, each fit sees months < t0 only (parameters, φ, season and K̂ refitted),
   * predicts each cohort's mean over months t0, …, t0 + 11, and is scored by the squared error,
   * exposure-weighted over cohorts: L(t0) = Σⱼ Wⱼ (Ŷⱼ − Yⱼ)² / Σⱼ Wⱼ, Wⱼ the cohort's volume over
   * the 12 target months (squared error is consistent for the mean, Gneiting 2011).
   * opts: { fits: keys of ROLL_FITS, burn (months, default 60), step (default 1), world (oracle only) }.
   * Returns the origins, the pooled loss per fit and origin, per-cohort squared errors and the
   * number of fallbacks per fit.
   */
  function rollingOrigin(data, opts) {
    const o = opts || {}, T = data.X[0].length, J = data.J, burn = o.burn || 60, step = o.step || 1, keys = o.fits || ['last', 'moment'];
    const origins = [];
    for (let t0 = burn; t0 + 12 <= T; t0 += step) origins.push(t0);
    const loss = {}, card = {}, fallback = {};
    keys.forEach((k) => { loss[k] = []; card[k] = []; fallback[k] = 0; });
    for (const t0 of origins) {
      const sub = truncate(data, t0);
      const Yt = data.X.map((row) => row.slice(t0, t0 + 12).reduce((a, x) => a + x, 0) / 12);
      const Wt = data.w.map((row) => row.slice(t0, t0 + 12).reduce((a, x) => a + x, 0)), WS = Wt.reduce((a, x) => a + x, 0);
      for (const k of keys) {
        const r = rollPredict(k, sub, o.world);
        if (r.fallback) fallback[k]++;
        const e2 = r.pred.map((y, j) => (y - Yt[j]) ** 2);
        card[k].push(e2);
        loss[k].push(e2.reduce((a, x, j) => a + Wt[j] * x, 0) / WS);
      }
    }
    return { origins, loss, card, fallback, J };
  }

  /** Regularized incomplete beta I_x(a, b) (continued fraction, Numerical Recipes betacf). */
  function betaInc(x, a, b) {
    if (x <= 0) return 0;
    if (x >= 1) return 1;
    const lnBeta = lgamma(a + b) - lgamma(a) - lgamma(b);
    const front = Math.exp(lnBeta + a * Math.log(x) + b * Math.log(1 - x));
    const cf = (x2, a2, b2) => {
      let c = 1, d = 1 - (a2 + b2) * x2 / (a2 + 1);
      if (Math.abs(d) < 1e-300) d = 1e-300;
      d = 1 / d;
      let h = d;
      for (let m = 1; m <= 300; m++) {
        const m2 = 2 * m;
        let aa = m * (b2 - m) * x2 / ((a2 + m2 - 1) * (a2 + m2));
        d = 1 + aa * d; if (Math.abs(d) < 1e-300) d = 1e-300; c = 1 + aa / c; if (Math.abs(c) < 1e-300) c = 1e-300; d = 1 / d; h *= d * c;
        aa = -(a2 + m) * (a2 + b2 + m) * x2 / ((a2 + m2) * (a2 + m2 + 1));
        d = 1 + aa * d; if (Math.abs(d) < 1e-300) d = 1e-300; c = 1 + aa / c; if (Math.abs(c) < 1e-300) c = 1e-300; d = 1 / d;
        const del = d * c; h *= del;
        if (Math.abs(del - 1) < 1e-14) break;
      }
      return h;
    };
    return x < (a + 1) / (a + b + 2) ? front * cf(x, a, b) / a : 1 - front * cf(1 - x, b, a) / b;
  }
  function lgamma(z) { // Lanczos, z > 0
    const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
      12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
    if (z < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * z))) - lgamma(1 - z);
    z -= 1;
    let x = c[0];
    for (let i = 1; i < g + 2; i++) x += c[i] / (z + i);
    const t = z + g + 0.5;
    return 0.5 * Math.log(2 * Math.PI) + (z + 0.5) * Math.log(t) - t + Math.log(x);
  }
  /** P(T ≤ t) for Student's t with df degrees of freedom. */
  function tCdf(t, df) {
    const x = df / (df + t * t), tail = 0.5 * betaInc(x, df / 2, 0.5);
    return t >= 0 ? 1 - tail : tail;
  }

  /**
   * Diebold–Mariano test of equal expected loss from the loss differentials d (fit A − fit B, same
   * targets), for h-step targets (h = 12 here: the 12-month targets of consecutive monthly origins
   * overlap, so d is autocorrelated up to lag h − 1). Long-run variance with uniform weights up to
   * lag h − 1 (Diebold & Mariano 1995); if that is not positive (possible in small samples, Harvey,
   * Leybourne & Whitehouse 2017), Bartlett weights (Newey–West), flagged. Harvey, Leybourne & Newbold
   * (1997): DM* = DM·√((n + 1 − 2h + h(h − 1)/n)/n) against t(n − 1). Two-sided p-value.
   * Returns null when n ≤ 2h (the correction is not positive for n ∈ {h − 1, h}; too few origins).
   */
  function dmTest(d, h) {
    const H = h || 12, n = d.length;
    if (n <= 2 * H) return null;
    const mean = d.reduce((a, x) => a + x, 0) / n;
    const gam = (k) => { let s = 0; for (let t = k; t < n; t++) s += (d[t] - mean) * (d[t - k] - mean); return s / n; };
    const g = Array.from({ length: H }, (_, k) => gam(k));
    let V = g[0] + 2 * g.slice(1).reduce((a, x) => a + x, 0), bartlett = false;
    if (!(V > 0)) { bartlett = true; V = g[0] + 2 * g.slice(1).reduce((a, x, k) => a + (1 - (k + 1) / H) * x, 0); }
    if (!(V > 0)) return { n, mean, V, dm: NaN, stat: NaN, p: NaN, bartlett };
    const dm = mean / Math.sqrt(V / n), stat = dm * Math.sqrt((n + 1 - 2 * H + H * (H - 1) / n) / n);
    const p = 2 * (1 - tCdf(Math.abs(stat), n - 1));
    return { n, mean, V, dm, stat, p, df: n - 1, bartlett };
  }

  /**
   * The weighted-periodogram version of the test (Coroneo & Iacone 2020, fixed-smoothing
   * asymptotics): long-run variance σ̂² = (2π/m) Σ_{k=1..m} I(2πk/n), I the periodogram of d,
   * m = ⌊n^(1/3)⌋, and √n·d̄/σ̂ against t(2m). Better sized than DM–HLN in small samples at
   * multi-step horizons, at the price of power. Two-sided p-value.
   */
  function wpeTest(d, m0) {
    const n = d.length, m = m0 || Math.floor(Math.cbrt(n));
    if (m < 1 || n < 4) return null;
    const mean = d.reduce((a, x) => a + x, 0) / n;
    let S = 0;
    for (let k = 1; k <= m; k++) {
      let re = 0, im = 0;
      for (let t = 0; t < n; t++) { const a = 2 * Math.PI * k * t / n; re += (d[t] - mean) * Math.cos(a); im -= (d[t] - mean) * Math.sin(a); }
      S += (re * re + im * im) / n; // 2π·I(λ_k)
    }
    const V = S / m, stat = mean / Math.sqrt(V / n), df = 2 * m;
    return { n, m, mean, V, stat, df, p: 2 * (1 - tCdf(Math.abs(stat), df)) };
  }

  /**
   * False alarms of both tests when the two fits are equally good: loss differentials d an MA(h − 1)
   * of standard normals (the overlap of h-month targets) with mean 0, n origins, `reps` series.
   * Returns the rejection rates at `alpha` (nominal size). Synthetic: no world, no fit.
   */
  function dmSize(n, reps, r, alpha, h) {
    const H = h || 12, al = alpha || 0.05;
    let dm = 0, wpe = 0, nd = 0;
    for (let k = 0; k < reps; k++) {
      const e = Array.from({ length: n + H - 1 }, () => r.normal());
      const d = Array.from({ length: n }, (_, t) => { let s = 0; for (let i = 0; i < H; i++) s += e[t + i]; return s; });
      const a = dmTest(d, H), b = wpeTest(d);
      if (a) { nd++; if (a.p < al) dm++; }
      if (b && b.p < al) wpe++;
    }
    return { dm: nd ? dm / nd : NaN, wpe: wpe / reps };
  }

  /**
   * The verdict of a paired comparison at level alpha: 'A' (A has lower loss), 'B', or 'none'
   * ("no evidence of a difference", not a ranking) for a rolling-origin result and two fit keys:
   * `verdict` by DM–HLN (the protocol), `verdictWpe` by the weighted-periodogram test.
   */
  function compareFits(roll, a, b, alpha) {
    const d = roll.loss[a].map((x, k) => x - roll.loss[b][k]), dm = dmTest(d, 12), wpe = wpeTest(d), al = alpha || 0.05;
    const call = (x) => (!x || !(x.p < al) ? 'none' : x.mean < 0 ? 'A' : 'B');
    const verdict = call(dm), verdictWpe = call(wpe);
    const meanA = roll.loss[a].reduce((s, x) => s + x, 0) / d.length, meanB = roll.loss[b].reduce((s, x) => s + x, 0) / d.length;
    return { d, dm, wpe, verdict, verdictWpe, meanA, meanB };
  }

  return { DEFAULTS, rng, solve, cholesky, eigSym, makeWorld, covTable, draw, basis, prepare, minque, minqueDense, yoyPooled, yoyShape, phiHat, phiProfile, phiIndex, toCSV, diagnose, fit, eigSymVec, clipPSD, constrainPSD, drawFuture, predictor, lastYear, truthTheta, hNormCheck, sZeroCohorts, zeroVarianceCohorts, truncate, ROLL_FITS, degenerateTable, rollPredict, rollingOrigin, betaInc, tCdf, dmTest, wpeTest, dmSize, compareFits };
});
