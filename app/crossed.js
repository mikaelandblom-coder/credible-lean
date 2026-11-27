/*
 * Crossed levels: a table of cells with a row and a column (country × car type), the thesis noise
 * on top, and the fit from the data alone (notes/crossed-2x2.md; studies/PLAN-done.md: crossed levels;
 * Lean: Credibility/Crossed.lean, CrossedEstimation.lean, CrossedMoments.lean).
 *
 * One file, run by the page and by the tests under Node (app/crossed.test.js). Uses engine.js for
 * the thesis noise (draw with τ = 0) and its noise table (vcEstimate). Kept apart as in engine.js
 * (PLAN.md §1, principle 1):
 *   world — makeWorld(params), exact(world), draw(world, r): the truth and one data set;
 *   fit   — fit(data, opts), thesisFit(data): get { nr, nc, cells } and nothing else.
 *
 * Cell j sits in row ⌊j/nc⌋ and column j mod nc. Its level is
 *   μⱼ = 1 + α A_row + β B_col + γ Cⱼ   (A, B, C uncorrelated, mean 0, variance 1, skewed),
 * so L = α²[same row] + β²[same column] + γ²I (Crossed.levelCov), and the data are
 * Xⱼₜ = μⱼ + σ/√wⱼₜ εⱼₜ with corr(εᵢₜ, εⱼₜ) = ρ: the thesis noise (Model.NoiseX).
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./engine.js'));
  else root.Crossed = factory(root.Engine);
})(typeof self !== 'undefined' ? self : this, function (E) {
  'use strict';

  const sum = (a) => a.reduce((s, x) => s + x, 0);
  const dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);
  const mulVec = (K, v) => K.map((row) => dot(row, v));
  const quad = (K, d) => dot(d, mulVec(K, d));

  const DEFAULTS = {
    nr: 4,           // rows (countries)
    nc: 3,           // columns (car types)
    T: 10,           // years
    alpha: 0.06,     // spread of the row effects
    beta: 0.10,      // spread of the column effects
    gamma: 0.04,     // spread of the cell effects (what is left for the cell)
    sigma: 6.0,      // noise of one vehicle-year: Var(Xⱼₜ | μⱼ) = σ²/wⱼₜ
    rho: 0,          // correlation of the noise between cells within a year
    volume: 500,     // vehicle-years per cell and year, middle cell
    spread: 0,       // how unequal the volumes are (log scale); 0: a balanced table
    growth: 0.03,
    levelShape: 4,
    noiseShape: 2,
    normal: false,
    missing: false,  // the first cell (row 1, column 1) has no data
  };

  /** L = α²[same row] + β²[same column] + γ²I over the given cells (Crossed.levelCov). */
  function levelCov(row, col, a2, b2, g2) {
    return row.map((ri, i) => row.map((rj, j) => (ri === rj ? a2 : 0) + (col[i] === col[j] ? b2 : 0) + (i === j ? g2 : 0)));
  }

  /** A fixed order that mixes the volumes over rows and columns (otherwise row 1 would hold the smallest cells). */
  function volumeOrder(J) {
    const key = (j) => (j * 0.6180339887) % 1;
    const idx = Array.from({ length: J }, (_, j) => j).sort((a, b) => key(a) - key(b));
    const rank = new Array(J);
    idx.forEach((j, k) => { rank[j] = k; });
    return rank;
  }

  function makeWorld(params) {
    const p = Object.assign({}, DEFAULTS, params || {});
    const J = p.nr * p.nc;
    const base = E.makeWorld({ J, T: p.T, tau: 0, sigma: p.sigma, rho: p.rho, volume: p.volume, spread: p.spread, growth: p.growth, levelShape: p.levelShape, noiseShape: p.noiseShape, normal: p.normal });
    const rank = volumeOrder(J);
    const noise = Object.assign({}, base, { w: rank.map((k) => base.w[k]) });
    const row = Array.from({ length: J }, (_, j) => Math.floor(j / p.nc)), col = Array.from({ length: J }, (_, j) => j % p.nc);
    const obs = [], miss = [];
    for (let j = 0; j < J; j++) (p.missing && j === 0 ? miss : obs).push(j);
    const a2 = p.alpha ** 2, b2 = p.beta ** 2, g2 = p.gamma ** 2;
    const Sigma = E.trueK(noise); // τ = 0: the noise covariance of the cell means μ̂ⱼ
    const truth = { mu: 1, alpha2: a2, beta2: b2, gamma2: g2, Sigma, rho: p.rho, sigma2: p.sigma ** 2 };
    return { params: p, nr: p.nr, nc: p.nc, J, T: p.T, row, col, obs, miss, w: noise.w, noise, truth };
  }

  /**
   * One data set: the levels of all cells (truth) and what the fit sees: per cell its row, its
   * column, and its volumes and ratios (null for a cell without data).
   */
  function draw(world, r) {
    const { truth: t, J, row, col } = world, p = world.params, nz = p.normal;
    const nd = E.draw(world.noise, r); // levels 1, thesis noise
    const A = Array.from({ length: world.nr }, () => r.unit(p.levelShape, nz));
    const B = Array.from({ length: world.nc }, () => r.unit(p.levelShape, nz));
    const levels = [], cells = [];
    for (let j = 0; j < J; j++) {
      const eff = Math.sqrt(t.alpha2) * A[row[j]] + Math.sqrt(t.beta2) * B[col[j]] + Math.sqrt(t.gamma2) * r.unit(p.levelShape, nz);
      levels.push(t.mu + eff);
      const has = !world.miss.includes(j);
      cells.push(Object.freeze({ row: row[j], col: col[j], w: has ? nd.data.w[j].slice() : null, X: has ? nd.data.X[j].map((x) => x + eff) : null }));
    }
    return { levels, data: Object.freeze({ nr: world.nr, nc: world.nc, cells: Object.freeze(cells) }) };
  }

  // ---------------------------------------------------------------- predictors for a given K, L

  /** GLS weights b = K⁻¹1 / 1ᵀK⁻¹1 and s² = 1/1ᵀK⁻¹1 (Core.glsWeight). */
  function gls(K) {
    const u = E.solve(K, K.map(() => 1)), tot = sum(u);
    return { b: u.map((x) => x / tot), s2: 1 / tot };
  }

  /**
   * Best linear unbiased predictor of a level with covariance ℓ with the cell means (Core.blup,
   * X = 1): d = K⁻¹ℓ + (1 − 1ᵀK⁻¹ℓ) b. For an observed cell ℓ is its column of L; for a cell
   * without data ℓ = α²[same row] + β²[same column] (Crossed.cellCov).
   */
  function blupD(K, b, ell) {
    const k = E.solve(K, ell), s = sum(k);
    return k.map((x, i) => x + (1 - s) * b[i]);
  }

  /** True MSE of Σᵢ dᵢμ̂ᵢ for a level with variance v and covariance ℓ (Core.predMse): dᵀKd − 2dᵀℓ + v. */
  function predMse(K, ell, v, d) { return quad(K, d) - 2 * dot(d, ell) + v; }

  /**
   * Weights of every cell's predictor on the observed cells, for the full predictor and for the
   * best blend zⱼμ̂ⱼ + (1 − zⱼ)μ̂ (eq. (26) for a general L, Core.levelMoments_bestZ_eq:
   * zⱼ = (Lⱼⱼ − (Lb)ⱼ)/(Kⱼⱼ − s²)); a cell without data gets the collective mean b.
   * row, col: of all cells; obs: indices of the observed cells; K over the observed cells.
   */
  function predictors(K, row, col, obs, a2, b2, g2) {
    const { b, s2 } = gls(K), n = obs.length;
    const out = [];
    for (let j = 0; j < row.length; j++) {
      const ell = obs.map((i) => (row[i] === row[j] ? a2 : 0) + (col[i] === col[j] ? b2 : 0) + (i === j ? g2 : 0));
      const v = a2 + b2 + g2, k = obs.indexOf(j);
      const full = blupD(K, b, ell);
      let blend, z = null;
      if (k >= 0) {
        z = (ell[k] - dot(ell, b)) / (K[k][k] - s2);
        if (!Number.isFinite(z)) z = 0;
        blend = b.map((x, i) => (1 - z) * x + (i === k ? z : 0));
      } else blend = b.slice();
      out.push({ ell, v, full, blend, z, observed: k >= 0, k });
    }
    return { b, s2, cells: out, n };
  }

  // ---------------------------------------------------------------- the truth: floors and the price per layer

  /** The true K over the observed cells, and the floors: full predictor and best blend, exact MSE per cell. */
  function exact(world) {
    const { truth: t, obs, row, col } = world;
    const L = levelCov(obs.map((j) => row[j]), obs.map((j) => col[j]), t.alpha2, t.beta2, t.gamma2);
    const K = obs.map((i, a) => obs.map((j, c) => t.Sigma[i][j] + L[a][c]));
    const P = predictors(K, row, col, obs, t.alpha2, t.beta2, t.gamma2);
    const cells = P.cells.map((c) => ({ full: c.full, blend: c.blend, z: c.z, observed: c.observed, mseFull: predMse(K, c.ell, c.v, c.full), mseBlend: predMse(K, c.ell, c.v, c.blend) }));
    const tot = (key, o) => sum(cells.filter((c) => c.observed === o).map((c) => c[key]));
    return { K, L, b: P.b, cells, full: tot('mseFull', true), blend: tot('mseBlend', true), missFull: tot('mseFull', false), missBlend: tot('mseBlend', false), layers: layers(world) };
  }

  /**
   * The blend's excess per layer (Crossed.sum_linMse_blendρ), for a balanced table: equal volumes,
   * every cell observed, equicorrelated noise. With s = σ²(1 − ρ)/w* the layers are rows (dimension
   * n_r − 1, λ_r = n_cα² + γ²), columns (n_c − 1, λ_c = n_rβ² + γ²) and cells ((n_r − 1)(n_c − 1), λ_i = γ²);
   * z_k = λ_k/(λ_k + s) (Crossed.blup_balancedρ) and the blend's best common z̄ = Σmₖλₖ/(Σmₖλₖ + (n_rn_c − 1)s)
   * (Crossed.bestZ_KBal) loses mₖ(λₖ + s)(z̄ − zₖ)² on layer k. null when the table is not balanced.
   */
  function layers(world) {
    const p = world.params, t = world.truth;
    if (p.spread !== 0 || world.miss.length || p.noiseSpread) return null;
    const wt = sum(world.w[0]), s = t.sigma2 * (1 - Math.max(t.rho, 0)) / wt, nr = world.nr, nc = world.nc;
    const L = [
      { name: 'rows', m: nr - 1, lambda: nc * t.alpha2 + t.gamma2 },
      { name: 'columns', m: nc - 1, lambda: nr * t.beta2 + t.gamma2 },
      { name: 'cells', m: (nr - 1) * (nc - 1), lambda: t.gamma2 },
    ];
    const sig = sum(L.map((l) => l.m * l.lambda)), zbar = sig / (sig + (nr * nc - 1) * s);
    for (const l of L) { l.z = l.lambda / (l.lambda + s); l.loss = l.m * (l.lambda + s) * (zbar - l.z) ** 2; l.floor = l.m * l.lambda * s / (l.lambda + s); }
    return { s, zbar, layers: L, excess: sum(L.map((l) => l.loss)) };
  }

  // ---------------------------------------------------------------- the fit (data only)

  /** The observed cells as the engine's { w, X } table, with their rows and columns. */
  function observed(data) {
    const idx = [], w = [], X = [], row = [], col = [];
    data.cells.forEach((c, j) => { if (c.X) { idx.push(j); w.push(c.w); X.push(c.X); row.push(c.row); col.push(c.col); } });
    return { idx, sub: { w, X }, row, col };
  }

  /** Pair classes: same row (other column), same column (other row), neither (CrossedEstimation: sameRowPairs, …). */
  function pairClass(row, col, i, j) {
    if (row[i] === row[j]) return col[i] === col[j] ? null : 'r';
    return col[i] === col[j] ? 'c' : 'n';
  }

  /**
   * Least squares on the three pool equations p_r = β² + γ², p_c = α² + γ², p_n = α² + β² + γ²
   * (p = pool/2) over θ = (α², β², γ²) ≥ 0: the projection of the raw solution onto the orthant in
   * the metric MᵀM (ConeProjection.hsq_proj_le). Exact for 3 variables by enumerating the faces.
   */
  function nnls3(p) {
    const M = [[0, 1, 1], [1, 0, 1], [1, 1, 1]];
    let best = null;
    for (let mask = 0; mask < 8; mask++) {
      const free = [0, 1, 2].filter((k) => mask & (1 << k));
      const th = [0, 0, 0];
      if (free.length) {
        const A = free.map((a) => free.map((b) => sum(M.map((r) => r[a] * r[b]))));
        const y = free.map((a) => sum(M.map((r, i) => r[a] * p[i])));
        let x;
        try { x = E.solve(A, y); } catch (e) { continue; }
        if (x.some((v) => v < -1e-15)) continue;
        free.forEach((k, i) => { th[k] = Math.max(x[i], 0); });
      }
      const res = sum(M.map((r, i) => (dot(r, th) - p[i]) ** 2));
      if (!best || res < best.res - 1e-18) best = { th, res };
    }
    return best.th;
  }

  /**
   * The three pair pools and the raw α̂², β̂², γ̂² (Model.crossed_unbiasedX). weights: 'iv' (inverse variance,
   * the default: studies/runs/crossed-fit.js), 'equal' (each pair of a class alike), 'vol' (∝ wᵢ*wⱼ*), or 'anova'
   * (∝ wᵢ*wⱼ* and the noise cross term omitted: Dannenburg's and Goulet's ANOVA statistics as pair pools,
   * biased under correlated noise, Finding 42).
   */
  function pairPools(data, weights) {
    const { idx, sub, row, col } = observed(data), n = idx.length;
    const { wt, m, Sig } = E.sigmaHat(sub); // eq. (39): unbiased σ²ᵢⱼρᵢⱼ^ for every pair
    // 'iv': inverse-variance weights 1/(E(μ̂ᵢ − μ̂ⱼ)²)², the normal-theory Var P̂ᵢⱼ up to a factor, from a first
    // pass with equal weights (class value, clipped at 0) and the noise of the difference from corrBS's Σ̂ (≥ 0)
    let ivw = null;
    if (weights === 'iv') {
      const P0 = pairPools(data, 'equal').P, V = E.vcEstimate(sub).Sig;
      ivw = (k, i, j) => 1 / (Math.max(P0[k], 0) + V[i][i] + V[j][j] - 2 * V[i][j]) ** 2;
    }
    const pool = { r: [0, 0], c: [0, 0], n: [0, 0] }, count = { r: 0, c: 0, n: 0 };
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const k = pairClass(row, col, i, j);
      if (!k) continue;
      const corr = Sig[i][i] + Sig[j][j] - (weights === 'anova' ? 0 : 2 * Sig[i][j]);
      const P = (m[i] - m[j]) ** 2 - corr, a = weights === 'equal' ? 1 : weights === 'iv' ? ivw(k, i, j) : wt[i] * wt[j];
      pool[k][0] += a * P; pool[k][1] += a; count[k]++;
    }
    const P = {};
    for (const k of ['r', 'c', 'n']) P[k] = count[k] ? pool[k][0] / pool[k][1] : NaN;
    // crossed_unbiasedX: α̂² = (P̂_n − P̂_r)/2, β̂² = (P̂_n − P̂_c)/2, γ̂² = (P̂_r + P̂_c − P̂_n)/2
    const raw = [(P.n - P.r) / 2, (P.n - P.c) / 2, (P.r + P.c - P.n) / 2];
    return { idx, sub, row, col, wt, m, Sig, P, count, raw };
  }

  // ---------------------------------------------------------------- REML on the cell means (studies/runs/crossed-small.js, S70)

  const inv = (A) => A.map((_, k) => E.solve(A, A.map((_, i) => (i === k ? 1 : 0)))); // A symmetric: columns = rows
  const mul = (A, B) => A.map((r) => B[0].map((_, j) => sum(r.map((x, k) => x * B[k][j]))));
  const tr = (A) => sum(A.map((r, i) => r[i]));

  /** P = K⁻¹ − K⁻¹11ᵀK⁻¹/1ᵀK⁻¹1, the REML projection (P1 = 0). */
  function projP(K) {
    const Ki = inv(K), u = Ki.map((r) => sum(r)), s = sum(u);
    return Ki.map((r, i) => r.map((x, j) => x - (u[i] * u[j]) / s));
  }

  /** The restricted log-likelihood −½(log|K| + log 1ᵀK⁻¹1 + mᵀPm), up to a constant; −∞ if K is not positive definite. */
  function remlLik(K, m) {
    const Lc = E.cholesky(K);
    if (!Lc) return -Infinity;
    const ld = 2 * sum(Lc.map((r, i) => Math.log(r[i]))), u = E.solve(K, K.map(() => 1)), P = projP(K);
    return -0.5 * (ld + Math.log(sum(u)) + dot(m, mulVec(P, m)));
  }

  /** The REML score ∂ℓ/∂θₖ = −½tr(PGₖ) + ½mᵀPGₖPm and Fisher information ½tr(PGₖPGₗ), θ = (α², β², γ²). */
  function remlScore(m, Sig, G, th) {
    const K = Sig.map((r, i) => r.map((x, j) => x + th[0] * G[0][i][j] + th[1] * G[1][i][j] + th[2] * G[2][i][j]));
    const P = projP(K), Pm = mulVec(P, m), PG = G.map((g) => mul(P, g));
    return { K, score: G.map((g, k) => -0.5 * tr(PG[k]) + 0.5 * quad(g, Pm)), info: PG.map((a) => PG.map((b) => 0.5 * tr(mul(a, b)))) };
  }

  /**
   * θ̂ = (α̂², β̂², γ̂²) ≥ 0 maximizing the restricted likelihood of the cell means m ~ N(μ1, Σ̂ + L(θ)), Σ̂ fixed:
   * projected Fisher scoring from theta0 (moved off 0 by 10⁻³ of the mean noise variance), coordinates at 0
   * with a negative score held there, step halving until the likelihood does not fall. A Gaussian working
   * likelihood: its estimating equations are quadratic in m and unbiased for any noise family at the true θ.
   * Returns { theta, iter, score, lik, lik0 } (lik0: at theta0).
   */
  function remlTheta(m, Sig, row, col, theta0) {
    const G = [0, 1, 2].map((k) => levelCov(row, col, k === 0 ? 1 : 0, k === 1 ? 1 : 0, k === 2 ? 1 : 0));
    const Kof = (th) => Sig.map((r, i) => r.map((x, j) => x + th[0] * G[0][i][j] + th[1] * G[1][i][j] + th[2] * G[2][i][j]));
    const scale = tr(Sig) / Sig.length;
    const lik0 = remlLik(Kof(theta0), m);
    let th = theta0.map((x) => Math.max(x, 1e-3 * scale)), lik = remlLik(Kof(th), m), it = 0;
    if (lik0 > lik) { th = theta0.slice(); lik = lik0; }
    for (; it < 50; it++) {
      const { score, info } = remlScore(m, Sig, G, th);
      const free = [0, 1, 2].filter((k) => th[k] > 0 || score[k] > 0);
      if (!free.length) break;
      let step;
      try { step = E.solve(free.map((a) => free.map((b) => info[a][b])), free.map((a) => score[a])); } catch (e) { break; }
      let t = 1, moved = false, done = false;
      for (let h = 0; h < 30; h++, t /= 2) {
        const nt = th.slice();
        free.forEach((k, i) => { nt[k] = Math.max(0, th[k] + t * step[i]); });
        const nl = remlLik(Kof(nt), m);
        if (nl >= lik - 1e-12) { done = Math.abs(nl - lik) < 1e-10; th = nt; lik = nl; moved = true; break; }
      }
      if (!moved || done) break;
    }
    return { theta: th, iter: it, score: remlScore(m, Sig, G, th).score, lik, lik0 };
  }

  /**
   * The crossed fit. opts.method: 'reml' (the default: REML on the cell means from the pools below, remlTheta;
   * S70 and crossed-fit.js: better than the pools in 48 of 96 worlds, worse in 9, by at most 3 points of the floor)
   * or 'pools' (the variances from the pools alone). opts.weights as for pairPools; opts.trunc: 'clip' (each
   * variance at 0, the Euclidean projection; the default) or 'nnls' (the projection in the pool equations' metric). The defaults are
   * provisional, from studies/runs/crossed-fit.js (1000 draws × 96 worlds: inverse variance + clip is never clearly
   * worse than equal weights and better in 59 worlds; least squares loses to clip in 67): a hypothesis for the
   * worlds it visits, until the general targets in PLAN-done.md (crossed levels) are proved.
   */
  function fit(data, opts) {
    const o = Object.assign({ weights: 'iv', trunc: 'clip', method: 'reml' }, opts || {});
    const isReml = o.method === 'reml';
    const { idx, sub, row, col, wt, m, Sig, P, count, raw } = pairPools(data, o.weights);
    const ok = raw.every(Number.isFinite);
    const pooled = !ok ? [0, 0, 0] : o.trunc === 'nnls' ? nnls3([P.r / 2, P.c / 2, P.n / 2]) : raw.map((x) => Math.max(x, 0));
    // the noise table of K̂: corrBS's (credibility σ̃ⱼ², one ρ̂), positive definite for ρ̂ ∈ [0, 1)
    const vc = E.vcEstimate(sub);
    const rm = isReml && ok ? remlTheta(m, vc.Sig, row, col, pooled) : null;
    const theta = rm ? rm.theta : pooled;
    const [a2, b2, g2] = theta;
    const L = levelCov(row, col, a2, b2, g2);
    const K = vc.Sig.map((r, i) => r.map((x, j) => x + L[i][j]));
    const allRow = data.cells.map((c) => c.row), allCol = data.cells.map((c) => c.col);
    const Pr = predictors(K, allRow, allCol, idx, a2, b2, g2);
    const rates = Pr.cells.map((c) => dot(c.full, m)), blendRates = Pr.cells.map((c) => dot(c.blend, m));
    const mu = dot(Pr.b, m);
    const warnings = [];
    if (!ok) warnings.push('a pair class is empty (a table needs at least two rows and two columns): the three variances are not identified');
    const neg = ['α̂²', 'β̂²', 'γ̂²'].filter((_, k) => raw[k] < 0);
    if (ok && neg.length && !isReml) warnings.push(`${neg.join(', ')} < 0 from the pools: ${o.trunc === 'nnls' ? 'the three are refitted by least squares on the pool equations with all three ≥ 0' : 'set to 0'} (a projection onto valid values: never further from the truth in its metric)`);
    // Finding 44 (CrossedSmall): in a 2×2 table each pool has two pairs, so each variance rests on one degree of freedom
    if (data.nr === 2 && data.nc === 2) warnings.push('a 2×2 table: each of α̂², β̂², γ̂² rests on one degree of freedom, so any unbiased estimate of one from the cell means has standard deviation at least √2 times the true value, at any volume (normal theory; Finding 44, CrossedSmall.sq_le_trace_row). The fit cannot tell rows, columns and cells apart reliably: use the thesis fit (one τ²), or add rows or columns.');
    const steps = [
      { name: 'cell means μ̂ⱼ', badge: 'proved', lean: 'Model.a_special' },
      { name: 'noise σ²ᵢⱼρᵢⱼ^ (eq. (39))', badge: 'proved', lean: 'Model.sigRhoHat_unbiasedX', note: 'unbiased with crossed levels too: the levels cancel within a cell' },
      { name: 'pair estimators P̂ᵢⱼ = (μ̂ᵢ − μ̂ⱼ)² − (σ̂ᵢᵢ + σ̂ⱼⱼ − 2σ̂ᵢⱼ)', badge: o.weights === 'anova' ? 'not proved yet' : 'proved', lean: o.weights === 'anova' ? 'Model.anovaStat_unbiasedX' : 'Model.pairHat_unbiasedX', note: o.weights === 'anova' ? 'ANOVA: the cross term −2σ̂ᵢⱼ is left out, biased by the noise covariances (Finding 42)' : 'E P̂ᵢⱼ = 2γ² + 2α²[other row] + 2β²[other column]' },
      { name: `three pools (${o.weights === 'equal' ? 'equal weights' : o.weights === 'iv' ? 'inverse-variance weights' : 'weights ∝ wᵢ*wⱼ*'}) → α̂², β̂², γ̂²`, values: raw, badge: o.weights === 'anova' || o.weights === 'iv' ? 'not proved yet' : 'proved', lean: o.weights === 'anova' ? 'Model.anovaStat_unbiasedX' : 'Model.crossed_unbiasedX', note: `pairs: ${count.r} same row, ${count.c} same column, ${count.n} neither` + (o.weights === 'iv' ? '. Weights 1/(P̂_class + noise of the difference)² from a first equal-weight pass: unbiased for fixed weights (Model.crossed_unbiasedX); with weights from the same data only nearly (γ̂² about +7% of τ² at ρ = 0.5 in the study)' : '') },
      { name: `truncation at 0 (${o.trunc === 'nnls' ? 'least squares, θ ≥ 0' : 'clip'})`, values: pooled, badge: 'proved', lean: 'ConeProjection.hsq_proj_le', note: 'a projection onto a convex set that contains the truth: its error is at most the raw one, in every draw' },
      ...(isReml ? [{ name: 'REML on the cell means: θ̂ ≥ 0 maximizing the restricted likelihood of μ̂ ~ N(μ1, Σ̂ + L(θ)), from the step above', values: theta, badge: 'not proved yet', note: `projected Fisher scoring, ${rm ? rm.iter : 0} steps. A Gaussian working likelihood: its score is unbiased at the true θ for any noise, but the estimate is not; the default because its rates beat the pools' in 69 of 128 small-table worlds (S70) and 48 of 96 larger ones (S71), and were never worse by more than 5 points of the floor` }] : []),
      { name: 'K̂ = L̂ + Σ̂ (Σ̂ from corrBS: σ̃ⱼ², one ρ̂)', values: [vc.rho], badge: 'proved', lean: 'Crossed.K_posDef', note: 'K̂ ≻ 0: L̂ ⪰ 0 for α̂², β̂², γ̂² ≥ 0 and Σ̂ ≻ 0' },
      { name: 'rates: the best linear unbiased predictor μ̂ + ℓ̂ᵀK̂⁻¹(μ̂ⱼ − μ̂)', badge: 'proved', lean: 'Core.blup_optimal', note: 'optimal for the true K and L; plugged in here. A cell without data uses ℓ = α²[same row] + β²[same column] (Crossed.missing_blup)' },
    ];
    return { idx, m, wt, Sig, pools: P, count, raw, pooled, reml: rm, method: o.method, theta, rho: vc.rho, K, b: Pr.b, mu, cells: Pr.cells, rates, blendRates, warnings, steps };
  }

  /** The thesis fit on the same cells, without rows and columns (corrBS, L = τ²I); a cell without data gets μ̂. */
  function thesisFit(data) {
    const { idx, sub } = observed(data), f = E.fitVC(sub);
    return { tau2: f.tau2, rho: f.rho, mu: f.mu, rates: data.cells.map((c, j) => { const k = idx.indexOf(j); return k >= 0 ? f.rates[k] : f.mu; }) };
  }

  // ---------------------------------------------------------------- many draws

  const VARIANTS = [
    { id: 'iv-clip', weights: 'iv', trunc: 'clip', method: 'pools' },
    { id: 'iv-nnls', weights: 'iv', trunc: 'nnls', method: 'pools' },
    { id: 'equal-clip', weights: 'equal', trunc: 'clip', method: 'pools' },
    { id: 'equal-nnls', weights: 'equal', trunc: 'nnls', method: 'pools' },
    { id: 'vol-clip', weights: 'vol', trunc: 'clip', method: 'pools' },
    { id: 'vol-nnls', weights: 'vol', trunc: 'nnls', method: 'pools' },
    { id: 'anova-clip', weights: 'anova', trunc: 'clip', method: 'pools' },
    { id: 'reml', weights: 'iv', trunc: 'clip', method: 'reml' },
  ];

  /**
   * n draws, common random numbers: per fit the summed squared error over observed cells (obs) and
   * over cells without data (miss), and per variant the errors of α̂², β̂², γ̂² (raw, before truncation).
   */
  function simulate(world, n, seed, variants) {
    const vs = variants || VARIANTS, r = E.rng(seed), ex = exact(world), t = world.truth;
    const out = { obs: {}, miss: {}, raw: {}, used: {} };
    const add = (key, id, x) => { (out[key][id] = out[key][id] || []).push(x); };
    for (let s = 0; s < n; s++) {
      const { levels, data } = draw(world, r);
      const { idx } = observed(data), m = idx.map((j) => sum(data.cells[j].w.map((w, k) => w * data.cells[j].X[k])) / sum(data.cells[j].w));
      const score = (id, rates) => {
        let so = 0, sm = 0;
        rates.forEach((x, j) => { const e = (x - levels[j]) ** 2; if (idx.includes(j)) so += e; else sm += e; });
        add('obs', id, so); add('miss', id, sm);
      };
      score('floor', ex.cells.map((c) => dot(c.full, m)));
      score('floorBlend', ex.cells.map((c) => dot(c.blend, m)));
      score('thesis', thesisFit(data).rates);
      for (const v of vs) {
        const f = fit(data, v);
        score(v.id, f.rates);
        add('raw', v.id, f.raw.map((x, k) => x - [t.alpha2, t.beta2, t.gamma2][k]));
        add('used', v.id, f.theta.map((x, k) => x - [t.alpha2, t.beta2, t.gamma2][k]));
      }
    }
    return out;
  }

  function toCSV(data) {
    const lines = ['row,column,year,volume,ratio'];
    data.cells.forEach((c) => { if (c.X) c.X.forEach((x, t) => lines.push(`${c.row + 1},${c.col + 1},${t + 1},${c.w[t].toFixed(1)},${x.toFixed(6)}`)); });
    return lines.join('\n') + '\n';
  }

  return { DEFAULTS, VARIANTS, levelCov, pairPools, projP, remlLik, remlTheta, makeWorld, draw, gls, blupD, predMse, predictors, exact, layers, observed, pairClass, nnls3, fit, thesisFit, simulate, toCSV };
});
