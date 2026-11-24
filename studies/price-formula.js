// Purpose: conjecture (pre-step for Lean) and decide. Can the gap between two fitted models be
// predicted from moments, without simulating the fits? (studies/PLAN.md §1; damping-theta.md S53–.)
// Decomposition: MSE(fitted F) = oracle part + estimation price.
//   oracle part: the exact MSE of F's weights at its limiting parameters θ̄ = θ(E s) (Core linMse,
//     CoreMoments.mse_blend_eq_blup_add for the gap to the BLUP);
//   "integrated": E over s of the exact MSE of the (clipped) weights d(s), s with the exact mean and
//     covariance (P and B on matched gamma scales by Wilson–Hilferty, Qn Gaussian given P; B is exactly
//     uncorrelated with P and Qn), by a 3-D Gauss–Hermite rule: deterministic, moments only; it ignores the
//     dependence of s and μ̂ beyond that, as g₃ does;
//   price (first order, Prasad–Rao g₃): Σₖₗ Cov(sₖ, sₗ) Gₖᵀ K Gₗ, Gₖ = ∂dⱼ/∂sₖ, for the
//     quadratic statistics s the fit depends on; the cross term vanishes under normal noise for even,
//     translation-invariant estimators (PlugInNormal), so the worlds here are normal.
// Pooled versions (one σ², the Finding 35 remedy): BS and corrBS pooled depend on the data only
// through s = (P, Qn, B): P the pooled within-region variance, Qn the sum of the cross-region
// residual products, B the volume-weighted spread of the means. Under normal data x ~ N(μ1, Σ),
// E xᵀAx = tr(AΣ) and Cov(xᵀAx, xᵀA'x) = 2 tr(AΣA'Σ) (A annihilates 1): exact, no simulation.
// The simulated MSE (same fits in app/engine.js, `draws` normal data sets) is the check.
// Run: node studies/price-formula.js [draws]
'use strict';
const E = require('../app/engine.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 2000);
const sum = L.sum;

// ---- the fits as functions of the statistics s = [P, Qn, B] on a fixed design w
function design(w) {
  const J = w.length, T = w[0].length, wt = w.map(sum), wall = sum(wt);
  const S = w.map((wi) => w.map((wj) => sum(wi.map((x, t) => Math.sqrt(x * wj[t])))));
  let A0 = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) A0 += (T - 2) + S[i][j] ** 2 / (wt[i] * wt[j]);
  return { J, T, w, wt, wall, S, A0, c0: wall - sum(wt.map((x) => x * x)) / wall };
}
function stats(D, X) {
  const { J, T, w, wt, wall } = D, m = X.map((row, j) => sum(row.map((x, t) => w[j][t] * x)) / wt[j]);
  let P = 0, Qn = 0;
  for (let j = 0; j < J; j++) for (let t = 0; t < T; t++) P += w[j][t] * (X[j][t] - m[j]) ** 2;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) for (let t = 0; t < T; t++) Qn += Math.sqrt(w[i][t] * w[j][t]) * (X[i][t] - m[i]) * (X[j][t] - m[j]);
  const mw = sum(m.map((x, j) => wt[j] * x)) / wall, B = sum(m.map((x, j) => wt[j] * (x - mw) ** 2));
  return [P / (J * (T - 1)), Qn, B];
}
// θ(s) → weights dⱼ (rows j) for each fit; clip = the engine's truncations (ρ ∈ [0, 1), τ² ≥ 0).
function weights(D, s, fit, clip) {
  const { J, wt, wall, S, A0, c0 } = D, [P, Qn, B] = s;
  if (fit === 'bs') {
    let t2 = (B - (J - 1) * P) / c0;
    if (clip) t2 = Math.max(t2, 0);
    const z = wt.map((x) => (t2 > 0 || !clip ? x / (x + P / t2) : 0)), zs = sum(z);
    const b = zs !== 0 ? z.map((x) => x / zs) : wt.map((x) => x / wall);
    return z.map((zj, j) => b.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi));
  }
  let rho = Qn / (P * A0);
  if (clip) rho = Math.min(Math.max(rho, 0), 1 - 1e-9);
  const Sig = S.map((row, i) => row.map((x, j) => (i === j ? P / wt[i] : rho * P * x / (wt[i] * wt[j]))));
  const cj = Sig.map((_, j) => sum(Sig.map((row, i) => ((i === j ? 1 : 0) - wt[i] / wall) * row[j])));
  let t2 = (B - sum(wt.map((x, j) => x * cj[j]))) / c0;
  if (clip) t2 = Math.max(t2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : x)));
  if (fit === 'blup') return Sig.map((_, j) => E.blupWeight(K, t2, j));
  const { b, z: z0 } = E.bestBlendWeights(K, t2), z = clip && !(t2 > 0) ? z0.map(() => 0) : z0;
  return z.map((zj, j) => b.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi));
}

// ---- exact moments of s under normal data
function dataCov(world) {
  const { J, T, w, truth } = world, n = J * T, sd = truth.sigmaj2.map(Math.sqrt);
  const V = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 0; i < J; i++) for (let t = 0; t < T; t++) for (let j = 0; j < J; j++) for (let u = 0; u < T; u++) {
    let v = i === j ? truth.tau2 : 0;
    if (t === u) v += truth.rho[i][j] * sd[i] * sd[j] / Math.sqrt(w[i][t] * w[j][t]);
    V[i * T + t][j * T + u] = v;
  }
  return V;
}
function quadMatrix(D, k) { // A with s_k(x) = xᵀAx, by polarization (s_k is a homogeneous quadratic form)
  const { J, T } = D, n = J * T, unit = (ps) => { const X = Array.from({ length: J }, () => new Array(T).fill(0)); ps.forEach((p) => { X[Math.floor(p / T)][p % T] += 1; }); return stats(D, X)[k]; };
  const d = Array.from({ length: n }, (_, p) => unit([p]));
  return Array.from({ length: n }, (_, p) => Array.from({ length: n }, (__, q) => (p === q ? d[p] : (unit([p, q]) - d[p] - d[q]) / 2)));
}
// Probabilists' Gauss–Hermite nodes and weights (9 points, by Golub–Welsch on the Jacobi matrix).
const GH = (() => {
  const n = 9, A = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (Math.abs(i - j) === 1 ? Math.sqrt(Math.max(i, j)) : 0)));
  const { values, V } = (() => { // Jacobi eigen-decomposition
    const M = A.map((r) => r.slice()), Q = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (i === j ? 1 : 0)));
    for (let sweep = 0; sweep < 100; sweep++) for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      if (Math.abs(M[p][q]) < 1e-15) continue;
      const th = (M[q][q] - M[p][p]) / (2 * M[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s2 = t * c;
      for (let k = 0; k < n; k++) { const a = M[k][p], b = M[k][q]; M[k][p] = c * a - s2 * b; M[k][q] = s2 * a + c * b; }
      for (let k = 0; k < n; k++) { const a = M[p][k], b = M[q][k]; M[p][k] = c * a - s2 * b; M[q][k] = s2 * a + c * b; }
      for (let k = 0; k < n; k++) { const a = Q[k][p], b = Q[k][q]; Q[k][p] = c * a - s2 * b; Q[k][q] = s2 * a + c * b; }
    }
    return { values: M.map((r, i) => r[i]), V: Q };
  })();
  const w = V[0].map((x) => x * x);
  return { x: values, w, total: Math.pow(w.reduce((a, b) => a + b, 0), 3) };
})();
const mul = (A, B) => A.map((row) => B[0].map((_, j) => row.reduce((s, x, k) => s + x * B[k][j], 0)));
const tr = (A) => A.reduce((s, row, i) => s + row[i], 0);

function predict(world, fits) {
  const D = design(world.w), V = dataCov(world), K = E.trueK(world), t2 = world.truth.tau2;
  const AV = [0, 1, 2].map((k) => mul(quadMatrix(D, k), V));
  const Es = AV.map(tr), C = AV.map((a) => AV.map((b) => 2 * tr(mul(a, b))));
  const h = C.map((row, k) => 1e-4 * Math.sqrt(row[k]));
  const out = {};
  for (const fit of fits) {
    const d0 = weights(D, Es, fit, true);
    const G = [0, 1, 2].map((k) => { const up = Es.slice(), dn = Es.slice(); up[k] += h[k]; dn[k] -= h[k]; const a = weights(D, up, fit, false), b = weights(D, dn, fit, false); return a.map((row, j) => row.map((x, i) => (x - b[j][i]) / (2 * h[k]))); });
    let oracle = 0, price = 0;
    for (let j = 0; j < D.J; j++) {
      oracle += D.wt[j] * E.linMse(K, t2, j, d0[j]);
      let pj = 0;
      for (let k = 0; k < 3; k++) for (let l = 0; l < 3; l++) { const gk = G[k][j], gl = G[l][j]; let q = 0; for (let a = 0; a < D.J; a++) for (let b = 0; b < D.J; b++) q += gk[a] * K[a][b] * gl[b]; pj += C[k][l] * q; }
      price += D.wt[j] * pj;
    }
    // Gauss–Hermite (probabilists', 9 nodes per axis) over s = E s + L ξ, L Lᵀ = Cov s.
    const Lc = E.cholesky(C) || C.map((row, i) => row.map((x, j) => (i === j ? Math.sqrt(x) : 0)));
    let integ = 0;
    for (let a = 0; a < GH.x.length; a++) for (let b = 0; b < GH.x.length; b++) for (let c = 0; c < GH.x.length; c++) {
      const xi = [GH.x[a], GH.x[b], GH.x[c]], wq = GH.w[a] * GH.w[b] * GH.w[c];
      // P and B are positive (weighted χ²): each on a gamma scale matched in mean and variance, through
      // Wilson–Hilferty (X/EX)^(1/3) ≈ N(1 − 1/(9k), 1/(9k)), k = (EX)²/Var X; Qn Gaussian given P.
      const wh = (mean, v, x) => { const k = mean * mean / v, c = 1 / (9 * k); return mean * Math.pow(Math.max(1 - c + x * Math.sqrt(c), 0), 3); };
      const sq = [wh(Es[0], C[0][0], xi[0]), Es[1] + Lc[1][0] * xi[0] + Lc[1][1] * xi[1], wh(Es[2], C[2][2], xi[2])];
      if (!(sq[0] > 0)) continue;
      const dq = weights(D, sq, fit, true);
      let v = 0;
      for (let j = 0; j < D.J; j++) v += D.wt[j] * E.linMse(K, t2, j, dq[j]);
      integ += wq * v;
    }
    out[fit] = { oracle: oracle / D.wall, price: price / D.wall, integ: integ / D.wall / GH.total };
  }
  return { out, Es, C };
}

const ENG = { bs: (d) => E.fitBS(d), vc: (d) => E.fitVC(d, { pooled: true }), blup: (d) => E.fitBLUP(d, { pooled: true }) };
const KEY = { bs: 'bs', vc: 'vc', blup: 'blup' };
module.exports = { design, stats, weights, predict };
if (require.main !== module) return;

// ---- check: the re-implementation equals the engine on one draw
{
  const world = E.makeWorld({ normal: true, rho: 0.5 }), D = design(world.w), { data } = E.draw(world, E.rng(3));
  const s = stats(D, data.X), { m } = E.cohortMeans(data);
  for (const f of ['bs', 'vc', 'blup']) {
    const dw = weights(D, s, f, true), mine = dw.map((d) => sum(d.map((x, i) => x * m[i]))), eng = ENG[f](data).rates;
    const err = Math.max(...mine.map((x, j) => Math.abs(x - eng[j])));
    if (err > 1e-9) throw new Error(`${f}: re-implementation differs from the engine by ${err}`);
  }
}

console.log(`Normal worlds, J = 8, equal σⱼ, pooled fits. MSE in % of the blend floor: predicted = oracle + price (exact moments,`);
console.log(`first-order price), simulated = ${N} draws (± 2 SE). Gap = BS − corrBS pooled and BLUP pooled − corrBS pooled (paired).`);
console.log('world                 | fit  | oracle | price | predicted | integrated | simulated    ');
const rows = [];
for (const p of L.grid({ regime: ['app', 'thesis'], rho: [0, 0.3, 0.6, 0.9], T: [5, 10] })) {
  const world = E.makeWorld(Object.assign({ normal: true, rho: p.rho, T: p.T }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), floor = sum(world.w.map(sum).map((x, j) => x * E.linMse(fl.K, world.truth.tau2, j, fl.z.map(() => 0).map((_, i) => (i === j ? fl.z[j] : 0) + (1 - fl.z[j]) * fl.b[i])))) / sum(world.w.map(sum));
  const pr = predict(world, ['bs', 'vc', 'blup']).out, r = E.rng(2026), sim = { bs: [], vc: [], blup: [] };
  for (let k = 0; k < N; k++) { const { levels, data } = E.draw(world, r); for (const f of Object.keys(sim)) sim[f].push(E.weightedSE(data, ENG[f](data).rates, levels)); }
  const name = `${p.regime} ρ=${p.rho} T=${p.T}`;
  for (const f of ['bs', 'vc', 'blup']) {
    const ms = L.meanSE(sim[f]), q = pr[f];
    console.log(`${name.padEnd(21)} | ${f.padEnd(4)} | ${(100 * q.oracle / floor).toFixed(1).padStart(6)} | ${(100 * q.price / floor).toFixed(1).padStart(5)} | ${(100 * (q.oracle + q.price) / floor).toFixed(1).padStart(9)} | ${(100 * q.integ / floor).toFixed(1).padStart(10)} | ${L.pm(ms, 100 / floor)}`);
  }
  const gp = (a, b) => 100 * (pr[a].oracle + pr[a].price - pr[b].oracle - pr[b].price) / floor;
  const gi = (a, b) => 100 * (pr[a].integ - pr[b].integ) / floor;
  const gs = (a, b) => L.paired(sim[a], sim[b]);
  rows.push({ name, bsI: gi('bs', 'vc'), blI: gi('blup', 'vc'), bsP: gp('bs', 'vc'), bsS: gs('bs', 'vc'), blP: gp('blup', 'vc'), blS: gs('blup', 'vc'), floor,
    bsO: 100 * (pr.bs.oracle - pr.vc.oracle) / floor, blO: 100 * (pr.blup.oracle - pr.vc.oracle) / floor });
}
console.log('\nGaps (points of the floor): predicted (oracle part) against simulated (± 2 SE)');
console.log('world                 | BS − corrBS: oracle | 1st order | integrated | simulated    | BLUP − corrBS: oracle | 1st order | integrated | simulated');
const f1 = (x) => x.toFixed(1).padStart(6);
for (const x of rows) console.log(`${x.name.padEnd(21)} |  ${f1(x.bsO)}             | ${f1(x.bsP)}    | ${f1(x.bsI)}     | ${L.pm(x.bsS, 100 / x.floor).padEnd(12)} |  ${f1(x.blO)}               | ${f1(x.blP)}    | ${f1(x.blI)}     | ${L.pm(x.blS, 100 / x.floor)}`);
