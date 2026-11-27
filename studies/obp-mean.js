// OBP collective mean against Bühlmann–Straub when the levels trend with volume (PLAN-done.md, "OBP
// collective mean"; literature §10p; Credibility/ObservedBest.lean, Finding 41).
// Purpose: decide. Does the observed best predictor's collective mean (weights ∝ uⱼ(1 − zⱼ)²,
// `Core.obpMean`) or grouping with a common τ² (`group_optimal_contiguous`) pay against BS (b ∝ z)?
//
// World: the engine world (gamma levels and noise, ρ = 0) plus a level trend in volume,
//   μⱼ = 1 + τ·ηⱼ − β·τ·sⱼ,  sⱼ = standardized rank of cohort j's volume (qnorm((j + ½)/J)),
// so β = 0 is the exchangeable world and β = 1 a trend as large as the residual spread τ.
// Loss: exposure-weighted squared error given the levels, Σ uⱼ(ĥⱼ − μⱼ)² / Σ uⱼ, uⱼ = wⱼ*.
//
// Part A (exact, known σⱼ², τ²): the blend with the true zⱼ and a fixed collective-mean weight b,
// error averaged over the noise and the residual levels ηⱼ (the trend fixed):
//   Eⱼ(b) = zⱼ²Dⱼ + 2zⱼ(1 − zⱼ)bⱼDⱼ + (1 − zⱼ)²[Σ bₖ²Dₖ + (bᵀt − tⱼ)² + τ²(Σ bₖ² − 2bⱼ + 1)],
// t the trend, for b ∝ z (best when the levels are exchangeable), b ∝ u(1 − z)² (OBP) and the best b.
// Part B (simulation, paired, common random numbers): fitted versions, all from data only:
//   BS        E.fitBS (σ̂² pooled, τ̂² moment, b ∝ ẑ);
//   OBP-m     BS's ẑ with the collective mean ∝ uⱼ(1 − ẑⱼ)² (Core.obpMean on the x̄ⱼ);
//   OBP       Jiang–Nguyen–Rao: τ² and m minimise the observed criterion Σ uⱼ[(1 − zⱼ)²(x̄ⱼ − m)² + 2zⱼDⱼ]
//             (the SURE of `integral_sure_given_level` up to a constant), D̂ⱼ = σ̂²/wⱼ*;
//   Trend-X   the trend as a fixed effect: BLUP with X = [1, log volume] (fitTrendX below);
//   G2-est    two groups, own means, one common τ̂² (pooled within-group moment estimator), the cut of
//             the sorted estimates with the smallest SURE (groups of at least 2);
//   G2-true   reference, not a fit: the same with the cut of the sorted TRUE levels (the order of the
//             theorem), to separate the sort by estimates from the choice of the cut;
//   G2-vol    the same with the cut of the volume order;
//   G-auto    the smallest SURE among BS (one group), G2-est and G2-vol.
// SURE for fixed τ̂² and groups: Σ uⱼ[(ĥⱼ − x̄ⱼ)² − D̂ⱼ + 2AⱼⱼD̂ⱼ], Aⱼⱼ = zⱼ + (1 − zⱼ)bⱼ.
// Run: node studies/obp-mean.js [draws]   (default 600)
'use strict';
const E = require('../app/engine.js');
const { sum, grid, paired, pm, regimes } = require('./lib.js');
const N = +(process.argv[2] || 600);

// Inverse normal CDF by bisection on erf (only for the trend's ranks).
function erf(x) { const t = 1 / (1 + 0.3275911 * Math.abs(x)); const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x); return x >= 0 ? y : -y; }
function qnorm(p) { let lo = -8, hi = 8; for (let i = 0; i < 80; i++) { const m = (lo + hi) / 2; if (0.5 * (1 + erf(m / Math.SQRT2)) < p) lo = m; else hi = m; } return (lo + hi) / 2; }

// ---------------------------------------------------------------- Part A: exact, known parameters
function exactLoss(b, z, D, t, tau2, u) {
  const J = z.length, bt = sum(b.map((x, k) => x * t[k])), bD = sum(b.map((x, k) => x * x * D[k])), b2 = sum(b.map((x) => x * x));
  let s = 0;
  for (let j = 0; j < J; j++) {
    const e = z[j] ** 2 * D[j] + 2 * z[j] * (1 - z[j]) * b[j] * D[j] + (1 - z[j]) ** 2 * (bD + (bt - t[j]) ** 2 + tau2 * (b2 - 2 * b[j] + 1));
    s += u[j] * e;
  }
  return s / sum(u);
}
// The best b with Σ b = 1: the loss is bᵀQb + cᵀb + const.
function bestB(z, D, t, tau2, u) {
  const J = z.length, Q = [], c = Array(J).fill(0);
  for (let i = 0; i < J; i++) { Q.push(Array(J).fill(0)); }
  for (let j = 0; j < J; j++) {
    const a = u[j] * (1 - z[j]) ** 2;
    for (let i = 0; i < J; i++) {
      Q[i][i] += a * (D[i] + tau2);
      for (let k = 0; k < J; k++) Q[i][k] += a * t[i] * t[k];
      c[i] += -2 * a * t[j] * t[i];
    }
    c[j] += 2 * u[j] * z[j] * (1 - z[j]) * D[j] - 2 * a * tau2;
  }
  // b = Q⁻¹(λ1 − c/2), λ from Σ b = 1.
  const q1 = E.solve(Q, Array(J).fill(1)), qc = E.solve(Q, c.map((x) => -x / 2));
  const lam = (1 - sum(qc)) / sum(q1);
  return qc.map((x, i) => x + lam * q1[i]);
}

// ---------------------------------------------------------------- Part B: fits from data
function stats(data) {
  const J = data.X.length, T = data.X[0].length, { wt, m } = E.cohortMeans(data);
  const sj2 = m.map((mj, j) => sum(data.X[j].map((x, t) => data.w[j][t] * (x - mj) ** 2)) / (T - 1));
  const s2 = sum(sj2) / J;
  return { J, wt, m, s2, D: wt.map((w) => s2 / w) };
}
// Groups (array of index arrays), one common τ̂², own means b ∝ ẑ (BS within each group).
function fitGroups(st, groups) {
  const { wt, m, s2, D, J } = st;
  let num = 0, den = 0;
  for (const g of groups) {
    const W = sum(g.map((j) => wt[j])), mw = sum(g.map((j) => wt[j] * m[j])) / W;
    num += sum(g.map((j) => wt[j] * (m[j] - mw) ** 2)); den += W - sum(g.map((j) => wt[j] ** 2)) / W;
  }
  const tau2 = Math.max(0, (num - (J - groups.length) * s2) / den);
  const z = wt.map((w) => (tau2 > 0 ? w / (w + s2 / tau2) : 0));
  const h = Array(J), A = Array(J);
  for (const g of groups) {
    const zs = sum(g.map((j) => z[j])), W = sum(g.map((j) => wt[j]));
    const b = {}; for (const j of g) b[j] = zs > 0 ? z[j] / zs : wt[j] / W;
    const mu = sum(g.map((j) => b[j] * m[j]));
    for (const j of g) { h[j] = z[j] * m[j] + (1 - z[j]) * mu; A[j] = z[j] + (1 - z[j]) * b[j]; }
  }
  const sure = sum(h.map((x, j) => wt[j] * ((x - m[j]) ** 2 - D[j] + 2 * A[j] * D[j]))) / sum(wt);
  return { rates: h, sure, tau2 };
}
function bestCut(st, order) {
  let best = null;
  for (let c = 2; c <= st.J - 2; c++) {
    const f = fitGroups(st, [order.slice(0, c), order.slice(c)]);
    if (!best || f.sure < best.sure) best = f;
  }
  return best;
}
const obpWeights = (u, z) => { const a = u.map((x, j) => x * (1 - z[j]) ** 2), s = sum(a); return a.map((x) => x / s); };
function fitOBPm(data) {
  const bs = E.fitBS(data), { wt } = E.cohortMeans(data);
  if (bs.tau2 <= 0) return bs.rates;
  return E.blend(bs.means, bs.z, obpWeights(wt, bs.z)).rates;
}
function fitOBP(st) {
  const { wt, m, D, s2 } = st;
  const score = (t2) => {
    const z = D.map((d) => t2 / (t2 + d)), b = obpWeights(wt, z), mu = sum(b.map((x, k) => x * m[k]));
    const q = sum(wt.map((w, j) => w * ((1 - z[j]) ** 2 * (m[j] - mu) ** 2 + 2 * z[j] * D[j])));
    return { q, rates: m.map((x, j) => z[j] * x + (1 - z[j]) * mu) };
  };
  const scale = s2 / (sum(wt) / wt.length);
  let best = score(0);
  for (let e = -4; e <= 3; e += 0.05) { const o = score(scale * Math.pow(10, e)); if (o.q < best.q) best = o; }
  return best.rates;
}

// Trend as a fixed effect (Core.blup with X = [1, s], s = standardized log volume, a known column):
// weighted-LS moment τ̂² = (Σ wⱼrⱼ² − (J − 2)σ̂²) / (tr W − tr(M XᵀW²X)), M = (XᵀWX)⁻¹ (unbiased, as
// eq. (13) with X = 1), then GLS β̂ on K̂ = diag(τ̂² + D̂ⱼ) and the rates x̂ⱼβ̂ + zⱼ(x̄ⱼ − x̂ⱼβ̂).
function fitTrendX(st) {
  const { wt, m, s2, D, J } = st, lw = wt.map(Math.log), mu = sum(lw) / J;
  const sd = Math.sqrt(sum(lw.map((x) => (x - mu) ** 2)) / J) || 1, X = lw.map((x) => [1, (x - mu) / sd]);
  const ls = (v) => { // weighted LS with weights v: β = (XᵀVX)⁻¹XᵀVm
    const A = [[0, 0], [0, 0]], c = [0, 0];
    for (let j = 0; j < J; j++) for (let a = 0; a < 2; a++) { c[a] += v[j] * X[j][a] * m[j]; for (let b = 0; b < 2; b++) A[a][b] += v[j] * X[j][a] * X[j][b]; }
    return { beta: E.solve(A, c), A };
  };
  const ols = ls(wt), r = m.map((x, j) => x - X[j][0] * ols.beta[0] - X[j][1] * ols.beta[1]);
  const Mi = E.solve(ols.A, [1, 0]), Mj = E.solve(ols.A, [0, 1]), M = [[Mi[0], Mj[0]], [Mi[1], Mj[1]]];
  let tr = 0; for (let j = 0; j < J; j++) for (let a = 0; a < 2; a++) for (let b = 0; b < 2; b++) tr += M[a][b] * wt[j] ** 2 * X[j][b] * X[j][a];
  const tau2 = Math.max(0, (sum(r.map((x, j) => wt[j] * x * x)) - (J - 2) * s2) / (sum(wt) - tr));
  const g = ls(D.map((d) => 1 / (tau2 + d))).beta, z = D.map((d) => tau2 / (tau2 + d));
  return m.map((x, j) => { const f = X[j][0] * g[0] + X[j][1] * g[1]; return f + z[j] * (x - f); });
}

// ---------------------------------------------------------------- the grid
const axes = { regime: Object.keys(regimes), J: [8, 20], T: [5, 10], beta: [0, 0.5, 1, 2] };
const FITS = ['OBP-m', 'OBP', 'Trend-X', 'G2-est', 'G2-true', 'G2-vol', 'G-auto'];
console.log(`draws ${N} per world; gamma levels (shape 4) and noise (shape 2), ρ = 0, τ = 0.10, σ = 6, volume spread per regime.`);
console.log('Part A (exact, known σⱼ², τ²): total error with collective mean b ∝ u(1 − z)² (OBP) and the best b, % of b ∝ z.');
console.log('Part B: fitted, paired difference to BS in % of BS’s mean loss (± 2 SE); negative = better than BS. BS/A = BS against the exact b ∝ z blend.');
console.log('regime       J  T  β   z range   | A: OBP  best | BS/A |   OBP-m        OBP          Trend-X      G2-est       G2-true      G2-vol       G-auto');
for (const c of grid(axes)) {
  const world = E.makeWorld(Object.assign({ J: c.J, T: c.T }, regimes[c.regime]));
  const { w, truth } = world, J = c.J, tau = Math.sqrt(truth.tau2);
  const u = w.map(sum);
  // volume rank: in makeWorld cohort j has the j-th smallest volume when spread > 0
  const order = u.map((x, j) => j).sort((a, b) => u[a] - u[b]), rank = Array(J);
  order.forEach((j, r) => { rank[j] = r; });
  const t = rank.map((r) => -c.beta * tau * qnorm((r + 0.5) / J));
  const D = truth.sigmaj2.map((s2, j) => s2 / u[j]), z = D.map((d) => truth.tau2 / (truth.tau2 + d));
  const zb = z.map((x) => x / sum(z));
  const lz = exactLoss(zb, z, D, t, truth.tau2, u);
  const lo = exactLoss(obpWeights(u, z), z, D, t, truth.tau2, u);
  const lb = exactLoss(bestB(z, D, t, truth.tau2, u), z, D, t, truth.tau2, u);
  const r = E.rng(1000 + 17 * c.J + c.T);
  const L = { BS: [] }; for (const f of FITS) L[f] = [];
  for (let n = 0; n < N; n++) {
    const d = E.draw(world, r), levels = d.levels.map((x, j) => x + t[j]);
    const data = { w: d.data.w, X: d.data.X.map((row, j) => row.map((x) => x + t[j])) };
    const loss = (h) => sum(h.map((x, j) => u[j] * (x - levels[j]) ** 2)) / sum(u);
    const st = stats(data), bs = E.fitBS(data);
    L.BS.push(loss(bs.rates));
    L['OBP-m'].push(loss(fitOBPm(data)));
    L.OBP.push(loss(fitOBP(st)));
    L['Trend-X'].push(loss(fitTrendX(st)));
    const byEst = st.m.map((x, j) => j).sort((a, b) => st.m[a] - st.m[b]);
    const ge = bestCut(st, byEst), gv = bestCut(st, order), g1 = fitGroups(st, [order.slice()]);
    const byTrue = levels.map((x, j) => j).sort((a, b) => levels[a] - levels[b]);
    L['G2-est'].push(loss(ge.rates)); L['G2-vol'].push(loss(gv.rates)); L['G2-true'].push(loss(bestCut(st, byTrue).rates));
    const auto = [g1, ge, gv].reduce((a, b) => (b.sure < a.sure ? b : a));
    L['G-auto'].push(loss(auto.rates));
  }
  const mBS = sum(L.BS) / N, sc = 100 / mBS;
  const cols = FITS.map((f) => pm(paired(L[f], L.BS), sc).padEnd(12)).join(' ');
  const zr = `${Math.min(...z).toFixed(2)}–${Math.max(...z).toFixed(2)}`;
  console.log(`${c.regime.padEnd(12)} ${String(J).padStart(2)} ${String(c.T).padStart(2)} ${c.beta.toFixed(1)}  ${zr} | ${(lo / lz * 100).toFixed(1).padStart(6)} ${(lb / lz * 100).toFixed(1).padStart(5)} | ${(mBS / lz * 100).toFixed(0).padStart(4)} | ${cols}`);
}
