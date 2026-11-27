// Exact check of the floor rows of vc-balance.js (findings S27–S29, FINDINGS 15): no simulation.
// The floor (true K, τ²) and three of its balanced corrections are fixed linear rules θ̂ = Aμ̂ whose
// rows sum to 1, so their exposure-weighted error is a formula in the second moments alone
// (level covariance L = τ²I, Cov(μ̂) = K, Cov(μ̂, μ) = L, as in blendMSE):
//     E Σⱼ wⱼ*(θ̂ⱼ − μⱼ)² / w** = Σⱼ wⱼ*(AKAᵀ − AL − LAᵀ + L)ⱼⱼ / w**.
// It holds for any noise law with these moments, so these numbers do not depend on the world's
// gamma draws, the seed or the number of draws. 'scale' is a ratio of data, not linear: not here.
//   bal    collective Σ wⱼ*(1 − zⱼ)μ̂ⱼ / Σ wⱼ*(1 − zⱼ), z kept (BS style)
//   shift  every rate + Σ wⱼ*(μ̂ⱼ − μ̂ⱼᵇ)/w** (Wang–Fuller–Qu 2008)
//   opt    best balanced blend zⱼ = 1 − c*·bⱼ/wⱼ* (PLAN G7, Core.bestBalanced_optimal)
// Run: node studies/runs/exact-balance.js (output in exact-balance.out.txt).
'use strict';
const E = require('../../app/engine.js');
const sum = (a) => a.reduce((s, x) => s + x, 0);

/** Exposure-weighted MSE of the linear rule θ̂ = Aμ̂ (rows of A sum to 1), level covariance τ²I. */
function linearMSE(A, K, tau2, wt) {
  const J = K.length; let s = 0;
  for (let j = 0; j < J; j++) {
    let q = 0;
    for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += A[j][i] * K[i][k] * A[j][k];
    s += wt[j] * (q - 2 * tau2 * A[j][j] + tau2);
  }
  return s / sum(wt);
}
/** The blend zⱼμ̂ⱼ + (1 − zⱼ)Σ bᵢμ̂ᵢ as a matrix. */
const blendMatrix = (z, b) => z.map((zj, j) => b.map((bi, i) => (1 - zj) * bi + (i === j ? zj : 0)));
/** The rule plus the common shift wᵀ(μ̂ − Aμ̂)/w**. */
function shiftMatrix(A, wt) {
  const W = sum(wt), r = A[0].map((_, i) => (wt[i] - sum(wt.map((w, j) => w * A[j][i]))) / W);
  return A.map((row) => row.map((x, i) => x + r[i]));
}

/** Floor and its balanced corrections in one world, errors in % of the floor. */
function exactRow(params) {
  const world = E.makeWorld(params), fl = E.floorBlend(world), t2 = world.truth.tau2, wt = world.w.map(sum);
  const A = blendMatrix(fl.z, fl.b), floor = linearMSE(A, fl.K, t2, wt);
  const c = wt.map((x, j) => x * (1 - fl.z[j])), cs = sum(c);
  const bal = linearMSE(blendMatrix(fl.z, c.map((x) => x / cs)), fl.K, t2, wt);
  const g = fl.b.map((_, j) => fl.K[j][j] - fl.s2), a = fl.b.map((x, j) => x / wt[j]);
  const cOpt = sum(a.map((x, j) => wt[j] * g[j] * (1 - fl.z[j]) * x)) / sum(a.map((x, j) => wt[j] * g[j] * x * x));
  const opt = linearMSE(blendMatrix(a.map((x) => 1 - cOpt * x), fl.b), fl.K, t2, wt);
  const shift = linearMSE(shiftMatrix(A, wt), fl.K, t2, wt);
  const pct = (x) => 100 * x / floor;
  return { floor, bal: pct(bal), shift: pct(shift), opt: pct(opt), minB: Math.min(...fl.b), maxZ: Math.max(...fl.z), fl, wt, t2 };
}

/** The 19 worlds of vc-balance.js, in its order. */
function worlds() {
  const out = [];
  for (const ns of [1, 0]) for (const [J, T] of [[8, 5], [8, 10], [20, 10]]) for (const rho of [0, 0.3, 0.6])
    out.push({ label: `σⱼ ${ns ? 'spread' : 'equal '} J=${String(J).padStart(2)} T=${String(T).padStart(2)} ρ=${rho.toFixed(1)}`, params: { J, T, rho, noiseSpread: ns } });
  out.push({ label: 'σⱼ spread J= 8 T=10 ρ=0.6 vol spread 2', params: { rho: 0.6, noiseSpread: 1, spread: 2 } });
  return out;
}

module.exports = { linearMSE, blendMatrix, shiftMatrix, exactRow, worlds };
if (require.main !== module) return;

console.log('Exact floor rows of vc-balance.js (no simulation; any noise law with these second moments).');
console.log('Errors in % of the floor. min b, max z: the floor\'s GLS weights and factors.');
const f0 = (x) => x.toFixed(0).padStart(4), f2 = (x) => x.toFixed(2).padStart(5);
for (const { label, params } of worlds()) {
  const r = exactRow(params);
  console.log(`${label} | min b ${f2(r.minB)} max z ${r.maxZ.toFixed(2)} | bal ${f0(r.bal)} shift ${f0(r.shift)} opt ${f0(r.opt)}`);
}
