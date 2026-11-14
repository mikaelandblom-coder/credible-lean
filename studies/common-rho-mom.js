// "Correlated Bühlmann–Straub": the thesis model with one σ² and one ρ, all parameters by
// unbiased moment equations (no ratio, no damping, no tuning):
//   Qᵢⱼ = Σₜ √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ),  Sᵢⱼ = Σₜ √(wᵢₜwⱼₜ),
//   E Qⱼⱼ = σ²(T − 1)                         → σ̂² = Σⱼ Qⱼⱼ / (J(T − 1))   (BS, 1/J fix)
//   E Qᵢⱼ = ρσ² ((T − 2) + Sᵢⱼ²/(wᵢ*wⱼ*))      → ĉ = Σᵢ<ⱼ Qᵢⱼ / Σᵢ<ⱼ ((T − 2) + Sᵢⱼ²/(wᵢ*wⱼ*))
//   Kᵢⱼ = τ²δᵢⱼ + σ²/wⱼ* δᵢⱼ + c Sᵢⱼ/(wᵢ*wⱼ*)(1 − δᵢⱼ),  τ̂² by eq. (39) on this Σ̂.
// Run: node studies/common-rho-mom.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const LAWS = {
  'two-point κ=-2': (r) => (r() < 0.5 ? -1 : 1),
  'normal κ=0': (r) => r.normal(),
  'gamma2 κ=3': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'gamma¼ κ=24': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
};
function fitCBS(data) {
  const J = data.X.length, T = data.X[0].length, { wt, m } = E.cohortMeans(data);
  const S = [], Q = [];
  for (let i = 0; i < J; i++) { S.push([]); Q.push([]); for (let j = 0; j < J; j++) {
    let s = 0, q = 0;
    for (let t = 0; t < T; t++) { const c = Math.sqrt(data.w[i][t] * data.w[j][t]); s += c; q += c * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]); }
    S[i].push(s); Q[i].push(q);
  } }
  let qd = 0; for (let j = 0; j < J; j++) qd += Q[j][j];
  const s2 = qd / (J * (T - 1));
  let qn = 0, qa = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { qn += Q[i][j]; qa += (T - 2) + S[i][j] ** 2 / (wt[i] * wt[j]); }
  const cRaw = qn / qa, c = Math.min(Math.max(cRaw, 0), s2 * (1 - 1e-9));   // 0 ≤ ρ̂ < 1
  const Sig = S.map((row, i) => row.map((x, j) => (i === j ? s2 / wt[i] : c * x / (wt[i] * wt[j]))));
  const t2 = Math.max(E.thesisTau(m, wt, Sig).tau2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return { rates: E.blend(m, t2 > 0 ? z : z.map(() => 0), b).rates, rho: cRaw / s2 };
}
module.exports = { fitCBS };
if (require.main === module) {
  console.log(`draws ${N}; error relative to the floor (100 = floor); ρ̂ = ĉ/σ̂² (mean, before clipping)`);
  console.log('law            J  T  ρ   |  BS  correlated-BS (ρ̂)');
  for (const [J, T] of [[4, 10], [8, 5], [8, 10], [20, 10]]) for (const [name, law] of Object.entries(LAWS)) for (const rho of [0, 0.3, 0.6, 0.9]) {
    const world = E.makeWorld({ J, T, rho }), fl = E.floorBlend(world), r = E.rng(2026);
    r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
    const a = { fl: 0, bs: 0, c: 0, rho: 0 };
    for (let n = 0; n < N; n++) {
      const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
      a.fl += se(fl.apply(data).rates); a.bs += se(E.fitBS(data).rates);
      const f = fitCBS(data); a.c += se(f.rates); a.rho += f.rho;
    }
    const rel = (x) => (x / a.fl * 100).toFixed(0).padStart(4);
    console.log(`${name.padEnd(14)} ${String(J).padEnd(2)} ${String(T).padEnd(2)} ${rho.toFixed(1)} | ${rel(a.bs)} ${rel(a.c)} (${(a.rho / N).toFixed(2)})`);
  }
}
