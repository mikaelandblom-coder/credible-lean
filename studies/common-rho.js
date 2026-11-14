// Common-correlation fit with no damping (θ = 1): fully data-determined, no formula from a
// distribution. Against θ̂ damping, BS and the full fit. Run: node studies/common-rho.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const LAWS = {
  'two-point κ=-2': (r) => (r() < 0.5 ? -1 : 1),
  'normal κ=0': (r) => r.normal(),
  'gamma2 κ=3': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'gamma¼ κ=24': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
};
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1];
function rhoBar(Sig) {
  const J = Sig.length; let s = 0, n = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
  return s / n;
}
const thetaHat = (rb, T) => rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1));
function commonRho(data, damp, pooled) {
  const est = E.sigmaHat(data), T = data.X[0].length, J = data.X.length;
  let v = est.Sig.map((row, j) => row[j]);
  if (pooled) { // BS-style pooled σ̂²: vⱼ = σ̂²/wⱼ*
    const s2 = v.reduce((a, x, j) => a + x * est.wt[j], 0) / J; v = est.wt.map((w) => s2 / w);
  }
  const rb = Math.min(Math.max(0, rhoBar(est.Sig)), 1 - 1e-9), th = damp ? thetaHat(rb, T) : 1;
  const Sig = v.map((vi, i) => v.map((vj, j) => (i === j ? vi : th * rb * Math.sqrt(vi * vj))));
  const t2 = Math.max(E.thesisTau(est.m, est.wt, Sig).tau2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return E.blend(est.m, t2 > 0 ? z : z.map(() => 0), b).rates;
}
function fullAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }).rates; } catch (e) { /* not PD */ }
  }
}
console.log(`draws ${N}; error relative to the floor (100 = floor)`);
console.log('law            J  T  ρ   |  BS  full θ̂ | cρ θ̂  cρ θ=1 | cρ pooled θ=1');
for (const [J, T] of [[4, 10], [8, 5], [8, 10], [20, 10]]) for (const [name, law] of Object.entries(LAWS)) for (const rho of [0, 0.3, 0.6, 0.9]) {
  const world = E.makeWorld({ J, T, rho }), fl = E.floorBlend(world), r = E.rng(2026);
  r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
  const a = { fl: 0, bs: 0, full: 0, cd: 0, c1: 0, cp: 0 };
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    a.fl += se(fl.apply(data).rates); a.bs += se(E.fitBS(data).rates);
    const rb = Math.max(-1, Math.min(1, rhoBar(E.sigmaHat(data).Sig)));
    a.full += se(fullAt(data, thetaHat(rb, T)));
    a.cd += se(commonRho(data, true, false)); a.c1 += se(commonRho(data, false, false)); a.cp += se(commonRho(data, false, true));
  }
  const rel = (x) => (x / a.fl * 100).toFixed(0).padStart(4);
  console.log(`${name.padEnd(14)} ${String(J).padEnd(2)} ${String(T).padEnd(2)} ${rho.toFixed(1)} | ${rel(a.bs)} ${rel(a.full)}   | ${rel(a.cd)} ${rel(a.c1)}   | ${rel(a.cp)}`);
}
