// Data-only choices, no hyperparameters: leave-one-year-out cross-validation (CV)
// to pick θ, or to pick the model, against the fixed rules. Run: node studies/damping-cv.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 400);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1];
const LAWS = {
  'normal κ=0': (r) => r.normal(),
  'gamma2 κ=3': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'gamma¼ κ=24': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
};
const sum = (a) => a.reduce((s, x) => s + x, 0);

function fullAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }).rates; } catch (e) { /* not PD */ }
  }
}
function rhoBar(data) {
  const { Sig } = E.sigmaHat(data), J = Sig.length;
  let s = 0, n = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
  return Math.max(-1, Math.min(1, s / n));
}
const thetaHat = (data) => { const rb = rhoBar(data), T = data.X[0].length; return rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1)); };
function commonRho(data) {
  const rb = Math.max(0, rhoBar(data)), th = thetaHat(data);
  const est = E.sigmaHat(data), Sig = est.Sig.map((row, i) => row.map((x, j) => (i === j ? x : rb * Math.sqrt(est.Sig[i][i] * est.Sig[j][j]))));
  const t2 = Math.max(E.thesisTau(est.m, est.wt, Sig).tau2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : th * x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return E.blend(est.m, t2 > 0 ? z : z.map(() => 0), b).rates;
}
const METHODS = {
  bs: (d) => E.fitBS(d).rates,
  fullRule: (d) => fullAt(d, thetaHat(d)),
  commonRho: commonRho,
};
GRID.forEach((th) => { METHODS['θ' + th] = (d) => fullAt(d, th); });

// Leave-one-year-out score: Σₜ Σⱼ wⱼₜ (Xⱼₜ − rateⱼ^(−t))².
function cvScore(data, method) {
  const T = data.X[0].length;
  let s = 0;
  for (let t = 0; t < T; t++) {
    const d = { w: data.w.map((row) => row.filter((_, u) => u !== t)), X: data.X.map((row) => row.filter((_, u) => u !== t)) };
    const r = method(d);
    data.X.forEach((row, j) => { s += data.w[j][t] * (row[t] - r[j]) ** 2; });
  }
  return s;
}
const argmin = (obj) => Object.entries(obj).reduce((a, b) => (b[1] < a[1] ? b : a))[0];

console.log(`draws ${N}; error relative to the floor (100 = floor)`);
console.log('law          J  T  ρ   | BS   fullRule commonρ | best θ (val) | CV-θ (mean θ) | CV-model (picks: bs/full/cρ)');
for (const [J, T] of [[8, 5], [8, 10], [20, 10]]) for (const [name, law] of Object.entries(LAWS)) for (const rho of [0, 0.3, 0.6, 0.9]) {
  const world = E.makeWorld({ J, T, rho }), fl = E.floorBlend(world), r = E.rng(2026);
  r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
  const acc = { floor: 0, cvTheta: 0, cvThetaVal: 0, cvModel: 0 }, picks = { bs: 0, fullRule: 0, commonRho: 0 };
  for (const k in METHODS) acc[k] = 0;
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, r);
    acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
    const rates = {};
    for (const k in METHODS) { rates[k] = METHODS[k](data); acc[k] += E.weightedSE(data, rates[k], levels); }
    const cvT = {}; GRID.forEach((th) => { cvT['θ' + th] = cvScore(data, METHODS['θ' + th]); });
    const bt = argmin(cvT); acc.cvTheta += E.weightedSE(data, rates[bt], levels); acc.cvThetaVal += +bt.slice(1);
    const cvM = { bs: cvScore(data, METHODS.bs), fullRule: cvScore(data, METHODS.fullRule), commonRho: cvScore(data, METHODS.commonRho) };
    const bm = argmin(cvM); picks[bm]++; acc.cvModel += E.weightedSE(data, rates[bm], levels);
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
  const thKeys = GRID.map((th) => 'θ' + th), bk = thKeys.reduce((a, b) => (acc[b] < acc[a] ? b : a));
  const pc = (x) => Math.round(100 * x / N);
  console.log(`${name.padEnd(12)} ${String(J).padEnd(2)} ${String(T).padEnd(2)} ${rho.toFixed(1)} | ${rel(acc.bs)} ${rel(acc.fullRule)}    ${rel(acc.commonRho)}   | ${rel(acc[bk])} (${bk.slice(1).padEnd(4)})  | ${rel(acc.cvTheta)} (${(acc.cvThetaVal / N).toFixed(2)})   | ${rel(acc.cvModel)} (${pc(picks.bs)}/${pc(picks.fullRule)}/${pc(picks.commonRho)})`);
}
