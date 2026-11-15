// SURE (Stein 1981) for credibility: m = region means, Σ = their noise covariance, h(m) = rates.
// Under normal noise, given the true levels μ:
//   E‖h(m) − μ‖²_W = E[ ‖h(m) − m‖²_W − tr(WΣ) + 2 tr(W Dh Σ) ],  Dh = ∂h/∂m,  W = diag(wⱼ*)/w**.
// (A) SURE as an error estimate for the moment fit (variance credibility), Dh by finite differences
//     (shift region j's years by δ: within-region estimates unchanged, τ̂² and the rates move);
//     against the jackknife MSEP and the actual error.
// (B) SURE-chosen shrinkage (Xie, Kou & Brown 2012): τ² minimising SURE, Σ̂ kept from the moment fit.
// Σ is the estimated Σ̂ throughout (data only). Run: node studies/sure.js [draws]
'use strict';
const E = require('../app/engine.js');
const { msep, params, blendWith, design } = require('./msep.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

function sigmaOf(p, des) {
  const sd = p.s2.map(Math.sqrt);
  return des.S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / des.wt[i] : p.rho * sd[i] * sd[j] * x / (des.wt[i] * des.wt[j]))));
}
// SURE given h, its Jacobian D, Σ and weights W (vector).
function sure(h, m, D, Sig, W) {
  const J = m.length; let s = 0;
  for (let j = 0; j < J; j++) {
    s += W[j] * ((h[j] - m[j]) ** 2 - Sig[j][j]);
    let dS = 0; for (let k = 0; k < J; k++) dS += D[j][k] * Sig[k][j];
    s += 2 * W[j] * dS;
  }
  return s;
}
function rateOf(data) { const des = design(data.w); return blendWith(params(data), des, E.cohortMeans(data).m).rates; }
// (A) SURE of the moment fit.
function sureMoment(data) {
  const des = design(data.w), p = params(data), m = E.cohortMeans(data).m, h = blendWith(p, des, m).rates;
  const J = m.length, delta = 1e-5 * (1 + Math.abs(m[0])), D = h.map(() => Array(J).fill(0));
  for (let k = 0; k < J; k++) {
    const X = data.X.map((row, j) => (j === k ? row.map((x) => x + delta) : row));
    const hk = rateOf({ w: data.w, X });
    for (let j = 0; j < J; j++) D[j][k] = (hk[j] - h[j]) / delta;
  }
  const W = des.wt.map((x) => x / sum(des.wt));
  return { h, est: sure(h, m, D, sigmaOf(p, des), W) };
}
// (B) τ² chosen by SURE: for fixed τ², h = A m with A = Z + (I − Z) 1 bᵀ (linear in m).
function fitSure(data) {
  const des = design(data.w), p = params(data), m = E.cohortMeans(data).m, Sig = sigmaOf(p, des), J = m.length;
  const W = des.wt.map((x) => x / sum(des.wt));
  const score = (t2) => {
    const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : x)));
    const { b, z } = E.bestBlendWeights(K, t2), A = z.map((zj, j) => b.map((bk, k) => (j === k ? zj : 0) + (1 - zj) * bk));
    const h = A.map((row) => sum(row.map((a, k) => a * m[k])));
    return { s: sure(h, m, A, Sig, W), h };
  };
  // τ² on a log grid around the scale of Σ̂, then a golden-section refinement; τ² = 0 allowed.
  const scale = sum(Sig.map((row, j) => row[j])) / J;
  let best = { t2: 0, ...score(0) };
  for (let e = -4; e <= 3; e += 0.25) { const t2 = scale * Math.pow(10, e), o = score(t2); if (o.s < best.s) best = { t2, ...o }; }
  if (best.t2 > 0) {
    let lo = best.t2 / Math.pow(10, 0.25), hi = best.t2 * Math.pow(10, 0.25);
    for (let it = 0; it < 30; it++) {
      const a = hi - (hi - lo) / 1.618, c = lo + (hi - lo) / 1.618;
      if (score(a).s < score(c).s) hi = c; else lo = a;
    }
    const t2 = (lo + hi) / 2, o = score(t2); if (o.s < best.s) best = { t2, ...o };
  }
  return { rates: best.h, t2: best.t2, tMoment: p.t2 };
}
module.exports = { fitSure, sureMoment };
if (require.main !== module) return;

const LAWS = { normal: (r) => r.normal(), gamma2: (r) => (r.gamma(2) - 2) / Math.SQRT2, 'gamma¼': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; } };
function run(label, J, T, sigF, rho, law) {
  const world = E.makeWorld({ J, T }), { w } = world, tau2 = world.truth.tau2, s = Math.sqrt(world.truth.sigma2);
  const wt = w.map(sum), wall = sum(wt), sig = sigF.map((f) => s * f), r = E.rng(17), L = LAWS[law], K = [];
  for (let i = 0; i < J; i++) { K.push([]); for (let j = 0; j < J; j++) {
    let S = 0; for (let t = 0; t < T; t++) S += Math.sqrt(w[i][t] * w[j][t]);
    K[i].push(sig[i] * sig[j] * (i === j ? 1 : rho) * S / (wt[i] * wt[j]) + (i === j ? tau2 : 0));
  } }
  const fl = E.bestBlendWeights(K, tau2);
  const a = { floor: 0, mom: 0, sur: 0, bs: 0, jack: 0, sure: 0, sureSq: 0, momSq: 0, cov: 0, tS: 0, tM: 0 };
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * (r.gamma(4) - 4) / 2);
    const eta = Array.from({ length: T }, () => L(r));
    const X = levels.map((lv, j) => Array.from({ length: T }, (_, t) => lv + sig[j] / Math.sqrt(w[j][t]) * (Math.sqrt(rho) * eta[t] + Math.sqrt(1 - rho) * L(r))));
    const data = { w, X }, m = E.cohortMeans(data).m, loss = (h) => sum(h.map((x, j) => wt[j] * (x - levels[j]) ** 2)) / wall;
    a.floor += loss(E.blend(m, fl.z, fl.b).rates); a.bs += loss(E.fitBS(data).rates);
    const sm = sureMoment(data), lm = loss(sm.h); a.mom += lm; a.momSq += lm * lm;
    a.sure += sm.est; a.sureSq += sm.est * sm.est; a.cov += sm.est * lm;
    a.jack += sum(msep(data).jack.map((x, j) => wt[j] * x)) / wall;
    const fs = fitSure(data); a.sur += loss(fs.rates); a.tS += fs.t2; a.tM += fs.tMoment;
  }
  const rel = (x) => (x / a.floor * 100).toFixed(0).padStart(4);
  const sd = (s, s2) => Math.sqrt(s2 / N - (s / N) ** 2);
  const corr = (a.cov / N - (a.sure / N) * (a.mom / N)) / (sd(a.sure, a.sureSq) * sd(a.mom, a.momSq));
  console.log(`${label.padEnd(26)} ${law.padEnd(7)} | ${rel(a.bs)} ${rel(a.mom)} ${rel(a.sur)} | ${(a.tM / N / tau2).toFixed(2)} ${(a.tS / N / tau2).toFixed(2)} | ${(a.jack / a.mom).toFixed(2)} ${(a.sure / a.mom).toFixed(2)}  ${corr.toFixed(2)}`);
}
console.log(`draws ${N}. Errors relative to the floor (100). τ̂²/τ² mean. MSEP: predicted/actual on average; corr = per-draw correlation of SURE with the actual loss.`);
console.log('world                      law     |  BS  mom SURE-τ | τ̂² mom SURE | jack SURE  corr');
for (const [J, T] of [[8, 10], [8, 5], [20, 10]]) {
  const one = Array(J).fill(1), spread = Array.from({ length: J }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5));
  for (const law of Object.keys(LAWS)) {
    run(`J=${J} T=${T} equal σ, ρ=0`, J, T, one, 0, law);
    run(`J=${J} T=${T} equal σ, ρ=0.6`, J, T, one, 0.6, law);
    run(`J=${J} T=${T} σⱼ spread, ρ=0.6`, J, T, spread, 0.6, law);
  }
}
