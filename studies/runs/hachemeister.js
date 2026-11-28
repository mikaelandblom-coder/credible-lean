// Real data: Hachemeister (1975), bodily-injury average claim amounts, 5 US states × 12 quarters
// (1970 Q3 – 1973 Q2), weights = numbers of claims. Data as shipped in the R package actuar
// (`data(hachemeister)`, GPL; read from github.com/cran/actuar data/hachemeister.rda).
// Compares Bühlmann–Straub with the app's fit (correlated BS, one ρ, credibility-weighted σ̃ⱼ²) and the
// plug-in BLUP on the same K̂, in full and held out. Run: node studies/runs/hachemeister.js
'use strict';
const E = require('../../app/engine.js');
const sum = (a) => a.reduce((s, x) => s + x, 0);
const X = [
  [1738, 1642, 1794, 2051, 2079, 2234, 2032, 2035, 2115, 2262, 2267, 2517],
  [1364, 1408, 1597, 1444, 1342, 1675, 1470, 1448, 1464, 1831, 1612, 1471],
  [1759, 1685, 1479, 1763, 1674, 2103, 1502, 1622, 1828, 2155, 2233, 2059],
  [1223, 1146, 1010, 1257, 1426, 1532, 1953, 1123, 1343, 1243, 1762, 1306],
  [1456, 1499, 1609, 1741, 1482, 1572, 1606, 1735, 1607, 1573, 1613, 1690],
];
const W = [
  [7861, 9251, 8706, 8575, 7917, 8263, 9456, 8003, 7365, 7832, 7849, 9077],
  [1622, 1742, 1523, 1515, 1622, 1602, 1964, 1515, 1527, 1748, 1654, 1861],
  [1147, 1357, 1329, 1204, 998, 1077, 1277, 1218, 896, 1003, 1108, 1121],
  [407, 396, 348, 341, 315, 328, 352, 331, 287, 384, 321, 342],
  [2902, 3172, 3046, 3068, 2693, 2910, 3275, 2697, 2663, 3017, 3242, 3425],
];
const J = X.length, T = X[0].length;
const cut = (a, t0, t1) => a.map((r) => r.slice(t0, t1));
const f = (x, d = 0) => (Array.isArray(x) ? x.map((v) => f(v, d)).join(' ') : x.toFixed(d).padStart(d ? 7 : 6));

function show(label, data) {
  const bs = E.fitBS(data), vc = E.fitVC(data), bl = E.fitBLUP(data), { m, wt } = E.cohortMeans(data);
  const cOwn = (z, b) => z.map((zj, j) => zj + (1 - zj) * b[j]);
  console.log(`\n== ${label} ==`);
  console.log(`state means        ${f(m)}   claims ${f(wt)}`);
  console.log(`BS   σ̂² ${bs.sigma2.toExponential(4)} τ̂² ${bs.tau2.toFixed(0)}  μ̂ ${bs.mu.toFixed(1)}`);
  console.log(`BS   z             ${f(bs.z, 3)}`);
  console.log(`BS   rates         ${f(bs.rates)}`);
  console.log(`cBS  ρ̂ ${vc.rhoRaw.toFixed(3)} (used ${vc.rho.toFixed(3)})  τ̂² ${vc.tau2.toFixed(0)}  μ̂ ${vc.mu.toFixed(1)}  β² ${vc.between.toExponential(3)}`);
  console.log(`cBS  σ̃ⱼ²/1e6       ${f(vc.sigma2.map((x) => x / 1e6), 1)}`);
  console.log(`cBS  b             ${f(vc.b, 3)}`);
  console.log(`cBS  z             ${f(vc.z, 3)}`);
  console.log(`cBS  own weight c  ${f(cOwn(vc.z, vc.b), 3)}`);
  console.log(`cBS  rates         ${f(vc.rates)}`);
  console.log(`BLUP rates         ${f(bl.rates)}`);
  return { bs, vc, bl, m };
}

console.log('Hachemeister (1975) data, 5 states × 12 quarters; amounts in dollars per claim');
show('all 12 quarters', { X, w: W });

// Raw residual correlation of the quarter-to-quarter deviations, claim-weighted (the ρ̂ moment equation, by pair).
{
  const { m } = E.cohortMeans({ X, w: W });
  const r = (i, j) => sum(X[i].map((x, t) => Math.sqrt(W[i][t] * W[j][t]) * (x - m[i]) * (X[j][t] - m[j]))) /
    Math.sqrt(sum(X[i].map((x, t) => W[i][t] * (x - m[i]) ** 2)) * sum(X[j].map((x, t) => W[j][t] * (x - m[j]) ** 2)));
  console.log('\npairwise residual correlations (weighted):');
  for (let i = 0; i < J; i++) console.log('  ' + Array.from({ length: J }, (_, j) => r(i, j).toFixed(2).padStart(6)).join(''));
}

// Held out: fit on quarters [0, k), score each fit's rates against the claim-weighted mean of quarters [k, 12).
// Inflation lifts every state after the cut, so the score has a common lag; the second score removes the
// portfolio-wide change (each rate rescaled so its claim-weighted mean matches the held-out one): relativities only.
console.log('\nheld out: fit on the first k quarters, target = each state\'s claim-weighted mean of the rest');
console.log('claim-weighted RMSE in $ (raw | relativities only)');
console.log('  k   |    own   pool     BS    cBS   BLUP');
for (const k of [4, 6, 8]) {
  const fit = { X: cut(X, 0, k), w: cut(W, 0, k) }, hold = { X: cut(X, k, T), w: cut(W, k, T) };
  const { m: tgt, wt: wh } = E.cohortMeans(hold), tot = sum(wh);
  const { m } = E.cohortMeans(fit), bs = E.fitBS(fit), vc = E.fitVC(fit), bl = E.fitBLUP(fit), pool = E.fitPool(fit);
  const score = (rates, rel) => {
    const g = rel ? sum(wh.map((x, j) => x * tgt[j])) / sum(wh.map((x, j) => x * rates[j])) : 1;
    return Math.sqrt(sum(rates.map((x, j) => wh[j] * (g * x - tgt[j]) ** 2)) / tot);
  };
  const row = (rel) => [m, pool.rates, bs.rates, vc.rates, bl.rates].map((r) => score(r, rel).toFixed(0).padStart(6)).join(' ');
  console.log(`  ${k}   | ${row(false)}   |   ${row(true)}    (ρ̂ ${vc.rhoRaw.toFixed(2)}, BS z ${f(bs.z, 2)}, cBS z ${f(vc.z, 2)})`);
}

// What moves the rates: the per-state variances σ̃ⱼ² or the correlation ρ̂? Same σ̃ⱼ², ρ set to 0, τ̂² re-estimated.
function rhoZero(data) {
  const vc = E.fitVC(data), { m, wt } = E.cohortMeans(data);
  const Sig = wt.map((x, i) => wt.map((_, j) => (i === j ? vc.sigma2[i] / x : 0)));
  const t2 = Math.max(E.thesisTau(m, wt, Sig).tau2, 0);
  const K = Sig.map((r, i) => r.map((x, j) => (i === j ? x + t2 : x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return { z, b, rates: E.blend(m, z, b).rates, t2 };
}
{
  const r0 = rhoZero({ X, w: W });
  console.log('\ndecomposition (all quarters): σ̃ⱼ² per state, ρ = 0');
  console.log(`  z ${f(r0.z, 3)}   rates ${f(r0.rates)}   τ̂² ${r0.t2.toFixed(0)}`);
}

// Inflation is a common trend, not mean-zero noise. Remove a common log-linear trend (one slope for all
// states, state intercepts, claim-weighted least squares) and refit: how much of ρ̂ was the trend?
{
  const tb = (T - 1) / 2;
  let sxy = 0, sxx = 0;
  for (let j = 0; j < J; j++) {
    const lw = sum(W[j]), ly = sum(X[j].map((x, t) => W[j][t] * Math.log(x))) / lw, lt = sum(W[j].map((w, t) => w * t)) / lw;
    for (let t = 0; t < T; t++) { sxy += W[j][t] * (t - lt) * (Math.log(X[j][t]) - ly); sxx += W[j][t] * (t - lt) ** 2; }
  }
  const g = sxy / sxx, Xd = X.map((r) => r.map((x, t) => x * Math.exp(-g * (t - tb))));
  console.log(`\ncommon trend: ${(100 * (Math.exp(g) - 1)).toFixed(2)}% per quarter (${(100 * (Math.exp(4 * g) - 1)).toFixed(1)}% a year); rates below at mid-period`);
  const d = show('detrended by the common trend', { X: Xd, w: W });
  const r0 = rhoZero({ X: Xd, w: W });
  console.log(`ρ = 0 z ${f(r0.z, 3)}   rates ${f(r0.rates)}`);
  // Held out after detrending with the trend fitted on the first k quarters only; target deflated with it too.
  console.log('held out, detrended with the trend of the first k quarters (claim-weighted RMSE in $):');
  console.log('  k   |    own   pool     BS    cBS   BLUP  cBS ρ=0');
  for (const k of [4, 6, 8]) {
    let sxy2 = 0, sxx2 = 0;
    for (let j = 0; j < J; j++) {
      const w = W[j].slice(0, k), x = X[j].slice(0, k), lw = sum(w);
      const ly = sum(x.map((v, t) => w[t] * Math.log(v))) / lw, lt = sum(w.map((v, t) => v * t)) / lw;
      for (let t = 0; t < k; t++) { sxy2 += w[t] * (t - lt) * (Math.log(x[t]) - ly); sxx2 += w[t] * (t - lt) ** 2; }
    }
    const gk = sxy2 / sxx2, Xk = X.map((r) => r.map((x, t) => x * Math.exp(-gk * t)));
    const fit = { X: cut(Xk, 0, k), w: cut(W, 0, k) }, hold = { X: cut(Xk, k, T), w: cut(W, k, T) };
    const { m: tgt, wt: wh } = E.cohortMeans(hold), tot = sum(wh), { m } = E.cohortMeans(fit);
    const rs = [m, E.fitPool(fit).rates, E.fitBS(fit).rates, E.fitVC(fit).rates, E.fitBLUP(fit).rates, rhoZero(fit).rates];
    const sc = (rates) => Math.sqrt(sum(rates.map((x, j) => wh[j] * (x - tgt[j]) ** 2)) / tot).toFixed(0).padStart(6);
    console.log(`  ${k}   | ${rs.map(sc).join(' ')}    (ρ̂ ${E.fitVC(fit).rhoRaw.toFixed(2)})`);
  }
}
