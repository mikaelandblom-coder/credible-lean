// Real data: workers' compensation, 121 occupation classes × 7 years (Klugman 1992, from NCCI),
// payroll as exposure, losses for permanent partial disability. studies/data/workerscomp.csv (R package
// insuranceData, data(WorkersComp)). Unlike Hachemeister (S85), volumes span five orders of magnitude, so z
// covers [0, 1]. Ratio = losses per 100 of payroll; volume = payroll in $M (a zero-payroll year has weight 0).
// Held out as in Klugman and Frees et al.: fit years 1..k, predict year k + 1. Run: node studies/runs/workerscomp.js
'use strict';
const fs = require('fs'), path = require('path');
const E = require('../../app/engine.js');
const sum = (a) => a.reduce((s, x) => s + x, 0);
const rows = fs.readFileSync(path.join(__dirname, '../data/workerscomp.csv'), 'utf8').split('\n')
  .filter((l) => l && !l.startsWith('#') && !l.startsWith('CL')).map((l) => l.split(',').map(Number));
const cls = [...new Set(rows.map((r) => r[0]))].sort((a, b) => a - b), T = 7, J = cls.length;
const X = cls.map(() => Array(T).fill(0)), W = cls.map(() => Array(T).fill(0));
for (const [c, y, pr, loss] of rows) { const j = cls.indexOf(c); W[j][y - 1] = pr / 1e6; X[j][y - 1] = pr > 0 ? 100 * loss / pr : 0; }
const cut = (a, t0, t1) => a.map((r) => r.slice(t0, t1));
const q = (a, p) => { const s = [...a].sort((x, y) => x - y); return s[Math.min(s.length - 1, Math.floor(p * s.length))]; };
const qs = (a, d = 3) => [0, 0.1, 0.5, 0.9, 1].map((p) => q(a, p).toFixed(d)).join(' / ');

function rhoZero(data) {
  const vc = E.fitVC(data), { m, wt } = E.cohortMeans(data);
  const Sig = wt.map((x, i) => wt.map((_, j) => (i === j ? vc.sigma2[i] / x : 0)));
  const t2 = Math.max(E.thesisTau(m, wt, Sig).tau2, 0);
  const K = Sig.map((r, i) => r.map((x, j) => (i === j ? x + t2 : x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return { z, rates: E.blend(m, z, b).rates };
}
// Year index: the portfolio's payroll-weighted loss ratio per year over its mean (estimated from 121 classes,
// so the correlation it induces between classes, about −1/J, is negligible).
function detrend(data) {
  const T = data.X[0].length;
  const idx = Array.from({ length: T }, (_, t) => sum(data.X.map((r, j) => data.w[j][t] * r[t])) / sum(data.w.map((r) => r[t])));
  const mi = sum(idx) / T;
  return { idx: idx.map((x) => x / mi), data: { X: data.X.map((r) => r.map((x, t) => x * mi / idx[t])), w: data.w } };
}
const FITS = {
  own: (d) => E.cohortMeans(d).m, pool: (d) => E.fitPool(d).rates, BS: (d) => E.fitBS(d).rates,
  cBS: (d) => E.fitVC(d).rates, BLUP: (d) => E.fitBLUP(d).rates, 'cBS rho=0': (d) => rhoZero(d).rates,
  'cBS pooled': (d) => E.fitVC(d, { pooled: true }).rates,
};

{
  const data = { X, w: W }, { m, wt } = E.cohortMeans(data), bs = E.fitBS(data), vc = E.fitVC(data);
  console.log(`workers' compensation: J = ${J} classes, T = ${T} years; ratio = losses per 100 payroll`);
  console.log(`payroll per class ($M, 7 years) min/10%/median/90%/max: ${qs(wt, 1)}`);
  console.log(`class means: ${qs(m)}`);
  console.log(`BS   mu ${bs.mu.toFixed(3)}  sigma2 ${bs.sigma2.toFixed(3)}  tau2 ${bs.tau2.toFixed(4)}   z: ${qs(bs.z, 2)}`);
  console.log(`cBS  mu ${vc.mu.toFixed(3)}  rho ${vc.rhoRaw.toFixed(3)}  tau2 ${vc.tau2.toFixed(4)}  z: ${qs(vc.z, 2)}`);
  console.log(`     sigma~2: ${qs(vc.sigma2, 2)}   b: ${qs(vc.b, 4)}`);
  const dt = detrend(data), vd = E.fitVC(dt.data);
  console.log(`year index: ${dt.idx.map((x) => x.toFixed(3)).join(' ')}`);
  console.log(`detrended cBS  rho ${vd.rhoRaw.toFixed(3)}  tau2 ${vd.tau2.toFixed(4)}  z: ${qs(vd.z, 2)}`);
  const d = vc.rates.map((x, j) => x - bs.rates[j]);
  console.log(`cBS - BS rates: ${qs(d, 3)}`);
  const top = [...m.keys()].sort((a, b) => Math.abs(d[b]) - Math.abs(d[a])).slice(0, 4);
  for (const j of top) console.log(`  class ${cls[j]}: payroll $${wt[j].toFixed(1)}M, own ${m[j].toFixed(2)}, BS ${bs.rates[j].toFixed(2)} (z ${bs.z[j].toFixed(2)}), cBS ${vc.rates[j].toFixed(2)} (z ${vc.z[j].toFixed(2)}, sigma~2 ${vc.sigma2[j].toFixed(1)})`);
}

console.log('\nheld out: fit years 1..k, predict year k+1; payroll-weighted MSE of the year-(k+1) ratio, relative to pool = 100');
console.log('(next year\'s own noise is in every column; "rel" rescales each fit\'s rates to that year\'s total: relativities only)');
const names = Object.keys(FITS);
console.log('  k  data      | ' + names.map((n) => n.padStart(11)).join(''));
const tot = {};
for (const dtr of [false, true]) for (const k of [3, 4, 5, 6]) {
  let fit = { X: cut(X, 0, k), w: cut(W, 0, k) };
  if (dtr) fit = detrend(fit).data;
  const y = X.map((r) => r[k]), w = W.map((r) => r[k]), wsum = sum(w);
  const R = names.map((n) => FITS[n](fit));
  for (const rel of [false, true]) {
    const sc = R.map((r) => {
      const g = rel ? sum(w.map((x, j) => x * y[j])) / sum(w.map((x, j) => x * r[j])) : 1;
      return sum(r.map((x, j) => w[j] * (g * x - y[j]) ** 2)) / wsum;
    });
    const key = `${dtr ? 'detr' : 'raw '} ${rel ? 'rel' : 'abs'}`;
    tot[key] = tot[key] || names.map(() => 0);
    sc.forEach((v, i) => { tot[key][i] += v; });
    console.log(`  ${k}  ${key}  | ` + sc.map((v) => (100 * v / sc[1]).toFixed(1).padStart(11)).join(''));
  }
}
console.log('sum over k = 3..6, relative to pool:');
for (const key in tot) console.log(`     ${key}  | ` + tot[key].map((v) => (100 * v / tot[key][1]).toFixed(1).padStart(11)).join(''));

// The payroll-weighted score is dominated by the large classes, where every fit has z ≈ 1. Credibility matters
// for the small ones: the same score over the classes below the median payroll (of years 1..k).
console.log('\nsmall classes only (payroll of years 1..k below the median), raw data, relative to pool:');
const totS = names.map(() => 0);
for (const k of [3, 4, 5, 6]) {
  const fit = { X: cut(X, 0, k), w: cut(W, 0, k) }, wt = E.cohortMeans(fit).wt, med = q(wt, 0.5);
  const small = wt.map((x) => x < med), y = X.map((r) => r[k]), w = W.map((r, j) => (small[j] ? r[k] : 0)), wsum = sum(w);
  const sc = names.map((n) => { const r = FITS[n](fit); return sum(r.map((x, j) => w[j] * (x - y[j]) ** 2)) / wsum; });
  sc.forEach((v, i) => { totS[i] += v; });
  console.log(`  ${k}            | ` + sc.map((v) => (100 * v / sc[1]).toFixed(1).padStart(11)).join(''));
}
console.log('  sum          | ' + totS.map((v) => (100 * v / totS[1]).toFixed(1).padStart(11)).join(''));
// Classes the variance credibility trusts fully because their own losses were all zero in years 1..k.
for (const k of [3, 6]) {
  const fit = { X: cut(X, 0, k), w: cut(W, 0, k) }, vc = E.fitVC(fit), { m, wt } = E.cohortMeans(fit);
  const zero = m.map((x, j) => j).filter((j) => m[j] === 0);
  console.log(`k = ${k}: ${zero.length} classes with no losses in years 1..k; cBS rates ${zero.map((j) => vc.rates[j].toFixed(2)).join(' ')}, ` +
    `BS ${zero.map((j) => E.fitBS(fit).rates[j].toFixed(2)).join(' ')}; their year-${k + 1} ratios ${zero.map((j) => X[j][k].toFixed(2)).join(' ')} (payroll $M ${zero.map((j) => wt[j].toFixed(1)).join(' ')})`);
}
