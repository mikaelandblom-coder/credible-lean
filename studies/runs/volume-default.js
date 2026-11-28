// S84. Purpose: may "Volumes vary by year" become the app's default? (PLAN Pending "Realistic volumes", step 3.)
// Reruns the simulation checks the page quotes, with the volumes of one shape (the current default) and
// varying by year (volNoise 0.2, volTrend 0.05, two volume patterns volSeed 1, 2):
//   A. Noise shape readouts (Engine.noiseDiagnostics, Engine.noiseShape): the predicted skew bias of the
//      same-years power against its seen mean, the fitted skew link against the world's, the pooled ĝ against
//      the world's skewness, the cross-fitted power's SD, and γ̂N (mean, median, SD).
//   B. Skew bias (Engine.skewBias, as skew-bias.js): predicted against simulated portfolio bias of the unbalanced
//      fits, simulated against BS on the same draws (BS is exposure-balanced for any volumes).
// S76's regret under varying volumes is balance-rule.js --vol (balance-rule-vol.out.txt).
// Run: node studies/runs/volume-default.js [drawsA] (B uses drawsA·3/8)
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 4000 });
const NB = Math.round(N * 3 / 8);
const VOL = [['one shape', {}], ['vary, pattern 1', { volNoise: 0.2, volTrend: 0.05, volSeed: 1 }], ['vary, pattern 2', { volNoise: 0.2, volTrend: 0.05, volSeed: 2 }]];
const A_WORLDS = [['default', {}], ['T = 5, shape 1', { T: 5, noiseShape: 1 }], ['normal', { normal: true }], ['ρ = 0.6', { rho: 0.6 }]];
const B_WORLDS = [['default', {}], ['T = 4, shape 1', { T: 4, noiseShape: 1 }], ['normal', { normal: true }], ['ρ = 0.6', { rho: 0.6 }],
  ['ρ = 0.6, T = 5', { rho: 0.6, T: 5 }], ['ρ = 0.6, J = 20', { rho: 0.6, J: 20 }]];
const IDS = ['vc', 'blup', 'blupPool'];
const tasks = [];
for (const [wl, wp] of A_WORLDS) for (const [vl, vp] of VOL) tasks.push({ part: 'A', wl, vl, p: Object.assign({}, wp, vp) });
for (const [wl, wp] of B_WORLDS) for (const [vl, vp] of VOL) tasks.push({ part: 'B', wl, vl, p: Object.assign({}, wp, vp) });

const mean = (v) => L.sum(v) / v.length, sd = (v) => { const m = mean(v); return Math.sqrt(L.sum(v.map((x) => (x - m) ** 2)) / (v.length - 1)); };
const med = (v) => v.slice().sort((x, y) => x - y)[v.length >> 1];

function partA(t) {
  const world = E.makeWorld(t.p), pr = world.params, r = E.rng(84);
  const a = Math.sqrt(Math.max(pr.rho, 0)), b = Math.sqrt(1 - Math.max(pr.rho, 0));
  const trueSkew = pr.normal ? 0 : (a ** 3 + b ** 3) * 2 / Math.sqrt(pr.noiseShape);
  const worldLink = pr.normal ? 0 : L.sum(world.truth.sigmaj2.map((s2, j) =>
    E.skewLink(world.w[j], Math.pow(s2, 1.5) * (a ** 3 + b ** 3) * 2 / Math.sqrt(pr.noiseShape), 1.5, s2, world.truth.mu).link)) / world.J;
  const c = { pred: [], same: [], power: [], link: [], skew: [], kurt: [], rskew: [] };
  for (let n = 0; n < N; n++) {
    const { data } = E.draw(world, r), D = E.noiseDiagnostics(data), S = E.noiseShape(data);
    if (D.powerSkewBias != null && D.powerSame) { c.pred.push(D.powerSkewBias); c.same.push(D.powerSame.b); }
    if (D.power) c.power.push(D.power.b);
    if (Number.isFinite(D.link)) c.link.push(D.link);
    if (Number.isFinite(D.skew)) c.skew.push(D.skew);
    if (S) { c.kurt.push(S.kurt); c.rskew.push(S.skew); }
  }
  const wv = world.w.map((row) => row.map((x) => x / L.sum(row)));
  const shapeSpread = Math.max(...wv.flatMap((row, j) => row.map((x, s) => Math.abs(x - wv[0][s]))));
  return { t, trueSkew, worldLink, shapeSpread, pred: mean(c.pred), same: mean(c.same), powerM: mean(c.power), powerSD: sd(c.power),
    link: mean(c.link), skew: mean(c.skew), kurtM: mean(c.kurt), kurtMed: med(c.kurt), kurtSD: sd(c.kurt), rskew: mean(c.rskew) };
}

function partB(t) {
  const world = E.makeWorld(t.p), wt = world.w.map(L.sum), wall = L.sum(wt), out = {};
  for (const id of IDS) {
    const r = E.rng(77), sim = [], pred = [];
    for (let n = 0; n < NB; n++) {
      const { data } = E.draw(world, r), f = E.MODELS[id].fit(data), g = E.fitBS(data);
      sim.push(L.sum(f.rates.map((x, j) => wt[j] * (x - g.rates[j]))) / wall);
      pred.push(E.skewBias(id, data).portfolio);
    }
    out[id] = { sim: L.meanSE(sim), pred: mean(pred) };
  }
  return { t, out };
}

L.mapWorlds(__filename, tasks, (t) => (t.part === 'A' ? partA(t) : partB(t)), jobs, (t) => (t.part === 'B' ? 3 : 1)).then((rows) => {
  const f2 = (x) => (x >= 0 ? ' ' : '') + x.toFixed(2);
  console.log(`A. Noise shape readouts, ${N} draws (gamma noise unless normal). Power: same-years slope (truth 0) and its predicted skew bias;`);
  console.log('   link: fitted skew link (mean over draws) against the world’s; ĝ pooled skewness against the world’s; γ̂N mean / median / SD.');
  console.log('world            volumes          | max |Δshare| | power same  pred | cross-fit mean  SD | link fit  world | ĝ fit  world | resid skew | γ̂N mean  med   SD');
  for (const r of rows.filter((x) => x.t.part === 'A')) {
    console.log(`${r.t.wl.padEnd(16)} ${r.t.vl.padEnd(16)} |   ${r.shapeSpread.toFixed(3)}     |   ${f2(r.same)} ${f2(r.pred)} |    ${f2(r.powerM)}    ${r.powerSD.toFixed(2)} |  ${f2(r.link)}  ${f2(r.worldLink)} | ${f2(r.skew)}  ${f2(r.trueSkew)} |   ${f2(r.rskew)}    |  ${f2(r.kurtM)} ${f2(r.kurtMed)} ${r.kurtSD.toFixed(2)}`);
  }
  console.log(`\nB. Skew bias of the unbalanced fits, portfolio, % of the tariff, ${NB} draws: simulated ± 2 SE | predicted mean`);
  console.log('world            volumes          | ' + IDS.map((id) => id.padEnd(22)).join('| '));
  for (const r of rows.filter((x) => x.t.part === 'B')) {
    console.log(`${r.t.wl.padEnd(16)} ${r.t.vl.padEnd(16)} | ` + IDS.map((id) => { const o = r.out[id];
      return `${f2(100 * o.sim.m)} ± ${(200 * o.sim.se).toFixed(2)} | ${f2(100 * o.pred)}`.padEnd(22); }).join('| '));
  }
});
