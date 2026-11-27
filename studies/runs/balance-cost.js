// S75. Purpose: check and size the cost-of-balancing identity (Credibility/BalanceCost.lean,
// integral_sum_sq_shift): balanced − raw exposure-weighted MSE = E(T − μ̄)² − E(r̄ − μ̄)², for corrBS
// balanced to the cross-fitted level (the app's switch) and to the exposure average Σ uⱼμ̂ⱼ.
// Worlds as S72/S74: regime app / thesis / thesisShape, ρ ∈ {0, 0.3, 0.6, 0.9}, σⱼ spread 0–2, T ∈ {5, 10}.
// Run: node studies/runs/balance-cost.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 400 });
const worlds = L.grid({ regime: ['app', 'thesis', 'thesisShape'], rho: [0, 0.3, 0.6, 0.9], noiseSpread: [0, 1, 2], T: [5, 10] })
  .filter((p) => p.regime !== 'thesisShape' || p.noiseSpread === 2);

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], dB = [], eT = [], eR = [], eX = [], gap = [];
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    const wt = data.w.map(L.sum), W = L.sum(wt), avg = (x) => L.sum(x.map((v, j) => wt[j] * v)) / W;
    const vc = E.fitVC(data), b = E.balanceFit(vc, data, { target: 'crossFit' }), mb = avg(levels), rb = avg(vc.rates);
    const d = se(b.rates) - se(vc.rates), t = (rb + b.shift - mb) ** 2, e = (rb - mb) ** 2;
    dB.push(d); eT.push(t); eR.push(e); gap.push(d - (t - e));
    eX.push((avg(E.cohortMeans(data).m) - mb) ** 2);
  }
  const f = L.meanSE(F).m, m = (x) => L.meanSE(x).m / f;
  return { p, cost: m(dB), eT: m(eT), eR: m(eR), eX: m(eX), gap: Math.max(...gap.map(Math.abs)) / f };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  console.log(`corrBS, ${N} draws. In % of the blend floor: cost = balanced (cross-fitted) − raw MSE; E(T − μ̄)² cross-fitted`);
  console.log('level; E(r̄ − μ̄)² corrBS\'s own exposure-weighted rate; E(ū̂ − μ̄)² the exposure average; max |identity gap| per draw.');
  console.log('world                          |  cost  | E(T−μ̄)² | E(r̄−μ̄)² | E(ū̂−μ̄)² | max gap');
  for (const r of rows) {
    const p = r.p, x = (v) => (100 * v).toFixed(1).padStart(7);
    console.log(`${`${p.regime} ρ=${p.rho} σⱼ×${p.noiseSpread} T=${p.T}`.padEnd(30)} | ${x(r.cost)} | ${x(r.eT)}  | ${x(r.eR)}  | ${x(r.eX)}  | ${r.gap.toExponential(1)}`);
  }
  const ratio = (k) => rows.map((r) => r[k] / r.eR);
  for (const sp of [0, 1, 2]) {
    const rs = rows.filter((r) => r.p.noiseSpread === sp), q = (k) => rs.map((r) => r[k] / r.eR);
    console.log(`σⱼ×${sp}: E(T−μ̄)²/E(r̄−μ̄)² ${Math.min(...q('eT')).toFixed(2)}–${Math.max(...q('eT')).toFixed(2)}, exposure average ${Math.min(...q('eX')).toFixed(2)}–${Math.max(...q('eX')).toFixed(2)}`);
  }
  console.log(`all: cross-fitted ${Math.min(...ratio('eT')).toFixed(2)}–${Math.max(...ratio('eT')).toFixed(2)}, max identity gap ${Math.max(...rows.map((r) => r.gap)).toExponential(1)}`);
});
