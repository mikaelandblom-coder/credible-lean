// Distance taper ρ̂^|i−j| against damping θ for the thesis fit with every pair estimated
// (studies/PLAN.md "Taper switch", OffDiagonal.lean). Run: node studies/runs/taper.js [draws]
// Entries: exposure-weighted MSE of the rates relative to the floor (100 = best blend with
// known K, τ²), the same draws for every column. Columns:
//   damp grid: the old rule (θ = the largest of 0.95, 0.9, … with K̂ ≻ 0; thetaRule 'grid');
//   damp S3:   θ̂ by the plug-in rule S3, the app's corr fit since 2026-11-22;
//   taper:     the app's corr taper fit (ρ̂ by the same criterion, per distance);
//   corrBS, BS for reference.
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 1000);

function dampS3(data) {
  const { Sig } = E.sigmaHat(data), th = E.taperRho(Sig, data.X[0].length, () => 1).rho;
  for (let x = th; ; x = Math.max(0, Math.round((x - 0.05) * 1000) / 1000)) {
    try { return { f: E.fitCorr(data, { theta: x }), th: x }; } catch (e) { if (x === 0) throw e; }
  }
}

const worlds = [];
for (const [J, T] of [[8, 10], [8, 5], [20, 10]]) {
  for (const rho of [0.3, 0.6, 0.9]) worlds.push({ J, T, rho, ordered: true });
  for (const rho of [0, 0.6]) worlds.push({ J, T, rho });
}
worlds.push({ J: 8, T: 10, rho: 0.6, ordered: true, noiseSpread: 1 });

const ids = ['grid', 's3', 'taper', 'vc', 'bs'];
console.log(`draws per world: ${N}; MSE relative to the floor (100 = floor), mean θ / ρ̂ in brackets`);
console.log('world                           | damp grid  | damp S3     | taper ρ̂     | corrBS | BS');
for (const p of worlds) {
  const world = E.makeWorld(p), fl = E.floorBlend(world), r = E.rng(2026);
  const acc = Object.fromEntries(ids.concat(['floor']).map((k) => [k, 0])), par = { grid: 0, s3: 0, taper: 0 };
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (rates) => E.weightedSE(data, rates, levels);
    acc.floor += se(fl.apply(data).rates);
    const g = E.fitCorr(data, { thetaRule: 'grid' }); acc.grid += se(g.rates); par.grid += g.theta;
    const s = dampS3(data); acc.s3 += se(s.f.rates); par.s3 += s.th;
    const t = E.fitCorr(data, { taper: 'distance' }); acc.taper += se(t.rates); par.taper += t.rhoTaper;
    acc.vc += se(E.fitVC(data).rates); acc.bs += se(E.fitBS(data).rates);
  }
  const rel = (id) => (acc[id] / acc.floor * 100).toFixed(0).padStart(4);
  const pm = (id) => `(${(par[id] / N).toFixed(2)})`;
  const name = `J=${p.J} T=${p.T} ρ=${p.rho}${p.ordered ? ' ordered' : ' common'}${p.noiseSpread ? ' σⱼ spread' : ''}`;
  console.log(`${name.padEnd(31)} | ${rel('grid')} ${pm('grid')} | ${rel('s3')} ${pm('s3')}  | ${rel('taper')} ${pm('taper')}  | ${rel('vc')}   | ${rel('bs')}`);
}
