// The distance taper on the BLUP (studies/LOG.md S34's hypothesis): the plug-in BLUP
// on the thesis's full K̂ (every pair), damped by S3's θ̂ or tapered by ρ̂^|i−j|, against the
// BLUP on corrBS's one-ρ̂ K̂ (app fit "BLUP"). Run: node studies/runs/taper-blup.js [draws]
// Entries: exposure-weighted MSE of the rates in % of the blend floor (true K, τ²); "oracle" is the
// BLUP with the true K. "best ρ" sweeps a fixed taper (an oracle choice, to see what the shape can do).
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 1000);
const SWEEP = [0, 0.3, 0.5, 0.7, 0.8, 0.9, 0.95];
const sum = (a) => a.reduce((s, x) => s + x, 0);
const blupRates = (K, tau2, m) => m.map((_, j) => sum(E.blupWeight(K, tau2, j).map((x, i) => x * m[i])));

const worlds = [];
for (const [J, T] of [[8, 10], [8, 5], [20, 10]]) {
  for (const rho of [0.6, 0.9]) worlds.push({ J, T, rho, ordered: true });
  worlds.push({ J, T, rho: 0.6 });
}
worlds.push({ J: 8, T: 10, rho: 0.6, ordered: true, noiseSpread: 1 });
worlds.push({ J: 20, T: 20, rho: 0.9, ordered: true });

console.log(`draws per world: ${N}; MSE in % of the blend floor`);
console.log('world                            | oracle | BLUP corrBS | BLUP damp θ̂ | BLUP taper ρ̂ | best fixed ρ | blend taper | corrBS');
for (const p of worlds) {
  const world = E.makeWorld(p), fl = E.floorBlend(world), r = E.rng(2026), t2 = world.truth.tau2;
  const acc = { floor: 0, oracle: 0, bc: 0, bd: 0, bt: 0, ct: 0, vc: 0, sw: SWEEP.map(() => 0) };
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels), { m } = E.cohortMeans(data);
    acc.floor += se(fl.apply(data).rates);
    acc.oracle += se(blupRates(fl.K, t2, m));
    acc.bc += se(E.fitBLUP(data).rates);
    const d = E.fitCorr(data); acc.bd += se(blupRates(d.K, d.tau2, m));
    const t = E.fitCorr(data, { taper: 'distance' }); acc.bt += se(blupRates(t.K, t.tau2, m)); acc.ct += se(t.rates);
    acc.vc += se(E.fitVC(data).rates);
    SWEEP.forEach((x, i) => { const f = E.fitCorr(data, { taper: 'distance', rho: x }); acc.sw[i] += se(blupRates(f.K, f.tau2, m)); });
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
  const bi = acc.sw.indexOf(Math.min(...acc.sw));
  const name = `J=${p.J} T=${p.T} ρ=${p.rho}${p.ordered ? ' ordered' : ' common'}${p.noiseSpread ? ' σⱼ spread' : ''}`;
  console.log(`${name.padEnd(32)} | ${rel(acc.oracle)}   | ${rel(acc.bc)}        | ${rel(acc.bd)}         | ${rel(acc.bt)}          | ${rel(acc.sw[bi])} (${SWEEP[bi]})   | ${rel(acc.ct)}        | ${rel(acc.vc)}`);
}
