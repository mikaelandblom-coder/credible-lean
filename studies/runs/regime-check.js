// The app's headline recommendations rechecked across credibility regimes (studies/PLAN.md §1,
// "Study conventions"; studies/LOG.md S3, S5, S6, S16, S17): BS, corrBS (recommended), the thesis
// model with full K̂ damped by S3's θ̂, the BLUP on corrBS's K̂, and own means, all on the same draws.
// Entries: exposure-weighted MSE of the rates in % of the blend floor; last columns are paired
// differences against corrBS (± 2 SE; negative = better than corrBS).
// Run: node studies/runs/regime-check.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 600);
const FITS = { bs: E.fitBS, vc: (d) => E.fitVC(d), corr: (d) => E.fitCorr(d), blup: (d) => E.fitBLUP(d), own: E.fitOwn };
const worlds = L.grid({ regime: ['app', 'thesis', 'thesisShape'], rho: [0, 0.3, 0.6, 0.9], noiseSpread: [0, 1], T: [5, 10] })
  .filter((p) => !(p.regime === 'thesisShape' && p.noiseSpread === 0)).map((p) => (p.regime === 'thesisShape' ? Object.assign(p, { noiseSpread: 2 }) : p));
console.log(`J = 8; draws per world: ${N}; MSE in % of the blend floor; Δ = fit − corrBS (± 2 SE, paired)`);
console.log('world                          | z range   |  BS | corrBS | corr | BLUP | own | Δ BS          | Δ corr        | Δ BLUP');
const tally = {};
for (const p of worlds) {
  const par = Object.assign({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread }, L.regimes[p.regime]);
  if (p.regime === 'thesisShape') par.noiseSpread = 2;
  const world = E.makeWorld(par), fl = E.floorBlend(world), r = E.rng(2026);
  const F = [], S = Object.fromEntries(Object.keys(FITS).map((k) => [k, []]));
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    for (const [k2, fn] of Object.entries(FITS)) S[k2].push(se(fn(data).rates));
  }
  const f = L.meanSE(F).m, rel = (x) => (100 * L.meanSE(x).m / f).toFixed(0).padStart(4), dd = (k2) => L.paired(S[k2], S.vc);
  const name = `${p.regime} ρ=${p.rho} σⱼ×${p.regime === 'thesisShape' ? 2 : p.noiseSpread} T=${p.T}`;
  console.log(`${name.padEnd(30)} | ${Math.min(...fl.z).toFixed(2)}–${Math.max(...fl.z).toFixed(2)} | ${rel(S.bs)} |  ${rel(S.vc)}  | ${rel(S.corr)} | ${rel(S.blup)} | ${rel(S.own)} | ${L.pm(dd('bs'), 100 / f).padEnd(13)} | ${L.pm(dd('corr'), 100 / f).padEnd(13)} | ${L.pm(dd('blup'), 100 / f)}`);
  for (const k2 of ['bs', 'corr', 'blup']) {
    const d = dd(k2), t = (tally[`${p.regime}/${k2}`] = tally[`${p.regime}/${k2}`] || { better: 0, worse: 0, tie: 0 });
    if (d.m + 2 * d.se < 0) t.better++; else if (d.m - 2 * d.se > 0) t.worse++; else t.tie++;
  }
}
console.log('\nAgainst corrBS, per regime: worlds where the fit is better / worse / within 2 SE');
for (const [k, t] of Object.entries(tally)) console.log(`${k.padEnd(18)} ${t.better} / ${t.worse} / ${t.tie}`);
