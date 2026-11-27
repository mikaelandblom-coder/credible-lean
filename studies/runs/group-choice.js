// S77. Purpose: decide. Does the app's "groups or none on held-out years" rule (Engine.fitGroups,
// CrossFit.integral_heldOutScore_sub) pick well, and is a cheaper rule as good?
// Rules: "groups" (always: Engine.fitGroupLevels, one GLS pass on the pair table, S69), "none" (always: the BLUP
// on corrBS's K̂, no groups), "held-out" (groups iff its leave-one-year-out score is lower: the app's rule),
// "θ̂ > 0" (groups iff the raw GLS estimate of φτ² is positive: the plug-in gain on K̂ without a price).
// Worlds: the app's world with group levels (J = 8, regions j mod G), G ∈ {2, 4}, φ ∈ {0, 0.3, 0.7}, T ∈ {5, 10},
// ρ ∈ {0, 0.5}, regimes app / thesis; 48 worlds. Regret against the better of always and never in each world.
// Run: node studies/runs/group-choice.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 300 });
const worlds = L.grid({ regime: ['app', 'thesis'], groups: [2, 4], phi: [0, 0.3, 0.7], T: [5, 10], rho: [0, 0.5] });
const IDS = ['grp', 'none', 'ho', 'pos'];

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ groups: p.groups, phi: p.phi, T: p.T, rho: p.rho }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], S = Object.fromEntries(IDS.map((k) => [k, []]));
  let pickH = 0, pickP = 0;
  const gfit = (d) => E.fitGroupLevels(d) || E.fitBLUP(d);
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    const g = gfit(data), n = E.fitBLUP(data);
    const useH = E.loyoLoss(data, gfit) < E.loyoLoss(data, E.fitBLUP), useP = g.phiTauRaw > 0;
    if (useH) pickH++; if (useP) pickP++;
    const fits = { grp: g, none: n, ho: useH ? g : n, pos: useP ? g : n };
    for (const id of IDS) S[id].push(se(fits[id].rates));
  }
  const f = L.meanSE(F).m, best = L.meanSE(S.grp).m <= L.meanSE(S.none).m ? S.grp : S.none;
  return { p, f, pickH: pickH / N, pickP: pickP / N, rel: Object.fromEntries(IDS.map((id) => [id, L.meanSE(S[id]).m / f])),
    regret: Object.fromEntries(IDS.map((id) => [id, L.paired(S[id], best)])), diff: L.paired(S.grp, S.none) };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  console.log(`${N} draws. MSE in % of the blend floor; picks = share of draws with groups.`);
  console.log('world                           | groups | none | held-out | θ̂>0 | grp − none     | picks ho | picks θ̂>0');
  for (const r of rows) {
    const p = r.p, x = (id) => (100 * r.rel[id]).toFixed(0).padStart(4);
    console.log(`${`${p.regime} G=${p.groups} φ=${p.phi} T=${p.T} ρ=${p.rho}`.padEnd(31)} |  ${x('grp')}  | ${x('none')} |   ${x('ho')}   | ${x('pos')} | ${L.pm(r.diff, 100 / r.f).padStart(13)} |   ${(100 * r.pickH).toFixed(0).padStart(3)}%   |   ${(100 * r.pickP).toFixed(0).padStart(3)}%`);
  }
  console.log('\nRegret against the better of always-groups and never in each world (points of the floor, paired):');
  for (const id of IDS) {
    let w = 0; const pts = rows.map((r) => { const d = r.regret[id]; if (L.sig(d, 1e-9 * r.f) > 0) w++; return 100 * d.m / r.f; });
    console.log(`  ${id.padEnd(5)} mean ${(L.sum(pts) / pts.length).toFixed(1)}, max ${Math.max(...pts).toFixed(1)}, worse in ${w} of ${rows.length}`);
  }
});
