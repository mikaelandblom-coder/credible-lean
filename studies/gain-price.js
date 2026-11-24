// Purpose: decide. Does Engine.gainPrice's verdict (region variances against one pooled variance: exact
// plug-in oracle gain against the first-order price z(1 − z)·2/(T − 1), S56) pick the better corrBS?
// "auto" = corrBS with pooled variances when the verdict is 'pooled', else corrBS. Same draws for all
// (paired), factorial over σⱼ spread × ρ × T × regime, gamma noise (the app's default). MSE in % of the floor.
// Run: node studies/gain-price.js [draws]
'use strict';
const E = require('../app/engine.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 600);
console.log(`J = 8, gamma noise, ${N} draws; MSE in % of the blend floor; regret = auto − better of corrBS / corrBS pooled (± 2 SE)`);
console.log('world                         | z range   | corrBS | pooled | auto | picks region | regret');
const rows = [];
for (const p of L.grid({ regime: ['app', 'thesis'], noiseSpread: [0, 1, 2], rho: [0, 0.6], T: [5, 10] })) {
  const world = E.makeWorld(Object.assign({ noiseSpread: p.noiseSpread, rho: p.rho, T: p.T }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], A = [], B = [], C = [];
  let region = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    const a = se(E.fitVC(data).rates), b = se(E.fitVC(data, { pooled: true }).rates), g = E.gainPrice(data);
    const reg = g ? g.verdict === 'region' : false;
    A.push(a); B.push(b); C.push(reg ? a : b);
    if (reg) region++;
  }
  const f = L.meanSE(F).m, rel = (x) => (100 * L.meanSE(x).m / f).toFixed(0).padStart(4);
  const best = L.meanSE(A).m <= L.meanSE(B).m ? A : B, d = L.paired(C, best);
  const name = `${p.regime} σⱼ×${p.noiseSpread} ρ=${p.rho} T=${p.T}`;
  console.log(`${name.padEnd(29)} | ${Math.min(...fl.z).toFixed(2)}–${Math.max(...fl.z).toFixed(2)} |  ${rel(A)}  |  ${rel(B)}  | ${rel(C)} |     ${(100 * region / N).toFixed(0).padStart(3)}%     | ${L.pm(d, 100 / f)}`);
  rows.push({ regret: 100 * d.m / f, se2: 200 * d.se / f, worseA: 100 * (L.meanSE(C).m - L.meanSE(A).m) / f });
}
console.log(`\nregret: mean ${L.meanSE(rows.map((x) => x.regret)).m.toFixed(1)}, max ${Math.max(...rows.map((x) => x.regret)).toFixed(1)}; within 2 SE of 0 in ${rows.filter((x) => Math.abs(x.regret) <= x.se2).length} of ${rows.length}`);
console.log(`auto − corrBS (today's default): mean ${L.meanSE(rows.map((x) => x.worseA)).m.toFixed(1)}, min ${Math.min(...rows.map((x) => x.worseA)).toFixed(1)}, max ${Math.max(...rows.map((x) => x.worseA)).toFixed(1)}`);
