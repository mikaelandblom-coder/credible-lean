// A data-side signal for the BLUP taper (studies/PLAN.md, taper bullet; damping-theta.md S36–S37):
// a practitioner cannot see whether the noise correlation falls with distance, so the fit must tell.
// Engine.taperSignal compares S3's plug-in loss of the tapered correlation table (ρ̂^d) with that of
// one common r̄ (corrBS); Engine.fitBLUPAuto takes the BLUP on the preferred table.
// Full factorial over structure × ρ × J × T × regime, common random numbers, paired SEs.
// Entries: exposure-weighted MSE of the rates in % of the blend floor (true K, τ²).
// Run: node studies/taper-signal.js [draws]
'use strict';
const E = require('../app/engine.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 600);

const worlds = L.grid({ ordered: [true, false], rho: [0.3, 0.6, 0.9], J: [8, 20], T: [5, 10], regime: ['app', 'thesis'] });
console.log(`draws per world: ${N}; MSE in % of the blend floor; "auto − best" = auto against the better of the two in that world (± 2 SE, paired)`);
console.log('world                         | z range   | BLUP corrBS | BLUP taper | auto | picks taper | auto − best');
const rows = [];
for (const p of worlds) {
  const par = Object.assign({ J: p.J, T: p.T, rho: p.rho, ordered: p.ordered }, L.regimes[p.regime]);
  const world = E.makeWorld(par), fl = E.floorBlend(world), r = E.rng(2026);
  const F = [], A = [], B = [], C = [];
  let picks = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    const a = se(E.fitBLUP(data).rates), b = se(E.fitBLUPTaper(data).rates);
    const t = E.taperSignal(data).preferTaper;
    A.push(a); B.push(b); C.push(t ? b : a);
    if (t) picks++;
  }
  const f = L.meanSE(F).m, rel = (x) => (100 * L.meanSE(x).m / f).toFixed(0).padStart(4);
  const best = L.meanSE(A).m <= L.meanSE(B).m ? A : B, d = L.paired(C, best);
  const name = `${p.ordered ? 'ordered' : 'common '} ρ=${p.rho} J=${String(p.J).padEnd(2)} T=${String(p.T).padEnd(2)} ${p.regime}`;
  const z = `${Math.min(...fl.z).toFixed(2)}–${Math.max(...fl.z).toFixed(2)}`;
  console.log(`${name.padEnd(29)} | ${z} |   ${rel(A)}      |   ${rel(B)}     | ${rel(C)} |    ${(100 * picks / N).toFixed(0).padStart(3)}%     | ${L.pm(d, 100 / f)}`);
  rows.push({ p, gapTaper: 100 * (L.meanSE(B).m - L.meanSE(A).m) / f, regret: 100 * d.m / f, regretSE: 200 * d.se / f, picks: picks / N });
}
// Summary: the selector's regret (auto − best) and how often its sign is within noise.
const within = rows.filter((x) => Math.abs(x.regret) <= x.regretSE).length;
console.log(`\nregret (auto − best), % of floor: mean ${L.meanSE(rows.map((x) => x.regret)).m.toFixed(1)}, max ${Math.max(...rows.map((x) => x.regret)).toFixed(1)}; within 2 SE of 0 in ${within} of ${rows.length} worlds`);
for (const reg of ['app', 'thesis']) {
  const g = rows.filter((x) => x.p.regime === reg).map((x) => Math.abs(x.gapTaper));
  console.log(`|BLUP taper − BLUP corrBS| in the ${reg} regime: mean ${L.meanSE(g).m.toFixed(1)}, max ${Math.max(...g).toFixed(1)} points`);
}
