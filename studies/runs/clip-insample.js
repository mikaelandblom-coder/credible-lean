// S83. Purpose: conjecture (G3b). A held-out ẑ can always be clipped safely when the best z* is in [0, 1]
// (ClipHeldOut.integral_sq_blend_clip_le). Does that survive an in-sample ẑ? corrBS's ẑⱼ (eq. (26) on K̂) vs the
// same fit with each ẑⱼ clipped to [0, 1] (thesis eq. (34)), b and μ̂ unchanged, paired draws. Columns: true z*
// range (floorBlend), share of draws with some ẑⱼ > 1 or < 0, MSE in % of the floor, clipped − raw (± 2 SE).
// A counterexample is a world with every z* in [0, 1] where clipping raises the error beyond 2 SE. The last 16 worlds
// (ρ 0.8–0.95, σⱼ spread 2–3) check whether the app's worlds can put z* well above 1 at all (they cannot: ≤ 1.01).
// Run: node studies/runs/clip-insample.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N } = L.args({ N: 1000 });
const clip = (z) => Math.max(0, Math.min(z, 1));
console.log(`corrBS, gamma noise, J = 8, ${N} draws: z* range | ẑ outside [0, 1] | MSE raw | clipped − raw (± 2 SE)`);
const rows = [];
const grid = L.grid({ regime: ['app', 'thesis'], noiseSpread: [0, 1, 2], rho: [0, 0.3, 0.6], T: [3, 5, 10] })
  .concat(L.grid({ regime: ['app', 'thesis'], noiseSpread: [2, 3], rho: [0.8, 0.95], T: [5, 10] }));   // extreme worlds: can z* leave [0, 1]?
for (const p of grid) {
  const world = E.makeWorld(Object.assign({ noiseSpread: p.noiseSpread, rho: p.rho, T: p.T }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], A = [], B = [];
  let out = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels), f = E.fitVC(data);
    F.push(se(fl.apply(data).rates)); A.push(se(f.rates));
    if (f.z.some((z) => z > 1 || z < 0)) out++;
    B.push(se(f.means.map((m, j) => clip(f.z[j]) * m + (1 - clip(f.z[j])) * f.mu)));
  }
  const fm = L.meanSE(F).m, d = L.paired(B, A), zin = fl.z.every((z) => z >= 0 && z <= 1);
  rows.push({ p, d: 100 * d.m / fm, sig: L.sig(d, 1e-12), zin, zmax: Math.max(...fl.z) });
  console.log(`${p.regime.padEnd(6)} σⱼ×${p.noiseSpread} ρ=${p.rho.toFixed(2)} T=${String(p.T).padEnd(2)} | ${Math.min(...fl.z).toFixed(2)}–${Math.max(...fl.z).toFixed(2)}${zin ? ' ' : '*'} | ${(100 * out / N).toFixed(0).padStart(3)}% | ${(100 * L.meanSE(A).m / fm).toFixed(0).padStart(4)} | ${L.pm(d, 100 / fm)}`);
}
const inr = rows.filter((x) => x.zin);
console.log(`\n* = some z* outside [0, 1]. Worlds with every z* in [0, 1]: ${inr.length}; clipping hurts (beyond 2 SE) in ${inr.filter((x) => x.sig > 0).length}, helps in ${inr.filter((x) => x.sig < 0).length}; mean ${(L.sum(inr.map((x) => x.d)) / inr.length).toFixed(2)}, max ${Math.max(...inr.map((x) => x.d)).toFixed(2)} points`);
const outr = rows.filter((x) => !x.zin);
if (outr.length) console.log(`Worlds with some z* outside: ${outr.length}; hurts in ${outr.filter((x) => x.sig > 0).length}, helps in ${outr.filter((x) => x.sig < 0).length}`);
console.log(`Largest z* in any world: ${Math.max(...rows.map((x) => x.zmax)).toFixed(3)}: these worlds never put z* far outside [0, 1], so they cannot show what clipping costs when it does (Finding 36's two-cohort example: +30%).`);
