// G2a (studies/PLAN.md §5, step 1): does building K̂ on the nearest PSD Σ̂⁺ (ConeProjection) move the
// corr fits' error? Σ̂ is PSD by construction when every region's volumes have the same shape over
// the years (wᵢₜ = aᵢgₜ, the app's worlds); here each cell's volume gets an independent log-normal
// jitter (year-to-year changes of ±jit), so Σ̂ can fail to be PSD. Compared: the fit on Σ̂⁺ (app
// default) and the old fit on Σ̂ (θ or ρ lowered until K̂ ≻ 0), error relative to the floor (100).
// Run: node studies/runs/psd-projection.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 400);

console.log(`draws ${N}; error relative to the floor (100 = floor); volumes jittered per cell`);
console.log('J  T  ρ    jit | Σ̂ not PSD | damped: Σ̂⁺  old  (θ lowered) | taper: Σ̂⁺  old | BS');
for (const J of [8, 12]) for (const T of [3, 5]) for (const rho of [0, 0.3, 0.6]) for (const jit of [0.1, 0.3]) {
  const world = E.makeWorld({ J, T, rho, ordered: false }), rw = E.rng(100 + J + T);
  world.w = world.w.map((row) => row.map((x) => x * Math.exp(jit * rw.normal())));
  const fl = E.floorBlend(world), r = E.rng(2026);
  const acc = { floor: 0, np: 0, dP: 0, dO: 0, low: 0, tP: 0, tO: 0, bs: 0 };
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r);
    const se = (f) => E.weightedSE(data, f.rates, levels);
    acc.floor += se(fl.apply(data));
    if (!E.isPSD(E.sigmaHat(data).Sig)) acc.np++;
    acc.dP += se(E.fitCorr(data));
    const old = E.fitCorr(data, { project: false });
    acc.dO += se(old); if (old.flags.thetaLow) acc.low++;
    acc.tP += se(E.fitCorr(data, { taper: 'distance' }));
    acc.tO += se(E.fitCorr(data, { taper: 'distance', project: false }));
    acc.bs += se(E.fitBS(data));
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(1).padStart(6);
  console.log(`${String(J).padEnd(2)} ${T}  ${rho.toFixed(1)}  ${jit.toFixed(1)} | ${(acc.np / N).toFixed(2).padStart(9)} | ${rel(acc.dP)} ${rel(acc.dO)} (${(acc.low / N).toFixed(2)})      | ${rel(acc.tP)} ${rel(acc.tO)} | ${rel(acc.bs)}`);
}
