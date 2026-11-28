// S82. Purpose: decide (and check BalanceCost.balance_cost_cellLin). With volumes that vary by year (S79), the
// cross-fitted level now exists for any volumes (common year shares πₛ; Core.Estimates.integral_crossFit_sub) and
// balanceAuto prices it on the yearly cells. Does it remove the skew under-pricing (Finding 35), and what does that
// cost? corrBS, 1500 draws per world, gamma noise, J = 8, volNoise 0.2, volTrend 0.05. Columns: portfolio bias in
// basis points of the tariff (± 2 SE) and exposure-weighted MSE (×10⁴): unbalanced | auto | always cross-fitted |
// always exposures. Run: node studies/runs/balance-volumes.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N } = L.args({ N: 1500 });
console.log(`corrBS, volumes vary by year, ${N} draws: bias bp (± 2 SE), MSE ×1e4 — raw | auto | crossFit | exposure`);
for (const p of L.grid({ noiseSpread: [0, 2], rho: [0, 0.6], T: [5, 10] })) {
  const w = E.makeWorld({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread, volNoise: 0.2, volTrend: 0.05 }), out = [];
  for (const o of [{}, { balance: 'auto' }, { balance: 'crossFit' }, { balance: true }]) {
    const r = E.simulate(w, ['vc'], N, 5, 1, o).vc;
    out.push(`${(1e4 * r.bias.mean).toFixed(0).padStart(4)} ± ${(2e4 * r.bias.se).toFixed(0).padStart(2)}  ${(1e4 * r.mse).toFixed(1).padStart(5)}`);
  }
  console.log(`σⱼ×${p.noiseSpread} ρ=${p.rho} T=${String(p.T).padEnd(2)} | ${out.join(' | ')}`);
}
