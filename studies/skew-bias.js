// Predicting the plug-in bias of Finding 35 from one data set (engine skewBias): first order,
// through the fit's variance statistics (σ̂ₖ², ρ̂, τ̂²), the covariances from third moments
// (Cumulants.covariance_quad_lin_of_cumulants; κ̂ from the data).
// Against the simulated bias of the unbalanced fit (exposure-weighted mean error of the rates),
// measured against BS on the same draws (BS is balanced, so its portfolio bias is 0 exactly,
// Core.Estimates.integral_portfolio_sub_of_balanced; the difference has a far smaller SE).
// Entries in % of the tariff (μ = 1): simulated ± 2 SE, mean predicted (median over draws).
// Run: node studies/skew-bias.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const ids = ['vc', 'blup', 'blupPool'];
const worlds = [['default', {}], ['T = 4, shape 1', { T: 4, noiseShape: 1 }], ['σⱼ spread', { noiseSpread: 1 }],
  ['J = 20', { J: 20 }], ['Lomax α = 4', { lomax: 4 }], ['normal', { normal: true }], ['ρ = 0.3', { rho: 0.3 }], ['ρ = 0.6', { rho: 0.6 }], ['ρ = 0.6, T = 5', { rho: 0.6, T: 5 }], ['ρ = 0.6, J = 20', { rho: 0.6, J: 20 }]];
const f2 = (x) => (100 * x).toFixed(2).padStart(6);
console.log(`draws ${N}; portfolio bias in % (unbalanced fits)`);
console.log('world            fit       | simulated ± 2SE | predicted mean (median) | own σ̂ₖ², ρ̂, τ̂² parts   | mean γ̂');
for (const [lab, p] of worlds) {
  const world = E.makeWorld(p), wt = world.w.map(sum), wall = sum(wt);
  for (const id of ids) {
    const r = E.rng(77), sim = [], pred = [], po = [], pc = [], pt = [], gm = [];
    for (let n = 0; n < N; n++) {
      const { data } = E.draw(world, r), f = E.MODELS[id].fit(data), g = E.fitBS(data);
      sim.push(sum(f.rates.map((x, j) => wt[j] * (x - g.rates[j]))) / wall);
      const P = E.skewBias(id, data); pred.push(P.portfolio); po.push(P.own); pc.push(P.cross); pt.push(P.tau || 0); gm.push(P.gamma);
    }
    const m = (v) => sum(v) / v.length, se = (v) => Math.sqrt((sum(v.map((x) => x * x)) / v.length - m(v) ** 2) / v.length);
    const med = (v) => v.slice().sort((x, y) => x - y)[v.length >> 1];
    console.log(`${lab.padEnd(16)} ${id.padEnd(9)} | ${f2(m(sim))} ± ${(200 * se(sim)).toFixed(2).padEnd(5)}  | ${f2(m(pred))} (${f2(med(pred))})       | ${f2(m(po))} ${f2(m(pc))} ${f2(m(pt))} | ${m(gm).toFixed(2)}`);
  }
}
