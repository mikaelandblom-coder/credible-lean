// Finding 35, the ρ̂ channel (notes/blup-credibility-form.md §3, PLAN "Finding 35: the ρ̂ channel").
// The plug-in BLUP on corrBS's K̂ is biased under skewed noise because its weights covary with the means
// they weight (Core.Estimates.integral_randomLin_sub). The pooled σ̂² removes the σ̂ⱼ² channel; under
// correlation a ρ̂ channel remains (predicted to first order by Engine.skewBias since 2026-11-23).
// Here:
//   attribution  the pooled BLUP with ρ fixed at the truth (σ̂², τ̂² still estimated);
//   P1           equal volumes, no growth, equal σⱼ: by symmetry the pooled BLUP is exposure-balanced
//                in every draw, so its portfolio bias is exactly 0 (a check, not a test);
//   R1           leave-one-year-out cross-fitting: rateⱼ = Σₛ Σᵢ d̂⁽⁻ˢ⁾ⱼᵢ aᵢₛ Xᵢₛ, with d̂⁽⁻ˢ⁾ the BLUP
//                weights for the full design from corrBS's parameters (σ̃², ρ̂, τ̂²) fitted without year s.
//                Years are independent, so d̂⁽⁻ˢ⁾ is independent of year s's noise and only the level
//                channel (τ̂² from the other years' means) is left. Region-specific (cf) and pooled (cfPool).
//   R1b          shiftPool / shiftBlup: the pooled / region-specific BLUP shifted by one constant to cfPool's
//                exposure-weighted level (regional structure of the plug-in, portfolio level of the cross-fit).
// Bias: exposure-weighted mean error in % of the tariff, measured against BS on the same draws (BS is
// exposure-balanced, so its portfolio bias is 0 exactly; the difference has a far smaller SE).
// MSE: exposure-weighted squared error in % of the oracle's (BLUP with the true K).
// Run: node studies/rho-channel.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 2000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

function design(data) {
  const J = data.X.length, T = data.X[0].length, wt = data.w.map(sum), S = [];
  for (let i = 0; i < J; i++) { S.push([]); for (let j = 0; j < J; j++) { let s = 0; for (let t = 0; t < T; t++) s += Math.sqrt(data.w[i][t] * data.w[j][t]); S[i].push(s); } }
  return { J, T, wt, S };
}

// K̂ on the full design from parameters p = { s2, rho, t2 } (as Engine.vcBlend).
function kOn(p, wt, S) {
  const sd = p.s2.map(Math.sqrt);
  return S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / wt[i] + p.t2 : p.rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
}

function blupRates(K, t2, m) {
  return m.map((_, j) => { const d = E.blupWeight(K, t2, j); return sum(d.map((x, i) => x * m[i])); });
}

// Pooled BLUP with ρ fixed at the world's ρ (σ̂², τ̂² estimated as in vcEstimate).
function fitTrueRho(data, rho) {
  const p = E.vcEstimate(data, { pooled: true }), { wt, S } = design(data), sd = p.s2.map(Math.sqrt);
  const Sig = S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / wt[i] : rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
  const t2 = Math.max(E.thesisTau(p.m, wt, Sig).tau2, 0);
  return blupRates(kOn({ s2: p.s2, rho, t2 }, wt, S), t2, p.m);
}

// Leave-one-year-out cross-fitted BLUP.
function fitCross(data, pooled) {
  const { J, T, wt, S } = design(data), rates = new Array(J).fill(0);
  for (let s = 0; s < T; s++) {
    const sub = { w: data.w.map((row) => row.filter((_, t) => t !== s)), X: data.X.map((row) => row.filter((_, t) => t !== s)) };
    const p = E.vcEstimate(sub, { pooled }), K = kOn(p, wt, S);
    const xs = data.X.map((row, i) => data.w[i][s] / wt[i] * row[s]);   // year s's share of each mean
    for (let j = 0; j < J; j++) { const d = E.blupWeight(K, p.t2, j); rates[j] += sum(d.map((x, i) => x * xs[i])); }
  }
  return rates;
}

const fits = {
  blup: (d) => E.fitBLUP(d).rates,
  blupPool: (d) => E.fitBLUP(d, { pooled: true }).rates,
  blupBal: (d) => E.balanceFit(E.fitBLUP(d), d).rates,
  poolTrueRho: (d, w) => fitTrueRho(d, w.params.rho),
  cf: (d) => fitCross(d, false),
  cfPool: (d) => fitCross(d, true),
  shiftPool: (d) => shiftTo(fits.blupPool(d), fitCross(d, true), d),
  shiftBlup: (d) => shiftTo(fits.blup(d), fitCross(d, true), d),
};
// R1b: keep a fit's regional rates, move its exposure-weighted level to the cross-fitted one (a common shift).
function shiftTo(rates, target, data) {
  const wt = data.w.map(sum), wall = sum(wt), lv = (v) => sum(v.map((x, j) => wt[j] * x)) / wall, D = lv(target) - lv(rates);
  return rates.map((x) => x + D);
}
const worlds = [['default', {}], ['normal', { normal: true }], ['T = 4, shape 1', { T: 4, noiseShape: 1 }],
  ['σⱼ spread 1', { noiseSpread: 1 }], ['ρ = 0.3', { rho: 0.3 }], ['ρ = 0.6', { rho: 0.6 }], ['ρ = 0.6, spread 1', { rho: 0.6, noiseSpread: 1 }],
  ['ρ = 0.6, T = 5', { rho: 0.6, T: 5 }], ['ρ = 0.6, J = 20', { rho: 0.6, J: 20 }], ['P1: ρ = 0.6 exch.', { rho: 0.6, spread: 0, growth: 0 }]];

console.log(`draws ${N}; cells: MSE in % of the oracle / portfolio bias in % of the tariff (± 2 SE)`);
console.log('world'.padEnd(20) + Object.keys(fits).map((k) => k.padStart(18)).join(''));
for (const [lab, par] of worlds) {
  const world = E.makeWorld(par), K0 = E.trueK(world), wt = world.w.map(sum), wall = sum(wt), r = E.rng(2026);
  const Dstar = K0.map((_, j) => E.blupWeight(K0, world.truth.tau2, j));
  const acc = {}; for (const k in fits) acc[k] = { e: 0, b: [], };
  let eOr = 0;
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, r), m = E.cohortMeans(data).m, bs = E.fitBS(data).rates;
    eOr += E.weightedSE(data, Dstar.map((d) => sum(d.map((x, i) => x * m[i]))), levels);
    for (const k in fits) {
      const rt = fits[k](data, world);
      acc[k].e += E.weightedSE(data, rt, levels);
      acc[k].b.push(sum(rt.map((x, j) => wt[j] * (x - bs[j]))) / wall);
    }
  }
  const cells = Object.keys(fits).map((k) => {
    const v = acc[k].b, mb = sum(v) / N, se = Math.sqrt(Math.max(sum(v.map((x) => x * x)) / N - mb * mb, 0) / N);
    return `${(100 * acc[k].e / eOr).toFixed(0)} / ${(100 * mb).toFixed(2)}±${(200 * se).toFixed(2)}`.padStart(18);
  });
  console.log(lab.padEnd(20) + cells.join(''));
}
