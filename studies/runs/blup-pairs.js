// Does the plug-in BLUP survive pair-specific correlations? (PLAN 3c, Finding 18.)
// corrBS assumes one common ρ; here the noise has a factor structure, so corrBS's K̂ is misspecified.
//   ε_jt = Σ_f L_jf η_ft + √(1 − Σ_f L_jf²) ξ_jt,   corr(ε_i, ε_j) = Σ_f L_if L_jf   (gamma(2) noise, skewed).
// Fits (data only): BS; corr = thesis full K̂, damped (app default θ rule); corrBS (one ρ̂);
//   BLUP = plug-in BLUP on corrBS's K̂ (app fit 'blup'); BLUPfull = plug-in BLUP on corr's damped full K̂.
// Floors (true K, τ²): blend floor (eq. (26)) and BLUP floor.
// Error: exposure-weighted MSE of the rates, % of the blend floor's (100 = floor). Typical error = √.
// Run: node studies/runs/blup-pairs.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 2000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

function blupRates(K, tau2, m) {
  return m.map((_, j) => { const d = E.blupWeight(K, tau2, j); return sum(d.map((x, i) => x * m[i])); });
}

// L: J × F loadings (rows with Σ L² ≤ 1). params: world size etc. (as the app's makeWorld).
function run(label, params, L) {
  const world = E.makeWorld(params), { J, T, w } = world, F = L[0].length;
  const R = L.map((li, i) => L.map((lj, j) => (i === j ? 1 : sum(li.map((x, f) => x * lj[f])))));
  world.truth.rho = R;                                   // trueK reads the full ρ table
  const K = E.trueK(world), tau2 = world.truth.tau2, sig = world.truth.sigmaj2.map(Math.sqrt);
  const fl = E.bestBlendWeights(K, tau2), price = E.worldPrice(world);
  const idio = L.map((l) => Math.sqrt(1 - sum(l.map((x) => x * x))));
  const r = E.rng(7), a = { fl: 0, flB: 0, bs: 0, corr: 0, vc: 0, blup: 0, blupFull: 0 };
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * r.skewed(world.params.levelShape));
    const eta = Array.from({ length: F }, () => Array.from({ length: T }, () => r.skewed(2)));
    const X = levels.map((mu, j) => Array.from({ length: T }, (_, t) => {
      let e = idio[j] * r.skewed(2);
      for (let f = 0; f < F; f++) e += L[j][f] * eta[f][t];
      return mu + sig[j] / Math.sqrt(w[j][t]) * e;
    }));
    const data = { w, X }, m = E.cohortMeans(data).m, se = (x) => E.weightedSE(data, x, levels);
    a.fl += se(E.blend(m, fl.z, fl.b).rates); a.flB += se(blupRates(K, tau2, m));
    a.bs += se(E.fitBS(data).rates); a.vc += se(E.fitVC(data).rates); a.blup += se(E.fitBLUP(data).rates);
    const c = E.fitCorr(data); a.corr += se(c.rates); a.blupFull += se(blupRates(c.K, c.tau2, m));
  }
  const rel = (x) => (x / a.fl * 100).toFixed(0).padStart(5);
  console.log(`${label.padEnd(46)}|${rel(a.flB)}${rel(a.bs)}${rel(a.corr)}${rel(a.vc)}${rel(a.blup)}${rel(a.blupFull)} | ${(100 * (price.weighted.blend / price.weighted.best - 1)).toFixed(1).padStart(5)}%`);
}

const countries = (J, G, rw, rb) => Array.from({ length: J }, (_, j) => {   // global √rb, country √(rw − rb)
  const row = [Math.sqrt(rb)]; for (let g = 0; g < G; g++) row.push(j % G === g ? Math.sqrt(rw - rb) : 0); return row;
});
const loadings = (J, seed, lo, hi) => { const r = E.rng(seed); return Array.from({ length: J }, () => [lo + (hi - lo) * r()]); };
const twoFactor = (J, seed) => { const r = E.rng(seed); return Array.from({ length: J }, () => {
  const a = 0.9 * r(), b = (2 * r() - 1) * Math.sqrt(0.9 - a * a > 0 ? 0.9 - a * a : 0); return [a, b]; }); };

console.log(`draws ${N}; gamma noise; MSE in % of the blend floor (100 = best blend with true K, τ²)`);
console.log('world                                         | BLUPfl   BS  corr corrBS BLUP BLUPfull | blend over BLUP (exact)');
for (const [J, T] of [[8, 10], [20, 10], [8, 5]]) {
  const p = { J, T };
  run(`J=${J} T=${T} common ρ = 0.6 (corrBS right)`, p, countries(J, 1, 0.6, 0.6));
  run(`J=${J} T=${T} 2 countries 0.8 within / 0.2 between`, p, countries(J, 2, 0.8, 0.2));
  run(`J=${J} T=${T} 4 countries 0.8 within / 0 between`, p, countries(J, 4, 0.8, 0));
  run(`J=${J} T=${T} loadings U(0.2, 0.95): ρᵢⱼ = λᵢλⱼ`, p, loadings(J, 11, 0.2, 0.95));
  run(`J=${J} T=${T} two factors, some ρᵢⱼ < 0`, p, twoFactor(J, 13));
  run(`J=${J} T=${T} 2 countries 0.8/0.2, σⱼ ×0.5–2`, Object.assign({ noiseSpread: 1 }, p), countries(J, 2, 0.8, 0.2));
}
