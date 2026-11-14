// Misspecification: worlds with region-specific σⱼ and/or country-structured ρ, against
// BS, the full thesis fit (app default θ rule) and correlated BS. Run: node studies/common-rho-misspec.js [draws]
'use strict';
const E = require('../app/engine.js');
const { fitCBS } = require('./common-rho-mom.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const skew = (r) => (r.gamma(2) - 2) / Math.SQRT2;
// sigF: σⱼ multipliers; groups: country of each region; rw / rb: correlation within / between.
function run(label, J, T, sigF, groups, rw, rb) {
  const world = E.makeWorld({ J, T }), { w } = world, tau2 = world.truth.tau2, s = Math.sqrt(world.truth.sigma2);
  const wt = w.map(sum), sig = sigF.map((f) => s * f);
  const K = [];
  for (let i = 0; i < J; i++) { K.push([]); for (let j = 0; j < J; j++) {
    let S = 0; for (let t = 0; t < T; t++) S += Math.sqrt(w[i][t] * w[j][t]);
    const rho = i === j ? 1 : groups[i] === groups[j] ? rw : rb;
    K[i].push(sig[i] * sig[j] * rho * S / (wt[i] * wt[j]) + (i === j ? tau2 : 0));
  } }
  const fl = E.bestBlendWeights(K, tau2), r = E.rng(7), G = Math.max(...groups) + 1;
  const a = { fl: 0, bs: 0, full: 0, cbs: 0 };
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * (r.gamma(4) - 4) / 2);
    const X = [];
    const eta = Array.from({ length: T }, () => skew(r)), etaG = Array.from({ length: G }, () => Array.from({ length: T }, () => skew(r)));
    for (let j = 0; j < J; j++) X.push(Array.from({ length: T }, (_, t) => {
      const e = Math.sqrt(rb) * eta[t] + Math.sqrt(rw - rb) * etaG[groups[j]][t] + Math.sqrt(1 - rw) * skew(r);
      return levels[j] + sig[j] / Math.sqrt(w[j][t]) * e;
    }));
    const data = { w, X }, m = E.cohortMeans(data).m, se = (x) => E.weightedSE(data, x, levels);
    a.fl += se(E.blend(m, fl.z, fl.b).rates); a.bs += se(E.fitBS(data).rates);
    a.full += se(E.fitCorr(data).rates); a.cbs += se(fitCBS(data).rates);
  }
  const rel = (x) => (x / a.fl * 100).toFixed(0).padStart(4);
  console.log(`${label.padEnd(44)} | ${rel(a.bs)} ${rel(a.full)} ${rel(a.cbs)}`);
}
console.log(`draws ${N}; gamma(2) noise; error relative to the floor (100 = floor)`);
console.log('world                                        |   BS full corrBS');
for (const [J, T] of [[8, 10], [20, 10]]) {
  const one = Array(J).fill(1), spread = Array.from({ length: J }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5)); // σⱼ ×0.5…2, not tied to size
  const two = Array.from({ length: J }, (_, j) => j % 2), four = Array.from({ length: J }, (_, j) => j % 4);
  run(`J=${J} T=${T} σⱼ ×0.5–2, ρ = 0`, J, T, spread, one.map(() => 0), 0, 0);
  run(`J=${J} T=${T} σⱼ ×0.5–2, ρ = 0.6`, J, T, spread, one.map(() => 0), 0.6, 0.6);
  run(`J=${J} T=${T} 2 countries ρ 0.8 within / 0.2 between`, J, T, one, two, 0.8, 0.2);
  run(`J=${J} T=${T} 4 countries ρ 0.8 within / 0 between`, J, T, one, four, 0.8, 0);
  run(`J=${J} T=${T} both: σⱼ spread, 2 countries 0.8/0.2`, J, T, spread, two, 0.8, 0.2);
}
