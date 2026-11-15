// The two extra error terms, measured directly (truth known in simulation):
//   fit error = e* + d,  e* = floor rate − μⱼ (true parameters),  d = fitted rate − floor rate
//   MSE(fit) = MSE(floor) + 2E[e*d] (cross term C) + E[d²] (estimation term g₃)
// and the jackknife's g₃ estimate against the true E[d²]. Run: node studies/msep-terms.js [draws]
'use strict';
const E = require('../app/engine.js');
const { msep } = require('./msep.js');
const N = +(process.argv[2] || 2000);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const LAWS = {
  'two-point (sym)': (r) => (r() < 0.5 ? -1 : 1),
  'normal (sym)': (r) => r.normal(),
  'gamma2 (skew 1.4)': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'gamma¼ (skew 4)': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
  'mirror gamma¼ (skew −4)': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return -(g - 0.25) / 0.5; },
};
function run(label, J, T, sigF, rho, law, symLevels) {
  const world = E.makeWorld({ J, T }), { w } = world, tau2 = world.truth.tau2, s = Math.sqrt(world.truth.sigma2);
  const wt = w.map(sum), sig = sigF.map((f) => s * f), K = [];
  for (let i = 0; i < J; i++) { K.push([]); for (let j = 0; j < J; j++) {
    let S = 0; for (let t = 0; t < T; t++) S += Math.sqrt(w[i][t] * w[j][t]);
    K[i].push(sig[i] * sig[j] * (i === j ? 1 : rho) * S / (wt[i] * wt[j]) + (i === j ? tau2 : 0));
  } }
  const fl = E.bestBlendWeights(K, tau2), r = E.rng(13), L = LAWS[law];
  const a = { floor: 0, cross: 0, g3: 0, g3jack: 0, fit: 0 };
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * (symLevels ? r.normal() : (r.gamma(4) - 4) / 2));
    const eta = Array.from({ length: T }, () => L(r));
    const X = levels.map((lv, j) => Array.from({ length: T }, (_, t) => lv + sig[j] / Math.sqrt(w[j][t]) * (Math.sqrt(rho) * eta[t] + Math.sqrt(1 - rho) * L(r))));
    const data = { w, X }, m = E.cohortMeans(data).m, star = E.blend(m, fl.z, fl.b).rates, o = msep(data);
    for (let j = 0; j < J; j++) {
      const e = star[j] - levels[j], d = o.rates[j] - star[j], W = wt[j];
      a.floor += W * e * e; a.cross += W * 2 * e * d; a.g3 += W * d * d; a.g3jack += W * o.g3[j]; a.fit += W * (e + d) ** 2;
    }
  }
  const p = (x) => (100 * x / a.floor).toFixed(1).padStart(6);
  console.log(`${label.padEnd(26)} ${law.padEnd(24)} | ${p(a.cross)} ${p(a.g3)} | ${p(a.g3jack)}  (${(a.g3jack / a.g3).toFixed(2)})`);
}
console.log(`draws ${N}; terms in % of the floor MSE (exposure-weighted over regions)`);
console.log('world                      noise law                |  cross  E[d²] | jackknife g₃ (÷ E[d²])');
for (const [J, T] of [[8, 10], [8, 5]]) {
  const one = Array(J).fill(1), spread = Array.from({ length: J }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5));
  for (const law of Object.keys(LAWS)) run(`J=${J} T=${T} equal σ, ρ=0.6`, J, T, one, 0.6, law, true);
  for (const law of ['normal (sym)', 'gamma¼ (skew 4)']) run(`J=${J} T=${T} σⱼ spread, ρ=0.6`, J, T, spread, 0.6, law, true);
  run(`J=${J} T=${T} equal σ, ρ=0`, J, T, one, 0, 'normal (sym)', true);
}
