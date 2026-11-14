// Does the best damping θ depend on the noise distribution (beyond two moments)?
// Same worlds, noise drawn from distributions with mean 0, variance 1 and
// different fourth moments. Run: node studies/damping-dist.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1];

// Standardised noise laws (mean 0, variance 1); excess kurtosis in the label.
const LAWS = {
  'two-point (κ=-2)': (r) => (r() < 0.5 ? -1 : 1),
  'normal (κ=0)': (r) => r.normal(),
  'gamma k=2 (κ=3)': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'exponential (κ=6)': (r) => -Math.log(1 - r()) - 1,
  'gamma k=0.25 (κ=24)': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
};

function fitAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }); } catch (e) { /* not PD */ }
  }
}
function rhoBar(data) {
  const { Sig } = E.sigmaHat(data), J = Sig.length;
  let s = 0, n = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
  return Math.max(-1, Math.min(1, s / n));
}
const thetaHat = (data) => { const rb = rhoBar(data), T = data.X[0].length; return rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1)); };

console.log(`draws ${N}; error relative to the floor (100 = floor); J = 8`);
console.log('law                  T  ρ   | full θ=' + GRID.join(' ') + ' | best θ | θ̂ rule (mean θ̂) | BS');
for (const [name, law] of Object.entries(LAWS)) {
  for (const T of [5, 10]) for (const rho of [0, 0.3, 0.6, 0.9]) {
    const world = E.makeWorld({ J: 8, T, rho }), fl = E.floorBlend(world), r = E.rng(2026);
    r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
    const acc = { floor: 0, bs: 0, full: GRID.map(() => 0), ad: 0, th: 0 };
    for (let k = 0; k < N; k++) {
      const { levels, data } = E.draw(world, r);
      acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
      acc.bs += E.weightedSE(data, E.fitBS(data).rates, levels);
      GRID.forEach((th, i) => { acc.full[i] += E.weightedSE(data, fitAt(data, th).rates, levels); });
      const th = thetaHat(data); acc.th += th;
      acc.ad += E.weightedSE(data, fitAt(data, th).rates, levels);
    }
    const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
    const best = GRID[acc.full.indexOf(Math.min(...acc.full))];
    console.log(`${name.padEnd(20)} ${String(T).padEnd(2)} ${rho.toFixed(1)} | ${acc.full.map(rel).join('')} | ${String(best).padEnd(5)}  | ${rel(acc.ad)} (${(acc.th / N).toFixed(2)})      | ${rel(acc.bs)}`);
  }
}
