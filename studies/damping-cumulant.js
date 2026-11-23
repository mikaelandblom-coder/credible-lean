// The damping θ in covariance form with the exact variance of Σ̂ᵢⱼ (PLAN G2,
// Cumulants.variance_crossResid / variance_sum_mul_lin, engine covTheta), against the S3 rule.
// θ̂ = Σ sᵢⱼ² / Σ (sᵢⱼ² + Vᵢⱼ), common-correlation plug-ins; κ = 0 (normal theory) or the world's
// true shock kurtosis (testing only: the fit never sees it). Oracle: θ* from the true table.
// Gamma (shape 2, κ = 3) and Lomax-claims (α = 3, the year shock still gamma) worlds.
// Entries: exposure-weighted MSE of the rates in % of the floor; (mean θ̂) after each rule.
// Run: node studies/damping-cumulant.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99];

function fitAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }); } catch (e) { /* not PD */ }
  }
  return E.fitCorr(data, { theta: 0 });
}

const worlds = [];
for (const [lab, p] of [['gamma', {}], ['Lomax α=3', { lomax: 3 }]])
  for (const [J, T, sp] of [[8, 5, 0], [8, 10, 0], [8, 10, 1], [20, 10, 0]])
    for (const rho of [0, 0.3, 0.6, 0.9]) worlds.push([lab, Object.assign({ J, T, rho, noiseSpread: sp }, p)]);

console.log(`draws ${N}; MSE in % of the floor (mean θ̂)`);
console.log('world          J  T  σsp ρ   | best fixed θ | S3          | cov κ=0     | cov κ true  | oracle θ*');
for (const [lab, p] of worlds) {
  const world = E.makeWorld(p), fl = E.floorBlend(world), r = E.rng(2026);
  const kappa = 6 / world.params.noiseShape;   // excess kurtosis of the gamma year shock
  const sd = world.truth.sigmaj2.map(Math.sqrt);
  const tcov = sd.map((a, i) => sd.map((b, j) => (i === j ? a * a : world.truth.rho[i][j] * a * b)));
  const oracle = E.covTheta(E.draw(world, E.rng(1)).data, kappa, { cov: tcov }).theta;   // data-free given cov
  const acc = { floor: 0, grid: GRID.map(() => 0), rules: [0, 0, 0, 0], th: [0, 0, 0, 0] };
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r);
    acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
    GRID.forEach((th, i) => { acc.grid[i] += E.weightedSE(data, fitAt(data, th).rates, levels); });
    const fits = [E.fitCorr(data), E.fitCorr(data, { thetaRule: 'cov', kappa: 0 }), E.fitCorr(data, { thetaRule: 'cov', kappa }), fitAt(data, oracle)];
    fits.forEach((f, i) => { acc.rules[i] += E.weightedSE(data, f.rates, levels); acc.th[i] += f.theta; });
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
  const bi = acc.grid.indexOf(Math.min(...acc.grid));
  const cells = acc.rules.map((x, i) => `${rel(x)} (${(acc.th[i] / N).toFixed(2)})`.padEnd(12));
  console.log(`${lab.padEnd(14)} ${String(p.J).padEnd(2)} ${String(p.T).padEnd(2)} ${String(p.noiseSpread).padEnd(3)} ${p.rho.toFixed(1)} | ${rel(acc.grid[bi])} (${GRID[bi].toFixed(2)})  | ${cells.join('| ')}`);
}
