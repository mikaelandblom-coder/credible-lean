// S3 with the exact variance of the estimated correlation (engine corrTheta): θ̂ = r̄²/(r̄² + V̄),
// V̄ the delta-method Var r̂ᵢⱼ from the exact covariances of Σ̂ᵢⱼ, Σ̂ᵢᵢ, Σ̂ⱼⱼ
// (Cumulants.variance_sum_mul_lin), with the fourth cumulants 0 (normal theory) or the world's
// true ones (shock and region part; testing only, the fit never sees them). Oracle: true r, σⱼ and
// cumulants. Follows studies/runs/damping-cumulant.js (S38–S40). Entries: MSE in % of the floor (mean θ).
// Run: node studies/runs/damping-corr-exact.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 1000);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99];

function fitAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }); } catch (e) { /* not PD */ }
  }
  return E.fitCorr(data, { theta: 0 });
}

const worlds = [];
for (const [lab, p] of [['gamma', {}], ['Lomax α=5', { lomax: 5 }], ['Lomax α=3', { lomax: 3 }]])
  for (const [J, T, sp] of [[8, 5, 0], [8, 10, 0], [8, 10, 1], [20, 10, 0]])
    for (const rho of [0.3, 0.6, 0.9]) worlds.push([lab, Object.assign({ J, T, rho, noiseSpread: sp }, p)]);

console.log(`draws ${N}; MSE in % of the floor (mean θ)`);
console.log('world          J  T  σsp ρ   | best fixed θ | S3          | exact κ=0   | exact κ true | oracle');
for (const [lab, p] of worlds) {
  const world = E.makeWorld(p), fl = E.floorBlend(world), r = E.rng(2026);
  const k = 6 / world.params.noiseShape, L = p.lomax ? E.lomaxMoments(p.lomax) : null;
  const kRegion = L ? (a, s) => L.m4 / (E.claimRate(world, a) * world.w[a][s] * L.m2 ** 2) : () => k;
  const truth = { kShock: k, kRegion };
  const sd = world.truth.sigmaj2.map(Math.sqrt);
  const oracle = E.corrTheta(E.draw(world, E.rng(1)).data, { r: p.rho, sd, kShock: k, kRegion }).V;
  const acc = { floor: 0, grid: GRID.map(() => 0), rules: [0, 0, 0, 0], th: [0, 0, 0, 0] };
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, r);
    acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
    GRID.forEach((th, i) => { acc.grid[i] += E.weightedSE(data, fitAt(data, th).rates, levels); });
    const rb = E.corrTheta(data, { r: 0 }).rbar, thO = isFinite(oracle) ? rb * rb / (rb * rb + oracle) : 0;
    const fits = [E.fitCorr(data), E.fitCorr(data, { thetaRule: 'corr' }), E.fitCorr(data, Object.assign({ thetaRule: 'corr' }, truth)), fitAt(data, thO)];
    fits.forEach((f, i) => { acc.rules[i] += E.weightedSE(data, f.rates, levels); acc.th[i] += f.theta; });
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
  const bi = acc.grid.indexOf(Math.min(...acc.grid));
  const cells = acc.rules.map((x, i) => `${rel(x)} (${(acc.th[i] / N).toFixed(2)})`.padEnd(12));
  console.log(`${lab.padEnd(14)} ${String(p.J).padEnd(2)} ${String(p.T).padEnd(2)} ${String(p.noiseSpread).padEnd(3)} ${p.rho.toFixed(1)} | ${rel(acc.grid[bi])} (${GRID[bi].toFixed(2)})  | ${cells.join('| ')}`);
}
