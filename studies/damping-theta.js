// Numerical study for gap G2 (studies/PLAN.md): how does the damping factor θ
// affect the fitted model's error? Run: node studies/damping-theta.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1];

// Fit with target θ; if K̂ is not PD there, step down through the grid.
function fitAt(data, theta, common) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return { f: E.fitCorr(data, { theta: th, common }), fell: th < theta }; } catch (e) { /* not PD */ }
  }
  throw new Error('no θ works');
}

// Average estimated correlation ρ̄ over the pairs, from Σ̂ (eq. (39)).
function rhoBar(data) {
  const { Sig } = E.sigmaHat(data), J = Sig.length;
  let s = 0, n = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
  return s / n;
}
// Shrinkage rule: θ̂ = ρ̄² / (ρ̄² + Var ρ̂), Var ρ̂ ≈ (1 − ρ̄²)² / (T − 1).
function thetaHat(data) {
  const rb = Math.max(-1, Math.min(1, rhoBar(data))), T = data.X[0].length;
  return rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1));
}
// Common correlation: Σ̂ᵢⱼ = ρ̄ √(Σ̂ᵢᵢ Σ̂ⱼⱼ), then the full GLS route (no closed form).
function fitCommonRho(data, theta) {
  const rb = Math.max(0, rhoBar(data));
  const est = E.sigmaHat(data), Sig = est.Sig.map((row, i) => row.map((x, j) => (i === j ? x : rb * Math.sqrt(est.Sig[i][i] * est.Sig[j][j]))));
  const t2 = Math.max(E.thesisTau(est.m, est.wt, Sig).tau2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : theta * x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return E.blend(est.m, t2 > 0 ? z : z.map(() => 0), b);
}

const worlds = [];
for (const [J, T] of [[4, 10], [8, 10], [8, 5], [20, 10], [20, 20]])
  for (const rho of [0, 0.3, 0.6, 0.9]) worlds.push({ J, T, rho });
if (process.argv[3] === 'tau') for (const tau of [0.03, 0.2]) for (const rho of [0, 0.6]) worlds.push({ J: 8, T: 10, rho, tau });

const pct = (x) => (100 * x).toFixed(1);
console.log(`draws per world: ${N}; entries: error relative to the floor (100 = floor)`);
console.log('J  T   ρ   τ    | BS    | full θ=' + GRID.join('  ') + ' | best θ | fallback% at 0.95/1 | common cov θ=0.95 | θ̂ (mean) | common ρ θ̂');
for (const p of worlds) {
  const world = E.makeWorld(p), fl = E.floorBlend(world), r = E.rng(2026);
  const acc = { bs: 0, floor: 0, full: GRID.map(() => 0), fell: GRID.map(() => 0), common: 0, adapt: 0, th: 0, crho: 0 };
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r);
    acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
    acc.bs += E.weightedSE(data, E.fitBS(data).rates, levels);
    GRID.forEach((th, i) => {
      const { f, fell } = fitAt(data, th, false);
      acc.full[i] += E.weightedSE(data, f.rates, levels); if (fell) acc.fell[i]++;
    });
    acc.common += E.weightedSE(data, fitAt(data, 0.95, true).f.rates, levels);
    const th = thetaHat(data); acc.th += th;
    acc.adapt += E.weightedSE(data, fitAt(data, th, false).f.rates, levels);
    acc.crho += E.weightedSE(data, fitCommonRho(data, th).rates, levels);
  }
  const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
  const best = GRID[acc.full.indexOf(Math.min(...acc.full))];
  console.log(`${String(p.J).padEnd(2)} ${String(p.T).padEnd(3)} ${p.rho.toFixed(1)} ${(p.tau || 0.1).toFixed(2)} | ${rel(acc.bs)}  | ${acc.full.map(rel).join(' ')} | ${String(best).padEnd(5)} | ${pct(acc.fell[5] / N)} / ${pct(acc.fell[7] / N)} | ${rel(acc.common)} | ${rel(acc.adapt)} (${(acc.th / N).toFixed(2)}) | ${rel(acc.crho)}`);
}
