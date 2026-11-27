// S73. Purpose: size the price of the BLUP over the blend on the same K̂ (Credibility/BlupPrice.lean),
// which Engine.gainPrice treats as "none extra". Part 1: Monte Carlo of the squared weight errors
// (d̂ − d)ᵀK(d̂ − d) of each family on corrBS's K̂ against its own true-K weights — by
// Core.linMse_eq_blupWeight_add this is each fit's extra MSE over its oracle when the weights are held
// fixed (the E B² of PlugIn.lean, without the cross term). Part 2: does one price dominate? Finite-
// difference directions for random K and ΔK (blupPrice against blendPrice, BlupPrice.tendsto_*).
// Worlds: regime app / thesis, σⱼ spread 0 or 2, ρ ∈ {0, 0.3, 0.6}, T = 5, J = 8 (as S72).
// Run: node studies/runs/blup-price.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N } = L.args({ N: 300 });
const q = (K, d) => { let s = 0; for (let i = 0; i < d.length; i++) for (let k = 0; k < d.length; k++) s += d[i] * K[i][k] * d[k]; return s; };
const blendRow = (K, t, j) => { const { b, z } = E.bestBlendWeights(K, t); return b.map((bi, i) => (i === j ? z[j] : 0) + (1 - z[j]) * bi); };

console.log(`Part 1: ${N} draws, J = 8, T = 5. In % of the blend floor (mean over regions): gain = floor − BLUP (true K);`);
console.log('price = mean squared weight error on corrBS\'s K̂, blend and BLUP; extra = BLUP − blend.');
for (const regime of ['app', 'thesis']) for (const sp of [0, 2]) for (const rho of [0, 0.3, 0.6]) {
  const world = E.makeWorld(Object.assign({ rho, T: 5, noiseSpread: sp }, L.regimes[regime]));
  const K = E.floorBlend(world).K, t2 = world.truth.tau2, J = K.length;
  const Db = K.map((_, j) => blendRow(K, t2, j)), Du = K.map((_, j) => E.blupWeight(K, t2, j));
  const floor = L.sum(Db.map((d, j) => E.linMse(K, t2, j, d))) / J, opt = L.sum(Du.map((d, j) => E.linMse(K, t2, j, d))) / J;
  const r = E.rng(1), pb = [], pu = [];
  for (let k = 0; k < N; k++) {
    const { data } = E.draw(world, r), f = E.fitVC(data);
    if (!(f.tau2 > 0)) continue;
    let sb = 0, su = 0;
    for (let j = 0; j < J; j++) {
      sb += q(K, blendRow(f.K, f.tau2, j).map((x, i) => x - Db[j][i]));
      su += q(K, E.blupWeight(f.K, f.tau2, j).map((x, i) => x - Du[j][i]));
    }
    pb.push(sb / J / floor); pu.push(su / J / floor);
  }
  const d = L.paired(pu, pb), pct = (x) => (100 * x).toFixed(1).padStart(6);
  console.log(`${`${regime} σⱼ×${sp} ρ=${rho}`.padEnd(22)} gain ${pct((floor - opt) / floor)}  price blend ${pct(L.meanSE(pb).m)}  BLUP ${pct(L.meanSE(pu).m)}  extra ${L.pm(d, 100)}`);
}

// Part 2: directional derivatives for random positive definite K = τ²I + AAᵀ + 0.05I, symmetric ΔK, Δτ².
const r = E.rng(5), R = () => 2 * r() - 1, h = 1e-6;
let below = 0;
const M = 20000;
for (let trial = 0; trial < M; trial++) {
  const J = 2 + Math.floor(r() * 4), t2 = 0.2 + r(), j = 0;
  const A = Array.from({ length: J }, () => Array.from({ length: J }, R));
  const K = A.map((row, i) => row.map((_, k) => A[i].reduce((s, x, m) => s + x * A[k][m], 0) + (i === k ? 0.05 + t2 : 0)));
  const D = Array.from({ length: J }, () => Array.from({ length: J }, R));
  for (let i = 0; i < J; i++) for (let k = 0; k < i; k++) D[i][k] = D[k][i];
  const dt = trial % 2 ? R() : 0;
  const Kh = K.map((row, i) => row.map((x, k) => x + h * (D[i][k] + (i === k ? dt : 0))));
  const du = E.blupWeight(Kh, t2 + h * dt, j).map((x, i) => (x - E.blupWeight(K, t2, j)[i]) / h);
  const db = blendRow(Kh, t2 + h * dt, j).map((x, i) => (x - blendRow(K, t2, j)[i]) / h);
  if (q(K, du) < q(K, db) * (1 - 1e-4)) below++;
}
console.log(`\nPart 2: random K, ΔK (J = 2–5, ${M} directions): BLUP's first-order price below the blend's in ${(100 * below / M).toFixed(1)}%.`);
