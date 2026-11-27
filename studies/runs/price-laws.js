// Purpose: conjecture. Two closed-form price laws (studies/LOG.md S56), checked over a volume sweep
// in balanced normal worlds (equal volumes, ρ = 0, equal σ). Relative price = (MSE of the fitted rates −
// floor) / floor. With z = τ²/(τ² + v), v = σ²/(wT), the balanced BS factor is exactly ẑ = 1 − v̂/S²
// (S² the sample variance of the region means), and to first order:
//   (a) fitting BS (τ̂² and σ̂²):            price ≈ (2/J)·T/(T − 1)·(1 − z)/z;
//   (b) own variances σ̂ⱼ² instead of σ̂²:   extra price ≈ z(1 − z)·2/(T − 1)
// (∂z/∂log v = −z(1 − z), Var log σ̂ⱼ² ≈ 2/(T − 1); one pooled σ̂² has 2/(J(T − 1))).
// Columns: the law, the exact first-order price (price-formula.js machinery), and simulation (± 2 SE).
// Run: node studies/runs/price-laws.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const PF = require('./price-formula.js');
const N = +(process.argv[2] || 4000);
const sum = L.sum;
// BS with each region's own variance σ̂ⱼ²: zⱼ = τ̂²/(τ̂² + σ̂ⱼ²/wⱼ*), τ̂² as BS's (pooled), b ∝ z.
function ownVarRates(data) {
  const J = data.X.length, T = data.X[0].length, { wt, m } = E.cohortMeans(data), f = E.fitBS(data);
  const sj = m.map((mj, j) => sum(data.X[j].map((x, t) => data.w[j][t] * (x - mj) ** 2)) / (T - 1));
  const z = wt.map((x, j) => (f.tau2 > 0 ? f.tau2 / (f.tau2 + sj[j] / x) : 0)), zs = sum(z);
  const b = zs > 0 ? z.map((x) => x / zs) : wt.map((x) => x / sum(wt)), mu = sum(m.map((x, j) => b[j] * x));
  return m.map((x, j) => z[j] * x + (1 - z[j]) * mu);
}
console.log(`Balanced normal worlds (equal volumes, ρ = 0, equal σ); ${N} draws; relative price in % of the floor.`);
console.log('J  T  | volume | z    | (a) law | 1st order | simulated     | (b) law | simulated extra');
for (const J of [8, 20]) for (const T of [5, 10]) for (const volume of [100, 300, 1000, 3000, 10000]) {
  const world = E.makeWorld({ J, T, volume, spread: 0, growth: 0, normal: true, rho: 0 });
  const fl = E.floorBlend(world), z = fl.z[0], t2 = world.truth.tau2;
  const floorJ = (j) => E.linMse(fl.K, t2, j, fl.b.map((bi, i) => (i === j ? fl.z[j] : 0) + (1 - fl.z[j]) * bi));
  const floor = sum(world.w.map((_, j) => floorJ(j))) / J;
  const pr = PF.predict(world, ['bs']).out.bs, first = pr.price;
  const lawA = (2 / J) * T / (T - 1) * (1 - z) / z, lawB = z * (1 - z) * 2 / (T - 1);
  const r = E.rng(7), F = [], A = [], B = [];
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates)); A.push(se(E.fitBS(data).rates)); B.push(se(ownVarRates(data)));
  }
  const f = L.meanSE(F).m, a = L.paired(A, F), b = L.paired(B, A);
  console.log(`${String(J).padEnd(2)} ${String(T).padEnd(2)} | ${String(volume).padStart(6)} | ${z.toFixed(2)} | ${(100 * lawA).toFixed(1).padStart(7)} | ${(100 * first / floor).toFixed(1).padStart(9)} | ${L.pm(a, 100 / f).padEnd(13)} | ${(100 * lawB).toFixed(1).padStart(7)} | ${L.pm(b, 100 / f)}`);
}
