// Purpose: decide (and check Finding 47). The app's Wⱼ (Var σ̂ⱼ² from the yearly terms) is low by a relative
// O(1/T) (VcW.integral_vcW_equal); the corrected Wⱼ = λW + μσ̂ⱼ⁴ (Engine.vcWCoef, opts.corrW; VcW.integral_vcWCorr) is
// unbiased when the noise has a fixed shape. Does the correction move corrBS's MSE, and β² (the spread of
// the σⱼ²) towards its target? Paired draws, factorial over regime × σⱼ spread × ρ × T, gamma noise (default).
// Columns: mean W / Var σ̂² over regions (raw, corrected; Var from the draws), β̂²raw − β² in units of β²
// (σⱼ spread > 0) or of σ⁴ (spread 0), corrBS MSE in % of the floor and the paired difference corrected − raw.
// Run: node studies/runs/vcw-corr.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 600 });
const worlds = L.grid({ regime: ['app', 'thesis'], noiseSpread: [0, 1, 2], rho: [0, 0.6], T: [3, 5, 10] });

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ noiseSpread: p.noiseSpread, rho: p.rho, T: p.T }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], A = [], B = [];
  const s2 = world.truth.sigmaj2, J = s2.length, mean = L.sum(s2) / J;
  const beta2 = L.sum(s2.map((x) => (x - mean) ** 2)) / (J - 1), scale = beta2 > 0 ? beta2 : world.truth.sigma2 ** 2;
  const own = [], Wr = [], Wc = [], bR = [], bC = [];
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    A.push(se(E.fitVC(data).rates)); B.push(se(E.fitVC(data, { corrW: true }).rates));
    const pr = E.vcEstimate(data), pc = E.vcEstimate(data, { corrW: true });
    own.push(pr.own); Wr.push(pr.W); Wc.push(pc.W); bR.push((pr.betweenRaw - beta2) / scale); bC.push((pc.betweenRaw - beta2) / scale);
  }
  // Var σ̂ⱼ² per region from the draws; ratio of the mean W to it, averaged over regions
  const ratio = (Ws) => L.sum(Array.from({ length: J }, (_, j) => {
    const x = own.map((o) => o[j]), m = L.sum(x) / N, v = L.sum(x.map((y) => (y - m) ** 2)) / (N - 1);
    return L.sum(Ws.map((w) => w[j])) / N / v;
  })) / J;
  const f = L.meanSE(F).m;
  return { p, a: 100 * L.meanSE(A).m / f, b: 100 * L.meanSE(B).m / f, d: L.paired(B, A), f, rr: ratio(Wr), rc: ratio(Wc), bR: L.meanSE(bR), bC: L.meanSE(bC), spread: beta2 > 0 };
}

L.mapWorlds(__filename, worlds, runWorld, jobs, (p) => p.T).then((rows) => {
  console.log(`J = 8, gamma noise, ${N} draws; W/Var: mean W over Var σ̂² (draws); β̂² bias in units of β² (σⱼ spread) or σ⁴ (none); MSE in % of the floor`);
  console.log('world                        | W/Var raw  corr | β̂² bias raw   corr  | MSE raw  corr | corr − raw (± 2 SE)');
  for (const x of rows) {
    const name = `${x.p.regime} σⱼ×${x.p.noiseSpread} ρ=${x.p.rho} T=${x.p.T}`;
    console.log(`${name.padEnd(28)} |  ${x.rr.toFixed(2)}   ${x.rc.toFixed(2)}  | ${x.bR.m.toFixed(2).padStart(6)}  ${x.bC.m.toFixed(2).padStart(6)}  | ${x.a.toFixed(0).padStart(5)} ${x.b.toFixed(0).padStart(5)} | ${L.pm(x.d, 100 / x.f)}`);
  }
  const diffs = rows.map((x) => 100 * x.d.m / x.f);
  console.log(`\ncorr − raw: mean ${(L.sum(diffs) / diffs.length).toFixed(1)}, min ${Math.min(...diffs).toFixed(1)}, max ${Math.max(...diffs).toFixed(1)} points; wins ${rows.filter((x) => L.sig(x.d, 1e-9) < 0).length}, losses ${rows.filter((x) => L.sig(x.d, 1e-9) > 0).length} of ${rows.length}`);
});
