// Purpose: conjecture + decide (G1c, Finding 48). Where does corrBS's ρ̂ bias come from, and does fixing it
// move the rates? Part A: E ρ̂ − ρ with ρ̂'s denominator built from the true σⱼ (unbiased, rhoPooled_unbiased),
// the own σ̂ⱼ, the app's σ̃ⱼ, and the pooled σ̄; the level Σσ̃ⱼ²/Σσ̂ⱼ² and how often the sufficient (W ordered
// like σ̂², VcW.sum_shrink_le) and exact (VcW.sum_shrink_le_iff) conditions hold. Part B: corrBS's MSE with
// opts.rhoOwn (ρ̂ from the own σ̂ⱼ) and opts.sigLevel (σ̃ⱼ² rescaled to the σ̂ⱼ²'s average), paired.
// App's world, gamma noise, J = 8. Run: node studies/runs/rho-level.js [draws]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N } = L.args({ N: 600 });
const worlds = L.grid({ regime: ['app', 'thesis'], noiseSpread: [0, 1, 2], rho: [0, 0.6], T: [5, 10] });
console.log(`Part A (app regime). E ρ̂ − ρ (± 2 SE), denominator from: true σ | own σ̂ | σ̃ (app) | pooled σ̄; level Σσ̃²/Σσ̂²; % draws: W ordered, level low`);
console.log(`Part B. corrBS MSE (% of floor) and paired differences, ± 2 SE`);
const rowsB = [];
for (const p of worlds) {
  const world = E.makeWorld(Object.assign({ noiseSpread: p.noiseSpread, rho: p.rho, T: p.T }, L.regimes[p.regime]));
  const sj = world.truth.sigmaj2.map(Math.sqrt), r = E.rng(2026), fl = E.floorBlend(world);
  const acc = { t: [], o: [], a: [], p: [] }, lv = [], F = [], A = [], B = [], C = [];
  let mono = 0, low = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), e = E.vcEstimate(data), J = e.m.length, T = p.T;
    const num = e.rhoRaw * e.qa;
    const D = (sd) => { let q = 0; for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) q += sd[i] * sd[j] * ((T - 2) + e.S[i][j] ** 2 / (e.wt[i] * e.wt[j])); return q; };
    acc.t.push(num / D(sj)); acc.o.push(num / D(e.own.map(Math.sqrt))); acc.a.push(e.rhoRaw); acc.p.push(num / D(e.own.map(() => Math.sqrt(e.pooled))));
    lv.push(L.sum(e.s2) / L.sum(e.own));
    let ok = true;
    for (let i = 0; i < J; i++) for (let j = 0; j < J; j++) if (e.own[i] < e.own[j] && e.W[i] > e.W[j]) ok = false;
    if (ok) mono++;
    if (L.sum(e.s2) <= L.sum(e.own) + 1e-12) low++;
    const se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates)); A.push(se(E.fitVC(data).rates));
    B.push(se(E.fitVC(data, { rhoOwn: true }).rates)); C.push(se(E.fitVC(data, { sigLevel: true }).rates));
  }
  const name = `${p.regime} σⱼ×${p.noiseSpread} ρ=${p.rho} T=${p.T}`.padEnd(26);
  if (p.regime === 'app' && p.rho > 0) {
    const f = (x) => { const m = L.meanSE(x); return `${(m.m - p.rho).toFixed(3)} ± ${(2 * m.se).toFixed(3)}`; };
    console.log(`A ${name} | ${f(acc.t)} | ${f(acc.o)} | ${f(acc.a)} | ${f(acc.p)} | ${L.meanSE(lv).m.toFixed(2)} | ${(100 * mono / N).toFixed(0)}% ${(100 * low / N).toFixed(0)}%`);
  }
  const fm = L.meanSE(F).m, dB = L.paired(B, A), dC = L.paired(C, A);
  rowsB.push({ name, a: 100 * L.meanSE(A).m / fm, dB, dC, fm });
}
for (const x of rowsB) console.log(`B ${x.name} | corrBS ${x.a.toFixed(0)} | rhoOwn − corrBS ${L.pm(x.dB, 100 / x.fm)} | sigLevel − corrBS ${L.pm(x.dC, 100 / x.fm)}`);
const mB = rowsB.map((x) => 100 * x.dB.m / x.fm), mC = rowsB.map((x) => 100 * x.dC.m / x.fm);
console.log(`\nrhoOwn − corrBS: mean ${(L.sum(mB) / mB.length).toFixed(1)}, ${Math.min(...mB).toFixed(1)} to ${Math.max(...mB).toFixed(1)}; sigLevel − corrBS: mean ${(L.sum(mC) / mC.length).toFixed(1)}, ${Math.min(...mC).toFixed(1)} to ${Math.max(...mC).toFixed(1)}`);
