// corrBS (fitVC) flags under correlation: are they the fit's fault or the optimum's?
// (1) The floor (true K, τ²): share of draws with b < 0, z > 1, off-balance > 1%.
// (2) The cost of restoring balance Σⱼ wⱼ*μ̂ⱼᵇ = Σⱼ wⱼ*μ̂ⱼ, keeping z:
//     'bal'   collective as in BS: μ̂ = Σ wⱼ*(1 − zⱼ)μ̂ⱼ / Σ wⱼ*(1 − zⱼ)  (in BS wⱼ*(1 − zⱼ) ∝ zⱼ, so b = z/z*),
//     'scale' every rate times Σ wⱼ*μ̂ⱼ / Σ wⱼ*μ̂ⱼᵇ (the base-rate correction).
//     'shift' every rate plus Σ wⱼ*(μ̂ⱼ − μ̂ⱼᵇ)/w** (benchmarking: Wang, Fuller & Qu 2008 with loss weights wⱼ*,
//             the smallest change in our exposure-weighted loss that restores the total).
//     'opt'   the best balanced blend (PLAN G7, Lean Core.bestBalanced_optimal): keep b, take
//             zⱼ = 1 − c*·bⱼ/wⱼ* with c* = Σ wgⱼ(1 − zⱼ)bⱼ/wⱼ* / Σ wgⱼ(bⱼ/wⱼ*)², gⱼ = Kⱼⱼ − s² (floor only).
//     All four are exactly balanced. Error = exposure-weighted squared error, % of the floor's.
// Data from E.draw (gamma levels and noise, the app's world). Run: node studies/vc-balance.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

function offBal(wt, m, rates) { return sum(wt.map((x, j) => x * (m[j] - rates[j]))) / sum(wt.map((x, j) => x * m[j])); }
function balanced(wt, m, z) {
  const c = wt.map((x, j) => x * (1 - z[j])), cs = sum(c);
  if (Math.abs(cs) < 1e-12 * sum(wt)) return null;           // Σ wⱼ*(1 − zⱼ) = 0: no collective balances
  const mu = sum(c.map((x, j) => x * m[j])) / cs;
  return m.map((x, j) => z[j] * x + (1 - z[j]) * mu);
}
function shifted(wt, m, rates) { const d = sum(wt.map((x, j) => x * (m[j] - rates[j]))) / sum(wt); return rates.map((r) => r + d); }
function scaled(wt, m, rates) { const f = sum(wt.map((x, j) => x * m[j])) / sum(wt.map((x, j) => x * rates[j])); return rates.map((r) => r * f); }

function run(params) {
  const world = E.makeWorld(params), fl = E.floorBlend(world), r = E.rng(7);
  const wt = world.w.map(sum);
  const fFlags = { bNeg: fl.b.some((x) => x < 0), zOver1: fl.z.some((x) => x > 1) };
  const acc = { floorOpt: 0, floor: 0, floorBal: 0, floorScale: 0, floorShift: 0, vc: 0, vcShift: 0, vcBal: 0, vcScale: 0, vcClip: 0, bs: 0 };
  // Weights the floor IS balanced for: Σ vⱼ(μ̂ⱼ − μ̂ⱼᵇ) = Σ vⱼ(1 − zⱼ)(μ̂ⱼ − μ̂) = 0 for all data iff vⱼ(1 − zⱼ) ∝ bⱼ.
  const v = fl.b.map((x, j) => x / (1 - fl.z[j])), vs = sum(v), vMin = Math.min(...v.map((x) => x / vs));
  // G7: the best balanced z for loss and balance weights wⱼ*, b fixed.
  const g = fl.b.map((_, j) => fl.K[j][j] - fl.s2), a = fl.b.map((x, j) => x / wt[j]);
  const cOpt = sum(a.map((x, j) => wt[j] * g[j] * (1 - fl.z[j]) * x)) / sum(a.map((x, j) => wt[j] * g[j] * x * x));
  const zOpt = a.map((x) => 1 - cOpt * x);
  const cnt = { flOff: 0, vcB: 0, vcZ: 0, vcOff: 0, vcNull: 0 };
  let flOffAbs = 0, vcOffAbs = 0;
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, r), m = E.cohortMeans(data).m;
    const se = (rates) => E.weightedSE(data, rates, levels);
    const fr = fl.apply(data).rates, fo = offBal(wt, m, fr);
    if (Math.abs(fo) > 0.01) cnt.flOff++; flOffAbs += Math.abs(fo);
    acc.floor += se(fr);
    acc.floorBal += se(balanced(wt, m, fl.z) || fr);
    acc.floorScale += se(scaled(wt, m, fr));
    acc.floorShift += se(shifted(wt, m, fr));
    acc.floorOpt += se(E.blend(m, zOpt, fl.b).rates);
    const f = E.fitVC(data);
    if (f.flags.bNeg) cnt.vcB++; if (f.flags.zOver1) cnt.vcZ++; if (f.flags.offBalance) cnt.vcOff++;
    vcOffAbs += Math.abs(offBal(wt, m, f.rates));
    acc.vc += se(f.rates);
    const vb = balanced(wt, m, f.z); if (!vb) cnt.vcNull++;
    acc.vcBal += se(vb || f.rates);
    acc.vcScale += se(scaled(wt, m, f.rates));
    acc.vcShift += se(shifted(wt, m, f.rates));
    acc.vcClip += se(E.blend(m, f.z.map((x) => Math.min(x, 1)), f.b).rates);
    acc.bs += se(E.fitBS(data).rates);
  }
  const p = (x) => `${(100 * x / N).toFixed(0)}%`.padStart(4);
  const rel = (x) => (100 * x / acc.floor).toFixed(0).padStart(4);
  return `floor min b ${Math.min(...fl.b).toFixed(2).padStart(5)} max z ${Math.max(...fl.z).toFixed(2)} min v ${vMin.toFixed(2).padStart(5)} off>1% ${p(cnt.flOff)} |off| ${(100 * flOffAbs / N).toFixed(2)}% | ` +
    `vc b<0 ${p(cnt.vcB)} z>1 ${p(cnt.vcZ)} off>1% ${p(cnt.vcOff)} |off| ${(100 * vcOffAbs / N).toFixed(2)}% | ` +
    `floor bal ${rel(acc.floorBal)} scale ${rel(acc.floorScale)} shift ${rel(acc.floorShift)} opt ${rel(acc.floorOpt)} | vc ${rel(acc.vc)} bal ${rel(acc.vcBal)} scale ${rel(acc.vcScale)} shift ${rel(acc.vcShift)} clip z ${rel(acc.vcClip)} | bs ${rel(acc.bs)}` +
    (cnt.vcNull ? ` (Σw(1−z)=0 in ${cnt.vcNull})` : '');
}
console.log(`draws ${N}. Flags: share of draws (floor b, z are fixed per world). Errors in % of the floor (floor = 100).`);
console.log('min v: smallest balancing weight vⱼ = bⱼ/(1 − zⱼ) of the floor (normalised); v ≥ 0 only if every b ≥ 0. clip z: vc with z capped at 1.');
console.log('bal = collective Σw(1−z)μ̂ⱼ/Σw(1−z) (BS style), scale = rates × Σwμ̂ⱼ/Σwμ̂ⱼᵇ, shift = rates + Σw(μ̂ⱼ − μ̂ⱼᵇ)/w**, opt = best balanced z (G7); all exactly balanced.');
for (const ns of [1, 0]) for (const [J, T] of [[8, 5], [8, 10], [20, 10]]) for (const rho of [0, 0.3, 0.6]) {
  const label = `σⱼ ${ns ? 'spread' : 'equal '} J=${String(J).padStart(2)} T=${String(T).padStart(2)} ρ=${rho.toFixed(1)}`;
  console.log(`${label} | ${run({ J, T, rho, noiseSpread: ns })}`);
}
// The default spread world of the request, with volume spread 2 for contrast.
console.log(`σⱼ spread J= 8 T=10 ρ=0.6 vol spread 2 | ${run({ rho: 0.6, noiseSpread: 1, spread: 2 })}`);
