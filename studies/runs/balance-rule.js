// S76. Purpose: a per-portfolio on/off rule for the balance switch (Finding 46: cost = E(T − μ̄)² − E(r̄ − μ̄)²).
// Rules: "on" (balance to the cross-fitted level, the app's default), "off" (raw corrBS),
// "held-out" (on iff the leave-one-year-out score of the balanced fit is lower), and "plug-in" (on iff the
// cost formula on corrBS's fitted K̂, τ̂² is negative: with the target's weights a (cross-fitted c̄, from
// Engine.crossFitLevel) and the fit's c = Σⱼ uⱼwⱼ, cost̂ = mse(a) − mse(c), mse(d) = dᵀK̂d − 2τ̂²dᵀu + τ̂²uᵀu;
// BalanceCost.balance_cost_portLin, fixed weights, no bias term).
// Worlds as S75 (56), corrBS, 400 draws. Also the portfolio bias of each rule (bp of the tariff).
// --vol (S84): volumes vary by year (volNoise 0.2, volTrend 0.05, volSeed 1) and a fifth rule "auto", the app's
// Engine.balanceAuto (priced on the yearly cells, BalanceCost.balance_cost_cellLin); output balance-rule-vol.out.txt.
// Run: node studies/runs/balance-rule.js [draws] [--jobs=k] [--vol]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 400 });
const worlds = L.grid({ regime: ['app', 'thesis', 'thesisShape'], rho: [0, 0.3, 0.6, 0.9], noiseSpread: [0, 1, 2], T: [5, 10] })
  .filter((p) => p.regime !== 'thesisShape' || p.noiseSpread === 2);
const VOL = process.argv.includes('--vol');
const IDS = VOL ? ['on', 'off', 'ho', 'plug', 'auto'] : ['on', 'off', 'ho', 'plug'];

function plugCost(f, data) {
  const cf = E.crossFitLevel(data);
  if (!cf || !(f.tau2 > 0)) return null;
  const wt = data.w.map(L.sum), W = L.sum(wt), u = wt.map((x) => x / W), J = u.length, K = f.K, t2 = f.tau2;
  const c = new Array(J).fill(0);
  for (let j = 0; j < J; j++) for (let i = 0; i < J; i++) c[i] += u[j] * ((i === j ? f.z[j] : 0) + (1 - f.z[j]) * f.b[i]);
  const mse = (d) => { let q = 0; for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += d[i] * K[i][k] * d[k];
    return q - 2 * t2 * L.sum(d.map((x, i) => x * u[i])) + t2 * L.sum(u.map((x) => x * x)); };
  return mse(cf.cbar) - mse(c);
}

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread }, L.regimes[p.regime], VOL ? { volNoise: 0.2, volTrend: 0.05, volSeed: 1 } : {}));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], S = Object.fromEntries(IDS.map((k) => [k, []])), B = Object.fromEntries(IDS.map((k) => [k, []]));
  let pickH = 0, pickP = 0, pickA = 0;
  const bal = (d) => E.balanceFit(E.fitVC(d), d, { target: 'crossFit' });
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), se = (x) => E.weightedSE(data, x, levels);
    const wt = data.w.map(L.sum), W = L.sum(wt), bias = (x) => 1e4 * L.sum(x.map((v, j) => wt[j] * (v - levels[j]))) / W;
    F.push(se(fl.apply(data).rates));
    const off = E.fitVC(data), on = E.balanceFit(off, data, { target: 'crossFit' });
    const useH = E.loyoLoss(data, bal) < E.loyoLoss(data, E.fitVC);
    const pc = plugCost(off, data), useP = pc !== null && pc < 0;
    if (useH) pickH++; if (useP) pickP++;
    const useA = VOL && E.balanceAuto(off, data).balanceAuto.on;
    if (useA) pickA++;
    const raw = { on, off, ho: useH ? on : off, plug: useP ? on : off, auto: useA ? on : off };
    for (const id of IDS) { S[id].push(se(raw[id].rates)); B[id].push(bias(raw[id].rates)); }
  }
  const f = L.meanSE(F).m, best = L.meanSE(S.on).m <= L.meanSE(S.off).m ? S.on : S.off;
  return { p, f, pickH: pickH / N, pickP: pickP / N, pickA: pickA / N, rel: Object.fromEntries(IDS.map((id) => [id, L.meanSE(S[id]).m / f])),
    regret: Object.fromEntries(IDS.map((id) => [id, L.paired(S[id], best)])),
    bias: Object.fromEntries(IDS.map((id) => [id, L.meanSE(B[id]).m])) };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  if (VOL) console.log('Volumes vary by year (volNoise 0.2, volTrend 0.05, volSeed 1); auto = Engine.balanceAuto.');
  console.log(`corrBS, ${N} draws. MSE in % of the blend floor; picks = share of draws balanced; bias in bp of the tariff (on / off).`);
  console.log('world                          |  on  | off  | held-out | plug-in | picks ho | picks plug | bias on / off' + (VOL ? ' | auto | picks auto | bias auto' : ''));
  for (const r of rows) {
    const p = r.p, x = (id) => (100 * r.rel[id]).toFixed(0).padStart(4);
    console.log(`${`${p.regime} ρ=${p.rho} σⱼ×${p.noiseSpread} T=${p.T}`.padEnd(30)} | ${x('on')} | ${x('off')} |   ${x('ho')}   |  ${x('plug')}   |   ${(100 * r.pickH).toFixed(0).padStart(3)}%   |    ${(100 * r.pickP).toFixed(0).padStart(3)}%    | ${r.bias.on.toFixed(0)} / ${r.bias.off.toFixed(0)}` + (VOL ? ` | ${x('auto')} |    ${(100 * r.pickA).toFixed(0).padStart(3)}%    | ${r.bias.auto.toFixed(0)}` : ''));
  }
  console.log('\nRegret against the better of on and off in each world (points of the floor, paired):');
  for (const id of IDS) {
    let w = 0; const pts = rows.map((r) => { const d = r.regret[id]; if (L.sig(d, 1e-9 * r.f) > 0) w++; return 100 * d.m / r.f; });
    console.log(`  ${id.padEnd(9)} mean ${(L.sum(pts) / pts.length).toFixed(1)}, max ${Math.max(...pts).toFixed(1)}, worse in ${w} of ${rows.length}`);
  }
});
