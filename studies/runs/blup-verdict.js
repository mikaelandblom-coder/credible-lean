// S74. Purpose: a data-side choice between the BLUP and corrBS (PLAN Pending "Gain against price"; Finding 45).
// Candidate "price": the BLUP iff its exact gain on K̂ exceeds its bootstrapped extra price
// (blupGainPrice below: parametric bootstrap of the weight errors, Butar & Lahiri 2003). Compared with
// corrBS, the BLUP and "held-out" (S72: the better leave-one-year-out score of the balanced fits).
// Worlds and scoring as S72 (runs/recommended-fit.js): regime app / thesis / thesisShape, σⱼ spread 0–2,
// ρ ∈ {0, 0.3, 0.6, 0.9}, T ∈ {5, 10}, J = 8, gamma noise, balance switch on (cross-fitted level).
// Run: node studies/runs/blup-verdict.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 400 });

/**
 * The BLUP against the blend on corrBS's K̂: gain against price (Finding 45, studies S73–S74).
 * gain: exact on K̂, (floor − BLUP)/floor with both scored on K̂ (CoreMoments.mse_blend_eq_blup_add).
 * price: the extra squared weight error of the BLUP over the blend, Σⱼ wⱼ*(‖d̂*ⱼ − d*ⱼ‖² − ‖ŵⱼ − wⱼ‖²)_K̂ /
 *   Σⱼ wⱼ* floorⱼ, by a parametric bootstrap from the fit (Butar & Lahiri 2003: g₃ without derivatives):
 *   draw data from K̂, τ̂², σ̃ⱼ², ρ̂ (normal noise, the volumes of the data), refit corrBS, compare the weights
 *   with those of K̂. First order this is blupPrice − blendPrice averaged over θ̂ (BlupPrice.tendsto_*);
 *   the bootstrap keeps clipping and shrinkage. No cross term 2E[AB].
 * `opts.B` bootstrap draws (default 60), `opts.seed`. Verdict 'blup' iff gain > price. Null when τ̂² = 0.
 */
function blupGainPrice(data, opts) {
  const B = (opts && opts.B) || 60, f = E.fitVC(data), J = f.means.length, T = data.X[0].length;
  if (!(f.tau2 > 0)) return null;
  const K = f.K, t2 = f.tau2, wt = data.w.map(L.sum), wall = L.sum(wt);
  const blendRows = (Kx, tx) => { const { b, z } = E.bestBlendWeights(Kx, tx); return z.map((zj, j) => b.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi)); };
  const blupRows = (Kx, tx) => Kx.map((_, j) => E.blupWeight(Kx, tx, j));
  const quad = (d) => { let q = 0; for (let i = 0; i < J; i++) for (let k = 0; k < J; k++) q += d[i] * K[i][k] * d[k]; return q; };
  const Db = blendRows(K, t2), Du = blupRows(K, t2);
  const floorJ = Db.map((d, j) => E.linMse(K, t2, j, d)), floor = L.sum(floorJ.map((x, j) => wt[j] * x)) / wall;
  const blup = L.sum(Du.map((d, j) => wt[j] * E.linMse(K, t2, j, d))) / wall;
  const world = E.makeWorld({ J, T, rho: f.rho, normal: true });
  world.w = data.w.map((row) => row.slice());
  world.truth = Object.assign({}, world.truth, { mu: f.mu, tau2: t2, sigmaj2: f.sigma2.slice(),
    L: Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, k) => (i === k ? t2 : 0))) });
  const r = E.rng((opts && opts.seed) || 7331);
  let eb = 0, eu = 0, n = 0;
  for (let k = 0; k < B; k++) {
    const g = E.fitVC(E.draw(world, r).data);
    if (!(g.tau2 > 0)) { // τ̂*² = 0: both rates are the GLS mean, the same weights b̂*
      const bb = E.bestBlendWeights(g.K, 1).b;
      for (let j = 0; j < J; j++) { eb += wt[j] * quad(bb.map((x, i) => x - Db[j][i])); eu += wt[j] * quad(bb.map((x, i) => x - Du[j][i])); }
    } else {
      const Gb = blendRows(g.K, g.tau2), Gu = blupRows(g.K, g.tau2);
      for (let j = 0; j < J; j++) { eb += wt[j] * quad(Gb[j].map((x, i) => x - Db[j][i])); eu += wt[j] * quad(Gu[j].map((x, i) => x - Du[j][i])); }
    }
    n++;
  }
  const priceBlend = eb / n / wall / floor, priceBlup = eu / n / wall / floor, gain = (floor - blup) / floor;
  return { floor, gain, price: priceBlup - priceBlend, priceBlend, priceBlup, B: n, verdict: gain > priceBlup - priceBlend ? 'blup' : 'blend' };
}


const worlds = L.grid({ regime: ['app', 'thesis', 'thesisShape'], rho: [0, 0.3, 0.6, 0.9], noiseSpread: [0, 1, 2], T: [5, 10] })
  .filter((p) => p.regime !== 'thesisShape' || p.noiseSpread === 2);
const IDS = ['vc', 'blup', 'price', 'ho'];
const UIDS = ['vc', 'blup']; // also scored without balancing

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [], S = Object.fromEntries(IDS.map((k) => [k, []])), U = Object.fromEntries(UIDS.map((k) => [k, []]));
  let pickP = 0, pickH = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r);
    const se = (x) => E.weightedSE(data, x, levels);
    F.push(se(fl.apply(data).rates));
    const bal = (fn) => (d) => E.balanceFit(fn(d), d, { target: 'crossFit' });
    const vc = E.fitVC(data), blup = E.fitBLUP(data);
    const g = blupGainPrice(data, { seed: 1 + k }), useP = !!g && g.verdict === 'blup';
    const useH = E.loyoLoss(data, bal(E.fitBLUP)) < E.loyoLoss(data, bal(E.fitVC));
    if (useP) pickP++; if (useH) pickH++;
    const raw = { vc, blup, price: useP ? blup : vc, ho: useH ? blup : vc };
    for (const id of IDS) S[id].push(se(E.balanceFit(raw[id], data, { target: 'crossFit' }).rates));
    for (const id of UIDS) U[id].push(se(raw[id].rates));
  }
  const f = L.meanSE(F).m, best = L.meanSE(S.vc).m <= L.meanSE(S.blup).m ? S.vc : S.blup;
  return { p, f, pickP: pickP / N, pickH: pickH / N, rel: Object.fromEntries(IDS.map((id) => [id, L.meanSE(S[id]).m / f])),
    relU: Object.fromEntries(UIDS.map((id) => [id, L.meanSE(U[id]).m / f])), dBal: L.paired(S.vc, U.vc), dU: L.paired(U.blup, U.vc),
    d: { blup: L.paired(S.blup, S.vc), price: L.paired(S.price, S.vc), ho: L.paired(S.ho, S.vc) },
    regret: { price: L.paired(S.price, best), ho: L.paired(S.ho, best) } };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  console.log(`J = 8, gamma noise, ${N} draws per world, balance switch on. MSE in % of the blend floor; Δ = fit − corrBS, paired ± 2 SE.`);
  console.log('world                          | corrBS | BLUP | price | held-out | price picks | held-out picks | Δ BLUP        | Δ price       | Δ held-out');
  for (const r of rows) {
    const p = r.p, rel = (id) => (100 * r.rel[id]).toFixed(0).padStart(4), pm = (d) => L.pm(d, 100 / r.f).padEnd(13);
    console.log(`${`${p.regime} ρ=${p.rho} σⱼ×${p.noiseSpread} T=${p.T}`.padEnd(30)} |  ${rel('vc')}  | ${rel('blup')} | ${rel('price')}  |   ${rel('ho')}   |    ${(100 * r.pickP).toFixed(0).padStart(3)}%     |      ${(100 * r.pickH).toFixed(0).padStart(3)}%     | ${pm(r.d.blup)} | ${pm(r.d.price)} | ${L.pm(r.d.ho, 100 / r.f)}`);
  }
  const tally = (get) => {
    let w = 0, b = 0;
    const pts = rows.map((r) => { const d = get(r), g = L.sig(d, 1e-9 * r.f); if (g > 0) w++; else if (g < 0) b++; return 100 * d.m / r.f; });
    return `worse in ${w}, better in ${b}, even in ${rows.length - w - b} of ${rows.length}; mean ${(L.sum(pts) / pts.length).toFixed(1)}, range ${Math.min(...pts).toFixed(1)} to ${Math.max(...pts).toFixed(1)} points of the floor`;
  };
  console.log('\nWithout balancing (raw rates): corrBS, BLUP; Δ bal = balanced corrBS − raw corrBS; Δ BLUP raw = raw BLUP − raw corrBS.');
  for (const r of rows) {
    const p = r.p;
    console.log(`${`${p.regime} ρ=${p.rho} σⱼ×${p.noiseSpread} T=${p.T}`.padEnd(30)} | ${(100 * r.relU.vc).toFixed(0).padStart(4)} | ${(100 * r.relU.blup).toFixed(0).padStart(4)} | Δ bal ${L.pm(r.dBal, 100 / r.f).padEnd(13)} | Δ BLUP raw ${L.pm(r.dU, 100 / r.f)}`);
  }
  console.log('\nSummary (paired):');
  console.log(`  balanced corrBS − raw corrBS: ${tally((r) => r.dBal)}`);
  console.log(`  raw BLUP − raw corrBS:        ${tally((r) => r.dU)}`);
  console.log(`  BLUP − corrBS:          ${tally((r) => r.d.blup)}`);
  console.log(`  price − corrBS:         ${tally((r) => r.d.price)}`);
  console.log(`  held-out − corrBS:      ${tally((r) => r.d.ho)}`);
  console.log(`  price − better of corrBS and BLUP (regret):    ${tally((r) => r.regret.price)}`);
  console.log(`  held-out − better of corrBS and BLUP (regret): ${tally((r) => r.regret.ho)}`);
});
