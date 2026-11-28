// S79. Recheck the app's conclusions when the regions' volumes no longer share one shape over the years.
// The app's worlds had wⱼₜ = aⱼ(1 + growth)^t for every region (one shape), which makes Σ̂ PSD by construction
// (S78) and several shortcuts exact (Finding 37: cov(B, P) = 0 needs proportional volumes). The world switch
// "Volumes vary by year" (params volNoise = 0.2, volTrend = 0.05; fixed per world by volSeed) gives each region
// its own growth and year-to-year noise. Same grid with the switch off and on, J = 8, gamma noise, the page's
// default balance (balance: 'auto', S76). Entries: exposure-weighted MSE of the rates in % of the floor (best
// blend with the true K of that world), so off and on are each against their own floor.
// Also: the gain-against-price choice (corrBS g/p) against the better of its two candidates, the damping rule
// S3 against the best fixed θ for the corr fit, and the share of draws where Σ̂ is not PSD.
// Run: node studies/runs/volume-noise.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 600 });

const VOL = { off: {}, on: { volNoise: 0.2, volTrend: 0.05 } };
const worlds = L.grid({ vol: ['off', 'on'], seed: [1, 2], T: [5, 10], rho: [0, 0.3, 0.6], noiseSpread: [0, 2] })
  .filter((p) => p.vol === 'on' || p.seed === 1);
const IDS = ['bs', 'vc', 'vcGP', 'blup', 'blupPool', 'corr'];
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.99];

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ T: p.T, rho: p.rho, noiseSpread: p.noiseSpread, volSeed: p.seed }, VOL[p.vol]));
  const fl = E.floorBlend(world), r = E.rng(2026);
  const F = [], S = Object.fromEntries(IDS.map((k) => [k, []])), U = Object.fromEntries(IDS.map((k) => [k, []])), Vp = [], Th = GRID.map(() => []);
  let np = 0, balOn = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r);
    const se = (x) => E.weightedSE(data, x.rates, levels);
    F.push(se(fl.apply(data)));
    for (const id of IDS) {
      const raw = E.fitWith(id, data), bal = E.fitWith(id, data, { balance: 'auto' });
      U[id].push(se(raw)); S[id].push(se(bal));
      if (id === 'vc' && bal.balanceAuto && bal.balanceAuto.on) balOn++;
    }
    Vp.push(se(E.balanceAuto(E.fitVC(data, { pooled: true }), data)));
    if (!E.isPSD(E.sigmaHat(data).Sig)) np++;
    GRID.forEach((th, i) => Th[i].push(se(E.fitCorr(data, { theta: th }))));
  }
  const f = L.meanSE(F).m, rel = (a) => 100 * L.meanSE(a).m / f;
  const out = Object.fromEntries(IDS.map((id) => [id, rel(S[id])])), outU = Object.fromEntries(IDS.map((id) => [id, rel(U[id])]));
  const vcPooled = rel(Vp), best2 = Math.min(out.vc, vcPooled);
  const thetas = Th.map(rel);
  return { p, out, outU, vcPooled, gpRegret: out.vcGP - best2, thetaBest: Math.min(...thetas), thetaArg: GRID[thetas.indexOf(Math.min(...thetas))], np: np / N, balOn: balOn / N };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  console.log(`J = 8, gamma noise, ${N} draws per world, balance 'auto'. MSE in % of the world's floor.`);
  console.log('Each fit: unbalanced / balanced (auto). Bal on: share of draws where the rule balances corrBS.');
  console.log('vol  seed T  ρ   σsp | ' + IDS.map((x) => x.padStart(14)).join('') + ' | vc pooled  g/p regret | corr S3, best θ (θ) | bal on');
  for (const r of rows) {
    const p = r.p;
    console.log(`${p.vol.padEnd(4)} ${p.seed}    ${String(p.T).padEnd(2)} ${p.rho.toFixed(1)} ${p.noiseSpread}   | ` +
      IDS.map((id) => `${r.outU[id].toFixed(1)}/${r.out[id].toFixed(1)}`.padStart(14)).join('') + ` | ${r.vcPooled.toFixed(1).padStart(9)} ${r.gpRegret.toFixed(1).padStart(10)} | ` +
      `${r.outU.corr.toFixed(1)}, ${r.thetaBest.toFixed(1)} (${r.thetaArg})`.padStart(20) + ` | ${r.balOn.toFixed(2)}`);
  }
  // summary: mean over worlds, off against on, and rank agreement
  const mean = (vol, f) => { const x = rows.filter((r) => r.p.vol === vol).map(f); return L.sum(x) / x.length; };
  console.log('\nMean over worlds (off | on):');
  for (const id of IDS) console.log(`  ${id.padEnd(9)} unbalanced ${mean('off', (r) => r.outU[id]).toFixed(1)} | ${mean('on', (r) => r.outU[id]).toFixed(1)};  balanced ${mean('off', (r) => r.out[id]).toFixed(1)} | ${mean('on', (r) => r.out[id]).toFixed(1)}`);
  console.log(`  balance on (corrBS) ${mean('off', (r) => r.balOn).toFixed(2)} | ${mean('on', (r) => r.balOn).toFixed(2)}`);
  console.log(`  g/p regret ${mean('off', (r) => r.gpRegret).toFixed(2)} | ${mean('on', (r) => r.gpRegret).toFixed(2)}; max ${Math.max(...rows.filter((r) => r.p.vol === 'off').map((r) => r.gpRegret)).toFixed(1)} | ${Math.max(...rows.filter((r) => r.p.vol === 'on').map((r) => r.gpRegret)).toFixed(1)}`);
  console.log(`  S3 − best θ (corr, unbalanced) ${mean('off', (r) => r.outU.corr - r.thetaBest).toFixed(2)} | ${mean('on', (r) => r.outU.corr - r.thetaBest).toFixed(2)}; max ${Math.max(...rows.filter((r) => r.p.vol === 'off').map((r) => r.outU.corr - r.thetaBest)).toFixed(1)} | ${Math.max(...rows.filter((r) => r.p.vol === 'on').map((r) => r.outU.corr - r.thetaBest)).toFixed(1)}`);
  console.log(`  Σ̂ not PSD ${mean('off', (r) => r.np).toFixed(3)} | ${mean('on', (r) => r.np).toFixed(3)} (T ≥ 5 here; T = 3 in S78)`);
  // ranking: does the best fit (and the order vc vs blup vs bs) change between off and the on worlds with the same T, ρ, σ spread?
  console.log('\nBest fit per world, balanced/unbalanced (off → on seed 1, on seed 2):');
  for (const r of rows.filter((x) => x.p.vol === 'off')) {
    const key = (x) => x.p.T === r.p.T && x.p.rho === r.p.rho && x.p.noiseSpread === r.p.noiseSpread;
    const best = (x) => IDS.reduce((a, b) => (x.out[a] <= x.out[b] ? a : b)) + '/' + IDS.reduce((a, b) => (x.outU[a] <= x.outU[b] ? a : b));
    const on = rows.filter((x) => x.p.vol === 'on' && key(x));
    console.log(`  T ${r.p.T} ρ ${r.p.rho} σsp ${r.p.noiseSpread}: ${best(r)} → ${on.map(best).join(', ')}`);
  }
});
