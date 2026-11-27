// S72. Purpose: decide (owner: which fit the app recommends; PLAN Pending, "Gain against price").
// Candidates: corrBS (today's recommendation), corrBS g/p (variances by gain against price, S57), the BLUP on
// corrBS's K̂ (S52), and the new combination "BLUP g/p": the BLUP on the K̂ that g/p's verdict picks
// (region variances, or one pooled σ̂², i.e. BLUP or BLUP pooled). The verdict is computed for the blend
// (Engine.gainPrice); here it is reused for the BLUP, the open question being whether that transfers.
// Worlds: S52's and S57's grids merged: regime app / thesis (σⱼ spread 0, 1, 2) and thesisShape (spread 2),
// ρ ∈ {0, 0.3, 0.6, 0.9}, T ∈ {5, 10}; J = 8, gamma noise (the app's default). Common random numbers.
// Scored with the balance switch on (cross-fitted level, the page's default), as the app prices: exposure-
// weighted MSE of the rates in % of the blend floor (true K); paired differences ± 2 SE.
// Also the Finding 35 channel: the portfolio bias of each fit before balancing (exposure-weighted mean of
// rate − level, in basis points of the tariff), which the balance switch removes.
// Run: node studies/runs/recommended-fit.js [draws] [--jobs=k]
'use strict';
const E = require('../../app/engine.js');
const L = require('./lib.js');
const { N, jobs } = L.args({ N: 600 }); // 600 draws by default, as S52 and S57

const worlds = L.grid({ regime: ['app', 'thesis', 'thesisShape'], rho: [0, 0.3, 0.6, 0.9], noiseSpread: [0, 1, 2], T: [5, 10] })
  .filter((p) => p.regime !== 'thesisShape' || p.noiseSpread === 2);
const IDS = ['vc', 'vcGP', 'blup', 'blupGP', 'ho'];
const NAMES = { vc: 'corrBS', vcGP: 'corrBS g/p', blup: 'BLUP', blupGP: 'BLUP g/p', ho: 'held-out' };

function runWorld(p) {
  const world = E.makeWorld(Object.assign({ rho: p.rho, T: p.T, noiseSpread: p.noiseSpread }, L.regimes[p.regime]));
  const fl = E.floorBlend(world), r = E.rng(2026), F = [];
  const S = Object.fromEntries(IDS.map((k) => [k, []])), B = Object.fromEntries(IDS.map((k) => [k, []])), U = Object.fromEntries(IDS.map((k) => [k, []]));
  let region = 0, pickBlup = 0;
  for (let k = 0; k < N; k++) {
    const { levels, data } = E.draw(world, r), wt = data.w.map(L.sum), wall = L.sum(wt);
    const se = (x) => E.weightedSE(data, x, levels), bias = (x) => 1e4 * L.sum(x.map((v, j) => wt[j] * (v - levels[j]))) / wall;
    F.push(se(fl.apply(data).rates));
    const g = E.gainPrice(data), pooled = !!g && g.verdict === 'pooled';
    if (!pooled) region++;
    const vc = E.fitVC(data), vcP = pooled ? E.fitVC(data, { pooled: true }) : vc;
    const blup = E.fitBLUP(data), blupP = pooled ? E.fitBLUP(data, { pooled: true }) : blup;
    // held-out: BLUP or corrBS by leave-one-year-out loss of the balanced fits (CrossFit.integral_heldOutScore_sub:
    // the difference of the scores is unbiased for the difference of their errors from T − 1 years)
    const bal = (fn) => (d) => E.balanceFit(fn(d), d, { target: 'crossFit' });
    const useBlup = E.loyoLoss(data, bal(E.fitBLUP)) < E.loyoLoss(data, bal(E.fitVC));
    if (useBlup) pickBlup++;
    const raw = { vc, vcGP: vcP, blup, blupGP: blupP, ho: useBlup ? blup : vc };
    for (const id of IDS) {
      B[id].push(bias(raw[id].rates)); U[id].push(se(raw[id].rates));
      S[id].push(se(E.balanceFit(raw[id], data, { target: 'crossFit' }).rates));
    }
  }
  const f = L.meanSE(F).m;
  return {
    p, f, zr: [Math.min(...fl.z), Math.max(...fl.z)], region: region / N, pickBlup: pickBlup / N,
    rel: Object.fromEntries(IDS.map((id) => [id, L.meanSE(S[id]).m / f])),
    d: Object.fromEntries(IDS.filter((id) => id !== 'vc').map((id) => [id, L.paired(S[id], S.vc)])),
    dBB: L.paired(S.blupGP, S.blup), dHB: L.paired(S.ho, S.blup), dHbest: L.paired(S.ho, L.meanSE(S.vc).m <= L.meanSE(S.blup).m ? S.vc : S.blup), dU: L.paired(U.blup, U.vc), relU: Object.fromEntries(IDS.map((id) => [id, L.meanSE(U[id]).m / f])),
    bias: Object.fromEntries(IDS.map((id) => [id, L.meanSE(B[id])])),
  };
}

L.mapWorlds(__filename, worlds, runWorld, jobs).then((rows) => {
  console.log(`J = 8, gamma noise, ${N} draws per world, balance switch on (cross-fitted level). MSE in % of the blend floor;`);
  console.log('Δ = fit − corrBS and BLUP g/p − BLUP, paired ± 2 SE (negative = better). Region: share of draws where g/p keeps region variances;');
  console.log('BLUP picked: share of draws where the held-out score prefers the BLUP.');
  console.log('world                          | z range   | corrBS | g/p | BLUP | BLUP g/p | held-out | region | BLUP picked | Δ g/p        | Δ BLUP        | Δ BLUP g/p    | Δ held-out');
  for (const r of rows) {
    const p = r.p, rel = (id) => (100 * r.rel[id]).toFixed(0).padStart(4), pm = (d) => L.pm(d, 100 / r.f).padEnd(13);
    const name = `${p.regime} ρ=${p.rho} σⱼ×${p.noiseSpread} T=${p.T}`;
    console.log(`${name.padEnd(30)} | ${r.zr[0].toFixed(2)}–${r.zr[1].toFixed(2)} |  ${rel('vc')}  | ${rel('vcGP')} | ${rel('blup')} |   ${rel('blupGP')}   |   ${rel('ho')}   |  ${(100 * r.region).toFixed(0).padStart(3)}%  |    ${(100 * r.pickBlup).toFixed(0).padStart(3)}%     | ${pm(r.d.vcGP)} | ${pm(r.d.blup)} | ${pm(r.d.blupGP)} | ${L.pm(r.d.ho, 100 / r.f)}`);
  }
  const tally = (get, sel) => {
    const rs = rows.filter(sel || (() => true));
    let w = 0, b = 0;
    const pts = rs.map((r) => { const d = get(r), g = L.sig(d, 1e-9 * r.f); if (g > 0) w++; else if (g < 0) b++; return 100 * d.m / r.f; });
    return `worse in ${w}, better in ${b}, even in ${rs.length - w - b} of ${rs.length}; mean ${(L.sum(pts) / pts.length).toFixed(1)}, range ${Math.min(...pts).toFixed(1)} to ${Math.max(...pts).toFixed(1)} points of the floor`;
  };
  console.log('\nSummary (paired):');
  for (const id of ['vcGP', 'blup', 'blupGP', 'ho']) console.log(`  ${(NAMES[id] + ' − corrBS:').padEnd(22)} ${tally((r) => r.d[id])}`);
  console.log(`  ${'BLUP g/p − BLUP:'.padEnd(22)} ${tally((r) => r.dBB)}`);
  console.log(`  ${'held-out − BLUP:'.padEnd(22)} ${tally((r) => r.dHB)}`);
  console.log(`  ${'held-out − better of corrBS and BLUP in that world (regret):'} ${tally((r) => r.dHbest)}`);
  for (const sp of [0, 1, 2]) console.log(`  σⱼ×${sp}: held-out − corrBS ${tally((r) => r.d.ho, (r) => r.p.noiseSpread === sp)}`);
  for (const rho of [0, 0.3, 0.6, 0.9]) console.log(`  ρ = ${rho}: BLUP g/p − corrBS ${tally((r) => r.d.blupGP, (r) => r.p.rho === rho)}`);
  for (const sp of [0, 1, 2]) console.log(`  σⱼ×${sp}: BLUP − corrBS ${tally((r) => r.d.blup, (r) => r.p.noiseSpread === sp)}`);
  console.log(`  without balancing, BLUP − corrBS: ${tally((r) => r.dU)}`);
  console.log(`  without balancing, σⱼ×2: BLUP − corrBS ${tally((r) => r.dU, (r) => r.p.noiseSpread === 2)}`);
  const mean = (f, sel) => { const rs = rows.filter(sel || (() => true)); return L.sum(rs.map(f)) / rs.length; };
  console.log('\nBy subgrid (mean % of the floor: corrBS / g/p / BLUP / BLUP g/p / held-out):');
  const line = (sel) => IDS.map((id) => (100 * mean((r) => r.rel[id], sel)).toFixed(1)).join(' / ');
  console.log(`  all              ${line()}`);
  for (const [k, vals] of [['regime', ['app', 'thesis', 'thesisShape']], ['rho', [0, 0.3, 0.6, 0.9]], ['noiseSpread', [0, 1, 2]], ['T', [5, 10]]])
    for (const v of vals) console.log(`  ${(k + '=' + v).padEnd(16)} ${line((r) => r.p[k] === v)}`);
  console.log('\nPortfolio bias before balancing (Finding 35), basis points of the tariff, mean over worlds (most negative world):');
  for (const id of IDS) console.log(`  ${NAMES[id].padEnd(11)} ${mean((r) => r.bias[id].m).toFixed(0)} (${Math.min(...rows.map((r) => r.bias[id].m)).toFixed(0)})`);
});
