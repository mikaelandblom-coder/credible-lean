// Decide (studies/PLAN.md, Pending: crossed): the crossed fit's pair weights and its truncation at 0.
// Pair weights per class: equal, ∝ wᵢ*wⱼ* (Dannenburg's volume weights, with the full noise
// correction), or inverse variance 1/(E(μ̂ᵢ − μ̂ⱼ)²)² from a first equal-weight pass (no settings); truncation: clip each variance at 0 (Euclidean projection) or least squares on the
// three pool equations with θ ≥ 0 (projection in their metric). Both are unbiased before truncation
// (Model.crossed_unbiasedX) and both projections are never further from the truth in their own
// metric (ConeProjection.hsq_proj_le), so only the rates' error can decide.
// Also: the ANOVA statistics (volume weights, noise cross term omitted, Finding 42), the thesis fit
// (corrBS: no rows or columns) and the best blend with the true K (the floor of the blend form).
// Full factorial: table × effect mix × ρ × volume spread × regime; common random numbers.
// Entries: summed squared error of the observed cells' rates in % of the floor (the full predictor
// with the true K); differences ± 2 SE, paired.
// Run: node studies/crossed-fit.js [draws]
'use strict';
const C = require('../app/crossed.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 400);

const mixes = { // (α, β, γ): spreads of the row, column and cell effects
  both: [0.06, 0.10, 0.04],
  rowOnly: [0.10, 0, 0.04],   // β² = 0: Bridge 4 (rows as groups); truncation matters for β̂²
  noCell: [0.06, 0.10, 0],    // γ² = 0: the additive table; truncation matters for γ̂²
  weak: [0.02, 0.03, 0.02],   // little signal: every variance often negative
};
const worlds = L.grid({ table: ['3x2', '4x3', '6x4'], mix: Object.keys(mixes), rho: [0, 0.5], spread: [0, 1], regime: ['app', 'thesis'] });
const ids = C.VARIANTS.map((v) => v.id);
console.log(`draws per world: ${N}; observed cells' summed squared error in % of the floor; differences vs equal-clip ± 2 SE`);
console.log('world                              | eq-clip | eq-nnls | vol-clip | vol-nnls | iv-clip | anova | thesis | best blend | eq-nnls − eq-clip | vol-clip − eq-clip');
const rows = [];
for (const p of worlds) {
  const [nr, nc] = p.table.split('x').map(Number), [alpha, beta, gamma] = mixes[p.mix];
  const world = C.makeWorld(Object.assign({ nr, nc, alpha, beta, gamma, rho: p.rho, spread: p.spread }, L.regimes[p.regime]));
  const s = C.simulate(world, N, 2026);
  const f = L.meanSE(s.obs.floor).m, rel = (id) => (100 * L.meanSE(s.obs[id]).m / f).toFixed(0).padStart(5);
  const dN = L.paired(s.obs['equal-nnls'], s.obs['equal-clip']), dV = L.paired(s.obs['vol-clip'], s.obs['equal-clip']);
  const dVN = L.paired(s.obs['vol-nnls'], s.obs['equal-clip']), dI = L.paired(s.obs['iv-clip'], s.obs['equal-clip']), dIV = L.paired(s.obs['iv-clip'], s.obs['vol-clip']);
  const name = `${p.table} ${p.mix.padEnd(7)} ρ=${p.rho} spread=${p.spread} ${p.regime}`;
  console.log(`${name.padEnd(34)} | ${ids.map(rel).join('   | ')}  | ${rel('thesis')}  |  ${rel('floorBlend')}     | ${L.pm(dN, 100 / f).padEnd(17)} | ${L.pm(dV, 100 / f)}`);
  // variance errors: RMSE of (α̂², β̂², γ̂²) after truncation, relative to τ² = α² + β² + γ²
  const tau2 = alpha ** 2 + beta ** 2 + gamma ** 2;
  const rm = (id) => Math.sqrt(L.meanSE(s.used[id].map((e) => L.sum(e.map((x) => x * x)))).m) / tau2;
  const bias = (id, k) => L.meanSE(s.raw[id].map((e) => e[k])).m / tau2;
  rows.push({ p, f, dN, dV, dVN, dI, dIV, rel: Object.fromEntries(ids.concat(['thesis', 'floorBlend']).map((id) => [id, L.meanSE(s.obs[id]).m / f])),
    rmse: Object.fromEntries(ids.map((id) => [id, rm(id)])), biasG: Object.fromEntries(ids.map((id) => [id, bias(id, 2)])) });
}

// summary over the grid
const sig = (d, f) => (d.m - 2 * d.se > 0 ? 1 : d.m + 2 * d.se < 0 ? -1 : 0);
const summary = (key) => {
  let worse = 0, better = 0;
  for (const r of rows) { const g = sig(r[key], r.f); if (g > 0) worse++; else if (g < 0) better++; }
  const pts = rows.map((r) => 100 * r[key].m / r.f);
  return `worse in ${worse}, better in ${better}, even in ${rows.length - worse - better} of ${rows.length} worlds; mean ${(L.sum(pts) / pts.length).toFixed(1)}, range ${Math.min(...pts).toFixed(1)} to ${Math.max(...pts).toFixed(1)} points of the floor`;
};
console.log('\nSummary (paired, against equal weights + clip):');
console.log(`  equal + least squares: ${summary('dN')}`);
console.log(`  volume + clip:         ${summary('dV')}`);
console.log(`  volume + least sq.:    ${summary('dVN')}`);
console.log(`  inverse var. + clip:   ${summary('dI')}`);
console.log(`  inverse var. vs volume + clip: ${summary('dIV')}`);
const mean = (f) => L.sum(rows.map(f)) / rows.length;
console.log('\nMean over the grid, % of the floor:');
for (const id of ids.concat(['thesis', 'floorBlend'])) console.log(`  ${id.padEnd(11)} ${(100 * mean((r) => r.rel[id])).toFixed(1)}`);
console.log('\nBy subgrid (mean % of the floor: eq-clip / vol-clip / iv-clip / anova / thesis / best blend):');
for (const [axis, vals] of [['spread', [0, 1]], ['rho', [0, 0.5]], ['mix', Object.keys(mixes)], ['table', ['3x2', '4x3', '6x4']], ['regime', ['app', 'thesis']]]) {
  for (const v of vals) {
    const sub = rows.filter((r) => r.p[axis] === v), m = (id) => (100 * L.sum(sub.map((r) => r.rel[id])) / sub.length).toFixed(1);
    console.log(`  ${axis}=${v}`.padEnd(18) + ` ${m('equal-clip')} / ${m('vol-clip')} / ${m('iv-clip')} / ${m('anova-clip')} / ${m('thesis')} / ${m('floorBlend')}`);
  }
}
console.log('\nγ̂² bias before truncation, in % of τ², at ρ = 0.5 (mean over those worlds): ' +
  ids.map((id) => `${id} ${(100 * L.sum(rows.filter((r) => r.p.rho === 0.5).map((r) => r.biasG[id])) / rows.filter((r) => r.p.rho === 0.5).length).toFixed(1)}`).join(', '));
console.log('Variance RMSE after truncation, in % of τ² (mean over the grid): ' + ids.map((id) => `${id} ${(100 * mean((r) => r.rmse[id])).toFixed(0)}`).join(', '));
