// Temporal decay (studies/PLAN-done.md; literature §10l, Morris 2026): an EWMA weighting of
// each cohort's own years, λ fitted, against the BLUP in the monthly card world (app/monthly.js:
// AR(1) factor φ per month, shock C, process noise s²/w, cohort × calendar-month season fixed).
// EWMA at a fixed λ is a predictor from aggregated data (own annual means), so its excess over the
// BLUP is exact (Blup.predMse_aggregate_eq_blup_add). "own years" is the best predictor from the
// same annual means (no hyperparameter); EWMA is a one-parameter family inside it.
// Run: node studies/runs/ewma-decay.js [draws]
'use strict';
const M = require('../../app/monthly.js');
const N = +(process.argv[2] || 200);
const pct = (a, b) => (100 * a / b).toFixed(0).padStart(4);
const tabOf = (t) => ({ phi: t.phi, A: t.A, C: t.C, s2: t.s2 });
const sum = (a) => a.reduce((s, x) => s + x, 0);

// ---- Part A: exact, true tables. Equal loadings so that cohorts differ by volume (w0·(1+j)) and s² only.
console.log('Part A (exact, true tables): J = 4, Y = 5, loadings equal; cohort j has volume w0·(1+j), s² ×1.5 for j odd.');
console.log('MSE in % of the BLUP. λ* = oracle EWMA λ. "BLUP last yr" = share of the BLUP\'s own-cohort weight on the last year');
console.log('(own weights per calendar month sum to 1/12 over years; other cohorts\' weights sum to 0 per month).');
console.log('φ     w0    | cohort | λ*   | EWMA λ* | own years | last yr | equal yrs | own-years c (oldest→last)      | BLUP own-yr shares');
for (const phi of [0.6, 0.9, 0.97]) for (const w0 of [100, 1000, 10000]) {
  const wd = M.makeWorld({ Y: 5, phi, w0, loadSpread: 0 }), tab = tabOf(wd.truth);
  const mom = M.targetMoments(wd.J, wd.w, tab, wd.wFuture), P = M.predictor(wd.J, wd.Y, wd.w, tab, wd.wFuture);
  const ew = M.ewmaYears(wd.J, wd.w, tab, wd.wFuture), ob = M.ownYearsBest(wd.J, wd.w, tab, wd.wFuture);
  for (let j = 0; j < wd.J; j++) {
    const ym = M.yearMoments(mom, j), b = P.mse[j];
    const at = (lam) => { const c = M.ewmaWeights(5, lam); let q = 0, l = 0; for (let y = 0; y < 5; y++) { l += c[y] * ym.la[y]; for (let z = 0; z < 5; z++) q += c[y] * ym.Ka[y][z] * c[z]; } return q - 2 * l + ym.v; };
    const own = Array.from({ length: 5 }, (_, y) => 12 * sum(P.weights[j].slice(j * 60 + 12 * y, j * 60 + 12 * y + 12)) / 12);
    console.log(`${phi.toFixed(2)}  ${String(w0).padEnd(5)} |   ${j + 1}    | ${ew[j].lam.toFixed(2)} |  ${pct(ew[j].mse, b)}   |   ${pct(ob[j].mse, b)}    |  ${pct(at(0), b)}   |   ${pct(at(1), b)}    | ${ob[j].c.map((x) => x.toFixed(2).padStart(5)).join(' ')} | ${own.map((x) => x.toFixed(2).padStart(5)).join(' ')}`);
  }
}

// ---- Part B: fitted (no truth), simulated. Each draw: fit φ̂ by year-on-year, valid MINQUE tables
// (as the app's rolling origin), then the plug-in BLUP, EWMA with λ̂ by the plug-in criterion, the
// plug-in own-years predictor, and the last-12-month mean. Realized squared error against the
// 12-month target, summed over cohorts, in % of the oracle BLUP's exact MSE.
console.log(`\nPart B (fitted, ${N} draws per world): realized MSE in % of the oracle BLUP's exact MSE (sum over cohorts).`);
console.log('world                         | oracle | BLUP plug-in | EWMA λ̂ | own years | last yr | λ̂ mean per cohort (λ*)            | fallbacks');
const worlds = [
  { Y: 5, phi: 0.9, w0: 1000, loadSpread: 0 },
  { Y: 5, phi: 0.97, w0: 1000, loadSpread: 0 },
  { Y: 5, phi: 0.97, w0: 100, loadSpread: 0 },
  { Y: 5, phi: 0.6, w0: 1000, loadSpread: 0 },
  { Y: 5, phi: 0.9, w0: 1000 },
  { Y: 3, phi: 0.97, w0: 1000, loadSpread: 0 },
];
for (const par of worlds) {
  const wd = M.makeWorld(par), tab = tabOf(wd.truth), r = M.rng(7);
  const P0 = M.predictor(wd.J, wd.Y, wd.w, tab, wd.wFuture), floor = sum(P0.mse);
  const lamStar = M.ewmaYears(wd.J, wd.w, tab, wd.wFuture).map((e) => e.lam);
  const se = { oracle: 0, blup: 0, ewma: 0, own: 0, last: 0 }, lamSum = new Array(wd.J).fill(0);
  let fb = 0;
  for (let k = 0; k < N; k++) {
    const { data, target } = M.drawFuture(wd, r), last = M.lastYear(data);
    const add = (key, pred) => { se[key] += sum(pred.map((x, j) => (x - target[j]) ** 2)); };
    add('oracle', P0.predict(data.X));
    add('last', last);
    const f = M.fit(data, { phiMethod: 'moment', psd: true });
    const ft = f.singular ? null : { phi: f.phi, A: f.A, C: f.C, s2: f.s2 };
    const P = ft && !M.degenerateTable(ft) ? M.predictor(data.J, data.Y, data.w, ft) : null;
    if (!P) { fb++; add('blup', last); add('ewma', last); add('own', last); continue; }
    add('blup', P.predict(data.X));
    const ew = M.ewmaYears(data.J, data.w, ft), ob = M.ownYearsBest(data.J, data.w, ft);
    const means = Array.from({ length: data.J }, (_, j) => M.annualMeans(data, j));
    add('ewma', ew.map((e, j) => sum(e.c.map((c, y) => c * means[j][y]))));
    add('own', ob.map((e, j) => sum(e.c.map((c, y) => c * means[j][y]))));
    ew.forEach((e, j) => { lamSum[j] += e.lam; });
  }
  const name = `φ=${par.phi} w0=${par.w0} Y=${par.Y}${par.loadSpread === 0 ? '' : ' loads 1±0.5'}`;
  const used = N - fb;
  console.log(`${name.padEnd(29)} |  ${pct(se.oracle / N, floor)}  |    ${pct(se.blup / N, floor)}      |  ${pct(se.ewma / N, floor)}  |   ${pct(se.own / N, floor)}    |  ${pct(se.last / N, floor)}   | ${lamSum.map((x, j) => `${(x / used).toFixed(2)}(${lamStar[j].toFixed(2)})`).join(' ')} | ${fb}`);
}
