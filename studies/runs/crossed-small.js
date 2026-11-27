// S70: small crossed tables (paper, open directions: "Small crossed tables"). With two pairs per class
// (2×2) the pair pools are noisy, the raw α̂², β̂², γ̂² are often negative, and the default (inverse
// variance from an equal-weight pass, clipped at 0; studies/runs/crossed-fit.js) loses to the thesis fit
// when the effects are weak. Two fits with no settings against the default:
//  * reml: restricted maximum likelihood on the cell means μ̂ⱼ ~ N(μ1, Σ̂ + L(θ)), θ = (α², β², γ²) ≥ 0,
//    Σ̂ the default's noise table (corrBS). Projected Fisher scoring from the default's θ. A Gaussian
//    working likelihood: its estimating equations are quadratic in μ̂ and unbiased for any noise family
//    (Fung & Xu 2009 found ML/REML beat Dannenburg's moment estimators; studies/literature.md).
//  * shrink: each clipped variance times θ̂²/(θ̂² + V̂), V̂ = 2tr(AK̂AK̂) the normal-theory variance of
//    the raw estimate (a quadratic form μ̂ᵀAμ̂ with A1 = 0) on the default's K̂: the plug-in of the
//    MSE-best multiple cθ̂ of an unbiased θ̂, c = θ²/(θ² + Var θ̂). Shrinks most where Var exceeds θ².
// Also the thesis fit (one τ², no rows or columns) and the best blend with the true K.
// Entries: observed cells' summed squared error in % of the floor (full predictor, true K); paired
// differences against the default ± 2 SE. Common random numbers.
// Run: node studies/runs/crossed-small.js [draws]
'use strict';
const C = require('../../app/crossed.js');
const E = require('../../app/engine.js');
const L = require('./lib.js');
const N = +(process.argv[2] || 400);

const sum = L.sum, dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);
const inv = (A) => A.map((_, k) => E.solve(A, A.map((_, i) => (i === k ? 1 : 0)))); // columns = rows (A symmetric)
const mul = (A, B) => A.map((r) => B[0].map((_, j) => sum(r.map((x, k) => x * B[k][j]))));
const tr = (A) => sum(A.map((r, i) => r[i]));

/** P = K⁻¹ − K⁻¹11ᵀK⁻¹/1ᵀK⁻¹1, the REML projection. */
function projP(K) {
  const Ki = inv(K), u = Ki.map((r) => sum(r)), s = sum(u);
  return Ki.map((r, i) => r.map((x, j) => x - (u[i] * u[j]) / s));
}
const remlLik = (K, m) => {
  const n = m.length, Ki = inv(K), u = Ki.map((r) => sum(r)), s = sum(u);
  // log|K| by Cholesky
  const Lc = K.map((r) => r.map(() => 0));
  let ld = 0;
  for (let i = 0; i < n; i++) for (let j = 0; j <= i; j++) {
    let v = K[i][j];
    for (let k = 0; k < j; k++) v -= Lc[i][k] * Lc[j][k];
    if (i === j) { if (!(v > 0)) return -Infinity; Lc[i][i] = Math.sqrt(v); ld += 2 * Math.log(Lc[i][i]); } else Lc[i][j] = v / Lc[j][j];
  }
  const P = projP(K), Pm = P.map((r) => dot(r, m));
  return -0.5 * (ld + Math.log(s) + dot(m, Pm));
};

function reml(m, Sig, row, col, theta0) {
  const G = [0, 1, 2].map((k) => C.levelCov(row, col, k === 0 ? 1 : 0, k === 1 ? 1 : 0, k === 2 ? 1 : 0));
  const Kof = (th) => Sig.map((r, i) => r.map((x, j) => x + th[0] * G[0][i][j] + th[1] * G[1][i][j] + th[2] * G[2][i][j]));
  const scale = sum(Sig.map((r, i) => r[i])) / Sig.length;
  let th = theta0.map((x) => Math.max(x, 1e-3 * scale)), lik = remlLik(Kof(th), m);
  for (let it = 0; it < 50; it++) {
    const P = projP(Kof(th)), Pm = P.map((r) => dot(r, m));
    const PG = G.map((g) => mul(P, g));
    const score = G.map((g, k) => -0.5 * tr(PG[k]) + 0.5 * dot(Pm, g.map((r) => dot(r, Pm))));
    const I = PG.map((a) => PG.map((b) => 0.5 * tr(mul(a, b))));
    // only free coordinates: those > 0, or at 0 with a positive score
    const free = [0, 1, 2].filter((k) => th[k] > 0 || score[k] > 0);
    if (!free.length) break;
    let step;
    try { step = E.solve(free.map((a) => free.map((b) => I[a][b])), free.map((a) => score[a])); } catch (e) { break; }
    let t = 1, done = false;
    for (let h = 0; h < 30; h++, t /= 2) {
      const nt = th.slice();
      free.forEach((k, i) => { nt[k] = Math.max(0, th[k] + t * step[i]); });
      const nl = remlLik(Kof(nt), m);
      if (nl >= lik - 1e-12) { done = Math.abs(nl - lik) < 1e-10; th = nt; lik = nl; break; }
    }
    if (done) break;
  }
  return th;
}

/** Rates of every cell for given variances θ, on the default's noise table (as C.fit). */
function ratesWith(data, theta) {
  const { idx, sub, row, col } = C.observed(data), m = C.pairPools(data, 'equal').m;
  const Sig = E.vcEstimate(sub).Sig, Lv = C.levelCov(row, col, ...theta);
  const K = Sig.map((r, i) => r.map((x, j) => x + Lv[i][j]));
  const Pr = C.predictors(K, data.cells.map((c) => c.row), data.cells.map((c) => c.col), idx, ...theta);
  return Pr.cells.map((c) => dot(c.full, m));
}

/** The raw estimates as quadratic forms μ̂ᵀAₖμ̂ (minus noise terms): Aₖ from the default's pool weights. */
function shrinkTheta(data, f) {
  const pp = C.pairPools(data, 'equal'), { row, col, m } = pp, n = m.length;
  const Vn = E.vcEstimate(pp.sub).Sig, P0 = pp.P;
  const a = (k, i, j) => 1 / (Math.max(P0[k], 0) + Vn[i][i] + Vn[j][j] - 2 * Vn[i][j]) ** 2; // as C.pairPools 'iv'
  const D = { r: null, c: null, n: null }, tot = { r: 0, c: 0, n: 0 };
  for (const k of ['r', 'c', 'n']) D[k] = m.map(() => m.map(() => 0));
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    const k = C.pairClass(row, col, i, j);
    if (!k) continue;
    const w = a(k, i, j);
    tot[k] += w; D[k][i][i] += w; D[k][j][j] += w; D[k][i][j] -= w; D[k][j][i] -= w;
  }
  for (const k of ['r', 'c', 'n']) D[k] = D[k].map((r) => r.map((x) => x / tot[k]));
  const comb = (cr, cc, cn) => D.r.map((r, i) => r.map((_, j) => (cr * D.r[i][j] + cc * D.c[i][j] + cn * D.n[i][j]) / 2));
  const A = [comb(-1, 0, 1), comb(0, -1, 1), comb(1, 1, -1)];
  return f.theta.map((th, k) => { const AK = mul(A[k], f.K), V = 2 * tr(mul(AK, AK)); return th > 0 ? th * th * th / (th * th + V) : 0; });
}

const mixes = { // (α, β, γ)
  both: [0.06, 0.10, 0.04],
  rowOnly: [0.10, 0, 0.04],
  weak: [0.02, 0.03, 0.02],
  none: [0, 0, 0],
};
const worlds = L.grid({ table: ['2x2', '3x2', '3x3', '4x3'], mix: Object.keys(mixes), rho: [0, 0.5], spread: [0, 1], regime: ['app', 'thesis'] });
const ids = ['default', 'reml', 'shrink', 'thesis', 'floorBlend'];
console.log(`draws per world: ${N}; observed cells' summed squared error in % of the floor; differences vs the default ± 2 SE`);
console.log('world                              | default | reml | shrink | thesis | best blend | reml − default | shrink − default | P(raw<0) α β γ');
const rows = [];
for (const p of worlds) {
  const [nr, nc] = p.table.split('x').map(Number), [alpha, beta, gamma] = mixes[p.mix];
  const world = C.makeWorld(Object.assign({ nr, nc, alpha, beta, gamma, rho: p.rho, spread: p.spread }, L.regimes[p.regime]));
  const ex = C.exact(world), r = E.rng(2026);
  const err = Object.fromEntries(ids.concat(['floor']).map((id) => [id, []])), neg = [0, 0, 0];
  for (let s = 0; s < N; s++) {
    const { levels, data } = C.draw(world, r);
    const { idx } = C.observed(data);
    const score = (id, rates) => err[id].push(sum(idx.map((j) => (rates[j] - levels[j]) ** 2)));
    const f = C.fit(data, { method: 'pools' }); // the pools default of S70's time (C.fit now defaults to REML)
    f.raw.forEach((x, k) => { if (x < 0) neg[k]++; });
    score('floor', ex.cells.map((c) => dot(c.full, f.m)));
    score('floorBlend', ex.cells.map((c) => dot(c.blend, f.m)));
    score('thesis', C.thesisFit(data).rates);
    score('default', f.rates);
    const { sub, row, col } = C.observed(data);
    score('reml', ratesWith(data, reml(f.m, E.vcEstimate(sub).Sig, row, col, f.theta)));
    score('shrink', ratesWith(data, shrinkTheta(data, f)));
  }
  const fl = L.meanSE(err.floor).m, rel = (id) => L.meanSE(err[id]).m / fl;
  const dR = L.paired(err.reml, err.default), dS = L.paired(err.shrink, err.default), dT = L.paired(err.thesis, err.default);
  const name = `${p.table} ${p.mix.padEnd(7)} ρ=${p.rho} spread=${p.spread} ${p.regime}`;
  console.log(`${name.padEnd(34)} | ${ids.map((id) => (100 * rel(id)).toFixed(0).padStart(5)).join('   | ')} | ${L.pm(dR, 100 / fl).padEnd(14)} | ${L.pm(dS, 100 / fl).padEnd(16)} | ${neg.map((x) => (x / N).toFixed(2)).join(' ')}`);
  rows.push({ p, fl, dR, dS, dT, rel: Object.fromEntries(ids.map((id) => [id, rel(id)])) });
}

const sig = (d) => (d.m - 2 * d.se > 0 ? 1 : d.m + 2 * d.se < 0 ? -1 : 0);
const summary = (key, sel) => {
  const rs = rows.filter(sel || (() => true));
  let worse = 0, better = 0;
  for (const r of rs) { const g = sig(r[key]); if (g > 0) worse++; else if (g < 0) better++; }
  const pts = rs.map((r) => 100 * r[key].m / r.fl);
  return `worse in ${worse}, better in ${better}, even in ${rs.length - worse - better} of ${rs.length}; mean ${(sum(pts) / pts.length).toFixed(1)}, range ${Math.min(...pts).toFixed(1)} to ${Math.max(...pts).toFixed(1)} points of the floor`;
};
console.log('\nSummary (paired, against the default):');
console.log(`  reml:   ${summary('dR')}`);
console.log(`  shrink: ${summary('dS')}`);
console.log(`  thesis: ${summary('dT')}`);
for (const t of ['2x2', '3x2', '3x3', '4x3']) {
  console.log(`  ${t}: reml ${summary('dR', (r) => r.p.table === t)}`);
  console.log(`  ${t}: shrink ${summary('dS', (r) => r.p.table === t)}`);
}
const mean = (f, sel) => { const rs = rows.filter(sel || (() => true)); return sum(rs.map(f)) / rs.length; };
console.log('\nBy subgrid (mean % of the floor: default / reml / shrink / thesis / best blend):');
const line = (sel) => ids.map((id) => (100 * mean((r) => r.rel[id], sel)).toFixed(1)).join(' / ');
console.log(`  all              ${line()}`);
for (const [k, vals] of [['table', ['2x2', '3x2', '3x3', '4x3']], ['mix', Object.keys(mixes)], ['rho', [0, 0.5]], ['spread', [0, 1]], ['regime', ['app', 'thesis']]])
  for (const v of vals) console.log(`  ${(k + '=' + v).padEnd(16)} ${line((r) => r.p[k] === v)}`);
