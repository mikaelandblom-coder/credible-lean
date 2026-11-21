// Tests for app/monthly.js: the Lean results of FactorEstimation.lean (card-data Step 5), checked
// numerically, plus unbiasedness by simulation with a fixed seed. Run: node --test app/monthly.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const M = require('./monthly.js');

const close = (a, b, tol, msg) =>
  assert.ok(Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b)), `${msg}: ${a} vs ${b}`);

test('the table is symmetric and positive definite (Factor.K_posDef)', () => {
  for (const par of [{}, { J: 2, phi: 0.9 }, { volume: 'flat', Y: 3 }]) {
    const V = M.covTable(M.makeWorld(par));
    V.forEach((row, p) => row.forEach((x, q) => close(x, V[q][p], 1e-14, 'symmetric')));
    assert.ok(M.cholesky(V), 'positive definite');
  }
});

test('Two years, AR(1), seasonal volumes: MINQUE is nonsingular (Factor.minque_ar1_two_years_det_ne_zero)', () => {
  const r = M.rng(1);
  for (const par of [{}, { J: 2 }, { J: 5, phi: 0.3 }]) {
    const w = M.makeWorld(par), mq = M.minque(M.draw(w, r), w.truth.phi);
    assert.ok(!mq.singular, `nonsingular, cond ${mq.cond}`);
  }
});

test('Finding 29: with two years, volumes flat over the calendar make MINQUE singular', () => {
  const r = M.rng(2);
  for (const volume of ['yearOnly', 'flat']) {
    const w = M.makeWorld({ volume }), d = M.draw(w, r);
    assert.ok(M.minque(d, 0.6).singular, `${volume}: singular (Factor.minque_cohortSeason_det_eq_zero_of_volume)`);
    const codes = M.fit(d, { phi: 0.6 }).warnings.map((x) => x.code);
    assert.ok(codes.includes('flatVolume') && codes.includes('singular'), `${volume}: warned`);
  }
  // Three years: the collapse is special to two (argued in Finding 29, not formalized).
  assert.ok(!M.minque(M.draw(M.makeWorld({ Y: 3, volume: 'yearOnly' }), r), 0.6).singular, 'three years: nonsingular');
});

test('Finding 28: one year, or φ ∈ {0, 1}, is singular', () => {
  const r = M.rng(3), w = M.makeWorld({}), d = M.draw(w, r);
  assert.ok(M.minque(M.draw(M.makeWorld({ Y: 1 }), r), 0.6).singular, 'one year (Factor.unbiasedMean_cohortSeason_eq_zero)');
  assert.ok(M.minque(d, 0).singular, 'φ = 0: A against C (Factor.hendersonMat_shape_one_det_eq_zero)');
  assert.ok(M.minque(d, 1).singular, 'φ = 1: the factor repeats with the calendar (Factor.hendersonMat_cohortSeason_det_eq_zero_of_shape)');
});

test('the centring R annihilates the cohort season (Model.minqueR_mul)', () => {
  // Data equal to a pure season give zero forms: q = 0.
  const w = M.makeWorld({ J: 3 }), d = { J: 3, Y: 2, w: w.w, X: w.w.map((row, j) => row.map((_, t) => 5 + j + Math.sin(t % 12))) };
  M.minque(d, 0.6).q.forEach((x) => close(x, 0, 1e-12, 'q'));
});

test('MINQUE given φ is unbiased for γλλᵀ, C, s², whatever τ² and the season (Factor.minque_ar1_two_years_unbiased)', () => {
  const w = M.makeWorld({ J: 3, tau2: 0.05 }), r = M.rng(4), N = 500;
  const pick = [['A', 0, 1], ['A', 2, 2], ['C', 0, 1], ['C', 1, 1], ['s', 0], ['s', 2]];
  const truth = (k) => (k[0] === 's' ? w.truth.s2[k[1]] : w.truth[k[0]][k[1]][k[2]]);
  const est = (f, k) => (k[0] === 's' ? f.s2[k[1]] : f[k[0]][k[1]][k[2]]);
  const s = pick.map(() => 0), ss = pick.map(() => 0);
  for (let n = 0; n < N; n++) {
    const f = M.fit(M.draw(w, r), { phi: w.truth.phi });
    pick.forEach((k, i) => { const x = est(f, k); s[i] += x; ss[i] += x * x; });
  }
  pick.forEach((k, i) => {
    const mean = s[i] / N, se = Math.sqrt((ss[i] / N - mean * mean) / N);
    assert.ok(Math.abs(mean - truth(k)) < 4 * se, `${k.join('')}: mean ${mean}, truth ${truth(k)}, se ${se}`);
  });
});

test('the year-on-year cross-products are unbiased for λᵢλⱼγ·g(φ, h) (Factor.yoy_unbiased_factor)', () => {
  const w = M.makeWorld({ J: 3 }), r = M.rng(5), N = 800, h = 1;
  const { load, gamma, phi } = w.truth;
  let pairs = 0, c = 0;
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) if (i !== j) { c += load[i] * load[j] * gamma; pairs++; }
  const target = (c / pairs) * M.yoyShape(phi, h);
  let s = 0, ss = 0;
  for (let n = 0; n < N; n++) { const x = M.yoyPooled(M.draw(w, r), h); s += x; ss += x * x; }
  const mean = s / N, se = Math.sqrt((ss / N - mean * mean) / N);
  assert.ok(Math.abs(mean - target) < 4 * se, `mean ${mean}, target ${target}, se ${se}`);
});

test('the fit gets the data table and nothing else', () => {
  const w = M.makeWorld({}), d = M.draw(w, M.rng(6));
  assert.deepEqual(Object.keys(d).sort(), ['J', 'X', 'Y', 'w']);
  const f = M.fit(d);
  assert.ok(f.phi > 0 && f.phi < 1, 'φ̂ in (0, 1)');
  assert.ok(f.steps.some((x) => x.badge === 'proved') && f.steps.some((x) => x.badge === 'not proved yet'), 'badges');
});

test('every proved step and every warning names a proved Lean declaration', () => {
  const { execFileSync } = require('node:child_process'), path = require('node:path');
  const proved = new Set(execFileSync('python3', [path.join(__dirname, '..', 'scripts', 'progress.py'), '--proved'],
    { encoding: 'utf8' }).split('\n').filter(Boolean));
  const r = M.rng(7), names = [];
  for (const par of [{}, { volume: 'flat' }, { Y: 1 }]) {
    const f = M.fit(M.draw(M.makeWorld(par), r), { phi: par.Y === 1 ? 0.99 : undefined });
    f.steps.filter((s) => s.badge === 'proved').forEach((s) => names.push(s.lean));
    f.warnings.forEach((x) => names.push(x.lean));
  }
  names.forEach((n) => assert.ok(proved.has('Credibility.' + n), `${n} is proved`));
});

test('the Kronecker MINQUE equals the dense one', () => {
  const r = M.rng(8);
  for (const par of [{}, { J: 3, Y: 3, volume: 'yearOnly' }]) {
    const w = M.makeWorld(par), d = M.draw(w, r), a = M.minqueDense(d, 0.55), b = M.minque(d, 0.55);
    a.H.forEach((row, k) => row.forEach((x, l) => close(b.H[k][l], x, 1e-10, `H ${k} ${l}`)));
    a.q.forEach((x, k) => close(b.q[k], x, 1e-10, `q ${k}`));
    assert.equal(a.singular, b.singular);
  }
});

test('the profile φ̂ maximises the explained share and recovers φ when the factor is strong', () => {
  const w = M.makeWorld({ J: 4, Y: 4, gamma: 0.1, s2: 4, c: 0.002 }), r = M.rng(9), est = [];
  for (let n = 0; n < 30; n++) {
    const p = M.phiProfile(M.draw(w, r));
    p.curve.filter((c) => Number.isFinite(c.share)).forEach((c) => assert.ok(c.share <= p.share + 1e-12, 'max of the curve'));
    est.push(p.phi);
  }
  est.sort((a, b) => a - b);
  assert.ok(Math.abs(est[15] - w.truth.phi) < 0.1, `median ${est[15]}`);
});

test('toCSV writes the data the fit sees, one row per cohort and month', () => {
  const w = M.makeWorld({ J: 2, Y: 2 }), d = M.draw(w, M.rng(10)), lines = M.toCSV(d).trim().split('\n');
  assert.equal(lines[0], 'cohort,year,month,volume,ratio');
  assert.equal(lines.length, 1 + 2 * 24);
  const [j, y, m, v, x] = lines[30].split(',').map(Number), t = 12 * (y - 1) + m - 1;
  assert.ok(Math.abs(v - d.w[j - 1][t]) < 1e-6 * v && Math.abs(x - d.X[j - 1][t]) < 1e-9, 'values round-trip');
});

test('fit: profile by default, moment on request, oracle φ when given; one year is singular', () => {
  const d = M.draw(M.makeWorld({}), M.rng(11));
  assert.equal(M.fit(d).phiMethod, 'profile');
  assert.equal(M.fit(d, { phiMethod: 'moment' }).phi, M.phiHat(d).phi);
  assert.equal(M.fit(d, { phi: 0.6 }).phi, 0.6);
  const f1 = M.fit(M.draw(M.makeWorld({ Y: 1 }), M.rng(12)));
  assert.ok(f1.singular && f1.warnings.some((x) => x.code === 'oneYear'));
});
