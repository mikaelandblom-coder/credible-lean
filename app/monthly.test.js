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

test('the drawn cells have the table covariance, and the index follows the same factor path', () => {
  const w = M.makeWorld({ J: 2, Y: 2, indexYears: 1, indexNoise: 0.5 }), V = M.covTable(w), r = M.rng(13), N = 4000, T = 24;
  // cells (cohort 0, month 3) with (cohort 1, month 4), (0, 5) with itself; index month 12 + 4 with cell (1, 4)
  const pairs = [[0 * T + 3, 1 * T + 4], [5, 5]], sx = pairs.map(() => [0, 0, 0]);
  const lam = w.truth.load[1], target = lam * w.truth.gamma; // cov(I at data month 4, X(1, 4)) = λ₁γ
  let a = 0, b = 0, ab = 0;
  for (let n = 0; n < N; n++) {
    const d = M.draw(w, r), x = d.X.flat();
    pairs.forEach(([p, q], k) => { sx[k][0] += x[p]; sx[k][1] += x[q]; sx[k][2] += x[p] * x[q]; });
    const i = d.index[12 + 4], c = d.X[1][4]; a += i; b += c; ab += i * c;
  }
  pairs.forEach(([p, q], k) => {
    const cov = sx[k][2] / N - (sx[k][0] / N) * (sx[k][1] / N);
    assert.ok(Math.abs(cov - V[p][q]) < 0.1 * V[p][q] + 0.002, `cell cov ${cov} vs ${V[p][q]}`);
  });
  const ci = ab / N - (a / N) * (b / N);
  assert.ok(Math.abs(ci - target) < 0.25 * target + 0.003, `index cov ${ci} vs ${target}`);
});

test('φ̂ from a long index recovers φ; the fit uses it on request and falls back without one', () => {
  const w = M.makeWorld({ indexYears: 30, indexNoise: 0.5 }), r = M.rng(14), est = [];
  for (let n = 0; n < 80; n++) est.push(M.phiIndex(M.draw(w, r)).phi);
  est.sort((x, y) => x - y);
  assert.ok(Math.abs(est[40] - w.truth.phi) < 0.05, `median ${est[40]}`);
  const d = M.draw(w, r), f = M.fit(d, { phiMethod: 'index' });
  assert.equal(f.phiMethod, 'index'); assert.equal(f.phi, M.phiIndex(d).phi);
  const g = M.fit(M.draw(M.makeWorld({}), r), { phiMethod: 'index' });
  assert.equal(g.phiMethod, 'profile'); assert.ok(g.warnings.some((x) => x.code === 'noIndex'));
});

test('toCSV appends the index with years before the data numbered 0, −1, …', () => {
  const d = M.draw(M.makeWorld({ J: 2, Y: 2, indexYears: 3 }), M.rng(15)), lines = M.toCSV(d).trim().split('\n');
  assert.equal(lines.length, 1 + 2 * 24 + 12 * 5);
  const first = lines[1 + 48].split(','), last = lines[lines.length - 1].split(',');
  assert.deepEqual(first.slice(0, 4), ['index', '-2', '1', '']);
  assert.deepEqual(last.slice(0, 3), ['index', '2', '12']);
  assert.ok(Math.abs(+last[4] - d.index[d.index.length - 1]) < 1e-9);
});

test('constrainPSD: valid tables, the unbiased fit when it is valid, and a minimum over the cone', () => {
  const r = M.rng(16), J = 4, mineig = (X) => Math.min(...M.eigSymVec(X).values);
  let checked = 0, kept = 0;
  for (let n = 0; n < 12; n++) {
    const w = M.makeWorld({ J }), d = M.draw(w, r), mq = M.minque(d, 0.6), c = M.constrainPSD(mq, J);
    const tab = (kind) => { const X = Array.from({ length: J }, () => new Array(J).fill(0)); mq.list.forEach((b, k) => { if (b.kind === kind) { X[b.i][b.j] = c.theta[k]; X[b.j][b.i] = c.theta[k]; } }); return X; };
    assert.ok(mineig(tab('A')) > -1e-10 && mineig(tab('C')) > -1e-10, 'PSD');
    mq.list.forEach((b, k) => { if (b.kind === 's') assert.ok(c.theta[k] >= 0, 's² ≥ 0'); });
    // Valid unbiased fit: unchanged.
    const valid = (() => { const u = { theta: mq.theta }; const t = (kind) => { const X = Array.from({ length: J }, () => new Array(J).fill(0)); mq.list.forEach((b, k) => { if (b.kind === kind) { X[b.i][b.j] = u.theta[k]; X[b.j][b.i] = u.theta[k]; } }); return X; };
      return mineig(t('A')) >= 0 && mineig(t('C')) >= 0 && mq.list.every((b, k) => b.kind !== 's' || u.theta[k] >= 0); })();
    if (valid) { kept++; mq.theta.forEach((x, k) => close(c.theta[k], x, 1e-8, 'unchanged')); }
    // No feasible point nearby does better: shrink towards 0 or mix with the clipped unbiased fit.
    const obj = (th) => th.reduce((v, x, k) => v + x * mq.H[k].reduce((h, y, l) => h + y * th[l], 0) - 2 * mq.q[k] * x, 0);
    for (const a of [0.9, 0.99, 1.01]) assert.ok(obj(c.theta.map((x) => a * x)) >= c.objective - 1e-9 * Math.abs(c.objective), `scale ${a}`);
    checked++;
  }
  assert.ok(checked === 12);
  void kept;
});

test('fit with psd: valid tables and the extra step, badge proved (ConeProjection.integral_hsq_proj_le)', () => {
  const w = M.makeWorld({}), d = M.draw(w, M.rng(17)), f = M.fit(d, { psd: true });
  assert.ok(Math.min(...M.eigSymVec(f.A).values) > -1e-10 && Math.min(...M.eigSymVec(f.C).values) > -1e-10 && f.s2.every((x) => x >= 0));
  assert.ok(f.steps.some((s) => s.badge === 'proved' && s.lean === 'ConeProjection.integral_hsq_proj_le' && /valid tables/.test(s.name)));
});

// The premium: the next-12-month mean of each cohort (Factor.blup_season_optimal).
const trueTab = (w) => ({ phi: w.truth.phi, A: w.truth.A, C: w.truth.C, s2: w.truth.s2 });
const monthSums = (d, J, T) => { const s = new Array(12 * J).fill(0); d.forEach((x, p) => { s[Math.floor(p / T) * 12 + ((p % T) % 12)] += x; }); return s; };

test('the predictor is unbiased: its month sums are 1/12 on the target cohort, 0 elsewhere (Core.blup_unbiased)', () => {
  const w = M.makeWorld({ J: 3 }), P = M.predictor(3, 2, w.w, trueTab(w), w.wFuture);
  P.weights.forEach((d, j0) => monthSums(d, 3, 24).forEach((x, c) => close(x, Math.floor(c / 12) === j0 ? 1 / 12 : 0, 1e-9, `sum ${j0} ${c}`)));
});

test('τ² does not change the predictor: the cohort level is in the span of the season', () => {
  const w = M.makeWorld({ J: 2, tau2: 0.3 }), J = 2, T = 24, n = J * T, V = M.covTable(w), P = M.predictor(J, 2, w.w, trueTab(w));
  const { phi, A, tau2 } = w.truth, q = 12 * J;
  const Xd = Array.from({ length: n }, (_, p) => Array.from({ length: q }, (_, c) => (Math.floor(p / T) * 12 + ((p % T) % 12) === c ? 1 : 0)));
  const Kinv = (b) => M.solve(V, b);
  for (let j0 = 0; j0 < J; j0++) {
    const ell = Array.from({ length: n }, (_, p) => {
      const i = Math.floor(p / T), t = p % T; let s = 0;
      for (let u = T; u < T + 12; u++) s += A[i][j0] * Math.pow(phi, u - t) / 12;
      return s + (i === j0 ? tau2 : 0); // ℓ with the level (Factor.ell_apply_of_future)
    });
    const Kl = Kinv(ell), KiX = Xd[0].map((_, c) => Kinv(Xd.map((row) => row[c])));
    const G = KiX.map((a) => KiX.map((_, e) => a.reduce((s, x, p) => s + x * Xd[p][e], 0)));
    const x0 = Array.from({ length: q }, (_, c) => (Math.floor(c / 12) === j0 ? 1 / 12 : 0));
    const r = x0.map((x, c) => x - Kl.reduce((s, y, p) => s + y * Xd[p][c], 0)), g = M.solve(G, r);
    const d = Kl.map((x, p) => x + KiX.reduce((s, a, c) => s + a[p] * g[c], 0));
    d.forEach((x, p) => close(x, P.weights[j0][p], 1e-7, `weight ${j0} ${p}`));
  }
});

test('the floor: simulated MSE of the true-table predictor matches dᵀKd − 2dᵀℓ + v (Factor.predMse_blup)', () => {
  const w = M.makeWorld({ J: 3, tau2: 0.05 }), P = M.predictor(3, 2, w.w, trueTab(w), w.wFuture), r = M.rng(18), N = 1500;
  const s = [0, 0, 0], ss = [0, 0, 0];
  for (let n = 0; n < N; n++) {
    const { data, target } = M.drawFuture(w, r), pr = P.predict(data.X);
    pr.forEach((x, j) => { const e = (x - target[j]) ** 2; s[j] += e; ss[j] += e * e; });
  }
  s.forEach((x, j) => {
    const mean = x / N, se = Math.sqrt((ss[j] / N - mean * mean) / N);
    assert.ok(Math.abs(mean - P.mse[j]) < 4 * se, `cohort ${j}: ${mean} vs ${P.mse[j]} (se ${se})`);
  });
});

test('the floor beats the last-year mean, which is unbiased too (Factor.blup_season_optimal)', () => {
  for (const par of [{}, { phi: 0.9, Y: 3 }, { volume: 'flat' }]) {
    const w = M.makeWorld(par), J = w.J, T = 12 * w.Y, V = M.covTable(w), P = M.predictor(J, w.Y, w.w, trueTab(w), w.wFuture);
    for (let j0 = 0; j0 < J; j0++) {
      const d = Array.from({ length: J * T }, (_, p) => (Math.floor(p / T) === j0 && p % T >= T - 12 ? 1 / 12 : 0));
      const ell = Array.from({ length: J * T }, (_, p) => { let s = 0; for (let u = T; u < T + 12; u++) s += w.truth.A[Math.floor(p / T)][j0] * Math.pow(w.truth.phi, u - p % T) / 12; return s; });
      const Kn = V.map((row, p) => row.map((x, p2) => x - (Math.floor(p / T) === Math.floor(p2 / T) ? w.truth.tau2 : 0)));
      const dKd = d.reduce((a, x, p) => a + x * Kn[p].reduce((b, y, p2) => b + y * d[p2], 0), 0);
      const vMinusFloor = P.mse[j0] - (P.weights[j0].reduce((a, x, p) => a + x * Kn[p].reduce((b, y, p2) => b + y * P.weights[j0][p2], 0), 0) - 2 * P.weights[j0].reduce((a, x, p) => a + x * ell[p], 0));
      const mseLast = dKd - 2 * d.reduce((a, x, p) => a + x * ell[p], 0) + vMinusFloor;
      assert.ok(P.mse[j0] <= mseLast + 1e-12, `${JSON.stringify(par)} cohort ${j0}: ${P.mse[j0]} vs ${mseLast}`);
    }
  }
});

test('H-norm check: the projection is never further from the truth (ConeProjection.hsq_proj_add_le)', () => {
  let n = 0, worst = Infinity, moved = 0;
  for (const par of [{}, { J: 3, phi: 0.9 }, { indexYears: 10 }, { Y: 3, gamma: 0.06 }]) {
    const w = M.makeWorld(par), r = M.rng(19);
    for (let k = 0; k < 40; k++) {
      const d = M.draw(w, r);
      for (const opt of [{}, { phi: w.truth.phi }]) { // the profile φ̂ and the true φ: the bound holds for any estimate
        const c = M.hNormCheck(w, M.fit(d, Object.assign({ psd: true }, opt)));
        if (!c) continue;
        // Tolerance: the block solver stops at a relative change of 1e-12 in the objective.
        assert.ok(c.slack >= -1e-6 * c.unbiased, `${JSON.stringify(par)}: slack ${c.slack}, unbiased ${c.unbiased}`);
        assert.ok(c.projected <= c.unbiased * (1 + 1e-6), 'projected ≤ unbiased');
        worst = Math.min(worst, c.slack / c.unbiased); if (c.moved > 0) moved++; n++;
      }
    }
  }
  assert.ok(n > 250 && moved > 100, `checked ${n} draws, ${moved} moved by the projection; worst relative slack ${worst}`);
});

test('Finding 30: valid tables with every ŝ² > 0 give a premium (tableK_posDef); a cohort with Â, Ĉ, ŝ² all 0 does not (tableK_not_posDef)', () => {
  // tableK_not_posDef: cohort 0 with zero variances makes K̂ singular, so no predictor.
  const w = M.makeWorld({ J: 3 }), t = w.truth;
  const zero = (X) => X.map((row, i) => row.map((x, j) => (i === 0 || j === 0 ? 0 : x)));
  const tab = { phi: t.phi, A: zero(t.A), C: zero(t.C), s2: t.s2.map((x, j) => (j === 0 ? 0 : x)) };
  assert.equal(M.predictor(3, 2, w.w, tab), null, 'singular K̂');
  assert.deepEqual(M.zeroVarianceCohorts({ s2: tab.s2, A: tab.A, C: tab.C }), [0]);
  // tableK_posDef: any PSD Â (here full rank, not γλλᵀ), Ĉ ⪰ 0 and every ŝ² > 0.
  const Afull = [[0.03, 0.01, 0], [0.01, 0.02, 0.005], [0, 0.005, 0.01]];
  assert.ok(M.predictor(3, 2, w.w, { phi: 0.6, A: Afull, C: t.C, s2: t.s2 }), 'positive definite');
  // Over draws: a missing premium always comes with some ŝⱼ² = 0 (the contrapositive of tableK_posDef).
  const r = M.rng(20); let n = 0, sz = 0;
  for (const par of [{}, { s2: 4 }, { J: 5 }]) {
    const ww = M.makeWorld(par);
    for (let k = 0; k < 25; k++) {
      const f = M.fit(M.draw(ww, r), { psd: true });
      if (f.singular) continue;
      const z = M.sZeroCohorts(f).length > 0, P = M.predictor(ww.J, ww.Y, ww.w, { phi: f.phi, A: f.A, C: f.C, s2: f.s2 });
      if (!P) assert.ok(z, 'no premium only with some ŝⱼ² = 0');
      if (M.zeroVarianceCohorts(f).length) assert.equal(P, null, 'a zero-variance cohort means no premium');
      f.s2.forEach((x) => assert.ok(x >= 0));
      if (z) sz++; n++;
    }
  }
  assert.ok(n > 60 && sz > 0, `${sz} of ${n} fits with some ŝⱼ² = 0`);
});

// ---------------------------------------------------------------- comparing fits (card-data Step 7b)

test('Student t CDF and the incomplete beta behind it', () => {
  close(M.tCdf(0, 5), 0.5, 1e-12, 't(5) at 0');
  close(M.tCdf(1, 1), 0.75, 1e-10, 'Cauchy at 1');
  close(M.tCdf(2, 10), 0.963306, 1e-6, 't(10) at 2');
  close(M.tCdf(-2.0423, 30), 0.025, 1e-4, 't(30) lower 2.5%');
  close(M.betaInc(0.3, 2, 3), 0.3483, 1e-4, 'I_0.3(2, 3)');
});

test('a fit with T not a multiple of 12: the centring still annihilates the season, Kronecker MINQUE = dense', () => {
  const w = M.makeWorld({ J: 2, Y: 3 }), d = M.truncate(M.draw(w, M.rng(30)), 30);
  assert.equal(d.X[0].length, 30);
  const pure = { J: 2, Y: d.Y, w: d.w, X: d.w.map((row, j) => row.map((_, t) => 3 + j + Math.cos(t % 12))) };
  M.minque(pure, 0.6).q.forEach((x) => close(x, 0, 1e-12, 'q'));
  const a = M.minque(d, 0.6), b = M.minqueDense(d, 0.6);
  a.H.forEach((row, k) => row.forEach((x, l) => close(x, b.H[k][l], 1e-9, 'H')));
  a.q.forEach((x, k) => close(x, b.q[k], 1e-9, 'q'));
});

test('rolling origin: no look-ahead, and the exposure-weighted loss', () => {
  const w = M.makeWorld({ J: 3, Y: 4 }), d = M.draw(w, M.rng(31)), burn = 24, T = 48;
  const ro = M.rollingOrigin(d, { fits: ['last', 'moment', 'oracle'], burn, world: w });
  assert.deepEqual(ro.origins, Array.from({ length: T - 12 - burn + 1 }, (_, k) => burn + k));
  // The first origin's loss uses months < burn + 12 only: change every later month, nothing moves.
  const d2 = { J: d.J, Y: d.Y, w: d.w, X: d.X.map((row) => row.map((x, t) => (t >= burn + 12 ? x + 100 : x))) };
  const ro2 = M.rollingOrigin(d2, { fits: ['last', 'moment', 'oracle'], burn, world: w });
  for (const k of ['last', 'moment', 'oracle']) assert.equal(ro2.loss[k][0], ro.loss[k][0], `${k}: origin ${burn}`);
  // The loss is Σ Wⱼ eⱼ² / Σ Wⱼ over the 12 target months.
  const t0 = ro.origins[3], pred = M.lastYear(M.truncate(d, t0));
  const Yt = d.X.map((row) => row.slice(t0, t0 + 12).reduce((a, x) => a + x, 0) / 12);
  const Wt = d.w.map((row) => row.slice(t0, t0 + 12).reduce((a, x) => a + x, 0));
  const L = pred.reduce((a, y, j) => a + Wt[j] * (y - Yt[j]) ** 2, 0) / Wt.reduce((a, x) => a + x, 0);
  close(ro.loss.last[3], L, 1e-12, 'weighted loss');
  ro.card.last[3].forEach((e, j) => close(e, (pred[j] - Yt[j]) ** 2, 1e-12, 'per card'));
});

test('a singular valid table is caught before the Cholesky (degenerateTable, Finding 30)', () => {
  const A = [[0.02, 0.02], [0.02, 0.02]], C = [[0.01, 0.01], [0.01, 0.01]];
  assert.ok(M.degenerateTable({ A, C, s2: [0, 0] }), 'rank one A + C on Z = {1, 2}');
  assert.ok(!M.degenerateTable({ A, C, s2: [0, 5] }), 'Z = {1}: A₁₁ + C₁₁ > 0');
  assert.ok(!M.degenerateTable({ A, C: [[0.01, 0], [0, 0.01]], s2: [0, 0] }), 'A + C ≻ 0');
  assert.ok(M.degenerateTable({ A: [[0, 0], [0, 0.02]], C: [[0, 0], [0, 0.01]], s2: [0, 5] }), 'tableK_not_posDef: one cohort');
  // Agrees with the exact Cholesky on a short table where rounding does not interfere.
  const w = M.makeWorld({ J: 2, Y: 2 });
  assert.equal(M.predictor(2, 2, w.w, { phi: 0.6, A, C, s2: [0, 0] }), null);
  assert.ok(M.predictor(2, 2, w.w, { phi: 0.6, A, C, s2: [0, 5] }));
});

test('Diebold–Mariano with the HLN correction: the formula, and null with too few origins', () => {
  const r = M.rng(32), d = Array.from({ length: 40 }, () => 0.1 + r.normal());
  const x = M.dmTest(d, 12), n = 40, mean = d.reduce((a, v) => a + v, 0) / n;
  const g = (k) => { let s = 0; for (let t = k; t < n; t++) s += (d[t] - mean) * (d[t - k] - mean); return s / n; };
  let V = g(0); for (let k = 1; k < 12; k++) V += 2 * g(k);
  if (!x.bartlett) close(x.V, V, 1e-12, 'uniform long-run variance');
  close(x.stat, x.dm * Math.sqrt((n + 1 - 24 + 132 / n) / n), 1e-12, 'HLN factor');
  close(x.p, 2 * (1 - M.tCdf(Math.abs(x.stat), n - 1)), 1e-12, 'p against t(n − 1)');
  assert.equal(M.dmTest(d.slice(0, 24), 12), null, 'n ≤ 2h');
});

test('size: on equally good fits (MA(11) differentials) both tests over-reject with few origins, less with more', () => {
  // The protocol's warning (card-data Step 7b; Harvey, Leybourne & Whitehouse 2017): with n monthly
  // origins and 12-month targets there are about n/12 independent comparisons.
  const few = M.dmSize(37, 1500, M.rng(33)), many = M.dmSize(145, 1500, M.rng(34));
  assert.ok(few.dm > 0.1, `DM–HLN at 37 origins: ${few.dm}`);
  assert.ok(many.dm < few.dm && many.dm < 0.1, `DM–HLN at 145 origins: ${many.dm}`);
  assert.ok(many.wpe < 0.1, `WPE at 145 origins: ${many.wpe}`);
});

test('power: the oracle beats the last-year mean on average, and the test sees it in some draws', () => {
  const w = M.makeWorld({ J: 3, Y: 6 }), r = M.rng(35);
  let s = 0, picksOracle = 0, picksLast = 0;
  const N = 12;
  for (let k = 0; k < N; k++) {
    const c = M.compareFits(M.rollingOrigin(M.draw(w, r), { fits: ['oracle', 'last'], burn: 36, world: w }), 'oracle', 'last');
    s += c.meanA - c.meanB;
    if (c.verdict === 'A') picksOracle++;
    if (c.verdict === 'B') picksLast++;
  }
  assert.ok(s < 0, `mean difference ${s / N}`);
  assert.ok(picksOracle >= 1 && picksLast <= 1, `oracle picked ${picksOracle}, last picked ${picksLast} of ${N}`);
});
