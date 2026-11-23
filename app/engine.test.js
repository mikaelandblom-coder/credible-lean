// Identity tests for app/engine.js: the proved results, to machine precision,
// plus statistical checks with a fixed seed. Run: node --test app/engine.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const E = require('./engine.js');

const close = (a, b, tol, msg) =>
  assert.ok(Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b)), `${msg}: ${a} vs ${b}`);
const sum = (a) => a.reduce((s, x) => s + x, 0);

test('BS is the special case ρ = 0 (Credibility.bs_z, bs_b)', () => {
  for (const params of [{}, { J: 3, T: 2, spread: 2 }, { J: 15, tau: 0.03, sigma: 9 }]) {
    const world = E.makeWorld(Object.assign({ rho: 0 }, params));
    const fl = E.floorBlend(world), { tau2, sigma2 } = world.truth;
    const wt = world.w.map(sum), zB = wt.map((x) => x / (x + sigma2 / tau2)), zs = sum(zB);
    world.w.forEach((_, j) => {
      close(fl.z[j], zB[j], 1e-12, `z[${j}]`);
      close(fl.b[j], zB[j] / zs, 1e-12, `b[${j}]`);
    });
  }
});

test('BS is balanced on any data (Credibility.bs_balance)', () => {
  const r = E.rng(1);
  for (const params of [{}, { rho: 0.7 }, { J: 4, T: 3, tau: 0.001, sigma: 20 }]) {
    const world = E.makeWorld(params);
    let truncated = 0;
    for (let k = 0; k < 200; k++) {
      const { data } = E.draw(world, r), f = E.fitBS(data);
      if (f.warnings.length) truncated++;
      const wt = data.w.map(sum), gap = sum(wt.map((x, j) => x * (f.means[j] - f.rates[j])));
      close(gap / sum(wt), 0, 1e-12, 'balance');
    }
    if (params.tau === 0.001) assert.ok(truncated > 0, 'the τ̂² ≤ 0 branch was exercised');
  }
});

test('Two cohorts: z₁ closed form and b₁ = z₁/(z₁+z₂) (TwoCohorts.z1_eq, b1_eq_z)', () => {
  const r = E.rng(2);
  for (let k = 0; k < 100; k++) {
    const s1 = 0.01 + r(), s2 = 0.01 + r(), tau2 = 0.01 + r(), rho = 2 * r() - 1;
    const K = [[tau2 + s1 * s1, s1 * s2 * rho], [s1 * s2 * rho, tau2 + s2 * s2]];
    const { b, z } = E.bestBlendWeights(K, tau2);
    const c = s1 * s2 * rho, z1 = tau2 / (tau2 + s1 * s1 - c), z2 = tau2 / (tau2 + s2 * s2 - c);
    close(z[0], z1, 1e-10, 'z1');
    close(z[1], z2, 1e-10, 'z2');
    close(b[0], z1 / (z1 + z2), 1e-10, 'b1');
  }
});

test('Equal covariances: zⱼ = τ²/(τ²+vⱼ−c), bⱼ = zⱼ/z* (Core.bestZ_of_equalCov, b_eq_of_equalCov)', () => {
  const r = E.rng(3);
  for (let k = 0; k < 50; k++) {
    const J = 2 + Math.floor(r() * 10), tau2 = 0.01 + r(), c = r() * 0.5;
    const v = Array.from({ length: J }, () => c + 0.01 + r());
    const K = v.map((vi, i) => v.map((_, j) => (i === j ? tau2 + vi : c)));
    assert.ok(E.cholesky(K), 'K ≻ 0');
    const { b, z } = E.bestBlendWeights(K, tau2);
    const zc = v.map((vj) => tau2 / (tau2 + vj - c)), zs = sum(zc);
    for (let j = 0; j < J; j++) { close(z[j], zc[j], 1e-10, 'z'); close(b[j], zc[j] / zs, 1e-10, 'b'); }
  }
});

test('Eq. (26) minimises the true MSE (Core.Estimates.bestZ_mse_optimal)', () => {
  for (const params of [{}, { rho: 0.6 }, { J: 3, rho: 0.9, spread: 2 }]) {
    const world = E.makeWorld(params), fl = E.floorBlend(world), tau2 = world.truth.tau2;
    for (let j = 0; j < world.J; j++) {
      const m0 = E.blendMSE(fl.K, tau2, fl.b, fl.s2, j, fl.z[j]);
      for (const d of [1e-3, -1e-3, 0.1, -0.1, 0.5]) {
        assert.ok(E.blendMSE(fl.K, tau2, fl.b, fl.s2, j, fl.z[j] + d) > m0, `j=${j}, d=${d}`);
      }
    }
  }
});

test('The floor MSE seen in simulation is the true MSE (moment layer)', () => {
  const world = E.makeWorld({ rho: 0.5 }), fl = E.floorBlend(world), tau2 = world.truth.tau2;
  const wt = world.w.map(sum), wall = sum(wt);
  const exact = sum(wt.map((x, j) => x * E.blendMSE(fl.K, tau2, fl.b, fl.s2, j, fl.z[j]))) / wall;
  const sim = E.simulate(world, [], 20000, 4).floor;
  assert.ok(Math.abs(sim.mse - exact) < 4 * sim.se, `${sim.mse} ± ${sim.se} vs ${exact}`);
});

test('The draws have the stated moments (Var μⱼ = τ², corr within a year = ρ)', () => {
  const world = E.makeWorld({ J: 2, T: 2, rho: 0.6, tau: 0.2 }), r = E.rng(5);
  const n = 40000, sig = Math.sqrt(world.truth.sigma2);
  let sl = 0, sll = 0, s00 = 0, s11 = 0, s01 = 0;
  for (let k = 0; k < n; k++) {
    const { levels, data } = E.draw(world, r);
    const e0 = (data.X[0][0] - levels[0]) * Math.sqrt(data.w[0][0]) / sig;
    const e1 = (data.X[1][0] - levels[1]) * Math.sqrt(data.w[1][0]) / sig;
    sl += levels[0]; sll += levels[0] * levels[0]; s00 += e0 * e0; s11 += e1 * e1; s01 += e0 * e1;
  }
  const varL = sll / n - (sl / n) ** 2;
  assert.ok(Math.abs(varL / world.truth.tau2 - 1) < 0.05, `Var μⱼ ratio ${varL / world.truth.tau2}`);
  assert.ok(Math.abs(s00 / n - 1) < 0.05 && Math.abs(s11 / n - 1) < 0.05, 'unit noise variance');
  assert.ok(Math.abs(s01 / Math.sqrt(s00 * s11) - 0.6) < 0.02, 'correlation');
});

test('BS estimators are unbiased on average at ρ = 0 (σ̂² via Model.sigRhoHat_self; raw τ̂²)', () => {
  const world = E.makeWorld({ J: 6, T: 5 }), r = E.rng(6), n = 20000;
  const acc = { s: [0, 0], t: [0, 0] };
  for (let k = 0; k < n; k++) {
    const f = E.fitBS(E.draw(world, r).data);
    const s = f.steps[1].values[0], t = f.steps[2].values[0];
    acc.s[0] += s; acc.s[1] += s * s; acc.t[0] += t; acc.t[1] += t * t;
  }
  for (const [key, truth] of [['s', world.truth.sigma2], ['t', world.truth.tau2]]) {
    const m = acc[key][0] / n, se = Math.sqrt((acc[key][1] / n - m * m) / n);
    assert.ok(Math.abs(m - truth) < 4 * se, `${key}: ${m} ± ${se} vs ${truth}`);
  }
});

test('No fit sees the world: fits read only data.w and data.X', () => {
  const world = E.makeWorld({ rho: 0.4 }), { data } = E.draw(world, E.rng(7));
  const guarded = new Proxy(data, {
    get(target, key) {
      if (key === 'w' || key === 'X') return target[key];
      throw new Error(`fit read data.${String(key)}`);
    },
  });
  for (const [id, m] of Object.entries(E.MODELS)) {
    if (!m.ready) continue;
    assert.equal(m.fit.length, 1, `${id} takes one argument`);
    const a = m.fit(guarded), b = m.fit({ w: data.w.map((x) => x.slice()), X: data.X.map((x) => x.slice()) });
    assert.deepEqual(a.rates, b.rates, `${id} depends on the data only`);
    assert.ok(!/truth|levels|world|params/.test(m.fit.toString()), `${id} source mentions the world`);
  }
});

// ---------------------------------------------------------------- step 3: the correlation fit

test('Damping: K̂ ≻ 0 for every fitted draw, and for any θ < 1 when Σ̂ ⪰ 0 (posDef_shrinkOffDiag, Unequal.dampedK_posDef)', () => {
  const r = E.rng(8);
  for (const params of [{}, { rho: 0.5 }, { rho: 0.9, J: 12, T: 3 }, { J: 3, T: 2, tau: 0.01 }]) {
    const world = E.makeWorld(params);
    for (let k = 0; k < 300; k++) {
      const { data } = E.draw(world, r);
      for (const common of [false, true]) {
        const f = E.fitCorr(data, { common });
        assert.ok(E.cholesky(f.K), 'K̂ ≻ 0');
        assert.ok(f.theta >= 0 && f.theta < 1, 'θ ∈ [0, 1)');
      }
    }
  }
  // The theorem itself: any PSD A with positive diagonal, θ ∈ [0, 1), τ ≥ 0.
  for (let k = 0; k < 200; k++) {
    const n = 2 + Math.floor(r() * 8), m = 1 + Math.floor(r() * n); // rank m ≤ n: often singular
    const B = Array.from({ length: n }, () => Array.from({ length: m }, () => r.normal()));
    const A = B.map((bi) => B.map((bj) => sum(bi.map((x, l) => x * bj[l]))));
    const th = r() * 0.999, tau = r() < 0.3 ? 0 : r();
    const K = E.shrinkOffDiag(th, A).map((row, i) => row.map((x, j) => (i === j ? x + tau : x)));
    assert.ok(E.cholesky(K), `n=${n}, rank ${m}, θ=${th}`);
  }
});

test('Thesis τ̂², σ²ᵢⱼρᵢⱼ^ and K̂ are unbiased on average (Model.tauHat_unbiased, sigRhoHat_unbiased, KHat_unbiased)', () => {
  for (const params of [{ J: 6, T: 5, rho: 0.5 }, { J: 4, T: 3, rho: 0 }]) {
    const world = E.makeWorld(params), K = E.trueK(world), r = E.rng(9), n = 20000;
    const acc = { tau: [0, 0], s01: [0, 0], s00: [0, 0] };
    const add = (a, x) => { a[0] += x; a[1] += x * x; };
    for (let k = 0; k < n; k++) {
      const { data } = E.draw(world, r), est = E.sigmaHat(data);
      add(acc.tau, E.thesisTau(est.m, est.wt, est.Sig).tau2);
      add(acc.s01, est.Sig[0][1]); add(acc.s00, est.Sig[0][0]);
    }
    const tau2 = world.truth.tau2;
    for (const [key, truth] of [['tau', tau2], ['s01', K[0][1]], ['s00', K[0][0] - tau2]]) {
      const m = acc[key][0] / n, se = Math.sqrt((acc[key][1] / n - m * m) / n);
      assert.ok(Math.abs(m - truth) < 4 * se, `${key}: ${m} ± ${se} vs ${truth}`);
    }
  }
});

// Not balanced: with a σ̂ⱼ per cohort, wⱼ*(1 − zⱼ) = (σ̂ⱼ²/τ̂²)zⱼ is not proportional to zⱼ.
test('Correlation fit at θ = 0 is BS-like: zⱼ = wⱼ*/(wⱼ* + σ̂ⱼ²/τ̂²), bⱼ = zⱼ/z* (Core.bestZ_of_diag)', () => {
  const world = E.makeWorld({ rho: 0 }), r = E.rng(10);
  let checked = 0;
  for (let k = 0; k < 200; k++) {
    const { data } = E.draw(world, r), f = E.fitCorr(data, { theta: 0 });
    if (f.tau2 <= 0) continue;
    const wt = data.w.map(sum), T = data.X[0].length;
    const sj2 = f.means.map((mj, j) => sum(data.X[j].map((x, t) => data.w[j][t] * (x - mj) ** 2)) / (T - 1));
    const z = wt.map((x, j) => x / (x + sj2[j] / f.tau2)), zs = sum(z);
    for (let j = 0; j < wt.length; j++) { close(f.z[j], z[j], 1e-9, 'z'); close(f.b[j], z[j] / zs, 1e-9, 'b'); }
    checked++;
  }
  assert.ok(checked > 100);
});

test('Correlation fit at ρ = 0 performs like BS (statistical)', () => {
  const world = E.makeWorld({ rho: 0 }), res = E.simulate(world, ['bs', 'corr', 'corrC'], 3000, 11);
  for (const id of ['corr', 'corrC']) {
    const ratio = res[id].mse / res.bs.mse;
    assert.ok(ratio > 0.9 && ratio < 1.15, `${id}/bs MSE ratio ${ratio}`);
  }
});

test('Common covariance: the closed form equals the GLS route (Core.bestZ_of_equalCov, b_eq_of_equalCov)', () => {
  const r = E.rng(12);
  for (const rho of [0, 0.4]) {
    const world = E.makeWorld({ rho });
    for (let k = 0; k < 200; k++) {
      const f = E.fitCorr(E.draw(world, r).data, { common: true });
      if (f.tau2 <= 0) continue;
      const g = E.bestBlendWeights(f.K, f.tau2);
      f.z.forEach((z, j) => { close(z, g.z[j], 1e-8, 'z'); close(f.b[j], g.b[j], 1e-8, 'b'); });
    }
  }
});

test('Warnings: z > 1 and negative b are flagged when they occur', () => {
  const world = E.makeWorld({ rho: 0.8, spread: 2 }), res = E.simulate(world, ['corr', 'corrC'], 500, 13);
  assert.ok(res.corr.flags.bNeg > 0, 'negative b seen');
  assert.ok(res.corrC.flags.zOver1 > 0, 'z > 1 seen');
  const r = E.rng(14);
  for (let k = 0; k < 100; k++) {
    const f = E.fitCorr(E.draw(world, r).data);
    assert.equal(f.flags.zOver1, f.z.some((z) => z > 1));
    assert.equal(f.flags.bNeg, f.b.some((b) => b < 0));
    assert.equal(f.warnings.length, Object.values(f.flags).filter(Boolean).length);
  }
});

test('Every step marked proved names a proved Lean declaration; every other step names its gap', () => {
  const world = E.makeWorld({ rho: 0.3 }), { data } = E.draw(world, E.rng(15));
  const path = require('node:path'), { execFileSync } = require('node:child_process');
  // The same list as PROGRESS.md and the handbook check (no sorry; CI's CheckAxioms
  // makes sure nothing counted as proved depends on one).
  const proved = new Set(execFileSync('python3', [path.join(__dirname, '..', 'scripts', 'progress.py'), '--proved'],
    { encoding: 'utf8' }).split(/\s+/).filter(Boolean));
  for (const [id, m] of Object.entries(E.MODELS)) {
    for (const s of m.fit(data).steps) {
      assert.ok(s.badge === 'proved' || s.badge === 'not proved yet', `${id}/${s.name} badge`);
      if (s.badge === 'proved') {
        assert.ok(proved.has(s.lean), `${id}/${s.name}: ${s.lean} is not a proved declaration`);
      } else assert.ok(s.gap || s.note, `${id}/${s.name}: no gap named`);
    }
    const pr = E.premium(m.fit(data), data, E.nextVolumes(data));
    if (pr) assert.ok(proved.has(pr.step.lean), `${id}/premium: ${pr.step.lean} is not a proved declaration`);
    else assert.ok(id === 'own' || id === 'pool', `${id}: no premium step`);
  }
});

// ---------------------------------------------------------------- correlated BS with credibility-weighted variances

test('Correlated BS (vc): K̂ ≻ 0 for every draw, with no damping (Model.K_posDef, ρ̂ ∈ [0, 1))', () => {
  const r = E.rng(16);
  for (const params of [{}, { rho: 0.5 }, { rho: 0.9, J: 12, T: 3 }, { J: 3, T: 2, tau: 0.01 }, { rho: 0.95, spread: 2, T: 20 }]) {
    const world = E.makeWorld(params);
    for (let k = 0; k < 300; k++) {
      const f = E.fitVC(E.draw(world, r).data);
      assert.ok(E.cholesky(f.K), `K̂ ≻ 0 (${JSON.stringify(params)}, draw ${k})`);
      assert.ok(f.rho >= 0 && f.rho < 1, 'ρ̂ ∈ [0, 1)');
      assert.ok(f.sigma2.every((x) => x > 0), 'σ̃ⱼ² > 0');
    }
  }
});

test('Correlated BS (vc) equals BS when ρ̂ = 0 and all σ̃ⱼ equal (β² = 0)', () => {
  const r = E.rng(17);
  let checked = 0;
  for (const params of [{ rho: 0 }, { rho: 0, J: 4, T: 3, spread: 2 }, { rho: 0, J: 15, tau: 0.03 }]) {
    const world = E.makeWorld(params);
    for (let k = 0; k < 400; k++) {
      const { data } = E.draw(world, r), f = E.fitVC(data);
      if (f.rhoRaw > 0 || f.between > 0) continue;
      const bs = E.fitBS(data);
      f.rates.forEach((x, j) => { close(x, bs.rates[j], 1e-9, 'rate'); close(f.z[j], bs.z[j], 1e-9, 'z'); close(f.b[j], bs.b[j], 1e-9, 'b'); });
      checked++;
    }
  }
  assert.ok(checked > 100, `only ${checked} draws with ρ̂ = 0 and β² = 0`);
});

test('Correlated BS (vc) and its jackknife MSEP match the studies (variance-credibility.js cred, msep.js)', () => {
  const { fitVC } = require('../studies/variance-credibility.js'), M = require('../studies/msep.js');
  const r = E.rng(18);
  for (const params of [{}, { rho: 0.6, J: 5, T: 4 }]) {
    const world = E.makeWorld(params);
    for (let k = 0; k < 30; k++) {
      const { data } = E.draw(world, r), ref = fitVC(data, 'cred'), jk = M.msep(data).jack, o = E.jackknifeMSEP(data);
      E.fitVC(data).rates.forEach((x, j) => close(x, ref[j], 1e-12, 'rate'));
      o.msep.forEach((x, j) => close(x, Math.max(jk[j], 0), 1e-12, 'MSEP'));
    }
  }
});

test('Jackknife MSEP is right on average within 25% (one fixed-seed world, finding S19)', () => {
  const world = E.makeWorld({ rho: 0.5 }), r = E.rng(19), n = 600, J = world.J;
  const act = new Array(J).fill(0), pred = new Array(J).fill(0);
  for (let k = 0; k < n; k++) {
    const { levels, data } = E.draw(world, r), o = E.jackknifeMSEP(data);
    for (let j = 0; j < J; j++) { act[j] += (o.rates[j] - levels[j]) ** 2; pred[j] += o.msep[j]; }
  }
  const wt = world.w.map(sum), tot = (a) => sum(a.map((x, j) => x * wt[j]));
  const ratio = tot(pred) / tot(act);
  assert.ok(ratio > 0.75 && ratio < 1.25, `predicted / actual MSE ${ratio}`);
});

// ---------------------------------------------------------------- region-specific σⱼ (spread worlds of the studies)

test('Noise spread: σⱼ factors are the studies’ ×0.5–2 at s = 1; s = 0 is the old world, draw for draw', () => {
  const study = Array.from({ length: 8 }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5)); // variance-credibility.js, msep.js
  const world = E.makeWorld({ noiseSpread: 1 }), s = Math.sqrt(world.truth.sigma2);
  world.truth.sigmaj2.forEach((x, j) => close(Math.sqrt(x), s * study[j], 1e-12, `σ_${j}`));
  assert.deepEqual([0, 3].map((j) => E.noiseFactor(j, 1)), [0.5, 2]);
  const w0 = E.makeWorld({ rho: 0.4 }), w1 = E.makeWorld({ rho: 0.4, noiseSpread: 0 });
  assert.ok(w0.truth.sigmaj2.every((x) => x === w0.truth.sigma2), 'σⱼ = σ by default');
  const a = E.draw(w0, E.rng(5)), b = E.draw(w1, E.rng(5));
  assert.deepEqual(a.data.X, b.data.X);
});

test('Noise spread: true K is the studies’ K, and the draws have Var = σⱼ²/w, corr = ρ', () => {
  const world = E.makeWorld({ J: 6, T: 4, rho: 0.5, noiseSpread: 1 }), { J, T, w } = world, K = E.trueK(world);
  const s = Math.sqrt(world.truth.sigma2), wt = w.map(sum), sig = Array.from({ length: J }, (_, j) => s * Math.pow(4, (j % 4) / 3 - 0.5));
  for (let i = 0; i < J; i++) for (let j = 0; j < J; j++) {
    let S = 0; for (let t = 0; t < T; t++) S += Math.sqrt(w[i][t] * w[j][t]);
    close(K[i][j], sig[i] * sig[j] * (i === j ? 1 : 0.5) * S / (wt[i] * wt[j]) + (i === j ? world.truth.tau2 : 0), 1e-12, `K[${i}][${j}]`);
  }
  // Standardised noise uⱼ = (Xⱼ₀ − μⱼ)√wⱼ₀/σⱼ: variance 1, correlation ρ between regions 0 and 3 (σ ×0.5 and ×2).
  const r = E.rng(21), n = 40000; let s00 = 0, s33 = 0, s03 = 0;
  for (let k = 0; k < n; k++) {
    const { levels, data } = E.draw(world, r);
    const u = [0, 3].map((j) => (data.X[j][0] - levels[j]) * Math.sqrt(w[j][0]) / sig[j]);
    s00 += u[0] * u[0]; s33 += u[1] * u[1]; s03 += u[0] * u[1];
  }
  close(s00 / n, 1, 0.05, 'Var u₀'); close(s33 / n, 1, 0.05, 'Var u₃'); close(s03 / Math.sqrt(s00 * s33), 0.5, 0.05, 'corr');
});

test('Spread world (σⱼ ×0.5–2, ρ = 0.6): corrBS beats BS and the damped full fit (finding S19 world)', () => {
  const world = E.makeWorld({ rho: 0.6, noiseSpread: 1 }), res = E.simulate(world, ['bs', 'vc', 'corr'], 800, 22);
  const gap = (a, b) => (res[a].mse - res[b].mse) / Math.hypot(res[a].se, res[b].se);
  assert.ok(gap('bs', 'vc') > 3, `BS ${res.bs.mse} vs corrBS ${res.vc.mse}`);
  assert.ok(res.corr.mse > res.vc.mse, `corr ${res.corr.mse} vs corrBS ${res.vc.mse}`);
});

test('Spread world: jackknife MSEP understates, by roughly 10–15% (finding S19)', () => {
  const world = E.makeWorld({ rho: 0.6, noiseSpread: 1 }), r = E.rng(23), n = 600, J = world.J;
  const act = new Array(J).fill(0), pred = new Array(J).fill(0);
  for (let k = 0; k < n; k++) {
    const { levels, data } = E.draw(world, r), o = E.jackknifeMSEP(data);
    for (let j = 0; j < J; j++) { act[j] += (o.rates[j] - levels[j]) ** 2; pred[j] += o.msep[j]; }
  }
  const wt = world.w.map(sum), tot = (a) => sum(a.map((x, j) => x * wt[j])), ratio = tot(pred) / tot(act);
  assert.ok(ratio > 0.75 && ratio < 0.95, `predicted / actual MSE ${ratio}`);
});

test('corrBS: flags the true-K optimum shows too are notes, not warnings (studies/vc-balance.js, findings S27–S29)', () => {
  const world = E.makeWorld({ rho: 0.6, noiseSpread: 1 }), fl = E.floorBlend(world);
  // The floor itself: negative b, z below but close to 1, balanced for vⱼ ∝ bⱼ/(1 − zⱼ) and not for the exposures.
  assert.ok(fl.b.some((b) => b < 0), 'floor has a negative b');
  assert.ok(fl.z.every((z) => z < 1) && Math.max(...fl.z) > 0.9, 'floor z < 1, largest close to 1');
  const { data } = E.draw(world, E.rng(31)), m = E.cohortMeans(data).m, rates = fl.apply(data).rates;
  const v = fl.b.map((b, j) => b / (1 - fl.z[j]));
  assert.ok(Math.abs(sum(v.map((x, j) => x * (m[j] - rates[j])))) < 1e-9 * sum(v.map(Math.abs)), 'floor balanced in bⱼ/(1 − zⱼ)');
  // The fit: with ρ̂ > 0, bNeg, zOver1 and offBalance go to notes; τ̂² ≤ 0 stays a warning.
  const r = E.rng(32);
  let noted = 0;
  for (let k = 0; k < 200; k++) {
    const f = E.fitVC(E.draw(world, r).data), on = Object.keys(f.flags).filter((x) => f.flags[x]);
    assert.equal(f.warnings.length + f.notes.length, on.length);
    assert.equal(f.notes.length, on.filter((x) => f.expected[x]).length);
    if (f.rho > 0) for (const x of ['bNeg', 'zOver1', 'offBalance']) assert.ok(f.expected[x]);
    assert.ok(!f.expected.tauNeg);
    noted += f.notes.length;
  }
  assert.ok(noted > 0, 'some notes seen');
  const res = E.simulate(world, ['vc'], 300, 33).vc;
  assert.ok(res.expected.bNeg > 0.5 && res.expected.bNeg <= res.flags.bNeg, `expected negative b ${res.expected.bNeg}`);
});

test('corrBS: forcing exposure balance is not cheap (studies/vc-balance.js)', () => {
  const world = E.makeWorld({ rho: 0.6, noiseSpread: 1 }), r = E.rng(34), n = 600;
  const wt = world.w.map(sum);
  let e = 0, eb = 0, es = 0;
  for (let k = 0; k < n; k++) {
    const { levels, data } = E.draw(world, r), f = E.fitVC(data), m = f.means;
    const c = wt.map((x, j) => x * (1 - f.z[j])), mu = sum(c.map((x, j) => x * m[j])) / sum(c);
    const bal = m.map((x, j) => f.z[j] * x + (1 - f.z[j]) * mu);
    const fac = sum(wt.map((x, j) => x * m[j])) / sum(wt.map((x, j) => x * f.rates[j]));
    e += E.weightedSE(data, f.rates, levels); eb += E.weightedSE(data, bal, levels); es += E.weightedSE(data, f.rates.map((x) => x * fac), levels);
  }
  assert.ok(eb > 1.05 * e && es > 1.05 * e, `unbalanced ${e / n}, BS-style ${eb / n}, rescaled ${es / n}`);
});

// ---------------------------------------------------------------- the premium step (PLAN G6)

test('Premium: the world’s next-year draw matches the forecast MSE on average (Core.Estimates.mse_forecast)', () => {
  for (const [params, factor, seed] of [[{}, 1, 41], [{ rho: 0.6, noiseSpread: 1 }, 1, 42], [{ rho: 0.3, J: 5, T: 4 }, 0.4, 43]]) {
    const world = E.makeWorld(params), fl = E.floorBlend(world), n = 6000;
    const wNext = world.w.map((row) => factor * sum(row) / world.T);
    const theory = E.floorForecast(world, wNext), r = E.rng(seed), rn = E.rng(seed + 1000);
    const se = new Array(world.J).fill(0);
    let tot = 0;
    const wt = world.w.map(sum), wall = sum(wt);
    for (let k = 0; k < n; k++) {
      const { levels, data } = E.draw(world, r), Y = E.drawNext(world, levels, wNext, rn), rates = fl.apply(data).rates;
      rates.forEach((x, j) => { se[j] += (x - Y[j]) ** 2; tot += wt[j] * (x - Y[j]) ** 2 / wall; });
    }
    // Level part is the true level MSE; the rest is next year's noise σⱼ²/wⱼ,next.
    theory.mse.forEach((m, j) => {
      close(m - theory.level[j], world.truth.sigmaj2[j] / wNext[j], 1e-12, `noise part ${j}`);
      close(se[j] / n, m, 0.1, `region ${j}, ${JSON.stringify(params)}`);
    });
    const agg = sum(theory.mse.map((m, j) => wt[j] * m)) / wall;
    close(tot / n, agg, 0.04, `weighted, ${JSON.stringify(params)}`);
    // simulate() reports the same comparison, and its level results are unchanged by it.
    const res = E.simulate(world, ['vc'], 1500, seed, factor);
    close(res.floor.ftheory, agg, 1e-12, 'ftheory');
    close(res.floor.fmse, agg, 0.08, 'simulate fmse');
    assert.ok(res.vc.fmse >= res.floor.fmse * 0.97, `fit ${res.vc.fmse} vs floor ${res.floor.fmse}`);
  }
});

test('Premium step: premium = rates, forecast = plug-in level MSE + σ̂ⱼ²/wⱼ,next', () => {
  const world = E.makeWorld({ rho: 0.4 }), { data } = E.draw(world, E.rng(44)), wt = data.w.map(sum);
  const wn = E.nextVolumes(data, 2);
  wn.forEach((x, j) => close(x, 2 * wt[j] / world.T, 1e-12, 'next volume'));
  const bs = E.fitBS(data), p = E.premium(bs, data, wn);
  assert.deepEqual(p.premium, bs.rates);
  p.noise.forEach((x, j) => close(x, bs.sigma2 / wn[j], 1e-12, 'BS noise σ̂²/w'));
  // BS level MSE in the classical closed form: (1 − zⱼ)τ²(1 + (1 − zⱼ)/z*).
  const zs = sum(bs.z);
  p.level.forEach((g, j) => close(g, (1 - bs.z[j]) * bs.tau2 * (1 + (1 - bs.z[j]) / zs), 1e-9, 'BS level MSE'));
  const vc = E.fitVC(data), jk = E.jackknifeMSEP(data), pv = E.premium(vc, data, wn, jk.msep);
  pv.mse.forEach((m, j) => close(m, jk.msep[j] + vc.sigma2[j] / wn[j], 1e-12, 'vc forecast'));
  assert.equal(E.premium(E.fitOwn(data), data, wn), null);
});

// ---------------------------------------------------------------- exact checks of study numbers
// studies/exact-balance.js: the floor and its balanced corrections are linear rules, so their error
// is a formula in K and τ² (no simulation). These tests tie the documented numbers to it.
const X = require('../studies/exact-balance.js');

test('Exact floor error equals the engine\'s blendMSE, weighted (studies/exact-balance.js)', () => {
  for (const { params } of X.worlds()) {
    const r = X.exactRow(params), { fl, wt, t2 } = r;
    const viaEngine = wt.reduce((s, w, j) => s + w * E.blendMSE(fl.K, t2, fl.b, fl.s2, j, fl.z[j]), 0) / wt.reduce((s, w) => s + w, 0);
    assert.ok(Math.abs(r.floor - viaEngine) < 1e-9 * viaEngine, `${r.floor} vs ${viaEngine}`);
  }
});

test('Exact floor and shift errors agree with simulation within 4 standard errors (one world)', () => {
  const params = { J: 8, T: 10, rho: 0.6, noiseSpread: 1 }, r = X.exactRow(params);
  const world = E.makeWorld(params), fl = E.floorBlend(world), rng = E.rng(11), N = 2000;
  const wt = world.w.map((w) => w.reduce((s, x) => s + x, 0)), W = wt.reduce((s, x) => s + x, 0);
  const A = X.shiftMatrix(X.blendMatrix(fl.z, fl.b), wt);
  const f = [], s = [];
  for (let n = 0; n < N; n++) {
    const { levels, data } = E.draw(world, rng), m = E.cohortMeans(data).m;
    f.push(E.weightedSE(data, fl.apply(data).rates, levels));
    s.push(E.weightedSE(data, A.map((row) => row.reduce((t, a, i) => t + a * m[i], 0)), levels));
  }
  const chk = (xs, exact) => {
    const mean = xs.reduce((t, x) => t + x, 0) / N, sd = Math.sqrt(xs.reduce((t, x) => t + (x - mean) ** 2, 0) / (N - 1));
    assert.ok(Math.abs(mean - exact) < 4 * sd / Math.sqrt(N), `simulated ${mean} vs exact ${exact}`);
  };
  chk(f, r.floor); chk(s, r.floor * r.shift / 100);
  assert.ok(W > 0);
});

test('Documented balance costs are the exact ones (FINDINGS 15, S28): change the docs if this fails', () => {
  const rows = X.worlds().map(({ params }) => X.exactRow(params));
  assert.equal(Math.round(Math.max(...rows.map((r) => r.shift))), 141);   // shift: at most +41%
  assert.equal(Math.round(Math.max(...rows.map((r) => r.opt))), 196);     // best balanced blend: up to +96%
  const eq0 = X.worlds().map((w, i) => [w, rows[i]]).filter(([w]) => w.params.rho === 0 && w.params.noiseSpread === 0);
  for (const [, r] of eq0) { assert.ok(Math.abs(r.shift - 100) < 1e-6); assert.ok(Math.abs(r.opt - 100) < 1e-6); }
  assert.ok(rows.every((r, i) => (X.worlds()[i].params.rho > 0) === (r.minB < 0)));  // S27: b < 0 iff ρ > 0
  assert.ok(rows.every((r) => r.maxZ < 1));                                          // S29: the floor has z < 1
});

// ---------------------------------------------------------------- Findings 17–20: the best linear predictor and the price of correlation

/** Finding 16/18/19 example: τ² = 1, v = (0.5, 1, 3), noise correlation 0.5. */
const exampleK = () => {
  const v = [0.5, 1, 3];
  return v.map((vi, i) => v.map((vk, k) => (i === k ? 1 + vi : 0.5 * Math.sqrt(vi * vk))));
};

test('BLUP weights sum to 1, are optimal, and MSE(d) = MSE(d*) + (d − d*)ᵀK(d − d*) (Core.blupWeight_optimal, linMse_eq_blupWeight_add)', () => {
  const r = E.rng(31);
  for (let rep = 0; rep < 20; rep++) {
    const K = E.trueK(E.makeWorld({ J: 2 + (rep % 6), rho: 0.8 * r(), noiseSpread: r(), tau: 0.02 + 0.2 * r() })), tau2 = K[0][0] - K[0][0] + (0.02 + 0.2 * r()) ** 2;
    const J = K.length, j = rep % J, d = E.blupWeight(K, tau2, j), best = E.linMse(K, tau2, j, d);
    assert.ok(Math.abs(d.reduce((s, x) => s + x, 0) - 1) < 1e-10);
    for (let k = 0; k < 5; k++) {
      const h = Array.from({ length: J }, () => r() - 0.5), m = h.reduce((s, x) => s + x, 0) / J;
      const e = d.map((x, i) => x + h[i] - m), diff = e.map((x, i) => x - d[i]);
      close(E.linMse(K, tau2, j, e), best + E.linMse(K, 0, j, diff), 1e-9, 'value');
      assert.ok(E.linMse(K, tau2, j, e) >= best - 1e-12);
    }
  }
});

test('The blend as weights has the blend’s MSE, and is the BLUP for two cohorts (Core.linMse_blendWeight, exists_blendWeight_eq_blupWeight_iff)', () => {
  const K = exampleK(), { b, z, s2 } = E.bestBlendWeights(K, 1);
  for (let j = 0; j < 3; j++) close(E.linMse(K, 1, j, E.blendWeight(z[j], b, j)), E.blendMSE(K, 1, b, s2, j, z[j]), 1e-12, 'value');
  const K2 = [[1.5, 0.4], [0.4, 3]], f = E.bestBlendWeights(K2, 1);
  for (let j = 0; j < 2; j++) {
    const w = E.blendWeight(f.z[j], f.b, j), d = E.blupWeight(K2, 1, j);
    w.forEach((x, i) => close(x, d[i], 1e-12, 'value'));
  }
});

test('Diagonal K: the BLUP is the blend with z = τ²/(τ² + vⱼ) and inverse-variance b (Core.blupWeight_diag_eq_blendWeight)', () => {
  const v = [0.5, 1, 3, 0.2], tau2 = 0.7, K = v.map((vi, i) => v.map((_, k) => (i === k ? tau2 + vi : 0)));
  const inv = v.map((x) => 1 / (tau2 + x)), tot = inv.reduce((s, x) => s + x, 0), b = inv.map((x) => x / tot);
  for (let j = 0; j < v.length; j++) {
    const d = E.blupWeight(K, tau2, j), w = E.blendWeight(tau2 / (tau2 + v[j]), b, j);
    d.forEach((x, i) => close(x, w[i], 1e-12, 'value'));
  }
});

test('Finding 18–19 example: blend 2.8/3.1/0.1% and ignoring correlation 14.3/9.2/0.4% above the BLUP (pinned: change FINDINGS if this fails)', () => {
  const p = E.correlationPrice(exampleK(), 1, [1, 1, 1]);
  const pc = (a) => a.map((x, j) => Math.round(1000 * (x / p.best[j] - 1)) / 10);
  assert.deepEqual(p.best.map((x) => +x.toFixed(4)), [0.4827, 0.8404, 1.5470]);
  assert.deepEqual(p.blend.map((x) => +x.toFixed(4)), [0.4961, 0.8668, 1.5492]);
  assert.deepEqual(pc(p.blend), [2.8, 3.1, 0.1]);
  assert.deepEqual(pc(p.ignore), [14.3, 9.2, 0.4]);
  close(p.dm, 0.5, 1e-9, 'δ₋'); close(p.dp, 1, 1e-9, 'δ₊');   // J = 3, r = 0.5: δ₋ = r, δ₊ = 2r
  close(p.bound, 1.5625, 1e-9, 'value');                        // Finding 20: (2 + r)²/(4(1 − r)(1 + 2r))
});

test('Equal correlations: δ₋ = r, δ₊ = (J − 1)r and the closed form bound (Core.linMse_ignoreCorr_equicorr_le)', () => {
  for (const [J, r] of [[2, 0.5], [3, 0.5], [8, 0.6], [20, 0.3]]) {
    const R = Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, k) => (i === k ? 1 : r)));
    const { dm, dp } = E.noiseDeltas(R);
    close(dm, r, 1e-9, `δ₋ J=${J}`); close(dp, (J - 1) * r, 1e-9, `δ₊ J=${J}`);
    const closed = (2 + (J - 2) * r) ** 2 / (4 * (1 - r) * (1 + (J - 1) * r));
    close(E.dampedBound(dm, dp, 0), closed, 1e-12, 'value');
    if (J === 2) close(closed, 1 / (1 - r * r), 1e-12, 'value');
  }
  close(E.dampedBound(0.5, 1, 0.5), 1.125, 1e-12, 'value');   // Finding 20: halfway damping at J = 3, r = 0.5 → 12.5%
  assert.equal(E.dampedBound(0.5, 1, 1), 1);
});

test('Ignoring correlation and damping never cost more than the bound, in app worlds (Core.linMse_damped_le)', () => {
  const r = E.rng(77);
  for (let rep = 0; rep < 40; rep++) {
    const world = E.makeWorld({ J: 2 + (rep % 10), rho: 0.9 * r(), noiseSpread: 1.5 * r(), spread: 2 * r(), tau: 0.01 + 0.2 * r() });
    const K = E.trueK(world), tau2 = world.truth.tau2, p = E.worldPrice(world);
    for (let j = 0; j < world.J; j++) {
      assert.ok(p.best[j] <= p.blend[j] + 1e-15 && p.blend[j] <= p.ignore[j] * (1 + 1e-12) + 1e-15 || p.best[j] <= p.ignore[j] + 1e-15);
      assert.ok(p.ignore[j] <= p.bound * p.best[j] * (1 + 1e-9), `ignore, rep ${rep}`);
      const theta = r(), Kt = K.map((row, i) => row.map((x, k) => (i === k ? x : theta * x)));
      const md = E.linMse(K, tau2, j, E.blupWeight(Kt, tau2, j));
      assert.ok(md <= E.dampedBound(p.dm, p.dp, theta) * p.best[j] * (1 + 1e-9), `damped, rep ${rep}`);
    }
  }
});

test('Indicator from data: δ̂ = 0 when ρ̂ = 0, bound 1 for a fit that keeps the correlation (θ = 1)', () => {
  const world = E.makeWorld({ rho: 0 });
  let zeros = 0;
  for (let k = 0; k < 20; k++) {
    const { data } = E.draw(world, E.rng(500 + k)), ind = E.correlationIndicator(data, 1);
    assert.equal(ind.damped, 1);
    if (ind.rho === 0) { zeros++; assert.ok(ind.dm < 1e-12 && ind.dp < 1e-12 && Math.abs(ind.ignore - 1) < 1e-12); }
  }
  assert.ok(zeros > 0);
});

test('Plug-in BLUP: weights from corrBS’s K̂, rates Σ d̂ᵢμ̂ᵢ, equal to the blend for J = 2', () => {
  const world = E.makeWorld({ J: 2, rho: 0.4 }), { data } = E.draw(world, E.rng(3));
  const b = E.fitBLUP(data), v = E.fitVC(data);
  b.rates.forEach((x, j) => close(x, v.rates[j], 1e-10, 'value'));
  const w8 = E.makeWorld({ rho: 0.6 }), d8 = E.draw(w8, E.rng(4)).data, f = E.fitBLUP(d8);
  f.rates.forEach((x, j) => { const d = E.blupWeight(f.K, f.tau2, j); close(x, d.reduce((s, y, i) => s + y * f.means[i], 0), 1e-12, 'value'); });
  const pr = E.premium(f, d8, E.nextVolumes(d8, 1));
  pr.level.forEach((g, j) => close(g, f.levelMSE[j], 1e-15, 'value'));
});

test('Floor BLUP in simulation is at most the blend floor, and matches its true MSE (Core.Estimates.blup_mse_optimal)', () => {
  const world = E.makeWorld({ rho: 0.6 }), res = E.simulate(world, ['bs'], 3000, 99), p = E.worldPrice(world);
  assert.ok(res.floorBlup.mse < res.floor.mse);
  assert.ok(Math.abs(res.floorBlup.mse - p.weighted.best) < 4 * res.floorBlup.se);
  assert.ok(Math.abs(res.floor.mse - p.weighted.blend) < 4 * res.floor.se);
});

test('z < 0 is flagged as a warning (Finding 17), not as an expected note', () => {
  const r = E.rng(5);
  let seen = 0;
  for (let k = 0; k < 400 && seen < 3; k++) {
    const world = E.makeWorld({ J: 3, T: 4, rho: 0.85, spread: 2, noiseSpread: 1.5 });
    const { data } = E.draw(world, r);
    for (const f of [E.fitVC(data), E.fitCorr(data)]) {
      assert.equal(!!f.flags.zNeg, f.z.some((x) => x < 0));
      if (f.flags.zNeg) { seen++; assert.ok(f.warnings.some((w) => w.startsWith('z < 0'))); }
    }
  }
  assert.ok(seen > 0, 'no z < 0 in 400 draws: pick a harsher world');
});

// ---------------------------------------------------------------- the Recipe section

test('Recipes match the fits: same steps, formulas and badges (one formula table F)', () => {
  const cases = [[{ rho: 0.3 }, 15], [{ rho: 0 }, 2], [{ rho: 0.6, noiseSpread: 1 }, 7], [{ tau: 0.005, J: 4, T: 3 }, 3]];
  for (const [params, seed] of cases) {
    const world = E.makeWorld(params), { data } = E.draw(world, E.rng(seed));
    for (const [id, m] of Object.entries(E.MODELS)) {
      const r = E.RECIPES[id];
      assert.ok(r && r.intro && r.steps.length, `${id}: no recipe`);
      const fit = m.fit(data), pr = E.premium(fit, data, E.nextVolumes(data));
      const steps = fit.steps.concat(pr ? [pr.step] : []);
      if (!steps.length) continue;   // own, pool: no estimation steps on the page
      assert.deepEqual(r.steps.map((s) => s.name).sort(), steps.map((s) => s.name).sort(), `${id}: step names`);
      for (const s of steps) {
        const rs = r.steps.find((x) => x.name === s.name);
        assert.ok(s.formula.startsWith(rs.formula), `${id}/${s.name}: formula differs from the recipe`);
        if (!rs.varies) {
          assert.equal(rs.badge, s.badge, `${id}/${s.name}: badge`);
          assert.equal(rs.lean || null, s.lean || null, `${id}/${s.name}: Lean name`);
        }
      }
    }
  }
});

test('Recipes: every symbol is defined (notation or an earlier formula), every proved step names a proved declaration', () => {
  const path = require('node:path'), { execFileSync } = require('node:child_process');
  const proved = new Set(execFileSync('python3', [path.join(__dirname, '..', 'scripts', 'progress.py'), '--proved'],
    { encoding: 'utf8' }).split(/\s+/).filter(Boolean));
  // Symbols a reader cannot know without a definition, and how a step defines them.
  const SYMBOLS = ['μ̄', 'Sᵢⱼ', 'Qᵢⱼ', 'Σ̂ᵢⱼ', 'v̂ⱼ', 'δᵢⱼ', ' eⱼ', 'z*', 'τ̂²⁺', 'w**', 'wⱼ*', 's²', 'ĉⱼ', 'ζⱼ', 'Wⱼ', 'β²', 'σ̃ⱼ', 'uⱼₜ', 'ℓ', 'θ', 'σ̂ⱼ²', 'd̂', 'wⱼ,next', 'MSEⱼ', 'Aⱼ', 'Bⱼ', 'Cⱼ'];
  for (const id of Object.keys(E.MODELS)) {
    const r = E.RECIPES[id], notes = E.recipeNotation(id).map((n) => n.sym + ' ' + n.text).join(' ');
    const texts = r.steps.map((s) => [s.formula, s.rule || '', s.note || ''].join(' ')).join(' ');
    for (const sym of SYMBOLS) {
      if (!texts.includes(sym)) continue;
      const defined = notes.includes(sym) || new RegExp(`(^|[ ,;(:])${sym.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}[^ ]{0,3} =`).test(texts) ||
        (sym === 'θ' && /θ = the largest/.test(texts)) || (sym === 'σ̃ⱼ' && texts.includes('σ̃ⱼ² ='));
      assert.ok(defined, `${id}: ${sym} is used but not defined`);
    }
    for (const s of r.steps) {
      if (s.badge === 'proved') assert.ok(proved.has(s.lean), `${id}/${s.name}: ${s.lean} is not a proved declaration`);
      else assert.ok(s.gap, `${id}/${s.name}: no gap named`);
    }
    assert.ok(E.recipeText(id).includes(r.steps[0].formula), `${id}: text export`);
  }
});

test('toCSV writes the data the fit sees, one row per region and year', () => {
  const w = E.makeWorld({ J: 3, T: 4 }), { data } = E.draw(w, E.rng(1)), lines = E.toCSV(data).trim().split('\n');
  assert.equal(lines[0], 'region,year,volume,ratio');
  assert.equal(lines.length, 1 + 3 * 4);
  const [j, t, v, x] = lines[5].split(',').map(Number);
  assert.ok(Math.abs(v - data.w[j - 1][t - 1]) < 1e-6 * v && Math.abs(x - data.X[j - 1][t - 1]) < 1e-9, 'values round-trip');
});

test('Excess over the oracle BLUP splits into E B² + 2E[AB] (Core.Target.integral_sq_plugIn); the cross term is 0 under normal noise (plugIn_mse_of_normal), not in the gamma world', () => {
  for (const [p, seed] of [[{}, 7], [{ normal: true }, 1], [{ rho: 0.6, normal: true }, 2], [{ T: 4, levelShape: 1, noiseShape: 1 }, 7]]) {
    const world = E.makeWorld(p), res = E.simulate(world, ['blup', 'bs'], 3000, seed);
    for (const id of ['blup', 'bs']) {
      const s = res[id].split;
      close(res[id].mse - res.floorBlup.mse, s.b2 + s.cross, 1e-10, `identity ${id} ${JSON.stringify(p)}`);
      assert.ok(s.b2 > 0);
    }
    const s = res.blup.split;
    if (p.normal) {
      assert.ok(Math.abs(s.cross) < 4 * s.crossSe, `normal: cross ${s.cross} ± ${s.crossSe}`);
      assert.ok(Math.abs(s.cross) < 0.15 * s.b2, `normal: cross ${s.cross} small against E B² ${s.b2}`);
    } else {
      assert.ok(s.cross < -4 * s.crossSe, `gamma: cross ${s.cross} ± ${s.crossSe} clearly negative`);
    }
  }
  // The normal switch draws normal levels: no skew in the level draws.
  const r = E.rng(3), wn = E.makeWorld({ normal: true, J: 3 }), lv = [];
  for (let k = 0; k < 4000; k++) lv.push(...E.draw(wn, r).levels);
  const m = lv.reduce((a, x) => a + x, 0) / lv.length, sd = Math.sqrt(lv.reduce((a, x) => a + (x - m) ** 2, 0) / lv.length);
  const skew = lv.reduce((a, x) => a + ((x - m) / sd) ** 3, 0) / lv.length;
  assert.ok(Math.abs(skew) < 0.1, `skew ${skew}`);
});

test('Plug-in bias: the BLUP on corrBS K̂ is even and translation invariant, so unbiased under normal noise (blup_plugIn_unbiased_of_symmetric); under gamma noise it prices low, BS and the oracle do not', () => {
  // Hypotheses of the theorem: data X → c + X shifts every rate by c; X → −X flips them (K̂ even).
  const world = E.makeWorld({ rho: 0.4, noiseSpread: 1 }), { data } = E.draw(world, E.rng(8)), f = E.fitBLUP(data);
  const shift = E.fitBLUP({ w: data.w, X: data.X.map((row) => row.map((x) => x + 0.37)) });
  const flip = E.fitBLUP({ w: data.w, X: data.X.map((row) => row.map((x) => -x)) });
  f.rates.forEach((x, j) => { close(shift.rates[j], x + 0.37, 1e-10, `shift ${j}`); close(flip.rates[j], -x, 1e-10, `flip ${j}`); });
  for (const [p, seed] of [[{ normal: true }, 5], [{ normal: true, T: 4, rho: 0.6 }, 6], [{ T: 4, levelShape: 1, noiseShape: 1 }, 5]]) {
    const res = E.simulate(E.makeWorld(p), ['blup', 'bs'], 3000, seed), b = res.blup.bias;
    for (const id of ['floorBlup', 'bs']) assert.ok(Math.abs(res[id].bias.mean) < 4 * res[id].bias.se, `${id} unbiased ${JSON.stringify(p)}`);
    if (p.normal) b.region.forEach((m, j) => assert.ok(Math.abs(m) < 4 * b.regionSe[j], `normal: region ${j} ${m} ± ${b.regionSe[j]}`));
    else assert.ok(b.mean < -10 * b.se, `gamma: ${b.mean} ± ${b.se} clearly negative`);
  }
});

test('Finding 35 remedies: BLUP balanced by a common shift (exact exposure balance, linear weights summing to 1) and BLUP with a pooled σ̂²; both remove the under-pricing without correlation', () => {
  const world = E.makeWorld({ rho: 0.4, noiseSpread: 1 }), { data } = E.draw(world, E.rng(9));
  const wt = data.w.map(sum), m = E.cohortMeans(data).m, f = E.fitBLUPBal(data), base = E.fitBLUP(data);
  close(sum(wt.map((x, j) => x * f.rates[j])), sum(wt.map((x, j) => x * m[j])), 1e-12, 'balanced');
  f.rates.forEach((x, j) => close(x, base.rates[j] + f.shift, 1e-12, `common shift ${j}`));
  const g = wt.map((x, i) => (x - sum(m.map((_, k) => wt[k] * E.blupWeight(base.K, base.tau2, k)[i]))) / sum(wt));
  m.forEach((_, j) => {
    const d = E.blupWeight(base.K, base.tau2, j).map((x, i) => x + g[i]);
    close(sum(d), 1, 1e-12, `weights sum to 1, ${j}`);
    close(f.rates[j], sum(d.map((x, i) => x * m[i])), 1e-12, `linear ${j}`);
    close(f.levelMSE[j], E.linMse(base.K, base.tau2, j, d), 1e-12, `MSE ${j}`);
  });
  const pooled = E.vcEstimate(data, { pooled: true });
  pooled.s2.forEach((x) => close(x, pooled.pooled, 1e-12, 'one σ̃²'));
  const wd = E.makeWorld({ T: 4, levelShape: 1, noiseShape: 1 });
  const res = E.simulate(wd, ['blup', 'blupPool'], 2000, 21), rb = E.simulate(wd, ['blup'], 2000, 21, 1, { balance: true });
  assert.ok(res.blup.bias.mean < -10 * res.blup.bias.se, 'BLUP prices low');
  assert.ok(Math.abs(res.blupPool.bias.mean) < 4 * res.blupPool.bias.se, `pooled unbiased: ${res.blupPool.bias.mean}`);
  assert.ok(Math.abs(rb.blup.bias.mean) < 4 * rb.blup.bias.se, `balanced unbiased: ${rb.blup.bias.mean}`);
  assert.ok(res.blupPool.mse < res.blup.mse && rb.blup.mse < res.blup.mse, 'and more accurate here');
  close(rb.blup.raw.mse, res.blup.mse, 1e-12, 'raw MSE is the unbalanced fit');
});

test('Σcov(d̂ᵢ, μ̂ᵢ) over draws equals the simulated bias (Core.Estimates.integral_randomLin_sub); exactly 0 at the portfolio level for balanced fits (integral_portfolio_sub_of_balanced)', () => {
  const wd = E.makeWorld({ T: 4, levelShape: 1, noiseShape: 1 });
  const res = E.simulate(wd, ['blup', 'bs', 'own'], 2000, 21), rb = E.simulate(wd, ['blup', 'vc'], 2000, 21, 1, { balance: true });
  const c = res.blup.covDiag;
  assert.ok(Math.abs(c.ownW + c.otherW - res.blup.bias.mean) < 4 * res.blup.bias.se, `sum ${c.ownW + c.otherW} vs bias ${res.blup.bias.mean}`);
  assert.ok(c.otherW < -10 * res.blup.bias.se, 'the portfolio weights carry most of it');
  for (const d of [res.bs.covDiag, rb.blup.covDiag, rb.vc.covDiag]) assert.ok(Math.abs(d.ownW + d.otherW) < 1e-12, `balanced: ${d.ownW + d.otherW}`);
  assert.equal(res.own.covDiag, undefined, 'own: no z, b, weights');
  const f = E.fitBLUP(E.draw(E.makeWorld({}), E.rng(2)).data);
  E.weightsOf(f).forEach((d) => close(sum(d), 1, 1e-12, 'weights sum to 1'));
});

test('Balance switch: any fit shifted by one D is exposure-balanced, linear weights still sum to 1, plug-in MSE exact; already balanced models untouched; recipe gets the step', () => {
  const world = E.makeWorld({ rho: 0.5, noiseSpread: 1 }), { data } = E.draw(world, E.rng(12)), wt = data.w.map(sum), m = E.cohortMeans(data).m;
  for (const id of Object.keys(E.MODELS)) {
    const raw = E.MODELS[id].fit(data), f = E.fitWith(id, data, { balance: true });
    close(sum(wt.map((x, j) => x * f.rates[j])), sum(wt.map((x, j) => x * m[j])), 1e-10, `${id} balanced`);
    if (E.MODELS[id].balanced) { assert.deepEqual(f.rates, raw.rates, `${id} left alone`); assert.ok(!f.balanced); assert.equal(E.recipeSteps(id, { balance: true }), E.RECIPES[id].steps); continue; }
    f.rates.forEach((x, j) => close(x, raw.rates[j] + f.shift, 1e-12, `${id} common shift`));
    assert.ok(!f.flags.offBalance && !f.warnings.concat(f.notes).some((t) => /off-balance/.test(t)), `${id}: no off-balance message`);
    if (f.weights) f.weights.forEach((d, j) => { close(sum(d), 1, 1e-12, `${id} sum`); close(sum(d.map((x, i) => x * m[i])), f.rates[j], 1e-10, `${id} linear`);
      if (raw.K) close(f.levelMSE[j], E.linMse(raw.K, raw.tau2, j, d), 1e-12, `${id} MSE`); });
    const names = f.steps.map((x) => x.name), rs = E.recipeSteps(id, { balance: true }).map((x) => x.name);
    assert.equal(names[names.length - 1], 'balance');
    assert.deepEqual(rs.filter((x) => x !== 'premium').sort(), names.slice().sort(), `${id}: recipe steps`);
    assert.ok(E.recipeText(id, { balance: true }).includes(E.F.balance));
  }
});

test('Noise shape: κ̂ⱼ unbiased for the third cumulant (any distribution, q = 3/2), 0 under normal noise; cross-fitted variance power ≈ 0 where the same-years slope is biased up', () => {
  for (const [params, n] of [[{}, 2000], [{ T: 4, noiseShape: 1 }, 2000], [{ rho: 0.6 }, 1500], [{ normal: true }, 1500]]) {
    const world = E.makeWorld(params), r = E.rng(7), p = world.params;
    const a = Math.sqrt(p.rho), b = Math.sqrt(1 - p.rho), g = p.normal ? 0 : (a ** 3 + b ** 3) * 2 / Math.sqrt(p.noiseShape);
    const k = [], pw = [], ps = [];
    for (let i = 0; i < n; i++) {
      const D = E.noiseDiagnostics(E.draw(world, r).data);
      k.push(D.regions[0].kappa / world.truth.sigmaj2[0] ** 1.5);
      if (D.power) pw.push(D.power.b);
      if (D.powerSame) ps.push(D.powerSame.b);
    }
    const m = sum(k) / n, se = Math.sqrt(sum(k.map((v) => (v - m) ** 2)) / (n - 1) / n);
    assert.ok(Math.abs(m - g) < 4 * se, `${JSON.stringify(params)}: κ̂/σ³ ${m} ± ${se} vs ${g}`);
    assert.ok(pw.length > 0.95 * n, `power defined in ${pw.length} of ${n} draws (needs every μ̂ > 0)`);
    const np = pw.length, mp = sum(pw) / np, sp = Math.sqrt(sum(pw.map((v) => (v - mp) ** 2)) / (np - 1) / np);
    assert.ok(Math.abs(mp) < 0.15 && Math.abs(mp) < 6 * sp + 0.05, `power ${mp} ± ${sp}`);
    if (!p.normal && p.rho === 0) assert.ok(sum(ps) / ps.length > 1, `same-years slope biased up: ${sum(ps) / ps.length}`);
  }
});

test('Distance taper ρ^|tᵢ−tⱼ|: PSD for any positions, ties allowed (distTaper_posSemidef); K̂ ≻ 0 by posDef_distTaper_hadamard; ρ̂ by the damping study’s plug-in rule S3', () => {
  const r = E.rng(31);
  // The theorem: R(ρ, t) ⪰ 0 for ρ ∈ [0, 1] and any positions t ∈ ℕ (ties allowed).
  for (let k = 0; k < 300; k++) {
    const n = 1 + Math.floor(r() * 9), t = Array.from({ length: n }, () => Math.floor(r() * 5)), rho = k % 10 === 0 ? 1 : r();
    const R = E.distTaper(rho, n, t);
    assert.ok(E.eigSym(R)[0] > -1e-12, `PSD at ρ = ${rho}, t = ${t}`);
    R.forEach((row, i) => assert.equal(row[i], 1, 'unit diagonal'));
  }
  // With every pair at distance 1 the criterion's minimiser is S3's θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T − 1)).
  for (const [params, seed] of [[{ rho: 0.5 }, 1], [{ rho: 0.9, T: 5 }, 2], [{ rho: 0.1, J: 12 }, 3]]) {
    const { data } = E.draw(E.makeWorld(params), E.rng(seed)), { Sig } = E.sigmaHat(data), J = Sig.length, T = data.X[0].length;
    let s = 0, n = 0;
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
    const rb = s / n, th = rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1));
    assert.ok(Math.abs(E.taperRho(Sig, T, () => 1).rho - th) <= 0.0006, `S3 θ̂ ${th}`);
  }
  // The ordered world: corr(εᵢ, εⱼ) = ρ^|i−j|, in trueK and in the draws.
  const wo = E.makeWorld({ rho: 0.7, ordered: true, J: 5 });
  assert.equal(wo.truth.rho[0][3], Math.pow(0.7, 3));
  const acc = [0, 0, 0, 0], N = 20000;
  for (let k = 0; k < N; k++) { const e = E.orderedNoise(5, 0.7, r, 2, false); for (let d = 1; d <= 4; d++) acc[d - 1] += e[0] * e[d]; }
  acc.forEach((x, i) => close(x / N, Math.pow(0.7, i + 1), 0.04, `corr at distance ${i + 1}`));
  // The fit: K̂ = R(ρ̂) ⊙ (Σ̂ + τ̂²I) ≻ 0 in every draw; ρ̂ follows the world.
  for (const [params, lo, hi] of [[{ rho: 0 }, 0, 0.6], [{ rho: 0.8, ordered: true }, 0.6, 1], [{ rho: 0.8, ordered: true, J: 12, T: 4 }, 0.3, 1], [{ rho: 0.5 }, 0.5, 1]]) {
    const world = E.makeWorld(params);
    let mean = 0;
    for (let k = 0; k < 200; k++) {
      const { data } = E.draw(world, r), f = E.fitCorr(data, { taper: 'distance' }), est = E.sigmaHat(data);
      assert.ok(E.cholesky(f.K), 'K̂ ≻ 0');
      assert.ok(f.rhoTaper >= 0 && f.rhoTaper <= f.rhoFit && f.rhoFit <= 1, 'ρ ∈ [0, ρ̂]');
      const R = E.distTaper(f.rhoTaper, f.K.length);
      f.K.forEach((row, i) => row.forEach((x, j) => close(x, R[i][j] * (est.Sig[i][j] + (i === j ? f.tau2 : 0)), 1e-12, 'K̂ = R ⊙ (Σ̂ + τ̂²I)')));
      const step = f.steps.find((s) => s.name === 'tapered K̂');
      if (E.isPSD(est.Sig) && f.tau2 > 0) {
        assert.equal(step.badge, 'proved');
        const Kraw = est.Sig.map((row, i) => row.map((y, j) => y + (i === j ? f.tau2 : 0)));
        for (const x of [0, 0.3, 0.9, 1]) {
          const Rx = E.distTaper(x, R.length);
          assert.ok(E.cholesky(Kraw.map((row, i) => row.map((y, j) => Rx[i][j] * y))), `≻ 0 at ρ = ${x}`);
        }
      }
      mean += f.rhoFit / 200;
    }
    assert.ok(mean >= lo && mean <= hi, `${JSON.stringify(params)}: mean ρ̂ ${mean} in [${lo}, ${hi}]`);
  }
});

test('Lomax claims world: moments of the claim (recursion E Yⁿ⁺¹/E Yⁿ = (n+1)/(α−n−1)), the claim rate keeps mean μ and variance σⱼ²', () => {
  for (const a of [2.5, 3.5, 6]) {
    const M = E.lomaxMoments(a);
    close(M.m2 / M.m1, 2 / (a - 2), 1e-12, 'm2/m1');
    if (a > 3) close(M.m3 / M.m2, 3 / (a - 3), 1e-12, 'm3/m2'); else assert.equal(M.m3, Infinity);
    if (a > 4) close(M.m4 / M.m3, 4 / (a - 4), 1e-12, 'm4/m3'); else assert.equal(M.m4, Infinity);
    const world = E.makeWorld({ lomax: a, noiseSpread: 1 });
    for (let j = 0; j < world.J; j++) {
      const lam = E.claimRate(world, j), sc = world.truth.sigmaj2[j] * M.m1 / (world.truth.mu * M.m2);
      close(lam * sc * M.m1, world.truth.mu, 1e-12, 'mean per vehicle-year');
      close(lam * sc * sc * M.m2, world.truth.sigmaj2[j], 1e-12, 'variance per vehicle-year');
    }
  }
  const w = E.makeWorld({ lomax: 3 });
  assert.ok(Math.abs(E.claimRate(w, 0) - 0.111) < 0.001, 'σ = 6, α = 3: about 0.11 claims per vehicle-year');
});

test('Lomax claim noise has mean 0, variance 1 and the compound Poisson skewness, exactly drawn (n ≤ 200) and split (n > 200)', () => {
  const a = 8, M = E.lomaxMoments(a), r = E.rng(21);
  for (const [n, N] of [[20, 60000], [150, 30000], [2000, 30000]]) {
    let s = 0, ss = 0, s3 = 0;
    for (let k = 0; k < N; k++) { const x = E.claimNoise(r, n, a); s += x; ss += x * x; s3 += x * x * x; }
    const m = s / N, v = ss / N - m * m, g = (s3 / N - 3 * m * v - m ** 3) / v ** 1.5;
    const skew = M.m3 / (Math.sqrt(n) * M.m2 ** 1.5);
    assert.ok(Math.abs(m) < 4 / Math.sqrt(N), `n = ${n}: mean ${m}`);
    assert.ok(Math.abs(v - 1) < 0.04, `n = ${n}: variance ${v}`);
    assert.ok(Math.abs(g - skew) < 0.25 * skew + 0.05, `n = ${n}: skewness ${g} vs ${skew}`);
  }
});

test('Lomax claims world: the floor MSE is unchanged (only two moments enter), and heavy tails (α = 3) run through every fit', () => {
  const world = E.makeWorld({ lomax: 6, rho: 0.5 }), fl = E.floorBlend(world), tau2 = world.truth.tau2;
  const wt = world.w.map(sum), wall = sum(wt);
  const exact = sum(wt.map((x, j) => x * E.blendMSE(fl.K, tau2, fl.b, fl.s2, j, fl.z[j]))) / wall;
  const sim = E.simulate(world, [], 8000, 4).floor;
  assert.ok(Math.abs(sim.mse - exact) < 4 * sim.se, `${sim.mse} ± ${sim.se} vs ${exact}`);
  for (const p of [{ lomax: 3 }, { lomax: 2.2, rho: 0.5, ordered: true, spread: 2, volume: 5000 }]) {
    const res = E.simulate(E.makeWorld(p), ['bs', 'vc', 'blup'], 30, 9);
    for (const [id, x] of Object.entries(res)) if (x && typeof x.mse === 'number') assert.ok(Number.isFinite(x.mse), `${JSON.stringify(p)} ${id}: ${x.mse}`);
  }
});

test('corr damps by S3’s θ̂ = r̄²/(r̄² + (1 − r̄²)²/(T − 1)), lowered only if K̂ is not ≻ 0; the old grid rule stays as thetaRule "grid"', () => {
  const r = E.rng(41);
  for (const params of [{}, { rho: 0.6 }, { rho: 0.9, T: 5 }, { J: 12, rho: 0.3 }]) {
    const world = E.makeWorld(params);
    for (let k = 0; k < 100; k++) {
      const { data } = E.draw(world, r), { Sig } = E.sigmaHat(data), J = Sig.length, T = data.X[0].length;
      let s = 0, n = 0;
      for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s += Sig[i][j] / Math.sqrt(Sig[i][i] * Sig[j][j]); n++; }
      const rb = Math.max(-1, Math.min(1, s / n)), th = Math.min(rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1)), 0.999);
      const f = E.fitCorr(data);
      assert.ok(Math.abs(f.thetaFit - th) <= 0.0006, `θ̂ ${f.thetaFit} vs ${th}`);
      assert.ok(f.theta <= f.thetaFit && f.theta >= 0 && E.cholesky(f.K), 'lowered only as needed, K̂ ≻ 0');
      if (f.theta < f.thetaFit) assert.ok(!E.cholesky(E.shrinkOffDiag(f.theta + 0.05, Sig).map((row, i) => row.map((x, j) => x + (i === j ? f.tau2 : 0)))), 'one step up fails');
      const g = E.fitCorr(data, { thetaRule: 'grid' });
      assert.ok(E.THETAS.includes(g.theta));
    }
  }
});

test('BLUP taper: the BLUP (Core.blupWeight_optimal) on corr taper’s K̂; beats BLUP on corrBS’s K̂ with many ordered regions (studies S36)', () => {
  const r = E.rng(51), sum = (a) => a.reduce((s, x) => s + x, 0);
  const { data } = E.draw(E.makeWorld({ rho: 0.7, ordered: true }), r);
  const f = E.fitBLUPTaper(data), base = E.fitCorr(data, { taper: 'distance' });
  f.rates.forEach((x, j) => close(x, sum(E.blupWeight(base.K, base.tau2, j).map((d, i) => d * base.means[i])), 1e-12, `rate ${j}`));
  f.weights.forEach((d) => close(sum(d), 1, 1e-12, 'weights sum to 1'));
  const world = E.makeWorld({ J: 20, rho: 0.9, ordered: true });
  let a = 0, b = 0;
  for (let k = 0; k < 150; k++) {
    const { levels, data: d } = E.draw(world, r);
    a += E.weightedSE(d, E.fitBLUPTaper(d).rates, levels); b += E.weightedSE(d, E.fitBLUP(d).rates, levels);
  }
  assert.ok(a < 0.9 * b, `BLUP taper ${a} vs BLUP ${b}`);
});

test('G2 V: exact Var Σ̂ᵢⱼ (sigmaHatVar); unit weights give variance_crossResid’s closed form; matches Monte Carlo with the shock kurtosis', () => {
  // Closed form of Cumulants.variance_crossResid (D = 1): Σₜₜ' [GⁱⁱGʲʲ + GⁱʲGʲⁱ] + Σₛ (1 − aᵢₛ − aⱼₛ + T aᵢₛaⱼₛ)² kₛᵢⱼᵢⱼ.
  const world = E.makeWorld({ J: 4, T: 5, rho: 0.5, noiseSpread: 1, spread: 1.5 }), { w, J, T } = world;
  const sd = world.truth.sigmaj2.map(Math.sqrt), cov = sd.map((a, i) => sd.map((b, j) => (i === j ? a * a : 0.5 * a * b)));
  const kappa = 3, wt = w.map(sum), a = (i, s) => w[i][s] / wt[i], dl = (t, s) => (t === s ? 1 : 0);
  const N = (s, b, c) => cov[b][c] / Math.sqrt(w[b][s] * w[c][s]);
  const resCross = (b, c, t, t2) => sum(Array.from({ length: T }, (_, s) => (dl(t, s) - a(b, s)) * (dl(t2, s) - a(c, s)) * N(s, b, c)));
  const V = E.sigmaHatVar(w, cov, kappa, true);
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) {
    let q = 0;
    for (let t = 0; t < T; t++) for (let t2 = 0; t2 < T; t2++) q += resCross(i, i, t, t2) * resCross(j, j, t, t2) + resCross(i, j, t, t2) * resCross(j, i, t, t2);
    for (let s = 0; s < T; s++) q += (1 - a(i, s) - a(j, s) + T * a(i, s) * a(j, s)) ** 2 * kappa * N(s, i, j) ** 2;
    close(V[i][j], q, 1e-10, `crossResid ${i}${j}`);
  }
  // Monte Carlo on the app's weighted Σ̂ (eq. (39)), gamma world: shock kurtosis 6/k = 3.
  const g = E.makeWorld({ rho: 0.6, T: 5 }), gs = g.truth.sigmaj2.map(Math.sqrt);
  const gc = gs.map((x, i) => gs.map((y, j) => (i === j ? x * x : 0.6 * x * y)));
  const Vg = E.sigmaHatVar(g.w, gc, 3), r = E.rng(5), M = 20000;
  let m = 0, m2 = 0;
  for (let k = 0; k < M; k++) { const x = E.sigmaHat(E.draw(g, r).data).Sig[0][1]; m += x; m2 += x * x; }
  const v = m2 / M - (m / M) ** 2;
  assert.ok(Math.abs(v / Vg[0][1] - 1) < 0.08 && v > 1.25 * E.sigmaHatVar(g.w, gc, 0)[0][1], `MC ${v} vs ${Vg[0][1]}`);
  // covTheta with the true table: θ* = Σs²/(Σs² + ΣV) (Damping.bestTheta), in (0, 1); κ lowers it.
  const d = E.draw(g, r).data, t0 = E.covTheta(d, 0, { cov: gc }).theta, t3 = E.covTheta(d, 3, { cov: gc }).theta;
  assert.ok(t0 > t3 && t3 > 0 && t0 < 1);
  assert.ok(E.fitCorr(d, { thetaRule: 'cov' }).thetaFit <= 0.999);
});

test('G2: delta-method Var r̂ᵢⱼ (corrVar) from the exact covariances of Σ̂; normal theory gives S3’s (1 − r²)²/(T − 1) when balanced; κ raises it', () => {
  const world = E.makeWorld({ J: 5, T: 10, rho: 0.6, spread: 0, growth: 0 }), sd = world.truth.sigmaj2.map(Math.sqrt);
  const M0 = E.sigmaHatMoments(world.w, sd, 0.6, 0, null);
  close(E.corrVar(M0, 0, 1), (1 - 0.36) ** 2 / 9, 1e-9, 'balanced normal = S3');
  const cov = sd.map((a, i) => sd.map((b, j) => (i === j ? a * a : 0.6 * a * b)));
  const M = E.sigmaHatMoments(world.w, sd, 0.6, 3, () => 3);
  close(M.cv(0, 1, 0, 1), E.sigmaHatVar(world.w, cov, 3)[0][1], 1e-10, 'cv = sigmaHatVar for i ≠ j');
  assert.ok(E.corrVar(M, 0, 1) > 1.3 * E.corrVar(M0, 0, 1));
  // corrTheta with κ = 0 is S3's θ̂ in a balanced world.
  const d = E.draw(world, E.rng(9)).data, t = E.corrTheta(d), rb = t.rbar;
  if (rb > 0) close(t.theta, rb * rb / (rb * rb + (1 - rb * rb) ** 2 / 9), 1e-9, 'κ = 0: S3');
});

test('Noise shape: the skew channel cov(σ̂ⱼ², μ̂ⱼ) = Σₛ aₛkₛ Σₜ cₜ(δₜₛ − aₛ)² (Cumulants.covariance_resVar_mean) against Monte Carlo; 0 for normal noise', () => {
  const world = E.makeWorld({}), j = 2, s2 = world.truth.sigmaj2[j], k = Math.pow(s2, 1.5) * 2 / Math.sqrt(world.params.noiseShape);
  const pred = E.skewLink(world.w[j], k, 1.5, s2, 1).cov, r = E.rng(17), N = 20000;
  let sx = 0, sy = 0, sxy = 0;
  for (let n = 0; n < N; n++) {
    const d = E.draw(world, r).data, w = d.w[j], x = d.X[j], ws = sum(w), mu = sum(x.map((v, t) => w[t] * v)) / ws;
    const v = sum(x.map((y, t) => w[t] * (y - mu) ** 2)) / (x.length - 1);
    sx += v; sy += mu; sxy += v * mu;
  }
  const mc = sxy / N - sx * sy / N / N;
  assert.ok(Math.abs(mc / pred - 1) < 0.1, `MC ${mc} vs ${pred}`);
  const D = E.noiseDiagnostics(E.draw(E.makeWorld({ normal: true }), r).data);
  assert.ok(Number.isFinite(D.link) && Number.isFinite(D.powerSkewBias));
});

test('Finding 35: the first-order skew bias (skewBias) predicts the plug-in under-pricing of corrBS; 0 for the pooled BLUP', () => {
  const world = E.makeWorld({ T: 6 }), r = E.rng(23), wt = world.w.map(sum), wall = sum(wt);
  let sim = 0, pred = 0, pool = 0;
  const N = 300;
  for (let n = 0; n < N; n++) {
    const { data } = E.draw(world, r), f = E.fitVC(data), g = E.fitBS(data);
    sim += sum(f.rates.map((x, j) => wt[j] * (x - g.rates[j]))) / wall;   // BS is balanced: portfolio bias 0
    pred += E.skewBias('vc', data).portfolio;
    pool += E.skewBias('blupPool', data).portfolio;
  }
  sim /= N; pred /= N;
  assert.ok(sim < 0 && pred < 0 && Math.abs(pred / sim - 1) < 0.5, `predicted ${pred} vs simulated ${sim}`);
  assert.ok(Math.abs(pool / N) < 0.2 * Math.abs(sim), `pooled σ̂²: small on average, ${pool / N}`);
});

test('Finding 35, ρ̂ channel: the pooled cross-region third moment γ̂ (crossSkew) is ≈ 0 without a shared shock and tends to ρ^(3/2)·skew(η) with many years; vcEstimate’s perturb hook moves one statistic', () => {
  const r = E.rng(29);
  let g0 = 0;
  const w0 = E.makeWorld({ rho: 0 });
  for (let n = 0; n < 200; n++) g0 += E.crossSkew(E.draw(w0, r).data);
  assert.ok(Math.abs(g0 / 200) < 0.03, `γ̂ at ρ = 0: ${g0 / 200}`);
  const w6 = E.makeWorld({ rho: 0.6, T: 100, growth: 0 });
  let g6 = 0;
  for (let n = 0; n < 100; n++) g6 += E.crossSkew(E.draw(w6, r).data);
  close(g6 / 100, Math.pow(0.6, 1.5) * Math.SQRT2, 0.1, 'γ̂ at ρ = 0.6, T = 100');
  const d = E.draw(E.makeWorld({ rho: 0.6 }), r).data, a = E.vcEstimate(d), b = E.vcEstimate(d, { perturb: { own: [2, 1.1] } }), c = E.vcEstimate(d, { perturb: { q: 0.01 } });
  close(b.own[2], 1.1 * a.own[2], 1e-12, 'own scaled'); close(b.own[3], a.own[3], 1e-12, 'others kept');
  close(c.rhoRaw, a.rhoRaw + 0.01, 1e-9, 'ρ̂ shifted'); close(c.own[0], a.own[0], 1e-12, 'variances kept');
});
