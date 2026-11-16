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
