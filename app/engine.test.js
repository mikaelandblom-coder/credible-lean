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
