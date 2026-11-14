// θ̂ from a data-based variance V̂ (independent years; no normal-theory formula)
// against the normal-theory rule and the best fixed θ, under five noise laws.
// Run: node studies/damping-vhat.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const GRID = [0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1];
const LAWS = {
  'two-point κ=-2': (r) => (r() < 0.5 ? -1 : 1),
  'normal κ=0': (r) => r.normal(),
  'gamma2 κ=3': (r) => (r.gamma(2) - 2) / Math.SQRT2,
  'expon κ=6': (r) => -Math.log(1 - r()) - 1,
  'gamma¼ κ=24': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; },
};
const clip = (x) => Math.max(0, Math.min(1, x));

function fitAt(data, theta) {
  for (const th of [theta].concat(GRID.filter((x) => x < theta).reverse())) {
    try { return E.fitCorr(data, { theta: th }); } catch (e) { /* not PD */ }
  }
}

// Pairwise products pₜ = √(wᵢₜwⱼₜ)(Xᵢₜ − μ̂ᵢ)(Xⱼₜ − μ̂ⱼ); Σ̂ᵢⱼ = Σₜ pₜ / Dᵢⱼ (eq. (39)).
// With independent years, Var Σ̂ᵢⱼ ≈ T · s²(p) / Dᵢⱼ², s²(p) the sample variance of the pₜ.
function thetas(data) {
  const J = data.X.length, T = data.X[0].length, { wt, m, Sig } = E.sigmaHat(data);
  let s2raw = 0, vraw = 0, s2cor = 0, vcor = 0, rs = 0, n = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) {
    const p = [];
    let S = 0;
    for (let t = 0; t < T; t++) {
      const c = Math.sqrt(data.w[i][t] * data.w[j][t]);
      S += c; p.push(c * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]));
    }
    const D = S + (T - 2) * wt[i] * wt[j] / S;
    const pb = p.reduce((a, x) => a + x, 0) / T;
    const sp2 = p.reduce((a, x) => a + (x - pb) ** 2, 0) / (T - 1);
    const V = T * sp2 / (D * D), s = Sig[i][j], scale = Sig[i][i] * Sig[j][j];
    s2raw += s * s; vraw += V; s2cor += s * s / scale; vcor += V / scale;
    rs += s / Math.sqrt(scale); n++;
  }
  const rb = Math.max(-1, Math.min(1, rs / n));
  return {
    normal: rb * rb / (rb * rb + (1 - rb * rb) ** 2 / (T - 1)),
    raw: clip(1 - vraw / s2raw),
    cor: clip(1 - vcor / s2cor),
  };
}

console.log(`draws ${N}; error relative to the floor (100 = floor). Columns: best fixed θ (its value), then each rule (mean θ̂)`);
console.log('law             J  T  ρ   | best fixed   | normal rule  | V̂ raw scale  | V̂ corr scale');
for (const [J, Ts] of [[8, [5, 10]], [20, [10]]]) for (const T of Ts)
for (const [name, law] of Object.entries(LAWS)) {
  for (const rho of [0, 0.3, 0.6, 0.9]) {
    const world = E.makeWorld({ J, T, rho }), fl = E.floorBlend(world), r = E.rng(2026);
    r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
    const acc = { floor: 0, full: GRID.map(() => 0) }, rules = ['normal', 'raw', 'cor'];
    for (const k of rules) { acc[k] = 0; acc[k + 'θ'] = 0; }
    for (let k = 0; k < N; k++) {
      const { levels, data } = E.draw(world, r);
      acc.floor += E.weightedSE(data, fl.apply(data).rates, levels);
      GRID.forEach((th, i) => { acc.full[i] += E.weightedSE(data, fitAt(data, th).rates, levels); });
      const th = thetas(data);
      for (const k of rules) { acc[k + 'θ'] += th[k]; acc[k] += E.weightedSE(data, fitAt(data, th[k]).rates, levels); }
    }
    const rel = (x) => (x / acc.floor * 100).toFixed(0).padStart(4);
    const bi = acc.full.indexOf(Math.min(...acc.full));
    const col = (k) => `${rel(acc[k])} (${(acc[k + 'θ'] / N).toFixed(2)})`;
    console.log(`${name.padEnd(15)} ${String(J).padEnd(2)} ${String(T).padEnd(2)} ${rho.toFixed(1)} | ${rel(acc.full[bi])} (${GRID[bi].toFixed(2)})  | ${col('normal')}  | ${col('raw')}  | ${col('cor')}`);
  }
}
