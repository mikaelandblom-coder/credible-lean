// S64: the held-out θ̂ of PlugInMix.lean (res:plugIn_proxy; PLAN "BLUP in credibility form").
// Path from the fitted blend (corrBS, Engine.fitVC) to the fitted BLUP (Engine.fitBLUP):
//   rate(θ) = (1 − θ)·blend + θ·BLUP,  MSE(θ) = (1 − θ)M₀ + θM₁ − θ(1 − θ)S.
// θ is chosen on a proxy of the levels: a held-out year's cells Xⱼₛ = μⱼ + εⱼₛ.
//   hoT    fit both on years 1..T−1, regress year T's blend error on Δ = BLUP − blend across regions
//          (weights wⱼₜ): θ̂ = −Σⱼ wⱼₜ(blendⱼ − Xⱼₜ)Δⱼ / Σⱼ wⱼₜΔⱼ², clipped to [0, 1] (mixLoss_clip_le);
//   loyo   the same regression pooled over every held-out year s (T refits; cross-fitted θ̂);
// each θ̂ is then applied to the fits on all T years (the rates a user would get).
// Compared with the blend (θ = 0), θ = ½, the plug-in BLUP (θ = 1) and the best fixed θ of the world
// (θ*_MC = −E[Σwe₀Δ]/E[ΣwΔ²] over the draws, an oracle).
// Worlds: the engine's (common year shock √ρηₜ, independent across years) and an AR(1) shock
// ηₜ = φηₜ₋₁ + √(1−φ²)uₜ (a persistent factor, cf. Factor.lean's AR(1) Γ), where the held-out year's
// noise is correlated with the fit: E[Δε] ≠ 0, the proxy's bias E[Δε]/EΔ² (proxy_neg_div_eq).
// MSE: exposure-weighted squared error against μⱼ in % of the oracle's (BLUP with the true K).
// Run: node studies/runs/held-out-theta.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 2000);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const clip = (x) => Math.max(0, Math.min(1, x));

// Draw with an AR(1) year shock (non-ordered gamma/normal worlds only).
function drawAR(world, r, phi) {
  const { J, T, w, truth, params } = world, a = Math.sqrt(params.rho), b = Math.sqrt(1 - params.rho);
  const sig = truth.sigmaj2.map(Math.sqrt), nz = params.normal, ns = params.noiseShape;
  const levels = Array.from({ length: J }, () => truth.mu + Math.sqrt(truth.tau2) * r.unit(params.levelShape, nz));
  const eta = [r.unit(ns, nz)];
  for (let t = 1; t < T; t++) eta.push(phi * eta[t - 1] + Math.sqrt(1 - phi * phi) * r.unit(ns, nz));
  const X = levels.map((mu, j) => w[j].map((wt, t) => mu + sig[j] / Math.sqrt(wt) * (a * eta[t] + b * r.unit(ns, nz))));
  return { levels, data: { w, X } };
}

const drop = (data, s) => ({ w: data.w.map((row) => row.filter((_, t) => t !== s)), X: data.X.map((row) => row.filter((_, t) => t !== s)) });
function pair(data) {
  let b, p;
  try { b = E.fitVC(data).rates; p = E.fitBLUP(data).rates; } catch (e) { return null; }
  return { b, d: p.map((x, j) => x - b[j]) };
}
// Σⱼ wⱼₛ (blendⱼ − Xⱼₛ)Δⱼ and Σⱼ wⱼₛ Δⱼ² for the fit without year s.
function heldOut(data, s) {
  const f = pair(drop(data, s)); if (!f) return null;
  let num = 0, den = 0;
  f.b.forEach((x, j) => { const wj = data.w[j][s]; num += wj * (x - data.X[j][s]) * f.d[j]; den += wj * f.d[j] ** 2; });
  return { num, den, f };
}

function run(params, phi) {
  const world = E.makeWorld(params), r = E.rng(64), { J, T } = world, K = E.trueK(world), t2 = world.truth.tau2;
  const wt = world.w.map(sum), W = sum(wt), loss = (rates, mu) => sum(rates.map((x, j) => wt[j] * (x - mu[j]) ** 2)) / W;
  const dO = Array.from({ length: J }, (_, j) => E.blupWeight(K, t2, j));
  const rows = [];
  let A = 0, B = 0, AT = 0, BT = 0, De = 0;
  for (let n = 0; n < N; n++) {
    const { levels, data } = phi ? drawAR(world, r, phi) : E.draw(world, r);
    const full = pair(data), hT = heldOut(data, T - 1); if (!full || !hT) continue;
    let ln = 0, ld = 0;
    for (let s = 0; s < T; s++) { const h = s === T - 1 ? hT : heldOut(data, s); if (h) { ln += h.num; ld += h.den; } }
    const m = E.cohortMeans(data).m, oracle = dO.map((d) => sum(d.map((x, i) => x * m[i])));
    const mix = (th) => full.b.map((x, j) => x + th * full.d[j]);
    const tiny = 1e-14, rawT = hT.den > tiny ? -hT.num / hT.den : NaN, rawL = ld > tiny ? -ln / ld : NaN;
    const use = (x) => (Number.isNaN(x) ? 1 : clip(x));   // Δ = 0 (ρ̂ = 0: BLUP = blend): θ does not matter
    rows.push({ levels, mix, LO: loss(oracle, levels), rawT, rawL,
      L: { blend: loss(mix(0), levels), half: loss(mix(0.5), levels), BLUP: loss(mix(1), levels), hoT: loss(mix(use(rawT)), levels), loyo: loss(mix(use(rawL)), levels) } });
    full.b.forEach((x, j) => { A += wt[j] * (x - levels[j]) * full.d[j]; B += wt[j] * full.d[j] ** 2; });
    hT.f.b.forEach((x, j) => { const wj = data.w[j][T - 1], d = hT.f.d[j]; AT += wj * (x - levels[j]) * d; BT += wj * d * d; De += wj * d * (data.X[j][T - 1] - levels[j]); });
  }
  const thRaw = -A / B, thStar = clip(thRaw);
  rows.forEach((x) => { x.L.best = loss(x.mix(thStar), x.levels); });
  const LO = sum(rows.map((x) => x.LO)) / rows.length;

  const pct = (k) => { const d = rows.map((x) => x.L[k] / LO * 100); const mm = sum(d) / d.length, v = sum(d.map((y) => (y - mm) ** 2)) / (d.length - 1); return { m: mm, se: Math.sqrt(v / d.length) }; };
  // θ̂ before clipping has heavy tails (a ratio): median and quartiles over the draws with Δ ≠ 0.
  const stat = (k) => { const v = rows.map((x) => x[k]).filter((x) => !Number.isNaN(x)).sort((a, b) => a - b), q = (p) => v[Math.floor(p * (v.length - 1))];
    return { q1: q(0.25), med: q(0.5), q3: q(0.75), lo: v.filter((x) => x <= 0).length / rows.length, hi: v.filter((x) => x >= 1).length / rows.length, zero: 1 - v.length / rows.length }; };
  const share = stat;
  return { n: rows.length, thRaw, thStar, thStarT: -AT / BT, proxyBias: De / BT, pct, stat, share, keys: ['blend', 'half', 'BLUP', 'best', 'hoT', 'loyo'] };
}

const worlds = [['default (gamma)', {}], ['normal', { normal: true }], ['ρ = 0.3', { rho: 0.3 }], ['ρ = 0.6', { rho: 0.6 }],
  ['ρ = 0.6, normal', { rho: 0.6, normal: true }], ['ρ = 0.6, T = 5', { rho: 0.6, T: 5 }], ['ρ = 0.6, J = 20', { rho: 0.6, J: 20 }],
  ['ρ = 0.6, thesis vol.', { rho: 0.6, volume: 4400 }], ['ρ = 0.6, AR φ = 0.5', { rho: 0.6 }, 0.5], ['ρ = 0.6, AR φ = 0.8', { rho: 0.6 }, 0.8],
  ['ρ = 0.6, φ = 0.8, normal', { rho: 0.6, normal: true }, 0.8]];

if (require.main === module) {
  console.log(`draws ${N}. MSE of the rates on all T years, in % of the oracle's (± 2 SE). θ̂ = clip of the regression; Δ = 0 draws use θ = 1.`);
  console.log('θ*: best fixed θ over the draws (full fits, before clipping; "best" uses it clipped); θ*ₜ₋₁ the same for the fits on 1..T−1;');
  console.log('bias = E[Δε]/EΔ² of year T against the fits on 1..T−1 (proxy_neg_div_eq: E-regression = θ*ₜ₋₁ + bias).');
  console.log('θ̂ hoT, loyo before clipping: quartiles q1/median/q3; clip: % of draws at 0 / at 1 / with Δ = 0.\n');
  const ks = ['blend', 'half', 'BLUP', 'best', 'hoT', 'loyo'];
  console.log('world'.padEnd(26) + ks.map((k) => k.padStart(13)).join('') + '     θ*  θ*ₜ₋₁   bias    θ̂ hoT q1/med/q3   θ̂ loyo q1/med/q3  clip hoT   clip loyo');
  for (const [name, p, phi] of worlds) {
    const R = run(p, phi), f = (x) => x.toFixed(2).padStart(7);
    const sT = R.stat('rawT'), sL = R.stat('rawL'), qs = (s) => `${s.q1.toFixed(2)}/${s.med.toFixed(2)}/${s.q3.toFixed(2)}`.padStart(19), cl = (s) => `${(100 * s.lo).toFixed(0)}/${(100 * s.hi).toFixed(0)}/${(100 * s.zero).toFixed(0)}`.padStart(11);
    console.log(name.padEnd(26) + ks.map((k) => { const c = R.pct(k); return `${c.m.toFixed(1)} ± ${(2 * c.se).toFixed(1)}`.padStart(13); }).join('')
      + f(R.thRaw) + f(R.thStarT) + f(R.proxyBias) + qs(sT) + qs(sL) + cl(sT) + cl(sL));
  }
}
// The price of choosing θ on one held-out year (target for PlugInMix.lean). Given the fit on 1..T−1
// (e₀ = blend − μ, Δ) and year T's noise ε, mean 0, covariance Σ, independent of the fit, with the
// regression weights W = diag(wⱼₜ) also as loss weights:
//   θ̂ = θ̃ + ΔᵀWε/ΔᵀWΔ,  θ̃ = −ΔᵀWe₀/ΔᵀWΔ  (E[θ̂ | fit] = θ̃),
//   E[(e₀ + θ̂Δ)ᵀW(e₀ + θ̂Δ) | fit] = (e₀ + θ̃Δ)ᵀW(e₀ + θ̃Δ) + price,  price = ΔᵀWΣWΔ / ΔᵀWΔ,
// a Rayleigh quotient of W^½ΣW^½ = (σᵢσⱼρᵢⱼ) here: price ≥ λmin = σ²(1 − ρ) for equal σⱼ, whatever the fits.
// θ̂ (unclipped) beats θ = 1 in conditional mean iff S(1 − θ̃)² > price, S = ΔᵀWΔ.
function priceCheck(params, phi) {
  const world = E.makeWorld(params), r = E.rng(65), { J, T, truth } = world, sd = truth.sigmaj2.map(Math.sqrt);
  let R = [], P = [], G = [], ratioMin = Infinity;
  const lmin = Math.min(...E.eigSym(truth.rho.map((row, i) => row.map((x, j) => sd[i] * sd[j] * x))));
  for (let n = 0; n < N; n++) {
    const { levels, data } = phi ? drawAR(world, r, phi) : E.draw(world, r);
    const h = heldOut(data, T - 1); if (!h || h.den < 1e-14) continue;
    const w = data.w.map((row) => row[T - 1]), d = h.f.d, e0 = h.f.b.map((x, j) => x - levels[j]);
    const S = sum(d.map((x, j) => w[j] * x * x)), thT = -sum(d.map((x, j) => w[j] * e0[j] * x)) / S, thH = -h.num / h.den;
    const L = (th) => sum(e0.map((x, j) => w[j] * (x + th * d[j]) ** 2));
    const u = d.map((x, j) => Math.sqrt(w[j]) * x);
    let q = 0; for (let i = 0; i < J; i++) for (let j = 0; j < J; j++) q += u[i] * u[j] * sd[i] * sd[j] * truth.rho[i][j];
    R.push(L(thH) - L(thT)); P.push(q / S); G.push(S * (1 - thT) ** 2); ratioMin = Math.min(ratioMin, q / S / lmin);
  }
  const ms = (v) => { const m = sum(v) / v.length; return { m, se: Math.sqrt(sum(v.map((y) => (y - m) ** 2)) / (v.length - 1) / v.length) }; };
  return { n: R.length, R: ms(R), P: ms(P), G: ms(G), lmin, ratioMin };
}

if (require.main === module) {
  console.log('\nThe price of one held-out year (fits on 1..T−1, loss weights wⱼₜ, draws with Δ ≠ 0):');
  console.log('realized L(θ̂) − L(θ̃) against the predicted price ΔᵀWΣWΔ/ΔᵀWΔ (exact in mean when year T is independent of the fit),');
  console.log('λmin of (σᵢσⱼρᵢⱼ), min over draws of price/λmin (≥ 1), and the gain of the per-draw best θ̃ over θ = 1, E S(1 − θ̃)².');
  console.log('world'.padEnd(26) + 'realized'.padStart(16) + 'price'.padStart(16) + 'λmin'.padStart(8) + 'min ratio'.padStart(11) + 'S(1−θ̃)²'.padStart(16));
  for (const [name, p, phi] of worlds) {
    const c = priceCheck(p, phi), f = (x) => `${x.m.toFixed(2)} ± ${(2 * x.se).toFixed(2)}`.padStart(16);
    console.log(name.padEnd(26) + f(c.R) + f(c.P) + c.lmin.toFixed(1).padStart(8) + c.ratioMin.toFixed(2).padStart(11) + f(c.G));
  }
}
module.exports = { run, drawAR, priceCheck };
