// Purpose: check Finding 38 beyond the balanced world. The first-order cross term 2E[AB] of the
// Bühlmann–Straub plug-in (PlugIn.lean's A, B), for ANY volumes wⱼₜ, exactly from the moment tables, and
// against simulation.
//
// World: cells xⱼₜ = μ + Lⱼ + eⱼₜ, independent levels (variance τ², excess kurtosis γL) and noise
// eⱼₜ = εⱼₜ/√wⱼₜ (Var ε = σ², excess kurtosis γN), so κ₄(Lⱼ) = γLτ⁴, κ₄(eⱼₜ) = γNσ⁴/wⱼₜ² as in Lean's primK4.
// Fit: Engine.fitBS (σ̂² = P, τ̂² = (B − (J − 1)P)/c, ẑⱼ = Wⱼ/(Wⱼ + σ̂²/τ̂²), collective b = ẑ/Σẑ).
// First order: the fit's weights dⱼ(θ) on the region means depend on θ = (P, B); linearize at θ₀ = (E P, E B),
// where the fit has the true z. Then Bⱼ ≈ Σₖ (gⱼₖ·x)(Qₖ − E Qₖ), gⱼₖ = ∂dⱼ/∂θₖ, and with X = (L, e),
// C = diag, κ₄ diagonal (Cumulants.integral_lin_lin_sumSq minus E[(a·X)(g·X)]·E Q):
//   E[(a·X)(g·X)(Q − E Q)] = Σₘ cₘ [2(aᵀCuₘ)(gᵀCuₘ) + Σₚ aₚgₚuₘₚ²κₚ]   for Q = Σₘ cₘ(uₘ·X)².
// Reported: exposure-weighted Σⱼ Wⱼ·2E[AⱼBⱼ] / Σⱼ Wⱼ(1 − zⱼ)τ², in %. Balanced check against the proved
// closed form −2(1 − 1/J)z(1 − z)(γL + γN/T)/J (Cumulants.crossTerm_of_balanced_cumulants).
// Simulation: the exact cross term of the full fit (τ̂² ≤ 0 truncated as in fitBS), symmetric (Laplace)
// and skewed (gamma) shapes; the first order has no third-cumulant term, the exact one does.
// Run: node studies/runs/cross-term.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 100000);

// ---------------------------------------------------------------- the first-order cross term
function firstOrder(w, tau2, sigma2, gammaL, gammaN) {
  const J = w.length, T = w[0].length, W = w.map((r) => r.reduce((a, b) => a + b, 0)), Wall = W.reduce((a, b) => a + b, 0);
  const a = w.map((r, j) => r.map((x) => x / W[j])); // shares
  const n = J + J * T, cell = (j, t) => J + j * T + t;
  const Cd = new Float64Array(n), kap = new Float64Array(n);
  for (let j = 0; j < J; j++) { Cd[j] = tau2; kap[j] = gammaL * tau2 * tau2; }
  for (let j = 0; j < J; j++) for (let t = 0; t < T; t++) { Cd[cell(j, t)] = sigma2 / w[j][t]; kap[cell(j, t)] = gammaN * sigma2 * sigma2 / (w[j][t] * w[j][t]); }
  // A linear combination Σᵢ βᵢ x̄ᵢ on the primitives: βᵢ on Lᵢ, βᵢaᵢₜ on eᵢₜ.
  const pullMeans = (beta) => { const v = new Float64Array(n); for (let i = 0; i < J; i++) { v[i] = beta[i]; for (let t = 0; t < T; t++) v[cell(i, t)] = beta[i] * a[i][t]; } return v; };
  // The statistics as Σₘ cₘ(uₘ·X)²: P over residual cells, B over the spreads.
  const stats = [[], []];
  for (let j = 0; j < J; j++) for (let t = 0; t < T; t++) {
    const u = new Float64Array(n);
    for (let s = 0; s < T; s++) u[cell(j, s)] = (s === t ? 1 : 0) - a[j][s];
    stats[0].push({ c: w[j][t] / (J * (T - 1)), u });
  }
  for (let j = 0; j < J; j++) stats[1].push({ c: W[j], u: pullMeans(W.map((x, i) => (i === j ? 1 : 0) - x / Wall)) });
  const EQ = stats.map((S) => S.reduce((acc, { c, u }) => { let q = 0; for (let p = 0; p < n; p++) q += u[p] * u[p] * Cd[p]; return acc + c * q; }, 0));
  // The fit's weights on the region means for target j, as a function of θ = (P, B).
  const cc = Wall - W.reduce((s, x) => s + x * x, 0) / Wall;
  const weights = (th) => {
    const s2 = th[0], t2 = (th[1] - (J - 1) * th[0]) / cc;
    const z = W.map((x) => x / (x + s2 / t2)), zs = z.reduce((p, q) => p + q, 0), b = z.map((x) => x / zs);
    return { z, D: z.map((zj, j) => b.map((bi, i) => (i === j ? zj : 0) + (1 - zj) * bi)) };
  };
  const { z, D } = weights(EQ);
  const grads = [0, 1].map((k) => {
    const h = 1e-6 * EQ[k], tp = EQ.slice(), tm = EQ.slice(); tp[k] += h; tm[k] -= h;
    const Dp = weights(tp).D, Dm = weights(tm).D;
    return Dp.map((row, j) => row.map((x, i) => (x - Dm[j][i]) / (2 * h)));
  });
  let num = 0, den = 0, numKnown = 0;
  const perRegion = [];
  for (let j = 0; j < J; j++) {
    const av = pullMeans(D[j]); av[j] -= 1; // A = dⱼ·x − (μ + Lⱼ)
    let cross = 0, crossB = 0;
    for (let k = 0; k < 2; k++) {
      const g = pullMeans(grads[k][j]);
      let s = 0;
      for (const { c, u } of stats[k]) {
        let aCu = 0, gCu = 0, kk = 0;
        for (let p = 0; p < n; p++) if (u[p] !== 0) { aCu += av[p] * Cd[p] * u[p]; gCu += g[p] * Cd[p] * u[p]; kk += av[p] * g[p] * u[p] * u[p] * kap[p]; }
        s += c * (2 * aCu * gCu + kk);
      }
      cross += 2 * s;
      if (k === 1) crossB += 2 * s;
    }
    perRegion.push(cross / ((1 - z[j]) * tau2));
    num += W[j] * cross; den += W[j] * (1 - z[j]) * tau2;
    numKnown += W[j] * crossB; // P held at its mean: only through B. Not "D known" for unequal volumes; balanced: it is.
  }
  return { rel: num / den, relB: numKnown / den, z, perRegion };
}

// ---------------------------------------------------------------- simulation
function rng(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
function normal(u) { let x; do { x = u(); } while (x === 0); return Math.sqrt(-2 * Math.log(x)) * Math.cos(2 * Math.PI * u()); }
function gamma(u, k) { // Marsaglia–Tsang, k ≥ 1
  const d = k - 1 / 3, c = 1 / Math.sqrt(9 * d);
  for (;;) { let x, v; do { x = normal(u); v = 1 + c * x; } while (v <= 0); v = v * v * v; const U = u(); if (Math.log(U) < 0.5 * x * x + d - d * v + d * Math.log(v)) return d * v; }
}
// Standardized draws (mean 0, variance 1) with a given shape: excess kurtosis 0 (normal), 3 (Laplace), 6/k (gamma k).
const shapes = {
  normal: { g: 0, draw: (u) => normal(u) },
  laplace: { g: 3, draw: (u) => { let x; do { x = u(); } while (x === 0); return (u() < 0.5 ? -1 : 1) * -Math.log(x) / Math.SQRT2; } },
  gamma2: { g: 3, draw: (u) => (gamma(u, 2) - 2) / Math.SQRT2 },
};
function simulate(w, tau2, sigma2, shL, shN, n, seed) {
  const J = w.length, T = w[0].length, u = rng(seed), mu = 1;
  const W = w.map((r) => r.reduce((p, q) => p + q, 0)), Wall = W.reduce((p, q) => p + q, 0);
  const cc = Wall - W.reduce((s, x) => s + x * x, 0) / Wall;
  const z0 = W.map((x) => x / (x + sigma2 / tau2)), zs0 = z0.reduce((p, q) => p + q, 0), b0 = z0.map((x) => x / zs0);
  let s = 0, ss = 0, trunc = 0;
  const den = W.reduce((acc, x, j) => acc + x * (1 - z0[j]) * tau2, 0);
  for (let k = 0; k < n; k++) {
    const L = W.map(() => Math.sqrt(tau2) * shapes[shL].draw(u));
    const X = w.map((r, j) => r.map((x) => mu + L[j] + Math.sqrt(sigma2 / x) * shapes[shN].draw(u)));
    const data = { X, w };
    const f = E.fitBS(data), m = f.means;
    if (f.flags.tauNeg) trunc++;
    const coll0 = b0.reduce((acc, bi, i) => acc + bi * m[i], 0);
    let c = 0;
    for (let j = 0; j < J; j++) {
      const oracle = z0[j] * m[j] + (1 - z0[j]) * coll0;
      c += W[j] * 2 * (oracle - mu - L[j]) * (f.rates[j] - oracle);
    }
    c /= den; s += c; ss += c * c;
  }
  const m = s / n;
  return { rel: m, se: Math.sqrt(Math.max(ss / n - m * m, 0) / n), trunc: trunc / n };
}

// ---------------------------------------------------------------- worlds
const balanced = (J, T, w0) => Array.from({ length: J }, () => new Array(T).fill(w0));
// Unbalanced: region sizes log-spread over a factor 16, years varying by 1–2×.
const unbalanced = (J, T, w0) => Array.from({ length: J }, (_, j) => Array.from({ length: T }, (_, t) => w0 * Math.pow(16, j / (J - 1) - 0.5) * (1 + 0.5 * ((j + t) % 3))));
const pct = (x) => (100 * x).toFixed(2).padStart(7);

console.log('1. Balanced: general first order against the proved closed form, in % of (1 − z)τ²');
for (const [J, T, z, gL, gN] of [[8, 5, 0.7, 3, 0], [8, 5, 0.7, 0, 3], [8, 10, 0.5, 3, 3], [30, 5, 0.85, 6, 2]]) {
  const tau2 = 1, w0 = 100, sigma2 = (1 - z) / z * tau2 * w0 * T; // z = τ²/(τ² + σ²/(w₀T))
  const r = firstOrder(balanced(J, T, w0), tau2, sigma2, gL, gN);
  const closed = -2 * (1 - 1 / J) * z * (1 - z) * (gL + gN / T) / J;
  console.log(`  J=${J} T=${T} z=${z} γL=${gL} γN=${gN}: general ${pct(r.rel)}   closed ${pct(closed)}`);
}

console.log(`\n2. Unbalanced volumes (sizes ×16 apart, years 1–2×): first order against simulation (${N} draws), in % of Σ W(1 − z)τ²`);
console.log('  world                     | z range   | shapes L/N      | 1st order (γ parts)          | simulated ± 2 SE   | τ̂²≤0');
for (const [J, T, zmid] of [[8, 5, 0.7], [30, 5, 0.7], [30, 10, 0.5]]) {
  const tau2 = 1, w0 = 100, sigma2 = (1 - zmid) / zmid * tau2 * w0 * T, w = unbalanced(J, T, w0);
  const fo = (gL, gN) => firstOrder(w, tau2, sigma2, gL, gN);
  const zr = fo(0, 0).z;
  for (const [shL, shN] of [['normal', 'normal'], ['laplace', 'normal'], ['normal', 'laplace'], ['laplace', 'laplace'], ['gamma2', 'gamma2']]) {
    const gL = shapes[shL].g, gN = shapes[shN].g, r = fo(gL, gN), rl = fo(gL, 0), rn = fo(0, gN);
    const sim = simulate(w, tau2, sigma2, shL, shN, N, 7 + J + T);
    console.log(`  J=${String(J).padEnd(2)} T=${String(T).padEnd(2)} z≈${zmid}`.padEnd(28) + `| ${Math.min(...zr).toFixed(2)}–${Math.max(...zr).toFixed(2)} | ${(shL + '/' + shN).padEnd(15)} | ${pct(r.rel)} (L ${pct(rl.rel)}, N ${pct(rn.rel)}) | ${pct(sim.rel)} ± ${(200 * sim.se).toFixed(2).padStart(5)} | ${(100 * sim.trunc).toFixed(1)}%`);
  }
}

console.log('\n3. Sign per region (unbalanced, J = 8, T = 5, γL = 0, γN = 3): first-order 2E[AⱼBⱼ]/((1 − zⱼ)τ²), in %');
{
  const J = 8, T = 5, tau2 = 1, w0 = 100, sigma2 = 0.3 / 0.7 * tau2 * w0 * T, w = unbalanced(J, T, w0);
  const r = firstOrder(w, tau2, sigma2, 0, 3);
  console.log('  z:     ' + r.z.map((x) => x.toFixed(2).padStart(7)).join(''));
  console.log('  cross: ' + r.perRegion.map(pct).join(''));
}
