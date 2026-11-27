// Fitting the group variance φτ² (PLAN G4; Credibility/GroupPoolWeights.lean, `phiTauPool_blue_optimal`).
// Purpose: decide. Which fit of φτ² (and of the non-shared part λ = (1 − φ)τ²) should the app use?
//
// World: J = 12 cohorts in G groups of unequal size, T years, volumes wⱼ lognormal (sd 1, mean 1),
//   μⱼ = 1 + √(φτ²)·γ_g + √((1 − φ)τ²)·ηⱼ,  Xⱼₜ = μⱼ + σ/√wⱼ · εⱼₜ,
// γ, η standard normal, ε centred and scaled: exponential (skew 2) or normal. Cohorts independent (ρ = 0),
// so the pair estimator is P̂ᵢⱼ = (μ̂ᵢ − μ̂ⱼ)² − v̂ᵢ − v̂ⱼ with v̂ⱼ = σ̂²/(wⱼT), σ̂² pooled within cohorts.
// E P̂ᵢⱼ = 2λ + 2θ[across], θ = φτ² (`pairHat_unbiasedG`).
//
// Fits of (λ, θ), all from data only:
//   vol   pairs weighted by wᵢwⱼ within each class, θ̂ = (Ā − W̄)/2, λ̂ = W̄/2 (`phiTauPooled_unbiasedG`);
//   BG    Bühlmann–Gisler bottom-up: pooled within-group BS estimator of λ, then the BS estimator of θ
//         from the volume-weighted group means with noise λ̂Σ(wⱼ/w_g)² + σ̂²/(T w_g);
//   GLS1  Gauss–Markov on the pair table V (`pairPool_blue_optimal`), V from `vol`'s estimates under the
//         normal formulas: Cov(P̂ₚ, P̂_q) = 2 Cov(Dₚ, D_q)² + cₚc_q Var σ̂², Dᵢⱼ = μ̂ᵢ − μ̂ⱼ, cᵢⱼ = (1/wᵢ + 1/wⱼ)/T;
//   GLS2  one more pass with GLS1's estimates;
//   GLS*  reference, not a fit: V from the true parameters (normal formulas).
// Negative estimates are clipped at 0 for the blend only (bias and SD are of the raw estimates).
// Blend: the BLUP of each μⱼ with unknown mean (universal kriging) on K̂ = L̂_G + diag(σ̂²/(wⱼT)); loss
// Σ wⱼ(μ̃ⱼ − μⱼ)²/Σ wⱼ, in % of the BLUP with the true parameters (100). "nogrp": the BLUP with one τ̂²
// (BS) and no groups.
// Run: node studies/runs/group-fit.js [draws]   (default 2000)
'use strict';

const draws = +(process.argv[2] || 2000);
let seed = 12345;
function rand() { seed = (seed * 1103515245 + 12345) % 2147483648; return (seed + 0.5) / 2147483648; }
function rnorm() { return Math.sqrt(-2 * Math.log(rand())) * Math.cos(2 * Math.PI * rand()); }
function rexpc() { return -Math.log(rand()) - 1; } // mean 0, sd 1, skew 2

function solve(A, b) { // Gaussian elimination with partial pivoting; A n×n, b n×m (copies)
  const n = A.length, m = b[0].length;
  const M = A.map((r, i) => r.concat(b[i]));
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    [M[c], M[p]] = [M[p], M[c]];
    for (let r = c + 1; r < n; r++) {
      const f = M[r][c] / M[c][c];
      if (f !== 0) for (let k = c; k < n + m; k++) M[r][k] -= f * M[c][k];
    }
  }
  const x = Array.from({ length: n }, () => new Array(m).fill(0));
  for (let r = n - 1; r >= 0; r--) for (let k = 0; k < m; k++) {
    let s = M[r][n + k];
    for (let c = r + 1; c < n; c++) s -= M[r][c] * x[c][k];
    x[r][k] = s / M[r][r];
  }
  return x;
}

function runWorld({ sizes, T, phi, noise }) {
  const J = sizes.reduce((a, b) => a + b, 0);
  const grp = []; sizes.forEach((n, g) => { for (let i = 0; i < n; i++) grp.push(g); });
  const G = sizes.length;
  const tau2 = 0.04, sig2 = 0.25; // z = τ²/(τ² + σ²/(wT)) ≈ 0.5 at w = 1, T = 6
  const lam = (1 - phi) * tau2, th = phi * tau2;
  const w = Array.from({ length: J }, () => Math.exp(rnorm() - 0.5)); // fixed volumes per world
  const pairs = [];
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) pairs.push([i, j, grp[i] === grp[j] ? 0 : 1]);
  const nP = pairs.length;
  const cP = pairs.map(([i, j]) => (1 / w[i] + 1 / w[j]) / T);
  const varSig = (s2) => 2 * s2 * s2 / (J * (T - 1));

  function Kmat(l, t, s2) {
    return Array.from({ length: J }, (_, i) => Array.from({ length: J }, (_, j) =>
      (i === j ? l + t + s2 / (w[i] * T) : 0) + (i !== j && grp[i] === grp[j] ? t : 0)));
  }
  function glsFit(P, l, t, s2) {
    const K = Kmat(Math.max(l, 1e-6), Math.max(t, 0), s2);
    const cd = (a, b, c, d) => K[a][c] - K[a][d] - K[b][c] + K[b][d];
    const vs = varSig(s2);
    const V = pairs.map(([a, b], p) => pairs.map(([c, d], q) => 2 * cd(a, b, c, d) ** 2 + cP[p] * cP[q] * vs));
    const X = pairs.map(([, , x]) => [2, 2 * x]);
    const VinvX = solve(V, X), VinvP = solve(V, P.map((v) => [v]));
    const A = [[0, 0], [0, 0]], r = [0, 0];
    for (let p = 0; p < nP; p++) for (let a = 0; a < 2; a++) {
      r[a] += X[p][a] * VinvP[p][0];
      for (let b = 0; b < 2; b++) A[a][b] += X[p][a] * VinvX[p][b];
    }
    const det = A[0][0] * A[1][1] - A[0][1] * A[1][0];
    return [(A[1][1] * r[0] - A[0][1] * r[1]) / det, (A[0][0] * r[1] - A[1][0] * r[0]) / det];
  }
  function blupLoss(l, t, s2, mh, mu) {
    const K = Kmat(Math.max(l, 0), Math.max(t, 0), s2);
    const L = Kmat(Math.max(l, 0), Math.max(t, 0), 0);
    const ones = new Array(J).fill(1);
    const sol = solve(K, mh.map((v, i) => [v, ones[i]]));
    let a = 0, b = 0; for (let i = 0; i < J; i++) { a += sol[i][0]; b += sol[i][1]; }
    const m = a / b;
    const r = solve(K, mh.map((v) => [v - m]));
    let loss = 0, W = 0;
    for (let j = 0; j < J; j++) {
      let pred = m; for (let i = 0; i < J; i++) pred += L[j][i] * r[i][0];
      loss += w[j] * (pred - mu[j]) ** 2; W += w[j];
    }
    return loss / W;
  }

  const names = ['vol', 'BG', 'GLS1', 'GLS2', 'GLS*'];
  const est = Object.fromEntries(names.map((n) => [n, { th: [], lam: [], loss: 0 }]));
  let oracle = 0, nogrp = 0;
  for (let d = 0; d < draws; d++) {
    const gam = Array.from({ length: G }, rnorm);
    const mu = grp.map((g) => 1 + Math.sqrt(th) * gam[g] + Math.sqrt(lam) * rnorm());
    const mh = [], ss = [];
    for (let j = 0; j < J; j++) {
      const x = Array.from({ length: T }, () => mu[j] + Math.sqrt(sig2 / w[j]) * (noise === 'exp' ? rexpc() : rnorm()));
      const m = x.reduce((a, b) => a + b, 0) / T;
      mh.push(m); ss.push(w[j] * x.reduce((a, b) => a + (b - m) ** 2, 0));
    }
    const s2 = ss.reduce((a, b) => a + b, 0) / (J * (T - 1));
    const v = w.map((wj) => s2 / (wj * T));
    const P = pairs.map(([i, j]) => (mh[i] - mh[j]) ** 2 - v[i] - v[j]);
    // vol
    let sw = [0, 0], sp = [0, 0];
    pairs.forEach(([i, j, x], p) => { sw[x] += w[i] * w[j]; sp[x] += w[i] * w[j] * P[p]; });
    const Wb = sp[0] / sw[0], Ab = sp[1] / sw[1];
    const fit = { vol: [Wb / 2, (Ab - Wb) / 2] };
    // BG bottom-up
    let num = 0, den = 0; const wg = new Array(G).fill(0), mg = new Array(G).fill(0), q2 = new Array(G).fill(0);
    for (let j = 0; j < J; j++) { wg[grp[j]] += w[j]; mg[grp[j]] += w[j] * mh[j]; }
    for (let g = 0; g < G; g++) mg[g] /= wg[g];
    for (let g = 0; g < G; g++) {
      let s = 0, n = 0, sq = 0;
      for (let j = 0; j < J; j++) if (grp[j] === g) { s += w[j] * (mh[j] - mg[g]) ** 2; n++; sq += w[j] * w[j]; q2[g] += (w[j] / wg[g]) ** 2; }
      num += s - (n - 1) * s2 / T; den += wg[g] - sq / wg[g];
    }
    const lamBG = num / den;
    const Wt = wg.reduce((a, b) => a + b, 0), mbar = mg.reduce((a, m, g) => a + wg[g] * m, 0) / Wt;
    let n2 = 0, d2 = 0;
    for (let g = 0; g < G; g++) {
      const f = wg[g] * (1 - wg[g] / Wt);
      n2 += wg[g] * (mg[g] - mbar) ** 2 - f * (Math.max(lamBG, 0) * q2[g] + s2 / (T * wg[g])); d2 += f;
    }
    fit.BG = [lamBG, n2 / d2];
    fit.GLS1 = glsFit(P, fit.vol[0], fit.vol[1], s2);
    fit.GLS2 = glsFit(P, fit.GLS1[0], fit.GLS1[1], s2);
    fit['GLS*'] = glsFit(P, lam, th, sig2);
    for (const n of names) {
      est[n].lam.push(fit[n][0]); est[n].th.push(fit[n][1]);
      est[n].loss += blupLoss(fit[n][0], fit[n][1], s2, mh, mu);
    }
    oracle += blupLoss(lam, th, sig2, mh, mu);
    // no groups: BS τ̂² (volume-weighted moment estimator over all pairs, ignoring the groups)
    let a = 0, b = 0; pairs.forEach(([i, j], p) => { a += w[i] * w[j] * P[p]; b += w[i] * w[j]; });
    nogrp += blupLoss(a / b / 2, 0, s2, mh, mu);
  }
  const mean = (x) => x.reduce((a, b) => a + b, 0) / x.length;
  const sd = (x) => { const m = mean(x); return Math.sqrt(x.reduce((a, b) => a + (b - m) ** 2, 0) / (x.length - 1)); };
  const out = { th, lam, rows: {} };
  for (const n of names) out.rows[n] = { bTh: mean(est[n].th) / th - 1, sTh: sd(est[n].th) / th, bLam: mean(est[n].lam) / lam - 1, sLam: sd(est[n].lam) / lam, mse: 100 * est[n].loss / oracle };
  out.nogrp = 100 * nogrp / oracle;
  return out;
}

// Optional third argument: run only world number k (0–15), for parallel runs.
const only = process.argv[3] === undefined ? null : +process.argv[3];
const worlds = [];
for (const sizes of [[8, 4], [5, 3, 2, 2]]) for (const T of [3, 6]) for (const phi of [0.3, 0.7]) for (const noise of ['exp', 'norm'])
  worlds.push({ sizes, T, phi, noise });
console.log(`${draws} draws per world. θ = φτ², λ = (1 − φ)τ²: relative bias and SD (in units of the true value);`);
console.log('MSE of the blend in % of the BLUP with true parameters.\n');
console.log('groups     T  φ    noise | fit    bias θ   SD θ  bias λ   SD λ   MSE');
for (const [k, wd] of worlds.entries()) {
  if (only !== null && k !== only) continue;
  seed = 12345 + 7919 * k;
  const r = runWorld(wd);
  const tag = `${wd.sizes.join('+').padEnd(9)} ${wd.T}  ${wd.phi}  ${wd.noise.padEnd(4)}`;
  for (const [n, x] of Object.entries(r.rows))
    console.log(`${tag}  | ${n.padEnd(5)} ${x.bTh.toFixed(2).padStart(6)} ${x.sTh.toFixed(2).padStart(6)} ${x.bLam.toFixed(2).padStart(6)} ${x.sLam.toFixed(2).padStart(6)} ${x.mse.toFixed(1).padStart(6)}`);
  console.log(`${tag}  | nogrp                                ${r.nogrp.toFixed(1).padStart(6)}`);
}
