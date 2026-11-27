// S67: S66's next step. Vector levels (F × S, level + slope per cohort) with year shocks: does a fit that
// models the shocks beat S66's default (exposure-weighted Λ̂, damped off-diagonals, independent cohorts),
// and why did off-diagonals pay more under shocks in S66? Purpose: decide, and check S66's guess.
// World: studies/vector-lambda-damp.js (cell noises of one year and component correlate across cohorts,
//   cov = ρ sᶜ²/√(wⱼₜ wᵢₜ)); frequency–severity correlation −0.6 throughout (S65–S66: it rarely matters).
// Estimates (data only):
//   ρ̂ᶜ — standardized line residuals ẽⱼₜ = rⱼₜ √wⱼₜ / ŝᶜ, ρ̂ᶜ = Σ_{i<j} Σₜ ẽⱼₜ ẽᵢₜ / (J(J−1)/2 · (T − 2)). In this
//     world every cohort's exposures have the same shape (wⱼₜ = wⱼ·1.05ᵗ), so the weighted hat matrices agree
//     and E Σₜ ẽⱼₜẽᵢₜ = ρ tr(I − H) = ρ(T − 2) (up to ŝ²);
//   N̂ — the noise covariance of the stacked line estimates β̂ⱼ (cohort × component), from ŝ², ρ̂;
//   corrected moment Λ̂ for any noise covariance N between cohorts and weights ωⱼ (Σωⱼ = 1):
//     E Σⱼ ωⱼ (β̂ⱼ − β̄)(β̂ⱼ − β̄)ᵀ = (1 − Σωⱼ²)Λ + Σⱼ ωⱼNⱼⱼ − Σᵢ Σₖ ωᵢωₖNᵢₖ, so
//     Λ̂ = [Σⱼ ωⱼ eⱼeⱼᵀ − Σⱼ ωⱼN̂ⱼⱼ + Σᵢ Σₖ ωᵢωₖN̂ᵢₖ] / (1 − Σωⱼ²) (N block diagonal: S66's estimator).
//     Ignoring the cross terms biases Λ̂ by −ΣΣ_{i≠k} ωᵢωₖNᵢₖ/(1 − Σω²): the shocks are partly read as
//     a smaller spread of the cohorts' lines.
// Fits: dampW (S66, the baseline: shocks ignored); dampWc (Λ̂ corrected, still an independent-cohort predictor);
//   jointDiag, jointDamp (corrected Λ̂ diagonal / damped, joint K̂ = I ⊗ Λ̂ + N̂, the joint BLUP over cohorts ×
//   components); oracle: the joint BLUP with the true Λ, s², ρ.
// Output: dampW in % above the oracle, the others minus dampW (negative = better), paired ± 2 SE, F | Y;
//   mean ρ̂ (F) and the relative bias of Λ̂'s level and slope variances for F, uncorrected / corrected.
// Run: node studies/vector-lambda-shocks.js [draws]
'use strict';
const { grid, paired, meanSE, pm } = require('./lib.js');
const { zeros, add, mv, inv, psd, restrict, predict, world, Smat, loss } = require('./vector-lambda.js');
const { draw, lambdaHat, damped } = require('./vector-lambda-damp.js');
const N = +(process.argv[2] || 1000);

// Noise covariance of the stacked β̂ (index 4j + k), components c = k >> 1, level/slope k & 1.
function noiseCov(d, s2, rho) {
  const J = d.bh.length, T = d.w[0].length, n = 4 * J, M = zeros(n, n);
  for (let j = 0; j < J; j++) for (let i = 0; i < J; i++) for (let k = 0; k < 4; k++) for (let l = 0; l < 4; l++) {
    if ((k >> 1) !== (l >> 1)) continue;
    const c = k >> 1, gk = d.g[j][k & 1], gl = d.g[i][l & 1];
    let v = 0;
    for (let t = 0; t < T; t++) v += gk[t] * gl[t] * s2[c] * (j === i ? 1 / d.w[j][t] : rho[c] / Math.sqrt(d.w[j][t] * d.w[i][t]));
    M[4 * j + k][4 * i + l] = v;
  }
  return M;
}
function jointBlup(d, Lam, Nn) {
  const J = d.bh.length, n = 4 * J, K = Nn.map((r) => r.slice());
  for (let j = 0; j < J; j++) for (let k = 0; k < 4; k++) for (let l = 0; l < 4; l++) K[4 * j + k][4 * j + l] += Lam[k][l] + (k === l ? 1e-9 : 0);
  const Ki = inv(K), x = d.bh.flat(), H = zeros(4, 4), g = [0, 0, 0, 0];
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) { H[a & 3][b & 3] += Ki[a][b]; g[a & 3] += Ki[a][b] * x[b]; }
  const m = mv(inv(H), g), Kr = mv(Ki, x.map((y, a) => y - m[a & 3]));
  return d.bh.map((_, j) => m.map((mk, k) => mk + Lam[k].reduce((s, lkl, l) => s + lkl * Kr[4 * j + l], 0)));
}
// ρ̂ per component from the line residuals (needs the residuals: recomputed from d).
function rhoHat(d, s2h) {
  const J = d.bh.length, T = d.w[0].length;
  return [0, 1].map((c) => {
    const e = d.bh.map((b, j) => d.X[j][c].map((x, t) => (x - b[2 * c] - b[2 * c + 1] * d.u[j][t]) * Math.sqrt(d.w[j][t] / s2h[c])));
    let s = 0; for (let j = 0; j < J; j++) for (let i = j + 1; i < J; i++) for (let t = 0; t < T; t++) s += e[j][t] * e[i][t];
    return s / ((J * (J - 1)) / 2 * (T - 2));
  });
}
// Corrected weighted moment Λ̂ (adds back the cross-cohort noise terms).
function lambdaCorr(d, S, Nn) {
  const J = d.bh.length, { Lh, Cs } = lambdaHat(d, S, true), om = d.wt.map((x) => x / d.wt.reduce((s, y) => s + y, 0));
  const s2om = om.reduce((s, x) => s + x * x, 0), X = zeros(4, 4);
  for (let j = 0; j < J; j++) for (let i = 0; i < J; i++) if (i !== j) for (let k = 0; k < 4; k++) for (let l = 0; l < 4; l++) X[k][l] += om[j] * om[i] * Nn[4 * j + k][4 * i + l];
  return { Lh: Lh.map((r, k) => r.map((x, l) => x + X[k][l] / (1 - s2om))), Cs };
}

const FITS = ['dampWc', 'jointDiag', 'jointDamp'];
function run(o) {
  const W = Object.assign(world(o), { rho: o.rho }), all = ['oracle', 'dampW'].concat(FITS);
  const L = Object.fromEntries(all.map((f) => [f, [[], []]])), rh = [], bias = [[], [], [], []];
  for (let n = 0; n < N; n++) {
    const d = draw(W), J = o.J, s2h = d.rss.map((r) => r / (J * (o.T - 2)));
    const S = d.Sraw.map((r) => Smat(r, s2h)), r = rhoHat(d, s2h);
    const Nh = noiseCov(d, s2h, r), Ntrue = noiseCov(d, W.s2, [o.rho, o.rho]);
    const w = lambdaHat(d, S, true), c = lambdaCorr(d, S, Nh);
    const dw = damped(w.Lh, w.Cs, J), dc = damped(c.Lh, c.Cs, J);
    rh.push(r[0]);
    bias[0].push(w.Lh[0][0] / W.Lam[0][0] - 1); bias[1].push(c.Lh[0][0] / W.Lam[0][0] - 1);
    bias[2].push(w.Lh[1][1] / W.Lam[1][1] - 1); bias[3].push(c.Lh[1][1] / W.Lam[1][1] - 1);
    const P = {
      oracle: jointBlup(d, W.Lam, Ntrue), dampW: predict(d.bh, S, dw.L), dampWc: predict(d.bh, S, dc.L),
      jointDiag: jointBlup(d, restrict(c.Lh, 'diag'), Nh), jointDamp: jointBlup(d, dc.L, Nh),
    };
    for (const f of all) { const l = loss(d, P[f]); L[f][0].push(l[0]); L[f][1].push(l[1]); }
  }
  const floor = [0, 1].map((c) => meanSE(L.oracle[c]).m);
  const cell = (f, g) => [0, 1].map((c) => pm(paired(L[f][c], L[g][c]), 100 / floor[c])).join(' | ');
  const pc = (x) => (100 * meanSE(x).m).toFixed(0);
  return { base: cell('dampW', 'oracle'), rest: FITS.map((f) => cell(f, 'dampW')), rho: meanSE(rh).m, bias: bias.map(pc) };
}

if (require.main === module) {
  const axes = { rho: [0, 0.3, 0.6], rab: [0, 0.7], J: [10, 30], T: [5, 8], zF: [0.5, 0.85] };
  console.log(`vector-lambda-shocks (S67): ${N} draws per world; volume 500; τ_a = 1, τ_b = 0.15/yr; severity noise 4×; rFY = −0.6.`);
  console.log('dampW: MSE in % above the joint oracle; other fits minus dampW (negative = better), ± 2 SE; F | Y.');
  console.log('ρ̂: mean (F). bias: Λ̂ level var F uncorr/corr, slope var F uncorr/corr, mean relative bias in %.');
  console.log('rho rab   J  T  zF  | dampW | ' + FITS.join(' | ') + ' | ρ̂ | bias');
  for (const o of grid(axes)) {
    const r = run(Object.assign({ volume: 500, rFY: -0.6 }, o));
    console.log(`${o.rho.toFixed(1)} ${o.rab.toFixed(1)} ${String(o.J).padStart(3)} ${String(o.T).padStart(2)} ${o.zF.toFixed(2)} | ` +
      [r.base].concat(r.rest).join('  ;  ') + `  ;  ${r.rho.toFixed(3)}  ;  ${r.bias[0]}/${r.bias[1]} ${r.bias[2]}/${r.bias[3]}`);
  }
}
module.exports = { noiseCov, jointBlup, rhoHat, lambdaCorr };
