// S66: S65's next step. Vector levels (F × S, level + slope per cohort): can a fitted Λ̂ with
// off-diagonals beat the diagonal one if they are damped, if Λ̂ is weighted, or with year shocks?
// Purpose: decide (the default for the app's "cohort trend lines" step). World and fits as
// studies/vector-lambda.js (S65), plus:
//   year shocks: the cell noises of one year and component correlate across cohorts,
//     cov(εⱼₜ, εᵢₜ) = ρ sᶜ² / √(wⱼₜ wᵢₜ) (the thesis's ρ); the fits still assume independent cohorts,
//     the oracle is the joint BLUP over cohorts × components with the true K (not block diagonal);
//   damp  — the diagonal fit plus θ̂ × the off-diagonals of Λ̂, projected PSD (θ̂ = 0 is `diag`; damping a PSD
//     matrix would stay PSD, `OffDiagonal.lean`, but Λ̂ is not PSD, so the projection is needed), θ̂ the
//     plug-in table-optimal θ* = Σr²/(Σr² + ΣV) of `Damping.lean` on the correlation scale:
//     r̂ₖₗ = Λ̂ₖₗ/√(ĈₖₖĈₗₗ), V̂ₖₗ = (1 + ρ̂ₖₗ²)/(J − 1) (normal-theory variance of a sample covariance, Ĉ the
//     sample covariance of the β̂ⱼ), θ̂ = max(0, 1 − ΣV̂/Σr̂²) (r² estimated by r̂² − V̂);
//   ...W  — the exposure-weighted moment estimate: ωⱼ ∝ Σₜ wⱼₜ, β̄ = Σ ωⱼ β̂ⱼ,
//     Λ̂ = [Σ ωⱼ (β̂ⱼ − β̄)(β̂ⱼ − β̄)ᵀ − Σ ωⱼ(1 − ωⱼ) Ŝⱼ] / (1 − Σ ωⱼ²) (unbiased for independent cohorts).
// Output: diag's MSE in % above the oracle, then each fit minus diag (negative: better than diag),
// paired ± 2 SE, F | Y. Run: node studies/vector-lambda-damp.js [draws]
'use strict';
const { grid, paired, meanSE, pm } = require('./lib.js');
const V = require('./vector-lambda.js');
const { zeros, add, mv, inv, psd, normal, restrict, predict, world, Smat, loss } = V;
const N = +(process.argv[2] || 1000);

function draw(W) {
  const { J, T, volume, Lc, s2, rho } = W;
  const out = { bh: [], Sraw: [], tgt: [], x0: [], wt: [], rss: [0, 0], g: [], w: [], X: [], u: [] };
  const f = [0, 1].map(() => Array.from({ length: T }, () => normal())); // year shocks per component
  for (let j = 0; j < J; j++) {
    const wj = volume * Math.exp(0.5 * normal() - 0.125), w = Array.from({ length: T }, (_, t) => wj * 1.05 ** (t + 1));
    const sw = w.reduce((s, x) => s + x, 0), tbar = w.reduce((s, x, t) => s + x * (t + 1), 0) / sw;
    const u = w.map((_, t) => t + 1 - tbar), suu = w.reduce((s, x, t) => s + x * u[t] ** 2, 0);
    const beta = mv(Lc, [normal(), normal(), normal(), normal()]), bh = [0, 0, 0, 0], Xs = [];
    for (const c of [0, 1]) {
      const a = beta[2 * c], b = beta[2 * c + 1];
      const X = w.map((x, t) => a + b * u[t] + Math.sqrt(s2[c] / x) * (Math.sqrt(1 - rho) * normal() + Math.sqrt(rho) * f[c][t]));
      const ah = X.reduce((s, x, t) => s + w[t] * x, 0) / sw, bhat = X.reduce((s, x, t) => s + w[t] * u[t] * x, 0) / suu;
      bh[2 * c] = ah; bh[2 * c + 1] = bhat; Xs.push(X);
      out.rss[c] += X.reduce((s, x, t) => s + w[t] * (x - ah - bhat * u[t]) ** 2, 0);
    }
    out.bh.push(bh); out.Sraw.push([1 / sw, 1 / suu]); out.wt.push(sw); out.w.push(w); out.X.push(Xs); out.u.push(u);
    out.g.push([w.map((x) => x / sw), w.map((x, t) => (x * u[t]) / suu)]); // β̂ = Σₜ gₜ Xₜ (level, slope)
    const h = T + 1 - tbar; out.x0.push(h); out.tgt.push([beta[0] + beta[1] * h, beta[2] + beta[3] * h]);
  }
  return out;
}

// Joint BLUP over (cohort, component) with the true K = I ⊗ Λ + noise covariance (year shocks across cohorts).
function oracleJoint(d, W) {
  const J = W.J, T = W.T, n = 4 * J, K = zeros(n, n), Lam = W.Lam;
  for (let j = 0; j < J; j++) for (let i = 0; i < J; i++) for (let k = 0; k < 4; k++) for (let l = 0; l < 4; l++) {
    let v = j === i ? Lam[k][l] : 0;
    if ((k >> 1) === (l >> 1)) {
      const c = k >> 1, gk = d.g[j][k & 1], gl = d.g[i][l & 1];
      for (let t = 0; t < T; t++) v += gk[t] * gl[t] * W.s2[c] * (j === i ? 1 / d.w[j][t] : W.rho / Math.sqrt(d.w[j][t] * d.w[i][t]));
    }
    K[4 * j + k][4 * i + l] = v;
  }
  const Ki = inv(K), x = d.bh.flat();
  // m̂ = (XᵀK⁻¹X)⁻¹XᵀK⁻¹x with X = 1_J ⊗ I₄.
  const H = zeros(4, 4), g = [0, 0, 0, 0];
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) { H[a & 3][b & 3] += Ki[a][b]; g[a & 3] += Ki[a][b] * x[b]; }
  const m = mv(inv(H), g), r = x.map((y, a) => y - m[a & 3]), Kr = mv(Ki, r);
  // pred βⱼ = m + Λ (K⁻¹ r)ⱼ (Cov(β, β̂) = I ⊗ Λ).
  return d.bh.map((_, j) => m.map((mk, k) => mk + Lam[k].reduce((s, lkl, l) => s + lkl * Kr[4 * j + l], 0)));
}

function lambdaHat(d, S, weighted) {
  const J = d.bh.length, om = weighted ? d.wt.map((x) => x / d.wt.reduce((s, y) => s + y, 0)) : d.bh.map(() => 1 / J);
  const bbar = [0, 1, 2, 3].map((k) => d.bh.reduce((s, b, j) => s + om[j] * b[k], 0)), s2om = om.reduce((s, x) => s + x * x, 0);
  let C = zeros(4, 4), Sb = zeros(4, 4);
  d.bh.forEach((b, j) => { const e = b.map((x, k) => x - bbar[k]); C = add(C, e.map((x) => e.map((y) => om[j] * x * y))); });
  S.forEach((Sj, j) => { Sb = add(Sb, Sj.map((r) => r.map((x) => om[j] * (1 - om[j]) * x))); });
  const Lh = C.map((r, k) => r.map((x, l) => (x - Sb[k][l]) / (1 - s2om)));
  const Cs = C.map((r) => r.map((x) => x / (1 - s2om))); // ≈ sample covariance of the β̂ⱼ
  return { Lh, Cs };
}
function damped(Lh, Cs, J) {
  let sr = 0, sv = 0;
  for (let k = 0; k < 4; k++) for (let l = k + 1; l < 4; l++) {
    const den = Math.sqrt(Cs[k][k] * Cs[l][l]); if (!(den > 0)) continue;
    const r = Lh[k][l] / den, rc = Cs[k][l] / den; sr += r * r; sv += (1 + rc * rc) / (J - 1);
  }
  const th = sr > 0 ? Math.max(0, 1 - sv / sr) : 0;
  // Start from the diagonal fit (θ = 0 is exactly `diag`), add θ × the off-diagonals, project onto PSD.
  return { L: psd(Lh.map((row, k) => row.map((x, l) => (k === l ? Math.max(x, 0) : th * x)))), th };
}

const FITS = ['block', 'full', 'damp', 'diagW', 'fullW', 'dampW'];
function run(o) {
  const W = Object.assign(world(o), { rho: o.rho }), all = ['oracle', 'diag'].concat(FITS);
  const L = Object.fromEntries(all.map((f) => [f, [[], []]])), th = [];
  for (let n = 0; n < N; n++) {
    const d = draw(W), J = o.J, s2h = d.rss.map((r) => r / (J * (o.T - 2)));
    const S = d.Sraw.map((r) => Smat(r, s2h)), Strue = d.Sraw.map((r) => Smat(r, W.s2));
    const u = lambdaHat(d, S, false), w = lambdaHat(d, S, true), du = damped(u.Lh, u.Cs, J), dw = damped(w.Lh, w.Cs, J);
    th.push(du.th);
    const P = {
      oracle: o.rho > 0 ? oracleJoint(d, W) : predict(d.bh, Strue, W.Lam),
      diag: predict(d.bh, S, restrict(u.Lh, 'diag')), block: predict(d.bh, S, restrict(u.Lh, 'block')),
      full: predict(d.bh, S, restrict(u.Lh, 'full')), damp: predict(d.bh, S, du.L),
      diagW: predict(d.bh, S, restrict(w.Lh, 'diag')), fullW: predict(d.bh, S, restrict(w.Lh, 'full')), dampW: predict(d.bh, S, dw.L),
    };
    for (const f of all) { const l = loss(d, P[f]); L[f][0].push(l[0]); L[f][1].push(l[1]); }
  }
  const floor = [0, 1].map((c) => meanSE(L.oracle[c]).m);
  const cell = (f, g) => [0, 1].map((c) => pm(paired(L[f][c], L[g][c]), 100 / floor[c])).join(' | ');
  return { diag: cell('diag', 'oracle'), rest: FITS.map((f) => cell(f, 'diag')), th: meanSE(th).m };
}

module.exports = { draw, oracleJoint, lambdaHat, damped };

if (require.main === module) {
  const axes = { rho: [0, 0.3], rab: [0, 0.7], rFY: [0, -0.6], J: [10, 30], T: [5, 8], zF: [0.5, 0.85] };
  console.log(`vector-lambda-damp (S66): ${N} draws per world; volume 500; τ_a = 1, τ_b = 0.15/yr; severity noise 4×.`);
  console.log('diag: MSE in % above the oracle; other fits: minus diag (negative = better), ± 2 SE; each F | Y. θ̄: mean θ̂ (damp).');
  console.log('rho rab  rFY   J  T  zF  | diag | ' + FITS.join(' | ') + ' | θ̄');
  for (const o of grid(axes)) {
    const r = run(Object.assign({ volume: 500 }, o));
    console.log(`${o.rho.toFixed(1)} ${o.rab.toFixed(1)} ${o.rFY.toFixed(1).padStart(4)} ${String(o.J).padStart(3)} ${String(o.T).padStart(2)} ${o.zF.toFixed(2)} | ` +
      [r.diag].concat(r.rest).join('  ;  ') + `  ;  ${r.th.toFixed(2)}`);
  }
}
