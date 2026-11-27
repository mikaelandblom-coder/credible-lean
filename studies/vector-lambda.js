// Vector levels (frequency × severity, level and slope per cohort): does the fit need the full Λ?
// Purpose: decide (which Λ structure the app's "cohort trend" step should fit) and conjecture (when the
// off-diagonal entries pay for their estimation noise). notes/time-trends.md §1 step 3, §2; owner 2026-11-27.
//
// World (independent cohorts, the Bühlmann–Gisler setting; ρ = 0 between cohorts):
//   cohort j, year t = 1..T, exposure wⱼₜ = wⱼ·1.05^t, wⱼ lognormal(0, 0.5²) × volume;
//   components c ∈ {F, Y}: Xᶜⱼₜ = aᶜⱼ + bᶜⱼ (t − t̄ⱼ) + noise, var sᶜ²/wⱼₜ, noises independent
//   (compound model), t̄ⱼ the exposure-weighted mean year (Bühlmann–Gisler centring).
//   βⱼ = (a_F, b_F, a_Y, b_Y)ⱼ ~ N(m, Λ), Λ = D R D, D = diag(1, τ_b, 1, τ_b), R with
//   corr(a, b) = rab within a component, corr(a_F, a_Y) = corr(b_F, b_Y) = rFY across, and
//   corr(a_F, b_Y) = corr(b_F, a_Y) = rab·rFY (a Kronecker R = R_comp ⊗ R_ab, always PD).
//   Target: next year's level aᶜⱼ + bᶜⱼ (T + 1 − t̄ⱼ), per component.
// Fits (data only; s² pooled from the lines' residuals, Λ̂ the unbiased moment estimate
//   (1/(J−1)) Σ (β̂ⱼ − β̄)(β̂ⱼ − β̄)ᵀ − (1/J) Σ Ŝⱼ, projected onto the PSD cone within its structure):
//   diag  — Λ̂ diagonal (each component, level and slope independent: four scalar credibilities);
//   block — Λ̂ block diagonal over components (level–slope correlation kept, F and Y separate);
//   full  — the full 4 × 4 Λ̂.
//   Predictor for each: the matrix BLUP m̂ + Zⱼ(β̂ⱼ − m̂), Zⱼ = Λ(Λ + Ŝⱼ)⁻¹, m̂ the GLS mean
//   (Σ Kⱼ⁻¹)⁻¹ Σ Kⱼ⁻¹ β̂ⱼ, Kⱼ = Λ + Ŝⱼ (independent cohorts: blend = BLUP, `blendW_eq_blupW_of_blockDiag`).
//   Oracles: the same with true Λ, sᶜ² (floor) and with the true Λ's diagonal / blocks only (the price of
//   the assumption without estimation noise). Λ̂ singular: a small ridge 1e-9 keeps Kⱼ invertible.
// Output: exposure-weighted MSE of next year's level, per component, in % above the full oracle;
//   paired ± 2 SE (lib.paired). Run: node studies/vector-lambda.js [draws]
'use strict';
const { grid, paired, meanSE, pm } = require('./lib.js');
const N = +(process.argv[2] || 2000);

// --- small dense linear algebra (P = 4) ---
const zeros = (n, m) => Array.from({ length: n }, () => Array(m).fill(0));
const add = (A, B) => A.map((r, i) => r.map((x, j) => x + B[i][j]));
const mul = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, x, k) => s + x * B[k][j], 0)));
const mv = (A, v) => A.map((r) => r.reduce((s, x, k) => s + x * v[k], 0));
function inv(A) {
  const n = A.length, M = A.map((r, i) => r.concat(Array.from({ length: n }, (_, j) => (i === j ? 1 : 0))));
  for (let c = 0; c < n; c++) {
    let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    [M[c], M[p]] = [M[p], M[c]];
    const d = M[c][c]; for (let j = 0; j < 2 * n; j++) M[c][j] /= d;
    for (let r = 0; r < n; r++) if (r !== c) { const f = M[r][c]; for (let j = 0; j < 2 * n; j++) M[r][j] -= f * M[c][j]; }
  }
  return M.map((r) => r.slice(n));
}
// Symmetric eigen-decomposition (Jacobi), for the PSD projection (Frobenius: clip eigenvalues at 0).
function eigSym(A) {
  const n = A.length, a = A.map((r) => r.slice()), V = zeros(n, n); for (let i = 0; i < n; i++) V[i][i] = 1;
  for (let sweep = 0; sweep < 60; sweep++) {
    let off = 0; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) off += a[i][j] ** 2;
    if (off < 1e-22) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      if (Math.abs(a[p][q]) < 1e-300) continue;
      const th = (a[q][q] - a[p][p]) / (2 * a[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1));
      const c = 1 / Math.sqrt(t * t + 1), s = t * c;
      for (let k = 0; k < n; k++) { const x = a[k][p], y = a[k][q]; a[k][p] = c * x - s * y; a[k][q] = s * x + c * y; }
      for (let k = 0; k < n; k++) { const x = a[p][k], y = a[q][k]; a[p][k] = c * x - s * y; a[q][k] = s * x + c * y; }
      for (let k = 0; k < n; k++) { const x = V[k][p], y = V[k][q]; V[k][p] = c * x - s * y; V[k][q] = s * x + c * y; }
    }
  }
  return { vals: a.map((r, i) => r[i]), V };
}
function psd(A) {
  const S = A.map((r, i) => r.map((x, j) => (x + A[j][i]) / 2)), { vals, V } = eigSym(S), n = A.length;
  return Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) =>
    vals.reduce((s, l, k) => s + Math.max(l, 0) * V[i][k] * V[j][k], 0)));
}
function chol(A) {
  const n = A.length, L = zeros(n, n);
  for (let i = 0; i < n; i++) for (let j = 0; j <= i; j++) {
    let s = A[i][j]; for (let k = 0; k < j; k++) s -= L[i][k] * L[j][k];
    L[i][j] = i === j ? Math.sqrt(Math.max(s, 0)) : s / L[j][j];
  }
  return L;
}

// --- random numbers (seeded, so every fit sees the same draws) ---
let seed = 12345;
const unif = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return (seed + 0.5) / 2147483648; };
const normal = () => Math.sqrt(-2 * Math.log(unif())) * Math.cos(2 * Math.PI * unif());

// Structures: which entries of Λ a fit keeps (P order a_F, b_F, a_Y, b_Y; component of index i is i >> 1).
const keep = { diag: (i, j) => i === j, block: (i, j) => (i >> 1) === (j >> 1), full: () => true };
function restrict(L, kind) {
  if (kind === 'full') return psd(L);
  if (kind === 'diag') return L.map((r, i) => r.map((x, j) => (i === j ? Math.max(x, 0) : 0)));
  const out = zeros(4, 4);
  for (const c of [0, 2]) {
    const B = psd([[L[c][c], L[c][c + 1]], [L[c + 1][c], L[c + 1][c + 1]]]);
    out[c][c] = B[0][0]; out[c][c + 1] = B[0][1]; out[c + 1][c] = B[1][0]; out[c + 1][c + 1] = B[1][1];
  }
  return out;
}
const mask = (L, kind) => L.map((r, i) => r.map((x, j) => (keep[kind](i, j) ? x : 0)));

// Matrix BLUP for independent cohorts: predictions of βⱼ given estimates bh[j], noise covariances S[j], Λ.
function predict(bh, S, Lam) {
  const J = bh.length, ridge = 1e-9;
  const Kinv = S.map((Sj) => inv(add(add(Lam, Sj), [[ridge, 0, 0, 0], [0, ridge, 0, 0], [0, 0, ridge, 0], [0, 0, 0, ridge]])));
  let H = zeros(4, 4), g = [0, 0, 0, 0];
  for (let j = 0; j < J; j++) { H = add(H, Kinv[j]); g = g.map((x, k) => x + mv(Kinv[j], bh[j])[k]); }
  const m = mv(inv(H), g);
  return bh.map((b, j) => { const Z = mul(Lam, Kinv[j]); return m.map((x, k) => x + mv(Z, b.map((y, i) => y - m[i]))[k]); });
}

function world(o) {
  const tb = 0.15, D = [1, tb, 1, tb];
  const Rc = [[1, o.rFY], [o.rFY, 1]], Rab = [[1, o.rab], [o.rab, 1]];
  const R = zeros(4, 4); for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) R[i][j] = Rc[i >> 1][j >> 1] * Rab[i & 1][j & 1];
  const Lam = R.map((r, i) => r.map((x, j) => x * D[i] * D[j]));
  // Noise: level credibility of a typical cohort z_F = zF (frequency), severity sᶜ² four times larger.
  const wbar = o.volume * o.T; const sF2 = wbar * (1 - o.zF) / o.zF; // τ_a² = 1: z = 1/(1 + s²/(wT))
  return { Lam, Lc: chol(Lam), s2: [sF2, 4 * sF2], ...o };
}

function draw(W) {
  const { J, T, volume, Lc, s2 } = W, out = { bh: [], Sraw: [], tgt: [], x0: [], wt: [], rss: [0, 0] };
  for (let j = 0; j < J; j++) {
    const wj = volume * Math.exp(0.5 * normal() - 0.125), w = Array.from({ length: T }, (_, t) => wj * 1.05 ** (t + 1));
    const sw = w.reduce((s, x) => s + x, 0), tbar = w.reduce((s, x, t) => s + x * (t + 1), 0) / sw;
    const u = w.map((_, t) => t + 1 - tbar), suu = w.reduce((s, x, t) => s + x * u[t] ** 2, 0);
    const z = [normal(), normal(), normal(), normal()], beta = mv(Lc, z);
    const bh = [0, 0, 0, 0];
    for (const c of [0, 1]) {
      const a = beta[2 * c], b = beta[2 * c + 1];
      const X = w.map((x, t) => a + b * u[t] + Math.sqrt(s2[c] / x) * normal());
      const ah = X.reduce((s, x, t) => s + w[t] * x, 0) / sw, bhat = X.reduce((s, x, t) => s + w[t] * u[t] * x, 0) / suu;
      bh[2 * c] = ah; bh[2 * c + 1] = bhat;
      out.rss[c] += X.reduce((s, x, t) => s + w[t] * (x - ah - bhat * u[t]) ** 2, 0);
    }
    out.bh.push(bh); out.Sraw.push([1 / sw, 1 / suu]); out.wt.push(sw);
    const h = T + 1 - tbar; out.x0.push(h);
    out.tgt.push([beta[0] + beta[1] * h, beta[2] + beta[3] * h]);
  }
  return out;
}
const Smat = (raw, s2) => { const S = zeros(4, 4); S[0][0] = s2[0] * raw[0]; S[1][1] = s2[0] * raw[1]; S[2][2] = s2[1] * raw[0]; S[3][3] = s2[1] * raw[1]; return S; };
function loss(d, pred) {
  const sw = d.wt.reduce((s, x) => s + x, 0), out = [0, 0];
  pred.forEach((p, j) => { for (const c of [0, 1]) out[c] += d.wt[j] * (p[2 * c] + p[2 * c + 1] * d.x0[j] - d.tgt[j][c]) ** 2 / sw; });
  return out;
}

function run(o) {
  const W = world(o), fits = ['oracle', 'oDiag', 'oBlock', 'diag', 'block', 'full'], L = Object.fromEntries(fits.map((f) => [f, [[], []]]));
  for (let n = 0; n < N; n++) {
    const d = draw(W), J = o.J;
    const s2h = d.rss.map((r) => r / (J * (o.T - 2)));
    const S = d.Sraw.map((r) => Smat(r, s2h)), Strue = d.Sraw.map((r) => Smat(r, W.s2));
    const bbar = [0, 1, 2, 3].map((k) => d.bh.reduce((s, b) => s + b[k], 0) / J);
    let Lh = zeros(4, 4);
    d.bh.forEach((b) => { const e = b.map((x, k) => x - bbar[k]); Lh = add(Lh, e.map((x) => e.map((y) => (x * y) / (J - 1)))); });
    S.forEach((Sj) => { Lh = add(Lh, Sj.map((r) => r.map((x) => -x / J))); });
    const P = {
      oracle: predict(d.bh, Strue, W.Lam), oDiag: predict(d.bh, Strue, mask(W.Lam, 'diag')), oBlock: predict(d.bh, Strue, mask(W.Lam, 'block')),
      diag: predict(d.bh, S, restrict(Lh, 'diag')), block: predict(d.bh, S, restrict(Lh, 'block')), full: predict(d.bh, S, restrict(Lh, 'full')),
    };
    for (const f of fits) { const l = loss(d, P[f]); L[f][0].push(l[0]); L[f][1].push(l[1]); }
  }
  const floor = [meanSE(L.oracle[0]).m, meanSE(L.oracle[1]).m];
  const row = (f, c) => pm(paired(L[f][c], L.oracle[c]), 100 / floor[c]);
  const rowVs = (f, g, c) => pm(paired(L[f][c], L[g][c]), 100 / floor[c]);
  return { floor, row, rowVs };
}

const axes = { rab: [0, 0.7], rFY: [0, -0.6], J: [10, 30], T: [5, 8], zF: [0.5, 0.85] };
console.log(`vector-lambda: ${N} draws per world; volume 500; τ_a = 1, τ_b = 0.15/yr; severity noise 4× frequency.`);
console.log('MSE of next year\'s level in % above the full oracle (± 2 SE); F | Y. Last column: full − block.');
console.log('rab  rFY    J  T  zF   | oDiag          oBlock         | diag           block          full           | full−block');
for (const o of grid(axes)) {
  const r = run(Object.assign({ volume: 500 }, o)), cell = (f) => `${r.row(f, 0)} | ${r.row(f, 1)}`;
  console.log(`${o.rab.toFixed(1)}  ${o.rFY.toFixed(1).padStart(4)} ${String(o.J).padStart(3)} ${String(o.T).padStart(2)} ${o.zF.toFixed(2)} | ` +
    ['oDiag', 'oBlock', 'diag', 'block', 'full'].map(cell).join('  ;  ') + `  ;  ${r.rowVs('full', 'block', 0)} | ${r.rowVs('full', 'block', 1)}`);
}
