// Credibility for the variances: σ̃ⱼ² = ζⱼ σ̂ⱼ² + (1 − ζⱼ) σ̂², ζⱼ = β²/(β² + Wⱼ), where
//   Wⱼ = estimated Var(σ̂ⱼ²) from the yearly terms (independent years),
//   β² = between-region variance of the σⱼ², by the moment equation (truncated at 0).
// Then the common correlation as a moment equation on standardised pairs:
//   E Qᵢⱼ ≈ ρ σᵢσⱼ ((T − 2) + Sᵢⱼ²/(wᵢ*wⱼ*)) → ρ̂ = Σ Qᵢⱼ / Σ σ̃ᵢσ̃ⱼ Aᵢⱼ.
// Everything from the data; no tuning. Run: node studies/variance-credibility.js [draws]
'use strict';
const E = require('../app/engine.js');
const { fitCBS } = require('./common-rho-mom.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

function fitVC(data, mode) { // mode: 'pooled' | 'own' | 'cred'
  const J = data.X.length, T = data.X[0].length, { wt, m } = E.cohortMeans(data);
  const S = [], Q = [];
  for (let i = 0; i < J; i++) { S.push([]); Q.push([]); for (let j = 0; j < J; j++) {
    let s = 0, q = 0;
    for (let t = 0; t < T; t++) { const c = Math.sqrt(data.w[i][t] * data.w[j][t]); s += c; q += c * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]); }
    S[i].push(s); Q[i].push(q);
  } }
  const own = Q.map((row, j) => row[j] / (T - 1)), pooled = sum(own) / J;
  let s2;
  if (mode === 'pooled') s2 = own.map(() => pooled);
  else if (mode === 'own') s2 = own;
  else {
    // Wⱼ: variance of the mean of T yearly terms uⱼₜ = wⱼₜ(Xⱼₜ − μ̂ⱼ)²·T/(T−1).
    const W = own.map((sj, j) => {
      const u = data.X[j].map((x, t) => data.w[j][t] * (x - m[j]) ** 2 * T / (T - 1));
      return sum(u.map((x) => (x - sj) ** 2)) / (T * (T - 1));
    });
    const between = Math.max(0, sum(own.map((x) => (x - pooled) ** 2)) / (J - 1) - sum(W) / J);
    s2 = own.map((x, j) => { const zeta = between > 0 ? between / (between + W[j]) : 0; return zeta * x + (1 - zeta) * pooled; });
  }
  const sd = s2.map(Math.sqrt);
  let qn = 0, qa = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { qn += Q[i][j]; qa += sd[i] * sd[j] * ((T - 2) + S[i][j] ** 2 / (wt[i] * wt[j])); }
  const rho = Math.min(Math.max(qn / qa, 0), 1 - 1e-9);
  const Sig = S.map((row, i) => row.map((x, j) => (i === j ? s2[i] / wt[i] : rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
  const t2 = Math.max(E.thesisTau(m, wt, Sig).tau2, 0);
  const K = Sig.map((row, i) => row.map((x, j) => (i === j ? x + t2 : x)));
  const { b, z } = E.bestBlendWeights(K, t2);
  return E.blend(m, t2 > 0 ? z : z.map(() => 0), b).rates;
}
module.exports = { fitVC };

const LAWS = { 'two-point': (r) => (r() < 0.5 ? -1 : 1), normal: (r) => r.normal(), gamma2: (r) => (r.gamma(2) - 2) / Math.SQRT2, 'gamma¼': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; } };
function run(label, J, T, sigF, groups, rw, rb, law) {
  const world = E.makeWorld({ J, T }), { w } = world, tau2 = world.truth.tau2, s = Math.sqrt(world.truth.sigma2);
  const wt = w.map(sum), sig = sigF.map((f) => s * f), K = [];
  for (let i = 0; i < J; i++) { K.push([]); for (let j = 0; j < J; j++) {
    let S = 0; for (let t = 0; t < T; t++) S += Math.sqrt(w[i][t] * w[j][t]);
    K[i].push(sig[i] * sig[j] * (i === j ? 1 : groups[i] === groups[j] ? rw : rb) * S / (wt[i] * wt[j]) + (i === j ? tau2 : 0));
  } }
  const fl = E.bestBlendWeights(K, tau2), r = E.rng(7), G = Math.max(...groups) + 1, L = LAWS[law];
  const a = { fl: 0, bs: 0, full: 0, pooled: 0, own: 0, cred: 0 };
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * (r.gamma(4) - 4) / 2);
    const eta = Array.from({ length: T }, () => L(r)), etaG = Array.from({ length: G }, () => Array.from({ length: T }, () => L(r)));
    const X = levels.map((lv, j) => Array.from({ length: T }, (_, t) => lv + sig[j] / Math.sqrt(w[j][t]) * (Math.sqrt(rb) * eta[t] + Math.sqrt(rw - rb) * etaG[groups[j]][t] + Math.sqrt(1 - rw) * L(r))));
    const data = { w, X }, m = E.cohortMeans(data).m, se = (x) => E.weightedSE(data, x, levels);
    a.fl += se(E.blend(m, fl.z, fl.b).rates); a.bs += se(E.fitBS(data).rates); a.full += se(E.fitCorr(data).rates);
    for (const k of ['pooled', 'own', 'cred']) a[k] += se(fitVC(data, k));
  }
  const rel = (x) => (x / a.fl * 100).toFixed(0).padStart(4);
  console.log(`${label.padEnd(40)} ${law.padEnd(9)} | ${rel(a.bs)} ${rel(a.full)} | ${rel(a.pooled)} ${rel(a.own)} ${rel(a.cred)}`);
}
if (require.main === module) {
  console.log(`draws ${N}; error relative to the floor (100 = floor). corrBS variants: pooled σ̂² / own σ̂ⱼ² / credibility σ̃ⱼ²`);
  console.log('world                                    law       |   BS full | pool  own cred');
  for (const [J, T] of [[8, 5], [8, 10], [20, 10]]) {
    const one = Array(J).fill(1), spread = Array.from({ length: J }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5));
    const zero = one.map(() => 0), two = Array.from({ length: J }, (_, j) => j % 2);
    for (const law of ['two-point', 'gamma2', 'gamma¼']) {
      run(`J=${J} T=${T} equal σ, ρ = 0`, J, T, one, zero, 0, 0, law);
      run(`J=${J} T=${T} equal σ, ρ = 0.6`, J, T, one, zero, 0.6, 0.6, law);
      run(`J=${J} T=${T} σⱼ ×0.5–2, ρ = 0`, J, T, spread, zero, 0, 0, law);
      run(`J=${J} T=${T} σⱼ ×0.5–2, ρ = 0.6`, J, T, spread, zero, 0.6, 0.6, law);
      run(`J=${J} T=${T} σⱼ spread, countries .8/.2`, J, T, spread, two, 0.8, 0.2, law);
    }
  }
}
