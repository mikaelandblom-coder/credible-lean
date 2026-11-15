// Can the fit estimate its own error? Jackknife MSEP (Jiang, Lahiri & Wan 2002, Ann. Stat.),
// deleting one year at a time (independent years), for the variance-credibility fit of
// variance-credibility.js. Predicted MSEP per region against the actual MSE over many draws.
// Run: node studies/msep.js [draws]
'use strict';
const E = require('../app/engine.js');
const N = +(process.argv[2] || 1000);
const sum = (a) => a.reduce((s, x) => s + x, 0);

// Design (known): wⱼ*, Sᵢⱼ. Parameters from the years in `ts`: σ̃ⱼ², ρ̂, τ̂².
function design(w) {
  const J = w.length, T = w[0].length, wt = w.map(sum), S = [];
  for (let i = 0; i < J; i++) { S.push([]); for (let j = 0; j < J; j++) { let s = 0; for (let t = 0; t < T; t++) s += Math.sqrt(w[i][t] * w[j][t]); S[i].push(s); } }
  return { J, T, wt, S };
}
function params(data) {
  const J = data.X.length, T = data.X[0].length, { wt, m } = E.cohortMeans(data), { S } = design(data.w), Q = [];
  for (let i = 0; i < J; i++) { Q.push([]); for (let j = 0; j < J; j++) { let q = 0; for (let t = 0; t < T; t++) q += Math.sqrt(data.w[i][t] * data.w[j][t]) * (data.X[i][t] - m[i]) * (data.X[j][t] - m[j]); Q[i].push(q); } }
  const own = Q.map((row, j) => row[j] / (T - 1)), pooled = sum(own) / J;
  const W = own.map((sj, j) => { const u = data.X[j].map((x, t) => data.w[j][t] * (x - m[j]) ** 2 * T / (T - 1)); return sum(u.map((x) => (x - sj) ** 2)) / (T * (T - 1)); });
  const between = Math.max(0, sum(own.map((x) => (x - pooled) ** 2)) / (J - 1) - sum(W) / J);
  const s2 = own.map((x, j) => { const ze = between > 0 ? between / (between + W[j]) : 0; return ze * x + (1 - ze) * pooled; });
  const sd = s2.map(Math.sqrt);
  let qn = 0, qa = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { qn += Q[i][j]; qa += sd[i] * sd[j] * ((T - 2) + S[i][j] ** 2 / (wt[i] * wt[j])); }
  const rho = Math.min(Math.max(qn / qa, 0), 1 - 1e-9);
  const Sig = S.map((row, i) => row.map((x, j) => (i === j ? s2[i] / wt[i] : rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
  const t2 = Math.max(E.thesisTau(m, wt, Sig).tau2, 0);
  return { s2, rho, t2 };
}
// Rates and the known-parameter MSE g₁₂ⱼ for parameters p, on the full design and full means m.
function blendWith(p, des, m) {
  const { J, wt, S } = des, sd = p.s2.map(Math.sqrt);
  const K = S.map((row, i) => row.map((x, j) => (i === j ? p.s2[i] / wt[i] + p.t2 : p.rho * sd[i] * sd[j] * x / (wt[i] * wt[j]))));
  const { b, z, s2 } = E.bestBlendWeights(K, p.t2);
  const zz = p.t2 > 0 ? z : z.map(() => 0);
  const rates = E.blend(m, zz, b).rates;
  const g = Array.from({ length: J }, (_, j) => E.blendMSE(K, p.t2, b, s2, j, zz[j]));
  return { rates, g };
}
function msep(data) {
  const des = design(data.w), { T, J } = des, m = E.cohortMeans(data).m;
  const full = blendWith(params(data), des, m);
  const gDel = Array(J).fill(0), rDel = Array(J).fill(0);
  for (let t = 0; t < T; t++) {
    const d = { w: data.w.map((r) => r.filter((_, u) => u !== t)), X: data.X.map((r) => r.filter((_, u) => u !== t)) };
    const o = blendWith(params(d), des, m);
    for (let j = 0; j < J; j++) { gDel[j] += o.g[j] - full.g[j]; rDel[j] += (o.rates[j] - full.rates[j]) ** 2; }
  }
  const c = (T - 1) / T;
  return { rates: full.rates, naive: full.g, jack: full.g.map((g, j) => g - c * gDel[j] + c * rDel[j]), g3: rDel.map((x) => c * x) };
}

const LAWS = { normal: (r) => r.normal(), gamma2: (r) => (r.gamma(2) - 2) / Math.SQRT2, 'gamma¼': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; } };
function run(label, J, T, sigF, rho, law) {
  const world = E.makeWorld({ J, T }), { w } = world, tau2 = world.truth.tau2, s = Math.sqrt(world.truth.sigma2);
  const sig = sigF.map((f) => s * f), r = E.rng(11), L = LAWS[law];
  const act = Array(J).fill(0), nai = Array(J).fill(0), jac = Array(J).fill(0), g3 = Array(J).fill(0);
  for (let n = 0; n < N; n++) {
    const levels = Array.from({ length: J }, () => 1 + Math.sqrt(tau2) * (r.gamma(4) - 4) / 2);
    const eta = Array.from({ length: T }, () => L(r));
    const X = levels.map((lv, j) => Array.from({ length: T }, (_, t) => lv + sig[j] / Math.sqrt(w[j][t]) * (Math.sqrt(rho) * eta[t] + Math.sqrt(1 - rho) * L(r))));
    const o = msep({ w, X });
    for (let j = 0; j < J; j++) { act[j] += (o.rates[j] - levels[j]) ** 2; nai[j] += o.naive[j]; jac[j] += o.jack[j]; g3[j] += o.g3[j]; }
  }
  const wt = w.map(sum), tot = (a) => sum(a.map((x, j) => x * wt[j]));
  const ratios = (a) => a.map((x, j) => x / act[j]);
  const rng = (a) => `${Math.min(...a).toFixed(2)}–${Math.max(...a).toFixed(2)}`;
  console.log(`${label.padEnd(30)} ${law.padEnd(7)} | ${(tot(nai) / tot(act)).toFixed(2)} (${rng(ratios(nai))}) | ${(tot(jac) / tot(act)).toFixed(2)} (${rng(ratios(jac))}) | ${(100 * tot(g3) / tot(jac)).toFixed(0)}%`);
}
console.log(`draws ${N}. Predicted / actual MSE, exposure-weighted over regions (range over regions). 1.00 = right on average.`);
console.log('world                          law     | naive g₁₂(θ̂)       | jackknife MSEP      | share of g₃');
for (const [J, T] of [[8, 5], [8, 10], [20, 10]]) {
  const one = Array(J).fill(1), spread = Array.from({ length: J }, (_, j) => Math.pow(4, (j % 4) / 3 - 0.5));
  for (const law of Object.keys(LAWS)) {
    run(`J=${J} T=${T} equal σ, ρ = 0`, J, T, one, 0, law);
    run(`J=${J} T=${T} equal σ, ρ = 0.6`, J, T, one, 0.6, law);
    run(`J=${J} T=${T} σⱼ spread, ρ = 0.6`, J, T, spread, 0.6, law);
  }
}
