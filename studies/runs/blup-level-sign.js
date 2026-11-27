// Purpose: Finding 40. Search for worlds where the level part of the first-order cross term of the
// plug-in BLUP on corrBS's K̂ is positive (studies/runs/blup-level-sign.py has the formula and the exact check).
// Hill climbing over volumes wⱼₜ = exp(size + year), ρ and τ², reporting the largest level part per unit γL
// relative to the region's BLUP MSE. Args: seed ρmax sizeRatio yearRatio [J T].
// Run: node studies/runs/blup-level-sign.js 7 0.9 16 100
const PF = require('./price-formula.js');
const sum = (a) => a.reduce((x, y) => x + y, 0);
let s0 = +(process.argv[2] || 7); const u = () => { s0 = (s0 * 1664525 + 1013904223) >>> 0; return s0 / 4294967296; };
const RHOMAX = +(process.argv[3] || 0.6), LOGR = Math.log(+(process.argv[4] || 16));
// relative level part per unit γL: 2τ⁴ Σ m(d−δ)∂d/∂B / mse_j
function rel(w, rho, t2, j) {
  const J = w.length, D = PF.design(w), P = 1, Qn = rho * P * D.A0, { wt, wall, S } = D;
  const Sig = S.map((row, i) => row.map((x, k) => (i === k ? P / wt[i] : rho * P * x / (wt[i] * wt[k]))));
  const cj = Sig.map((_, k) => sum(Sig.map((row, i) => ((i === k ? 1 : 0) - wt[i] / wall) * row[k])));
  const B = t2 * D.c0 + sum(wt.map((x, k) => x * cj[k])), h = 1e-5 * t2 * D.c0;
  const m = wt.map((x) => x * (1 - x / wall));
  const d = PF.weights(D, [P, Qn, B], 'blup', false)[j], dp = PF.weights(D, [P, Qn, B + h], 'blup', false)[j], dm = PF.weights(D, [P, Qn, B - h], 'blup', false)[j];
  let v = 0; for (let p = 0; p < J; p++) v += m[p] * (d[p] - (p === j ? 1 : 0)) * (dp[p] - dm[p]) / (2 * h);
  const K = Sig.map((row, i) => row.map((x, k) => (i === k ? x + t2 : x)));
  const mse = sum(d.map((di, i) => di * sum(d.map((dk, k) => K[i][k] * dk)))) - 2 * t2 * d[j] + t2;
  return 2 * t2 * t2 * v / mse;
}
const YR = Math.log(+(process.argv[5] || 2)) ; const mk = (x, J, T) => Array.from({ length: J }, (_, i) => Array.from({ length: T }, (_, t) => Math.exp(Math.max(-LOGR / 2, Math.min(LOGR / 2, x.sz[i])) + Math.max(-YR, Math.min(YR, x.yr[i * T + t])))));
let best = -Infinity, arg;
for (let r = 0; r < 150; r++) {
  const J = +(process.argv[6] || 0) || 2 + Math.floor(u() * 9), T = +(process.argv[7] || 0) || 2 + Math.floor(u() * 6), j = Math.floor(u() * J);
  let x = { sz: Array.from({ length: J }, () => (u() - 0.5) * LOGR), yr: Array.from({ length: J * T }, () => (u() - 0.5) * 1.4), rho: u() * RHOMAX, lt2: Math.log(10 ** ((u() - 0.5) * 3)) - Math.log(T) };
  const F = (x) => rel(mk(x, J, T), x.rho, Math.exp(x.lt2), j);
  let f = F(x), step = 1;
  for (let it = 0; it < 1500; it++) {
    const y = { sz: x.sz.map((a) => a + (u() < 0.3 ? (u() - 0.5) * step : 0)), yr: x.yr.map((a) => a + (u() < 0.2 ? (u() - 0.5) * step : 0)), rho: Math.min(RHOMAX, Math.max(0, x.rho + (u() - 0.5) * 0.1 * step)), lt2: x.lt2 + (u() - 0.5) * step };
    const g = F(y); if (isFinite(g) && g > f) { x = y; f = g; } else step = Math.max(0.05, step * 0.998);
  }
  if (f > best) { best = f; arg = { J, T, j, rho: +x.rho.toFixed(3), t2: +Math.exp(x.lt2).toPrecision(3), w: mk(x, J, T).map((r) => r.map((a) => +a.toFixed(3))) }; }
}
console.log('max rel level part per γL:', best.toPrecision(4), JSON.stringify(arg));
