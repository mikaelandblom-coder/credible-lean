// Exact size of the winner's curse for merging two cohorts (paper §Open directions; notes/merging-cohorts.md
// §4 "Winner's curse"; Credibility/PreTestNormal.lean; Finding 43).
// Purpose: decide. Is there a threshold c for "merge iff (X₁ − X₂)² < c" that never loses to both
// always-merging and never-merging?
//
// World: two cohorts, fixed levels with gap δ = μ₁ − μ₂ (d = δ²), normal noise, V = Var(X₁ − X₂).
// Reduction (PreTestNormal.lean): with a = (v₁ − c₁₂)/V, the predictor X₁ − β(X₁ − X₂) has error
//   u + a·(D·m(D) − δ) up to sign,  D = X₁ − X₂ ~ N(δ, V),  u independent of D,
// where m = 0 when merged (β = a) and m = 1 − k when kept separate (β = a·k, k = V/(V + 2τ²) for the
// thesis rule, k = 0 for the cohort's own estimate). So every rule's excess over Var u is a²·R, R the
// risk of the estimate D·m(D) of the gap δ: the pre-test merge is hard thresholding of the gap.
// In units of V: θ = δ/√V, t = √(c/V), λ = 1 − k, Z ~ N(θ, 1):
//   always: θ²   never: (λZ − θ)² mean = λ² + k²θ²   pre-test: θ²·P(|Z| < t) + E[(λZ − θ)²; |Z| ≥ t].
// The two fixed rules tie at θ₀² = (1 − k)/(1 + k).
// Run: node studies/runs/pretest-merge.js
'use strict';

const phi = (x) => Math.exp(-x * x / 2) / Math.sqrt(2 * Math.PI);
// ∫_lo^hi f(z) φ(z − θ) dz by Simpson's rule
function integ(f, th, lo, hi, n = 4000) {
  const h = (hi - lo) / n;
  let s = 0;
  for (let i = 0; i <= n; i++) {
    const z = lo + i * h;
    const w = i === 0 || i === n ? 1 : i % 2 ? 4 : 2;
    s += w * f(z) * phi(z - th);
  }
  return (s * h) / 3;
}
const always = (th) => th * th;
const never = (th, k) => (1 - k) ** 2 + k * k * th * th;
function pretest(th, t, k) {
  const lam = 1 - k;
  const inside = integ(() => th * th, th, -t, t);
  const f = (z) => (lam * z - th) ** 2;
  const out = integ(f, th, th - 12, -t) + integ(f, th, t, th + 12);
  return inside + (t < th + 12 ? out : 0);
}

const ks = [0, 0.25, 0.5, 0.75];
const ts = [0.25, 0.5, 1, Math.SQRT2, 1.5, 2, 3];
const thetas = [];
for (let i = 0; i <= 120; i++) thetas.push(i * 0.05);

console.log('Excess of the pre-test rule over the better and the worse fixed rule (units of a²V).');
console.log('At θ₀ (the tie), over the grid θ ∈ [0, 6]: max over min(always, never), max over max(·,·),');
console.log('and the share of θ where it loses to both.\n');
console.log('  k     t     θ₀    excess@θ₀  maxRegret  maxOverWorse  θ@max  lossToBoth%');
for (const k of ks) {
  const th0 = Math.sqrt((1 - k) / (1 + k));
  for (const t of ts) {
    const e0 = pretest(th0, t, k) - always(th0);
    let mr = -Infinity, mw = -Infinity, at = 0, both = 0;
    for (const th of thetas) {
      const r = pretest(th, t, k), a = always(th), nv = never(th, k);
      mr = Math.max(mr, r - Math.min(a, nv));
      if (r - Math.max(a, nv) > mw) { mw = r - Math.max(a, nv); at = th; }
      if (r > Math.max(a, nv) + 1e-12) both++;
    }
    console.log(
      `${k.toFixed(2)}  ${t.toFixed(2)}  ${th0.toFixed(3)}  ${e0.toFixed(4).padStart(9)}  ` +
        `${mr.toFixed(4).padStart(9)}  ${mw.toFixed(4).padStart(12)}  ${at.toFixed(2).padStart(5)}  ` +
        `${((100 * both) / thetas.length).toFixed(0).padStart(6)}`,
    );
  }
}

// The plug-in threshold of notes/merging-cohorts.md §4: merge iff D² < V(V + 2τ²)/(V + τ²),
// i.e. t² = (1 + 2r)/(1 + r) with r = τ²/V, and the thesis separate rule k = 1/(1 + 2r).
console.log('\nPlug-in threshold t² = (1 + 2r)/(1 + r), separate rule k = 1/(1 + 2r), r = τ²/V:');
console.log('  r     k      t     excess@θ₀  maxOverWorse  θ@max');
for (const r of [0.1, 0.5, 1, 2, 5]) {
  const k = 1 / (1 + 2 * r), t = Math.sqrt((1 + 2 * r) / (1 + r));
  const th0 = Math.sqrt((1 - k) / (1 + k));
  const e0 = pretest(th0, t, k) - always(th0);
  let mw = -Infinity, at = 0;
  for (const th of thetas) {
    const v = pretest(th, t, k) - Math.max(always(th), never(th, k));
    if (v > mw) { mw = v; at = th; }
  }
  console.log(`${r.toFixed(1).padStart(4)}  ${k.toFixed(3)}  ${t.toFixed(3)}  ${e0.toFixed(4).padStart(9)}  ` +
    `${mw.toFixed(4).padStart(12)}  ${at.toFixed(2).padStart(5)}`);
}
