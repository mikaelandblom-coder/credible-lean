import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Merging two cohorts: Result A of `notes/merging-cohorts.md` (Case A)

Not in the thesis: an extension answering FINDINGS item 6. Two cohorts on their
own (the §2.7 setting, `μ` estimated from the pair). Notation of the note:

* `v₁ = σ₁²`, `v₂ = σ₂²` are the error variances of the cohort estimates and
  `c = σ₁₂²ρ₁₂` their covariance (`c = σ₁σ₂ρ` in §2.7);
* `V = v₁ + v₂ - 2c = Var(μ̂₁ - μ̂₂)`;
* `d = E(μ₁ - μ₂)²` is the true gap between the levels.

An unbiased linear predictor of `μ₁` is `μ̃₁ = X₁ - β(X₁ - X₂)`, with MSE
`v₁ - 2β(v₁ - c) + β²(V + d)` (likewise for cohort 2 with `v₂`). As elsewhere,
second moments are given numbers: this MSE formula is the definition `mse`.

A working model with gap variance `x` uses the weight `β(x) = (vⱼ - c)/(V + x)`;
the separate (thesis) rule has `x = 2τ²`, the merged rule `x = 0`.
-/

namespace Credibility.Merging

/-- `V = v₁ + v₂ - 2c`, the variance of the observed difference `μ̂₁ - μ̂₂`. -/
def V (v1 v2 c : ℝ) : ℝ := v1 + v2 - 2 * c

/-- MSE of `μ̃ = X - β(X - X')` for a cohort with error variance `v`, when the
true level gap is `d` (with `V` the variance of the observed gap). -/
def mse (v c V d β : ℝ) : ℝ := v - 2 * β * (v - c) + β ^ 2 * (V + d)

/-- The weight on the other cohort under a working gap variance `x`:
`β(x) = (v - c)/(V + x)`. With `x = d` it is the best weight `β*`. -/
noncomputable def weight (v c V x : ℝ) : ℝ := (v - c) / (V + x)

/-- `Q = (v₁ - c)² + (v₂ - c)²`. -/
def Q (v1 v2 c : ℝ) : ℝ := (v1 - c) ^ 2 + (v2 - c) ^ 2

/-- Excess total MSE `ΔL(d_w)` over both cohorts of the rule built with working
gap variance `d_w`, against the best rule, when the true gap is `d`. -/
noncomputable def excessLoss (v1 v2 c d dw : ℝ) : ℝ :=
  (mse v1 c (V v1 v2 c) d (weight v1 c (V v1 v2 c) dw)
      - mse v1 c (V v1 v2 c) d (weight v1 c (V v1 v2 c) d))
    + (mse v2 c (V v1 v2 c) d (weight v2 c (V v1 v2 c) dw)
      - mse v2 c (V v1 v2 c) d (weight v2 c (V v1 v2 c) d))

/-- Excess-loss identity for one cohort (fact 1 of the note):
`MSE(β) = MSE(β*) + (V + d)(β - β*)²`, with `β* = (v - c)/(V + d)`. -/
theorem mse_eq {v c V d : ℝ} (hVd : V + d ≠ 0) (β : ℝ) :
    mse v c V d β = mse v c V d (weight v c V d) + (V + d) * (β - weight v c V d) ^ 2 := by
  -- Complete the square: β²(V+d) - 2β(v-c) = (V+d)(β - β*)² - (v-c)²/(V+d).
  rw [mse, mse, weight]
  field_simp
  ring

/-- The note's closed form: `ΔL(d_w) = Q (V + d) (1/(V + d_w) - 1/(V + d))²`. -/
theorem excessLoss_eq {v1 v2 c d dw : ℝ} (hd : V v1 v2 c + d ≠ 0)
    (hdw : V v1 v2 c + dw ≠ 0) :
    excessLoss v1 v2 c d dw
      = Q v1 v2 c * (V v1 v2 c + d) * (1 / (V v1 v2 c + dw) - 1 / (V v1 v2 c + d)) ^ 2 := by
  -- Each cohort contributes (V+d)(β(d_w) - β*)² by `mse_eq`, and
  -- β(d_w) - β* = (vⱼ - c)(1/(V+d_w) - 1/(V+d)).
  rw [excessLoss, mse_eq hd (weight v1 _ _ dw), mse_eq hd (weight v2 _ _ dw), Q, weight,
    weight, weight, weight]
  field_simp
  ring

/-- **Result A (midpoint rule).** Merging (`d_w = 0`) beats keeping the cohorts
separate (`d_w = 2τ²`) iff `d (V + τ²) < V τ²`, i.e. `d < Vτ²/(V + τ²)`. -/
theorem merge_iff {v1 v2 c τ2 d : ℝ} (hτ : 0 < τ2) (hV : 0 < V v1 v2 c)
    (hQ : 0 < Q v1 v2 c) (hd : 0 ≤ d) :
    excessLoss v1 v2 c d 0 < excessLoss v1 v2 c d (2 * τ2)
      ↔ d * (V v1 v2 c + τ2) < V v1 v2 c * τ2 := by
  -- ΔL(x) ∝ (1/(V+x) - t)² with t = 1/(V+d). For a = 1/V > b = 1/(V+2τ²),
  -- (a - t)² < (b - t)² ⟺ t > (a + b)/2 ⟺ d(V + τ²) < Vτ².
  have hd' : 0 < V v1 v2 c + d := by linarith
  have h2 : 0 < V v1 v2 c + 2 * τ2 := by linarith
  rw [excessLoss_eq hd'.ne' (by simpa using hV.ne'), excessLoss_eq hd'.ne' h2.ne',
    mul_lt_mul_iff_of_pos_left (mul_pos hQ hd'), add_zero, ← sub_pos, ← sub_pos (a := _ * τ2)]
  have key : (1 / (V v1 v2 c + 2 * τ2) - 1 / (V v1 v2 c + d)) ^ 2
      - (1 / V v1 v2 c - 1 / (V v1 v2 c + d)) ^ 2
      = 4 * τ2 * (V v1 v2 c * τ2 - d * (V v1 v2 c + τ2))
        / (V v1 v2 c ^ 2 * (V v1 v2 c + 2 * τ2) ^ 2 * (V v1 v2 c + d)) := by
    field_simp
    ring
  have hden : 0 < V v1 v2 c ^ 2 * (V v1 v2 c + 2 * τ2) ^ 2 * (V v1 v2 c + d) := by positivity
  rw [key, div_pos_iff_of_pos_right hden]
  exact mul_pos_iff_of_pos_left (by positivity)

end Credibility.Merging
