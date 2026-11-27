import Credibility.Merging
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-!
# Merging two cohorts when the gap looks small: the exact winner's curse under normal noise

**Optional distribution layer** (owner, 2026-11-15): this file assumes *normal noise*, so nothing
in the core depends on it.

Two cohorts with fixed levels `μ₁`, `μ₂`, gap `δ = μ₁ - μ₂`, estimates `Xⱼ = μⱼ + eⱼ`, as in
`Merging.lean`: `V = Var(X₁ - X₂)`, and the predictor `X₁ - β(X₁ - X₂)` of `μ₁`. Merging uses
the weight `a = (v₁ - c₁₂)/V` (`Merging.weight` at gap `0`), keeping the cohorts separate the
weight `a·k` (the thesis blend: `k = V/(V + 2τ²)`; the cohort's own estimate: `k = 0`). The
**pre-test rule** merges iff the observed gap looks small, `(X₁ - X₂)² < c`, and so decides with
the same data it then blends (notes/merging-cohorts.md §4, "Winner's curse").

**Reduction** (`integral_sq_pretest`). Write `D = X₁ - X₂` (law `N(δ, V)`) and
`e₁ = u + a(D - δ)` (the regression of `e₁` on `D`; under normal noise `u` is independent of `D`).
Then the error of every such rule is `u + a·G(D)` with `G(x) = -δ` when merged and
`G(x) = (1 - k)x - δ` when kept separate, and

`E(error)² = E u² + a² R`,  `R = E G(D)²` (`gapRisk`):

predicting `μ₁` is estimating the gap `δ`, and the pre-test merge is **hard thresholding** of the
observed gap (with shrinkage `1 - k` above the threshold). The same holds for cohort 2 with
`a₂ = (v₂ - c₁₂)/V`, so the comparison of rules is the comparison of `R`, cohort by cohort.
Always merging has `R = δ²` (`gapRisk_merge`), never merging `R = m²V + (1 - m)²δ²` with
`m = 1 - k` (`gapRisk_never`); they tie at `δ²(2 - m) = mV`.

**Finding 43** (`lt_gapRisk_of_tie`). At that tie, the pre-test rule is strictly worse than both,
for every threshold `c > 0`: no threshold makes "merge iff the gap looks small" never lose to both
fixed rules (Judge & Bock's pre-test estimator; hard thresholding). Numerically
(`studies/runs/pretest-merge.js`): with own estimates (`k = 0`), `c = 2V` it loses by `0.20·a²V`,
a fifth of the separate rule's whole excess; it loses to both on 5–14% of the gaps.

Proof idea of the Finding (not yet in Lean): with `p(x) = δ² - (mx - δ)² = mx(2δ - mx)`,
`R - δ² = -E[p(D); D² ≥ c]`, and `E p(D) = 0` at the tie. Folding `x ↦ -x`, the integrand on
`x > 0` is `m x φ(x - δ)·h(x)` with `h(x)e^{δx/V} = 2cosh(δx/V)(2δ tanh(δx/V) - mx)` (for
`V = 1`), which is positive then negative (concavity of `tanh`, slope `2δ² - m > 0` at `0`).
So `∫_{√c}^∞` of it is negative when `√c` lies past the sign change, and `∫_0^{√c}` of it is
positive (and equals minus the tail) otherwise.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Credibility
namespace PreTest

/-- The pre-test weight on the other cohort: `a` (merge) when the observed gap looks small,
`x² < c`, and `a·k` (keep separate) otherwise. -/
noncomputable def weight (a k c x : ℝ) : ℝ := if x ^ 2 < c then a else a * k

/-- The pre-test weight switches between the two rules of `Merging.lean`: with
`a = (v - c₁₂)/V` and `k = V/(V + x)` it is `Merging.weight` at gap `0` (merge) when the gap looks
small and at the working gap `x` (separate, `x = 2τ²` for the thesis rule) otherwise. -/
theorem weight_eq_merging {v c₁₂ V x : ℝ} (hV : V ≠ 0) (hVx : V + x ≠ 0) (c D : ℝ) :
    weight ((v - c₁₂) / V) (V / (V + x)) c D
      = if D ^ 2 < c then Merging.weight v c₁₂ V 0 else Merging.weight v c₁₂ V x := by
  rw [Merging.weight_eq (by simpa using hV), Merging.weight_eq hVx, weight, add_zero]
  congr 1
  field_simp

/-- The rule's error in units of `a`, as an estimate of the gap: `G(x) = -δ` when merged and
`G(x) = m x - δ` (`m = 1 - k`) when kept separate. -/
noncomputable def gapErr (m δ c x : ℝ) : ℝ := if x ^ 2 < c then -δ else m * x - δ

/-- The risk `R = E G(D)²` of the gap estimate, `D ~ N(δ, V)`. -/
noncomputable def gapRisk (m δ c : ℝ) (V : ℝ≥0) : ℝ := ∫ x, gapErr m δ c x ^ 2 ∂gaussianReal δ V

lemma measurable_gapErr (m δ c : ℝ) : Measurable (gapErr m δ c) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const (by fun_prop)

lemma memLp_gapErr (m δ c : ℝ) (V : ℝ≥0) : MemLp (gapErr m δ c) 2 (gaussianReal δ V) := by
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal δ V) := memLp_id_gaussianReal 2
  have hg : MemLp (fun x : ℝ => |m * x - δ| + |δ|) 2 (gaussianReal δ V) :=
    ((hid.const_mul m).sub (memLp_const δ)).abs.add (memLp_const _)
  refine hg.of_le (measurable_gapErr m δ c).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  simp only [gapErr, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |m * x - δ| + |δ|)]
  split_ifs
  · rw [abs_neg]; linarith [abs_nonneg (m * x - δ)]
  · linarith [abs_nonneg δ]

/-- The pre-test rule's error is `u + a·G(D)`. -/
lemma err_eq (u a k c δ D : ℝ) :
    u + a * (D - δ) - weight a k c D * D = u + a * gapErr (1 - k) δ c D := by
  simp only [weight, gapErr]
  split_ifs <;> ring

/-- **The reduction**: if `D = X₁ - X₂` has law `N(δ, V)` and the residual `u = e₁ - a(D - δ)`
(mean `0`) is independent of `D` (as under normal noise), the pre-test rule's MSE is

`E(u + a(D - δ) - β̂(D)·D)² = E u² + a²·R(1 - k, δ, c, V)`. -/
theorem integral_sq_pretest {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u D : Ω → ℝ} {δ : ℝ} {V : ℝ≥0} (hu : MemLp u 2 P)
    (hu0 : P[u] = 0) (hD : HasLaw D (gaussianReal δ V) P) (hind : IndepFun u D P) (a k c : ℝ) :
    P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2]
      = P[fun ω => u ω ^ 2] + a ^ 2 * gapRisk (1 - k) δ c V := by
  set G := gapErr (1 - k) δ c
  have hG : MemLp (fun ω => G (D ω)) 2 P := hD.memLp_comp (memLp_gapErr (1 - k) δ c V)
  have hpt : ∀ ω, (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2
      = u ω ^ 2 + 2 * a * (u ω * G (D ω)) + a ^ 2 * G (D ω) ^ 2 := fun ω => by
    rw [err_eq]; ring
  simp_rw [hpt]
  have i1 := hu.integrable_sq
  have i2 := (hu.integrable_mul hG).const_mul (2 * a)
  have i3 := hG.integrable_sq.const_mul (a ^ 2)
  have e1 := integral_add (i1.add i2) i3
  have e2 := integral_add i1 i2
  simp only [Pi.add_apply, Pi.mul_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul]
  have hcross : P[fun ω => u ω * G (D ω)] = 0 := by
    have hi : IndepFun u (fun ω => G (D ω)) P :=
      hind.comp measurable_id (measurable_gapErr (1 - k) δ c)
    have := hi.integral_mul_eq_mul_integral hu.aestronglyMeasurable hG.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hu0, zero_mul]
  have hsq : P[fun ω => G (D ω) ^ 2] = gapRisk (1 - k) δ c V :=
    hD.integral_comp (f := fun x => G x ^ 2)
      ((measurable_gapErr (1 - k) δ c).pow_const 2).aestronglyMeasurable
  rw [hcross, hsq]
  ring

/-- **Always merging** (`m = 0`, i.e. `k = 1`): `R = δ²`. -/
theorem gapRisk_merge (δ c : ℝ) (V : ℝ≥0) : gapRisk 0 δ c V = δ ^ 2 := by
  have : ∀ x, gapErr 0 δ c x ^ 2 = δ ^ 2 := fun x => by
    simp only [gapErr]; split_ifs <;> ring
  simp [gapRisk, this]

/-- **Never merging** (`c ≤ 0`): `R = m²V + (1 - m)²δ²`. -/
theorem gapRisk_never (m δ : ℝ) {c : ℝ} (hc : c ≤ 0) (V : ℝ≥0) :
    gapRisk m δ c V = m ^ 2 * V + (1 - m) ^ 2 * δ ^ 2 := by
  have hpt : ∀ x, gapErr m δ c x ^ 2
      = m ^ 2 * (x - δ) ^ 2 + (2 * m * (m - 1) * δ) * (x - δ) + (m - 1) ^ 2 * δ ^ 2 := fun x => by
    have : ¬ x ^ 2 < c := not_lt.2 (le_trans hc (sq_nonneg x))
    simp only [gapErr, this, ite_false]; ring
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal δ V) := memLp_id_gaussianReal 2
  have hc' : MemLp (fun x : ℝ => x - δ) 2 (gaussianReal δ V) := hid.sub (memLp_const δ)
  have i1 := hc'.integrable_sq.const_mul (m ^ 2)
  have i2 := (hc'.integrable one_le_two).const_mul (2 * m * (m - 1) * δ)
  have hvar : ∫ x, (x - δ) ^ 2 ∂gaussianReal δ V = V := by
    have h := variance_fun_id_gaussianReal (μ := δ) (v := V)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    exact h
  have hmean : ∫ x, (x - δ) ∂gaussianReal δ V = 0 := by
    rw [integral_sub (hid.integrable one_le_two) (integrable_const _), integral_id_gaussianReal]
    simp
  simp only [gapRisk, hpt]
  have e1 := integral_add (i1.add i2) (integrable_const ((m - 1) ^ 2 * δ ^ 2))
  have e2 := integral_add i1 i2
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, hvar, hmean]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- **Finding 43: the pre-test merge loses to both fixed rules.** At the gap where always and
never merging tie (`δ²(2 - m) = mV`, `0 < m < 2`), the pre-test rule's risk exceeds their common
risk `δ²` for every threshold `c > 0`, under normal noise. -/
theorem lt_gapRisk_of_tie {m δ c : ℝ} {V : ℝ≥0} (hm : 0 < m) (hm2 : m < 2) (hδ : 0 < δ)
    (htie : δ ^ 2 * (2 - m) = m * V) (hc : 0 < c) : δ ^ 2 < gapRisk m δ c V := by
  sorry

/-- **Finding 43 for the predictor**: under the hypotheses of `integral_sq_pretest`, with
`a ≠ 0`, `0 < 1 - k < 2` and the gap at the tie, the pre-test rule's MSE exceeds both that of
always merging (`k = 1`) and that of never merging (`c = 0`), for every threshold `c > 0`. -/
theorem pretest_mse_gt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u D : Ω → ℝ} {δ : ℝ} {V : ℝ≥0} (hu : MemLp u 2 P)
    (hu0 : P[u] = 0) (hD : HasLaw D (gaussianReal δ V) P) (hind : IndepFun u D P)
    {a k c : ℝ} (ha : a ≠ 0) (hk : 0 < 1 - k) (hk2 : 1 - k < 2) (hδ : 0 < δ)
    (htie : δ ^ 2 * (2 - (1 - k)) = (1 - k) * V) (hc : 0 < c) :
    P[fun ω => (u ω + a * (D ω - δ) - weight a 1 c (D ω) * D ω) ^ 2]
        < P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2] ∧
      P[fun ω => (u ω + a * (D ω - δ) - weight a k 0 (D ω) * D ω) ^ 2]
        < P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2] := by
  -- Counted as proved only once `lt_gapRisk_of_tie` is (CheckAxioms). Proof, checked with it:
  -- have hlt := lt_gapRisk_of_tie hk hk2 hδ htie hc
  -- have ha2 : 0 < a ^ 2 := by positivity
  -- rw [integral_sq_pretest hu hu0 hD hind, integral_sq_pretest hu hu0 hD hind,
  --   integral_sq_pretest hu hu0 hD hind, sub_self, gapRisk_merge,
  --   gapRisk_never _ _ le_rfl]
  -- have hnev : (1 - k) ^ 2 * (V : ℝ) + (1 - (1 - k)) ^ 2 * δ ^ 2 = δ ^ 2 := by
  --   have : (1 - k) * (V : ℝ) = δ ^ 2 * (2 - (1 - k)) := htie.symm
  --   nlinarith [this]
  -- rw [hnev]
  -- exact ⟨by nlinarith, by nlinarith⟩
  sorry

end PreTest
end Credibility
