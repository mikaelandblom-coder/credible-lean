import Credibility.CoreMoments

/-!
# The collective mean given the levels: observed best prediction (extension, distribution-free)

`Core.blupWeight_optimal` averages the error over the levels: for interchangeable levels the
collective mean's weights `b ∝ z` are best. Here the levels are **fixed**. A cohort's estimate
`x̄ⱼ` has `E x̄ⱼ = θⱼ` and `Var x̄ⱼ = Dⱼ`, nothing else is assumed, and the blend
`zⱼx̄ⱼ + (1 − zⱼ)m` uses a fixed collective mean `m`. Then

* its error given the level is `zⱼ²Dⱼ + (1 − zⱼ)²(m − θⱼ)²`
  (`integral_sq_blend_given_level`), and `(1 − z)²(x̄ − m)² − 2(1 − z)D + D` is an unbiased
  estimate of it (`integral_sure_given_level`, Stein's unbiased risk estimate, SURE);
* over cohorts with volumes `uⱼ`, the `m` with the smallest total error is the
  `uⱼ(1 − zⱼ)²`-weighted mean of the levels (`condRisk_obpMean_le`), and the same weights applied
  to the `x̄ⱼ` minimise the observed criterion (`sure_obpMean_le`).

That plug-in is the collective mean of the observed best predictor (OBP; Jiang, Nguyen and Rao
2011; Zhang and Jiang 2025, literature §10p). So given the levels the weights are `∝ (1 − z)²`,
the small cohorts count most; averaged over interchangeable levels they are `∝ z`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core

section GivenLevel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A quadratic in the centred estimate: `E[a(x̄ − θ)² + b(x̄ − θ) + c] = aD + c`. -/
lemma integral_quad_centred {xbar : Ω → ℝ} {θ D : ℝ} (hx : MemLp xbar 2 P)
    (hmean : P[xbar] = θ) (hvar : Var[xbar; P] = D) (a b c : ℝ) :
    P[fun ω => a * (xbar ω - θ) ^ 2 + b * (xbar ω - θ) + c] = a * D + c := by
  have hc : MemLp (fun ω => xbar ω - θ) 2 P := hx.sub (memLp_const θ)
  have hci : Integrable (fun ω => xbar ω - θ) P := hc.integrable one_le_two
  have hsq : Integrable (fun ω => (xbar ω - θ) ^ 2) P := hc.integrable_sq
  have hV : P[fun ω => (xbar ω - θ) ^ 2] = D := by
    rw [← hvar, variance_eq_integral hx.aestronglyMeasurable.aemeasurable, hmean]
  have hE : P[fun ω => xbar ω - θ] = 0 := by
    rw [integral_sub (hx.integrable one_le_two) (integrable_const θ), hmean, integral_const]
    simp
  rw [integral_add (f := fun ω => a * (xbar ω - θ) ^ 2 + b * (xbar ω - θ)) (g := fun _ => c)
      ((hsq.const_mul a).add (hci.const_mul b)) (integrable_const c),
    integral_add (f := fun ω => a * (xbar ω - θ) ^ 2) (g := fun ω => b * (xbar ω - θ))
      (hsq.const_mul a) (hci.const_mul b), integral_const_mul, integral_const_mul,
    hV, hE, integral_const]
  simp

/-- **The blend's error given the level.** If `E x̄ = θ` and `Var x̄ = D`, the blend
`z x̄ + (1 − z)m` with a fixed collective mean `m` has
`E(z x̄ + (1 − z)m − θ)² = z²D + (1 − z)²(m − θ)²`. -/
theorem integral_sq_blend_given_level {xbar : Ω → ℝ} {θ D : ℝ} (hx : MemLp xbar 2 P)
    (hmean : P[xbar] = θ) (hvar : Var[xbar; P] = D) (z m : ℝ) :
    P[fun ω => (z * xbar ω + (1 - z) * m - θ) ^ 2] = z ^ 2 * D + (1 - z) ^ 2 * (m - θ) ^ 2 := by
  have h := integral_quad_centred hx hmean hvar (z ^ 2) (2 * z * ((1 - z) * (m - θ)))
    (((1 - z) * (m - θ)) ^ 2)
  convert h using 1
  · congr 1; funext ω; ring
  · ring

/-- **An unbiased estimate of that error** (SURE, fixed `m`): no distribution is needed,
because `m` is fixed. `E[(1 − z)²(x̄ − m)² − 2(1 − z)D + D] = z²D + (1 − z)²(m − θ)²`. -/
theorem integral_sure_given_level {xbar : Ω → ℝ} {θ D : ℝ} (hx : MemLp xbar 2 P)
    (hmean : P[xbar] = θ) (hvar : Var[xbar; P] = D) (z m : ℝ) :
    P[fun ω => (1 - z) ^ 2 * (xbar ω - m) ^ 2 - 2 * (1 - z) * D + D]
      = z ^ 2 * D + (1 - z) ^ 2 * (m - θ) ^ 2 := by
  have h := integral_quad_centred hx hmean hvar ((1 - z) ^ 2) (2 * (1 - z) ^ 2 * (θ - m))
    ((1 - z) ^ 2 * (θ - m) ^ 2 - 2 * (1 - z) * D + D)
  convert h using 1
  · congr 1; funext ω; ring
  · ring

end GivenLevel

section ObpMean

variable {J : Type*} [Fintype J]

/-- A weighted sum of squares about `m` is its value about the weighted mean plus
`(Σ w)(m − m*)²`. -/
lemma sum_mul_sq_sub_eq (w a : J → ℝ) (hw : ∑ j, w j ≠ 0) (m : ℝ) :
    ∑ j, w j * (m - a j) ^ 2
      = ∑ j, w j * ((∑ i, w i * a i) / ∑ i, w i - a j) ^ 2
        + (∑ j, w j) * (m - (∑ i, w i * a i) / ∑ i, w i) ^ 2 := by
  set S := ∑ j, w j
  set A := ∑ i, w i * a i
  have hSA : A / S * S = A := div_mul_cancel₀ A hw
  have key : ∀ j, w j * (m - a j) ^ 2 = w j * (A / S - a j) ^ 2
      + (w j * (m - A / S) ^ 2 + 2 * (m - A / S) * (A / S * w j - w j * a j)) := fun j => by
    ring
  rw [sum_congr rfl fun j _ => key j, sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum,
    sum_sub_distrib, ← mul_sum, hSA, sub_self, mul_zero, add_zero]

/-- The collective mean of the observed best predictor: the mean of `a` with weights
`uⱼ(1 − zⱼ)²`. -/
noncomputable def obpMean (u z a : J → ℝ) : ℝ :=
  (∑ j, u j * (1 - z j) ^ 2 * a j) / ∑ j, u j * (1 - z j) ^ 2

/-- **The best collective mean given the levels.** For volumes `uⱼ` with
`Σⱼ uⱼ(1 − zⱼ)² > 0`, the total error given the levels `θⱼ`,
`Σⱼ uⱼ(zⱼ²Dⱼ + (1 − zⱼ)²(m − θⱼ)²)`, is smallest at `m = obpMean u z θ`. -/
theorem condRisk_obpMean_le (u z D θ : J → ℝ) (hpos : 0 < ∑ j, u j * (1 - z j) ^ 2) (m : ℝ) :
    ∑ j, u j * (z j ^ 2 * D j + (1 - z j) ^ 2 * (obpMean u z θ - θ j) ^ 2)
      ≤ ∑ j, u j * (z j ^ 2 * D j + (1 - z j) ^ 2 * (m - θ j) ^ 2) := by
  have h := sum_mul_sq_sub_eq (fun j => u j * (1 - z j) ^ 2) θ hpos.ne' m
  have e : ∀ c : ℝ, ∑ j, u j * (z j ^ 2 * D j + (1 - z j) ^ 2 * (c - θ j) ^ 2)
      = ∑ j, u j * z j ^ 2 * D j + ∑ j, u j * (1 - z j) ^ 2 * (c - θ j) ^ 2 := fun c => by
    rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hn := mul_nonneg hpos.le (sq_nonneg (m - obpMean u z θ))
  rw [e, e, h]
  unfold obpMean at hn ⊢
  linarith

/-- **The observed best predictor's collective mean.** The same weights applied to the observed
`x̄ⱼ` (here `a`) minimise the observed criterion
`Σⱼ uⱼ((1 − zⱼ)²(x̄ⱼ − m)² − 2(1 − zⱼ)Dⱼ + Dⱼ)`, the unbiased estimate of the total error
(`integral_sure_given_level`). -/
theorem sure_obpMean_le (u z D a : J → ℝ) (hpos : 0 < ∑ j, u j * (1 - z j) ^ 2) (m : ℝ) :
    ∑ j, u j * ((1 - z j) ^ 2 * (a j - obpMean u z a) ^ 2 - 2 * (1 - z j) * D j + D j)
      ≤ ∑ j, u j * ((1 - z j) ^ 2 * (a j - m) ^ 2 - 2 * (1 - z j) * D j + D j) := by
  have h := sum_mul_sq_sub_eq (fun j => u j * (1 - z j) ^ 2) a hpos.ne' m
  have e : ∀ c : ℝ, ∑ j, u j * ((1 - z j) ^ 2 * (a j - c) ^ 2 - 2 * (1 - z j) * D j + D j)
      = ∑ j, u j * (D j - 2 * (1 - z j) * D j) + ∑ j, u j * (1 - z j) ^ 2 * (c - a j) ^ 2 :=
    fun c => by rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hn := mul_nonneg hpos.le (sq_nonneg (m - obpMean u z a))
  rw [e, e, h]
  unfold obpMean at hn ⊢
  linarith

end ObpMean

end Core
end Credibility
