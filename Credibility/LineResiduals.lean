import Credibility.Expectation

/-!
# Residuals of per-cohort regression lines (extension, distribution-free)

Each cohort `j` fits its own line (any `p` coefficients: level and slope, or more) to its
cells `Xⱼₜ` by weighted least squares with volumes `wⱼₜ`. The data have fixed-effect means
`Uⱼβⱼ` (`blockDesign`) and the noise of S67: `cov(Xⱼₜ, Xᵢₛ) = δₜₛσ²cᵢⱼ/√(wⱼₜwᵢₜ)`, `cⱼⱼ = 1`,
`cᵢⱼ = ρ` (`lineCov`; the thesis's `δₜₛ` correlation). With the whitened design
`Vⱼ = Wⱼ^{1/2}Uⱼ` and hat matrix `Pⱼ = Vⱼ(VⱼᵀVⱼ)⁻¹Vⱼᵀ` (`hat`), the whitened residuals are
`ẽⱼ = (I - Pⱼ)Wⱼ^{1/2}Xⱼ` (`resid`).

Each residual is a linear form annihilating its cohort's design, so a product of two has an
expectation free of the coefficients (`unbiasedMean_sum_mul`, from `Model.unbiasedMean_mul`):
`E Σₜ ẽᵢₜẽⱼₜ = σ²cᵢⱼ tr((I - Pᵢ)(I - Pⱼ))` (`unbiasedMean_resid_mul`), and
`tr((I - Pᵢ)(I - Pⱼ)) = T - 2p + tr(PᵢPⱼ)` (`trace_one_sub_hat_mul`). Hence the residual
variance `Σₜ ẽⱼₜ²/(T - p)` is unbiased for `σ²` (`unbiasedMean_s2`), and the cross product over
`tr((I - Pᵢ)(I - Pⱼ))` for `σ²ρ` (`unbiasedMean_cross`: Zellner's SUR estimator). With one
design and equal exposure shapes `wⱼₜ = aⱼgₜ` all hat matrices agree (`hat_eq_of_shape`), so
S67's divisor `T - p` is the right one (`unbiasedMean_cross_of_shape`). Otherwise `tr(PᵢPⱼ)`
can fall below `p` (levels only with non-proportional volumes, by Cauchy–Schwarz), and that
divisor then biases `ρ̂` towards `0`. With `p = 1` (levels only) this is
the thesis's pair estimator (handbook `res:pooled`).

`UnbiasedMean.integral_eq` turns each statement into one about actual random variables with
these moments.
-/

open Finset Matrix

namespace Credibility.LineResiduals
open Credibility.Model

variable {J T B : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] [Fintype B]
  [DecidableEq B]

/-- The block design of per-cohort regressions: cell `(j, t)` has the row `Uⱼ t` on cohort
`j`'s own coefficients `(j, ·)`, so the mean of cell `(j, t)` is `Σ_b Uⱼ t b βⱼ_b`. -/
def blockDesign (U : J → Matrix T B ℝ) : Matrix (J × T) (J × B) ℝ :=
  fun p q => if q.1 = p.1 then U p.1 p.2 q.2 else 0

/-- A linear form of cohort `j`'s cells, `Σₛ aₛ X₍ⱼ,ₛ₎`. -/
def cohortForm (j : J) (a : T → ℝ) : J × T → ℝ := fun p => if p.1 = j then a p.2 else 0

omit [DecidableEq T] in
lemma cohortForm_sum (j : J) (a : T → ℝ) (X : J × T → ℝ) :
    ∑ p, cohortForm j a p * X p = ∑ s, a s * X (j, s) := by
  simp [cohortForm, Fintype.sum_prod_type, ite_mul]

omit [DecidableEq T] [Fintype B] [DecidableEq B] in
lemma blockDesign_transpose_cohortForm (U : J → Matrix T B ℝ) (j : J) (a : T → ℝ)
    (ha : (U j)ᵀ *ᵥ a = 0) : (blockDesign U)ᵀ *ᵥ cohortForm j a = 0 := by
  funext q
  have := congrFun ha q.2
  simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply] at this ⊢
  simp only [blockDesign, cohortForm, Fintype.sum_prod_type]
  by_cases h : q.1 = j
  · subst h; simp [mul_comm, this]
  · simp [ite_mul, h]

omit [DecidableEq T] [DecidableEq B] in
/-- **Residual products under per-cohort regressions**: if the rows `ℓᵢₜ`, `mⱼₜ` of linear
forms of cohorts `i` and `j` annihilate those cohorts' designs, `Σₜ (ℓᵢₜ·Xᵢ)(mⱼₜ·Xⱼ)` is
unbiased, whatever the coefficients, for `Σₜ Σₛ Σₛ' ℓᵢₜₛ mⱼₜₛ' C₍ᵢ,ₛ₎₍ⱼ,ₛ'₎`. -/
theorem unbiasedMean_sum_mul (C : J × T → J × T → ℝ) (U : J → Matrix T B ℝ) (i j : J)
    (ℓ m : T → T → ℝ) (hℓ : ∀ t, (U i)ᵀ *ᵥ ℓ t = 0) :
    UnbiasedMean C (blockDesign U)
      (fun X => ∑ t, (∑ s, ℓ t s * X (i, s)) * (∑ s, m t s * X (j, s)))
      (∑ t, ∑ s, ∑ s', ℓ t s * m t s' * C (i, s) (j, s')) := by
  refine (UnbiasedMean.sum univ fun t _ =>
    unbiasedMean_mul C (blockDesign U) (cohortForm i (ℓ t)) (cohortForm j (m t))
      (blockDesign_transpose_cohortForm U i _ (hℓ t))).congr (fun X => ?_) ?_
  · simp only [cohortForm_sum]
  · refine sum_congr rfl fun t _ => ?_
    simp [cohortForm, Fintype.sum_prod_type, ite_mul, mul_ite]

/-! ### Weighted least squares per cohort -/

variable (w : J → T → ℝ) (U : J → Matrix T B ℝ)

/-- The whitened design `Vⱼ = Wⱼ^{1/2} Uⱼ`. -/
noncomputable def white (j : J) : Matrix T B ℝ := diagonal (fun t => √(w j t)) * U j

/-- The hat matrix of cohort `j`'s whitened fit, `Pⱼ = Vⱼ(VⱼᵀVⱼ)⁻¹Vⱼᵀ`. -/
noncomputable def hat (j : J) : Matrix T T ℝ :=
  white w U j * ((white w U j)ᵀ * white w U j)⁻¹ * (white w U j)ᵀ

/-- The whitened residual of cohort `j` in period `t`, `ẽⱼₜ = ((I - Pⱼ)Wⱼ^{1/2}Xⱼ)ₜ`: the
weighted least-squares residual times `√wⱼₜ`. -/
noncomputable def resid (X : J × T → ℝ) (j : J) (t : T) : ℝ :=
  ∑ s, ((1 : Matrix T T ℝ) - hat w U j) t s * √(w j s) * X (j, s)

/-- Cell noise of one period correlated across cohorts: `cov(Xⱼₜ, Xᵢₛ) = δₜₛ σ² cᵢⱼ/√(wⱼₜwᵢₜ)`
with `cⱼⱼ = 1`, `cᵢⱼ = ρ` otherwise (the thesis's `δₜₛ` correlation; S67's world). -/
noncomputable def lineCov (σ2 ρ : ℝ) : J × T → J × T → ℝ := fun p q =>
  if p.2 = q.2 then σ2 * (if p.1 = q.1 then 1 else ρ) / (√(w p.1 p.2) * √(w q.1 q.2)) else 0

variable {w U}

omit [Fintype J] [DecidableEq J] in
lemma hat_mul_white {j : J} (h : IsUnit ((white w U j)ᵀ * white w U j).det) :
    hat w U j * white w U j = white w U j := by
  rw [hat, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]

omit [Fintype J] [DecidableEq J] in
lemma hat_transpose (j : J) : (hat w U j)ᵀ = hat w U j := by
  rw [hat, transpose_mul, transpose_mul, transpose_transpose, transpose_nonsing_inv,
    transpose_mul, transpose_transpose, Matrix.mul_assoc]

omit [Fintype J] [DecidableEq J] in
lemma trace_hat {j : J} (h : IsUnit ((white w U j)ᵀ * white w U j).det) :
    trace (hat w U j) = Fintype.card B := by
  rw [hat, trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ h, trace_one]

omit [Fintype J] [DecidableEq J] in
lemma hat_mul_hat {j : J} (h : IsUnit ((white w U j)ᵀ * white w U j).det) :
    hat w U j * hat w U j = hat w U j := by
  have e : hat w U j * hat w U j = white w U j * (((white w U j)ᵀ * white w U j)⁻¹
      * ((white w U j)ᵀ * white w U j) * ((white w U j)ᵀ * white w U j)⁻¹) * (white w U j)ᵀ := by
    simp only [hat, Matrix.mul_assoc]
  rw [e, nonsing_inv_mul _ h, Matrix.one_mul, hat, Matrix.mul_assoc]

omit [Fintype J] [DecidableEq J] in
lemma one_sub_hat_mul_white {j : J} (h : IsUnit ((white w U j)ᵀ * white w U j).det) :
    ((1 : Matrix T T ℝ) - hat w U j) * white w U j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hat_mul_white h, sub_self]

/-- **Expected whitened residual products** of two cohorts' weighted least-squares lines:
`E Σₜ ẽᵢₜẽⱼₜ = σ²cᵢⱼ tr((I - Pᵢ)(I - Pⱼ))`, `cⱼⱼ = 1`, `cᵢⱼ = ρ`, whatever the lines'
coefficients. -/
theorem unbiasedMean_resid_mul (σ2 ρ : ℝ) (hw : ∀ j t, 0 < w j t)
    (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (i j : J) :
    UnbiasedMean (lineCov w σ2 ρ) (blockDesign U)
      (fun X => ∑ t, resid w U X i t * resid w U X j t)
      (σ2 * (if i = j then 1 else ρ)
        * trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j))) := by
  refine (unbiasedMean_sum_mul (lineCov w σ2 ρ) U i j
    (fun t s => ((1 : Matrix T T ℝ) - hat w U i) t s * √(w i s))
    (fun t s => ((1 : Matrix T T ℝ) - hat w U j) t s * √(w j s)) fun t => ?_).congr
    (fun X => rfl) ?_
  · funext b
    have := congrFun (congrFun (one_sub_hat_mul_white (h i)) t) b
    simp only [Matrix.mul_apply, white, diagonal_apply, ite_mul, zero_mul, sum_ite_eq,
      mem_univ, ite_true, Matrix.zero_apply] at this
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply]
    rw [← this]
    exact sum_congr rfl fun s _ => by ring
  · have hs : ∀ k t, √(w k t) ≠ 0 := fun k t => (Real.sqrt_pos.2 (hw k t)).ne'
    have hP : ∀ s t, ((1 : Matrix T T ℝ) - hat w U j) s t = ((1 : Matrix T T ℝ) - hat w U j) t s :=
      fun s t => by
        rw [← transpose_apply ((1 : Matrix T T ℝ) - hat w U j) t s, transpose_sub,
          transpose_one, hat_transpose]
    simp only [lineCov, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, trace,
      Matrix.diag_apply, Matrix.mul_apply, mul_sum]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    rw [hP s t]
    have h1 := hs i s
    have h2 := hs j s
    generalize (if i = j then σ2 * 1 else σ2 * ρ) = c
    field_simp

omit [Fintype J] [DecidableEq J] in
/-- `tr((I - Pᵢ)(I - Pⱼ)) = T - 2p + tr(PᵢPⱼ)`, `p` the number of coefficients per line. -/
lemma trace_one_sub_hat_mul (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (i j : J) :
    trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j))
      = Fintype.card T - 2 * Fintype.card B + trace (hat w U i * hat w U j) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, trace_sub,
    trace_one, trace_hat (h i), trace_hat (h j)]
  ring

omit [DecidableEq T] in
lemma hatOf_smul {V : Matrix T B ℝ} {c : ℝ} (hc : c ≠ 0) (h : IsUnit ((c • V)ᵀ * (c • V)).det) :
    (c • V) * ((c • V)ᵀ * (c • V))⁻¹ * (c • V)ᵀ = V * (Vᵀ * V)⁻¹ * Vᵀ := by
  have hG : (c • V)ᵀ * (c • V) = (c * c) • (Vᵀ * V) := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcc : c * c ≠ 0 := mul_ne_zero hc hc
  have hV : IsUnit (Vᵀ * V).det := by
    rw [hG, det_smul] at h
    exact isUnit_of_mul_isUnit_right h
  have hinv : ((c * c) • (Vᵀ * V))⁻¹ = (c * c)⁻¹ • (Vᵀ * V)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, nonsing_inv_mul _ hV, smul_smul, inv_mul_cancel₀ hcc,
      one_smul]
  rw [hG, hinv]
  simp only [transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [show c * ((c * c)⁻¹ * c) = 1 by field_simp, one_smul]

omit [Fintype J] [DecidableEq J] in
/-- **Equal exposure shapes give equal hat matrices**: with one design `U₀` for all cohorts and
volumes `wⱼₜ = aⱼgₜ` (`aⱼ > 0`), every cohort's whitened fit has the same hat matrix. -/
theorem hat_eq_of_shape {U₀ : Matrix T B ℝ} {a : J → ℝ} {g : T → ℝ} (hU : ∀ j, U j = U₀)
    (hwg : ∀ j t, w j t = a j * g t) (ha : ∀ j, 0 < a j)
    (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (i j : J) :
    hat w U i = hat w U j := by
  have hV : ∀ k, white w U k = √(a k) • (diagonal (fun t => √(g t)) * U₀) := fun k => by
    ext t b
    simp only [white, hU k, Matrix.smul_apply, diagonal_mul, smul_eq_mul, hwg,
      Real.sqrt_mul (ha k).le]
    ring
  have hk : ∀ k, hat w U k = (diagonal (fun t => √(g t)) * U₀)
      * ((diagonal (fun t => √(g t)) * U₀)ᵀ * (diagonal (fun t => √(g t)) * U₀))⁻¹
      * (diagonal (fun t => √(g t)) * U₀)ᵀ := fun k => by
    have := h k
    rw [hV k] at this
    rw [hat, hV k]
    exact hatOf_smul (Real.sqrt_pos.2 (ha k)).ne' this
  rw [hk i, hk j]

omit [Fintype J] [DecidableEq J] in
/-- With equal hat matrices `tr((I - Pᵢ)(I - Pⱼ)) = T - p`. -/
lemma trace_one_sub_hat_mul_of_eq (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det)
    {i j : J} (hij : hat w U i = hat w U j) :
    trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j))
      = Fintype.card T - Fintype.card B := by
  rw [trace_one_sub_hat_mul h, hij, hat_mul_hat (h j), trace_hat (h j)]
  ring

/-- **The residual variance is unbiased** for any volumes: `Σₜ ẽⱼₜ² / (T - p)` has
expectation `σ²` (`p < T` coefficients per line). -/
theorem unbiasedMean_s2 (σ2 ρ : ℝ) (hw : ∀ j t, 0 < w j t)
    (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (hT : Fintype.card B < Fintype.card T)
    (j : J) :
    UnbiasedMean (lineCov w σ2 ρ) (blockDesign U)
      (fun X => (Fintype.card T - Fintype.card B : ℝ)⁻¹ * ∑ t, resid w U X j t * resid w U X j t)
      σ2 := by
  have hT' : (Fintype.card T - Fintype.card B : ℝ) ≠ 0 := by
    have : (Fintype.card B : ℝ) < Fintype.card T := by exact_mod_cast hT
    linarith
  refine ((unbiasedMean_resid_mul σ2 ρ hw h j j).const_mul _).congr (fun X => rfl) ?_
  simp only [↓reduceIte]
  rw [trace_one_sub_hat_mul_of_eq h rfl]
  field_simp

/-- **The SUR estimator of the cross-cohort covariance** (Zellner): for `i ≠ j`,
`Σₜ ẽᵢₜẽⱼₜ / tr((I - Pᵢ)(I - Pⱼ))` has expectation `σ²ρ` for any volumes and designs. -/
theorem unbiasedMean_cross (σ2 ρ : ℝ) (hw : ∀ j t, 0 < w j t)
    (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) {i j : J} (hij : i ≠ j)
    (htr : trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j)) ≠ 0) :
    UnbiasedMean (lineCov w σ2 ρ) (blockDesign U)
      (fun X => (trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j)))⁻¹
        * ∑ t, resid w U X i t * resid w U X j t) (σ2 * ρ) := by
  refine ((unbiasedMean_resid_mul σ2 ρ hw h i j).const_mul _).congr (fun X => rfl) ?_
  simp only [hij, ↓reduceIte]
  field_simp

/-- **S67's divisor**: with one design and equal exposure shapes, `Σₜ ẽᵢₜẽⱼₜ / (T - p)` is
unbiased for `σ²ρ` (`i ≠ j`). For other shapes the right divisor is
`T - 2p + tr(PᵢPⱼ)` (`unbiasedMean_cross`, `trace_one_sub_hat_mul`). -/
theorem unbiasedMean_cross_of_shape (σ2 ρ : ℝ) {U₀ : Matrix T B ℝ} {a : J → ℝ} {g : T → ℝ}
    (hU : ∀ j, U j = U₀) (hwg : ∀ j t, w j t = a j * g t) (ha : ∀ j, 0 < a j)
    (hg : ∀ t, 0 < g t) (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det)
    (hT : Fintype.card B < Fintype.card T) {i j : J} (hij : i ≠ j) :
    UnbiasedMean (lineCov w σ2 ρ) (blockDesign U)
      (fun X => (Fintype.card T - Fintype.card B : ℝ)⁻¹ * ∑ t, resid w U X i t * resid w U X j t)
      (σ2 * ρ) := by
  have hw : ∀ j t, 0 < w j t := fun j t => by rw [hwg]; exact mul_pos (ha j) (hg t)
  have heq := trace_one_sub_hat_mul_of_eq h (hat_eq_of_shape hU hwg ha h i j)
  have hT' : (Fintype.card T - Fintype.card B : ℝ) ≠ 0 := by
    have : (Fintype.card B : ℝ) < Fintype.card T := by exact_mod_cast hT
    linarith
  simpa only [heq] using unbiasedMean_cross σ2 ρ hw h hij (by rw [heq]; exact hT')

end Credibility.LineResiduals
