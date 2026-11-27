import Credibility.LineResiduals
import Credibility.CoreVectorMoments
import Credibility.FactorHenderson

/-!
# The moment layer for the cohort lines (extension, distribution-free)

`LineResiduals.lean` takes the second moments of the cells as a given table. Here they are the
covariances of actual random variables, and the pieces are composed. Cells `Xⱼₜ` (`LineData`)
have mean `(Uⱼb)ₜ` and covariance `lineCov + D(I ⊗ Λ)Dᵀ`: each cohort's line varies around a
common `b` with covariance `Λ` (`levelM`, `design_levelM_apply`), plus the year-correlated noise.

* A form unbiased for every *fixed* line stays unbiased when the lines are random
  (`Model.UnbiasedMean.add_design` in `FactorHenderson`: adding `DMDᵀ` to the table, `M`
  symmetric), so the residual
  estimators of `LineResiduals.lean` keep their expectations.
* The fitted lines `β̂ⱼ = GⱼXⱼ` (`fitW`, `LineData.coef`) have mean `b` and covariance
  `δⱼᵢΛ + Nⱼᵢ` (`LineData.cov_coef`), `N` the noise passed through the fit (`noiseN`).
* `N̂` (`noiseHat`) is `N` with `σ²`, `σ²ρ` replaced by residual estimates; so
  `CoreVector.integral_correctedLambda` gives `E Λ̂ = Λ` (`integral_correctedLambda_lines`), and
  with the pooled SUR estimators for any volumes (`integral_correctedLambda_pooled`). S67's fit
  (`studies/runs/vector-lambda-shocks.js`) is this with divisor `T - 2`, exact for equal exposure
  shapes (`unbiasedMean_cross_of_shape`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility.LineResiduals
open Credibility.Model

variable {Ω : Type*} [MeasurableSpace Ω] {J T B : Type*} [Fintype J] [DecidableEq J]
  [Fintype T] [DecidableEq T] [Fintype B] [DecidableEq B]

/-- The covariance of the stacked coefficients when each cohort's line varies around the
common mean with covariance `Λ`, independently across cohorts: `δᵢⱼΛ`. -/
def levelM (Λ : Matrix B B ℝ) : Matrix (J × B) (J × B) ℝ :=
  fun x y => if x.1 = y.1 then Λ x.2 y.2 else 0

omit [Fintype T] [DecidableEq T] [DecidableEq B] in
lemma design_levelM_apply (U : J → Matrix T B ℝ) (Λ : Matrix B B ℝ) (j i : J) (t s : T) :
    (blockDesign U * levelM (J := J) Λ * (blockDesign U)ᵀ) (j, t) (i, s)
      = if j = i then (U j * Λ * (U j)ᵀ) t s else 0 := by
  simp only [Matrix.mul_apply, transpose_apply, blockDesign, levelM, Fintype.sum_prod_type]
  by_cases h : j = i
  · subst h
    simp [ite_mul, mul_ite, sum_ite_eq']
  · simp [ite_mul, mul_ite, Ne.symm h, h]

variable (w : J → T → ℝ) (U : J → Matrix T B ℝ)

/-- The weighted least-squares coefficient map `Gⱼ = (VⱼᵀVⱼ)⁻¹VⱼᵀWⱼ^{1/2}`: `β̂ⱼ = GⱼXⱼ`. -/
noncomputable def fitW (j : J) : Matrix B T ℝ :=
  ((white w U j)ᵀ * white w U j)⁻¹ * (white w U j)ᵀ * diagonal (fun t => √(w j t))

/-- The noise covariance of the fitted coefficients, `Nⱼᵢ = σ²cⱼᵢ GⱼWⱼ^{-1/2}Wᵢ^{-1/2}Gᵢᵀ`. -/
noncomputable def noiseN (σ2 ρ : ℝ) (j i : J) : Matrix B B ℝ := fun p r =>
  σ2 * (if j = i then 1 else ρ) * ∑ s, fitW w U j p s * fitW w U i r s / (√(w j s) * √(w i s))

variable {w U}

omit [Fintype J] [DecidableEq J] in
lemma fitW_mul {j : J} (h : IsUnit ((white w U j)ᵀ * white w U j).det) :
    fitW w U j * U j = 1 := by
  rw [fitW, Matrix.mul_assoc, ← white, Matrix.mul_assoc, nonsing_inv_mul _ h]

variable (w U) in
/-- Cohort lines with random coefficients, as moments only: square-integrable cells
`Xⱼₜ` with mean `(Uⱼb)ₜ` (a common mean line `b`) and covariance `lineCov + D(I ⊗ Λ)Dᵀ`, i.e.
`δₜₛσ²cᵢⱼ/√(wⱼₜwᵢₜ) + δᵢⱼ(UⱼΛUⱼᵀ)ₜₛ` (`design_levelM_apply`): each cohort's line varies around
`b` with covariance `Λ`, independently across cohorts and of the noise. No distribution. -/
structure LineData (σ2 ρ : ℝ) (Λ : Matrix B B ℝ) (b : B → ℝ) (Pr : Measure Ω) where
  /-- The cell `Xⱼₜ`. -/
  X : J × T → Ω → ℝ
  memLp : ∀ p, MemLp (X p) 2 Pr
  mean : ∀ p, Pr[X p] = (blockDesign U *ᵥ fun y => b y.2) p
  cov : ∀ p q, cov[X p, X q; Pr]
    = lineCov w σ2 ρ p q + (blockDesign U * levelM (J := J) Λ * (blockDesign U)ᵀ) p q

namespace LineData

variable {σ2 ρ : ℝ} {Λ : Matrix B B ℝ} {b : B → ℝ} {Pr : Measure Ω}
  (E : LineData w U σ2 ρ Λ b Pr)

/-- The fitted coefficients `β̂ⱼ = GⱼXⱼ`, indexed by `(j, p)`. -/
noncomputable def coef (x : J × B) (ω : Ω) : ℝ := ∑ s, fitW w U x.1 x.2 s * E.X (x.1, s) ω

lemma memLp_coef (x : J × B) : MemLp (E.coef x) 2 Pr :=
  memLp_finsetSum _ fun _ _ => (E.memLp _).const_mul _

variable [IsProbabilityMeasure Pr]

/-- The fitted lines are unbiased for the mean line: `E β̂ⱼ = b`. -/
lemma integral_coef (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (x : J × B) :
    Pr[E.coef x] = b x.2 := by
  unfold coef
  rw [integral_finsetSum _ fun s _ => ((E.memLp _).const_mul _).integrable (by norm_num)]
  simp only [integral_const_mul, E.mean]
  have hU : ∀ j s, (blockDesign U *ᵥ fun y => b y.2) (j, s) = (U j *ᵥ b) s := fun j s => by
    simp [blockDesign, mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]
  simp only [hU]
  have e : ∑ s, fitW w U x.1 x.2 s * (U x.1 *ᵥ b) s = ((fitW w U x.1 * U x.1) *ᵥ b) x.2 := by
    rw [← mulVec_mulVec]; rfl
  rw [e, fitW_mul (h x.1), one_mulVec]

/-- **The fitted coefficients have covariance `δⱼᵢΛ + Nⱼᵢ`**: the lines' own variation plus
the noise passed through the fit (`noiseN`), for every distribution with these moments. -/
theorem cov_coef (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) (j i : J) (p r : B) :
    cov[E.coef (j, p), E.coef (i, r); Pr]
      = (if j = i then Λ p r else 0) + noiseN w U σ2 ρ j i p r := by
  unfold coef
  rw [covariance_fun_sum_fun_sum (fun _ => (E.memLp _).const_mul _)
    (fun _ => (E.memLp _).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, E.cov, design_levelM_apply,
    mul_add, sum_add_distrib]
  rw [add_comm]
  congr 1
  · -- the lines' own variation
    by_cases hji : j = i
    · subst hji
      simp only [ite_true]
      have e : fitW w U j * (U j * Λ * (U j)ᵀ) * (fitW w U j)ᵀ = Λ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, fitW_mul (h j), Matrix.one_mul,
          Matrix.mul_assoc, ← transpose_mul, fitW_mul (h j), transpose_one, Matrix.mul_one]
      conv_rhs => rw [← e]
      simp only [Matrix.mul_apply, transpose_apply, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    · simp [hji]
  · -- the noise
    simp only [lineCov, noiseN, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, mul_sum]
    exact sum_congr rfl fun s _ => by ring

include E in
/-- `Λ` is symmetric: it is the covariance of the fitted lines less a symmetric noise part. -/
lemma transpose_levelM (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) :
    (levelM (J := J) Λ)ᵀ = levelM Λ := by
  ext x y
  simp only [transpose_apply, levelM]
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ↓reduceIte]
    have e1 := E.cov_coef h x.1 x.1 y.2 x.2
    have e2 := E.cov_coef h x.1 x.1 x.2 y.2
    rw [covariance_comm] at e1
    have hN : noiseN w U σ2 ρ x.1 x.1 y.2 x.2 = noiseN w U σ2 ρ x.1 x.1 x.2 y.2 := by
      simp only [noiseN]
      congr 1
      exact sum_congr rfl fun _ _ => by ring
    simp only [ite_true] at e1 e2
    linarith
  · simp only [hxy, Ne.symm hxy, ↓reduceIte]

end LineData

/-- The noise estimate of the fitted lines: `N̂ⱼᵢ = ŝ²ⱼᵢ GⱼWⱼ^{-1/2}Wᵢ^{-1/2}Gᵢᵀ` with
`ŝ²ⱼᵢ = s2f(X)` on the diagonal (an estimate of `σ²`) and `rf(X)` off it (of `σ²ρ`). -/
noncomputable def noiseHat (w : J → T → ℝ) (U : J → Matrix T B ℝ) (s2f rf : (J × T → ℝ) → ℝ)
    (X : J × T → Ω → ℝ) (ω : Ω) : J → J → Matrix B B ℝ := fun j i p r =>
  (if j = i then s2f (fun q => X q ω) else rf (fun q => X q ω))
    * ∑ s, fitW w U j p s * fitW w U i r s / (√(w j s) * √(w i s))

omit [DecidableEq J] [DecidableEq T] [DecidableEq B] in
lemma integrable_of_unbiasedMean {Pr : Measure Ω} {C : J × T → J × T → ℝ} {D : Matrix (J × T) B ℝ}
    {f : (J × T → ℝ) → ℝ} {θ : ℝ} (h : UnbiasedMean C D f θ) {Z : J × T → Ω → ℝ}
    (hZ : ∀ p, MemLp (Z p) 2 Pr) : Integrable (fun ω => f (fun p => Z p ω)) Pr := by
  obtain ⟨Q, hQ, -⟩ := h
  simp_rw [← hQ, quad]
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  have := ((hZ p).integrable_mul (hZ q)).const_mul (Q p q)
  simpa only [Pi.mul_apply, mul_assoc] using this

/-- **The corrected `Λ̂` of the cohort lines is unbiased**: fit each cohort's line by weighted
least squares, estimate `σ²` and `σ²ρ` by any forms in the residuals that are unbiased for
every fixed line (e.g. `unbiasedMean_s2`, `unbiasedMean_cross`), build `N̂` from them, and the
corrected moment `Λ̂` of the fitted lines (`CoreVector.correctedLambda`) has `E Λ̂ = Λ`, for
every distribution with these moments. -/
theorem integral_correctedLambda_lines {σ2 ρ : ℝ} {Λ : Matrix B B ℝ} {b : B → ℝ}
    {Pr : Measure Ω} [IsProbabilityMeasure Pr] (E : LineData w U σ2 ρ Λ b Pr)
    (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det) {s2f rf : (J × T → ℝ) → ℝ}
    (hs2 : UnbiasedMean (lineCov w σ2 ρ) (blockDesign U) s2f σ2)
    (hr : UnbiasedMean (lineCov w σ2 ρ) (blockDesign U) rf (σ2 * ρ))
    (v : J → ℝ) (hv : ∑ j, v j = 1) (hv2 : ∑ j, v j ^ 2 ≠ 1) :
    Matrix.of (fun p r =>
      Pr[fun ω => CoreVector.correctedLambda v E.coef (noiseHat w U s2f rf E.X) ω p r]) = Λ := by
  have hM := E.transpose_levelM h
  have hE : ∀ {f θ}, UnbiasedMean (lineCov w σ2 ρ) (blockDesign U) f θ →
      Pr[fun ω => f (fun q => E.X q ω)] = θ := fun hf =>
    (hf.add_design hM).integral_eq E.X (fun y => b y.2) E.memLp E.mean E.cov
  refine CoreVector.integral_correctedLambda E.coef b Λ (noiseN w U σ2 ρ) E.memLp_coef
    (E.integral_coef h) (E.cov_coef h) v hv hv2 _ (fun j i p r => ?_) (fun j i p r => ?_)
  · by_cases hji : j = i
    · simpa only [noiseHat, hji, ite_true] using
        (integrable_of_unbiasedMean hs2 E.memLp).mul_const _
    · simpa only [noiseHat, hji, ite_false] using
        (integrable_of_unbiasedMean hr E.memLp).mul_const _
  · by_cases hji : j = i
    · simp only [noiseHat, noiseN, hji, ite_true, integral_mul_const, hE hs2, mul_one]
    · simp only [noiseHat, noiseN, hji, ite_false, integral_mul_const, hE hr]

/-- **The pooled fit, end to end**: with the pooled `ŝ²` (`s2Pool`) and the pooled `ρ̂ŝ²` with
SUR divisors (`rhoS2Pool`) in `N̂`, the corrected `Λ̂` of the cohort lines is unbiased for any
volumes, designs and distribution with these moments (`p < T`, `J ≥ 2`, nonzero traces). -/
theorem integral_correctedLambda_pooled {σ2 ρ : ℝ} {Λ : Matrix B B ℝ} {b : B → ℝ}
    {Pr : Measure Ω} [IsProbabilityMeasure Pr] (E : LineData w U σ2 ρ Λ b Pr)
    (hw : ∀ j t, 0 < w j t) (h : ∀ j, IsUnit ((white w U j)ᵀ * white w U j).det)
    (hT : Fintype.card B < Fintype.card T) (hJ : 1 < Fintype.card J)
    (htr : ∀ i j : J, i ≠ j →
      trace (((1 : Matrix T T ℝ) - hat w U i) * ((1 : Matrix T T ℝ) - hat w U j)) ≠ 0)
    (v : J → ℝ) (hv : ∑ j, v j = 1) (hv2 : ∑ j, v j ^ 2 ≠ 1) :
    Matrix.of (fun p r => Pr[fun ω => CoreVector.correctedLambda v E.coef
      (noiseHat w U (s2Pool w U) (rhoS2Pool w U) E.X) ω p r]) = Λ := by
  have : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  exact integral_correctedLambda_lines E h (unbiasedMean_s2Pool σ2 ρ hw h hT)
    (unbiasedMean_rhoS2Pool σ2 ρ hw h hJ htr) v hv hv2

end Credibility.LineResiduals
