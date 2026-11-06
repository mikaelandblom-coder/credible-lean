import Mathlib

/-!
# Best unbiased linear weights (thesis §2.5)

* Cohort level: inverse-variance weights, eq. (23).
* Portfolio level: `b = K⁻¹u / uᵀK⁻¹u`, eqs. (24)–(25).
-/

open Finset Matrix

namespace Credibility

section InverseVariance

variable {T : Type*} [Fintype T]

/-- Inverse-variance weights, eq. (23). -/
noncomputable def invVarWeight (σsq : T → ℝ) (t : T) : ℝ :=
  (σsq t)⁻¹ / ∑ s, (σsq s)⁻¹

lemma sum_inv_pos [Nonempty T] (σsq : T → ℝ) (hσ : ∀ t, 0 < σsq t) :
    0 < ∑ s, (σsq s)⁻¹ :=
  Finset.sum_pos (fun t _ => inv_pos.mpr (hσ t)) Finset.univ_nonempty

theorem sum_invVarWeight [Nonempty T] (σsq : T → ℝ) (hσ : ∀ t, 0 < σsq t) :
    ∑ t, invVarWeight σsq t = 1 := by
  simp only [invVarWeight, ← Finset.sum_div]
  exact div_self (sum_inv_pos σsq hσ).ne'

/-- The minimal error variance. -/
theorem invVarWeight_value [Nonempty T] (σsq : T → ℝ) (hσ : ∀ t, 0 < σsq t) :
    ∑ t, invVarWeight σsq t ^ 2 * σsq t = (∑ s, (σsq s)⁻¹)⁻¹ := by
  have hS := (sum_inv_pos σsq hσ).ne'
  have : ∀ t, invVarWeight σsq t ^ 2 * σsq t = (σsq t)⁻¹ / (∑ s, (σsq s)⁻¹) ^ 2 := by
    intro t
    have := (hσ t).ne'
    simp only [invVarWeight]
    field_simp
  simp only [this, ← Finset.sum_div]
  field_simp

/-- Eq. (23) minimises `Σ aₜ² σₜ²` among weights summing to one. -/
theorem invVarWeight_optimal (σsq : T → ℝ) (hσ : ∀ t, 0 < σsq t)
    (a : T → ℝ) (ha : ∑ t, a t = 1) :
    ∑ t, invVarWeight σsq t ^ 2 * σsq t ≤ ∑ t, a t ^ 2 * σsq t := by
  sorry

end InverseVariance

section GLS

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- `uᵀK⁻¹u`, written `K⁻¹ₓₓ` in the thesis. -/
noncomputable def invTotal (K : Matrix J J ℝ) : ℝ := 1 ⬝ᵥ (K⁻¹ *ᵥ 1)

/-- Portfolio weights, eq. (25) (vector form just before (24)). -/
noncomputable def glsWeight (K : Matrix J J ℝ) (j : J) : ℝ :=
  (K⁻¹ *ᵥ 1) j / invTotal K

theorem invTotal_pos [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) : 0 < invTotal K := by
  sorry

theorem sum_glsWeight [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) :
    ∑ j, glsWeight K j = 1 := by
  sorry

/-- `v = K b = s² u`: every cohort estimate has the same covariance with the
portfolio estimate, namely `Var(μ̂)`. -/
theorem mulVec_glsWeight {K : Matrix J J ℝ} (hK : K.PosDef) :
    K *ᵥ glsWeight K = fun _ => (invTotal K)⁻¹ := by
  sorry

/-- Eq. (24): the minimal portfolio error variance `s² = 1 / K⁻¹ₓₓ`. -/
theorem glsWeight_value [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) :
    glsWeight K ⬝ᵥ (K *ᵥ glsWeight K) = (invTotal K)⁻¹ := by
  sorry

/-- `b = K⁻¹u / uᵀK⁻¹u` (just before (24)) minimises `bᵀKb` subject to `uᵀb = 1`. -/
theorem glsWeight_optimal {K : Matrix J J ℝ} (hK : K.PosDef) (b : J → ℝ)
    (hb : ∑ j, b j = 1) :
    glsWeight K ⬝ᵥ (K *ᵥ glsWeight K) ≤ b ⬝ᵥ (K *ᵥ b) := by
  sorry

end GLS
end Credibility
