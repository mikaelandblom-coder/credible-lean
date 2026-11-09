import Credibility.UnequalEstimation

/-!
# The Bühlmann–Straub special case (thesis §2.6, eqs. (28)–(30), and §2.9)

`σⱼₜ² = σ²/wⱼₜ` and `ρᵢⱼ = δᵢⱼ`. Eq. (30), the weights and the factor are the
case `Tⱼ = T` of the unequal-length versions (`Unequal.σ2_bs`, `Unequal.b_bs`,
`Unequal.bestZ_bs`); the balance property itself is in `Balance.lean`.
-/

open Finset Matrix

namespace Credibility

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- The model under the Bühlmann–Straub assumptions (28). -/
noncomputable def bsModel (τ2 σsq : ℝ) (w : J → T → ℝ)
    (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : ∀ j t, 0 < w j t) : Model J T where
  τ2 := τ2
  σ := fun j t => Real.sqrt (σsq / w j t)
  ρ := fun i j => if i = j then 1 else 0
  τ2_pos := hτ
  σ_pos := fun j t => Real.sqrt_pos.mpr (div_pos hσ (hw j t))
  ρ_self := by intro j; simp
  ρ_symm := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]

variable (τ2 σsq : ℝ) (w : J → T → ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : ∀ j t, 0 < w j t)

omit [Fintype J] [DecidableEq T] in
/-- Eq. (29): inverse-variance weights become volume weights. -/
theorem bs_a (j : J) (t : T) :
    (bsModel τ2 σsq w hτ hσ hw).a j t = w j t / ∑ s, w j s := by
  -- `σⱼₜ⁻² = wⱼₜ/σ²`; the factor `1/σ²` cancels.
  have h : ∀ s, (bsModel τ2 σsq w hτ hσ hw).σ j s ^ 2 = σsq / w j s := fun s =>
    Real.sq_sqrt (div_pos hσ (hw j s)).le
  simp only [Model.a, invVarWeight, h, inv_div]
  rw [← sum_div, div_div_div_cancel_right₀ hσ.ne']

omit [Fintype J] [Fintype T] [DecidableEq T] in
/-- `σⱼₜ = √σ² / √wⱼₜ`: the hypothesis of the unequal-length Bühlmann–Straub results. -/
lemma bs_σ_eq (j : J) (t : T) :
    (bsModel τ2 σsq w hτ hσ hw).σ j t = √σsq / √(w j t) :=
  Real.sqrt_div' σsq (hw j t).le

omit [Fintype J] in
/-- Eq. (30). -/
theorem bs_σ2 [Nonempty T] (j : J) :
    (bsModel τ2 σsq w hτ hσ hw).σ2 j j = σsq / ∑ t, w j t := by
  -- `Unequal.σ2_bs` with `Tⱼ = T`, `s = √σ²`.
  set M := bsModel τ2 σsq w hτ hσ hw
  have := M.toUnequal.σ2_bs (√σsq) hw (bs_σ_eq τ2 σsq w hτ hσ hw) j
  rwa [M.toUnequal_σ2, Real.sq_sqrt hσ.le] at this

omit [Fintype J] in
/-- `K` is diagonal. -/
theorem bs_K [Nonempty T] :
    (bsModel τ2 σsq w hτ hσ hw).K = diagonal fun j => τ2 + σsq / ∑ t, w j t := by
  -- `ρᵢⱼ = δᵢⱼ` makes `K` diagonal (`Unequal.K_eq_diagonal` with `Tⱼ = T`).
  set M := bsModel τ2 σsq w hτ hσ hw
  have h0 : ∀ i k, i ≠ k → M.toUnequal.σ2 i k * M.toUnequal.ρ i k = 0 := fun i k h => by
    simp [M, Model.toUnequal, bsModel, h]
  rw [← M.toUnequal_K, Unequal.K_eq_diagonal _ h0, M.toUnequal_σ2]
  exact congrArg diagonal (funext fun i => by
    rw [show M.σ2 i i = _ from bs_σ2 τ2 σsq w hτ hσ hw i]; rfl)

/-- The classical credibility factor `zⱼᴮ = wⱼ* / (wⱼ* + σ²/τ²)`. -/
noncomputable def bsZ (j : J) : ℝ := (∑ t, w j t) / (∑ t, w j t + σsq / τ2)

omit [DecidableEq T] in
include hτ hσ hw in
/-- The inverse of a diagonal `K = diag(τ² + σ²/wⱼ*)` applied to `u` is `zⱼᴮ/τ²`. -/
theorem bs_Kinv_one [Nonempty T] (K : Matrix J J ℝ)
    (hK : K = diagonal fun j => τ2 + σsq / ∑ t, w j t) :
    K⁻¹ *ᵥ 1 = fun j => bsZ τ2 σsq w j / τ2 := by
  -- `Core.Kinv_one_of_diag`, and `1/(τ² + σ²/wⱼ*) = zⱼᴮ/τ²`.
  have hW : ∀ j, 0 < ∑ t, w j t := fun j => sum_pos (fun t _ => hw j t) univ_nonempty
  rw [Core.Kinv_one_of_diag hK fun j => (add_pos hτ (div_pos hσ (hW j))).ne']
  ext j
  have := (hW j).ne'
  have : (∑ t, w j t) + σsq / τ2 ≠ 0 := (add_pos (hW j) (div_pos hσ hτ)).ne'
  simp only [bsZ]
  field_simp

/-- `bⱼ = zⱼᴮ / z*ᴮ`. -/
theorem bs_b [Nonempty T] (j : J) :
    (bsModel τ2 σsq w hτ hσ hw).b j = bsZ τ2 σsq w j / ∑ i, bsZ τ2 σsq w i := by
  -- `Unequal.b_bs` with `Tⱼ = T`, `s = √σ²`.
  set M := bsModel τ2 σsq w hτ hσ hw
  have := M.toUnequal.b_bs (√σsq) hw (bs_σ_eq τ2 σsq w hτ hσ hw)
    (fun i k => rfl) j
  rwa [M.toUnequal_b, Real.sq_sqrt hσ.le] at this

/-- The proposed model reduces to Bühlmann–Straub (§2.6).
Note: with a single cohort, `bⱼ = 1` and eq. (26) is `0/0`; the thesis
derivation silently needs at least two cohorts. -/
theorem bs_z [Nonempty T] (hJ : 1 < Fintype.card J) (j : J) :
    ((bsModel τ2 σsq w hτ hσ hw).moments j).bestZ = bsZ τ2 σsq w j := by
  -- `Unequal.bestZ_bs` with `Tⱼ = T`, `s = √σ²`.
  set M := bsModel τ2 σsq w hτ hσ hw
  have := M.toUnequal.bestZ_bs (√σsq) hw (bs_σ_eq τ2 σsq w hτ hσ hw)
    (fun i k => rfl) hJ j
  rwa [M.toUnequal_moments, Real.sq_sqrt hσ.le] at this

end Credibility
