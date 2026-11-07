import Credibility.Model

/-!
# The Bühlmann–Straub special case (thesis §2.6, eqs. (28)–(30), and §2.9)

`σⱼₜ² = σ²/wⱼₜ` and `ρᵢⱼ = δᵢⱼ`.
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

/-- Eq. (30). -/
theorem bs_σ2 [Nonempty T] (j : J) :
    (bsModel τ2 σsq w hτ hσ hw).σ2 j j = σsq / ∑ t, w j t := by
  sorry

/-- `K` is diagonal. -/
theorem bs_K [Nonempty T] :
    (bsModel τ2 σsq w hτ hσ hw).K = diagonal fun j => τ2 + σsq / ∑ t, w j t := by
  sorry

/-- The classical credibility factor `zⱼᴮ = wⱼ* / (wⱼ* + σ²/τ²)`. -/
noncomputable def bsZ (j : J) : ℝ := (∑ t, w j t) / (∑ t, w j t + σsq / τ2)

/-- `bⱼ = zⱼᴮ / z*ᴮ`. -/
theorem bs_b [Nonempty T] (j : J) :
    (bsModel τ2 σsq w hτ hσ hw).b j = bsZ τ2 σsq w j / ∑ i, bsZ τ2 σsq w i := by
  sorry

/-- The proposed model reduces to Bühlmann–Straub (§2.6).
Note: with a single cohort, `bⱼ = 1` and eq. (26) is `0/0`; the thesis
derivation silently needs at least two cohorts. -/
theorem bs_z [Nonempty T] (hJ : 1 < Fintype.card J) (j : J) :
    ((bsModel τ2 σsq w hτ hσ hw).moments j).bestZ = bsZ τ2 σsq w j := by
  sorry

/-- The balance property (§2.9) holds for Bühlmann–Straub weights for any data,
whether or not the model assumptions hold. Here `W j = wⱼ*`, `κ = σ²/τ²`,
and `m j` is the cohort estimate `μ̂ⱼ`. -/
theorem bs_balance [Nonempty J] (W : J → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ∀ j, 0 < W j)
    (m : J → ℝ) :
    let z := fun j => W j / (W j + κ)
    let mhat := (∑ j, z j * m j) / ∑ j, z j
    ∑ j, W j * (1 - z j) * (m j - mhat) = 0 := by
  sorry

end Credibility
