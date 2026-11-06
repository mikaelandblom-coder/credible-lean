import Credibility.Weights

/-!
# Two cohorts with time-constant weights (thesis §2.7, eqs. (75)–(84))

`σᵢ` is the noise of cohort `i`'s estimate, `κᵢ = σᵢ²/τ²`.
Eq. (81), `z₁ = 1 / (1 + κ₁ - √(κ₁κ₂) ρ)`, is stated here without square roots:
`z₁ = τ² / (τ² + σ₁² - σ₁σ₂ρ)`.
-/

open Matrix

namespace Credibility.TwoCohorts

variable (σ1 σ2 τ2 ρ : ℝ)

/-- `σ₁² + σ₂² + 2τ² - 2σ₁σ₂ρ`. -/
def D : ℝ := σ1 ^ 2 + σ2 ^ 2 + 2 * τ2 - 2 * σ1 * σ2 * ρ

noncomputable def s2 : ℝ :=
  ((σ1 ^ 2 + τ2) * (σ2 ^ 2 + τ2) - σ1 ^ 2 * σ2 ^ 2 * ρ ^ 2) / D σ1 σ2 τ2 ρ

noncomputable def b1 : ℝ := (σ2 ^ 2 + τ2 - σ1 * σ2 * ρ) / D σ1 σ2 τ2 ρ

/-- The covariance matrix of the two cohort estimates. -/
def K : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ1 ^ 2 + τ2, σ1 * σ2 * ρ; σ1 * σ2 * ρ, σ2 ^ 2 + τ2]

variable {σ1 σ2 τ2 ρ}

theorem D_pos (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : ρ ≤ 1) :
    0 < D σ1 σ2 τ2 ρ := by
  sorry

/-- The general GLS weights specialise to (77)–(78). -/
theorem gls_two (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : |ρ| < 1) :
    glsWeight (K σ1 σ2 τ2 ρ) 0 = b1 σ1 σ2 τ2 ρ
      ∧ (invTotal (K σ1 σ2 τ2 ρ))⁻¹ = s2 σ1 σ2 τ2 ρ := by
  sorry

/-- Eqs. (79), (81). -/
theorem z1_eq (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : ρ ≤ 1)
    (hsing : τ2 + σ1 ^ 2 - σ1 * σ2 * ρ ≠ 0) :
    (1 - b1 σ1 σ2 τ2 ρ) * τ2 / (τ2 + σ1 ^ 2 - s2 σ1 σ2 τ2 ρ)
      = τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) := by
  sorry

/-- Bühlmann–Straub is recovered at `ρ = 0`. -/
theorem z1_rho_zero : τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * 0) = τ2 / (τ2 + σ1 ^ 2) := by
  simp

/-- Eqs. (83)–(84): the sign flip past `ρ* = (τ² + σ₁²) / (σ₁σ₂)`. -/
theorem z1_neg_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) :
    τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) < 0 ↔ (τ2 + σ1 ^ 2) / (σ1 * σ2) < ρ := by
  sorry

/-- The singularity lies in `[-1, 1]` iff `κ₂ ≥ (1 + κ₁)² / κ₁`. -/
theorem singularity_reachable_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) :
    (τ2 + σ1 ^ 2) / (σ1 * σ2) ≤ 1
      ↔ (1 + σ1 ^ 2 / τ2) ^ 2 / (σ1 ^ 2 / τ2) ≤ σ2 ^ 2 / τ2 := by
  sorry

/-- Sharpens §2.7: the thesis notes `z₁ > 1` can occur and clips it in
eq. (87), but gives no condition. Below the singularity, correlation pushes
the credibility above one ("noise cancellation") exactly when `σ₁ < σ₂ρ`. -/
theorem z1_gt_one_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2)
    (hρ : ρ < (τ2 + σ1 ^ 2) / (σ1 * σ2)) :
    1 < τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) ↔ σ1 < σ2 * ρ := by
  sorry

end Credibility.TwoCohorts
