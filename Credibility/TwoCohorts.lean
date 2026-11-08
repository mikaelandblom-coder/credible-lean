import Credibility.Weights

/-!
# Two cohorts with time-constant weights (thesis §2.7, eqs. (31)–(32))

`σᵢ` is the noise of cohort `i`'s estimate, `κᵢ = σᵢ²/τ²`.
Eq. (32), `z₁ = 1 / (1 + κ₁ - √(κ₁κ₂) ρ)`, is stated here without square roots:
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
  -- D = (σ₁ - σ₂)² + 2τ² + 2σ₁σ₂(1 - ρ)
  unfold D
  nlinarith [sq_nonneg (σ1 - σ2), mul_pos h1 h2, mul_nonneg (mul_pos h1 h2).le (sub_nonneg.2 hρ)]

/-- The general GLS weights specialise to (31) and the `s²` display before it. -/
theorem gls_two (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : |ρ| < 1) :
    glsWeight (K σ1 σ2 τ2 ρ) 0 = b1 σ1 σ2 τ2 ρ
      ∧ (invTotal (K σ1 σ2 τ2 ρ))⁻¹ = s2 σ1 σ2 τ2 ρ := by
  have hD := (D_pos h1 h2 hτ (abs_lt.1 hρ).2.le).ne'
  -- det K = (σ₁² + τ²)(σ₂² + τ²) - σ₁²σ₂²ρ² > 0 since ρ² < 1.
  have hc : (σ1 * σ2 * ρ) ^ 2 < (σ1 * σ2) ^ 2 := by
    have : ρ ^ 2 < 1 := by nlinarith [abs_lt.1 hρ]
    rw [mul_pow]; exact mul_lt_of_lt_one_right (by positivity) this
  set det := (σ1 ^ 2 + τ2) * (σ2 ^ 2 + τ2) - σ1 ^ 2 * σ2 ^ 2 * ρ ^ 2 with hdet_def
  have hdet : det ≠ 0 := by
    apply ne_of_gt; rw [hdet_def]; nlinarith [mul_pos h1 h2, sq_nonneg σ1, sq_nonneg σ2]
  have hinv : (K σ1 σ2 τ2 ρ)⁻¹ = det⁻¹ • !![σ2 ^ 2 + τ2, -(σ1 * σ2 * ρ); -(σ1 * σ2 * ρ), σ1 ^ 2 + τ2] := by
    rw [Matrix.inv_def, K, adjugate_fin_two_of, Matrix.det_fin_two_of, Ring.inverse_eq_inv]
    congr 2; rw [hdet_def]; ring
  have hv : (K σ1 σ2 τ2 ρ)⁻¹ *ᵥ 1 = ![det⁻¹ * (σ2 ^ 2 + τ2 - σ1 * σ2 * ρ),
      det⁻¹ * (σ1 ^ 2 + τ2 - σ1 * σ2 * ρ)] := by
    rw [hinv]; ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have htot : invTotal (K σ1 σ2 τ2 ρ) = det⁻¹ * D σ1 σ2 τ2 ρ := by
    rw [invTotal, hv]; simp [dotProduct, Fin.sum_univ_two, D]; ring
  refine ⟨?_, ?_⟩
  · rw [glsWeight, htot, hv, b1]; simp; field_simp
  · rw [htot, s2, ← hdet_def]; field_simp

/-- Eq. (32) and the display before it. For `|ρ| < 1` this is the case `J = 2`
of `Core.bestZ_of_equalCov` with `c = σ₁σ₂ρ`; it is proved directly since it is an
algebraic identity that needs only `ρ ≤ 1`, not `K ≻ 0` (e.g. `ρ = -3`). -/
theorem z1_eq (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : ρ ≤ 1)
    (hsing : τ2 + σ1 ^ 2 - σ1 * σ2 * ρ ≠ 0) :
    (1 - b1 σ1 σ2 τ2 ρ) * τ2 / (τ2 + σ1 ^ 2 - s2 σ1 σ2 τ2 ρ)
      = τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) := by
  -- With A = σ₁² + τ², c = σ₁σ₂ρ: 1 - b₁ = (A - c)/D and A·D - det K = (A - c)²,
  -- so the left side is ((A - c)τ²/D) / ((A - c)²/D).
  have hD := (D_pos h1 h2 hτ hρ).ne'
  have h1b : 1 - b1 σ1 σ2 τ2 ρ = (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) / D σ1 σ2 τ2 ρ := by
    rw [b1, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, D]; ring
  have hs : τ2 + σ1 ^ 2 - s2 σ1 σ2 τ2 ρ
      = (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) ^ 2 / D σ1 σ2 τ2 ρ := by
    rw [s2, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, D]; ring
  rw [h1b, hs]
  field_simp

/-- Portfolio weight from the credibility factors: `b₁ = z₁ / (z₁ + z₂)`, with
`zᵢ = τ² / (τ² + σᵢ² - σ₁σ₂ρ)` as in eq. (32). Not in the published thesis:
it is on the defence slides and was later added to `main.tex` in §2.7.1, just
after (36). It has the Bühlmann–Straub form `b_j = z_j / z_*`, which for
correlated data holds with two cohorts but not in general with three or more
(it does under equal covariances: `Model.b_eq_of_equalCov`). -/
theorem b1_eq_z (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) (hρ : ρ ≤ 1)
    (hs1 : τ2 + σ1 ^ 2 - σ1 * σ2 * ρ ≠ 0) (hs2 : τ2 + σ2 ^ 2 - σ1 * σ2 * ρ ≠ 0) :
    b1 σ1 σ2 τ2 ρ = τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ)
      / (τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) + τ2 / (τ2 + σ2 ^ 2 - σ1 * σ2 * ρ)) := by
  -- With Aᵢ = τ² + σᵢ² - σ₁σ₂ρ: zᵢ = τ²/Aᵢ, so z₁/(z₁ + z₂) = A₂/(A₁ + A₂),
  -- and A₁ + A₂ = D.
  have hD := (D_pos h1 h2 hτ hρ).ne'
  set A1 := τ2 + σ1 ^ 2 - σ1 * σ2 * ρ
  set A2 := τ2 + σ2 ^ 2 - σ1 * σ2 * ρ
  have hDA : D σ1 σ2 τ2 ρ = A1 + A2 := by rw [D]; ring
  rw [hDA] at hD
  have hz : τ2 / A1 + τ2 / A2 = τ2 * (A1 + A2) / (A1 * A2) := by
    field_simp; ring
  rw [hz, b1, hDA, div_div_eq_mul_div, eq_div_iff (by positivity)]
  field_simp
  ring

/-- Bühlmann–Straub is recovered at `ρ = 0`. -/
theorem z1_rho_zero : τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * 0) = τ2 / (τ2 + σ1 ^ 2) := by
  simp

/-- The sign flip (displays after (32)) past `ρ* = (τ² + σ₁²) / (σ₁σ₂)`. -/
theorem z1_neg_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) :
    τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) < 0 ↔ (τ2 + σ1 ^ 2) / (σ1 * σ2) < ρ := by
  -- τ² > 0, so the sign is that of the denominator.
  rw [div_lt_iff₀ (mul_pos h1 h2), div_neg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · intro h; left; constructor <;> nlinarith

/-- The singularity lies in `[-1, 1]` iff `κ₂ ≥ (1 + κ₁)² / κ₁`. -/
theorem singularity_reachable_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2) :
    (τ2 + σ1 ^ 2) / (σ1 * σ2) ≤ 1
      ↔ (1 + σ1 ^ 2 / τ2) ^ 2 / (σ1 ^ 2 / τ2) ≤ σ2 ^ 2 / τ2 := by
  -- Both sides say (τ² + σ₁²)² ≤ σ₁²σ₂², i.e. τ² + σ₁² ≤ σ₁σ₂.
  have hp := mul_pos h1 h2
  have hA : 0 < τ2 + σ1 ^ 2 := by positivity
  have hrhs : (1 + σ1 ^ 2 / τ2) ^ 2 / (σ1 ^ 2 / τ2) = (τ2 + σ1 ^ 2) ^ 2 / (τ2 * σ1 ^ 2) := by
    field_simp
  rw [hrhs, div_le_iff₀ hp, one_mul, div_le_div_iff₀ (by positivity) hτ]
  constructor
  · intro h
    have := mul_le_mul h h hA.le hp.le
    nlinarith
  · intro h
    by_contra h'
    push Not at h'
    have := mul_lt_mul'' h' h' hp.le hp.le
    nlinarith

/-- Sharpens §2.7: the thesis notes `z₁ > 1` can occur and clips it in
eq. (34), but gives no condition. Below the singularity, correlation pushes
the credibility above one ("noise cancellation") exactly when `σ₁ < σ₂ρ`. -/
theorem z1_gt_one_iff (h1 : 0 < σ1) (h2 : 0 < σ2) (hτ : 0 < τ2)
    (hρ : ρ < (τ2 + σ1 ^ 2) / (σ1 * σ2)) :
    1 < τ2 / (τ2 + σ1 ^ 2 - σ1 * σ2 * ρ) ↔ σ1 < σ2 * ρ := by
  -- Below the singularity the denominator is positive, so z₁ > 1 iff
  -- σ₁² < σ₁σ₂ρ, i.e. σ₁ < σ₂ρ.
  have hden : 0 < τ2 + σ1 ^ 2 - σ1 * σ2 * ρ := by
    rw [lt_div_iff₀ (mul_pos h1 h2)] at hρ; linarith
  rw [one_lt_div hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end Credibility.TwoCohorts
