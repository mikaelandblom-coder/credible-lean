import Credibility.Model
import Credibility.OffDiagonal

/-!
# Bridge to hierarchical credibility: a shared group level

Not in the thesis; first step towards two-level credibility (FINDINGS item 6,
`notes/merging-cohorts.md`). In the thesis the cohort levels `μⱼ` are
uncorrelated with variance `τ²`. Here they share a fraction `φ` of that
variance: `cov(μᵢ, μⱼ) = τ²` if `i = j` and `φτ²` otherwise, i.e. the level
covariance is `τ²·(11ᵀ)^φ` with `(·)^φ` the damping of `OffDiagonal.lean`.
The cohort estimates then have covariance `K_φ = τ²·(11ᵀ)^φ + Σ`, where
`Σᵢⱼ = σ²ᵢⱼρᵢⱼ` is the error covariance.

* `φ = 0` is the thesis: `K_0 = K` (`Kφ_zero`);
* `φ ∈ [0,1)` keeps `K_φ` positive definite (`Kφ_posDef`);
* `φ = 1` (one common level) gives `Σ + τ²·11ᵀ`: the error covariance plus
  a rank-one term along `1`, the structure behind Finding 5 (`Kφ_one`).
-/

open Matrix

namespace Credibility

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- Covariance of the cohort levels when they share a fraction `φ` of the
level variance: `τ²` on the diagonal, `φτ²` off it. -/
noncomputable def levelCov (τ2 φ : ℝ) : Matrix J J ℝ :=
  τ2 • shrinkOffDiag φ (of fun _ _ => (1 : ℝ))

/-- The error covariance `Σᵢⱼ = σ²ᵢⱼρᵢⱼ` of the cohort estimates. -/
noncomputable def errCov : Matrix J J ℝ := of fun i j => M.σ2 i j * M.ρ i j

/-- `K_φ = τ²·(11ᵀ)^φ + Σ`, the covariance of the cohort estimates when the
levels share a fraction `φ` of their variance. -/
noncomputable def Kφ (φ : ℝ) : Matrix J J ℝ := levelCov M.τ2 φ + M.errCov

omit [Fintype J] [Fintype T] [DecidableEq T] in
lemma levelCov_apply (τ2 φ : ℝ) (i j : J) :
    levelCov τ2 φ i j = if i = j then τ2 else φ * τ2 := by
  by_cases h : i = j <;> simp [levelCov, shrinkOffDiag, h, mul_comm]

omit [Fintype J] in
/-- `φ = 0` is the thesis model: `K_0 = K`. -/
theorem Kφ_zero [Nonempty T] : M.Kφ 0 = M.K := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h, add_comm]

omit [Fintype J] [DecidableEq T] in
/-- `φ = 1` (one common level): `K_1 = Σ + τ²·11ᵀ`, the error covariance plus
a rank-one term along `1`. -/
theorem Kφ_one : M.Kφ 1 = M.errCov + M.τ2 • vecMulVec 1 1 := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, add_comm]
  by_cases h : i = j <;> simp [h]

omit [Fintype J] in
/-- The error covariance is `K - τ²·I`, so `K_1 = K - τ²·I + τ²·11ᵀ`. -/
theorem errCov_eq [Nonempty T] : M.errCov = M.K - M.τ2 • (1 : Matrix J J ℝ) := by
  ext i j
  rw [Matrix.sub_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h]

/-- The error covariance is positive semidefinite when `ρ` is: for every
`ε > 0`, `Σ + εI` is the `K` of the model with `τ² = ε`, positive definite by
`K_posDef`. -/
theorem errCov_posSemidef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) :
    M.errCov.PosSemidef := by
  -- The model with `τ² = ε`.
  let Mε : (ε : ℝ) → 0 < ε → Model J T := fun ε hε => { M with τ2 := ε, τ2_pos := hε }
  have hK : ∀ ε (hε : 0 < ε), (Mε ε hε).K = M.errCov + ε • (1 : Matrix J J ℝ) := by
    intro ε hε
    ext i j
    rw [Matrix.add_apply, (Mε ε hε).K_apply]
    by_cases h : i = j <;> simp [Mε, errCov, h, σ2, a]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have hE : M.errCov = (Mε 1 one_pos).K - 1 := by rw [hK, one_smul, add_sub_cancel_right]
    rw [hE]
    exact ((Mε 1 one_pos).K_posDef hρ).isHermitian.sub isHermitian_one
  · -- `xᵀΣx + ε‖x‖² ≥ 0` for every `ε > 0`.
    have h : ∀ ε, 0 < ε → 0 ≤ star x ⬝ᵥ (M.errCov *ᵥ x) + ε * (star x ⬝ᵥ x) := by
      intro ε hε
      have := ((hK ε hε) ▸ (Mε ε hε).K_posDef hρ).posSemidef.dotProduct_mulVec_nonneg x
      simpa [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul] using this
    by_contra hneg
    rw [not_le] at hneg
    have hxx : 0 ≤ star x ⬝ᵥ x := by
      simp only [dotProduct, star_trivial]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    set q := star x ⬝ᵥ (M.errCov *ᵥ x)
    set n := star x ⬝ᵥ x
    have := h (-q / (2 * (n + 1))) (div_pos (by linarith) (by linarith))
    have hn1 : 0 < n + 1 := by linarith
    have : -q / (2 * (n + 1)) * n ≤ -q / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith

/-- For `φ ∈ [0,1)`, `K_φ` is positive definite: `τ²·(11ᵀ)^φ ≻ 0` by
`posDef_shrinkOffDiag` (`11ᵀ ⪰ 0` with unit diagonal), and `Σ ⪰ 0`. -/
theorem Kφ_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (M.Kφ φ).PosDef := by
  have h11 : (of fun _ _ => (1 : ℝ) : Matrix J J ℝ).PosSemidef := by
    simpa [vecMulVec] using posSemidef_vecMulVec_self_star (1 : J → ℝ)
  exact PosDef.add_posSemidef
    ((posDef_shrinkOffDiag h11 h0 h1 fun _ => one_pos).smul M.τ2_pos)
    (M.errCov_posSemidef hρ)

end Model
end Credibility
