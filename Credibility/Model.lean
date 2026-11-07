import Credibility.Blend
import Credibility.Weights

/-!
# The correlated data model and the proposed credibility factor
(thesis §2.3–2.5, eqs. (15)–(27))

`μⱼ = μ + τ εⱼ`, `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`, `cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ`.
-/

open Finset Matrix

namespace Credibility

structure Model (J T : Type*) where
  /-- Heterogeneity between cohorts. -/
  τ2 : ℝ
  /-- Observation noise (standard deviation) of cohort `j` in period `t`. -/
  σ : J → T → ℝ
  /-- Contemporaneous correlation between cohorts. -/
  ρ : J → J → ℝ
  τ2_pos : 0 < τ2
  σ_pos : ∀ j t, 0 < σ j t
  ρ_self : ∀ j, ρ j j = 1
  ρ_symm : ∀ i j, ρ i j = ρ j i

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- `cov(μᵢₜ, μⱼₛ)` (the thesis's `K̄ᵢⱼᵗˢ`), eq. (16). -/
def obsCov (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0)
    + M.τ2 * (if i = j then 1 else 0)

/-- Cohort weights `aⱼₜ`, eq. (23). -/
noncomputable def a (j : J) (t : T) : ℝ := invVarWeight (fun s => M.σ j s ^ 2) t

/-- `σ²ᵢⱼ = Σₜ aᵢₜ aⱼₜ σᵢₜ σⱼₜ`, eq. (18). -/
noncomputable def σ2 (i j : J) : ℝ := ∑ t, M.a i t * M.a j t * M.σ i t * M.σ j t

/-- `Kᵢⱼ = cov(μ̂ᵢ, μ̂ⱼ) = Σₜₛ aᵢₜ aⱼₛ K̄ᵢⱼᵗˢ`, eq. (21). -/
noncomputable def K : Matrix J J ℝ :=
  fun i j => ∑ t, ∑ s, M.a i t * M.a j s * M.obsCov i j t s

omit [Fintype J] in
/-- `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ`, as in eq. (27). -/
theorem K_apply [Nonempty T] (i j : J) :
    M.K i j = M.σ2 i j * M.ρ i j + M.τ2 * (if i = j then 1 else 0) := by
  have hsum : ∀ k, ∑ t, M.a k t = 1 := fun k =>
    sum_invVarWeight _ (fun t => pow_pos (M.σ_pos k t) 2)
  simp only [K, obsCov, mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true]
  rw [σ2, sum_mul]
  congr 1
  · exact sum_congr rfl fun t _ => by ring
  · split_ifs with h
    · subst h
      calc ∑ x, ∑ y, M.a i x * M.a i y * M.τ2
          = (∑ x, M.a i x) * (∑ y, M.a i y) * M.τ2 := by
            rw [sum_mul_sum, sum_mul]; simp_rw [sum_mul]
        _ = M.τ2 := by rw [hsum]; ring
    · simp

theorem K_symm : M.Kᵀ = M.K := by
  sorry

/-- The thesis takes positive-definiteness of `K` for granted. Here it needs
the correlations to form a positive-semidefinite matrix, and `τ² > 0`. -/
theorem K_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) : M.K.PosDef := by
  sorry

/-- Portfolio weights `bⱼ`. -/
noncomputable def b : J → ℝ := glsWeight M.K

/-- Portfolio error variance `s²`. -/
noncomputable def s2 : ℝ := (invTotal M.K)⁻¹

/-- The moments entering the blend for cohort `j` (§2.4). -/
noncomputable def moments (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := M.s2
  varTarget := M.τ2
  covEst := (M.K *ᵥ M.b) j
  covCohortTarget := M.τ2
  covPortfolioTarget := M.b j * M.τ2

/-- Eq. (22): the credibility factor for any linear model (17). -/
theorem bestZ_linear (j : J) :
    (M.moments j).bestZ
      = (M.s2 - (M.K *ᵥ M.b) j + M.τ2 - M.b j * M.τ2)
        / (M.s2 - 2 * (M.K *ᵥ M.b) j + M.τ2 + M.σ2 j j) := by
  sorry

/-- Eqs. (26)/(27): the proposed credibility factor at the optimal weights. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) := by
  sorry

/-- Eq. (26), second form: `zⱼ = cov(μ̂ⱼ - μ̂, μⱼ) / Var(μ̂ⱼ - μ̂)`. -/
theorem gap_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).gap = M.τ2 + M.σ2 j j - M.s2 := by
  sorry

end Model
end Credibility
