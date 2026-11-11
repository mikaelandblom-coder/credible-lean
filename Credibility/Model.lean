import Credibility.Unequal

/-!
# The correlated data model and the proposed credibility factor
(thesis §2.3–2.5, eqs. (15)–(27))

The parameters and eq. (16) are in `Data.lean`. The thesis observes every
cohort in every period: this is `Unequal` with `Tⱼ = T` (`toUnequal`), so the
results below with an `Unequal` twin are proved as corollaries of it.
-/

open Finset Matrix

namespace Credibility

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- Cohort weights `aⱼₜ`, eq. (23). -/
noncomputable def a (j : J) (t : T) : ℝ := invVarWeight (fun s => M.σ j s ^ 2) t

/-- `σ²ᵢⱼ = Σₜ aᵢₜ aⱼₜ σᵢₜ σⱼₜ`, eq. (18). -/
noncomputable def σ2 (i j : J) : ℝ := ∑ t, M.a i t * M.a j t * M.σ i t * M.σ j t

/-- `Kᵢⱼ = cov(μ̂ᵢ, μ̂ⱼ) = Σₜₛ aᵢₜ aⱼₛ K̄ᵢⱼᵗˢ`, eq. (21). -/
noncomputable def K : Matrix J J ℝ :=
  fun i j => ∑ t, ∑ s, M.a i t * M.a j s * M.obsCov i j t s

end Model

namespace Unequal

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Unequal J T)

omit [Fintype J] [DecidableEq J] in
/-- With full series (`Tⱼ = T`) the weights are those of the thesis. -/
theorem a_eq_of_full (h : ∀ j, M.obs j = univ) : M.a = M.toModel.a := by
  funext j t
  simp [a, Model.a, invVarWeight, h]

omit [Fintype J] [DecidableEq J] in
/-- With full series, `σ²ᵢⱼ` is that of the thesis, eq. (18). -/
theorem σ2_eq_of_full (h : ∀ j, M.obs j = univ) : M.σ2 = M.toModel.σ2 := by
  funext i j
  simp [σ2, Model.σ2, overlap, h, M.a_eq_of_full h]

omit [Fintype J] in
/-- With full series, `K` is that of the thesis, eq. (21). -/
theorem K_eq_of_full (h : ∀ j, M.obs j = univ) : M.K = M.toModel.K := by
  funext i j
  simp [K, Model.K, h, M.a_eq_of_full h]

end Unequal

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- The thesis model as the unequal-lengths model with full series `Tⱼ = T`. -/
def toUnequal [Nonempty T] : Unequal J T where
  toModel := M
  obs := fun _ => univ
  obs_nonempty := fun _ => univ_nonempty

omit [Fintype J] [DecidableEq J] in
lemma toUnequal_a [Nonempty T] : M.toUnequal.a = M.a := Unequal.a_eq_of_full _ fun _ => rfl

omit [Fintype J] [DecidableEq J] in
lemma toUnequal_σ2 [Nonempty T] : M.toUnequal.σ2 = M.σ2 := Unequal.σ2_eq_of_full _ fun _ => rfl

omit [Fintype J] in
lemma toUnequal_K [Nonempty T] : M.toUnequal.K = M.K := Unequal.K_eq_of_full _ fun _ => rfl

/-- Portfolio weights `bⱼ`. -/
noncomputable def b : J → ℝ := glsWeight M.K

/-- Portfolio error variance `s²`. -/
noncomputable def s2 : ℝ := (invTotal M.K)⁻¹

/-- The moments entering the blend for cohort `j` (§2.4): those of `Core` for this
model's `K`, `τ²` and `vⱼ = σ²ⱼⱼ` (`Var(μ̂ⱼ) = τ² + σ²ⱼⱼ`, `s²`, `cov(μ̂ⱼ, μ̂) = (K b)ⱼ`,
`cov(μ̂, μⱼ) = bⱼτ²`). -/
noncomputable def moments (j : J) : BlendMoments := Core.moments M.K M.τ2 (fun j => M.σ2 j j) j

/-- The six fields of `moments` in the model's own notation. -/
lemma moments_eq_mk (j : J) : M.moments j =
    { varCohort := M.τ2 + M.σ2 j j, varPortfolio := M.s2, varTarget := M.τ2,
      covEst := (M.K *ᵥ M.b) j, covCohortTarget := M.τ2,
      covPortfolioTarget := M.b j * M.τ2 } := rfl

lemma toUnequal_b [Nonempty T] : M.toUnequal.b = M.b := by rw [Unequal.b, toUnequal_K]; rfl

lemma toUnequal_s2 [Nonempty T] : M.toUnequal.s2 = M.s2 := by rw [Unequal.s2, toUnequal_K]; rfl

lemma toUnequal_moments [Nonempty T] : M.toUnequal.moments = M.moments := by
  funext j; rw [Unequal.moments, Model.moments, toUnequal_σ2, toUnequal_K]; rfl

omit [Fintype J] in
/-- A positive definite `K` (with some cohort) forces `T ≠ ∅`: otherwise `K = 0`. -/
lemma nonempty_of_posDef (hK : M.K.PosDef) (j : J) : Nonempty T := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hK.diag_pos (i := j)
  simp [K] at this

omit [Fintype J] in
/-- `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ`, as in eq. (27). -/
theorem K_apply [Nonempty T] (i j : J) :
    M.K i j = M.σ2 i j * M.ρ i j + M.τ2 * (if i = j then 1 else 0) := by
  rw [← toUnequal_K, Unequal.K_apply, toUnequal_σ2]; rfl

omit [Fintype J] in
theorem K_symm : M.Kᵀ = M.K := by
  rcases isEmpty_or_nonempty T with hT | hT
  · ext i j; simp [K]
  · simpa [toUnequal_K] using M.toUnequal.K_symm

/-- The thesis takes positive-definiteness of `K` for granted. Here it needs
the correlations to form a positive-semidefinite matrix, and `τ² > 0`. -/
theorem K_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) : M.K.PosDef :=
  M.toUnequal_K ▸ M.toUnequal.K_posDef_of_posSemidef hρ

/-- Eq. (22): the credibility factor for any linear model (17). -/
theorem bestZ_linear (j : J) :
    (M.moments j).bestZ
      = (M.s2 - (M.K *ᵥ M.b) j + M.τ2 - M.b j * M.τ2)
        / (M.s2 - 2 * (M.K *ᵥ M.b) j + M.τ2 + M.σ2 j j) := by
  simp only [BlendMoments.bestZ, BlendMoments.gap, moments_eq_mk]
  ring

/-- Eqs. (26)/(27): the proposed credibility factor at the optimal weights. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) :=
  Core.bestZ_eq hK j

/-- Eq. (26), second form: `zⱼ = cov(μ̂ⱼ - μ̂, μⱼ) / Var(μ̂ⱼ - μ̂)`. -/
theorem gap_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).gap = M.τ2 + M.σ2 j j - M.s2 :=
  Core.gap_eq hK j

/-! ### Equal covariances (new, answers the open question in Finding 4)

If every pair of cohorts has the same covariance `Kᵢⱼ = σ²ᵢⱼρᵢⱼ = c`, then
`K = diag(dⱼ) + c·11ᵀ` with `dⱼ = τ² + σ²ⱼⱼ - c`. The rank-one part lies along
`u`, so `K⁻¹u ∝ (1/dⱼ)` and the Bühlmann–Straub form `bⱼ = zⱼ/z*` survives for
any number of cohorts. Equal *correlations* are not enough when the `σⱼ` differ. -/

omit [Fintype J] in
/-- The diagonal of `K` is `τ² + σ²ⱼⱼ`. -/
lemma K_self [Nonempty T] (j : J) : M.K j j = M.τ2 + M.σ2 j j := by
  rw [M.K_apply, M.ρ_self]; simp [add_comm]

omit [Fintype J] in
/-- Under equal covariances, `Kᵢⱼ = c` off the diagonal. -/
lemma K_of_equalCov [Nonempty T] {c : ℝ} (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c)
    {i j : J} (h : i ≠ j) : M.K i j = c := by
  rw [M.K_apply, hc i j h]; simp [h]

/-- Under equal covariances, `K⁻¹u ∝ (1/dⱼ)` with `dⱼ = τ² + σ²ⱼⱼ - c`. -/
theorem Kinv_one_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) :
    let v := fun j => (M.τ2 + M.σ2 j j - c)⁻¹
    1 + c * ∑ i, v i ≠ 0 ∧ M.K⁻¹ *ᵥ 1 = (1 + c * ∑ i, v i)⁻¹ • v :=
  Core.Kinv_one_of_equalCov hK c (fun _ _ => M.K_of_equalCov hc) M.K_self hd

/-- Weights from credibility factors under equal covariances (new): if all
cohort pairs have the same covariance `σ²ᵢⱼρᵢⱼ = c`, then `bⱼ = zⱼ/z*` with
`zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, for any number of cohorts. -/
theorem b_eq_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) (j : J) :
    M.b j = M.τ2 / (M.τ2 + M.σ2 j j - c) / ∑ i, M.τ2 / (M.τ2 + M.σ2 i i - c) :=
  Core.b_eq_of_equalCov hK M.τ2_pos.ne' c (fun _ _ => M.K_of_equalCov hc) M.K_self hd j

/-- …and the proposed credibility factor is then `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`,
eq. (32) with `σ₁σ₂ρ` replaced by `c`. `bⱼ ≠ 1` rules out the `0/0` case. -/
theorem bestZ_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) (j : J)
    (hb : M.b j ≠ 1) :
    (M.moments j).bestZ = M.τ2 / (M.τ2 + M.σ2 j j - c) :=
  Core.bestZ_of_equalCov hK M.τ2_pos.ne' c (fun _ _ => M.K_of_equalCov hc) M.K_self hd j hb

end Model
end Credibility
