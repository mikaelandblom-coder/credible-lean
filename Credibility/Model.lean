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

/-- Finding 5, the converse for three cohorts: if the portfolio weights are the
credibility factors rescaled, `bⱼ = zⱼ/z*` for every `j`, and no weight is zero,
then all cohort pairs have the same covariance `σ²ᵢⱼρᵢⱼ = c`. Together with
`b_eq_of_equalCov`: for three cohorts with nonzero weights, weights follow from
factors exactly under equal covariances. -/
theorem equalCov_of_b_eq_z (M : Model (Fin 3) T) (hK : M.K.PosDef) (hb : ∀ j, M.b j ≠ 0)
    (hz : ∀ j, M.b j = (M.moments j).bestZ / ∑ i, (M.moments i).bestZ) :
    ∃ c, ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c := by
  have : Nonempty T := M.nonempty_of_posDef hK 0
  obtain ⟨c, hc⟩ := Core.equalCov_of_b_eq_z hK M.K_self hb hz
  exact ⟨c, fun i j h => by simpa [M.K_apply, h] using hc i j h⟩

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- With one period, `σ²ᵢⱼ = σᵢσⱼ`. -/
lemma σ2_of_unique [Unique T] (i j : J) :
    M.σ2 i j = M.σ i default * M.σ j default := by
  have h : ∀ k, M.a k default = 1 := fun k => by
    simp [a, invVarWeight, (M.σ_pos k default).ne']
  simp [σ2, h]

/-- Finding 4: for three or more cohorts the weights need not be the credibility
factors rescaled. Example: three cohorts, one period, `τ² = 1`, equal noise
`σⱼ = 1`, correlations `ρ₁₂ = 1/4`, `ρ₁₃ = ρ₂₃ = 0`; then `b ≠ z/z*`. -/
theorem exists_b_ne_z : ∃ M : Model (Fin 3) (Fin 1), (∀ j t, M.σ j t = 1) ∧ M.K.PosDef ∧
    ¬ ∀ j, M.b j = (M.moments j).bestZ / ∑ i, (M.moments i).bestZ := by
  let ρ : Fin 3 → Fin 3 → ℝ := fun i j =>
    if i = j then 1 else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 / 4 else 0
  let M : Model (Fin 3) (Fin 1) :=
    { τ2 := 1, σ := fun _ _ => 1, ρ := ρ, τ2_pos := one_pos, σ_pos := fun _ _ => one_pos,
      ρ_self := fun j => by simp [ρ],
      ρ_symm := fun i j => by fin_cases i <;> fin_cases j <;> simp [ρ] }
  have hρ : (Matrix.of M.ρ).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [M, ρ]
    · simp [M, ρ, dotProduct, mulVec, Fin.sum_univ_three]
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hK := M.K_posDef hρ
  have hKe : ∀ i j, M.K i j = M.ρ i j + if i = j then 1 else 0 := fun i j => by
    simp [M.K_apply, σ2_of_unique, M]
  refine ⟨M, fun _ _ => rfl, hK, fun hz => ?_⟩
  have hx : M.K *ᵥ ![4 / 9, 4 / 9, 1 / 2] = 1 := by
    ext i; simp only [mulVec, dotProduct, Fin.sum_univ_three, hKe]
    fin_cases i <;> simp [M, ρ] <;> norm_num
  have hb : ∀ j, M.b j ≠ 0 := fun j => by
    rw [b, Core.glsWeight_of_mulVec hK hx]; fin_cases j <;> simp [Fin.sum_univ_three] <;> norm_num
  obtain ⟨c, hc⟩ := M.equalCov_of_b_eq_z hK hb hz
  have h01 := hc 0 1 (by decide)
  have h02 := hc 0 2 (by decide)
  simp [σ2_of_unique, M, ρ] at h01 h02
  linarith

/-- Finding 4: equal correlations do not help when the noise levels differ.
Example: three cohorts, one period, `τ² = 1`, `σ = (1, 1, 2)`, every correlation
`ρᵢⱼ = 1/2`; then `b ≠ z/z*`. (With equal `σⱼ` too, the covariances are equal and
`b = z/z*` by `b_eq_of_equalCov`.) -/
theorem exists_b_ne_z_equalCorr : ∃ M : Model (Fin 3) (Fin 1),
    (∀ i j, i ≠ j → M.ρ i j = 1 / 2) ∧ M.K.PosDef ∧
    ¬ ∀ j, M.b j = (M.moments j).bestZ / ∑ i, (M.moments i).bestZ := by
  let ρ : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 1 / 2
  let σ : Fin 3 → Fin 1 → ℝ := fun j _ => if j = 2 then 2 else 1
  let M : Model (Fin 3) (Fin 1) :=
    { τ2 := 1, σ := σ, ρ := ρ, τ2_pos := one_pos,
      σ_pos := fun j _ => by fin_cases j <;> simp [σ],
      ρ_self := fun j => by simp [ρ],
      ρ_symm := fun i j => by fin_cases i <;> fin_cases j <;> simp [ρ] }
  have hρ : (Matrix.of M.ρ).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [M, ρ]
    · simp [M, ρ, dotProduct, mulVec, Fin.sum_univ_three]
      nlinarith [sq_nonneg (x 0 + x 1 + x 2), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hK := M.K_posDef hρ
  have hKe : ∀ i j, M.K i j = σ i 0 * σ j 0 * ρ i j + if i = j then 1 else 0 := fun i j => by
    simp [M.K_apply, σ2_of_unique, M]
  refine ⟨M, fun i j h => by simp [M, ρ, h], hK, fun hz => ?_⟩
  have hx : M.K *ᵥ ![8 / 21, 8 / 21, 1 / 21] = 1 := by
    ext i; simp only [mulVec, dotProduct, Fin.sum_univ_three, hKe]
    fin_cases i <;> simp [σ, ρ] <;> norm_num
  have hb : ∀ j, M.b j ≠ 0 := fun j => by
    rw [b, Core.glsWeight_of_mulVec hK hx]; fin_cases j <;> simp [Fin.sum_univ_three] <;> norm_num
  obtain ⟨c, hc⟩ := M.equalCov_of_b_eq_z hK hb hz
  have h01 := hc 0 1 (by decide)
  have h02 := hc 0 2 (by decide)
  simp [σ2_of_unique, M, σ, ρ] at h01 h02
  linarith

end Model
end Credibility
