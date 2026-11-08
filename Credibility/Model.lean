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

/-- The moments entering the blend for cohort `j` (§2.4). -/
noncomputable def moments (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := M.s2
  varTarget := M.τ2
  covEst := (M.K *ᵥ M.b) j
  covCohortTarget := M.τ2
  covPortfolioTarget := M.b j * M.τ2

lemma toUnequal_b [Nonempty T] : M.toUnequal.b = M.b := by rw [Unequal.b, toUnequal_K]; rfl

lemma toUnequal_s2 [Nonempty T] : M.toUnequal.s2 = M.s2 := by rw [Unequal.s2, toUnequal_K]; rfl

lemma toUnequal_moments [Nonempty T] : M.toUnequal.moments = M.moments := by
  funext j
  simp only [Unequal.moments, Model.moments, toUnequal_σ2, toUnequal_s2, toUnequal_K,
    toUnequal_b]
  rfl

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
  simp only [BlendMoments.bestZ, BlendMoments.gap, moments]
  ring

/-- Eqs. (26)/(27): the proposed credibility factor at the optimal weights. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) := by
  have := M.nonempty_of_posDef hK j
  rw [← M.toUnequal_moments, ← M.toUnequal_b, ← M.toUnequal_σ2, ← M.toUnequal_s2]
  exact M.toUnequal.bestZ_eq (M.toUnequal_K ▸ hK) j

/-- Eq. (26), second form: `zⱼ = cov(μ̂ⱼ - μ̂, μⱼ) / Var(μ̂ⱼ - μ̂)`. -/
theorem gap_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).gap = M.τ2 + M.σ2 j j - M.s2 := by
  have hv : (M.K *ᵥ M.b) j = M.s2 := by
    rw [b, mulVec_glsWeight hK, s2]
  simp only [BlendMoments.gap, moments, hv]
  ring

/-! ### Equal covariances (new, answers the open question in Finding 4)

If every pair of cohorts has the same covariance `Kᵢⱼ = σ²ᵢⱼρᵢⱼ = c`, then
`K = diag(dⱼ) + c·11ᵀ` with `dⱼ = τ² + σ²ⱼⱼ - c`. The rank-one part lies along
`u`, so `K⁻¹u ∝ (1/dⱼ)` and the Bühlmann–Straub form `bⱼ = zⱼ/z*` survives for
any number of cohorts. Equal *correlations* are not enough when the `σⱼ` differ. -/

/-- Under equal covariances, `K⁻¹u ∝ (1/dⱼ)` with `dⱼ = τ² + σ²ⱼⱼ - c`. -/
theorem Kinv_one_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) :
    let v := fun j => (M.τ2 + M.σ2 j j - c)⁻¹
    1 + c * ∑ i, v i ≠ 0 ∧ M.K⁻¹ *ᵥ 1 = (1 + c * ∑ i, v i)⁻¹ • v := by
  intro v
  have hd' : ∀ j, M.τ2 + M.σ2 j j - c ≠ 0 := fun j => sub_ne_zero.mpr (hd j)
  -- `K = diag(d) + c·11ᵀ`, so `K v = (1 + c Σ v) u`.
  have hKv : M.K *ᵥ v = (1 + c * ∑ i, v i) • (1 : J → ℝ) := by
    ext i
    simp only [mulVec, dotProduct, M.K_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
      mul_one]
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i), mul_add]
    have : ∀ k ∈ univ.erase i,
        (M.σ2 i k * M.ρ i k + M.τ2 * if i = k then 1 else 0) * v k = c * v k := by
      intro k hk
      have hik : i ≠ k := (Ne.symm (mem_erase.mp hk).1)
      rw [hc i k hik]; simp [hik]
    rw [sum_congr rfl this, ← mul_sum, M.ρ_self]
    simp only [↓reduceIte]
    simp only [v]
    field_simp [hd' i]
    ring
  have hdet : IsUnit M.K.det := (Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit
  have hv : v = (1 + c * ∑ i, v i) • (M.K⁻¹ *ᵥ 1) := by
    rw [← mulVec_smul, ← hKv, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hne : 1 + c * ∑ i, v i ≠ 0 := by
    intro h0
    obtain ⟨j⟩ : Nonempty J := by
      by_contra hJ
      rw [not_nonempty_iff] at hJ
      simp at h0
    have := congrFun hv j
    rw [h0, zero_smul] at this
    exact inv_ne_zero (hd' j) this
  refine ⟨hne, ?_⟩
  rw [eq_inv_smul_iff₀ hne]; exact hv.symm

/-- Weights from credibility factors under equal covariances (new): if all
cohort pairs have the same covariance `σ²ᵢⱼρᵢⱼ = c`, then `bⱼ = zⱼ/z*` with
`zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, for any number of cohorts. -/
theorem b_eq_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) (j : J) :
    M.b j = M.τ2 / (M.τ2 + M.σ2 j j - c) / ∑ i, M.τ2 / (M.τ2 + M.σ2 i i - c) := by
  obtain ⟨hne, hinv⟩ := M.Kinv_one_of_equalCov hK c hc hd
  simp only [div_eq_mul_inv M.τ2, ← mul_sum]
  rw [mul_div_mul_left _ _ M.τ2_pos.ne', b, glsWeight, invTotal, hinv, dotProduct_smul,
    one_dotProduct, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ (inv_ne_zero hne)]


/-- …and the proposed credibility factor is then `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`,
eq. (32) with `σ₁σ₂ρ` replaced by `c`. `bⱼ ≠ 1` rules out the `0/0` case. -/
theorem bestZ_of_equalCov [Nonempty T] (hK : M.K.PosDef) (c : ℝ)
    (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) (hd : ∀ j, M.τ2 + M.σ2 j j ≠ c) (j : J)
    (hb : M.b j ≠ 1) :
    (M.moments j).bestZ = M.τ2 / (M.τ2 + M.σ2 j j - c) := by
  obtain ⟨hne, hinv⟩ := M.Kinv_one_of_equalCov hK c hc hd
  have : Nonempty J := ⟨j⟩
  set V := ∑ i, (M.τ2 + M.σ2 i i - c)⁻¹
  have htot : invTotal M.K = (1 + c * V)⁻¹ * V := by
    rw [invTotal, hinv, dotProduct_smul, one_dotProduct, smul_eq_mul]
  have hV : V ≠ 0 := by
    intro h0; have := invTotal_pos hK; rw [htot, h0, mul_zero] at this; exact lt_irrefl _ this
  have hbj : M.b j = (M.τ2 + M.σ2 j j - c)⁻¹ / V := by
    rw [b, glsWeight, htot, hinv, Pi.smul_apply, smul_eq_mul,
      mul_div_mul_left _ _ (inv_ne_zero hne)]
  have hdj : M.τ2 + M.σ2 j j - c ≠ 0 := sub_ne_zero.mpr (hd j)
  -- `1 - bⱼ = (V - vⱼ)/V` and `τ² + σ²ⱼⱼ - s² = dⱼ - 1/V = (V - vⱼ)/(vⱼV)`.
  have hVv : V - (M.τ2 + M.σ2 j j - c)⁻¹ ≠ 0 := by
    intro h; apply hb; have := sub_eq_zero.mp h; rw [hbj, ← this, div_self hV]
  rw [M.bestZ_eq hK, Model.s2, htot, hbj]
  set d := M.τ2 + M.σ2 j j - c
  rw [show M.τ2 + M.σ2 j j = d + c by simp [d]]
  have hτ := M.τ2_pos.ne'
  rw [show d + c - ((1 + c * V)⁻¹ * V)⁻¹ = (V - d⁻¹) * d / V by
      rw [mul_inv, inv_inv]; field_simp; ring,
    show 1 - d⁻¹ / V = (V - d⁻¹) / V by field_simp]
  have : V * d - 1 ≠ 0 := by
    intro h; apply hVv; field_simp; linarith
  field_simp

end Model
end Credibility
