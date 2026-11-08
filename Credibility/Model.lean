import Credibility.Blend
import Credibility.Weights

/-!
# The correlated data model and the proposed credibility factor
(thesis §2.3–2.5, eqs. (15)–(27))

`μⱼ = μ + τ ηⱼ` (cohort effect), `μⱼₜ = μⱼ + σⱼₜ εⱼₜ` (sampling noise),
`cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ`. The thesis writes the cohort effect `εⱼ`; it is
renamed `ηⱼ` here to keep it apart from the noise. Distribution-free: only
first and second moments are assumed.
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

omit [Fintype J] in
theorem K_symm : M.Kᵀ = M.K := by
  ext i j
  simp only [transpose_apply, K, obsCov]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  rw [M.ρ_symm j i]
  simp only [eq_comm (a := s), eq_comm (a := j)]
  ring

/-- The thesis takes positive-definiteness of `K` for granted. Here it needs
the correlations to form a positive-semidefinite matrix, and `τ² > 0`. -/
theorem K_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) : M.K.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, M.K_symm]
  -- `xᵀKx = Σₜ yₜᵀ R yₜ + τ²‖x‖²` with `(yₜ)ⱼ = aⱼₜ σⱼₜ xⱼ`.
  set y : T → J → ℝ := fun t j => M.a j t * M.σ j t * x j
  have key : star x ⬝ᵥ (M.K *ᵥ x)
      = ∑ t, star (y t) ⬝ᵥ (Matrix.of M.ρ *ᵥ y t) + M.τ2 * ∑ i, x i ^ 2 := by
    simp only [dotProduct, mulVec, M.K_apply, star_trivial, of_apply, y, σ2, add_mul,
      mul_add, sum_add_distrib, ite_mul, mul_ite, mul_one, mul_zero, zero_mul, sum_ite_eq,
      mem_univ, ite_true, mul_sum, sum_mul]
    congr 1
    · symm
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring
    · exact sum_congr rfl fun i _ => by ring
  rw [key]
  have h1 : 0 ≤ ∑ t, star (y t) ⬝ᵥ (Matrix.of M.ρ *ᵥ y t) :=
    sum_nonneg fun t _ => hρ.dotProduct_mulVec_nonneg (y t)
  have h2 : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩
  nlinarith [M.τ2_pos]

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
  simp only [BlendMoments.bestZ, BlendMoments.gap, moments]
  ring

/-- Eqs. (26)/(27): the proposed credibility factor at the optimal weights. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) := by
  -- `v = K b = s² u` (`mulVec_glsWeight`), substituted into eq. (22).
  have hv : (M.K *ᵥ M.b) j = M.s2 := by
    rw [b, mulVec_glsWeight hK, s2]
  rw [BlendMoments.bestZ, show (M.moments j).gap = M.τ2 + M.σ2 j j - M.s2 by
    simp only [BlendMoments.gap, moments, hv]; ring]
  simp only [moments, hv]
  ring

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
