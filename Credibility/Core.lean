import Credibility.Blend
import Credibility.Weights

/-!
# The credibility factor at the level of `K` (thesis §2.5, eqs. (24)–(26))

Everything here only needs the covariance matrix `K` of the cohort estimates,
the heterogeneity `τ²` and the cohort variances `vⱼ = σ²ⱼⱼ`, so that
`Var(μ̂ⱼ) = τ² + vⱼ` and `Kⱼⱼ = τ² + vⱼ`. The models (`Unequal`, and `Model` as
its case `Tⱼ = T`) build their own `K` and take these results as corollaries.
-/

open Finset Matrix

namespace Credibility
namespace Core

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {K : Matrix J J ℝ} {τ2 : ℝ} {v : J → ℝ}

/-- The moments entering the blend for cohort `j` (§2.4), with the GLS weights
`b` of `K` and `s² = 1/K⁻¹ₓₓ`. -/
noncomputable def moments (K : Matrix J J ℝ) (τ2 : ℝ) (v : J → ℝ) (j : J) : BlendMoments where
  varCohort := τ2 + v j
  varPortfolio := (invTotal K)⁻¹
  varTarget := τ2
  covEst := (K *ᵥ glsWeight K) j
  covCohortTarget := τ2
  covPortfolioTarget := glsWeight K j * τ2

/-! ### A general level covariance

The cohort levels may be correlated: `cov(μᵢ, μⱼ) = Lᵢⱼ` for a level covariance
matrix `L`. The thesis has `L = τ²I`; a shared level within groups
(`Hierarchical.lean`) has other `L`. Only `cov(μ̂ⱼ, μⱼ) = Lⱼⱼ` and
`cov(μ̂, μⱼ) = (L b)ⱼ` depend on it. -/

/-- The moments entering the blend for cohort `j` (§2.4) when the cohort
estimates have covariance `K`, the levels have covariance `L` and
`Var(μ̂ⱼ) = d` (`= Kⱼⱼ` in every model): the GLS weights `b` of `K`,
`s² = 1/K⁻¹ₓₓ`, `Var(μⱼ) = cov(μ̂ⱼ, μⱼ) = Lⱼⱼ` and `cov(μ̂, μⱼ) = (L b)ⱼ`. -/
noncomputable def levelMoments (K L : Matrix J J ℝ) (d : ℝ) (j : J) : BlendMoments where
  varCohort := d
  varPortfolio := (invTotal K)⁻¹
  varTarget := L j j
  covEst := (K *ᵥ glsWeight K) j
  covCohortTarget := L j j
  covPortfolioTarget := (L *ᵥ glsWeight K) j

/-- `Var(μ̂ⱼ - μ̂) = Var(μ̂ⱼ) - s²`, using `K b = s² u`. -/
theorem levelMoments_gap_eq (hK : K.PosDef) (L : Matrix J J ℝ) (d : ℝ) (j : J) :
    (levelMoments K L d j).gap = d - (invTotal K)⁻¹ := by
  simp only [BlendMoments.gap, levelMoments, mulVec_glsWeight hK]
  ring

/-- Eq. (26) for a general level covariance:
`zⱼ = (Lⱼⱼ - (L b)ⱼ) / (Var(μ̂ⱼ) - s²)`. -/
theorem levelMoments_bestZ_eq (hK : K.PosDef) (L : Matrix J J ℝ) (d : ℝ) (j : J) :
    (levelMoments K L d j).bestZ = (L j j - (L *ᵥ glsWeight K) j) / (d - (invTotal K)⁻¹) := by
  rw [BlendMoments.bestZ, levelMoments_gap_eq hK]
  simp only [levelMoments, mulVec_glsWeight hK]
  ring

/-- The thesis moments are the case `L = τ²I`, `d = τ² + vⱼ`. -/
theorem moments_eq_levelMoments (j : J) :
    moments K τ2 v j = levelMoments K (τ2 • (1 : Matrix J J ℝ)) (τ2 + v j) j := by
  simp only [moments, levelMoments, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply, Matrix.one_apply_eq, mul_one]
  rw [mul_comm]

/-- `Var(μ̂ⱼ - μ̂) = τ² + vⱼ - s²`, using `K b = s² u`. -/
theorem gap_eq (hK : K.PosDef) (j : J) :
    (moments K τ2 v j).gap = τ2 + v j - (invTotal K)⁻¹ := by
  rw [moments_eq_levelMoments, levelMoments_gap_eq hK]

/-- Eq. (26): `zⱼ = (1 - bⱼ) τ² / (τ² + vⱼ - s²)`. -/
theorem bestZ_eq (hK : K.PosDef) (j : J) :
    (moments K τ2 v j).bestZ = (1 - glsWeight K j) * τ2 / (τ2 + v j - (invTotal K)⁻¹) := by
  rw [moments_eq_levelMoments, levelMoments_bestZ_eq hK]
  simp only [smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
    Matrix.one_apply_eq, mul_one]
  ring

/-! ### Diagonal `K = diag(τ² + vⱼ)` -/

/-- For diagonal `K`, `K⁻¹u = (τ² + vⱼ)⁻¹`. -/
theorem Kinv_one_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, τ2 + v j ≠ 0) :
    K⁻¹ *ᵥ 1 = fun j => (τ2 + v j)⁻¹ := by
  have hinv : (diagonal fun j => τ2 + v j)⁻¹ = diagonal fun j => (τ2 + v j)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hd _), diagonal_one]
  rw [hK, hinv]
  ext j
  simp [mulVec_diagonal]

/-- For diagonal `K`, `bⱼ = (τ² + vⱼ)⁻¹ / Σᵢ (τ² + vᵢ)⁻¹`. -/
theorem b_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, τ2 + v j ≠ 0) (j : J) :
    glsWeight K j = (τ2 + v j)⁻¹ / ∑ i, (τ2 + v i)⁻¹ := by
  rw [glsWeight, invTotal, Kinv_one_of_diag hK hd, one_dotProduct]

/-- For diagonal `K` with positive entries and `J ≥ 2`, `zⱼ = τ²/(τ² + vⱼ)`. -/
theorem bestZ_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, 0 < τ2 + v j)
    (hJ : 1 < Fintype.card J) (j : J) :
    (moments K τ2 v j).bestZ = τ2 / (τ2 + v j) := by
  have hpd : K.PosDef := by rw [hK, posDef_diagonal_iff]; exact hd
  set V := ∑ i, (τ2 + v i)⁻¹
  have hs2 : (invTotal K)⁻¹ = V⁻¹ := by
    rw [invTotal, Kinv_one_of_diag hK fun j => (hd j).ne', one_dotProduct]
  -- `J ≥ 2`: `V > (τ² + vⱼ)⁻¹`, so there is no `0/0`.
  have hV : (τ2 + v j)⁻¹ < V := by
    obtain ⟨i, hij⟩ := Fintype.exists_ne_of_one_lt_card hJ j
    change _ < ∑ i, _
    rw [← add_sum_erase _ _ (mem_univ j)]
    exact lt_add_of_pos_right _
      (sum_pos (fun k _ => inv_pos.mpr (hd k)) ⟨i, mem_erase.mpr ⟨hij, mem_univ i⟩⟩)
  rw [bestZ_eq hpd, b_of_diag hK (fun j => (hd j).ne'), hs2,
    show ∑ x, (τ2 + v x)⁻¹ = V from rfl]
  have hdj := (hd j).ne'
  have hV0 : 0 < V := (inv_pos.mpr (hd j)).trans hV
  have hne : V - (τ2 + v j)⁻¹ ≠ 0 := (sub_pos.mpr hV).ne'
  have hne' : τ2 + v j - V⁻¹ ≠ 0 := by
    rw [show τ2 + v j - V⁻¹ = (τ2 + v j) * (V - (τ2 + v j)⁻¹) / V by field_simp]
    exact div_ne_zero (mul_ne_zero hdj hne) hV0.ne'
  rw [div_eq_div_iff hne' hdj]
  field_simp

/-! ### Equal covariances `K = diag(dⱼ) + c·11ᵀ`

If every pair of cohorts has the same covariance `Kᵢⱼ = c`, then
`K = diag(dⱼ) + c·11ᵀ` with `dⱼ = τ² + vⱼ - c`. The rank-one part lies along
`u`, so `K⁻¹u ∝ (1/dⱼ)` and the Bühlmann–Straub form `bⱼ = zⱼ/z*` survives for
any number of cohorts. -/

/-- Under equal covariances, `K⁻¹u ∝ (1/dⱼ)` with `dⱼ = τ² + vⱼ - c`. -/
theorem Kinv_one_of_equalCov (hK : K.PosDef) (c : ℝ) (hc : ∀ i j, i ≠ j → K i j = c)
    (hdiag : ∀ j, K j j = τ2 + v j) (hd : ∀ j, τ2 + v j ≠ c) :
    let w := fun j => (τ2 + v j - c)⁻¹
    1 + c * ∑ i, w i ≠ 0 ∧ K⁻¹ *ᵥ 1 = (1 + c * ∑ i, w i)⁻¹ • w := by
  intro w
  have hd' : ∀ j, τ2 + v j - c ≠ 0 := fun j => sub_ne_zero.mpr (hd j)
  -- `K = diag(d) + c·11ᵀ`, so `K w = (1 + c Σ w) u`.
  have hKw : K *ᵥ w = (1 + c * ∑ i, w i) • (1 : J → ℝ) := by
    ext i
    simp only [mulVec, dotProduct, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i), mul_add]
    have : ∀ k ∈ univ.erase i, K i k * w k = c * w k := fun k hk => by
      rw [hc i k (Ne.symm (mem_erase.mp hk).1)]
    rw [sum_congr rfl this, ← mul_sum, hdiag]
    simp only [w]
    field_simp [hd' i]
    ring
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit
  have hw : w = (1 + c * ∑ i, w i) • (K⁻¹ *ᵥ 1) := by
    rw [← mulVec_smul, ← hKw, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hne : 1 + c * ∑ i, w i ≠ 0 := by
    intro h0
    obtain ⟨j⟩ : Nonempty J := by
      by_contra hJ
      rw [not_nonempty_iff] at hJ
      simp at h0
    have := congrFun hw j
    rw [h0, zero_smul] at this
    exact inv_ne_zero (hd' j) this
  refine ⟨hne, ?_⟩
  rw [eq_inv_smul_iff₀ hne]; exact hw.symm

/-- Weights from credibility factors under equal covariances: `bⱼ = zⱼ/z*` with
`zⱼ = τ²/(τ² + vⱼ - c)`, for any number of cohorts. -/
theorem b_eq_of_equalCov (hK : K.PosDef) (hτ : τ2 ≠ 0) (c : ℝ)
    (hc : ∀ i j, i ≠ j → K i j = c) (hdiag : ∀ j, K j j = τ2 + v j)
    (hd : ∀ j, τ2 + v j ≠ c) (j : J) :
    glsWeight K j = τ2 / (τ2 + v j - c) / ∑ i, τ2 / (τ2 + v i - c) := by
  obtain ⟨hne, hinv⟩ := Kinv_one_of_equalCov hK c hc hdiag hd
  simp only [div_eq_mul_inv τ2, ← mul_sum]
  rw [mul_div_mul_left _ _ hτ, glsWeight, invTotal, hinv, dotProduct_smul,
    one_dotProduct, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ (inv_ne_zero hne)]

/-- …and then `zⱼ = τ²/(τ² + vⱼ - c)`, eq. (32) with `σ₁σ₂ρ` replaced by `c`.
`bⱼ ≠ 1` rules out the `0/0` case. -/
theorem bestZ_of_equalCov (hK : K.PosDef) (hτ : τ2 ≠ 0) (c : ℝ)
    (hc : ∀ i j, i ≠ j → K i j = c) (hdiag : ∀ j, K j j = τ2 + v j)
    (hd : ∀ j, τ2 + v j ≠ c) (j : J) (hb : glsWeight K j ≠ 1) :
    (moments K τ2 v j).bestZ = τ2 / (τ2 + v j - c) := by
  obtain ⟨hne, hinv⟩ := Kinv_one_of_equalCov hK c hc hdiag hd
  have : Nonempty J := ⟨j⟩
  set V := ∑ i, (τ2 + v i - c)⁻¹
  have htot : invTotal K = (1 + c * V)⁻¹ * V := by
    rw [invTotal, hinv, dotProduct_smul, one_dotProduct, smul_eq_mul]
  have hV : V ≠ 0 := by
    intro h0; have := invTotal_pos hK; rw [htot, h0, mul_zero] at this; exact lt_irrefl _ this
  have hbj : glsWeight K j = (τ2 + v j - c)⁻¹ / V := by
    rw [glsWeight, htot, hinv, Pi.smul_apply, smul_eq_mul,
      mul_div_mul_left _ _ (inv_ne_zero hne)]
  have hdj : τ2 + v j - c ≠ 0 := sub_ne_zero.mpr (hd j)
  -- `1 - bⱼ = (V - wⱼ)/V` and `τ² + vⱼ - s² = dⱼ - 1/V = (V - wⱼ)/(wⱼV)`.
  have hVv : V - (τ2 + v j - c)⁻¹ ≠ 0 := by
    intro h; apply hb; have := sub_eq_zero.mp h; rw [hbj, ← this, div_self hV]
  rw [bestZ_eq hK, htot, hbj]
  set d := τ2 + v j - c
  rw [show τ2 + v j = d + c by simp [d]]
  rw [show d + c - ((1 + c * V)⁻¹ * V)⁻¹ = (V - d⁻¹) * d / V by
      rw [mul_inv, inv_inv]; field_simp; ring,
    show 1 - d⁻¹ / V = (V - d⁻¹) / V by field_simp]
  have : V * d - 1 ≠ 0 := by
    intro h; apply hVv; field_simp; linarith
  field_simp

end Core
end Credibility
