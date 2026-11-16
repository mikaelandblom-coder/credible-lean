import Mathlib
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

/-- `Var(μ̂ⱼ - μ̂) = (eⱼ - b)ᵀ K (eⱼ - b)`: the gap variance as a quadratic form
in the weights of `μ̂ⱼ - μ̂`. -/
theorem quadForm_single_sub_glsWeight [Nonempty J] (hK : K.PosDef) (j : J) :
    (Pi.single j 1 - glsWeight K) ⬝ᵥ (K *ᵥ (Pi.single j 1 - glsWeight K))
      = K j j - (invTotal K)⁻¹ := by
  -- `K(eⱼ - b) = Kₓⱼ - s²·1`; `eⱼ ⬝ Kₓⱼ = Kⱼⱼ`, `b ⬝ Kₓⱼ = (Kb)ⱼ = s²`, `(eⱼ - b) ⬝ 1 = 0`.
  have hs : ∑ i, glsWeight K i * K i j = (invTotal K)⁻¹ := by
    have h := congrFun (mulVec_glsWeight hK) j
    simp only [mulVec, dotProduct] at h
    rw [← h]; refine sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← hK.isHermitian.apply i j]; simp
  rw [mulVec_sub, mulVec_glsWeight hK]
  simp only [dotProduct, Pi.sub_apply, mulVec_single, sub_mul, mul_sub, sum_sub_distrib,
    Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, ← sum_mul,
    sum_glsWeight hK]
  simp [Matrix.col]
  exact hs

/-- Finding 17: the own-data weight is bounded. If `xᵀKx ≥ m‖x‖²` for all `x`
(e.g. `m = λ_min(K)`), then `|zⱼ| ‖eⱼ - b‖ ≤ τ²/m`. The blend
`zⱼμ̂ⱼ + (1 - zⱼ)μ̂ = μ̂ + zⱼ(eⱼ - b)·μ̂` therefore has bounded coefficients, in
particular `cⱼ = bⱼ + zⱼ(1 - bⱼ)`, even where `zⱼ` is large. The proof:
`zⱼ = (1 - bⱼ)τ²/Var(gap)`, `|1 - bⱼ| ≤ ‖eⱼ - b‖` and
`Var(gap) = (eⱼ - b)ᵀK(eⱼ - b) ≥ m‖eⱼ - b‖²`. -/
theorem abs_bestZ_mul_norm_le [Nonempty J] (hK : K.PosDef) (hτ : 0 ≤ τ2) {m : ℝ} (hm : 0 < m)
    (hRay : ∀ x : J → ℝ, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (K *ᵥ x)) (j : J) (hKjj : K j j = τ2 + v j) :
    |(moments K τ2 v j).bestZ| * √((Pi.single j 1 - glsWeight K) ⬝ᵥ (Pi.single j 1 - glsWeight K))
      ≤ τ2 / m := by
  set x := Pi.single j 1 - glsWeight K with hx
  have hxj : x j = 1 - glsWeight K j := by simp [hx]
  set n := x ⬝ᵥ x
  have hn : 0 ≤ n := by simp only [n, dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _
  -- `(1 - bⱼ)² ≤ ‖x‖²`
  have hxj2 : x j ^ 2 ≤ n := by
    simp only [n, dotProduct, ← sq]
    exact single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (mem_univ j)
  have hg : τ2 + v j - (invTotal K)⁻¹ = x ⬝ᵥ (K *ᵥ x) := by
    rw [hx, quadForm_single_sub_glsWeight hK, hKjj]
  rw [bestZ_eq hK, hg, ← hxj]
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, mul_zero]; positivity
  have hq : m * n ≤ x ⬝ᵥ (K *ᵥ x) := hRay x
  have hqpos : 0 < x ⬝ᵥ (K *ᵥ x) := lt_of_lt_of_le (mul_pos hm hpos) hq
  -- `|x j| τ² √n / q ≤ τ² n / (m n)` since `|x j| ≤ √n` and `q ≥ m n`.
  have hab : |x j| ≤ √n := Real.abs_le_sqrt hxj2
  rw [abs_div, abs_mul, abs_of_nonneg hτ, abs_of_pos hqpos, div_mul_eq_mul_div,
    div_le_div_iff₀ hqpos hm]
  calc |x j| * τ2 * √n * m ≤ √n * τ2 * √n * m := by gcongr
    _ = τ2 * (m * n) := by rw [mul_comm √n τ2, mul_assoc τ2, Real.mul_self_sqrt hn]; ring
    _ ≤ τ2 * x ⬝ᵥ (K *ᵥ x) := by gcongr

/-- Finding 17: the own-data weight `cⱼ = bⱼ + zⱼ(1 - bⱼ)`, the coefficient of
`μ̂ⱼ` in the blend, stays within `τ²/m` of `bⱼ`: `|zⱼ(1 - bⱼ)| ≤ τ²/m` whenever
`xᵀKx ≥ m‖x‖²`, since `|1 - bⱼ| ≤ ‖eⱼ - b‖`. -/
theorem abs_bestZ_mul_one_sub_le [Nonempty J] (hK : K.PosDef) (hτ : 0 ≤ τ2) {m : ℝ} (hm : 0 < m)
    (hRay : ∀ x : J → ℝ, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (K *ᵥ x)) (j : J) (hKjj : K j j = τ2 + v j) :
    |(moments K τ2 v j).bestZ * (1 - glsWeight K j)| ≤ τ2 / m := by
  set x := Pi.single j 1 - glsWeight K with hx
  have hxj : x j = 1 - glsWeight K j := by simp [hx]
  have hxj2 : x j ^ 2 ≤ x ⬝ᵥ x := by
    simp only [dotProduct, ← sq]
    exact single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (mem_univ j)
  rw [abs_mul, ← hxj]
  exact (mul_le_mul_of_nonneg_left (Real.abs_le_sqrt hxj2) (abs_nonneg _)).trans
    (abs_bestZ_mul_norm_le hK hτ hm hRay j hKjj)

/-! ### Solving `K x = 1` -/

/-- If `K` is invertible and `K w = c·1` with `c ≠ 0`, then `K⁻¹1 = c⁻¹ w`. Every
closed form for the GLS weights below comes from guessing such a `w`. -/
theorem Kinv_one_eq_of_mulVec (hK : IsUnit K.det) {w : J → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hw : K *ᵥ w = c • 1) : K⁻¹ *ᵥ 1 = c⁻¹ • w := by
  rw [eq_inv_smul_iff₀ hc, ← mulVec_smul, ← hw, mulVec_mulVec, nonsing_inv_mul _ hK, one_mulVec]

/-! ### Diagonal `K = diag(τ² + vⱼ)` -/

/-- For diagonal `K`, `K⁻¹u = (τ² + vⱼ)⁻¹`. -/
theorem Kinv_one_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, τ2 + v j ≠ 0) :
    K⁻¹ *ᵥ 1 = fun j => (τ2 + v j)⁻¹ := by
  have hdet : IsUnit K.det := by
    rw [hK, det_diagonal]; exact (Finset.prod_ne_zero_iff.mpr fun j _ => hd j).isUnit
  rw [Kinv_one_eq_of_mulVec hdet one_ne_zero (w := fun j => (τ2 + v j)⁻¹), inv_one, one_smul]
  ext j
  simp [hK, mulVec_diagonal, hd j]

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
  -- `1 + c Σ w = 0` would give `K w = 0`, so `w = 0`, but `wⱼ ≠ 0`.
  have hne : 1 + c * ∑ i, w i ≠ 0 := by
    intro h0
    obtain ⟨j⟩ : Nonempty J := by
      by_contra hJ
      rw [not_nonempty_iff] at hJ
      simp at h0
    have h := congrArg (K⁻¹ *ᵥ ·) hKw
    simp only [h0, zero_smul, mulVec_zero, mulVec_mulVec, nonsing_inv_mul _ hdet,
      one_mulVec] at h
    exact inv_ne_zero (hd' j) (congrFun h j)
  exact ⟨hne, Kinv_one_eq_of_mulVec hdet hne hKw⟩

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

/-! ### A rank-one term along `1` -/

section RankOne

/-- If `K` and `K + c·11ᵀ` are positive definite, then
`(K + c·11ᵀ)⁻¹1 = K⁻¹1 / (1 + c·1ᵀK⁻¹1)`, with `1 + c·1ᵀK⁻¹1 > 0`:
`(K + c·11ᵀ) K⁻¹1 = (1 + c·1ᵀK⁻¹1)·1`. -/
theorem Kinv_one_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    0 < 1 + c * invTotal K ∧
      (K + c • vecMulVec 1 1)⁻¹ *ᵥ 1 = (1 + c * invTotal K)⁻¹ • (K⁻¹ *ᵥ 1) := by
  set w := K⁻¹ *ᵥ 1
  set S := invTotal K
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).mp hK'.isUnit
  have hKw : (K + c • vecMulVec 1 1) *ᵥ w = (1 + c * S) • (1 : J → ℝ) := by
    rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, mulVec_mulVec, mul_nonsing_inv K hdet,
      one_mulVec]
    ext i; simp [S, invTotal, w]
  -- `wᵀ(K + c·11ᵀ)w = (1 + cS)·S > 0` with `S > 0`.
  have hpos : 0 < 1 + c * S := by
    rcases isEmpty_or_nonempty J with hJ | hJ
    · simp [S, invTotal]
    have hS : 0 < S := invTotal_pos hK
    have hw0 : w ≠ 0 := by
      intro h0
      have : S = 0 := by
        simp only [S, invTotal]; rw [show K⁻¹ *ᵥ 1 = w from rfl, h0, dotProduct_zero]
      linarith
    have := hK'.dotProduct_mulVec_pos hw0
    rw [star_trivial, hKw, dotProduct_smul, dotProduct_one, smul_eq_mul] at this
    have hS' : ∑ i, w i = S := by simp [S, invTotal, w, one_dotProduct]
    rw [hS'] at this
    exact pos_of_mul_pos_left this hS.le
  exact ⟨hpos, Kinv_one_eq_of_mulVec hdet' hpos.ne' hKw⟩

/-- A rank-one term along `1` does not change the GLS weights:
`b(K + c·11ᵀ) = b(K)`, since `(K + c·11ᵀ)⁻¹1 ∝ K⁻¹1`. -/
theorem glsWeight_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    glsWeight (K + c • vecMulVec 1 1) = glsWeight K := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  ext j
  rw [glsWeight, glsWeight, invTotal, hinv, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_div_mul_left _ _ (inv_ne_zero hpos.ne'), invTotal]

/-- …and it adds `c` to the portfolio variance: `s²(K + c·11ᵀ) = s²(K) + c`. -/
theorem invTotal_inv_add_rankOne [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    (invTotal (K + c • vecMulVec 1 1))⁻¹ = (invTotal K)⁻¹ + c := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  have hS := (invTotal_pos hK).ne'
  rw [invTotal, hinv, dotProduct_smul, smul_eq_mul, ← invTotal]
  field_simp

end RankOne

/-! ### Balance (§2.9) for any blend

The blend `μ̂ⱼᵇ = zⱼμ̂ⱼ + (1 - zⱼ)Σᵢbᵢμ̂ᵢ` is balanced for weights `u` if
`Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = 0` for all data. Pure algebra: it holds exactly when
`uⱼ(1 - zⱼ) ∝ bⱼ`. -/

section Balance

/-- The blend `μ̂ⱼᵇ = zⱼμ̂ⱼ + (1 - zⱼ)Σᵢbᵢμ̂ᵢ` is balanced for the weights `u`:
`Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = 0` for every data vector `μ̂`. -/
def Balanced (u z b : J → ℝ) : Prop :=
  ∀ m : J → ℝ, ∑ j, u j * (m j - (z j * m j + (1 - z j) * ∑ i, b i * m i)) = 0

omit [DecidableEq J] in
/-- `μ̂ⱼ - μ̂ⱼᵇ = (1 - zⱼ)(μ̂ⱼ - μ̂)` with `μ̂ = Σᵢbᵢμ̂ᵢ`. -/
theorem sum_mul_sub_blend (u z b m : J → ℝ) :
    ∑ j, u j * (m j - (z j * m j + (1 - z j) * ∑ i, b i * m i))
      = ∑ j, u j * (1 - z j) * (m j - ∑ i, b i * m i) :=
  sum_congr rfl fun j _ => by ring

omit [DecidableEq J] in
/-- Balance for any blend: with `Σbⱼ = 1`, the blend is balanced for the weights `u`
iff `uⱼ(1 - zⱼ) = c·bⱼ` for some `c`. -/
theorem balanced_iff (u z b : J → ℝ) (hb : ∑ j, b j = 1) :
    Balanced u z b ↔ ∃ c, ∀ j, u j * (1 - z j) = c * b j := by
  set a := fun j => u j * (1 - z j)
  -- `Σⱼ aⱼ(μ̂ⱼ - Σᵢbᵢμ̂ᵢ) = Σⱼ (aⱼ - (Σa) bⱼ) μ̂ⱼ`: zero for all `μ̂` iff each coefficient is.
  have key : ∀ m : J → ℝ, ∑ j, u j * (m j - (z j * m j + (1 - z j) * ∑ i, b i * m i))
      = ∑ j, (a j - (∑ i, a i) * b j) * m j := by
    intro m
    rw [sum_mul_sub_blend]
    simp only [a, mul_sub, sub_mul, sum_sub_distrib, ← sum_mul, mul_assoc, ← mul_sum]
    rw [sum_mul univ (fun x => u x * z x)]; simp only [mul_assoc]
  simp only [Balanced, key]
  constructor
  · classical
    intro h
    refine ⟨∑ i, a i, fun j => ?_⟩
    have := h (Pi.single j 1)
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ite_true] at this
    exact sub_eq_zero.mp this
  · rintro ⟨c, hc⟩ m
    have hA : ∑ i, a i = c := by
      simp only [a, hc, ← mul_sum, hb, mul_one]
    refine sum_eq_zero fun j _ => ?_
    rw [hA]; simp only [a, hc, sub_self, zero_mul]

/-- With a diagonal `K = diag(τ² + vⱼ)`, `vⱼ ≠ 0` and the optimal `z` and `b`, the blend
is balanced exactly for weights `uⱼ ∝ 1/(Kⱼⱼ - τ²) = 1/vⱼ`, the precisions of the noise. -/
theorem balanced_iff_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, 0 < τ2 + v j)
    (hv : ∀ j, v j ≠ 0) (hJ : 1 < Fintype.card J) (u : J → ℝ) :
    Balanced u (fun j => (moments K τ2 v j).bestZ) (glsWeight K) ↔
      ∃ c, ∀ j, u j = c / (K j j - τ2) := by
  have hpd : K.PosDef := by rw [hK, posDef_diagonal_iff]; exact hd
  have : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  set V := ∑ i, (τ2 + v i)⁻¹
  have hV : 0 < V := sum_pos (fun i _ => inv_pos.mpr (hd i)) univ_nonempty
  rw [balanced_iff _ _ _ (sum_glsWeight hpd)]
  have hKjj : ∀ j, K j j - τ2 = v j := fun j => by rw [hK]; simp
  simp only [bestZ_of_diag hK hd hJ, b_of_diag hK (fun j => (hd j).ne'), hKjj]
  -- `uⱼ(1 - zⱼ) = uⱼvⱼ/(τ² + vⱼ)` and `bⱼ = (τ² + vⱼ)⁻¹/V`: both sides say `uⱼvⱼ` is constant.
  have h : ∀ j (c : ℝ), u j * (1 - τ2 / (τ2 + v j)) = c * ((τ2 + v j)⁻¹ / V) ↔
      u j = c / V / v j := fun j c => by
    have := (hd j).ne'; have := hv j
    rw [eq_div_iff (hv j)]
    constructor <;> intro h
    · field_simp at h ⊢; linarith
    · field_simp; field_simp at h; linarith
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c / V, fun j => (h j c).mp (hc j)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c * V, fun j => (h j _).mpr (by rw [hc j, mul_div_cancel_right₀ _ hV.ne'])⟩

/-! ### The best balanced blend (PLAN G7)

With `uⱼ ≠ 0`, `balanced_iff` says the balanced blends form a line: `zⱼ = 1 - c·bⱼ/uⱼ`.
Each cohort's error variance is a parabola `gapⱼ(zⱼ - zⱼ*)²` above its optimum
(`errVar_eq`), so the best balanced blend for the loss `Σⱼ φⱼ MSEⱼ` is a weighted least
squares fit in the one number `c`. -/

/-- The balanced credibility factors `zⱼ = 1 - c·bⱼ/uⱼ`. -/
noncomputable def balancedZ (u b : J → ℝ) (c : ℝ) (j : J) : ℝ := 1 - c * b j / u j

omit [DecidableEq J] in
/-- With `Σbⱼ = 1` and `uⱼ ≠ 0`, the balanced blends are exactly `zⱼ = 1 - c·bⱼ/uⱼ`. -/
theorem balanced_iff_balancedZ (u z b : J → ℝ) (hb : ∑ j, b j = 1) (hu : ∀ j, u j ≠ 0) :
    Balanced u z b ↔ ∃ c, z = balancedZ u b c := by
  rw [balanced_iff u z b hb]
  refine exists_congr fun c => ⟨fun h => funext fun j => ?_, fun h j => ?_⟩
  · rw [balancedZ, ← h j]; field_simp [hu j]; ring
  · rw [h, balancedZ]; field_simp [hu j]; ring

/-- The best `c` for the loss weights `φ`: with `aⱼ = bⱼ/uⱼ` and `gⱼ = Var(μ̂ⱼ - μ̂)`,
`c* = Σφⱼgⱼ(1 - zⱼ*)aⱼ / Σφⱼgⱼaⱼ²`. -/
noncomputable def bestBalancedC (φ u b : J → ℝ) (m : J → BlendMoments) : ℝ :=
  (∑ j, φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j)) /
    ∑ j, φ j * (m j).gap * (b j / u j) ^ 2

omit [DecidableEq J] in
/-- The total loss along the balanced line: `Σφⱼ MSEⱼ(z*) + S₀ - 2cS₁ + c²S₂`. -/
theorem sum_errVar_balancedZ (φ u b : J → ℝ) (m : J → BlendMoments)
    (hg : ∀ j, (m j).gap ≠ 0) (c : ℝ) :
    ∑ j, φ j * (m j).errVar (balancedZ u b c j)
      = ∑ j, φ j * (m j).errVar (m j).bestZ
        + ∑ j, φ j * (m j).gap * (1 - (m j).bestZ) ^ 2
        - 2 * c * ∑ j, φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j)
        + c ^ 2 * ∑ j, φ j * (m j).gap * (b j / u j) ^ 2 := by
  calc ∑ j, φ j * (m j).errVar (balancedZ u b c j)
      = ∑ j, (φ j * (m j).errVar (m j).bestZ + φ j * (m j).gap * (1 - (m j).bestZ) ^ 2
          - 2 * c * (φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j))
          + c ^ 2 * (φ j * (m j).gap * (b j / u j) ^ 2)) :=
        sum_congr rfl fun j _ => by rw [(m j).errVar_eq (hg j), balancedZ]; ring
    _ = _ := by simp only [sum_add_distrib, sum_sub_distrib, mul_sum]

omit [DecidableEq J] in
/-- `S₂c* = S₁`, also when `S₂ = 0` (then every term of `S₁` vanishes). -/
theorem mul_bestBalancedC (φ u b : J → ℝ) (m : J → BlendMoments) (hφ : ∀ j, 0 ≤ φ j)
    (hg : ∀ j, 0 < (m j).gap) :
    (∑ j, φ j * (m j).gap * (b j / u j) ^ 2) * bestBalancedC φ u b m
      = ∑ j, φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j) := by
  by_cases h : ∑ j, φ j * (m j).gap * (b j / u j) ^ 2 = 0
  · have hj := (sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hφ j) (hg j).le) (sq_nonneg (b j / u j))).mp h
    rw [h, zero_mul]
    refine (sum_eq_zero fun j _ => ?_).symm
    rcases mul_eq_zero.mp (hj j (mem_univ j)) with h0 | h0
    · rw [show φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j)
          = φ j * (m j).gap * ((1 - (m j).bestZ) * (b j / u j)) by ring, h0, zero_mul]
    · rw [pow_eq_zero_iff two_ne_zero |>.mp h0, mul_zero]
  · rw [bestBalancedC, mul_div_cancel₀ _ h]

omit [DecidableEq J] in
/-- **The best balanced blend** (PLAN G7). Among all blends `zⱼμ̂ⱼ + (1 - zⱼ)Σᵢbᵢμ̂ᵢ`
with `Σbⱼ = 1` that are balanced for the weights `uⱼ ≠ 0`, the factors
`zⱼ = 1 - c*·bⱼ/uⱼ` with `c* = bestBalancedC` are balanced and minimise the weighted
loss `Σⱼ φⱼ MSEⱼ(zⱼ)` (`φⱼ ≥ 0`, each `Var(μ̂ⱼ - μ̂) > 0`). The moments `m j` are
arbitrary, so correlated cohorts are covered. -/
theorem bestBalanced_optimal (φ u b : J → ℝ) (m : J → BlendMoments) (hb : ∑ j, b j = 1)
    (hu : ∀ j, u j ≠ 0) (hφ : ∀ j, 0 ≤ φ j) (hg : ∀ j, 0 < (m j).gap) :
    Balanced u (balancedZ u b (bestBalancedC φ u b m)) b ∧
      ∀ z, Balanced u z b →
        ∑ j, φ j * (m j).errVar (balancedZ u b (bestBalancedC φ u b m) j)
          ≤ ∑ j, φ j * (m j).errVar (z j) := by
  refine ⟨(balanced_iff_balancedZ _ _ _ hb hu).mpr ⟨_, rfl⟩, fun z hz => ?_⟩
  obtain ⟨c, rfl⟩ := (balanced_iff_balancedZ _ _ _ hb hu).mp hz
  have hg0 : ∀ j, (m j).gap ≠ 0 := fun j => (hg j).ne'
  rw [sum_errVar_balancedZ φ u b m hg0, sum_errVar_balancedZ φ u b m hg0]
  have hS := mul_bestBalancedC φ u b m hφ hg
  have hS2 : 0 ≤ ∑ j, φ j * (m j).gap * (b j / u j) ^ 2 := sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hφ j) (hg j).le) (sq_nonneg _)
  -- The difference is `S₂(c - c*)² ≥ 0`.
  rw [← hS]
  nlinarith [mul_nonneg hS2 (sq_nonneg (c - bestBalancedC φ u b m))]

omit [DecidableEq J] in
/-- **The cost of balance**: when `S₂ = Σφⱼgⱼ(bⱼ/uⱼ)² ≠ 0`, the best balanced blend loses
`S₀ - S₁²/S₂` against the unconstrained optimum, with `S₀ = Σφⱼgⱼ(1 - zⱼ*)²` and
`S₁ = Σφⱼgⱼ(1 - zⱼ*)bⱼ/uⱼ`. By Cauchy–Schwarz this is `≥ 0`, and it is `0` exactly
when the optimal blend is itself balanced. -/
theorem bestBalanced_cost (φ u b : J → ℝ) (m : J → BlendMoments) (hg : ∀ j, (m j).gap ≠ 0)
    (hS2 : ∑ j, φ j * (m j).gap * (b j / u j) ^ 2 ≠ 0) :
    ∑ j, φ j * (m j).errVar (balancedZ u b (bestBalancedC φ u b m) j)
      = ∑ j, φ j * (m j).errVar (m j).bestZ
        + (∑ j, φ j * (m j).gap * (1 - (m j).bestZ) ^ 2
          - (∑ j, φ j * (m j).gap * (1 - (m j).bestZ) * (b j / u j)) ^ 2
            / ∑ j, φ j * (m j).gap * (b j / u j) ^ 2) := by
  rw [sum_errVar_balancedZ φ u b m hg, bestBalancedC]
  have := hS2
  field_simp
  ring

/-! ### The best balanced correction (PLAN G7b, Wang–Fuller–Qu)

Keep any blend `μ̂ⱼᵇ` and correct it by a multiple of its imbalance
`D = Σᵢ uᵢ(μ̂ᵢ - μ̂ᵢᵇ)`: `θ̂ⱼ = μ̂ⱼᵇ + cⱼD`. Then `Σⱼ uⱼ(μ̂ⱼ - θ̂ⱼ) = (1 - Σⱼ uⱼcⱼ)D`, so the
corrections are balanced exactly when `Σⱼ uⱼcⱼ = 1`. With `κⱼ = cov(μ̂ⱼᵇ - μⱼ, D)` and
`V = Var D`, the error of `θ̂ⱼ` is the parabola `MSEⱼ + 2cⱼκⱼ + cⱼ²V` in `cⱼ`
(`Estimates.mse_correct`), so the best `c` for the loss `Σⱼ φⱼ MSE(θ̂ⱼ)` is a least squares
problem under one linear constraint (Wang, Fuller and Qu 2008). The common shift
`cⱼ = 1/Σᵢuᵢ` is its solution for `φ = u` exactly when `κⱼ` is the same for all `j`; this
holds for independent cohorts (`imbalanceCov_of_diag`) but not under correlation
(Finding 16). -/

/-- The imbalance `D = Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ)` as a linear combination `Σᵢ wᵢμ̂ᵢ`:
`wᵢ = uᵢ(1 - zᵢ) - (Σⱼ uⱼ(1 - zⱼ)) bᵢ`. -/
def imbalanceWeight (u z b : J → ℝ) (i : J) : ℝ :=
  u i * (1 - z i) - (∑ j, u j * (1 - z j)) * b i

omit [DecidableEq J] in
/-- `Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = Σᵢ wᵢμ̂ᵢ` for every data vector `μ̂`. -/
theorem sum_mul_sub_blend_eq (u z b m : J → ℝ) :
    ∑ j, u j * (m j - (z j * m j + (1 - z j) * ∑ i, b i * m i))
      = ∑ i, imbalanceWeight u z b i * m i := by
  rw [sum_mul_sub_blend]
  calc _ = ∑ j, (u j * (1 - z j) * m j - u j * (1 - z j) * ∑ i, b i * m i) :=
        sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [sum_sub_distrib, ← sum_mul]
      simp only [imbalanceWeight, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]

omit [DecidableEq J] in
/-- With `Σbⱼ = 1` the imbalance weights sum to zero, so `E D = 0`. -/
theorem sum_imbalanceWeight (u z b : J → ℝ) (hb : ∑ j, b j = 1) :
    ∑ i, imbalanceWeight u z b i = 0 := by
  simp only [imbalanceWeight, sum_sub_distrib, ← mul_sum, hb, mul_one, sub_self]

/-- `κⱼ = cov(μ̂ⱼᵇ - μⱼ, D)` for `D = Σᵢ wᵢμ̂ᵢ`: `zⱼ(Kw)ⱼ - (Lw)ⱼ`. The portfolio estimate
does not appear: with GLS weights `cov(μ̂, D) = s²Σᵢwᵢ = 0`. -/
def imbalanceCov (K L : Matrix J J ℝ) (z w : J → ℝ) (j : J) : ℝ :=
  z j * (K *ᵥ w) j - (L *ᵥ w) j

/-- Independent cohorts (`K = diag(τ² + vⱼ)`, `L = τ²I`, `J ≥ 2`): with the optimal
factors the blend error is uncorrelated with every imbalance, `κⱼ = 0`. -/
theorem imbalanceCov_of_diag (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, 0 < τ2 + v j)
    (hJ : 1 < Fintype.card J) (w : J → ℝ) (j : J) :
    imbalanceCov K (τ2 • (1 : Matrix J J ℝ)) (fun j => (moments K τ2 v j).bestZ) w j = 0 := by
  have h := (hd j).ne'
  simp only [imbalanceCov]
  rw [bestZ_of_diag hK hd hJ]
  simp only [hK, mulVec_diagonal, smul_mulVec,
    one_mulVec, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The loss `Σⱼ φⱼ(MSEⱼ + 2cⱼκⱼ + cⱼ²V)` of the corrections `μ̂ⱼᵇ + cⱼD`. -/
def correctionLoss (φ mse κ : J → ℝ) (V : ℝ) (c : J → ℝ) : ℝ :=
  ∑ j, φ j * (mse j + 2 * c j * κ j + c j ^ 2 * V)

/-- The best correction factors (Wang–Fuller–Qu): `cⱼ* = (λuⱼ/φⱼ - κⱼ)/V` with
`λ = (V + Σᵢuᵢκᵢ)/Σᵢ(uᵢ²/φᵢ)`. -/
noncomputable def bestCorrectionC (φ u κ : J → ℝ) (V : ℝ) (j : J) : ℝ :=
  ((V + ∑ i, u i * κ i) / (∑ i, u i ^ 2 / φ i) * (u j / φ j) - κ j) / V

omit [DecidableEq J] in
/-- The best correction factors satisfy the balance constraint `Σⱼ uⱼcⱼ = 1`. -/
theorem sum_mul_bestCorrectionC (φ u κ : J → ℝ) {V : ℝ} (hV : V ≠ 0)
    (hS : ∑ i, u i ^ 2 / φ i ≠ 0) : ∑ j, u j * bestCorrectionC φ u κ V j = 1 := by
  have h : ∀ j, u j * bestCorrectionC φ u κ V j
      = ((V + ∑ i, u i * κ i) / (∑ i, u i ^ 2 / φ i) * (u j ^ 2 / φ j) - u j * κ j) / V :=
    fun j => by rw [bestCorrectionC]; ring
  simp only [h, ← sum_div, sum_sub_distrib, ← mul_sum]
  rw [div_mul_cancel₀ _ hS, add_sub_cancel_right, div_self hV]

omit [DecidableEq J] in
/-- **The best balanced correction** (PLAN G7b, Wang–Fuller–Qu). Among the corrections
`μ̂ⱼᵇ + cⱼD` of a blend by a multiple of its imbalance that are balanced (`Σⱼ uⱼcⱼ = 1`,
some `uⱼ ≠ 0`), `c* = bestCorrectionC` minimises the loss `Σⱼ φⱼ(MSEⱼ + 2cⱼκⱼ + cⱼ²V)`
(`φⱼ > 0`, `V > 0`). The excess loss of any other balanced `c` is `VΣⱼφⱼ(cⱼ - cⱼ*)²`. -/
theorem bestCorrection_optimal (φ u mse κ : J → ℝ) (V : ℝ) (hφ : ∀ j, 0 < φ j) (hV : 0 < V)
    (hu : ∃ j, u j ≠ 0) :
    ∑ j, u j * bestCorrectionC φ u κ V j = 1 ∧
      ∀ c, ∑ j, u j * c j = 1 →
        correctionLoss φ mse κ V (bestCorrectionC φ u κ V) ≤ correctionLoss φ mse κ V c := by
  have hS : 0 < ∑ i, u i ^ 2 / φ i := by
    obtain ⟨j, hj⟩ := hu
    exact sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (hφ i).le)
      ⟨j, mem_univ j, div_pos (by positivity) (hφ j)⟩
  have h1 := sum_mul_bestCorrectionC φ u κ hV.ne' hS.ne'
  refine ⟨h1, fun c hc => ?_⟩
  set cs := bestCorrectionC φ u κ V
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (V + ∑ i, u i * κ i) / (∑ i, u i ^ 2 / φ i) := ⟨_, rfl⟩
  -- First-order condition: `φⱼ(κⱼ + Vcⱼ*) = λuⱼ`.
  have hfoc : ∀ j, φ j * (κ j + V * cs j) = lam * u j := fun j => by
    have := (hφ j).ne'
    simp only [cs, bestCorrectionC, ← hlam]
    field_simp
    ring
  have hsplit : correctionLoss φ mse κ V c = correctionLoss φ mse κ V cs
      + V * ∑ j, φ j * (c j - cs j) ^ 2
      + 2 * lam * (∑ j, u j * c j - ∑ j, u j * cs j) := by
    simp only [correctionLoss, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by linear_combination (2 * (c j - cs j)) * hfoc j
  rw [hsplit, hc, h1, sub_self, mul_zero, add_zero]
  have : 0 ≤ ∑ j, φ j * (c j - cs j) ^ 2 :=
    sum_nonneg fun j _ => mul_nonneg (hφ j).le (sq_nonneg _)
  nlinarith

omit [DecidableEq J] in
/-- **The common shift is the best balanced correction** when the loss weights are the
balance weights (`φ = u > 0`) and `κⱼ = cov(μ̂ⱼᵇ - μⱼ, D)` is the same for every cohort:
`θ̂ⱼ = μ̂ⱼᵇ + D/Σᵢuᵢ`, i.e. every rate is shifted by the same amount. -/
theorem commonShift_optimal (u mse κ : J → ℝ) (V k : ℝ) (hu : ∀ j, 0 < u j) (hV : 0 < V)
    (hκ : ∀ j, κ j = k) (c : J → ℝ) (hc : ∑ j, u j * c j = 1) :
    correctionLoss u mse κ V (fun _ => (∑ i, u i)⁻¹) ≤ correctionLoss u mse κ V c := by
  obtain ⟨j, -, -⟩ := exists_ne_zero_of_sum_ne_zero (hc.trans_ne one_ne_zero)
  have hU : 0 < ∑ i, u i := sum_pos (fun i _ => hu i) ⟨j, mem_univ j⟩
  have hshift : bestCorrectionC u u κ V = fun _ => (∑ i, u i)⁻¹ := by
    have hsq : ∑ i, u i ^ 2 / u i = ∑ i, u i :=
      sum_congr rfl fun i _ => by rw [sq, mul_div_assoc, div_self (hu i).ne', mul_one]
    funext l
    simp only [bestCorrectionC, hκ, hsq, div_self (hu l).ne', ← sum_mul]
    field_simp
    ring
  rw [← hshift]
  exact (bestCorrection_optimal u u mse κ V hu hV ⟨j, (hu j).ne'⟩).2 c hc

end Balance

/-! ### Block-diagonal `K`: two-stage GLS -/

section Blocks

variable {G : Type*} [Fintype G] [DecidableEq G] (grp : J → G)

/-- The block of `K` on group `g`. -/
def groupBlock (K : Matrix J J ℝ) (g : G) : Matrix {j // grp j = g} {j // grp j = g} ℝ :=
  K.submatrix Subtype.val Subtype.val

/-- `K` is block diagonal with respect to `grp`. -/
def IsBlockDiag (K : Matrix J J ℝ) : Prop := ∀ i j, grp i ≠ grp j → K i j = 0

variable {grp}

omit [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G] in
lemma groupBlock_posDef {K : Matrix J J ℝ} (hK : K.PosDef) (g : G) : (groupBlock grp K g).PosDef :=
  hK.submatrix Subtype.val_injective

omit [DecidableEq J] [Fintype G] in
/-- A sum over `J` of a function vanishing outside group `g` is a sum over the group. -/
lemma sum_eq_sum_groupBlock (g : G) (f : J → ℝ) (hf : ∀ j, grp j ≠ g → f j = 0) :
    ∑ j, f j = ∑ j : {j // grp j = g}, f j := by
  rw [← Finset.sum_subtype (Finset.univ.filter (grp · = g)) (by simp), Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> simp [hf j, h]

omit [Fintype G] in
/-- For block-diagonal `K`, `K⁻¹1` is assembled from the blocks: `(K⁻¹1)ⱼ = (K_g⁻¹1)ⱼ`
with `g` the group of `j`. -/
theorem Kinv_one_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K)
    (j : J) : (K⁻¹ *ᵥ 1) j = ((groupBlock grp K (grp j))⁻¹ *ᵥ 1) ⟨j, rfl⟩ := by
  set x : J → ℝ := fun j => ((groupBlock grp K (grp j))⁻¹ *ᵥ 1) ⟨j, rfl⟩
  have hx : ∀ g (j : J) (h : grp j = g), x j = ((groupBlock grp K g)⁻¹ *ᵥ 1) ⟨j, h⟩ := by
    intro g j h; subst h; rfl
  have hKx : K *ᵥ x = 1 := by
    ext i
    simp only [mulVec, dotProduct, Pi.one_apply]
    rw [sum_eq_sum_groupBlock (grp := grp) (grp i) _ fun j hj => by rw [hb i j (Ne.symm hj), zero_mul]]
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (groupBlock_posDef (grp := grp) hK (grp i)).isUnit
    have := congrFun (mul_nonsing_inv _ hdet) ⟨i, rfl⟩
    have h1 : ((groupBlock grp K (grp i)) *ᵥ ((groupBlock grp K (grp i))⁻¹ *ᵥ 1)) ⟨i, rfl⟩ = 1 := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]; rfl
    rw [← h1]
    simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hx _ _ j.2]; rfl
  rw [Kinv_one_eq_of_mulVec ((Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit) one_ne_zero
    (by rw [hKx, one_smul]), inv_one, one_smul]

/-- The precision `1ᵀK⁻¹1` of a block-diagonal `K` is the sum of the block precisions. -/
theorem invTotal_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K) :
    invTotal K = ∑ g, invTotal (groupBlock grp K g) := by
  rw [invTotal, one_dotProduct, ← Finset.sum_fiberwise Finset.univ grp]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [invTotal, one_dotProduct, Finset.sum_subtype _ (p := (grp · = g)) (by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Kinv_one_blockDiag hK hb]
  obtain ⟨j, h⟩ := a
  subst h; rfl

/-- Two-stage GLS: for block-diagonal `K`, the GLS weight of `j` is its GLS weight
within its group `g`, times the inverse-variance weight (eq. (23)) of the group,
whose variance is the group's `s²_g = 1/1ᵀK_g⁻¹1`. -/
theorem glsWeight_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K)
    (j : J) : glsWeight K j = glsWeight (groupBlock grp K (grp j)) ⟨j, rfl⟩
      * invVarWeight (fun g => (invTotal (groupBlock grp K g))⁻¹) (grp j) := by
  have : Nonempty {i // grp i = grp j} := ⟨⟨j, rfl⟩⟩
  have hg := (invTotal_pos (groupBlock_posDef (grp := grp) hK (grp j))).ne'
  simp only [glsWeight, invVarWeight, inv_inv, ← invTotal_blockDiag hK hb,
    Kinv_one_blockDiag hK hb]
  field_simp

end Blocks

end Core
end Credibility
