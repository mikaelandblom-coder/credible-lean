import Mathlib
import Credibility.Blend
import Credibility.Weights
import Credibility.OffDiagonal

/-!
# The credibility factor at the level of `K` (thesis §2.5, eqs. (24)–(26))

Everything here only needs the covariance matrix `K` of the cohort estimates,
the heterogeneity `τ²` and the cohort variances `vⱼ = σ²ⱼⱼ`, so that
`Var(μ̂ⱼ) = τ² + vⱼ` and `Kⱼⱼ = τ² + vⱼ`. The models (`Unequal`, and `Model` as
its case `Tⱼ = T`) build their own `K` and take these results as corollaries.
-/

open Finset Matrix

/-- Rayleigh-quotient bound for a real symmetric matrix: if every eigenvalue is at
least `m`, then `m‖x‖² ≤ xᵀAx`. With `A = U diag(λ) Uᵀ` and `y = Uᵀx`,
`xᵀAx = Σ λᵢ yᵢ²` and `‖y‖ = ‖x‖`. -/
theorem Matrix.IsHermitian.mul_dotProduct_le_dotProduct_mulVec {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) {m : ℝ}
    (hm : ∀ i, m ≤ hA.eigenvalues i) (x : n → ℝ) : m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hA' : A = U * diagonal hA.eigenvalues * Uᵀ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [U, star_eq_conjTranspose]
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    simpa [U, star_eq_conjTranspose] using this
  set y := Uᵀ *ᵥ x
  have hq : x ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ (diagonal hA.eigenvalues *ᵥ y) := by
    conv_lhs => rw [hA']
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have hn : x ⬝ᵥ x = y ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, hUU,
      one_mulVec]
  rw [hq, hn]
  simp only [dotProduct, mulVec_diagonal, mul_sum]
  exact sum_le_sum fun i _ => by nlinarith [hm i, mul_self_nonneg (y i)]

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

/-- Scaling `K`, `τ²` and `v` by `c ≠ 0` scales all blend moments by `c`. -/
theorem moments_smul {c : ℝ} (hc : c ≠ 0) (j : J) :
    moments (c • K) (c * τ2) (c • v) j = (moments K τ2 v j).smul c := by
  simp only [moments, BlendMoments.smul, glsWeight_smul K hc, invTotal_smul K hc, smul_mulVec,
    Pi.smul_apply, smul_eq_mul, mul_inv, inv_inv]
  congr 1 <;> ring

/-- …so the best credibility factor does not change (it is unit-free). -/
theorem bestZ_smul {c : ℝ} (hc : c ≠ 0) (j : J) :
    (moments (c • K) (c * τ2) (c • v) j).bestZ = (moments K τ2 v j).bestZ := by
  rw [moments_smul hc, BlendMoments.bestZ_smul _ hc]

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

/-- Finding 17 with the smallest eigenvalue: `|zⱼ| ‖eⱼ - b‖ ≤ τ²/λ_min(K)`. -/
theorem abs_bestZ_mul_norm_le_eigenvalues [Nonempty J] (hK : K.PosDef) (hτ : 0 ≤ τ2) (j : J)
    (hKjj : K j j = τ2 + v j) :
    |(moments K τ2 v j).bestZ| * √((Pi.single j 1 - glsWeight K) ⬝ᵥ (Pi.single j 1 - glsWeight K))
      ≤ τ2 / univ.inf' univ_nonempty hK.isHermitian.eigenvalues :=
  abs_bestZ_mul_norm_le hK hτ ((lt_inf'_iff _).2 fun i _ => hK.eigenvalues_pos i)
    (hK.isHermitian.mul_dotProduct_le_dotProduct_mulVec fun i => inf'_le _ (mem_univ i)) j hKjj

/-- Finding 17 with the smallest eigenvalue: the own-data weight
`cⱼ = bⱼ + zⱼ(1 - bⱼ)` satisfies `|cⱼ - bⱼ| ≤ τ²/λ_min(K)`. -/
theorem abs_bestZ_mul_one_sub_le_eigenvalues [Nonempty J] (hK : K.PosDef) (hτ : 0 ≤ τ2) (j : J)
    (hKjj : K j j = τ2 + v j) :
    |(moments K τ2 v j).bestZ * (1 - glsWeight K j)|
      ≤ τ2 / univ.inf' univ_nonempty hK.isHermitian.eigenvalues :=
  abs_bestZ_mul_one_sub_le hK hτ ((lt_inf'_iff _).2 fun i _ => hK.eigenvalues_pos i)
    (hK.isHermitian.mul_dotProduct_le_dotProduct_mulVec fun i => inf'_le _ (mem_univ i)) j hKjj

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

/-- Finding 5, the converse direction: if the weights are the credibility factors
rescaled, `bⱼ = zⱼ/z*` for all `j` (with `z* ≠ 0` and every gap
`τ² + vⱼ - s² ≠ 0`), then one shift `λ = τ²/z* - s²` makes every row's
off-diagonal sum vanish: `Σ_{i≠j} (Kⱼᵢ + λ) bᵢ = 0`. Reason: `z = z*·b` turns
eq. (26) into `(1 - bⱼ)τ² = z* bⱼ (Kⱼⱼ - s²)`, and `K b = s² u` gives
`Σ_{i≠j} Kⱼᵢ bᵢ = s² - Kⱼⱼ bⱼ`. -/
theorem exists_shift_of_b_eq_z (hK : K.PosDef) (hdiag : ∀ j, K j j = τ2 + v j)
    (hgap : ∀ j, τ2 + v j - (invTotal K)⁻¹ ≠ 0)
    (hZ : ∑ i, (moments K τ2 v i).bestZ ≠ 0)
    (hz : ∀ j, glsWeight K j = (moments K τ2 v j).bestZ / ∑ i, (moments K τ2 v i).bestZ) :
    ∃ l : ℝ, ∀ j, ∑ i ∈ univ.erase j, (K j i + l) * glsWeight K i = 0 := by
  refine ⟨τ2 / ∑ i, (moments K τ2 v i).bestZ - (invTotal K)⁻¹, fun j => ?_⟩
  have hj := hz j
  rw [eq_div_iff hZ, bestZ_eq hK, eq_div_iff (hgap j)] at hj
  have hKb : ∑ i, K j i * glsWeight K i = (invTotal K)⁻¹ :=
    congrFun (mulVec_glsWeight hK) j
  have : Nonempty J := ⟨j⟩
  have hsum := sum_glsWeight hK
  simp only [add_mul, sum_add_distrib, ← mul_sum,
    sum_erase_eq_sub (mem_univ j), hKb, hsum, hdiag]
  field_simp
  linear_combination -hj

/-- Finding 5, the converse for three cohorts: if `bⱼ = zⱼ/z*` for every `j` and no
weight is zero, then all cohort pairs have the same covariance. With
`xᵢⱼ = Kᵢⱼ + λ` the three conditions of `exists_shift_of_b_eq_z` are a linear
system in `(x₁₂, x₁₃, x₂₃)` with determinant `2 b₁b₂b₃ ≠ 0`, so every `xᵢⱼ = 0`. -/
theorem equalCov_of_b_eq_z {K : Matrix (Fin 3) (Fin 3) ℝ} {v : Fin 3 → ℝ} (hK : K.PosDef)
    (hdiag : ∀ j, K j j = τ2 + v j) (hb : ∀ j, glsWeight K j ≠ 0)
    (hz : ∀ j, glsWeight K j = (moments K τ2 v j).bestZ / ∑ i, (moments K τ2 v i).bestZ) :
    ∃ c, ∀ i j, i ≠ j → K i j = c := by
  have hZ : ∑ i, (moments K τ2 v i).bestZ ≠ 0 := by
    intro h; apply hb 0; rw [hz 0, h, div_zero]
  have hgap : ∀ j, τ2 + v j - (invTotal K)⁻¹ ≠ 0 := by
    intro j
    rw [← hdiag, ← quadForm_single_sub_glsWeight hK]
    refine (hK.dotProduct_mulVec_pos ?_).ne'
    intro h0
    obtain ⟨i, hij⟩ : ∃ i, i ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
    have := congrFun h0 i
    simp [hij] at this
    exact hb i this
  obtain ⟨l, hl⟩ := exists_shift_of_b_eq_z hK hdiag hgap hZ hz
  have hs : ∀ i j, K i j = K j i := fun i j => by simpa using hK.isHermitian.apply j i
  have e0 := hl 0
  have e1 := hl 1
  have e2 := hl 2
  simp [sum_erase_eq_sub, Fin.sum_univ_three] at e0 e1 e2
  set b0 := glsWeight K 0
  set b1 := glsWeight K 1
  set b2 := glsWeight K 2
  rw [hs 1 0] at e1
  rw [hs 2 0, hs 2 1] at e2
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  have hw : K 0 1 + l = 0 := by
    have : (2 * b0 * b1 * b2) * (K 0 1 + l) = 0 := by
      linear_combination b0 * b2 * e0 + b1 * b2 * e1 - b2 ^ 2 * e2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h0) h1) h2)
  have hy : K 0 2 + l = 0 := by
    have : (2 * b0 * b1 * b2) * (K 0 2 + l) = 0 := by
      linear_combination b0 * b1 * e0 - b1 ^ 2 * e1 + b1 * b2 * e2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h0) h1) h2)
  have hx : K 1 2 + l = 0 := by
    have : (2 * b0 * b1 * b2) * (K 1 2 + l) = 0 := by
      linear_combination - b0 ^ 2 * e0 + b0 * b1 * e1 + b0 * b2 * e2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h0) h1) h2)
  refine ⟨-l, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  all_goals first | linarith | (rw [hs]; linarith)

/-- `K⁻¹u = x` from `Kx = u`, so `bⱼ = xⱼ/x*`: to compute the weights, solve `Kx = u`. -/
lemma glsWeight_of_mulVec {K : Matrix J J ℝ} (hK : K.PosDef) {x : J → ℝ} (hx : K *ᵥ x = 1)
    (j : J) : glsWeight K j = x j / ∑ i, x i := by
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have : K⁻¹ *ᵥ 1 = x := by rw [← hx, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  simp [glsWeight, invTotal, this, one_dotProduct]

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

/-! ### The best linear unbiased predictor (Finding 18)

The blend `z μ̂ⱼ + (1 - z) μ̂` is one linear combination `Σᵢ dᵢ μ̂ᵢ` with `Σᵢ dᵢ = 1`
(unbiased whatever the common mean). Among all of them the best one for `μⱼ` is the
classical best linear unbiased predictor (Goldberger 1962; the homogeneous credibility
estimator). Its weights, the exact loss of any other weights against it, and when the
blend is the best one. Row `j` of `L` is `cov(μⱼ, μ̂ᵢ)`. -/

section Blup

/-- The mean squared error `dᵀKd - 2 dᵀLⱼ + Lⱼⱼ` of `Σᵢ dᵢ μ̂ᵢ` (`Σᵢ dᵢ = 1`) for `μⱼ`
(`Estimates.mse_portLin`). -/
def linMse (K L : Matrix J J ℝ) (j : J) (d : J → ℝ) : ℝ :=
  d ⬝ᵥ (K *ᵥ d) - 2 * (d ⬝ᵥ L j) + L j j

/-- The weights of the best linear unbiased predictor of `μⱼ`:
`d* = K⁻¹Lⱼ + (1 - 1ᵀK⁻¹Lⱼ) b`, with the GLS weights `b`. -/
noncomputable def blupWeight (K L : Matrix J J ℝ) (j : J) : J → ℝ :=
  K⁻¹ *ᵥ L j + (1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) • glsWeight K

/-- The weights `z eⱼ + (1 - z) b` of the blend `z μ̂ⱼ + (1 - z) μ̂` on the cohort
estimates. -/
noncomputable def blendWeight (K : Matrix J J ℝ) (j : J) (z : ℝ) : J → ℝ :=
  z • Pi.single j 1 + (1 - z) • glsWeight K

omit [DecidableEq J] in
/-- For symmetric `K`, `xᵀKy = yᵀKx`. -/
lemma dotProduct_mulVec_comm_of_isHermitian (hK : K.IsHermitian) (x y : J → ℝ) :
    x ⬝ᵥ (K *ᵥ y) = y ⬝ᵥ (K *ᵥ x) := by
  have hsymm : Kᵀ = K := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hK
  rw [dotProduct_mulVec, ← hsymm, vecMul_transpose, hsymm, dotProduct_comm]

/-- The best predictor is unbiased: `Σᵢ d*ᵢ = 1`. -/
theorem sum_blupWeight [Nonempty J] (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) :
    ∑ i, blupWeight K L j i = 1 := by
  simp only [blupWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
    sum_glsWeight hK, one_dotProduct]
  ring

/-- The first-order condition: `K d* - Lⱼ` is a constant vector. -/
theorem mulVec_blupWeight (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) (i : J) :
    (K *ᵥ blupWeight K L j) i - L j i = (1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹ := by
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  rw [blupWeight, mulVec_add, mulVec_mulVec, mul_nonsing_inv K hdet, one_mulVec, mulVec_smul,
    mulVec_glsWeight hK]
  simp

omit [DecidableEq J] in
/-- Pythagoras for linear predictors: if `K e - Lⱼ` is a constant vector, then any
weights `d` with the same sum as `e` lose exactly `(d - e)ᵀK(d - e)` against `e`. -/
theorem linMse_eq_add_of_mulVec (hK : K.IsHermitian) (L : Matrix J J ℝ) (j : J)
    {e : J → ℝ} {c : ℝ} (he : ∀ i, (K *ᵥ e) i - L j i = c) (d : J → ℝ)
    (hd : ∑ i, d i = ∑ i, e i) :
    linMse K L j d = linMse K L j e + (d - e) ⬝ᵥ (K *ᵥ (d - e)) := by
  have hsymm := dotProduct_mulVec_comm_of_isHermitian hK e d
  -- `(d - e)ᵀ(K e - Lⱼ) = c Σ(d - e) = 0`.
  have hx : d ⬝ᵥ (K *ᵥ e) - e ⬝ᵥ (K *ᵥ e) - (d ⬝ᵥ L j - e ⬝ᵥ L j) = 0 := by
    have : ∑ i, (d i - e i) * ((K *ᵥ e) i - L j i) = 0 := by
      simp only [he, ← sum_mul, sum_sub_distrib, hd, sub_self, zero_mul]
    rw [← this]
    simp only [dotProduct, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  simp only [linMse, mulVec_sub, dotProduct_sub, sub_dotProduct]
  linarith

/-- The loss of any unbiased weights `d` against the best predictor is
`(d - d*)ᵀK(d - d*)`. -/
theorem linMse_eq_blupWeight_add [Nonempty J] (hK : K.PosDef) (L : Matrix J J ℝ) (j : J)
    (d : J → ℝ) (hd : ∑ i, d i = 1) :
    linMse K L j d = linMse K L j (blupWeight K L j)
      + (d - blupWeight K L j) ⬝ᵥ (K *ᵥ (d - blupWeight K L j)) :=
  linMse_eq_add_of_mulVec hK.isHermitian L j (mulVec_blupWeight hK L j) d
    (hd.trans (sum_blupWeight hK L j).symm)

/-- **The best linear unbiased predictor**: `d*` has the smallest mean squared error
among all weights with `Σᵢ dᵢ = 1`. -/
theorem blupWeight_optimal (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) (d : J → ℝ)
    (hd : ∑ i, d i = 1) : linMse K L j (blupWeight K L j) ≤ linMse K L j d := by
  have : Nonempty J := ⟨j⟩
  rw [linMse_eq_blupWeight_add hK L j d hd]
  have := hK.posSemidef.dotProduct_mulVec_nonneg (d - blupWeight K L j)
  simp only [star_trivial] at this
  linarith

/-- …and it is the only one. -/
theorem blupWeight_unique (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) {d : J → ℝ}
    (hd : ∑ i, d i = 1) (h : linMse K L j d ≤ linMse K L j (blupWeight K L j)) :
    d = blupWeight K L j := by
  have : Nonempty J := ⟨j⟩
  rw [linMse_eq_blupWeight_add hK L j d hd] at h
  by_contra hne
  have := hK.dotProduct_mulVec_pos (x := d - blupWeight K L j) (sub_ne_zero.mpr hne)
  simp only [star_trivial] at this
  linarith

/-- The blend is unbiased: its weights sum to one. -/
theorem sum_blendWeight [Nonempty J] (hK : K.PosDef) (j : J) (z : ℝ) :
    ∑ i, blendWeight K j z i = 1 := by
  simp only [blendWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
    sum_glsWeight hK, Finset.sum_pi_single', mem_univ, ite_true]
  ring

/-- `K(z eⱼ + (1 - z) b) = z Kₓⱼ + (1 - z) s² 1`. -/
theorem mulVec_blendWeight (hK : K.PosDef) (j : J) (z : ℝ) (i : J) :
    (K *ᵥ blendWeight K j z) i = z * K i j + (1 - z) * (invTotal K)⁻¹ := by
  rw [blendWeight, mulVec_add, mulVec_smul, mulVec_smul, mulVec_glsWeight hK, mulVec_single_one]
  simp

/-- The mean squared error of the blend's weights is `errVar`, eq. (6). -/
theorem linMse_blendWeight [Nonempty J] (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) (z : ℝ) :
    linMse K L j (blendWeight K j z) = (levelMoments K L (K j j) j).errVar z := by
  have h1 : blendWeight K j z ⬝ᵥ (K *ᵥ blendWeight K j z)
      = z * (z * K j j + (1 - z) * (invTotal K)⁻¹) + (1 - z) * (invTotal K)⁻¹ := by
    have hb : glsWeight K ⬝ᵥ (K *ᵥ blendWeight K j z) = (invTotal K)⁻¹ := by
      rw [dotProduct_mulVec_comm_of_isHermitian hK.isHermitian, mulVec_glsWeight hK]
      simp only [dotProduct, ← sum_mul, sum_blendWeight hK, one_mul]
    rw [show blendWeight K j z ⬝ᵥ (K *ᵥ blendWeight K j z)
      = (z • Pi.single j 1 + (1 - z) • glsWeight K) ⬝ᵥ (K *ᵥ blendWeight K j z) from rfl,
      add_dotProduct, smul_dotProduct, smul_dotProduct, single_one_dotProduct, hb,
      mulVec_blendWeight hK]
    simp only [smul_eq_mul]
  have h2 : blendWeight K j z ⬝ᵥ L j = z * L j j + (1 - z) * (L *ᵥ glsWeight K) j := by
    rw [blendWeight, add_dotProduct, smul_dotProduct, smul_dotProduct, single_one_dotProduct]
    simp only [smul_eq_mul, mulVec, dotProduct_comm]
  rw [linMse, h1, h2]
  simp only [BlendMoments.errVar, levelMoments, mulVec_glsWeight hK]
  ring

/-- **The price of the blend**: the blend with factor `z` loses exactly
`(w - d*)ᵀK(w - d*)` against the best linear unbiased predictor, `w = z eⱼ + (1 - z) b`. -/
theorem errVar_eq_blupWeight_add [Nonempty J] (hK : K.PosDef) (L : Matrix J J ℝ) (j : J)
    (z : ℝ) :
    (levelMoments K L (K j j) j).errVar z = linMse K L j (blupWeight K L j)
      + (blendWeight K j z - blupWeight K L j) ⬝ᵥ
          (K *ᵥ (blendWeight K j z - blupWeight K L j)) := by
  rw [← linMse_blendWeight hK]
  exact linMse_eq_blupWeight_add hK L j _ (sum_blendWeight hK j z)

/-- **When the blend is the best linear unbiased predictor**: exactly when
`cov(μⱼ, μ̂ᵢ) - z cov(μ̂ᵢ, μ̂ⱼ)` is the same for every cohort `i`. -/
theorem blendWeight_eq_blupWeight_iff (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) (z : ℝ) :
    blendWeight K j z = blupWeight K L j ↔ ∃ c, ∀ i, L j i - z * K i j = c := by
  have : Nonempty J := ⟨j⟩
  constructor
  · intro h
    refine ⟨(1 - z) * (invTotal K)⁻¹ - (1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹, fun i => ?_⟩
    have h1 := mulVec_blupWeight hK L j i
    rw [← h, mulVec_blendWeight hK] at h1
    linarith
  · rintro ⟨c, hc⟩
    have he : ∀ i, (K *ᵥ blendWeight K j z) i - L j i = (1 - z) * (invTotal K)⁻¹ - c :=
      fun i => by rw [mulVec_blendWeight hK]; linarith [hc i]
    refine blupWeight_unique hK L j (sum_blendWeight hK j z) ?_
    rw [linMse_eq_add_of_mulVec hK.isHermitian L j he (blupWeight K L j)
      ((sum_blupWeight hK L j).trans (sum_blendWeight hK j z).symm)]
    have := hK.posSemidef.dotProduct_mulVec_nonneg (blupWeight K L j - blendWeight K j z)
    simp only [star_trivial] at this
    linarith

/-- **Uncorrelated levels** (`L = τ²I`, the thesis): if cohort `j` has the same covariance
`c ≠ Kⱼⱼ` with every other cohort estimate, the blend with `z = τ²/(Kⱼⱼ - c)` is the best
linear unbiased predictor of `μⱼ`. Two cohorts, equal covariances and independent cohorts
are cases. -/
theorem blendWeight_eq_blupWeight_of_equalCol (hK : K.PosDef) (j : J) {c : ℝ}
    (hc : ∀ i, i ≠ j → K i j = c) (hne : c ≠ K j j) :
    blendWeight K j (τ2 / (K j j - c)) = blupWeight K (τ2 • (1 : Matrix J J ℝ)) j := by
  have hd : K j j - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine (blendWeight_eq_blupWeight_iff hK _ j _).mpr ⟨-(τ2 / (K j j - c) * c), fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    field_simp
    ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hij), smul_eq_mul, mul_zero,
      hc i hij]
    ring

/-- **Uncorrelated levels: the blend is the best linear unbiased predictor only then.**
For `L = τ²I`, `τ² ≠ 0`, some blend of cohort `j` is the best linear unbiased predictor of
`μⱼ` exactly when `j` has the same covariance `c ≠ Kⱼⱼ` with every other cohort estimate. -/
theorem exists_blendWeight_eq_blupWeight_iff (hK : K.PosDef) (hτ : τ2 ≠ 0) (j : J) :
    (∃ z, blendWeight K j z = blupWeight K (τ2 • (1 : Matrix J J ℝ)) j)
      ↔ ∃ c, c ≠ K j j ∧ ∀ i, i ≠ j → K i j = c := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, hc⟩ := (blendWeight_eq_blupWeight_iff hK _ j z).mp hz
    have hj := hc j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hj
    have hi : ∀ i, i ≠ j → -(z * K i j) = c := fun i hij => by
      have := hc i
      simpa [Matrix.one_apply_ne (Ne.symm hij)] using this
    by_cases hz0 : z = 0
    · -- Then `c = τ² ≠ 0` and `c = 0` at any other cohort, so there is none.
      refine ⟨K j j + 1, by linarith, fun i hij => absurd ?_ hτ⟩
      have := hi i hij
      rw [hz0] at this hj
      linarith
    · refine ⟨-c / z, fun h => hτ ?_, fun i hij => ?_⟩
      · rw [← h] at hj
        field_simp at hj
        linarith
      · rw [← hi i hij]
        field_simp
  · rintro ⟨c, hne, hc⟩
    exact ⟨_, blendWeight_eq_blupWeight_of_equalCol hK j hc hne⟩

end Blup

/-! ### A wrong covariance model (Finding 19)

A fitted model computes its weights from a working `K̃`, `L̃` (e.g. ignoring the
correlation between cohorts). If the working model's error variances are within factors
`a ≤ A` of the true ones, the working best predictor loses at most the factor
`(a + A)²/(4aA)` of Kantorovich (Wielandt's inequality). The variances compared are those of
`Σᵢ dᵢμ̂ᵢ - tμⱼ` for all `d` and `t`. -/

section Misspec

/-- `Var(Σᵢ dᵢμ̂ᵢ - tμⱼ) = dᵀKd - 2t dᵀLⱼ + t²Lⱼⱼ`; `linMse` is the case `t = 1`. -/
def predForm (K L : Matrix J J ℝ) (j : J) (d : J → ℝ) (t : ℝ) : ℝ :=
  d ⬝ᵥ (K *ᵥ d) - 2 * t * (d ⬝ᵥ L j) + t ^ 2 * L j j

omit [DecidableEq J] in
lemma predForm_one (K L : Matrix J J ℝ) (j : J) (d : J → ℝ) :
    predForm K L j d 1 = linMse K L j d := by
  simp [predForm, linMse]

omit [DecidableEq J] in
/-- Expanding `Var(Σᵢ (s xᵢ + u yᵢ)μ̂ᵢ - sμⱼ)` around `x`, for symmetric `K`. -/
lemma predForm_smul_add (hK : K.IsHermitian) (L : Matrix J J ℝ) (j : J) (x y : J → ℝ)
    (s u : ℝ) :
    predForm K L j (s • x + u • y) s = s ^ 2 * predForm K L j x 1
      + 2 * s * u * (y ⬝ᵥ (K *ᵥ x) - y ⬝ᵥ L j) + u ^ 2 * (y ⬝ᵥ (K *ᵥ y)) := by
  have hc := dotProduct_mulVec_comm_of_isHermitian hK x y
  simp only [predForm, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hc]
  ring

omit [DecidableEq J] in
/-- If `K x - Lⱼ` is a constant vector and `Σᵢ yᵢ = 0` then `yᵀ(K x - Lⱼ) = 0`. -/
lemma dotProduct_sub_eq_zero_of_const (L : Matrix J J ℝ) (j : J) {x : J → ℝ} {c : ℝ}
    (hx : ∀ i, (K *ᵥ x) i - L j i = c) {y : J → ℝ} (hy : ∑ i, y i = 0) :
    y ⬝ᵥ (K *ᵥ x) - y ⬝ᵥ L j = 0 := by
  have : ∑ i, y i * ((K *ᵥ x) i - L j i) = 0 := by simp only [hx, ← sum_mul, hy, zero_mul]
  rw [← this]
  simp only [dotProduct, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- Wielandt's inequality for two directions, in the form needed here: if
`a Q̃ ≤ Q ≤ A Q̃` for `Q(s, u) = s²r + 2sup + u²p` and `Q̃(s, u) = s²R + u²P` (the
directions are orthogonal for `Q̃`, and the cross term of `Q` equals its `u²` term), then
`(A + a)² p ≤ (A - a)² r`. -/
lemma wielandt_aux {a A p r P R : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hlo : ∀ s u : ℝ, a * (s ^ 2 * R + u ^ 2 * P) ≤ s ^ 2 * r + 2 * s * u * p + u ^ 2 * p)
    (hhi : ∀ s u : ℝ, s ^ 2 * r + 2 * s * u * p + u ^ 2 * p ≤ A * (s ^ 2 * R + u ^ 2 * P)) :
    (A + a) ^ 2 * p ≤ (A - a) ^ 2 * r := by
  -- `a(S + X) ≤ aAQ̃ ≤ A(S - X)` with `X = 2sup`, `S = s²r + u²p`, so `(A + a)X ≤ (A - a)S`.
  have key : ∀ s u : ℝ, (A + a) * (2 * s * u * p) ≤ (A - a) * (s ^ 2 * r + u ^ 2 * p) :=
    fun s u => by nlinarith [mul_le_mul_of_nonneg_left (hhi s u) ha,
      mul_le_mul_of_nonneg_left (hlo s (-u)) hA]
  rcases lt_or_ge a A with h | h
  · -- `s = A - a`, `u = A + a`, then divide by `A - a > 0`.
    have := key (A - a) (A + a)
    nlinarith
  · -- `A ≤ a`: then `(A + a)X ≤ (A - a)S ≤ 0` for both signs of `u`, so `p = 0` or `A + a = 0`.
    have h1 := key 1 1
    nlinarith [mul_le_mul_of_nonneg_left h1 (add_nonneg hA ha),
      mul_nonneg (sub_nonneg.mpr h) (add_nonneg hr hp), mul_nonneg (add_nonneg hA ha) hp,
      mul_nonneg (sq_nonneg (A - a)) hr]

/-- **The best predictor of a wrong model** (Kantorovich bound): let the working `K̃`, `L̃`
satisfy `a·Var̃ ≤ Var ≤ A·Var̃` for every `Σᵢ dᵢμ̂ᵢ - tμⱼ` (`predForm`), and its variances
be nonnegative. Then the best linear unbiased predictor of the working model has mean
squared error at most `(a + A)²/(4aA)` times the smallest. -/
theorem linMse_blupWeight_working_le (hK : K.PosDef) {K' L' : Matrix J J ℝ} (hK' : K'.PosDef)
    (L : Matrix J J ℝ) (j : J) {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hlo : ∀ d t, a * predForm K' L' j d t ≤ predForm K L j d t)
    (hhi : ∀ d t, predForm K L j d t ≤ A * predForm K' L' j d t)
    (hQ : ∀ d t, 0 ≤ predForm K' L' j d t) :
    4 * a * A * linMse K L j (blupWeight K' L' j)
      ≤ (A + a) ^ 2 * linMse K L j (blupWeight K L j) := by
  have : Nonempty J := ⟨j⟩
  set e := blupWeight K' L' j
  set h := e - blupWeight K L j
  have he1 : ∑ i, e i = 1 := sum_blupWeight hK' L' j
  have hsum : ∑ i, h i = 0 := by
    simp [h, sum_sub_distrib, he1, sum_blupWeight hK]
  -- Pythagoras: `MSE(e) = MSE(d*) + hᵀKh`.
  have hpy := linMse_eq_blupWeight_add hK L j e (sum_blupWeight hK' L' j)
  -- The cross term of the true form is `hᵀKh`, that of the working form `0`.
  have hB : h ⬝ᵥ (K *ᵥ e) - h ⬝ᵥ L j = h ⬝ᵥ (K *ᵥ h) := by
    have h0 := dotProduct_sub_eq_zero_of_const L j (mulVec_blupWeight hK L j) hsum
    have he : e = blupWeight K L j + h := by simp [h]
    rw [he, mulVec_add, dotProduct_add] at *
    linarith
  have hB' : h ⬝ᵥ (K' *ᵥ e) - h ⬝ᵥ L' j = 0 :=
    dotProduct_sub_eq_zero_of_const L' j (mulVec_blupWeight hK' L' j) hsum
  have hp : 0 ≤ h ⬝ᵥ (K *ᵥ h) := by
    simpa using hK.posSemidef.dotProduct_mulVec_nonneg h
  have hr : 0 ≤ linMse K L j e := by
    rw [← predForm_one]
    exact le_trans (mul_nonneg ha (hQ e 1)) (hlo e 1)
  have hW := wielandt_aux (p := h ⬝ᵥ (K *ᵥ h)) (r := linMse K L j e)
    (P := h ⬝ᵥ (K' *ᵥ h)) (R := linMse K' L' j e) ha hA hp hr
    (fun s u => by
      have := hlo (s • e + u • h) s
      rw [predForm_smul_add hK.isHermitian, predForm_smul_add hK'.isHermitian, hB, hB'] at this
      simp only [predForm_one] at this
      linarith)
    (fun s u => by
      have := hhi (s • e + u • h) s
      rw [predForm_smul_add hK.isHermitian, predForm_smul_add hK'.isHermitian, hB, hB'] at this
      simp only [predForm_one] at this
      linarith)
  rw [hpy] at hW ⊢
  nlinarith

/-- With the true `L`, the working best predictor of a diagonal `K̃ = diag(τ² + vᵢ)` is the
blend with `z = τ²/(τ² + vⱼ)` and inverse-variance weights: the Bühlmann–Straub estimate
that ignores correlation. -/
theorem blupWeight_diag_eq_blendWeight {τ2 : ℝ} {v : J → ℝ} (hd : ∀ i, 0 < τ2 + v i) (j : J) :
    blupWeight (diagonal fun i => τ2 + v i) (τ2 • (1 : Matrix J J ℝ)) j
      = blendWeight (diagonal fun i => τ2 + v i) j (τ2 / (τ2 + v j)) := by
  have hK : (diagonal fun i => τ2 + v i).PosDef := by
    rw [posDef_diagonal_iff]; exact hd
  have := blendWeight_eq_blupWeight_of_equalCol (τ2 := τ2) hK j (c := 0)
    (fun i hij => by simp [diagonal_apply_ne _ hij]) (by simpa using (hd j).ne)
  simpa using this.symm

/-- `K = τ²I + V` is positive definite when `τ² > 0` and the noise correlation is at most
`δ < 1` (`|yᵀVy - Σᵢ vᵢyᵢ²| ≤ δ Σᵢ vᵢyᵢ²`): then `yᵀVy ≥ (1 - δ) Σᵢ vᵢyᵢ² ≥ 0`. -/
lemma posDef_smul_one_add_of_corr {τ2 δ : ℝ} {V : Matrix J J ℝ} (hτ : 0 < τ2)
    (hV : V.IsHermitian) (hv : ∀ i, 0 ≤ V i i) (hδ1 : δ < 1)
    (hδ : ∀ y : J → ℝ, |y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2| ≤ δ * ∑ i, V i i * y i ^ 2) :
    (τ2 • (1 : Matrix J J ℝ) + V).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · exact (isHermitian_one.smul (IsSelfAdjoint.all τ2)).add hV
  · have hxx : 0 < x ⬝ᵥ x := by
      simpa [dotProduct, ← sq] using
        (sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mpr
          (by obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
              exact ⟨i, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩)
    have hW0 : 0 ≤ ∑ i, V i i * x i ^ 2 :=
      sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)
    have := hδ x
    have h2 := neg_abs_le (x ⬝ᵥ (V *ᵥ x) - ∑ i, V i i * x i ^ 2)
    simp only [star_trivial, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    nlinarith

/-- For `K = τ²I + X` and `L = τ²I`: `Var(Σᵢ dᵢμ̂ᵢ - tμⱼ) = τ²(‖d‖² - 2t dⱼ + t²) + dᵀXd`. -/
lemma predForm_smul_one_add (τ2 : ℝ) (X : Matrix J J ℝ) (j : J) (d : J → ℝ) (t : ℝ) :
    predForm (τ2 • 1 + X) (τ2 • 1) j d t
      = τ2 * (d ⬝ᵥ d - 2 * t * d j + t ^ 2) + d ⬝ᵥ (X *ᵥ d) := by
  have hLj : d ⬝ᵥ (τ2 • (1 : Matrix J J ℝ)) j = τ2 * d j := by
    simp [dotProduct, Matrix.one_apply, mul_comm]
  simp only [predForm, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hLj, Matrix.smul_apply, Matrix.one_apply_eq, mul_one]
  ring

omit [DecidableEq J] in
lemma dotProduct_sub_two_mul_add_sq_nonneg (d : J → ℝ) (j : J) (t : ℝ) :
    0 ≤ d ⬝ᵥ d - 2 * t * d j + t ^ 2 := by
  have hdd : d j ^ 2 ≤ d ⬝ᵥ d := by
    simp only [dotProduct, ← sq]
    exact single_le_sum (f := fun i => d i ^ 2) (fun i _ => sq_nonneg _) (mem_univ j)
  nlinarith [sq_nonneg (d j - t)]

/-- **A working noise covariance within factors `a ≤ 1 ≤ A`**: let the true and working
covariances be `K = τ²I + V` and `K̃ = τ²I + Ṽ` with `L = τ²I`, and
`a·yᵀṼy ≤ yᵀVy ≤ A·yᵀṼy` for all `y`. Then the best predictor of the working model has
mean squared error at most `(A + a)²/(4aA)` times the smallest. -/
theorem linMse_noiseWorking_le {τ2 a A : ℝ} {V W : Matrix J J ℝ} (hτ : 0 < τ2)
    (hV : V.IsHermitian) (hW : W.PosSemidef) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hA1 : 1 ≤ A)
    (hlo : ∀ y : J → ℝ, a * (y ⬝ᵥ (W *ᵥ y)) ≤ y ⬝ᵥ (V *ᵥ y))
    (hhi : ∀ y : J → ℝ, y ⬝ᵥ (V *ᵥ y) ≤ A * (y ⬝ᵥ (W *ᵥ y))) (j : J) :
    4 * a * A * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + W) (τ2 • 1) j)
      ≤ (A + a) ^ 2 * linMse (τ2 • 1 + V) (τ2 • 1) j
          (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  have hW0 : ∀ y : J → ℝ, 0 ≤ y ⬝ᵥ (W *ᵥ y) := fun y => by
    simpa using hW.dotProduct_mulVec_nonneg y
  have hVpsd : V.PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hV fun y => by
    simpa using (mul_nonneg ha (hW0 y)).trans (hlo y)
  have hI : (τ2 • (1 : Matrix J J ℝ)).PosDef := PosDef.one.smul hτ
  refine linMse_blupWeight_working_le (hI.add_posSemidef hVpsd) (hI.add_posSemidef hW) _ j ha
    (by linarith) (fun d t => ?_) (fun d t => ?_) (fun d t => ?_)
  · rw [predForm_smul_one_add, predForm_smul_one_add]
    have hT := dotProduct_sub_two_mul_add_sq_nonneg d j t
    nlinarith [hlo d, mul_le_mul_of_nonneg_right ha1 (mul_nonneg hτ.le hT)]
  · rw [predForm_smul_one_add, predForm_smul_one_add]
    have hT := dotProduct_sub_two_mul_add_sq_nonneg d j t
    nlinarith [hhi d, mul_le_mul_of_nonneg_right hA1 (mul_nonneg hτ.le hT)]
  · rw [predForm_smul_one_add]
    exact add_nonneg (mul_nonneg hτ.le (dotProduct_sub_two_mul_add_sq_nonneg d j t)) (hW0 d)

omit [DecidableEq J] in
/-- `yᵀ(shrinkOffDiag θ V)y = Σᵢ vᵢyᵢ² + θ(yᵀVy - Σᵢ vᵢyᵢ²)`. -/
lemma dotProduct_shrinkOffDiag_mulVec [DecidableEq J] (θ : ℝ) (V : Matrix J J ℝ) (y : J → ℝ) :
    y ⬝ᵥ (shrinkOffDiag θ V *ᵥ y)
      = ∑ i, V i i * y i ^ 2 + θ * (y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2) := by
  have hd : y ⬝ᵥ (diagonal V.diag *ᵥ y) = ∑ i, V i i * y i ^ 2 := by
    simp only [mulVec_diagonal, dotProduct, Matrix.diag_apply]
    exact sum_congr rfl fun i _ => by ring
  rw [shrinkOffDiag_eq, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul, hd, smul_eq_mul, smul_eq_mul]
  ring

/-- **The price of damping correlation**: let the noise correlation lie between `-δ₋` and
`δ₊` (`-δ₋ Σᵢ vᵢyᵢ² ≤ yᵀVy - Σᵢ vᵢyᵢ² ≤ δ₊ Σᵢ vᵢyᵢ²`, `δ₋ < 1`), and the working model
multiply the noise covariances off the diagonal by `θ ∈ [0, 1]` (`shrinkOffDiag`). Its best
predictor has mean squared error at most `(A + a)²/(4aA)` times the smallest, with
`a = (1 - δ₋)/(1 - θδ₋)` and `A = (1 + δ₊)/(1 + θδ₊)`. `θ = 0` ignores the correlation,
`θ = 1` is the true model. -/
theorem linMse_damped_le {τ2 θ δm δp : ℝ} {V : Matrix J J ℝ} (hτ : 0 < τ2)
    (hV : V.IsHermitian) (hv : ∀ i, 0 ≤ V i i) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hm0 : 0 ≤ δm)
    (hm1 : δm < 1) (hp0 : 0 ≤ δp)
    (hδ : ∀ y : J → ℝ, -δm * ∑ i, V i i * y i ^ 2 ≤ y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2 ∧
      y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2 ≤ δp * ∑ i, V i i * y i ^ 2) (j : J) :
    4 * ((1 - δm) * (1 + δp) * (1 - θ * δm) * (1 + θ * δp))
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + shrinkOffDiag θ V) (τ2 • 1) j)
      ≤ ((1 + δp) * (1 - θ * δm) + (1 - δm) * (1 + θ * δp)) ^ 2
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  have hS0 : ∀ y : J → ℝ, 0 ≤ ∑ i, V i i * y i ^ 2 :=
    fun y => sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)
  have hm : 0 < 1 - θ * δm := by nlinarith
  have hp : 0 < 1 + θ * δp := by positivity
  have hm' : 0 < 1 - δm := by linarith
  have hVt : (shrinkOffDiag θ V).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · rw [shrinkOffDiag_eq]
      exact (hV.smul (IsSelfAdjoint.all θ)).add
        (isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _) |>.smul
          (IsSelfAdjoint.all _))
    · simp only [star_trivial]
      rw [dotProduct_shrinkOffDiag_mulVec]
      nlinarith [(hδ y).1, hS0 y]
  have key := linMse_noiseWorking_le (a := (1 - δm) / (1 - θ * δm))
    (A := (1 + δp) / (1 + θ * δp)) hτ hV hVt (by positivity)
    (by rw [div_le_one hm]; nlinarith) (by rw [le_div_iff₀ hp]; nlinarith)
    (fun y => by
      rw [dotProduct_shrinkOffDiag_mulVec, div_mul_eq_mul_div, div_le_iff₀ hm]
      nlinarith [(hδ y).1, hS0 y, mul_nonneg (sub_nonneg.mpr hθ1)
        (show 0 ≤ y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2 + δm * ∑ i, V i i * y i ^ 2 by
          linarith [(hδ y).1])])
    (fun y => by
      rw [dotProduct_shrinkOffDiag_mulVec, div_mul_eq_mul_div, le_div_iff₀ hp]
      nlinarith [(hδ y).2, hS0 y, mul_nonneg (sub_nonneg.mpr hθ1)
        (show 0 ≤ δp * ∑ i, V i i * y i ^ 2 - (y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2) by
          linarith [(hδ y).2])]) j
  have e1 : 4 * ((1 - δm) * (1 + δp) * (1 - θ * δm) * (1 + θ * δp))
      = (4 * ((1 - δm) / (1 - θ * δm)) * ((1 + δp) / (1 + θ * δp)))
        * ((1 - θ * δm) * (1 + θ * δp)) ^ 2 := by
    field_simp
  have e2 : ((1 + δp) * (1 - θ * δm) + (1 - δm) * (1 + θ * δp)) ^ 2
      = ((1 + δp) / (1 + θ * δp) + (1 - δm) / (1 - θ * δm)) ^ 2
        * ((1 - θ * δm) * (1 + θ * δp)) ^ 2 := by
    field_simp
  rw [e1, e2, mul_right_comm, mul_right_comm _ (((1 - θ * δm) * (1 + θ * δp)) ^ 2)]
  exact mul_le_mul_of_nonneg_right key (sq_nonneg _)

/-- **The price of ignoring correlation, two-sided**: if the noise correlation lies between
`-δ₋` and `δ₊` (`δ₋ < 1`), the estimate that ignores it (`K̃ = diag(τ² + vᵢ)`) has mean
squared error at most `(2 + δ₊ - δ₋)²/(4(1 - δ₋)(1 + δ₊))` times the smallest: `δ₋` and
`δ₊` are `1` minus the smallest and the largest eigenvalue minus `1` of the noise
correlation matrix. -/
theorem linMse_ignoreCorr_le_two_sided {τ2 δm δp : ℝ} {V : Matrix J J ℝ} (hτ : 0 < τ2)
    (hV : V.IsHermitian) (hv : ∀ i, 0 ≤ V i i) (hm0 : 0 ≤ δm) (hm1 : δm < 1) (hp0 : 0 ≤ δp)
    (hδ : ∀ y : J → ℝ, -δm * ∑ i, V i i * y i ^ 2 ≤ y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2 ∧
      y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2 ≤ δp * ∑ i, V i i * y i ^ 2) (j : J) :
    4 * ((1 - δm) * (1 + δp)) * linMse (τ2 • 1 + V) (τ2 • 1) j
        (blupWeight (diagonal fun i => τ2 + V i i) (τ2 • 1) j)
      ≤ (2 + δp - δm) ^ 2
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  have h0 : τ2 • (1 : Matrix J J ℝ) + shrinkOffDiag 0 V = diagonal fun i => τ2 + V i i := by
    ext i k
    by_cases h : i = k
    · subst h; simp [shrinkOffDiag]
    · simp [shrinkOffDiag, h, Matrix.one_apply_ne h]
  have := linMse_damped_le hτ hV hv le_rfl zero_le_one hm0 hm1 hp0 hδ j
  rw [h0] at this
  convert this using 2 <;> ring


/-- **The price of ignoring correlation**: let the cohort estimates have covariance
`K = τ²I + V` and the levels `L = τ²I`, with noise variances `vᵢ = Vᵢᵢ`. If the noise
correlation is at most `δ < 1` in the sense `|yᵀVy - Σᵢ vᵢyᵢ²| ≤ δ Σᵢ vᵢyᵢ²` (`δ` is the
spectral norm of the noise correlation matrix minus `I`), then the estimate that ignores the
correlation (`K̃ = diag(τ² + vᵢ)`, `blupWeight_diag_eq_blendWeight`) has mean squared error
at most `1/(1 - δ²)` times the smallest. -/
theorem linMse_ignoreCorr_le {τ2 δ : ℝ} {V : Matrix J J ℝ} (hτ : 0 < τ2) (hV : V.IsHermitian)
    (hv : ∀ i, 0 ≤ V i i) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : ∀ y : J → ℝ, |y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2| ≤ δ * ∑ i, V i i * y i ^ 2)
    (j : J) :
    (1 - δ ^ 2) * linMse (τ2 • 1 + V) (τ2 • 1) j
        (blupWeight (diagonal fun i => τ2 + V i i) (τ2 • 1) j)
      ≤ linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  have := linMse_ignoreCorr_le_two_sided hτ hV hv hδ0 hδ1 hδ0
    (fun y => (abs_le.mp (hδ y)).imp (fun h => by linarith) id) j
  nlinarith

omit [DecidableEq J] in
/-- If every off-diagonal noise correlation is at most `r` (`Vᵢₖ² ≤ r² vᵢvₖ`), the bound of
`linMse_ignoreCorr_le` holds with `δ = (J - 1)r`: by AM–GM,
`2|yᵢVᵢₖyₖ| ≤ r(vᵢyᵢ² + vₖyₖ²)` for each pair. -/
lemma corrBound_of_offDiag {V : Matrix J J ℝ} (hv : ∀ i, 0 ≤ V i i) {r : ℝ} (hr : 0 ≤ r)
    (hV : ∀ i k, i ≠ k → V i k ^ 2 ≤ r ^ 2 * V i i * V k k) (y : J → ℝ) :
    |y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2|
      ≤ ((Fintype.card J : ℝ) - 1) * r * ∑ i, V i i * y i ^ 2 := by
  classical
  set f : J → ℝ := fun i => V i i * y i ^ 2
  -- The off-diagonal part of `yᵀVy`.
  have hoff : y ⬝ᵥ (V *ᵥ y) - ∑ i, V i i * y i ^ 2
      = ∑ i, ∑ k, if i = k then 0 else y i * V i k * y k := by
    have h0 : ∀ i k, (if i = k then (0 : ℝ) else y i * V i k * y k)
        = y i * V i k * y k - if i = k then y i * V i k * y k else 0 := fun i k => by
      split_ifs <;> ring
    simp_rw [h0]
    simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, dotProduct, mulVec, mul_sum]
    congr 1
    · exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
    · exact sum_congr rfl fun i _ => by ring
  -- Each pair: `|yᵢVᵢₖyₖ| ≤ (r/2)(fᵢ + fₖ)`.
  have hpair : ∀ i k, |if i = k then 0 else y i * V i k * y k|
      ≤ if i = k then 0 else r / 2 * (f i + f k) := fun i k => by
    split_ifs with h
    · simp
    · have h1 := hV i k h
      have hfi : 0 ≤ f i := mul_nonneg (hv i) (sq_nonneg _)
      have hfk : 0 ≤ f k := mul_nonneg (hv k) (sq_nonneg _)
      have hsq : (y i * V i k * y k) ^ 2 ≤ (r / 2 * (f i + f k)) ^ 2 := by
        have : (y i * V i k * y k) ^ 2 ≤ r ^ 2 * f i * f k := by
          simp only [f]
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg (y i)) (sq_nonneg (y k)))
          nlinarith
        nlinarith [sq_nonneg (f i - f k), mul_nonneg hr hr]
      have hB : 0 ≤ r / 2 * (f i + f k) := by positivity
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  -- Summing: `Σᵢ Σₖ≠ᵢ (r/2)(fᵢ + fₖ) = r(J - 1) Σ f`.
  have hsum : ∑ i, ∑ k, (if i = k then 0 else r / 2 * (f i + f k))
      = ((Fintype.card J : ℝ) - 1) * r * ∑ i, f i := by
    have : ∀ i k, (if i = k then 0 else r / 2 * (f i + f k))
        = r / 2 * (f i + f k) - if i = k then r / 2 * (f i + f k) else 0 := fun i k => by
      split_ifs <;> ring
    simp_rw [this]
    simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, mul_add, sum_add_distrib,
      sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    ring
  rw [hoff]
  calc |∑ i, ∑ k, if i = k then 0 else y i * V i k * y k|
      ≤ ∑ i, |∑ k, if i = k then 0 else y i * V i k * y k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, |if i = k then 0 else y i * V i k * y k| :=
        sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, (if i = k then 0 else r / 2 * (f i + f k)) :=
        sum_le_sum fun i _ => sum_le_sum fun k _ => hpair i k
    _ = ((Fintype.card J : ℝ) - 1) * r * ∑ i, V i i * y i ^ 2 := hsum

/-- **The price of ignoring correlations of at most `r`**: if every noise correlation is at
most `r` in absolute value (`Vᵢₖ² ≤ r² vᵢvₖ`) and `(J - 1)r < 1`, the estimate that ignores
correlation has mean squared error at most `1/(1 - (J - 1)²r²)` times the smallest. For two
cohorts: at most `1/(1 - ρ²)`. -/
theorem linMse_ignoreCorr_le_of_offDiag {τ2 r : ℝ} {V : Matrix J J ℝ} (hτ : 0 < τ2)
    (hV : V.IsHermitian) (hv : ∀ i, 0 ≤ V i i) (hr : 0 ≤ r)
    (hρ : ∀ i k, i ≠ k → V i k ^ 2 ≤ r ^ 2 * V i i * V k k)
    (hJ : ((Fintype.card J : ℝ) - 1) * r < 1) (j : J) :
    (1 - (((Fintype.card J : ℝ) - 1) * r) ^ 2) * linMse (τ2 • 1 + V) (τ2 • 1) j
        (blupWeight (diagonal fun i => τ2 + V i i) (τ2 • 1) j)
      ≤ linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  have hJ1 : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
  exact linMse_ignoreCorr_le hτ hV hv (mul_nonneg (by linarith) hr) hJ
    (corrBound_of_offDiag hv hr hρ) j

/-- An equicorrelated noise covariance, `Vᵢᵢ = vᵢ` and `Vᵢₖ = r√(vᵢvₖ)` (`i ≠ k`), has
`yᵀVy - Σᵢ vᵢyᵢ² = r((Σᵢ √vᵢ yᵢ)² - Σᵢ vᵢyᵢ²)`: correlation between `-r` and `(J - 1)r`. -/
lemma equicorr_bounds {v : J → ℝ} (hv : ∀ i, 0 ≤ v i) {r : ℝ} (hr : 0 ≤ r) (y : J → ℝ) :
    -r * ∑ i, (of fun i k => if i = k then v i else r * √(v i * v k) : Matrix J J ℝ) i i
        * y i ^ 2
      ≤ y ⬝ᵥ ((of fun i k => if i = k then v i else r * √(v i * v k)) *ᵥ y)
        - ∑ i, (of fun i k => if i = k then v i else r * √(v i * v k) : Matrix J J ℝ) i i
          * y i ^ 2 ∧
    y ⬝ᵥ ((of fun i k => if i = k then v i else r * √(v i * v k)) *ᵥ y)
        - ∑ i, (of fun i k => if i = k then v i else r * √(v i * v k) : Matrix J J ℝ) i i
          * y i ^ 2
      ≤ ((Fintype.card J : ℝ) - 1) * r
        * ∑ i, (of fun i k => if i = k then v i else r * √(v i * v k) : Matrix J J ℝ) i i
          * y i ^ 2 := by
  set s : J → ℝ := fun i => √(v i)
  have hs : ∀ i, s i ^ 2 = v i := fun i => Real.sq_sqrt (hv i)
  have hdiag : ∀ i, (of fun i k => if i = k then v i else r * √(v i * v k) : Matrix J J ℝ) i i
      = v i := fun i => by simp
  simp only [hdiag]
  set S := ∑ i, v i * y i ^ 2
  have hentry : ∀ i k, (if i = k then v i else r * √(v i * v k))
      = r * (s i * s k) + if i = k then (1 - r) * v i else 0 := fun i k => by
    by_cases h : i = k
    · subst h; simp only [ite_true, s]; rw [← sq, hs]; ring
    · simp only [h, ite_false, s, Real.sqrt_mul (hv i)]; ring
  have hq : y ⬝ᵥ ((of fun i k => if i = k then v i else r * √(v i * v k)) *ᵥ y)
      = r * (∑ i, s i * y i) ^ 2 + (1 - r) * S := by
    simp only [dotProduct, mulVec, of_apply, hentry]
    calc ∑ x, y x * ∑ i, (r * (s x * s i) + if x = i then (1 - r) * v x else 0) * y i
        = ∑ x, (r * (s x * y x) * ∑ i, s i * y i + (1 - r) * (v x * y x ^ 2)) :=
          sum_congr rfl fun x _ => by
            simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, mem_univ,
              ite_true, mul_add, mul_sum]
            congr 1
            · exact sum_congr rfl fun i _ => by ring
            · ring
      _ = r * (∑ i, s i * y i) ^ 2 + (1 - r) * S := by
          simp only [sum_add_distrib, ← sum_mul, ← mul_sum, S, sq]; ring
  have hS : ∑ i, (s i * y i) ^ 2 = S := sum_congr rfl fun i _ => by rw [mul_pow, hs]
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i => s i * y i)
  rw [hS, card_univ] at hcs
  rw [hq]
  constructor
  · nlinarith [mul_nonneg hr (sq_nonneg (∑ i, s i * y i))]
  · nlinarith [mul_le_mul_of_nonneg_left hcs hr]

/-- **The price of damping equal correlations**: if all noise correlations equal `r ∈ [0, 1)`
(`Vᵢₖ = r√(vᵢvₖ)`) and the working model multiplies them by `θ ∈ [0, 1]`, its best predictor
has mean squared error at most `(A + a)²/(4aA)` times the smallest, with
`a = (1 - r)/(1 - θr)` and `A = (1 + (J - 1)r)/(1 + θ(J - 1)r)`. -/
theorem linMse_damped_equicorr_le {τ2 θ r : ℝ} {v : J → ℝ} (hτ : 0 < τ2) (hv : ∀ i, 0 ≤ v i)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : J) :
    let V : Matrix J J ℝ := of fun i k => if i = k then v i else r * √(v i * v k)
    let ρ := ((Fintype.card J : ℝ) - 1) * r
    4 * ((1 - r) * (1 + ρ) * (1 - θ * r) * (1 + θ * ρ))
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + shrinkOffDiag θ V) (τ2 • 1) j)
      ≤ ((1 + ρ) * (1 - θ * r) + (1 - r) * (1 + θ * ρ)) ^ 2
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  intro V ρ
  have hJ1 : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
  have hV : V.IsHermitian := by
    ext i k
    simp only [V, conjTranspose_apply, of_apply, star_trivial]
    by_cases h : i = k
    · subst h; rfl
    · simp [h, Ne.symm h, mul_comm (v i)]
  exact linMse_damped_le hτ hV (fun i => by simpa [V] using hv i) hθ0 hθ1 hr0 hr1
    (mul_nonneg (by linarith) hr0) (equicorr_bounds hv hr0) j

/-- **The price of ignoring equal correlations**: if all noise correlations equal
`r ∈ [0, 1)`, the estimate that ignores them has mean squared error at most
`(2 + (J - 2)r)²/(4(1 - r)(1 + (J - 1)r))` times the smallest, and this is sharp (as
`τ² → 0`). Two cohorts: `1/(1 - r²)`; three cohorts and `r = 0.5`: `1.5625`. -/
theorem linMse_ignoreCorr_equicorr_le {τ2 r : ℝ} {v : J → ℝ} (hτ : 0 < τ2)
    (hv : ∀ i, 0 ≤ v i) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : J) :
    let V : Matrix J J ℝ := of fun i k => if i = k then v i else r * √(v i * v k)
    4 * ((1 - r) * (1 + ((Fintype.card J : ℝ) - 1) * r))
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (diagonal fun i => τ2 + v i) (τ2 • 1) j)
      ≤ (2 + ((Fintype.card J : ℝ) - 2) * r) ^ 2
        * linMse (τ2 • 1 + V) (τ2 • 1) j (blupWeight (τ2 • 1 + V) (τ2 • 1) j) := by
  intro V
  have h := linMse_damped_equicorr_le hτ hv le_rfl zero_le_one hr0 hr1 j
  have h0 : τ2 • (1 : Matrix J J ℝ) + shrinkOffDiag 0 V = diagonal fun i => τ2 + v i := by
    ext i k
    by_cases h : i = k
    · subst h; simp [V, shrinkOffDiag]
    · simp [V, shrinkOffDiag, h, Matrix.one_apply_ne h]
  simp only at h
  rw [h0] at h
  convert h using 2 <;> ring

end Misspec

end Core
end Credibility
