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
