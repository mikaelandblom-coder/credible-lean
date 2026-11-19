import Mathlib
import Credibility.Blend
import Credibility.Weights

/-!
# The matrix Blend: vector levels (towards Hachemeister and frequency × severity)

Each cohort has a level vector `μⱼ ∈ ℝᴾ` (e.g. level and slope, Hachemeister 1975; or
frequency and severity, Jewell 1973), an estimate `μ̂ⱼ ∈ ℝᴾ`, and the blend is
`μ̂ + Z (μ̂ⱼ - μ̂)` with a `P × P` credibility matrix `Z`.

* `VecBlendMoments`: the matrix version of `BlendMoments` (thesis eq. (7)). The error
  covariance is a matrix parabola in `Z` with vertex `Z* = cov(μⱼ - μ̂, μ̂ⱼ - μ̂) Var(μ̂ⱼ - μ̂)⁻¹`,
  optimal in the Loewner order, hence for every linear combination `aᵀμⱼ` (a premium) and for
  the trace. The scalar blend is the case `P = Unit`.
* `Core` level: cohort estimates with a joint covariance `K` over `J × P` (correlated cohorts
  *and* components), the matrix GLS portfolio `μ̂ = Σ Bⱼ μ̂ⱼ` with `Σ Bⱼ = I`, and its moments.
  The classical multidimensional Bühlmann–Straub model (Bühlmann & Gisler 2005, ch. 7) has
  `K` block diagonal over cohorts; here it need not be.

All second moments are given matrices, as in `Blend.lean`.
-/

open Matrix

namespace Credibility

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The second moments (`P × P` matrices) that determine the error covariance of the
matrix blend `μ̂ + Z (μ̂ⱼ - μ̂)` as an estimator of `μⱼ`. For random vectors `X`, `Y`,
`cov(X, Y) = E[(X - EX)(Y - EY)ᵀ]`. -/
structure VecBlendMoments (P : Type*) where
  /-- `Var(μ̂ⱼ)` -/
  varCohort : Matrix P P ℝ
  /-- `Var(μ̂)` -/
  varPortfolio : Matrix P P ℝ
  /-- `Var(μⱼ)` -/
  varTarget : Matrix P P ℝ
  /-- `cov(μ̂ⱼ, μ̂)` -/
  covEst : Matrix P P ℝ
  /-- `cov(μ̂ⱼ, μⱼ)` -/
  covCohortTarget : Matrix P P ℝ
  /-- `cov(μ̂, μⱼ)` -/
  covPortfolioTarget : Matrix P P ℝ

namespace VecBlendMoments

variable (m : VecBlendMoments P)

/-- `Var(μ̂ⱼ - μ̂)`, the curvature of `errVar`. -/
def gap : Matrix P P ℝ := m.varCohort - m.covEst - m.covEstᵀ + m.varPortfolio

/-- `cov(μ̂ⱼ - μ̂, μⱼ - μ̂)`. -/
def cross : Matrix P P ℝ :=
  m.varPortfolio - m.covEst + m.covCohortTarget - m.covPortfolioTarget

/-- `Var(μⱼ - μ̂)`, the error covariance of the portfolio estimate alone (`Z = 0`). -/
def varRest : Matrix P P ℝ :=
  m.varTarget - m.covPortfolioTarget - m.covPortfolioTargetᵀ + m.varPortfolio

/-- `Var(μ̂ + Z (μ̂ⱼ - μ̂) - μⱼ)`, the matrix version of eq. (6). -/
def errVar (Z : Matrix P P ℝ) : Matrix P P ℝ :=
  Z * m.gap * Zᵀ - Z * m.cross - m.crossᵀ * Zᵀ + m.varRest

/-- The best credibility matrix, the matrix version of eq. (7):
`Z* = cov(μⱼ - μ̂, μ̂ⱼ - μ̂) Var(μ̂ⱼ - μ̂)⁻¹`. -/
noncomputable def bestZ : Matrix P P ℝ := m.crossᵀ * m.gap⁻¹

omit [Fintype P] [DecidableEq P] in
/-- `Var(μ̂ⱼ - μ̂)` is symmetric when `Var(μ̂ⱼ)` and `Var(μ̂)` are. -/
theorem gap_transpose (hc : m.varCohortᵀ = m.varCohort) (hp : m.varPortfolioᵀ = m.varPortfolio) :
    m.gapᵀ = m.gap := by
  simp only [gap, transpose_add, transpose_sub, transpose_transpose, hc, hp]
  abel

/-- `errVar` is a matrix parabola with its vertex at `bestZ`:
`errVar Z = errVar Z* + (Z - Z*) Var(μ̂ⱼ - μ̂) (Z - Z*)ᵀ`. -/
theorem errVar_eq (hc : m.varCohortᵀ = m.varCohort) (hp : m.varPortfolioᵀ = m.varPortfolio)
    (hg : IsUnit m.gap.det) (Z : Matrix P P ℝ) :
    m.errVar Z = m.errVar m.bestZ + (Z - m.bestZ) * m.gap * (Z - m.bestZ)ᵀ := by
  have hG := m.gap_transpose hc hp
  -- `Z* G = Cᵀ` and `G Z*ᵀ = C`
  have h1 : m.bestZ * m.gap = m.crossᵀ := by
    rw [bestZ, Matrix.mul_assoc, nonsing_inv_mul _ hg, Matrix.mul_one]
  have h2 : m.gap * m.bestZᵀ = m.cross := by
    rw [← hG, ← transpose_mul, h1, transpose_transpose]
  unfold errVar
  rw [← h1, ← h2]
  generalize m.bestZ = A
  simp only [transpose_sub]
  noncomm_ring

/-- Eq. (7) is optimal in the Loewner order whenever `Var(μ̂ⱼ - μ̂)` is positive
semidefinite and invertible: `errVar Z - errVar Z*` is positive semidefinite. -/
theorem bestZ_optimal (hc : m.varCohortᵀ = m.varCohort) (hp : m.varPortfolioᵀ = m.varPortfolio)
    (hg : m.gap.PosSemidef) (hdet : IsUnit m.gap.det) (Z : Matrix P P ℝ) :
    (m.errVar Z - m.errVar m.bestZ).PosSemidef := by
  rw [m.errVar_eq hc hp hdet Z, add_sub_cancel_left]
  simpa [conjTranspose_eq_transpose_of_trivial] using hg.mul_mul_conjTranspose_same (Z - m.bestZ)

/-- So `Z*` is best for every linear combination: `aᵀ errVar(Z*) a ≤ aᵀ errVar(Z) a`, the
MSE of the blend as an estimator of `aᵀμⱼ` (e.g. a first-order premium). -/
theorem bestZ_optimal_dotProduct (hc : m.varCohortᵀ = m.varCohort)
    (hp : m.varPortfolioᵀ = m.varPortfolio) (hg : m.gap.PosSemidef) (hdet : IsUnit m.gap.det)
    (Z : Matrix P P ℝ) (a : P → ℝ) :
    a ⬝ᵥ (m.errVar m.bestZ *ᵥ a) ≤ a ⬝ᵥ (m.errVar Z *ᵥ a) := by
  have h := (m.bestZ_optimal hc hp hg hdet Z).dotProduct_mulVec_nonneg a
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at h
  linarith

/-- …and for the trace (the summed MSE of all components). -/
theorem bestZ_optimal_trace (hc : m.varCohortᵀ = m.varCohort)
    (hp : m.varPortfolioᵀ = m.varPortfolio) (hg : m.gap.PosSemidef) (hdet : IsUnit m.gap.det)
    (Z : Matrix P P ℝ) : (m.errVar m.bestZ).trace ≤ (m.errVar Z).trace := by
  have h := (m.bestZ_optimal hc hp hg hdet Z).trace_nonneg
  rw [trace_sub] at h
  linarith

/-- …and it is the unique optimum when `Var(μ̂ⱼ - μ̂)` is positive definite: a credibility
matrix whose summed MSE is no larger is `Z*`. -/
theorem bestZ_unique (hc : m.varCohortᵀ = m.varCohort) (hp : m.varPortfolioᵀ = m.varPortfolio)
    (hg : m.gap.PosDef) {Z : Matrix P P ℝ}
    (hZ : (m.errVar Z).trace ≤ (m.errVar m.bestZ).trace) : Z = m.bestZ := by
  have hdet : IsUnit m.gap.det := isUnit_iff_ne_zero.2 hg.det_pos.ne'
  rw [m.errVar_eq hc hp hdet Z, trace_add] at hZ
  set D := Z - m.bestZ with hD
  -- `tr(D G Dᵀ) = Σᵢ dᵢᵀ G dᵢ` over the rows `dᵢ` of `D`
  have htr : (D * m.gap * Dᵀ).trace = ∑ i, D i ⬝ᵥ (m.gap *ᵥ D i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, Matrix.mul_apply]
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnn : ∀ i, 0 ≤ D i ⬝ᵥ (m.gap *ᵥ D i) := fun i => by
    simpa using hg.posSemidef.dotProduct_mulVec_nonneg (D i)
  have h0 : ∑ i, D i ⬝ᵥ (m.gap *ᵥ D i) = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => hnn i)
  have hrow : ∀ i, D i = 0 := by
    intro i
    by_contra hne
    have hpos := hg.dotProduct_mulVec_pos hne
    simp only [star_trivial] at hpos
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h0 i (Finset.mem_univ _)
    linarith
  have : D = 0 := funext hrow
  exact sub_eq_zero.1 this

end VecBlendMoments

/-! ### The scalar blend is the case `P = Unit` -/

namespace BlendMoments

/-- A scalar blend as a `1 × 1` matrix blend. -/
def toVec (m : BlendMoments) : VecBlendMoments Unit where
  varCohort := of fun _ _ => m.varCohort
  varPortfolio := of fun _ _ => m.varPortfolio
  varTarget := of fun _ _ => m.varTarget
  covEst := of fun _ _ => m.covEst
  covCohortTarget := of fun _ _ => m.covCohortTarget
  covPortfolioTarget := of fun _ _ => m.covPortfolioTarget

/-- The matrix error covariance of `Z = (z)` is the scalar `errVar z`, eq. (6). -/
theorem toVec_errVar (m : BlendMoments) (z : ℝ) :
    m.toVec.errVar (of fun _ _ => z) () () = m.errVar z := by
  simp only [VecBlendMoments.errVar, VecBlendMoments.gap, VecBlendMoments.cross,
    VecBlendMoments.varRest, toVec, errVar, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    transpose_apply,
    of_apply, Finset.univ_unique, Finset.sum_singleton]
  ring

/-- …and the best credibility matrix is the scalar `bestZ`, eq. (7). -/
theorem toVec_bestZ (m : BlendMoments) : m.toVec.bestZ () () = m.bestZ := by
  simp only [VecBlendMoments.bestZ, VecBlendMoments.gap, VecBlendMoments.cross, toVec, bestZ, gap,
    inv_subsingleton, Matrix.mul_apply, diagonal_apply_eq, Matrix.sub_apply, Matrix.add_apply,
    transpose_apply,
    of_apply, Finset.univ_unique, Finset.sum_singleton, Ring.inverse_eq_inv']
  rw [div_eq_mul_inv]
  ring

end BlendMoments

/-! ### Core level: a joint covariance over cohorts × components

The stacked estimates `(μ̂ⱼ)ⱼ` have covariance `K : (J × P) × (J × P)`, the stacked levels
covariance `L`. `U` stacks `|J|` identity matrices: `Uᵀx = Σⱼ xⱼ`. The matrix GLS portfolio
estimate is `μ̂ = Wᵀ x` with `W = K⁻¹U (UᵀK⁻¹U)⁻¹`, so `Bⱼ = (rows j of W)ᵀ` and `Σⱼ Bⱼ = I`. -/

namespace CoreVector

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- `U`: `|J|` stacked `P × P` identity matrices. -/
def stack (J P : Type*) [DecidableEq P] : Matrix (J × P) P ℝ := fun jp q => if jp.2 = q then 1 else 0

/-- The information matrix `UᵀK⁻¹U` (matrix version of `invTotal K = 1ᵀK⁻¹1`); its inverse
is `Var(μ̂)`. -/
noncomputable def info (K : Matrix (J × P) (J × P) ℝ) : Matrix P P ℝ := (stack J P)ᵀ * K⁻¹ * stack J P

/-- The matrix GLS weights `W = K⁻¹U (UᵀK⁻¹U)⁻¹` (matrix version of `glsWeight`). -/
noncomputable def glsW (K : Matrix (J × P) (J × P) ℝ) : Matrix (J × P) P ℝ :=
  K⁻¹ * stack J P * (info K)⁻¹

omit [Fintype J] [DecidableEq J] in
/-- `U` has full column rank (when there is a cohort). -/
theorem stack_mulVec_injective [Nonempty J] : Function.Injective (stack J P).mulVec := by
  intro x y h
  funext q
  have := congrFun h (Classical.arbitrary J, q)
  simpa [stack, mulVec, dotProduct] using this

/-- The information matrix is positive definite. -/
theorem info_posDef [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) :
    (info K).PosDef := by
  simpa [info, conjTranspose_eq_transpose_of_trivial] using
    hK.inv.conjTranspose_mul_mul_same (stack_mulVec_injective (J := J) (P := P))

/-- The weights sum to the identity, `Σⱼ Bⱼ = UᵀW = I`: the portfolio estimate is unbiased. -/
theorem stack_transpose_mul_glsW [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) :
    (stack J P)ᵀ * glsW K = 1 := by
  rw [glsW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← info]
  exact mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (info_posDef hK).det_pos.ne')

/-- `K W = U (UᵀK⁻¹U)⁻¹`: every cohort estimate has covariance `Var(μ̂)` with `μ̂`
(matrix version of `K b = s² 1`). -/
theorem mul_glsW {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) :
    K * glsW K = stack J P * (info K)⁻¹ := by
  rw [glsW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hK.det_pos.ne'), Matrix.one_mul]

/-- The weights `W` give the best unbiased portfolio estimate (matrix version of eq. (25)):
for any weights `A` with `UᵀA = I` (`Σⱼ Aⱼ = I`), `Var(Aᵀx) - Var(Wᵀx) = AᵀKA - WᵀKW` is
positive semidefinite. -/
theorem glsW_optimal [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) :
    (Aᵀ * K * A - (glsW K)ᵀ * K * glsW K).PosSemidef := by
  set W := glsW K
  set D := A - W
  have hUD : (stack J P)ᵀ * D = 0 := by
    rw [Matrix.mul_sub, hA, stack_transpose_mul_glsW hK, sub_self]
  -- `WᵀKD = S UᵀD = 0`, using `Kᵀ = K`
  have hKt : Kᵀ = K := by simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hWKD : Wᵀ * K * D = 0 := by
    have : Wᵀ * K = (K * W)ᵀ := by rw [transpose_mul, hKt]
    rw [this, mul_glsW hK, transpose_mul, Matrix.mul_assoc, hUD, Matrix.mul_zero]
  have hDKW : Dᵀ * K * W = 0 := by
    rw [← transpose_transpose (Dᵀ * K * W)]
    simp only [transpose_mul, transpose_transpose, hKt, ← Matrix.mul_assoc, hWKD,
      transpose_zero]
  have hA' : A = W + D := by simp [D]
  have : Aᵀ * K * A - Wᵀ * K * W = Dᵀ * K * D := by
    rw [hA']
    simp only [transpose_add, Matrix.add_mul, Matrix.mul_add, hWKD, hDKW]
    abel
  rw [this]
  simpa [conjTranspose_eq_transpose_of_trivial] using hK.posSemidef.conjTranspose_mul_mul_same D

/-! ### The moments of the matrix blend for cohort `j` -/

/-- `Eⱼ`: picks the block of cohort `j`, `Eⱼᵀx = xⱼ`. -/
def sel (P : Type*) [DecidableEq P] (j : J) : Matrix (J × P) P ℝ :=
  fun ip q => if ip.1 = j ∧ ip.2 = q then 1 else 0

/-- The moments of the matrix blend for cohort `j` when the stacked estimates have
covariance `K` and the stacked levels covariance `L` (estimate = level + noise, the noise
uncorrelated with the levels): `Var(μ̂ⱼ) = Kⱼⱼ`, `Var(μ̂) = (UᵀK⁻¹U)⁻¹`, `Var(μⱼ) =
cov(μ̂ⱼ, μⱼ) = Lⱼⱼ`, `cov(μ̂ⱼ, μ̂) = EⱼᵀKW` and `cov(μ̂, μⱼ) = WᵀLEⱼ`. -/
noncomputable def moments (K L : Matrix (J × P) (J × P) ℝ) (j : J) : VecBlendMoments P where
  varCohort := (sel P j)ᵀ * K * sel P j
  varPortfolio := (info K)⁻¹
  varTarget := (sel P j)ᵀ * L * sel P j
  covEst := (sel P j)ᵀ * K * glsW K
  covCohortTarget := (sel P j)ᵀ * L * sel P j
  covPortfolioTarget := (glsW K)ᵀ * L * sel P j

/-- `EⱼᵀU = I`: the block of cohort `j` of `|J|` stacked identities. -/
theorem sel_transpose_mul_stack (j : J) : (sel P j)ᵀ * stack J P = 1 := by
  ext p q
  simp [Matrix.mul_apply, sel, stack, Fintype.sum_prod_type, Matrix.one_apply, ite_and, eq_comm]

/-- Every cohort estimate has covariance `Var(μ̂)` with the portfolio estimate,
`cov(μ̂ⱼ, μ̂) = (UᵀK⁻¹U)⁻¹` (matrix version of `(K b)ⱼ = s²`). -/
theorem moments_covEst {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) (L : Matrix (J × P) (J × P) ℝ)
    (j : J) : (moments K L j).covEst = (info K)⁻¹ := by
  simp only [moments]
  rw [Matrix.mul_assoc, mul_glsW hK, ← Matrix.mul_assoc, sel_transpose_mul_stack, Matrix.one_mul]

/-- `Var(μ̂ⱼ - μ̂) = Kⱼⱼ - (UᵀK⁻¹U)⁻¹` (matrix version of `levelMoments_gap_eq`). -/
theorem moments_gap [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) :
    (moments K L j).gap = (sel P j)ᵀ * K * sel P j - (info K)⁻¹ := by
  have hS : ((info K)⁻¹)ᵀ = (info K)⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using (info_posDef hK).inv.isHermitian.eq
  rw [VecBlendMoments.gap, moments_covEst hK, hS]
  simp only [moments]
  abel

/-- Matrix eq. (26): `Z*ⱼ = (Lⱼⱼ - EⱼᵀLW) (Kⱼⱼ - (UᵀK⁻¹U)⁻¹)⁻¹`, the matrix
version of `Core.levelMoments_bestZ_eq`. -/
theorem moments_bestZ [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) :
    (moments K L j).bestZ = ((sel P j)ᵀ * L * sel P j - (sel P j)ᵀ * L * glsW K)
      * ((sel P j)ᵀ * K * sel P j - (info K)⁻¹)⁻¹ := by
  rw [VecBlendMoments.bestZ, moments_gap hK, VecBlendMoments.cross, moments_covEst hK]
  congr 1
  simp only [moments, transpose_sub, transpose_add, transpose_mul, transpose_transpose, hL,
    Matrix.mul_assoc]
  abel

end CoreVector
end Credibility
