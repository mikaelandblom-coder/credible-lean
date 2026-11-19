import Mathlib
import Credibility.Blend
import Credibility.Weights
import Credibility.Core

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

/-! ### The gap and the portfolio weights per cohort -/

/-- `Σⱼ EⱼEⱼᵀ = I`: the cohort blocks partition the stacked vector. -/
theorem sum_sel_mul_sel_transpose : ∑ j, sel P j * (sel P j)ᵀ = (1 : Matrix (J × P) (J × P) ℝ) := by
  ext ⟨i, p⟩ ⟨k, q⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, transpose_apply, sel, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases hik : i = k
  · subst hik
    by_cases hpq : p = q <;> simp [hpq, ite_and]
  · simp [hik, ite_and]

/-- `EᵢᵀMEₖ` is the `(i, k)` block of `M`. -/
theorem sel_transpose_mul_mul_sel (M : Matrix (J × P) (J × P) ℝ) (i k : J) :
    (sel P i)ᵀ * M * sel P k = fun p q => M (i, p) (k, q) := by
  ext p q
  simp [Matrix.mul_apply, sel, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq']

/-- `EᵢᵀEₖ = 0` for different cohorts, `I` for the same. -/
theorem sel_transpose_mul_sel (i k : J) :
    (sel P i)ᵀ * sel P k = if i = k then 1 else 0 := by
  have h := sel_transpose_mul_mul_sel (P := P) (1 : Matrix (J × P) (J × P) ℝ) i k
  rw [Matrix.mul_one] at h
  rw [h]
  ext p q
  split_ifs with hik <;> simp [Matrix.one_apply, hik]

/-- `Eᵢᵀ(EₖX) = X` if `i = k`, else `0`. -/
theorem sel_transpose_mul_sel_mul {n : Type*} (i k : J) (X : Matrix P n ℝ) :
    (sel P i)ᵀ * (sel P k * X) = if i = k then X else 0 := by
  rw [← Matrix.mul_assoc, sel_transpose_mul_sel]
  split_ifs <;> simp

/-- `Eᵢᵀ Σₖ EₖXₖ = Xᵢ`. -/
theorem sel_transpose_mul_sum_sel {n : Type*} (i : J) (X : J → Matrix P n ℝ) :
    (sel P i)ᵀ * ∑ k, sel P k * X k = X i := by
  simp [Matrix.mul_sum, sel_transpose_mul_sel_mul]

omit [Fintype P] in
/-- `U = Σⱼ Eⱼ`. -/
theorem stack_eq_sum_sel : stack J P = ∑ j, sel P j := by
  ext ⟨i, p⟩ q
  by_cases hpq : p = q <;> simp [stack, sel, Matrix.sum_apply, hpq]

/-- The weight matrix `Bⱼ = (EⱼᵀW)ᵀ` of cohort `j` in the matrix GLS portfolio estimate. -/
noncomputable def weight (K : Matrix (J × P) (J × P) ℝ) (j : J) : Matrix P P ℝ :=
  ((sel P j)ᵀ * glsW K)ᵀ

/-- The portfolio estimate is `μ̂ = Wᵀx = Σⱼ Bⱼ μ̂ⱼ` with `μ̂ⱼ = Eⱼᵀx`. -/
theorem glsW_transpose_mulVec (K : Matrix (J × P) (J × P) ℝ) (x : J × P → ℝ) :
    (glsW K)ᵀ *ᵥ x = ∑ j, weight K j *ᵥ ((sel P j)ᵀ *ᵥ x) := by
  conv_lhs => rw [← Matrix.mul_one (glsW K)ᵀ, ← sum_sel_mul_sel_transpose, Matrix.mul_sum]
  simp only [weight, transpose_mul, transpose_transpose, Matrix.sum_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

/-- …and the weights sum to the identity, `Σⱼ Bⱼ = I`. -/
theorem sum_weight [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) :
    ∑ j, weight K j = 1 := by
  simp only [weight]
  rw [← transpose_sum, ← Matrix.sum_mul, ← transpose_sum, ← stack_eq_sum_sel,
    stack_transpose_mul_glsW hK, transpose_one]

/-- `Var(μ̂ⱼ - μ̂) = (Eⱼ - W)ᵀ K (Eⱼ - W)`: the gap as a quadratic form in the weights of
`μ̂ⱼ - μ̂` (matrix version of `quadForm_single_sub_glsWeight`). -/
theorem moments_gap_eq_quadForm [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) :
    (moments K L j).gap = (sel P j - glsW K)ᵀ * K * (sel P j - glsW K) := by
  have hKt : Kᵀ = K := by simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hS : ((info K)⁻¹)ᵀ = (info K)⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using (info_posDef hK).inv.isHermitian.eq
  have h1 : (sel P j)ᵀ * K * glsW K = (info K)⁻¹ := moments_covEst hK L j
  have h2 : (glsW K)ᵀ * K * sel P j = (info K)⁻¹ := by
    rw [← hS, ← h1]; simp [transpose_mul, hKt, Matrix.mul_assoc]
  have h3 : (glsW K)ᵀ * K * glsW K = (info K)⁻¹ := by
    rw [Matrix.mul_assoc, mul_glsW hK, ← Matrix.mul_assoc,
      show (glsW K)ᵀ * stack J P = ((stack J P)ᵀ * glsW K)ᵀ by
        rw [transpose_mul, transpose_transpose],
      stack_transpose_mul_glsW hK, transpose_one, Matrix.one_mul]
  rw [moments_gap hK]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, h1, h2, h3]
  abel

/-- The gap `Kⱼⱼ - (UᵀK⁻¹U)⁻¹` is positive definite exactly when `Eⱼ - W` has full column
rank: no component combination `a ≠ 0` has its portfolio weights `Wa` all on cohort `j`
(matrix version of `bⱼ ≠ eⱼ`, the scalar condition for `Var(μ̂ⱼ - μ̂) > 0`). -/
theorem moments_gap_posDef_iff [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) :
    (moments K L j).gap.PosDef ↔ Function.Injective (sel P j - glsW K).mulVec := by
  rw [moments_gap_eq_quadForm hK L j]
  constructor
  · intro h a b hab
    rw [← sub_eq_zero]
    by_contra hne
    have hpos := h.dotProduct_mulVec_pos hne
    have hz : (sel P j - glsW K) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
    simp only [star_trivial, ← mulVec_mulVec, hz, mulVec_zero] at hpos
    simp at hpos
  · intro h
    simpa [conjTranspose_eq_transpose_of_trivial] using hK.conjTranspose_mul_mul_same h

/-! ### Independent cohorts: block-diagonal `K` (Bühlmann & Gisler 2005, ch. 7)

When the cohorts are uncorrelated, `K` is block diagonal with blocks `Kⱼⱼ = EⱼᵀKEⱼ`. Then
`K⁻¹` is block diagonal with blocks `Kⱼⱼ⁻¹`, `UᵀK⁻¹U = Σⱼ Kⱼⱼ⁻¹`, the portfolio weights are
`Bⱼ = (Σᵢ Kᵢᵢ⁻¹)⁻¹ Kⱼⱼ⁻¹`, and with block-diagonal `L` the best credibility matrix is
`Zⱼ = Lⱼⱼ Kⱼⱼ⁻¹`. With `Kⱼⱼ = Λ + Sⱼ` and `Lⱼⱼ = Λ` this is the multidimensional
Bühlmann–Straub model: `Zⱼ = Λ(Λ + Sⱼ)⁻¹` and `μ̂ = (Σᵢ Zᵢ)⁻¹ Σⱼ Zⱼ μ̂ⱼ`. -/

/-- `M` has no covariance between different cohorts. -/
def IsCohortBlockDiag (M : Matrix (J × P) (J × P) ℝ) : Prop :=
  ∀ i k, i ≠ k → ∀ p q, M (i, p) (k, q) = 0

/-- The block of cohort `j`, `Mⱼⱼ = EⱼᵀMEⱼ`. -/
def blk (M : Matrix (J × P) (J × P) ℝ) (j : J) : Matrix P P ℝ := fun p q => M (j, p) (j, q)

/-- For a block-diagonal `M`, `EᵢᵀMEₖ = 0` off the diagonal and `Mⱼⱼ` on it. -/
theorem sel_transpose_mul_mul_sel_of_blockDiag {M : Matrix (J × P) (J × P) ℝ}
    (hM : IsCohortBlockDiag M) (i k : J) :
    (sel P i)ᵀ * M * sel P k = if i = k then blk M i else 0 := by
  rw [sel_transpose_mul_mul_sel]
  split_ifs with h
  · subst h; rfl
  · ext p q; exact hM i k h p q

omit [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J] in
/-- The blocks of a positive definite matrix are positive definite. -/
theorem blk_posDef {M : Matrix (J × P) (J × P) ℝ} (hM : M.PosDef) (j : J) : (blk M j).PosDef :=
  hM.submatrix (e := fun p => (j, p)) fun _ _ h => (Prod.mk.inj h).2

/-- The inverse of a positive definite block-diagonal `K` is block diagonal with blocks
`Kⱼⱼ⁻¹`. -/
theorem sel_transpose_mul_inv_mul_sel_of_blockDiag {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) (i k : J) :
    (sel P i)ᵀ * K⁻¹ * sel P k = if i = k then (blk K i)⁻¹ else 0 := by
  let M : Matrix (J × P) (J × P) ℝ :=
    Matrix.of fun x y => if x.1 = y.1 then (blk K x.1)⁻¹ x.2 y.2 else 0
  have hKM : K * M = 1 := by
    ext ⟨i, p⟩ ⟨k, q⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, M, Matrix.of_apply, mul_ite, mul_zero,
      Matrix.one_apply, Prod.mk.injEq]
    by_cases hik : i = k
    · subst hik
      have := congrFun (congrFun (mul_nonsing_inv (blk K i)
        (isUnit_iff_ne_zero.2 (blk_posDef hK i).det_pos.ne')) p) q
      simpa [Matrix.mul_apply, blk, Matrix.one_apply] using this
    · simp [hb i k hik, hik]
  rw [inv_eq_right_inv hKM, sel_transpose_mul_mul_sel]
  split_ifs with h
  · subst h; ext p q; simp [M]
  · ext p q; simp [M, h]

/-- `UᵀK⁻¹U = Σⱼ Kⱼⱼ⁻¹`: the information adds up over independent cohorts. -/
theorem info_of_blockDiag {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (hb : IsCohortBlockDiag K) : info K = ∑ j, (blk K j)⁻¹ := by
  rw [info, stack_eq_sum_sel, transpose_sum, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  simp [sel_transpose_mul_inv_mul_sel_of_blockDiag hK hb]

/-- `EⱼᵀW = Kⱼⱼ⁻¹ (UᵀK⁻¹U)⁻¹` for independent cohorts. -/
theorem sel_transpose_mul_glsW_of_blockDiag {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (hb : IsCohortBlockDiag K) (j : J) :
    (sel P j)ᵀ * glsW K = (blk K j)⁻¹ * (info K)⁻¹ := by
  rw [glsW, stack_eq_sum_sel, Matrix.mul_sum, ← Matrix.mul_assoc, Matrix.mul_sum, Matrix.sum_mul]
  simp [← Matrix.mul_assoc, sel_transpose_mul_inv_mul_sel_of_blockDiag hK hb]

/-- The portfolio weights of independent cohorts: `Bⱼ = (Σᵢ Kᵢᵢ⁻¹)⁻¹ Kⱼⱼ⁻¹`. -/
theorem weight_of_blockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (hb : IsCohortBlockDiag K) (j : J) :
    weight K j = (∑ i, (blk K i)⁻¹)⁻¹ * (blk K j)⁻¹ := by
  have hsym : ∀ {M : Matrix P P ℝ}, M.PosDef → Mᵀ = M := fun h => by
    simpa [conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq
  rw [weight, sel_transpose_mul_glsW_of_blockDiag hK hb, transpose_mul,
    hsym (info_posDef hK).inv, hsym (blk_posDef hK j).inv, info_of_blockDiag hK hb]

/-- With another cohort, the gap of independent cohorts is positive definite: `Wa` puts
`Kᵢᵢ⁻¹(UᵀK⁻¹U)⁻¹a ≠ 0` on every cohort `i`. -/
theorem moments_gap_posDef_of_blockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) (L : Matrix (J × P) (J × P) ℝ) {i j : J}
    (hij : i ≠ j) : (moments K L j).gap.PosDef := by
  rw [moments_gap_posDef_iff hK L j]
  refine (injective_iff_map_eq_zero' ((sel P j - glsW K).mulVecLin)).2 fun a => ⟨fun ha => ?_,
    fun ha => by simp [ha]⟩
  have h0 : ((sel P i)ᵀ * (sel P j - glsW K)) *ᵥ a = 0 := by
    rw [← mulVec_mulVec]; simp only [mulVecLin_apply] at ha; rw [ha, mulVec_zero]
  rw [Matrix.mul_sub, sel_transpose_mul_sel, if_neg hij, zero_sub,
    sel_transpose_mul_glsW_of_blockDiag hK hb, neg_mulVec, neg_eq_zero] at h0
  have hdet : ((blk K i)⁻¹ * (info K)⁻¹).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (blk_posDef hK i).inv.det_pos.ne' (info_posDef hK).inv.det_pos.ne'
  exact eq_zero_of_mulVec_eq_zero hdet h0

/-- The best credibility matrix of independent cohorts with independent levels:
`Zⱼ = Lⱼⱼ Kⱼⱼ⁻¹` (when there is another cohort). The estimation of `μ̂` changes nothing,
as in the scalar Bühlmann–Straub model (`Core.bestZ_of_diag`). -/
theorem moments_bestZ_of_blockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L)
    (hLb : IsCohortBlockDiag L) {i j : J} (hij : i ≠ j) :
    (moments K L j).bestZ = blk L j * (blk K j)⁻¹ := by
  have hG := moments_gap_posDef_of_blockDiag hK hb L hij
  have hGu : IsUnit (moments K L j).gap.det := isUnit_iff_ne_zero.2 hG.det_pos.ne'
  rw [moments_gap hK] at hGu
  -- `EⱼᵀLW = Lⱼⱼ Kⱼⱼ⁻¹ (UᵀK⁻¹U)⁻¹`, inserting `Σᵢ EᵢEᵢᵀ = I` between `L` and `W`
  have hLW : (sel P j)ᵀ * L * glsW K = blk L j * ((blk K j)⁻¹ * (info K)⁻¹) := by
    rw [← Matrix.mul_one ((sel P j)ᵀ * L), ← sum_sel_mul_sel_transpose, Matrix.mul_sum,
      Matrix.sum_mul]
    simp only [← Matrix.mul_assoc]
    simp only [Matrix.mul_assoc _ (sel P _)ᵀ (glsW K), sel_transpose_mul_glsW_of_blockDiag hK hb,
      sel_transpose_mul_mul_sel_of_blockDiag hLb, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [Matrix.mul_assoc]
  rw [moments_bestZ hK hL, hLW, sel_transpose_mul_mul_sel_of_blockDiag hLb, if_pos rfl,
    sel_transpose_mul_mul_sel_of_blockDiag hb, if_pos rfl]
  -- `(Λ - ΛK⁻¹S)(K - S)⁻¹ = ΛK⁻¹(K - S)(K - S)⁻¹`
  have hKj : IsUnit (blk K j).det := isUnit_iff_ne_zero.2 (blk_posDef hK j).det_pos.ne'
  rw [sel_transpose_mul_mul_sel_of_blockDiag hb, if_pos rfl] at hGu
  have : blk L j - blk L j * ((blk K j)⁻¹ * (info K)⁻¹)
      = blk L j * (blk K j)⁻¹ * (blk K j - (info K)⁻¹) := by
    rw [Matrix.mul_assoc, Matrix.mul_sub, nonsing_inv_mul _ hKj, Matrix.mul_sub, Matrix.mul_one]
  rw [this, Matrix.mul_assoc, mul_nonsing_inv _ hGu, Matrix.mul_one]

/-- **Multidimensional Bühlmann–Straub** (Bühlmann & Gisler 2005, §7.3; Bühlmann & Gisler
1997, `Zᵣ = A(A + Wᵣ⁻¹)⁻¹`): independent cohorts with `Var(μ̂ⱼ) = Λ + Sⱼ` (`Λ` the level
covariance, `Sⱼ` the noise covariance) and independent levels with covariance `Λ` give
`Zⱼ = Λ(Λ + Sⱼ)⁻¹`… -/
theorem moments_bestZ_buhlmannGisler [Nonempty J] {K L : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) (hL : Lᵀ = L) (hLb : IsCohortBlockDiag L)
    {Λ : Matrix P P ℝ} {S : J → Matrix P P ℝ} (hKj : ∀ j, blk K j = Λ + S j)
    (hLj : ∀ j, blk L j = Λ) {i j : J} (hij : i ≠ j) :
    (moments K L j).bestZ = Λ * (Λ + S j)⁻¹ := by
  rw [moments_bestZ_of_blockDiag hK hb hL hLb hij, hKj, hLj]

/-- …and the portfolio estimate is the `Zⱼ`-weighted mean `μ̂ = (Σᵢ Zᵢ)⁻¹ Σⱼ Zⱼ μ̂ⱼ`:
the weight of cohort `j` is `Bⱼ = (Σᵢ Zᵢ)⁻¹ Zⱼ` (when `Λ` is invertible). -/
theorem weight_buhlmannGisler [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) {Λ : Matrix P P ℝ} (hΛ : IsUnit Λ.det)
    {S : J → Matrix P P ℝ} (hKj : ∀ j, blk K j = Λ + S j) (j : J) :
    weight K j = (∑ i, Λ * (Λ + S i)⁻¹)⁻¹ * (Λ * (Λ + S j)⁻¹) := by
  have hsum : IsUnit (∑ i, (blk K i)⁻¹).det := by
    rw [← info_of_blockDiag hK hb]
    exact isUnit_iff_ne_zero.2 (info_posDef hK).det_pos.ne'
  rw [weight_of_blockDiag hK hb, ← Finset.mul_sum]
  simp only [← hKj]
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc Λ⁻¹, nonsing_inv_mul _ hΛ,
    Matrix.one_mul]

/-- A matrix is cohort block diagonal iff its off-diagonal blocks `EᵢᵀMEₖ` vanish. -/
theorem isCohortBlockDiag_iff (M : Matrix (J × P) (J × P) ℝ) :
    IsCohortBlockDiag M ↔ ∀ i k : J, i ≠ k → (sel P i)ᵀ * M * sel P k = 0 := by
  simp only [sel_transpose_mul_mul_sel]
  constructor
  · intro h i k hik; ext p q; exact h i k hik p q
  · intro h i k hik p q; exact congrFun (congrFun (h i k hik) p) q

theorem blk_eq (M : Matrix (J × P) (J × P) ℝ) (j : J) : blk M j = (sel P j)ᵀ * M * sel P j :=
  (sel_transpose_mul_mul_sel M j j).symm

/-! ### Hachemeister's regression model with correlated cohorts

Cohort `j` has observations `Xⱼ ∈ ℝᵀ` (one per period), design `Yⱼ` (`T × P`, e.g. columns
`1` and `t` for level and slope) and `Xⱼ = Yⱼβⱼ + εⱼ`. The stacked noise `ε` has covariance
`Φ` over cohorts × periods, *not* necessarily block diagonal (a year shock hits all
cohorts), and the stacked `β` has covariance `L`. Each cohort's line is fitted by its own GLS,
`bⱼ = MⱼXⱼ` with `Mⱼ = (YⱼᵀΦⱼⱼ⁻¹Yⱼ)⁻¹YⱼᵀΦⱼⱼ⁻¹`. As `MⱼYⱼ = I`, `bⱼ = βⱼ + Mⱼεⱼ` and
`Var(b) = L + MΦMᵀ`. Hachemeister (1975) and Bühlmann & Gisler (1997) have `Φ` block
diagonal; then `Var(bⱼ) = A + Wⱼ⁻¹` with `Wⱼ = YⱼᵀΦⱼⱼ⁻¹Yⱼ` and `Zⱼ = A(A + Wⱼ⁻¹)⁻¹`. -/

section Hachemeister

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `Wⱼ = YⱼᵀΦⱼⱼ⁻¹Yⱼ`, the GLS information of cohort `j`. -/
noncomputable def gram (Y : J → Matrix T P ℝ) (Φ : Matrix (J × T) (J × T) ℝ) (j : J) :
    Matrix P P ℝ :=
  (Y j)ᵀ * (blk Φ j)⁻¹ * Y j

/-- `Mⱼ = Wⱼ⁻¹YⱼᵀΦⱼⱼ⁻¹`: cohort `j`'s own GLS line is `bⱼ = MⱼXⱼ`. -/
noncomputable def indiv (Y : J → Matrix T P ℝ) (Φ : Matrix (J × T) (J × T) ℝ) (j : J) :
    Matrix P T ℝ :=
  (gram Y Φ j)⁻¹ * (Y j)ᵀ * (blk Φ j)⁻¹

/-- The stacked estimator `b = MX`, `M = Σⱼ EⱼMⱼEⱼᵀ`. -/
noncomputable def hachM (Y : J → Matrix T P ℝ) (Φ : Matrix (J × T) (J × T) ℝ) :
    Matrix (J × P) (J × T) ℝ :=
  ∑ j, sel P j * indiv Y Φ j * (sel T j)ᵀ

/-- The stacked design `D = Σⱼ EⱼYⱼEⱼᵀ`: `X = Dβ + ε`. -/
def design (Y : J → Matrix T P ℝ) : Matrix (J × T) (J × P) ℝ :=
  ∑ j, sel T j * Y j * (sel P j)ᵀ

/-- `K = Var(b) = L + MΦMᵀ`, the covariance of the individual line estimates. -/
noncomputable def hachK (L : Matrix (J × P) (J × P) ℝ) (Y : J → Matrix T P ℝ)
    (Φ : Matrix (J × T) (J × T) ℝ) : Matrix (J × P) (J × P) ℝ :=
  L + hachM Y Φ * Φ * (hachM Y Φ)ᵀ

omit [DecidableEq P] [Fintype J] [DecidableEq J] in
/-- `Wⱼ ≻ 0` when `Φ ≻ 0` and `Yⱼ` has full column rank. -/
theorem gram_posDef {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) (j : J) : (gram Y Φ j).PosDef := by
  simpa [gram, conjTranspose_eq_transpose_of_trivial] using
    (blk_posDef hΦ j).inv.conjTranspose_mul_mul_same (hY j)

omit [Fintype J] [DecidableEq J] in
/-- `MⱼYⱼ = I`: the own GLS line is unbiased for `βⱼ`. -/
theorem indiv_mul {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) (j : J) : indiv Y Φ j * Y j = 1 := by
  rw [indiv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Y j)ᵀ, ← gram,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_posDef hΦ hY j).det_pos.ne')]

/-- `EᵢᵀM = MᵢEᵢᵀ`. -/
theorem sel_transpose_mul_hachM (Y : J → Matrix T P ℝ) (Φ : Matrix (J × T) (J × T) ℝ) (i : J) :
    (sel P i)ᵀ * hachM Y Φ = indiv Y Φ i * (sel T i)ᵀ := by
  rw [hachM]
  simp only [Matrix.mul_assoc]
  exact sel_transpose_mul_sum_sel i _

/-- `MD = I`: the stacked lines are unbiased, `b = β + Mε`. -/
theorem hachM_mul_design {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) : hachM Y Φ * design Y = 1 := by
  rw [← sum_sel_mul_sel_transpose (J := J) (P := P), hachM, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : (sel T j)ᵀ * design Y = Y j * (sel P j)ᵀ := by
    rw [design]
    simp only [Matrix.mul_assoc]
    exact sel_transpose_mul_sum_sel j _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hd, ← Matrix.mul_assoc (indiv Y Φ j),
    indiv_mul hΦ hY, Matrix.one_mul]

/-- **Distribution-free covariance of the lines**: if `Var(X) = DLDᵀ + Φ` (levels and noise
uncorrelated), then `Var(b) = M Var(X) Mᵀ = L + MΦMᵀ`. -/
theorem hachM_mul_cov_mul {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef)
    {Y : J → Matrix T P ℝ} (hY : ∀ j, Function.Injective (Y j).mulVec)
    (L : Matrix (J × P) (J × P) ℝ) :
    hachM Y Φ * (design Y * L * (design Y)ᵀ + Φ) * (hachM Y Φ)ᵀ = hachK L Y Φ := by
  have h := hachM_mul_design hΦ hY
  have ht : (design Y)ᵀ * (hachM Y Φ)ᵀ = 1 := by rw [← transpose_mul, h, transpose_one]
  rw [hachK, Matrix.mul_add, Matrix.add_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_assoc, ht,
    Matrix.mul_one]

/-- The covariance of the lines is positive definite: `Φ ≻ 0`, `L ⪰ 0` and every design of
full column rank. -/
theorem hachK_posDef {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) {L : Matrix (J × P) (J × P) ℝ}
    (hL : L.PosSemidef) : (hachK L Y Φ).PosDef := by
  have ht : (design Y)ᵀ * (hachM Y Φ)ᵀ = 1 := by
    rw [← transpose_mul, hachM_mul_design hΦ hY, transpose_one]
  have hinj : Function.Injective (hachM Y Φ)ᵀ.mulVec := fun a b hab => by
    have := congrArg ((design Y)ᵀ *ᵥ ·) hab
    simpa only [mulVec_mulVec, ht, one_mulVec] using this
  have := hΦ.conjTranspose_mul_mul_same hinj
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
  exact Matrix.PosDef.posSemidef_add hL this

/-- **Hachemeister with correlated cohorts**: matrix eq. (26) for the line estimates,
`Zⱼ = (Lⱼⱼ - EⱼᵀL𝒲)(Kⱼⱼ - (UᵀK⁻¹U)⁻¹)⁻¹` with `K = L + MΦMᵀ`. -/
theorem hachemeister_bestZ [Nonempty J] {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef)
    {Y : J → Matrix T P ℝ} (hY : ∀ j, Function.Injective (Y j).mulVec)
    {L : Matrix (J × P) (J × P) ℝ} (hL : L.PosSemidef) (j : J) :
    (moments (hachK L Y Φ) L j).bestZ
      = ((sel P j)ᵀ * L * sel P j - (sel P j)ᵀ * L * glsW (hachK L Y Φ))
        * ((sel P j)ᵀ * hachK L Y Φ * sel P j - (info (hachK L Y Φ))⁻¹)⁻¹ :=
  moments_bestZ (hachK_posDef hΦ hY hL)
    (by simpa [conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq) j

/-- With independent cohorts (`Φ` block diagonal) the noise part `MΦMᵀ` is block diagonal
with blocks `MⱼΦⱼⱼMⱼᵀ = Wⱼ⁻¹`. -/
theorem hachM_noise_blockDiag {Φ : Matrix (J × T) (J × T) ℝ} (hΦ : Φ.PosDef)
    (hb : IsCohortBlockDiag Φ) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) (i k : J) :
    (sel P i)ᵀ * (hachM Y Φ * Φ * (hachM Y Φ)ᵀ) * sel P k
      = if i = k then (gram Y Φ i)⁻¹ else 0 := by
  have hk : (hachM Y Φ)ᵀ * sel P k = sel T k * (indiv Y Φ k)ᵀ := by
    rw [← transpose_transpose (sel P k), ← transpose_mul, sel_transpose_mul_hachM,
      transpose_mul, transpose_transpose]
  have e1 : (sel P i)ᵀ * (hachM Y Φ * Φ * (hachM Y Φ)ᵀ) * sel P k
      = ((sel P i)ᵀ * hachM Y Φ) * Φ * ((hachM Y Φ)ᵀ * sel P k) := by
    simp only [Matrix.mul_assoc]
  rw [e1, sel_transpose_mul_hachM, hk]
  have e2 : indiv Y Φ i * (sel T i)ᵀ * Φ * (sel T k * (indiv Y Φ k)ᵀ)
      = indiv Y Φ i * ((sel T i)ᵀ * Φ * sel T k) * (indiv Y Φ k)ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, sel_transpose_mul_mul_sel_of_blockDiag hb]
  split_ifs with h
  · subst h
    have hS : ∀ {M : Matrix P P ℝ}, M.PosDef → (M⁻¹)ᵀ = M⁻¹ := fun h => by
      simpa [conjTranspose_eq_transpose_of_trivial] using h.inv.isHermitian.eq
    have hF : ((blk Φ i)⁻¹)ᵀ = (blk Φ i)⁻¹ := by
      simpa [conjTranspose_eq_transpose_of_trivial] using (blk_posDef hΦ i).inv.isHermitian.eq
    have hBu : IsUnit (blk Φ i).det := isUnit_iff_ne_zero.2 (blk_posDef hΦ i).det_pos.ne'
    have hGu : IsUnit (gram Y Φ i).det :=
      isUnit_iff_ne_zero.2 (gram_posDef hΦ hY i).det_pos.ne'
    -- `W⁻¹YᵀΦ⁻¹ Φ Φ⁻¹YW⁻¹ = W⁻¹ W W⁻¹`
    simp only [indiv, transpose_mul, transpose_transpose, hF, hS (gram_posDef hΦ hY i),
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blk Φ i)⁻¹ (blk Φ i), nonsing_inv_mul _ hBu, Matrix.one_mul,
      ← Matrix.mul_assoc (Y i)ᵀ, ← Matrix.mul_assoc ((Y i)ᵀ * (blk Φ i)⁻¹), ← gram,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hGu, Matrix.one_mul]
  · simp

/-- **Classical Hachemeister** (independent cohorts, independent `βⱼ` with covariance `A`):
`Zⱼ = A(A + Wⱼ⁻¹)⁻¹`, `Wⱼ = YⱼᵀΦⱼⱼ⁻¹Yⱼ` (Bühlmann & Gisler 1997; 2005, §8.3), and the
collective line is the `Z`-weighted mean of the cohort lines. -/
theorem hachemeister_bestZ_of_blockDiag [Nonempty J] {Φ : Matrix (J × T) (J × T) ℝ}
    (hΦ : Φ.PosDef) (hΦb : IsCohortBlockDiag Φ) {Y : J → Matrix T P ℝ}
    (hY : ∀ j, Function.Injective (Y j).mulVec) {L : Matrix (J × P) (J × P) ℝ}
    (hL : L.PosSemidef) (hLb : IsCohortBlockDiag L) {A : Matrix P P ℝ} (hA : ∀ j, blk L j = A)
    {i j : J} (hij : i ≠ j) :
    (moments (hachK L Y Φ) L j).bestZ = A * (A + (gram Y Φ j)⁻¹)⁻¹ := by
  have hKb : IsCohortBlockDiag (hachK L Y Φ) := by
    rw [isCohortBlockDiag_iff] at hLb ⊢
    intro i k hik
    rw [hachK, Matrix.mul_add, Matrix.add_mul, hLb i k hik, hachM_noise_blockDiag hΦ hΦb hY,
      if_neg hik, add_zero]
  refine moments_bestZ_buhlmannGisler (hachK_posDef hΦ hY hL) hKb
    (by simpa [conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq) hLb
    (S := fun j => (gram Y Φ j)⁻¹) (fun k => ?_) hA hij
  rw [blk_eq, hachK, Matrix.mul_add, Matrix.add_mul, hachM_noise_blockDiag hΦ hΦb hY, if_pos rfl,
    ← blk_eq, hA]

end Hachemeister

/-! ### The best linear unbiased predictor, and separate blends per component

A linear predictor `Aᵀx` of `μⱼ` from the stacked cohort estimates `x` is unbiased whatever
the common mean iff `UᵀA = I` (`Σⱼ Aⱼ = I`). Its error covariance is
`AᵀKA - AᵀLEⱼ - EⱼᵀLA + Lⱼⱼ`. The best one (the homogeneous credibility estimator, matrix
version of `Core.blupWeight`) is `A* = K⁻¹LEⱼ + W(I - UᵀK⁻¹LEⱼ)`, optimal in the Loewner order.
The matrix blend is one such predictor; so are *separate* blends, one scalar blend per
component (e.g. frequency and severity) that uses only that component's data. So the best
predictor beats separate blending; the matrix *blend* need not (Finding 22). -/

/-- The error covariance `Var(Aᵀx - μⱼ) = AᵀKA - AᵀLEⱼ - EⱼᵀLA + Lⱼⱼ` of the linear
predictor `Aᵀx` (matrix version of `Core.linMse`). -/
def linMse (K L : Matrix (J × P) (J × P) ℝ) (j : J) (A : Matrix (J × P) P ℝ) : Matrix P P ℝ :=
  Aᵀ * K * A - Aᵀ * L * sel P j - (sel P j)ᵀ * L * A + (sel P j)ᵀ * L * sel P j

/-- The weights of the best linear unbiased predictor of `μⱼ`:
`A* = K⁻¹LEⱼ + W(I - UᵀK⁻¹LEⱼ)` (matrix version of `Core.blupWeight`). -/
noncomputable def blupW (K L : Matrix (J × P) (J × P) ℝ) (j : J) : Matrix (J × P) P ℝ :=
  K⁻¹ * L * sel P j + glsW K * (1 - (stack J P)ᵀ * K⁻¹ * L * sel P j)

/-- The weights `W + (Eⱼ - W)Zᵀ` of the matrix blend `μ̂ + Z(μ̂ⱼ - μ̂)` on `x`. -/
noncomputable def blendW (K : Matrix (J × P) (J × P) ℝ) (j : J) (Z : Matrix P P ℝ) :
    Matrix (J × P) P ℝ :=
  glsW K + (sel P j - glsW K) * Zᵀ

/-- Pythagoras for linear predictors: if `KE - LEⱼ = UC`, then any weights `A` with
`UᵀA = UᵀE` lose exactly `(A - E)ᵀK(A - E)` against `E`. -/
theorem linMse_eq_add_of_mul {K L : Matrix (J × P) (J × P) ℝ} (hKt : Kᵀ = K) (hL : Lᵀ = L)
    (j : J) {E : Matrix (J × P) P ℝ} {C : Matrix P P ℝ}
    (hE : K * E - L * sel P j = stack J P * C) (A : Matrix (J × P) P ℝ)
    (hA : (stack J P)ᵀ * A = (stack J P)ᵀ * E) :
    linMse K L j A = linMse K L j E + (A - E)ᵀ * K * (A - E) := by
  obtain ⟨D, rfl⟩ : ∃ D, A = E + D := ⟨A - E, by abel⟩
  have hD : (stack J P)ᵀ * D = 0 := by
    rw [Matrix.mul_add] at hA
    simpa using hA
  have h1 : Dᵀ * K * E - Dᵀ * L * sel P j = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_sub, hE, ← Matrix.mul_assoc,
      show Dᵀ * stack J P = ((stack J P)ᵀ * D)ᵀ by rw [transpose_mul, transpose_transpose], hD,
      transpose_zero, Matrix.zero_mul]
  have h2 : Eᵀ * K * D - (sel P j)ᵀ * L * D = 0 := by
    have := congrArg transpose h1
    simpa [transpose_sub, transpose_mul, hKt, hL, Matrix.mul_assoc] using this
  have key : linMse K L j (E + D) = linMse K L j E + Dᵀ * K * D
      + (Dᵀ * K * E - Dᵀ * L * sel P j) + (Eᵀ * K * D - (sel P j)ᵀ * L * D) := by
    simp only [linMse, transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [key, h1, h2, add_sub_cancel_left]
  abel

/-- The best predictor is unbiased: `UᵀA* = I`. -/
theorem stack_transpose_mul_blupW [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) : (stack J P)ᵀ * blupW K L j = 1 := by
  rw [blupW, Matrix.mul_add, ← Matrix.mul_assoc (stack J P)ᵀ (glsW K),
    stack_transpose_mul_glsW hK, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- The first-order condition: `KA* - LEⱼ = U(UᵀK⁻¹U)⁻¹(I - UᵀK⁻¹LEⱼ)`. -/
theorem mul_blupW {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) :
    K * blupW K L j - L * sel P j
      = stack J P * ((info K)⁻¹ * (1 - (stack J P)ᵀ * K⁻¹ * L * sel P j)) := by
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hK.det_pos.ne'
  rw [blupW, Matrix.mul_add, ← Matrix.mul_assoc K (glsW K), mul_glsW hK,
    show K * (K⁻¹ * L * sel P j) = L * sel P j by
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hKu],
    add_sub_cancel_left, Matrix.mul_assoc]

/-- The loss of any unbiased weights `A` against the best predictor is `(A - A*)ᵀK(A - A*)`
(matrix version of `Core.linMse_eq_blupWeight_add`). -/
theorem linMse_eq_blupW_add [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) {A : Matrix (J × P) P ℝ}
    (hA : (stack J P)ᵀ * A = 1) :
    linMse K L j A = linMse K L j (blupW K L j) + (A - blupW K L j)ᵀ * K * (A - blupW K L j) :=
  linMse_eq_add_of_mul (by simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq)
    hL j (mul_blupW hK L j) A (hA.trans (stack_transpose_mul_blupW hK L j).symm)

/-- **The best linear unbiased predictor** (matrix version of `Core.blupWeight_optimal`):
`A*` is optimal in the Loewner order among all weights with `Σⱼ Aⱼ = I`. -/
theorem blupW_optimal [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) {A : Matrix (J × P) P ℝ}
    (hA : (stack J P)ᵀ * A = 1) :
    (linMse K L j A - linMse K L j (blupW K L j)).PosSemidef := by
  rw [linMse_eq_blupW_add hK hL j hA, add_sub_cancel_left]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hK.posSemidef.conjTranspose_mul_mul_same (A - blupW K L j)

/-- …so it is best for every premium `aᵀμⱼ`… -/
theorem blupW_optimal_dotProduct [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) {A : Matrix (J × P) P ℝ}
    (hA : (stack J P)ᵀ * A = 1) (a : P → ℝ) :
    a ⬝ᵥ (linMse K L j (blupW K L j) *ᵥ a) ≤ a ⬝ᵥ (linMse K L j A *ᵥ a) := by
  have h := (blupW_optimal hK hL j hA).dotProduct_mulVec_nonneg a
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at h
  linarith

/-- …and for the trace. -/
theorem blupW_optimal_trace [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) {A : Matrix (J × P) P ℝ}
    (hA : (stack J P)ᵀ * A = 1) :
    (linMse K L j (blupW K L j)).trace ≤ (linMse K L j A).trace := by
  have h := (blupW_optimal hK hL j hA).trace_nonneg
  rw [trace_sub] at h
  linarith

/-- The matrix blend is unbiased: `Uᵀ(W + (Eⱼ - W)Zᵀ) = I`. -/
theorem stack_transpose_mul_blendW [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (j : J) (Z : Matrix P P ℝ) : (stack J P)ᵀ * blendW K j Z = 1 := by
  rw [blendW, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_sub, stack_transpose_mul_glsW hK,
    show (stack J P)ᵀ * sel P j = ((sel P j)ᵀ * stack J P)ᵀ by
      rw [transpose_mul, transpose_transpose],
    sel_transpose_mul_stack, transpose_one, sub_self, Matrix.zero_mul, add_zero]

/-- The error covariance of the matrix blend's weights is `errVar`
(matrix version of `Core.linMse_blendWeight`). -/
theorem linMse_blendW [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) (Z : Matrix P P ℝ) :
    linMse K L j (blendW K j Z) = (moments K L j).errVar Z := by
  have hKt : Kᵀ = K := by simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hS : ((info K)⁻¹)ᵀ = (info K)⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using (info_posDef hK).inv.isHermitian.eq
  set W := glsW K
  set E := sel P j
  set S := (info K)⁻¹
  have h1 : Eᵀ * K * W = S := moments_covEst hK L j
  have h2 : Wᵀ * K * E = S := by
    rw [← hS, ← h1]; simp [transpose_mul, hKt, Matrix.mul_assoc]
  have h3 : Wᵀ * K * W = S := by
    rw [Matrix.mul_assoc, mul_glsW hK, ← Matrix.mul_assoc,
      show Wᵀ * stack J P = ((stack J P)ᵀ * W)ᵀ by rw [transpose_mul, transpose_transpose],
      stack_transpose_mul_glsW hK, transpose_one, Matrix.one_mul]
  have h4 : (Wᵀ * L * E)ᵀ = Eᵀ * L * W := by simp [transpose_mul, hL, Matrix.mul_assoc]
  have h5 : (Eᵀ * L * E)ᵀ = Eᵀ * L * E := by simp [transpose_mul, hL, Matrix.mul_assoc]
  have key : linMse K L j (W + (E - W) * Zᵀ)
      = Wᵀ * K * W + Z * (Eᵀ * K * W - Wᵀ * K * W) + (Wᵀ * K * E - Wᵀ * K * W) * Zᵀ
        + Z * (Eᵀ * K * E - Eᵀ * K * W - Wᵀ * K * E + Wᵀ * K * W) * Zᵀ
        - Wᵀ * L * E - Z * (Eᵀ * L * E - Wᵀ * L * E) - Eᵀ * L * W
        - (Eᵀ * L * E - Eᵀ * L * W) * Zᵀ + Eᵀ * L * E := by
    simp only [linMse, transpose_add, transpose_mul, transpose_sub, transpose_transpose,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have rhs : (moments K L j).errVar Z = Z * (Eᵀ * K * E - S) * Zᵀ
      - Z * (Eᵀ * L * E - Wᵀ * L * E) - (Eᵀ * L * E - Eᵀ * L * W) * Zᵀ
      + (Eᵀ * L * E - Wᵀ * L * E - Eᵀ * L * W + S) := by
    rw [VecBlendMoments.errVar, moments_gap hK, VecBlendMoments.cross,
      VecBlendMoments.varRest, moments_covEst hK]
    simp only [moments]
    rw [transpose_sub, transpose_add, transpose_sub, h4, h5, hS]
    noncomm_ring
  rw [blendW, key, h1, h2, h3, rhs]
  noncomm_ring

/-- **The price of the matrix blend** (matrix version of `Core.errVar_eq_blupWeight_add`):
the blend with credibility matrix `Z` loses exactly `(A - A*)ᵀK(A - A*)` against the best
linear unbiased predictor, `A = W + (Eⱼ - W)Zᵀ`. -/
theorem errVar_eq_blupW_add [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) (Z : Matrix P P ℝ) :
    (moments K L j).errVar Z = linMse K L j (blupW K L j)
      + (blendW K j Z - blupW K L j)ᵀ * K * (blendW K j Z - blupW K L j) := by
  rw [← linMse_blendW hK hL]
  exact linMse_eq_blupW_add hK hL j (stack_transpose_mul_blendW hK j Z)

/-! #### Separate blends per component (frequency × severity) -/

/-- The covariance across cohorts of the `p`-th components, `(M(i,p),(k,p))ᵢₖ`. -/
def component (M : Matrix (J × P) (J × P) ℝ) (p : P) : Matrix J J ℝ :=
  fun i k => M (i, p) (k, p)

omit [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J] in
/-- The component covariances of a positive definite `K` are positive definite. -/
theorem component_posDef {M : Matrix (J × P) (J × P) ℝ} (hM : M.PosDef) (p : P) :
    (component M p).PosDef :=
  hM.submatrix (e := fun i => (i, p)) fun _ _ h => (Prod.mk.inj h).1

/-- Separate weights: component `p` of the prediction is `Σₖ aₚₖ μ̂ₖₚ`, from the `p`-th
components only. -/
def sepW (a : P → J → ℝ) : Matrix (J × P) P ℝ := fun x q => if x.2 = q then a q x.1 else 0

omit [DecidableEq J] in
/-- Separate weights are unbiased when each component's weights sum to one. -/
theorem stack_transpose_mul_sepW {a : P → J → ℝ} (ha : ∀ p, ∑ k, a p k = 1) :
    (stack J P)ᵀ * sepW a = 1 := by
  ext p q
  simp only [Matrix.mul_apply, transpose_apply, stack, sepW, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul, Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq; simp [ha]
  · simp [hpq]

/-- The error variance of component `p` of separate predictions is the scalar `Core.linMse`
of that component's data alone. -/
theorem linMse_sepW_apply {K L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J)
    (a : P → J → ℝ) (p : P) :
    linMse K L j (sepW a) p p = Core.linMse (component K p) (component L p) j (a p) := by
  have hLs : ∀ x y, L x y = L y x := fun x y => by
    rw [← transpose_apply L y x, hL]
  simp only [linMse, Core.linMse, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    transpose_apply, sepW, sel, component, Fintype.sum_prod_type, dotProduct, mulVec,
    ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, hLs (_, p) (j, p)]
  have e1 : ∑ x, (∑ y, a p y * K (y, p) (x, p)) * a p x
      = ∑ i, a p i * ∑ k, K (i, p) (k, p) * a p k := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, L (j, p) (x, p) * a p x = ∑ x, a p x * L (j, p) (x, p) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e1, e2]
  ring

/-- **Vector credibility beats separate credibility** (frequency × severity): the best
linear unbiased predictor of the level vector has a summed error variance no larger than
that of separate scalar blends, one per component on that component's data alone, whatever
their credibility factors `zₚ`. (The matrix *blend* is not always better: Finding 22.) -/
theorem trace_linMse_blupW_le_separate [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L) (j : J) (z : P → ℝ) :
    (linMse K L j (blupW K L j)).trace
      ≤ ∑ p, (Core.levelMoments (component K p) (component L p) (K (j, p) (j, p)) j).errVar
          (z p) := by
  let a : P → J → ℝ := fun p => Core.blendWeight (component K p) j (z p)
  have ha : ∀ p, ∑ k, a p k = 1 := fun p => Core.sum_blendWeight (component_posDef hK p) j (z p)
  refine (blupW_optimal_trace hK hL j (stack_transpose_mul_sepW ha)).trans_eq ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [diag_apply, linMse_sepW_apply hL j a p]
  exact Core.linMse_blendWeight (component_posDef hK p) (component L p) j (z p)

/-! #### When the matrix blend is the best predictor -/

/-- The first-order condition characterises the best predictor: unbiased weights `A` with
`KA - LEⱼ = UC` for some `C` are `A*`. -/
theorem eq_blupW_of_mul [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) {A : Matrix (J × P) P ℝ} {C : Matrix P P ℝ}
    (hA : (stack J P)ᵀ * A = 1) (hC : K * A - L * sel P j = stack J P * C) :
    A = blupW K L j := by
  set C₀ := (info K)⁻¹ * (1 - (stack J P)ᵀ * K⁻¹ * L * sel P j)
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hK.det_pos.ne'
  have hD : K * (A - blupW K L j) = stack J P * (C - C₀) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hC, ← mul_blupW hK L j]; abel
  have hD' : A - blupW K L j = K⁻¹ * stack J P * (C - C₀) := by
    rw [Matrix.mul_assoc, ← hD, ← Matrix.mul_assoc, nonsing_inv_mul _ hKu, Matrix.one_mul]
  have h0 : info K * (C - C₀) = 0 := by
    have : (stack J P)ᵀ * (A - blupW K L j) = 0 := by
      rw [Matrix.mul_sub, hA, stack_transpose_mul_blupW hK, sub_self]
    rw [hD'] at this
    simpa [info, Matrix.mul_assoc] using this
  have hC0 : C - C₀ = 0 := by
    have hi : IsUnit (info K).det := isUnit_iff_ne_zero.2 (info_posDef hK).det_pos.ne'
    rw [← Matrix.one_mul (C - C₀), ← nonsing_inv_mul _ hi, Matrix.mul_assoc, h0,
      Matrix.mul_zero]
  rw [← sub_eq_zero, hD', hC0, Matrix.mul_zero]

/-- `K(W + (Eⱼ - W)Zᵀ) = U(S - SZᵀ) + KEⱼZᵀ` with `S = (UᵀK⁻¹U)⁻¹`. -/
theorem mul_blendW {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef) (j : J) (Z : Matrix P P ℝ) :
    K * blendW K j Z
      = stack J P * ((info K)⁻¹ - (info K)⁻¹ * Zᵀ) + K * sel P j * Zᵀ := by
  rw [blendW, Matrix.mul_add, mul_glsW hK, ← Matrix.mul_assoc, Matrix.mul_sub, mul_glsW hK]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **When the matrix blend is the best predictor** (matrix version of
`Core.blendWeight_eq_blupWeight_iff`): the blend with credibility matrix `Z` is the best
linear unbiased predictor iff `LEⱼ - KEⱼZᵀ = UC` for some `C`, i.e. the block
`cov(x, μⱼ) - cov(x, μ̂ⱼ)Zᵀ` is the same for every cohort. -/
theorem blendW_eq_blupW_iff [Nonempty J] {K : Matrix (J × P) (J × P) ℝ} (hK : K.PosDef)
    (L : Matrix (J × P) (J × P) ℝ) (j : J) (Z : Matrix P P ℝ) :
    blendW K j Z = blupW K L j
      ↔ ∃ C : Matrix P P ℝ, L * sel P j - K * sel P j * Zᵀ = stack J P * C := by
  constructor
  · intro h
    have h1 := mul_blupW hK L j
    rw [← h, mul_blendW hK] at h1
    have h2 : L * sel P j - K * sel P j * Zᵀ = stack J P * ((info K)⁻¹ - (info K)⁻¹ * Zᵀ)
        - stack J P * ((info K)⁻¹ * (1 - (stack J P)ᵀ * K⁻¹ * L * sel P j)) := by
      rw [← h1]; abel
    exact ⟨_, h2.trans (Matrix.mul_sub _ _ _).symm⟩
  · rintro ⟨C, hC⟩
    have h2 : K * blendW K j Z - L * sel P j
        = stack J P * ((info K)⁻¹ - (info K)⁻¹ * Zᵀ) - stack J P * C := by
      rw [mul_blendW hK, ← hC]; abel
    exact (eq_blupW_of_mul hK L j (stack_transpose_mul_blendW hK j Z)
      (h2.trans (Matrix.mul_sub _ _ _).symm))

/-- For a block-diagonal `M`, `MEⱼ = EⱼMⱼⱼ`. -/
theorem mul_sel_of_blockDiag {M : Matrix (J × P) (J × P) ℝ} (hM : IsCohortBlockDiag M)
    (j : J) : M * sel P j = sel P j * blk M j := by
  ext ⟨i, p⟩ q
  by_cases hij : i = j
  · subst hij
    simp [Matrix.mul_apply, sel, blk, Fintype.sum_prod_type, ite_and]
  · simp [Matrix.mul_apply, sel, blk, Fintype.sum_prod_type, ite_and, hij, hM i j hij]

/-- **Independent cohorts: the matrix blend with `Zⱼ = LⱼⱼKⱼⱼ⁻¹` is the best linear
unbiased predictor** (multidimensional Bühlmann–Straub: `Λ(Λ + Sⱼ)⁻¹`, Bühlmann & Gisler
2005, §7.3). -/
theorem blendW_eq_blupW_of_blockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L)
    (hLb : IsCohortBlockDiag L) (j : J) :
    blendW K j (blk L j * (blk K j)⁻¹) = blupW K L j := by
  have hsym : ∀ {M : Matrix P P ℝ}, M.PosDef → Mᵀ = M := fun h => by
    simpa [conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq
  have hLj : (blk L j)ᵀ = blk L j := by
    ext p q; exact (congrFun (congrFun hL (j, q)) (j, p)).symm
  have hKj : IsUnit (blk K j).det := isUnit_iff_ne_zero.2 (blk_posDef hK j).det_pos.ne'
  refine (blendW_eq_blupW_iff hK L j _).mpr ⟨0, ?_⟩
  rw [mul_sel_of_blockDiag hLb, mul_sel_of_blockDiag hb, transpose_mul, hLj,
    hsym (blk_posDef hK j).inv, Matrix.mul_assoc (sel P j), ← Matrix.mul_assoc (blk K j),
    mul_nonsing_inv _ hKj, Matrix.one_mul, sub_self]
  exact (Matrix.mul_zero _).symm

/-- …so with another cohort the best matrix blend *is* the best linear unbiased predictor:
for independent cohorts nothing is lost by blending (contrast Finding 22). -/
theorem blendW_bestZ_eq_blupW_of_blockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) {L : Matrix (J × P) (J × P) ℝ} (hL : Lᵀ = L)
    (hLb : IsCohortBlockDiag L) {i j : J} (hij : i ≠ j) :
    blendW K j (moments K L j).bestZ = blupW K L j := by
  rw [moments_bestZ_of_blockDiag hK hb hL hLb hij, blendW_eq_blupW_of_blockDiag hK hb hL hLb]

/-- `M` has no covariance between different components (e.g. frequency and severity). -/
def IsComponentBlockDiag (M : Matrix (J × P) (J × P) ℝ) : Prop :=
  ∀ i k p q, p ≠ q → M (i, p) (k, q) = 0

/-- **No cross-component covariance: the vector BLUP is the separate BLUPs.** If neither the
estimates nor the levels are correlated across components, the best linear unbiased
predictor of the level vector predicts each component by the scalar BLUP
(`Core.blupWeight`) of that component's data alone: the other components carry no
information. -/
theorem blupW_eq_sepW_of_componentBlockDiag [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hKc : IsComponentBlockDiag K) {L : Matrix (J × P) (J × P) ℝ}
    (hL : Lᵀ = L) (hLc : IsComponentBlockDiag L) (j : J) :
    blupW K L j = sepW fun p => Core.blupWeight (component K p) (component L p) j := by
  set c : P → ℝ := fun p => (1 - 1 ⬝ᵥ ((component K p)⁻¹ *ᵥ component L p j))
    * (invTotal (component K p))⁻¹
  refine (eq_blupW_of_mul hK L j (stack_transpose_mul_sepW fun p =>
    Core.sum_blupWeight (component_posDef hK p) _ j) (C := diagonal c) ?_).symm
  ext ⟨i, p⟩ q
  have hLs : L (i, p) (j, q) = L (j, q) (i, p) := congrFun (congrFun hL (j, q)) (i, p)
  by_cases hpq : p = q
  · subst hpq
    have h := Core.mulVec_blupWeight (component_posDef hK p) (component L p) j i
    simp only [mulVec, dotProduct, component] at h
    simp [Matrix.mul_apply, sepW, sel, stack, Fintype.sum_prod_type, ite_and, hLs, c, h,
      dotProduct, mulVec, component]
  · simp [Matrix.mul_apply, sepW, sel, stack, Fintype.sum_prod_type, ite_and, hpq,
      hLc i j p q hpq, hKc i _ p q hpq]

/-! ### Balance (§2.9) for the matrix blend

The matrix blends `μ̂ⱼᵇ = μ̂ + Zⱼ(μ̂ⱼ - μ̂)` with `μ̂ = Σᵢ Bᵢμ̂ᵢ`, `Σᵢ Bᵢ = I`, are balanced
for matrix weights `Uⱼ` (e.g. `uⱼI` for a volume `uⱼ`) if `Σⱼ Uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = 0` for all
data. As in `Core.balanced_iff`, pure algebra: it holds exactly when `Uⱼ(I - Zⱼ) = CBⱼ` for
one matrix `C`. -/

/-- The matrix blends `μ̂ + Zⱼ(μ̂ⱼ - μ̂)`, `μ̂ = Σᵢ Bᵢμ̂ᵢ`, are balanced for the weights `Uⱼ`:
`Σⱼ Uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = 0` for every data `μ̂ⱼ ∈ ℝᴾ` (matrix version of `Core.Balanced`). -/
def VecBalanced (U Z B : J → Matrix P P ℝ) : Prop :=
  ∀ m : J → P → ℝ,
    ∑ j, U j *ᵥ (m j - (∑ i, B i *ᵥ m i + Z j *ᵥ (m j - ∑ i, B i *ᵥ m i))) = 0

/-- **Balance for any matrix blend** (matrix version of `Core.balanced_iff`): with
`Σⱼ Bⱼ = I`, the blends are balanced for the weights `Uⱼ` iff `Uⱼ(I - Zⱼ) = CBⱼ` for some
matrix `C`. -/
theorem vecBalanced_iff (U Z B : J → Matrix P P ℝ) (hB : ∑ j, B j = 1) :
    VecBalanced U Z B ↔ ∃ C : Matrix P P ℝ, ∀ j, U j * (1 - Z j) = C * B j := by
  set A : J → Matrix P P ℝ := fun j => U j * (1 - Z j) with hA
  -- `Σⱼ Uⱼ(μ̂ⱼ - μ̂ⱼᵇ) = Σⱼ (Aⱼ - (Σᵢ Aᵢ)Bⱼ) μ̂ⱼ`
  have key : ∀ m : J → P → ℝ,
      ∑ j, U j *ᵥ (m j - (∑ i, B i *ᵥ m i + Z j *ᵥ (m j - ∑ i, B i *ᵥ m i)))
        = ∑ j, (A j - (∑ i, A i) * B j) *ᵥ m j := by
    intro m
    have h1 : ∀ j, U j *ᵥ (m j - (∑ i, B i *ᵥ m i + Z j *ᵥ (m j - ∑ i, B i *ᵥ m i)))
        = A j *ᵥ m j - A j *ᵥ ∑ i, B i *ᵥ m i := fun j => by
      simp only [hA, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, mulVec_sub, mulVec_add,
        ← mulVec_mulVec]
      abel
    have h2 : ∑ j, A j *ᵥ ∑ i, B i *ᵥ m i = ∑ j, ((∑ i, A i) * B j) *ᵥ m j := by
      rw [← sum_mulVec, mulVec_sum]
      simp only [mulVec_mulVec]
    simp only [h1, Finset.sum_sub_distrib, h2, sub_mulVec]
  have hsingle : ∀ (D : J → Matrix P P ℝ) (k : J) (v : P → ℝ),
      ∑ j, D j *ᵥ Pi.single (M := fun _ => P → ℝ) k v j = D k *ᵥ v := fun D k v => by
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mulVec_zero])
      (by simp), Pi.single_eq_same]
  simp only [VecBalanced, key]
  constructor
  · intro h
    refine ⟨∑ i, A i, fun k => ?_⟩
    rw [← sub_eq_zero]
    ext p q
    have := congrFun (h (Pi.single k (Pi.single q 1))) p
    rw [hsingle] at this
    simpa using this
  · rintro ⟨C, hC⟩ m
    have hsum : ∑ i, A i = C := by
      simp only [hA, hC, ← Finset.mul_sum, hB, Matrix.mul_one]
    rw [hsum]
    simp [hA, hC]

/-- **Multidimensional Bühlmann–Straub is balanced for the volumes.** Independent cohorts
with `Var(μ̂ⱼ) = Λ + S₀/wⱼ` (`S₀` the noise covariance per unit volume) and the credibility
matrices `Zⱼ = Λ(Λ + S₀/wⱼ)⁻¹` (the best ones, `moments_bestZ_buhlmannGisler`) with the GLS
portfolio are balanced for the volumes: `Σⱼ wⱼ(μ̂ⱼ - μ̂ⱼᵇ) = 0` (vector version of the
Bühlmann–Straub balance, `Core.balanced_iff_of_diag`). -/
theorem vecBalanced_buhlmannGisler [Nonempty J] {K : Matrix (J × P) (J × P) ℝ}
    (hK : K.PosDef) (hb : IsCohortBlockDiag K) {Λ S₀ : Matrix P P ℝ} {w : J → ℝ}
    (hw : ∀ j, w j ≠ 0) (hKj : ∀ j, blk K j = Λ + (w j)⁻¹ • S₀) :
    VecBalanced (fun j => w j • (1 : Matrix P P ℝ)) (fun j => Λ * (Λ + (w j)⁻¹ • S₀)⁻¹)
      (weight K) := by
  refine (vecBalanced_iff _ _ _ (sum_weight hK)).mpr ⟨S₀ * ∑ i, (blk K i)⁻¹, fun j => ?_⟩
  have hu : IsUnit (blk K j).det := isUnit_iff_ne_zero.2 (blk_posDef hK j).det_pos.ne'
  have hI : IsUnit (∑ i, (blk K i)⁻¹).det := by
    rw [← info_of_blockDiag hK hb]
    exact isUnit_iff_ne_zero.2 (info_posDef hK).det_pos.ne'
  -- `I - Λ(Λ + S)⁻¹ = S(Λ + S)⁻¹`
  have h1 : 1 - Λ * (blk K j)⁻¹ = (w j)⁻¹ • S₀ * (blk K j)⁻¹ := by
    rw [← mul_nonsing_inv _ hu]
    nth_rewrite 1 [hKj j]
    rw [Matrix.add_mul, add_sub_cancel_left]
  rw [weight_of_blockDiag hK hb, ← Matrix.mul_assoc, Matrix.mul_assoc S₀,
    mul_nonsing_inv _ hI, Matrix.mul_one, ← hKj, h1, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, mul_inv_cancel₀ (hw j), one_smul]

end CoreVector
end Credibility
