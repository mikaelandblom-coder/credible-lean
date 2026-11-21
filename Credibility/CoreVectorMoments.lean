import Credibility.CoreVector
import Credibility.CoreMoments

/-!
# The moment layer for the matrix Blend (extension, distribution-free)

`CoreVector.lean` takes the joint covariance `K` of the stacked cohort estimates
`x = (μ̂ⱼₚ)` over cohorts × components and the covariance `L` of the stacked levels
`(μⱼₚ)` as given matrices. Here they become actual covariances: **any** square-integrable
random variables `μ̂ⱼₚ` (`est`) and `μⱼₚ` (`level`) whose component `p` has mean `mₚ` (the
same for all cohorts), with `cov(μ̂ᵢ, μ̂ₖ) = K`, `cov(μᵢ, μ̂ₖ) = cov(μᵢ, μₖ) = L` entrywise
(`CoreVector.VecEstimates`). Then for every unbiased linear predictor `Aᵀx` (`UᵀA = I`)
the error `Aᵀx - μⱼ` has mean `0` and true error covariance `E[(Aᵀx - μⱼ)(Aᵀx - μⱼ)ᵀ]`
equal to `linMse K L j A`; for the matrix blend `μ̂ + Z(μ̂ⱼ - μ̂)` it is
`(moments K L j).errVar Z`. So the BLUP and `bestZ` results of `CoreVector` are statements
about real random vectors.

Nothing is re-proved: centring each component by its mean gives a `Core.Estimates K L 0`
over the index set `J × P` (`VecEstimates.centred`), and each entry of the error covariance
is a covariance of two linear combinations there (`Core.Estimates.cov_portLin_sub_level`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Core.Estimates

variable {J : Type*} [Fintype J] {K L : Matrix J J ℝ} {μ : ℝ} {Pr : Measure Ω}
  (E : Estimates K L μ Pr)

omit [Fintype J] in
include E in
/-- The level covariance is symmetric: `L = cov(μᵢ, μₖ)`. -/
lemma transpose_L : Lᵀ = L := by
  ext i k
  rw [transpose_apply, ← E.cov_level, ← E.cov_level, covariance_comm]

variable [IsProbabilityMeasure Pr]

/-- The covariance of the errors of two linear predictors `Σ dₓ μ̂ₓ - μᵢ` and
`Σ d'ₓ μ̂ₓ - μₖ`: `dᵀK d' - (L d)ₖ - (L d')ᵢ + Lᵢₖ`. -/
lemma cov_portLin_sub_level (d d' : J → ℝ) (i k : J) :
    cov[fun ω => E.portLin d ω - E.level i ω, fun ω => E.portLin d' ω - E.level k ω; Pr]
      = d ⬝ᵥ (K *ᵥ d') - (L *ᵥ d) k - (L *ᵥ d') i + L i k := by
  rw [show (fun ω => E.portLin d ω - E.level i ω) = E.portLin d - E.level i from rfl,
    show (fun ω => E.portLin d' ω - E.level k ω) = E.portLin d' - E.level k from rfl,
    covariance_sub_left (E.memLp_portLin d) (E.level_memLp i)
      ((E.memLp_portLin d').sub (E.level_memLp k)),
    covariance_sub_right (E.memLp_portLin d) (E.memLp_portLin d') (E.level_memLp k),
    covariance_sub_right (E.level_memLp i) (E.memLp_portLin d') (E.level_memLp k),
    cov_portLin, covariance_comm (E.portLin d), cov_level_portLin, cov_level_portLin, E.cov_level]
  ring

end Core.Estimates

namespace CoreVector

variable {J P : Type*} [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P]

/-- `(MEⱼ)ₓᵣ = M_{x,(j,r)}`. -/
theorem mul_sel_apply {n : Type*} (M : Matrix n (J × P) ℝ) (j : J) (x : n) (r : P) :
    (M * sel P j) x r = M x (j, r) := by
  simp [Matrix.mul_apply, sel, Fintype.sum_prod_type, ite_and]

/-- `(EⱼᵀM)ₚᵧ = M_{(j,p),y}`. -/
theorem sel_transpose_mul_apply {n : Type*} (M : Matrix (J × P) n ℝ) (j : J) (p : P) (y : n) :
    ((sel P j)ᵀ * M) p y = M (j, p) y := by
  simp [Matrix.mul_apply, sel, Fintype.sum_prod_type, ite_and]

/-- `Eⱼᵀx = xⱼ`. -/
theorem sel_transpose_mulVec (j : J) (v : J × P → ℝ) :
    (sel P j)ᵀ *ᵥ v = fun q => v (j, q) := by
  ext q
  simp [mulVec, dotProduct, sel, Fintype.sum_prod_type, ite_and]

/-- Stacked cohort estimates `μ̂ⱼₚ` (`est`) and levels `μⱼₚ` (`level`) under `Pr`: square
integrable, component `p` with mean `mₚ` in every cohort, `cov(μ̂ₓ, μ̂_y) = K_xy` and
`cov(μₓ, μ̂_y) = cov(μₓ, μ_y) = L_xy` (an estimate differs from its level by noise
uncorrelated with all levels). Only moments are assumed, no distribution. -/
structure VecEstimates (K L : Matrix (J × P) (J × P) ℝ) (m : P → ℝ) (Pr : Measure Ω) where
  /-- The estimate `μ̂ⱼₚ` of component `p` of cohort `j`. -/
  est : J × P → Ω → ℝ
  /-- The level `μⱼₚ`. -/
  level : J × P → Ω → ℝ
  est_memLp : ∀ x, MemLp (est x) 2 Pr
  level_memLp : ∀ x, MemLp (level x) 2 Pr
  est_mean : ∀ x, Pr[est x] = m x.2
  level_mean : ∀ x, Pr[level x] = m x.2
  cov_est : ∀ x y, cov[est x, est y; Pr] = K x y
  cov_level_est : ∀ x y, cov[level x, est y; Pr] = L x y
  cov_level : ∀ x y, cov[level x, level y; Pr] = L x y

namespace VecEstimates

variable {K L : Matrix (J × P) (J × P) ℝ} {m : P → ℝ} {Pr : Measure Ω}
  (E : VecEstimates K L m Pr)

/-- The stacked estimate vector `x(ω)`. -/
def vec (ω : Ω) : J × P → ℝ := fun x => E.est x ω

/-- The error `Aᵀx - μⱼ` of the linear predictor with weights `A`, as a random vector. -/
def err (A : Matrix (J × P) P ℝ) (j : J) (ω : Ω) : P → ℝ :=
  Aᵀ *ᵥ E.vec ω - fun p => E.level (j, p) ω

/-- The error covariance `E[(Y - μⱼ)(Y - μⱼ)ᵀ]` (matrix MSE) of a random vector `Y`
predicting `μⱼ`. -/
noncomputable def mse (j : J) (Y : Ω → P → ℝ) : Matrix P P ℝ :=
  fun p r => Pr[fun ω => (Y ω p - E.level (j, p) ω) * (Y ω r - E.level (j, r) ω)]

/-- The matrix GLS portfolio estimate `μ̂ = Wᵀx = Σⱼ Bⱼ μ̂ⱼ`. -/
noncomputable def portEst (ω : Ω) : P → ℝ := (glsW K)ᵀ *ᵥ E.vec ω

/-- The matrix blend `μ̂ + Z(μ̂ⱼ - μ̂)`. -/
noncomputable def blend (j : J) (Z : Matrix P P ℝ) (ω : Ω) : P → ℝ :=
  E.portEst ω + Z *ᵥ ((fun q => E.est (j, q) ω) - E.portEst ω)

/-- The blend is the linear predictor with weights `blendW K j Z = W + (Eⱼ - W)Zᵀ`. -/
theorem blend_eq (j : J) (Z : Matrix P P ℝ) (ω : Ω) :
    E.blend j Z ω = (blendW K j Z)ᵀ *ᵥ E.vec ω := by
  rw [blend, portEst, blendW, transpose_add, transpose_mul, transpose_transpose, add_mulVec,
    ← mulVec_mulVec, transpose_sub, sub_mulVec, sel_transpose_mulVec]
  rfl

variable [IsProbabilityMeasure Pr]

/-- Centring each component at its mean gives cohort estimates over `J × P` with common
mean `0` and the same covariances `K`, `L`. -/
noncomputable def centred : Core.Estimates K L 0 Pr where
  est x ω := E.est x ω - m x.2
  level x ω := E.level x ω - m x.2
  est_memLp x := (E.est_memLp x).sub (memLp_const _)
  level_memLp x := (E.level_memLp x).sub (memLp_const _)
  est_mean x := by
    rw [integral_sub ((E.est_memLp x).integrable (by norm_num)) (integrable_const _),
      E.est_mean]
    simp
  level_mean x := by
    rw [integral_sub ((E.level_memLp x).integrable (by norm_num)) (integrable_const _),
      E.level_mean]
    simp
  cov_est x y := by
    rw [covariance_sub_const_left ((E.est_memLp x).integrable (by norm_num)),
      covariance_sub_const_right ((E.est_memLp y).integrable (by norm_num)), E.cov_est]
  cov_level_est x y := by
    rw [covariance_sub_const_left ((E.level_memLp x).integrable (by norm_num)),
      covariance_sub_const_right ((E.est_memLp y).integrable (by norm_num)), E.cov_level_est]
  cov_level x y := by
    rw [covariance_sub_const_left ((E.level_memLp x).integrable (by norm_num)),
      covariance_sub_const_right ((E.level_memLp y).integrable (by norm_num)), E.cov_level]

omit [IsProbabilityMeasure Pr] [DecidableEq J] in
/-- Unbiased weights reproduce the means: `UᵀA = I` gives `Σₓ Aₓₚ m_{x₂} = mₚ`. -/
theorem sum_mul_mean {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) (p : P) :
    ∑ x, A x p * m x.2 = m p := by
  have h : ∀ q, ∑ x : J × P, (if x.2 = q then A x p else 0) = if q = p then 1 else 0 := by
    intro q
    have := congrFun (congrFun hA q) p
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [stack] using this
  calc ∑ x, A x p * m x.2 = ∑ q, ∑ x : J × P, (if x.2 = q then A x p else 0) * m q := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun x _ => ?_
        simp [ite_mul]
    _ = m p := by simp only [← sum_mul, h]; simp

omit [DecidableEq J] in
/-- An unbiased linear predictor's error is the centred one's. -/
theorem err_eq {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) (j : J) (ω : Ω) (p : P) :
    E.err A j ω p = E.centred.portLin (fun x => A x p) ω - E.centred.level (j, p) ω := by
  have h := sum_mul_mean (m := m) hA p
  simp only [err, vec, Pi.sub_apply, mulVec, dotProduct, transpose_apply, centred,
    Core.Estimates.portLin, Core.portLin, mul_sub, sum_sub_distrib] at h ⊢
  rw [h]
  ring

omit [DecidableEq J] in
/-- **The moment layer for linear predictors**: an unbiased linear predictor `Aᵀx`
(`UᵀA = I`) of `μⱼ` has error of mean `0`… -/
theorem integral_err {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) (j : J) (p : P) :
    Pr[fun ω => E.err A j ω p] = 0 := by
  simp_rw [E.err_eq hA]
  rw [integral_sub ((E.centred.memLp_portLin _).integrable (by norm_num))
    ((E.centred.level_memLp _).integrable (by norm_num)), E.centred.integral_portLin,
    E.centred.level_mean]
  simp

/-- …and true error covariance `E[(Aᵀx - μⱼ)(Aᵀx - μⱼ)ᵀ] = linMse K L j A`, for every
distribution with these moments. -/
theorem mse_linear {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) (j : J) :
    E.mse j (fun ω => Aᵀ *ᵥ E.vec ω) = linMse K L j A := by
  ext p r
  have hL := E.centred.transpose_L
  have hX : ∀ p, MemLp (fun ω => E.err A j ω p) 2 Pr := fun p => by
    simp_rw [E.err_eq hA]
    exact (E.centred.memLp_portLin _).sub (E.centred.level_memLp _)
  have key : Pr[fun ω => E.err A j ω p * E.err A j ω r]
      = cov[fun ω => E.err A j ω p, fun ω => E.err A j ω r; Pr] := by
    rw [covariance_eq_sub (hX p) (hX r), E.integral_err hA, E.integral_err hA]
    simp
  have hcov := E.centred.cov_portLin_sub_level (fun x => A x p) (fun x => A x r) (j, p) (j, r)
  simp_rw [← E.err_eq hA] at hcov
  change Pr[fun ω => E.err A j ω p * E.err A j ω r] = _
  rw [key, hcov, linMse, Matrix.mul_assoc (sel P j)ᵀ L A]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_sel_apply, sel_transpose_mul_apply]
  congr 1
  congr 1
  · congr 1
    · simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    · simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec]
      exact sum_congr rfl fun x _ => by rw [← transpose_apply L x (j, r), hL]; ring

/-- **The true MSE of the matrix blend**: `E[(blend - μⱼ)(blend - μⱼ)ᵀ] = errVar Z` for the
moments `moments K L j`, for every distribution with these moments. -/
theorem mse_blend [Nonempty J] (hK : K.PosDef) (j : J) (Z : Matrix P P ℝ) :
    E.mse j (E.blend j Z) = (moments K L j).errVar Z := by
  rw [show E.blend j Z = fun ω => (blendW K j Z)ᵀ *ᵥ E.vec ω from funext (E.blend_eq j Z),
    E.mse_linear (stack_transpose_mul_blendW hK j Z), linMse_blendW hK E.centred.transpose_L]

/-- **The BLUP in true MSE**: among all unbiased linear predictors `Aᵀx` (`UᵀA = I`), the
weights `blupW` minimise the true error covariance in the Loewner order. -/
theorem blup_mse_optimal [Nonempty J] (hK : K.PosDef) (j : J) {A : Matrix (J × P) P ℝ}
    (hA : (stack J P)ᵀ * A = 1) :
    (E.mse j (fun ω => Aᵀ *ᵥ E.vec ω)
      - E.mse j (fun ω => (blupW K L j)ᵀ *ᵥ E.vec ω)).PosSemidef := by
  rw [E.mse_linear hA, E.mse_linear (stack_transpose_mul_blupW hK L j)]
  exact blupW_optimal hK E.centred.transpose_L j hA

/-- **The price of the matrix blend in true MSE**: the blend loses exactly
`(A - A*)ᵀK(A - A*)` against the BLUP, `A = W + (Eⱼ - W)Zᵀ`. -/
theorem mse_blend_eq_blup_add [Nonempty J] (hK : K.PosDef) (j : J) (Z : Matrix P P ℝ) :
    E.mse j (E.blend j Z) = E.mse j (fun ω => (blupW K L j)ᵀ *ᵥ E.vec ω)
      + (blendW K j Z - blupW K L j)ᵀ * K * (blendW K j Z - blupW K L j) := by
  rw [E.mse_blend hK, E.mse_linear (stack_transpose_mul_blupW hK L j)]
  exact errVar_eq_blupW_add hK E.centred.transpose_L j Z

/-- **Matrix eq. (26) in true MSE**: when `Var(μ̂ⱼ - μ̂)` is positive definite
(`moments_gap_posDef_iff`), the best credibility matrix `bestZ` (`moments_bestZ`) minimises
the true error covariance of the blend in the Loewner order. -/
theorem bestZ_mse_optimal [Nonempty J] (hK : K.PosDef) (j : J)
    (hg : (moments K L j).gap.PosDef) (Z : Matrix P P ℝ) :
    (E.mse j (E.blend j Z) - E.mse j (E.blend j (moments K L j).bestZ)).PosSemidef := by
  have hKt : Kᵀ = K := by simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hS : ((info K)⁻¹)ᵀ = (info K)⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using (info_posDef hK).inv.isHermitian.eq
  rw [E.mse_blend hK, E.mse_blend hK]
  exact (moments K L j).bestZ_optimal
    (by simp [moments, transpose_mul, hKt, Matrix.mul_assoc]) hS hg.posSemidef
    (isUnit_iff_ne_zero.2 hg.det_pos.ne') Z


omit [DecidableEq J] in
/-- **The bias of a product of predictions is exact** (e.g. frequency × severity: the pure
premium). For unbiased weights `A` (`UᵀA = I`) and components `p`, `r`,
`E[(Aᵀx)ₚ(Aᵀx)ᵣ] - E[μⱼₚμⱼᵣ] = (AᵀKA)ₚᵣ - L₍ⱼₚ₎₍ⱼᵣ₎`: the covariance of the two predictions
minus that of the two levels. No delta method and no distribution: only `E[XY] = EX·EY +
cov(X, Y)`. -/
theorem integral_mul_pred_sub {A : Matrix (J × P) P ℝ} (hA : (stack J P)ᵀ * A = 1) (j : J)
    (p r : P) :
    Pr[fun ω => (Aᵀ *ᵥ E.vec ω) p * (Aᵀ *ᵥ E.vec ω) r]
        - Pr[fun ω => E.level (j, p) ω * E.level (j, r) ω]
      = (Aᵀ * K * A) p r - L (j, p) (j, r) := by
  have hpred : ∀ q, (fun ω => (Aᵀ *ᵥ E.vec ω) q)
      = fun ω => E.centred.portLin (fun x => A x q) ω + m q := by
    intro q; funext ω
    have h := sum_mul_mean (m := m) hA q
    simp only [vec, mulVec, dotProduct, transpose_apply, centred, Core.Estimates.portLin,
      Core.portLin, mul_sub, sum_sub_distrib] at h ⊢
    rw [h]; ring
  have hm : ∀ q, MemLp (fun ω => (Aᵀ *ᵥ E.vec ω) q) 2 Pr := fun q => by
    rw [hpred]; exact (E.centred.memLp_portLin _).add (memLp_const _)
  have hi : ∀ q, Pr[fun ω => (Aᵀ *ᵥ E.vec ω) q] = m q := fun q => by
    rw [hpred, integral_add ((E.centred.memLp_portLin _).integrable (by norm_num))
      (integrable_const _), E.centred.integral_portLin]
    simp
  have hc : cov[fun ω => (Aᵀ *ᵥ E.vec ω) p, fun ω => (Aᵀ *ᵥ E.vec ω) r; Pr]
      = (fun x => A x p) ⬝ᵥ (K *ᵥ fun x => A x r) := by
    rw [hpred, hpred, covariance_add_const_left
      ((E.centred.memLp_portLin _).integrable (by norm_num)),
      covariance_add_const_right ((E.centred.memLp_portLin _).integrable (by norm_num)),
      E.centred.cov_portLin]
  have e1 := covariance_eq_sub (hm p) (hm r)
  have e2 := covariance_eq_sub (E.level_memLp (j, p)) (E.level_memLp (j, r))
  rw [hc, hi, hi] at e1
  rw [E.cov_level, E.level_mean, E.level_mean] at e2
  change _ = Pr[fun ω => (Aᵀ *ᵥ E.vec ω) p * (Aᵀ *ᵥ E.vec ω) r] - _ at e1
  change _ = Pr[fun ω => E.level (j, p) ω * E.level (j, r) ω] - _ at e2
  have hq : (fun x => A x p) ⬝ᵥ (K *ᵥ fun x => A x r) = (Aᵀ * K * A) p r := by
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  simp only at e2
  linarith [hq]

end VecEstimates

end CoreVector

end Credibility
