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
about real random vectors. `integral_spread` gives the expected weighted spread of vector
estimates under any noise covariance between cohorts, and `integral_correctedLambda` that the
moment `Λ̂` corrected by an unbiased `N̂` is unbiased (S67).

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

/-- **The expected weighted spread of vector estimates** (S67's corrected moment identity for
`Λ̂`). Random vectors `β̂ⱼ` (`est (j, p)`), square integrable with a common mean `b`, and
`cov(β̂ⱼₚ, β̂ᵢᵣ) = δⱼᵢΛₚᵣ + (Nⱼᵢ)ₚᵣ`: the cohorts' own variation `Λ` plus any noise covariance
`N`, within and between cohorts. For weights `ω` with `Σⱼ ωⱼ = 1` and `β̄ = Σⱼ ωⱼβ̂ⱼ`,
`E Σⱼ ωⱼ(β̂ⱼ - β̄)(β̂ⱼ - β̄)ᵀ = (1 - Σⱼ ωⱼ²)Λ + Σⱼ ωⱼNⱼⱼ - Σᵢ Σₖ ωᵢωₖNᵢₖ`. So the corrected
`Λ̂ = (S - Σⱼ ωⱼN̂ⱼⱼ + Σᵢ Σₖ ωᵢωₖN̂ᵢₖ) / (1 - Σⱼ ωⱼ²)` is unbiased for every noise covariance
`N` it is given unbiased estimates of. Only moments, no distribution. -/
theorem integral_spread {Pr : Measure Ω} [IsProbabilityMeasure Pr] (est : J × P → Ω → ℝ)
    (b : P → ℝ) (Λ : Matrix P P ℝ) (N : J → J → Matrix P P ℝ)
    (hL2 : ∀ x, MemLp (est x) 2 Pr) (hmean : ∀ x, Pr[est x] = b x.2)
    (hcov : ∀ j i p r, cov[est (j, p), est (i, r); Pr] = (if j = i then Λ p r else 0) + N j i p r)
    (w : J → ℝ) (hw : ∑ j, w j = 1) :
    Matrix.of (fun p r => Pr[fun ω => ∑ j, w j * ((est (j, p) ω - ∑ k, w k * est (k, p) ω)
        * (est (j, r) ω - ∑ k, w k * est (k, r) ω))])
      = (1 - ∑ j, w j ^ 2) • Λ + ∑ j, w j • N j j - ∑ i, ∑ k, (w i * w k) • N i k := by
  ext p r
  rw [Matrix.of_apply]
  set a : J → J → ℝ := fun j k => (if k = j then 1 else 0) - w k with ha
  have hD : ∀ j q ω, est (j, q) ω - ∑ k, w k * est (k, q) ω = ∑ k, a j k * est (k, q) ω := by
    intro j q ω
    simp [ha, sub_mul, sum_sub_distrib, ite_mul]
  have hsa : ∀ j, ∑ k, a j k = 0 := fun j => by simp [ha, sum_sub_distrib, hw]
  -- the centred variables as `Core.Estimates` over `J × P` (level = estimate)
  let C : Matrix (J × P) (J × P) ℝ := Matrix.of fun x y => cov[est x, est y; Pr]
  have hcen : ∀ x, MemLp (fun ω => est x ω - b x.2) 2 Pr := fun x =>
    (hL2 x).sub (memLp_const _)
  have hcc : ∀ x y, cov[fun ω => est x ω - b x.2, fun ω => est y ω - b y.2; Pr] = C x y :=
    fun x y => by
      rw [covariance_sub_const_left ((hL2 x).integrable (by norm_num)),
        covariance_sub_const_right ((hL2 y).integrable (by norm_num))]
      rfl
  have hcm : ∀ x, Pr[fun ω => est x ω - b x.2] = 0 := fun x => by
    rw [integral_sub ((hL2 x).integrable (by norm_num)) (integrable_const _), hmean]
    simp
  let E : Core.Estimates C C 0 Pr :=
    { est := fun x ω => est x ω - b x.2, level := fun x ω => est x ω - b x.2,
      est_memLp := hcen, level_memLp := hcen, est_mean := hcm, level_mean := hcm,
      cov_est := hcc, cov_level_est := hcc, cov_level := hcc }
  set d : J → P → J × P → ℝ := fun j q x => if x.2 = q then a j x.1 else 0 with hd
  have hE : ∀ j q ω, ∑ k, a j k * est (k, q) ω = E.portLin (d j q) ω := by
    intro j q ω
    simp only [Core.Estimates.portLin, Core.portLin, E, hd, Fintype.sum_prod_type, ite_mul,
      zero_mul, sum_ite_eq', mem_univ, ite_true, mul_sub, sum_sub_distrib, ← sum_mul, hsa]
    ring
  have hm : ∀ j q, MemLp (fun ω => ∑ k, a j k * est (k, q) ω) 2 Pr := fun j q => by
    simp_rw [hE]; exact E.memLp_portLin _
  have hc : ∀ j, Pr[fun ω => (∑ k, a j k * est (k, p) ω) * ∑ k, a j k * est (k, r) ω]
      = ∑ k, ∑ l, a j k * a j l * ((if k = l then Λ p r else 0) + N k l p r) := by
    intro j
    have e := covariance_eq_sub (E.memLp_portLin (d j p)) (E.memLp_portLin (d j r))
    rw [E.integral_portLin, E.integral_portLin, mul_zero, mul_zero, mul_zero, sub_zero,
      E.cov_portLin] at e
    simp only [Pi.mul_apply] at e
    simp_rw [hE]
    rw [← e]
    simp only [dotProduct, mulVec, hd, C, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul, sum_ite_eq', mem_univ, ite_true, mul_ite, mul_zero, hcov, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, ite_true]
    exact sum_congr rfl fun _ _ => by ring
  simp_rw [hD]
  have hs := integral_finsetSum (μ := Pr) univ
    (f := fun j ω => w j * ((∑ k, a j k * est (k, p) ω) * ∑ k, a j k * est (k, r) ω))
    fun j _ => ((hm j p).integrable_mul (hm j r)).const_mul (w j)
  rw [hs]
  simp only [integral_const_mul]
  simp only [hc]
  have hin : ∀ j, ∑ k, ∑ l, a j k * a j l * ((if k = l then Λ p r else 0) + N k l p r)
      = (1 - 2 * w j + ∑ k, w k ^ 2) * Λ p r + (N j j p r - ∑ l, w l * N j l p r
        - ∑ k, w k * N k j p r + ∑ k, ∑ l, w k * w l * N k l p r) := by
    intro j
    simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
    congr 1
    · simp only [ha, ← sum_mul]
      congr 1
      simp only [sub_mul, mul_sub, sum_sub_distrib, ite_mul, mul_ite, one_mul, mul_one,
        zero_mul, mul_zero, sum_ite_eq', mem_univ, ite_true]
      simp only [sq]; ring
    · simp only [ha, sub_mul, mul_sub, sum_sub_distrib, ite_mul, mul_ite, one_mul, mul_one,
        zero_mul, mul_zero, sum_ite_eq', mem_univ, ite_true]
      rw [Finset.sum_eq_single (f := fun x => ∑ y, if x = j then w y * N x y p r else 0) j
        (fun b _ hb => by simp [hb]) (by simp)]
      simp only [ite_true]
      ring
  simp only [hin, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  set S := ∑ k, w k ^ 2
  set T := ∑ k, ∑ l, w k * w l * N k l p r
  have e1 : ∑ x, w x * ∑ l, w l * N x l p r = T := by simp [T, mul_sum, mul_assoc]
  have e2 : ∑ x, w x * ∑ k, w k * N k x p r = T := by
    rw [show T = ∑ l, ∑ k, w k * w l * N k l p r from sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, w x * (1 - 2 * w x + S) = 1 - S := by
    simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, ← sum_mul, hw, S]
    have : ∑ x, w x * (2 * w x) = 2 * ∑ k, w k ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [this]; ring
  have hx : ∀ x, w x * ((1 - 2 * w x + S) * Λ p r + (N x x p r - ∑ l, w l * N x l p r
      - ∑ k, w k * N k x p r + T)) = w x * (1 - 2 * w x + S) * Λ p r + w x * N x x p r
      - w x * ∑ l, w l * N x l p r - w x * ∑ k, w k * N k x p r + w x * T := fun x => by ring
  simp only [hx, sum_add_distrib, sum_sub_distrib, ← sum_mul, e1, e2, e3, hw]
  ring

/-- The weighted spread `Σⱼ ωⱼ(β̂ⱼ - β̄)(β̂ⱼ - β̄)ᵀ`, `β̄ = Σⱼ ωⱼβ̂ⱼ`, of vector estimates. -/
noncomputable def spread (w : J → ℝ) (est : J × P → Ω → ℝ) (ω : Ω) : Matrix P P ℝ :=
  Matrix.of fun p r => ∑ j, w j * ((est (j, p) ω - ∑ k, w k * est (k, p) ω)
    * (est (j, r) ω - ∑ k, w k * est (k, r) ω))

/-- The corrected moment estimate
`Λ̂ = (Σⱼ ωⱼ(β̂ⱼ - β̄)(β̂ⱼ - β̄)ᵀ - Σⱼ ωⱼN̂ⱼⱼ + Σᵢ Σₖ ωᵢωₖN̂ᵢₖ) / (1 - Σⱼ ωⱼ²)`, with an
estimate `N̂` of the noise covariance within and between cohorts. -/
noncomputable def correctedLambda (w : J → ℝ) (est : J × P → Ω → ℝ)
    (Nh : Ω → J → J → Matrix P P ℝ) (ω : Ω) : Matrix P P ℝ :=
  (1 - ∑ j, w j ^ 2)⁻¹ • (spread w est ω - ∑ j, w j • Nh ω j j
    + ∑ i, ∑ k, (w i * w k) • Nh ω i k)

omit [DecidableEq J] [Fintype P] [DecidableEq P] in
/-- Each entry of the spread is integrable. -/
theorem integrable_spread {Pr : Measure Ω} (w : J → ℝ) {est : J × P → Ω → ℝ}
    (hL2 : ∀ x, MemLp (est x) 2 Pr) (p r : P) :
    Integrable (fun ω => spread w est ω p r) Pr := by
  have hm : ∀ j q, MemLp (fun ω => est (j, q) ω - ∑ k, w k * est (k, q) ω) 2 Pr := fun j q =>
    (hL2 _).sub (memLp_finsetSum _ fun k _ => (hL2 (k, q)).const_mul (w k))
  simp only [spread, Matrix.of_apply]
  exact integrable_finsetSum _ fun j _ => ((hm j p).integrable_mul (hm j r)).const_mul (w j)

/-- **The corrected moment `Λ̂` is unbiased** for any noise covariance between cohorts:
with estimates `β̂ⱼ` as in `integral_spread`, weights `Σⱼ ωⱼ = 1` with `Σⱼ ωⱼ² ≠ 1`, and any
integrable estimates `N̂ᵢₖ` with `E N̂ᵢₖ = Nᵢₖ`, `E Λ̂ = Λ`. No distribution, and nothing on how
`N̂` is built beyond its mean. -/
theorem integral_correctedLambda {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (est : J × P → Ω → ℝ) (b : P → ℝ) (Λ : Matrix P P ℝ) (N : J → J → Matrix P P ℝ)
    (hL2 : ∀ x, MemLp (est x) 2 Pr) (hmean : ∀ x, Pr[est x] = b x.2)
    (hcov : ∀ j i p r, cov[est (j, p), est (i, r); Pr] = (if j = i then Λ p r else 0) + N j i p r)
    (w : J → ℝ) (hw : ∑ j, w j = 1) (hw2 : ∑ j, w j ^ 2 ≠ 1)
    (Nh : Ω → J → J → Matrix P P ℝ) (hNi : ∀ i k p r, Integrable (fun ω => Nh ω i k p r) Pr)
    (hN : ∀ i k p r, Pr[fun ω => Nh ω i k p r] = N i k p r) :
    Matrix.of (fun p r => Pr[fun ω => correctedLambda w est Nh ω p r]) = Λ := by
  have hS := integral_spread est b Λ N hL2 hmean hcov w hw
  ext p r
  have hA : Pr[fun ω => spread w est ω p r]
      = ((1 - ∑ j, w j ^ 2) • Λ + ∑ j, w j • N j j - ∑ i, ∑ k, (w i * w k) • N i k) p r := by
    simpa [spread] using congrFun (congrFun hS p) r
  have iB : Integrable (fun ω => ∑ j, w j * Nh ω j j p r) Pr :=
    integrable_finsetSum _ fun j _ => (hNi j j p r).const_mul _
  have iC : Integrable (fun ω => ∑ i, ∑ k, w i * w k * Nh ω i k p r) Pr :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (hNi i k p r).const_mul _
  have hB : Pr[fun ω => ∑ j, w j * Nh ω j j p r] = ∑ j, w j * N j j p r := by
    rw [integral_finsetSum _ fun j _ => (hNi j j p r).const_mul _]
    simp only [integral_const_mul, hN]
  have hC : Pr[fun ω => ∑ i, ∑ k, w i * w k * Nh ω i k p r] = ∑ i, ∑ k, w i * w k * N i k p r := by
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun k _ => (hNi i k p r).const_mul _]
    refine sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun k _ => (hNi i k p r).const_mul _]
    simp only [integral_const_mul, hN]
  have h1 : (1 - ∑ j, w j ^ 2) ≠ 0 := sub_ne_zero.2 (Ne.symm hw2)
  simp only [Matrix.of_apply, correctedLambda, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul]
  have iAB : Integrable (fun ω => spread w est ω p r - ∑ j, w j * Nh ω j j p r) Pr :=
    (integrable_spread w hL2 p r).sub iB
  rw [integral_const_mul, integral_add iAB iC,
    integral_sub (integrable_spread w hL2 p r) iB, hA, hB, hC]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  field_simp
  ring

end CoreVector

end Credibility
