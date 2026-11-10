import Credibility.Unequal
import Credibility.Expectation
import Credibility.CoreMoments

/-!
# The moment layer for unequal lengths (extension, distribution-free)

The moment layer for `Unequal.lean` (`Moments.lean` is its case `Tⱼ = T`):
cohort `j` is observed only in `Tⱼ`, and
random variables are assumed only on observed cells. For **any** probability
space and **any** square-integrable random variables with the first two
moments of eq. (15) on the observed cells, `K` (on `Tⱼ`) is the actual
covariance of the cohort estimates, and `zⱼ` minimises the actual mean
squared error. Nothing is assumed about unobserved cells: `ε j t` for
`t ∉ Tⱼ` is an arbitrary function that no estimator reads.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

namespace Unequal

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Random variables with the moments of eq. (15) on the observed cells, under
`P`: cohort effects `η` and noise `ε`, centred, of unit variance, the `η`
uncorrelated with each other and with the noise, and
`cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ` for `t ∈ Tᵢ`, `s ∈ Tⱼ`. So `ρᵢⱼ` is used only on
shared periods. Only moments are assumed, no distribution. -/
structure Noise (M : Unequal J T) (P : Measure Ω) where
  /-- Cohort effect `ηⱼ`. -/
  η : J → Ω → ℝ
  /-- Sampling noise `εⱼₜ` (only read for `t ∈ Tⱼ`). -/
  ε : J → T → Ω → ℝ
  η_memLp : ∀ j, MemLp (η j) 2 P
  ε_memLp : ∀ j, ∀ t ∈ M.obs j, MemLp (ε j t) 2 P
  η_mean : ∀ j, P[η j] = 0
  ε_mean : ∀ j, ∀ t ∈ M.obs j, P[ε j t] = 0
  cov_η_η : ∀ i j, cov[η i, η j; P] = if i = j then 1 else 0
  cov_η_ε : ∀ i j, ∀ t ∈ M.obs j, cov[η i, ε j t; P] = 0
  cov_ε_ε : ∀ i j, ∀ t ∈ M.obs i, ∀ s ∈ M.obs j,
    cov[ε i t, ε j s; P] = M.ρ i j * if t = s then 1 else 0

namespace Noise

variable {M : Unequal J T} {P : Measure Ω} (N : M.Noise P) (μ : ℝ)

/-- The true key ratio `μⱼ = μ + τ ηⱼ`. -/
noncomputable def trueMean (j : J) : Ω → ℝ := fun ω => μ + Real.sqrt M.τ2 * N.η j ω

/-- The key ratio `μⱼₜ = μⱼ + σⱼₜ εⱼₜ` (observed for `t ∈ Tⱼ`). -/
noncomputable def obsVal (j : J) (t : T) : Ω → ℝ :=
  fun ω => N.trueMean μ j ω + M.σ j t * N.ε j t ω

/-- A linear estimate `Σ_{t∈Tⱼ} cₜ μⱼₜ` of cohort `j` from its observed cells. -/
noncomputable def cohortLin (j : J) (c : T → ℝ) : Ω → ℝ :=
  fun ω => ∑ t ∈ M.obs j, c t * N.obsVal μ j t ω

/-- The cohort estimate `μ̂ⱼ = Σ_{t∈Tⱼ} aⱼₜ μⱼₜ`, eq. (23) on `Tⱼ`. -/
noncomputable def cohortEst (j : J) : Ω → ℝ := N.cohortLin μ j (M.a j)

/-- A linear portfolio estimate `Σⱼ dⱼ μ̂ⱼ` with arbitrary weights `d`. -/
noncomputable def portLin (d : J → ℝ) : Ω → ℝ := fun ω => ∑ j, d j * N.cohortEst μ j ω

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights of the new `K`. -/
noncomputable def portEst : Ω → ℝ := N.portLin μ M.b

/-- The blend `z μ̂ⱼ + (1 - z) μ̂`. -/
noncomputable def blend (j : J) (z : ℝ) : Ω → ℝ :=
  fun ω => z * N.cohortEst μ j ω + (1 - z) * N.portEst μ ω

omit [Fintype J] [Fintype T] in
lemma trueMean_def (j : J) :
    N.trueMean μ j = fun ω => μ + Real.sqrt M.τ2 * N.η j ω := rfl

omit [Fintype J] [Fintype T] in
lemma obsVal_def (j : J) (t : T) :
    N.obsVal μ j t = fun ω => N.trueMean μ j ω + M.σ j t * N.ε j t ω := rfl

variable [IsProbabilityMeasure P]

omit [Fintype J] [Fintype T] in
lemma memLp_trueMean (j : J) : MemLp (N.trueMean μ j) 2 P :=
  (memLp_const μ).add ((N.η_memLp j).const_mul _)

omit [Fintype J] [Fintype T] in
lemma memLp_obsVal (j : J) {t : T} (ht : t ∈ M.obs j) : MemLp (N.obsVal μ j t) 2 P :=
  (N.memLp_trueMean μ j).add ((N.ε_memLp j t ht).const_mul _)

omit [Fintype J] [Fintype T] in
lemma integral_trueMean (j : J) : P[N.trueMean μ j] = μ := by
  simp only [trueMean]
  rw [integral_add (integrable_const μ) (((N.η_memLp j).const_mul _).integrable (by norm_num))]
  simp [integral_const_mul, N.η_mean]

omit [Fintype J] [Fintype T] in
/-- Observed cells are unbiased: `E[μⱼₜ] = μ` for `t ∈ Tⱼ`. -/
theorem obsVal_mean (j : J) {t : T} (ht : t ∈ M.obs j) : P[N.obsVal μ j t] = μ := by
  simp only [obsVal]
  rw [integral_add ((N.memLp_trueMean μ j).integrable (by norm_num))
    (((N.ε_memLp j t ht).const_mul _).integrable (by norm_num)), integral_trueMean]
  simp [integral_const_mul, N.ε_mean j t ht]

omit [Fintype J] [Fintype T] in
lemma cov_η_trueMean (i j : J) :
    cov[N.η i, N.trueMean μ j; P] = Real.sqrt M.τ2 * if i = j then 1 else 0 := by
  rw [N.trueMean_def μ j]
  rw [covariance_const_add_right (((N.η_memLp j).const_mul _).integrable (by norm_num)),
    covariance_const_mul_right, N.cov_η_η]

omit [Fintype J] [Fintype T] in
lemma cov_ε_trueMean (i j : J) {t : T} (ht : t ∈ M.obs i) :
    cov[N.ε i t, N.trueMean μ j; P] = 0 := by
  rw [N.trueMean_def μ j]
  rw [covariance_const_add_right (((N.η_memLp j).const_mul _).integrable (by norm_num)),
    covariance_const_mul_right, covariance_comm, N.cov_η_ε j i t ht, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_trueMean (i j : J) :
    cov[N.trueMean μ i, N.trueMean μ j; P] = M.τ2 * if i = j then 1 else 0 := by
  rw [N.trueMean_def μ i, covariance_const_add_left (((N.η_memLp i).const_mul _).integrable (by norm_num)),
    covariance_const_mul_left, cov_η_trueMean, ← mul_assoc, M.sqrt_τ2_mul]

omit [Fintype J] [Fintype T] in
lemma cov_obsVal_trueMean (i j : J) {t : T} (ht : t ∈ M.obs i) :
    cov[N.obsVal μ i t, N.trueMean μ j; P] = M.τ2 * if i = j then 1 else 0 := by
  rw [N.obsVal_def μ i t, show (fun ω => N.trueMean μ i ω + M.σ i t * N.ε i t ω)
      = N.trueMean μ i + fun ω => M.σ i t * N.ε i t ω from rfl,
    covariance_add_left (N.memLp_trueMean μ i) ((N.ε_memLp i t ht).const_mul _)
      (N.memLp_trueMean μ j),
    covariance_const_mul_left, cov_ε_trueMean _ _ _ _ ht, cov_trueMean]
  ring

omit [Fintype J] [Fintype T] in
/-- Eq. (16) is the actual covariance on observed cells: `cov(μᵢₜ, μⱼₛ) = K̄ᵢⱼᵗˢ`
for `t ∈ Tᵢ`, `s ∈ Tⱼ`. -/
theorem cov_obsVal (i j : J) {t s : T} (ht : t ∈ M.obs i) (hs : s ∈ M.obs j) :
    cov[N.obsVal μ i t, N.obsVal μ j s; P] = M.toModel.obsCov i j t s := by
  rw [N.obsVal_def μ i t, N.obsVal_def μ j s, cov_add_add (N.memLp_trueMean μ i) ((N.ε_memLp i t ht).const_mul _)
    (N.memLp_trueMean μ j) ((N.ε_memLp j s hs).const_mul _)]
  rw [covariance_const_mul_right, covariance_comm (N.trueMean μ i) (N.ε j s), N.cov_ε_trueMean μ j i hs,
    covariance_const_mul_left, N.cov_ε_trueMean μ i j ht, covariance_const_mul_left,
    covariance_const_mul_right, N.cov_ε_ε i j t ht s hs, cov_trueMean, Model.obsCov]
  ring

/-- §2.8 in true expectation with unequal lengths: for a quadratic form `quad Q`
reading only observed cells (`Qₚq ≠ 0` only if `p` and `q` are observed),
`E[Σₚ,q Qₚq μₚ μq] = M.E μ Q`. So `Unbiased f θ` for such a form means
`E f = θ` for any random variables with the moments of eq. (15) on the
observed cells, whatever the unobserved cells hold. -/
theorem integral_quad (Q : J × T → J × T → ℝ)
    (hQ : ∀ p q, Q p q ≠ 0 → p.2 ∈ M.obs p.1 ∧ q.2 ∈ M.obs q.1) :
    P[fun ω => Model.quad Q (fun p => N.obsVal μ p.1 p.2 ω)] = M.toModel.E μ Q := by
  -- Each term is `0` or a product of two square-integrable observed cells,
  -- with `E[μₚμq] = cov(μₚ, μq) + μ²`.
  have hI : ∀ p q : J × T,
      Integrable (fun ω => Q p q * (N.obsVal μ p.1 p.2 ω * N.obsVal μ q.1 q.2 ω)) P := by
    intro p q
    by_cases h : Q p q = 0
    · simp [h]
    obtain ⟨hp, hq⟩ := hQ p q h
    exact ((N.memLp_obsVal μ p.1 hp).integrable_mul (N.memLp_obsVal μ q.1 hq)).const_mul _
  have hm : ∀ p q : J × T,
      P[fun ω => Q p q * (N.obsVal μ p.1 p.2 ω * N.obsVal μ q.1 q.2 ω)]
        = Q p q * (M.toModel.cov p q + μ ^ 2) := by
    intro p q
    by_cases h : Q p q = 0
    · simp [h]
    obtain ⟨hp, hq⟩ := hQ p q h
    have hc := covariance_eq_sub (N.memLp_obsVal μ p.1 hp) (N.memLp_obsVal μ q.1 hq)
    rw [N.cov_obsVal μ p.1 q.1 hp hq, N.obsVal_mean μ p.1 hp, N.obsVal_mean μ q.1 hq] at hc
    rw [integral_const_mul, Model.cov, hc]
    simp only [Pi.mul_def]
    ring
  simp only [Model.quad, Model.E, Model.Ecov, mul_assoc]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hI p q]
  refine sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => hI p q]
  exact sum_congr rfl fun q _ => hm p q

omit [Fintype J] [Fintype T] in
lemma memLp_cohortLin (j : J) (c : T → ℝ) : MemLp (N.cohortLin μ j c) 2 P :=
  memLp_finsetSum _ fun _ ht => (N.memLp_obsVal μ j ht).const_mul _

omit [Fintype J] [Fintype T] in
lemma integral_cohortLin (j : J) (c : T → ℝ) :
    P[N.cohortLin μ j c] = (∑ t ∈ M.obs j, c t) * μ := by
  simp only [cohortLin]
  rw [integral_finsetSum _ fun t ht => ((N.memLp_obsVal μ j ht).const_mul (c t)).integrable
    (by norm_num), sum_mul]
  exact sum_congr rfl fun t ht => by rw [integral_const_mul, N.obsVal_mean μ j ht]

omit [Fintype J] [Fintype T] in
lemma cov_cohortLin (i j : J) (c c' : T → ℝ) :
    cov[N.cohortLin μ i c, N.cohortLin μ j c'; P]
      = ∑ t ∈ M.obs i, ∑ s ∈ M.obs j, c t * c' s * M.toModel.obsCov i j t s := by
  unfold cohortLin
  rw [covariance_fun_sum_fun_sum' (fun t ht => (N.memLp_obsVal μ i ht).const_mul (c t))
    (fun s hs => (N.memLp_obsVal μ j hs).const_mul (c' s))]
  refine sum_congr rfl fun t ht => sum_congr rfl fun s hs => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, N.cov_obsVal μ i j ht hs]
  ring

omit [Fintype J] [Fintype T] in
lemma cov_cohortLin_trueMean (i j : J) (c : T → ℝ) :
    cov[N.cohortLin μ i c, N.trueMean μ j; P]
      = (∑ t ∈ M.obs i, c t) * M.τ2 * if i = j then 1 else 0 := by
  unfold cohortLin
  rw [covariance_fun_sum_left' (fun t ht => (N.memLp_obsVal μ i ht).const_mul (c t))
    (N.memLp_trueMean μ j), sum_mul, sum_mul]
  exact sum_congr rfl fun t ht => by
    rw [covariance_const_mul_left, N.cov_obsVal_trueMean μ i j ht]; ring

omit [Fintype J] [Fintype T] in
lemma cov_cohortLin_self (j : J) (c : T → ℝ) :
    cov[N.cohortLin μ j c, N.cohortLin μ j c; P]
      = ∑ t ∈ M.obs j, c t ^ 2 * M.σ j t ^ 2 + (∑ t ∈ M.obs j, c t) ^ 2 * M.τ2 := by
  rw [cov_cohortLin]
  simp only [Model.obsCov, M.ρ_self, ↓reduceIte, mul_one, mul_add, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun t ht => ?_
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, ht, ↓reduceIte]
    ring
  · rw [sq, sum_mul_sum, sum_mul]
    exact sum_congr rfl fun t _ => by rw [sum_mul]

omit [Fintype J] [Fintype T] in
/-- Eq. (21) on the observed cells is the actual covariance: `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`. -/
theorem cov_cohortEst (i j : J) : cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.K i j := by
  rw [cohortEst, cohortEst, cov_cohortLin]
  rfl

omit [Fintype J] [Fintype T] in
lemma memLp_cohortEst (j : J) : MemLp (N.cohortEst μ j) 2 P := N.memLp_cohortLin μ j _

omit [Fintype J] [Fintype T] in
lemma integral_cohortEst (j : J) : P[N.cohortEst μ j] = μ := by
  rw [cohortEst, integral_cohortLin, M.sum_a, one_mul]

omit [Fintype J] [Fintype T] in
/-- The cohort estimates and levels as an instance of the Core moment layer:
`cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ` and level covariance `L = τ²I`. -/
noncomputable def toEstimates : Core.Estimates M.K (M.τ2 • (1 : Matrix J J ℝ)) μ P where
  est := N.cohortEst μ
  level := N.trueMean μ
  est_memLp := N.memLp_cohortEst μ
  level_memLp := N.memLp_trueMean μ
  est_mean := N.integral_cohortEst μ
  level_mean := N.integral_trueMean μ
  cov_est := N.cov_cohortEst μ
  cov_level_est i j := by
    rw [covariance_comm, cohortEst, cov_cohortLin_trueMean, M.sum_a]
    by_cases h : i = j <;> simp [h, Ne.symm]
  cov_level i j := by
    rw [cov_trueMean]
    by_cases h : i = j <;> simp [h]

omit [Fintype T] in
lemma memLp_portLin (d : J → ℝ) : MemLp (N.portLin μ d) 2 P :=
  (N.toEstimates μ).memLp_portLin d

omit [Fintype T] in
lemma cov_portLin (d d' : J → ℝ) :
    cov[N.portLin μ d, N.portLin μ d'; P] = d ⬝ᵥ (M.K *ᵥ d') :=
  (N.toEstimates μ).cov_portLin d d'

omit [Fintype T] in
lemma cov_cohortEst_portLin (i : J) (d : J → ℝ) :
    cov[N.cohortEst μ i, N.portLin μ d; P] = (M.K *ᵥ d) i :=
  (N.toEstimates μ).cov_est_portLin i d

omit [Fintype T] in
lemma cov_portLin_trueMean (d : J → ℝ) (j : J) :
    cov[N.portLin μ d, N.trueMean μ j; P] = d j * M.τ2 := by
  rw [covariance_comm]
  refine ((N.toEstimates μ).cov_level_portLin j d).trans ?_
  simp [smul_mulVec, mul_comm]

omit [Fintype T] in
lemma integral_portLin (d : J → ℝ) : P[N.portLin μ d] = (∑ j, d j) * μ :=
  (N.toEstimates μ).integral_portLin d

omit [Fintype J] [Fintype T] in
/-- Any linear estimate from cohort `j`'s observed cells with weights summing to
one has error variance `Var(Σ_{t∈Tⱼ} cₜ μⱼₜ - μⱼ) = Σ_{t∈Tⱼ} cₜ² σⱼₜ²`. -/
theorem var_cohortLin_err (j : J) (c : T → ℝ) (hc : ∑ t ∈ M.obs j, c t = 1) :
    Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P]
      = ∑ t ∈ M.obs j, c t ^ 2 * M.σ j t ^ 2 := by
  have hX := N.memLp_cohortLin μ j c
  have hY := N.memLp_trueMean μ j
  have hXY : MemLp (fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω) 2 P := hX.sub hY
  rw [← covariance_self hXY.aestronglyMeasurable.aemeasurable,
    covariance_fun_sub_fun_sub hX hY hX hY, covariance_comm (N.trueMean μ j),
    cov_cohortLin_self, cov_cohortLin_trueMean, cov_trueMean, hc]
  simp

omit [Fintype J] [Fintype T] in
/-- Eq. (23) on `Tⱼ` in true variance: among unbiased linear estimates from
cohort `j`'s observed cells, `μ̂ⱼ` has the smallest error variance. -/
theorem cohortEst_optimal (j : J) (c : T → ℝ) (hc : ∑ t ∈ M.obs j, c t = 1) :
    Var[fun ω => N.cohortEst μ j ω - N.trueMean μ j ω; P]
      ≤ Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] := by
  rw [cohortEst, N.var_cohortLin_err μ j _ (M.sum_a j), N.var_cohortLin_err μ j c hc]
  exact M.a_optimal j c hc

omit [Fintype T] in
/-- Eq. (24) in true variance with unequal lengths: among unbiased linear
portfolio estimates built from the `μ̂ⱼ`, the GLS one has the smallest
variance, and it equals `s²`. -/
theorem portEst_optimal (hK : M.K.PosDef) (d : J → ℝ) (hd : ∑ j, d j = 1) :
    Var[N.portEst μ; P] = M.s2 ∧ M.s2 ≤ Var[N.portLin μ d; P] :=
  (N.toEstimates μ).portEst_optimal hK d hd

omit [Fintype T] in
/-- The blend moments are the Core ones for `L = τ²I` and `Var(μ̂ⱼ) = Kⱼⱼ`. -/
lemma moments_eq_levelMoments (j : J) :
    M.moments j = Core.levelMoments M.K (M.τ2 • (1 : Matrix J J ℝ)) (M.K j j) j := by
  rw [moments_eq_core, Core.moments_eq_levelMoments, K_apply, M.ρ_self]
  simp [add_comm]

omit [Fintype T] in
/-- Every field of `M.moments j` is the actual moment it names (§2.4). -/
theorem moments_eq (hK : M.K.PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.moments j).varCohort ∧
    Var[N.portEst μ; P] = (M.moments j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.moments j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.moments j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.moments j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.moments j).covPortfolioTarget := by
  rw [moments_eq_levelMoments]
  exact (N.toEstimates μ).levelMoments_eq hK j

omit [Fintype T] in
/-- The blend is unbiased and its actual mean squared error is `errVar`,
eq. (6), with the `K`, `b`, `s²` of unequal lengths. -/
theorem mse_blend (hK : M.K.PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.moments j).errVar z := by
  rw [moments_eq_levelMoments]
  exact (N.toEstimates μ).mse_blend hK j z

omit [Fintype T] in
/-- Eq. (26) with unequal lengths, in true MSE: `zⱼ` (`Unequal.bestZ_eq`)
minimises the actual mean squared error of the blend, for every distribution
with the assumed moments on the observed cells. -/
theorem bestZ_mse_optimal (hK : M.K.PosDef) (j : J)
    (hgap : 0 < (M.moments j).gap) (z : ℝ) :
    P[fun ω => (N.blend μ j (M.moments j).bestZ ω - N.trueMean μ j ω) ^ 2]
      ≤ P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] := by
  rw [N.mse_blend μ hK j, N.mse_blend μ hK j]
  exact (M.moments j).bestZ_optimal hgap z

end Noise

/-! ### Consistency: when do such random variables exist? -/

/-- Noise correlations at period `t` used for the witness: `ρᵢⱼ` between
cohorts observed at `t`, independent unit noise on unobserved cells. -/
def corrAt (M : Unequal J T) (t : T) (i j : J) : ℝ :=
  if t ∈ M.obs i ∧ t ∈ M.obs j then M.ρ i j else if i = j then 1 else 0

/-- Covariances of `ηⱼ` (`inl j`) and `εⱼₜ` (`inr (j, t)`) for the witness. -/
def gram (M : Unequal J T) : J ⊕ (J × T) → J ⊕ (J × T) → ℝ
  | .inl i, .inl j => if i = j then 1 else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr p, .inr q => M.corrAt p.2 p.1 q.1 * if p.2 = q.2 then 1 else 0

omit [Fintype T] in
/-- `vᵀ C_t v ≥ 0` for the witness correlations, when the block at `t` is PSD. -/
lemma corrAt_quad_nonneg (M : Unequal J T) (t : T) (hρ : (M.block t).PosSemidef) (v : J → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * M.corrAt t i j := by
  -- Split `v` into its observed part `w` and unobserved part `u`.
  set w : J → ℝ := fun j => if t ∈ M.obs j then v j else 0
  set u : J → ℝ := fun j => if t ∈ M.obs j then 0 else v j
  have hterm : ∀ i j, v i * v j * M.corrAt t i j
      = w i * w j * M.ρ i j + if i = j then u i * u j else 0 := fun i j => by
    by_cases hij : i = j
    · subst hij
      by_cases hi : t ∈ M.obs i <;> simp [corrAt, w, u, hi, M.ρ_self]
    · by_cases hi : t ∈ M.obs i <;> by_cases hj : t ∈ M.obs j <;>
        simp [corrAt, w, hi, hj, hij]
  simp only [hterm, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  refine add_nonneg ?_ (sum_nonneg fun i _ => mul_self_nonneg _)
  have h := hρ.dotProduct_mulVec_nonneg (fun j => w j.1)
  simp only [dotProduct, mulVec, star_trivial, block, submatrix_apply, of_apply] at h
  rw [M.sum_eq_sum_block t _ fun i hi => by simp [w, hi]]
  convert h using 1
  refine sum_congr rfl fun i _ => ?_
  rw [M.sum_eq_sum_block t _ fun j hj => by simp [w, hj], mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The witness covariance table is positive semidefinite when every block is. -/
theorem gram_posSemidef (M : Unequal J T) (hρ : ∀ t, (M.block t).PosSemidef) :
    (Matrix.of M.gram).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext u v
    cases u <;> cases v <;> simp [gram, corrAt, M.ρ_symm, eq_comm, and_comm]
    rename_i p q
    by_cases h : p.2 = q.2 <;> simp [h]
  · simp only [dotProduct, mulVec, star_trivial, of_apply, Fintype.sum_sum_type, gram,
      zero_mul, sum_const_zero, add_zero, zero_add]
    refine add_nonneg ?_ ?_
    · simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]
      exact sum_nonneg fun i _ => mul_self_nonneg _
    · have h := fun t : T => M.corrAt_quad_nonneg t (hρ t) (fun j => x (.inr (j, t)))
      simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        sum_ite_eq, mem_univ, ↓reduceIte, mul_sum]
      rw [sum_comm]
      refine sum_nonneg fun t _ => ?_
      convert h t using 1
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- The moment assumptions with unequal lengths are consistent exactly when,
for every period `t`, the correlations of the cohorts observed at `t` form a
positive-semidefinite matrix: the hypothesis of `Unequal.K_posDef`. Pairs that
never share a period are unconstrained. -/
theorem exists_noise_iff (M : Unequal J T) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.Noise P)) ↔ ∀ t, (M.block t).PosSemidef := by
  constructor
  · -- Necessity: `xᵀρ_t x = Var(Σ_{j∈Jₜ} xⱼ εⱼₜ) ≥ 0`.
    rintro ⟨Ω, _, P, _, ⟨N⟩⟩ t
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; simp [block, M.ρ_symm]
    · have hε : ∀ j : {j // t ∈ M.obs j}, MemLp (fun ω => x j * N.ε j t ω) 2 P :=
        fun j => (N.ε_memLp j t j.2).const_mul _
      have hS : MemLp (fun ω => ∑ j, x j * N.ε j t ω) 2 P :=
        memLp_finsetSum _ fun j _ => hε j
      have key : star x ⬝ᵥ (M.block t *ᵥ x) = Var[fun ω => ∑ j, x j * N.ε j t ω; P] := by
        rw [← covariance_self hS.aestronglyMeasurable.aemeasurable,
          covariance_fun_sum_fun_sum hε hε]
        simp only [covariance_const_mul_left, covariance_const_mul_right,
          dotProduct, mulVec, star_trivial, block, submatrix_apply, of_apply, mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [N.cov_ε_ε i j t i.2 t j.2]
        simp only [↓reduceIte, mul_one]
        ring
      rw [key]; exact variance_nonneg _ _
  · -- Sufficiency: a Gaussian vector with covariance `gram` (a witness only).
    intro hρ
    let e := Fintype.equivFin (J ⊕ (J × T))
    let S := (Matrix.of M.gram).submatrix e.symm e.symm
    have hS : S.PosSemidef := (M.gram_posSemidef hρ).submatrix _
    let P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin (Fintype.card (J ⊕ (J × T))))) S
    let Z : J ⊕ (J × T) → EuclideanSpace ℝ (Fin (Fintype.card (J ⊕ (J × T)))) → ℝ :=
      fun u x => x (e u)
    have hmp : ∀ u, MeasurePreserving (Z u) P (gaussianReal 0 (S (e u) (e u)).toNNReal) :=
      fun u => measurePreserving_eval_multivariateGaussian hS
    have hZm : ∀ u, MemLp (Z u) 2 P := fun u =>
      (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving (hmp u)
    have hZi : ∀ u, P[Z u] = 0 := fun u => by
      have := integral_map (μ := P) (f := id) (hmp u).measurable.aemeasurable
        aestronglyMeasurable_id
      rw [(hmp u).map_eq] at this
      simpa [integral_id_gaussianReal] using this.symm
    have hZc : ∀ u v, cov[Z u, Z v; P] = M.gram u v := fun u v => by
      simp [Z, P, covariance_eval_multivariateGaussian hS, S]
    exact ⟨_, inferInstance, P, inferInstance, ⟨{
      η := fun j => Z (.inl j)
      ε := fun j t => Z (.inr (j, t))
      η_memLp := fun j => hZm _
      ε_memLp := fun j t _ => hZm _
      η_mean := fun j => hZi _
      ε_mean := fun j t _ => hZi _
      cov_η_η := fun i j => hZc _ _
      cov_η_ε := fun i j t _ => hZc _ _
      cov_ε_ε := fun i j t ht s hs => by
        rw [hZc]
        by_cases h : t = s
        · subst h; simp [gram, corrAt, ht, hs]
        · simp [gram, h] }⟩⟩

end Unequal

end Credibility
