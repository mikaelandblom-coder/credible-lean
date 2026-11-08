import Credibility.Model

/-!
# The moment layer (extension, distribution-free)

The rest of the development takes the second moments `τ²`, `σⱼₜ`, `ρᵢⱼ` as
given numbers and *defines* the covariances (16), (21) from them. Here they
become theorems: for **any** probability space and **any** square-integrable
random variables with the first two moments of eq. (15), the formulas are
the actual covariances, and `zⱼ` minimises the actual mean squared error.
No distribution is assumed anywhere.

Notation: cohort effect `ηⱼ` (the thesis's `εⱼ`), sampling noise `εⱼₜ`:

    μⱼ = μ + τ ηⱼ,   μⱼₜ = μⱼ + σⱼₜ εⱼₜ.

Finally, such random variables exist exactly when the correlation table `ρ`
is positive semidefinite (`exists_noise_iff`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Random variables with the first two moments of eq. (15), under the
probability measure `P`: cohort effects `η` and sampling noise `ε`, centred,
of unit variance, the `η` uncorrelated with each other and with all noise,
and `cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ`. Only moments are assumed, no distribution. -/
structure Noise (M : Model J T) (P : Measure Ω) where
  /-- Cohort effect `ηⱼ`. -/
  η : J → Ω → ℝ
  /-- Sampling noise `εⱼₜ`. -/
  ε : J → T → Ω → ℝ
  η_memLp : ∀ j, MemLp (η j) 2 P
  ε_memLp : ∀ j t, MemLp (ε j t) 2 P
  η_mean : ∀ j, P[η j] = 0
  ε_mean : ∀ j t, P[ε j t] = 0
  cov_η_η : ∀ i j, cov[η i, η j; P] = if i = j then 1 else 0
  cov_η_ε : ∀ i j t, cov[η i, ε j t; P] = 0
  cov_ε_ε : ∀ i j t s, cov[ε i t, ε j s; P] = M.ρ i j * if t = s then 1 else 0

/-- Covariances of the basic variables `ηⱼ` (`inl j`) and `εⱼₜ` (`inr (j, t)`). -/
def gram (M : Model J T) : J ⊕ (J × T) → J ⊕ (J × T) → ℝ
  | .inl i, .inl j => if i = j then 1 else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr p, .inr q => M.ρ p.1 q.1 * if p.2 = q.2 then 1 else 0

/-- Weights of the true mean `μⱼ = μ + τ ηⱼ` on the basic variables. -/
noncomputable def wTrue (M : Model J T) (j : J) : J ⊕ (J × T) → ℝ
  | .inl k => if k = j then Real.sqrt M.τ2 else 0
  | .inr _ => 0

/-- Weights of the observation `μⱼₜ = μ + τ ηⱼ + σⱼₜ εⱼₜ` on the basic variables. -/
noncomputable def wObs (M : Model J T) (j : J) (t : T) : J ⊕ (J × T) → ℝ
  | .inl k => if k = j then Real.sqrt M.τ2 else 0
  | .inr p => if p = (j, t) then M.σ j t else 0

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
lemma sqrt_τ2_mul (M : Model J T) : Real.sqrt M.τ2 * Real.sqrt M.τ2 = M.τ2 :=
  Real.mul_self_sqrt M.τ2_pos.le

namespace Noise

variable {M : Model J T} {P : Measure Ω} (N : M.Noise P) (μ : ℝ)

/-- The true key ratio `μⱼ = μ + τ ηⱼ`. -/
noncomputable def trueMean (j : J) : Ω → ℝ := fun ω => μ + Real.sqrt M.τ2 * N.η j ω

/-- The observed key ratio `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`. -/
noncomputable def obs (j : J) (t : T) : Ω → ℝ :=
  fun ω => N.trueMean μ j ω + M.σ j t * N.ε j t ω

/-- A linear estimate `Σₜ cₜ μⱼₜ` of cohort `j` with arbitrary weights `c`. -/
noncomputable def cohortLin (j : J) (c : T → ℝ) : Ω → ℝ := fun ω => ∑ t, c t * N.obs μ j t ω

/-- The cohort estimate `μ̂ⱼ = Σₜ aⱼₜ μⱼₜ`, eq. (23). -/
noncomputable def cohortEst (j : J) : Ω → ℝ := N.cohortLin μ j (M.a j)

/-- A linear portfolio estimate `Σⱼ dⱼ μ̂ⱼ` with arbitrary weights `d`. -/
noncomputable def portLin (d : J → ℝ) : Ω → ℝ := fun ω => ∑ j, d j * N.cohortEst μ j ω

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights. -/
noncomputable def portEst : Ω → ℝ := N.portLin μ M.b

/-- The blend `z μ̂ⱼ + (1 - z) μ̂`. -/
noncomputable def blend (j : J) (z : ℝ) : Ω → ℝ :=
  fun ω => z * N.cohortEst μ j ω + (1 - z) * N.portEst μ ω

variable [IsProbabilityMeasure P]

/-! ### Linear combinations of the basic variables

Every estimator here is a constant plus a linear combination of the `ηⱼ` and
`εⱼₜ`. We index both by `J ⊕ (J × T)`; their covariances form `gram`. -/

/-- The basic variables: `ηⱼ` at `inl j`, `εⱼₜ` at `inr (j, t)`. -/
def basic : J ⊕ (J × T) → Ω → ℝ
  | .inl j => N.η j
  | .inr p => N.ε p.1 p.2

omit [Fintype J] [Fintype T] [IsProbabilityMeasure P] in
lemma memLp_basic (u : J ⊕ (J × T)) : MemLp (N.basic u) 2 P := by
  cases u with
  | inl j => exact N.η_memLp j
  | inr p => exact N.ε_memLp p.1 p.2

omit [Fintype J] [Fintype T] [IsProbabilityMeasure P] in
lemma integral_basic (u : J ⊕ (J × T)) : P[N.basic u] = 0 := by
  cases u with
  | inl j => exact N.η_mean j
  | inr p => exact N.ε_mean p.1 p.2

omit [Fintype J] [Fintype T] [IsProbabilityMeasure P] in
lemma cov_basic (u v : J ⊕ (J × T)) : cov[N.basic u, N.basic v; P] = M.gram u v := by
  cases u with
  | inl i =>
    cases v with
    | inl j => exact N.cov_η_η i j
    | inr q => exact N.cov_η_ε i q.1 q.2
  | inr p =>
    cases v with
    | inl j => rw [basic, basic, covariance_comm]; exact N.cov_η_ε j p.1 p.2
    | inr q => exact N.cov_ε_ε p.1 q.1 p.2 q.2

/-- The random variable `c + Σᵤ wᵤ · basicᵤ`. -/
noncomputable def lin (c : ℝ) (w : J ⊕ (J × T) → ℝ) : Ω → ℝ :=
  fun ω => c + ∑ u, w u * N.basic u ω

omit [Fintype J] [Fintype T] [IsProbabilityMeasure P] in
lemma memLp_term (w : J ⊕ (J × T) → ℝ) (u : J ⊕ (J × T)) :
    MemLp (fun ω => w u * N.basic u ω) 2 P :=
  (N.memLp_basic u).const_mul (w u)

omit [IsProbabilityMeasure P] in
lemma memLp_sum (w : J ⊕ (J × T) → ℝ) : MemLp (fun ω => ∑ u, w u * N.basic u ω) 2 P :=
  memLp_finsetSum _ fun u _ => N.memLp_term w u

lemma memLp_lin (c : ℝ) (w : J ⊕ (J × T) → ℝ) : MemLp (N.lin c w) 2 P :=
  (memLp_const c).add (N.memLp_sum w)

lemma integral_lin (c : ℝ) (w : J ⊕ (J × T) → ℝ) : P[N.lin c w] = c := by
  have hi : ∀ u, Integrable (fun ω => w u * N.basic u ω) P :=
    fun u => (N.memLp_term w u).integrable (by norm_num)
  simp only [lin]
  rw [integral_add (integrable_const c) (integrable_finsetSum _ fun u _ => hi u),
    integral_finsetSum _ fun u _ => hi u]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, N.integral_basic, mul_zero, sum_const_zero, add_zero]

lemma cov_lin (c c' : ℝ) (w w' : J ⊕ (J × T) → ℝ) :
    cov[N.lin c w, N.lin c' w'; P] = ∑ u, ∑ v, w u * w' v * M.gram u v := by
  have hi : ∀ w : J ⊕ (J × T) → ℝ, Integrable (fun ω => ∑ u, w u * N.basic u ω) P :=
    fun w => (N.memLp_sum w).integrable (by norm_num)
  unfold lin
  rw [covariance_const_add_left (hi w), covariance_const_add_right (hi w'),
    covariance_fun_sum_fun_sum (N.memLp_term w) (N.memLp_term w')]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, N.cov_basic]
  ring

lemma var_lin (c : ℝ) (w : J ⊕ (J × T) → ℝ) :
    Var[N.lin c w; P] = ∑ u, ∑ v, w u * w v * M.gram u v := by
  rw [← covariance_self (N.memLp_lin c w).aestronglyMeasurable.aemeasurable, N.cov_lin]

omit [IsProbabilityMeasure P] in
lemma trueMean_eq (j : J) : N.trueMean μ j = N.lin μ (M.wTrue j) := by
  funext ω
  simp [trueMean, lin, Fintype.sum_sum_type, wTrue, basic]

omit [IsProbabilityMeasure P] in
lemma obs_eq (j : J) (t : T) : N.obs μ j t = N.lin μ (M.wObs j t) := by
  funext ω
  simp [obs, trueMean, lin, Fintype.sum_sum_type, wObs, basic, add_assoc]

/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs μ j t] = μ := by
  rw [obs_eq, integral_lin]

/-- Eq. (16) is the actual covariance: `cov(μᵢₜ, μⱼₛ) = K̄ᵢⱼᵗˢ`. -/
theorem cov_obs (i j : J) (t s : T) : cov[N.obs μ i t, N.obs μ j s; P] = M.obsCov i j t s := by
  rw [obs_eq, obs_eq, cov_lin]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, gram, wObs, obsCov, ite_mul, mul_ite]
  simp only [ite_and, sum_ite_eq', mem_univ, ↓reduceIte, M.sqrt_τ2_mul, eq_comm (a := s),
    eq_comm (a := j)]
  ring

lemma memLp_obs (j : J) (t : T) : MemLp (N.obs μ j t) 2 P := by
  rw [obs_eq]; exact N.memLp_lin _ _

lemma memLp_trueMean (j : J) : MemLp (N.trueMean μ j) 2 P := by
  rw [trueMean_eq]; exact N.memLp_lin _ _

lemma cov_obs_trueMean (i j : J) (t : T) :
    cov[N.obs μ i t, N.trueMean μ j; P] = M.τ2 * if i = j then 1 else 0 := by
  rw [obs_eq, trueMean_eq, cov_lin]
  simp [Fintype.sum_sum_type, gram, wObs, wTrue, ite_mul, mul_ite,
    M.sqrt_τ2_mul, eq_comm (a := j)]

lemma cov_trueMean (i j : J) :
    cov[N.trueMean μ i, N.trueMean μ j; P] = M.τ2 * if i = j then 1 else 0 := by
  rw [trueMean_eq, trueMean_eq, cov_lin]
  simp [Fintype.sum_sum_type, gram, wTrue, ite_mul, mul_ite,
    M.sqrt_τ2_mul, eq_comm (a := j)]

lemma memLp_cohortLin (j : J) (c : T → ℝ) : MemLp (N.cohortLin μ j c) 2 P :=
  memLp_finsetSum _ fun t _ => (N.memLp_obs μ j t).const_mul (c t)

lemma integral_cohortLin (j : J) (c : T → ℝ) : P[N.cohortLin μ j c] = (∑ t, c t) * μ := by
  simp only [cohortLin]
  rw [integral_finsetSum _ fun t _ => ((N.memLp_obs μ j t).const_mul (c t)).integrable
    (by norm_num)]
  simp [integral_const_mul, N.obs_mean, sum_mul]

lemma cov_cohortLin (i j : J) (c c' : T → ℝ) :
    cov[N.cohortLin μ i c, N.cohortLin μ j c'; P]
      = ∑ t, ∑ s, c t * c' s * M.obsCov i j t s := by
  unfold cohortLin
  rw [covariance_fun_sum_fun_sum (fun t => (N.memLp_obs μ i t).const_mul (c t))
    (fun s => (N.memLp_obs μ j s).const_mul (c' s))]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, N.cov_obs]
  ring

lemma cov_cohortLin_trueMean (i j : J) (c : T → ℝ) :
    cov[N.cohortLin μ i c, N.trueMean μ j; P] = (∑ t, c t) * M.τ2 * if i = j then 1 else 0 := by
  unfold cohortLin
  rw [covariance_fun_sum_left (fun t => (N.memLp_obs μ i t).const_mul (c t))
    (N.memLp_trueMean μ j)]
  simp only [covariance_const_mul_left, N.cov_obs_trueMean, sum_mul]
  exact sum_congr rfl fun t _ => by ring

lemma cov_cohortLin_self (j : J) (c : T → ℝ) :
    cov[N.cohortLin μ j c, N.cohortLin μ j c; P]
      = ∑ t, c t ^ 2 * M.σ j t ^ 2 + (∑ t, c t) ^ 2 * M.τ2 := by
  rw [cov_cohortLin]
  simp only [obsCov, M.ρ_self, mul_one, ↓reduceIte, mul_add, mul_ite, mul_zero, sum_add_distrib,
    sum_ite_eq, mem_univ]
  rw [sq, sum_mul_sum, sum_mul]
  congr 1
  · exact sum_congr rfl fun t _ => by ring
  · exact sum_congr rfl fun t _ => by rw [sum_mul]

/-- Eq. (21) is the actual covariance: `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`. -/
theorem cov_cohortEst (i j : J) : cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.K i j := by
  rw [cohortEst, cohortEst, cov_cohortLin]
  rfl

lemma memLp_cohortEst (j : J) : MemLp (N.cohortEst μ j) 2 P := N.memLp_cohortLin μ j _

lemma memLp_portLin (d : J → ℝ) : MemLp (N.portLin μ d) 2 P :=
  memLp_finsetSum _ fun j _ => (N.memLp_cohortEst μ j).const_mul (d j)

lemma cov_portLin (d d' : J → ℝ) :
    cov[N.portLin μ d, N.portLin μ d'; P] = d ⬝ᵥ (M.K *ᵥ d') := by
  unfold portLin
  rw [covariance_fun_sum_fun_sum (fun i => (N.memLp_cohortEst μ i).const_mul (d i))
    (fun j => (N.memLp_cohortEst μ j).const_mul (d' j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, N.cov_cohortEst,
    dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma cov_cohortEst_portLin (i : J) (d : J → ℝ) :
    cov[N.cohortEst μ i, N.portLin μ d; P] = (M.K *ᵥ d) i := by
  unfold portLin
  rw [covariance_fun_sum_right (fun j => (N.memLp_cohortEst μ j).const_mul (d j))
    (N.memLp_cohortEst μ i)]
  simp only [covariance_const_mul_right, N.cov_cohortEst, mulVec, dotProduct]
  exact sum_congr rfl fun j _ => by ring

lemma cov_portLin_trueMean [Nonempty T] (d : J → ℝ) (j : J) :
    cov[N.portLin μ d, N.trueMean μ j; P] = d j * M.τ2 := by
  have ha : ∀ i, ∑ t, M.a i t = 1 := fun i =>
    sum_invVarWeight _ fun t => pow_pos (M.σ_pos i t) 2
  unfold portLin
  rw [covariance_fun_sum_left (fun i => (N.memLp_cohortEst μ i).const_mul (d i))
    (N.memLp_trueMean μ j)]
  simp [covariance_const_mul_left, cohortEst, N.cov_cohortLin_trueMean, ha]

lemma integral_portLin [Nonempty T] (d : J → ℝ) : P[N.portLin μ d] = (∑ j, d j) * μ := by
  have ha : ∀ i, ∑ t, M.a i t = 1 := fun i =>
    sum_invVarWeight _ fun t => pow_pos (M.σ_pos i t) 2
  unfold portLin
  rw [integral_finsetSum _ fun j _ => ((N.memLp_cohortEst μ j).const_mul (d j)).integrable
    (by norm_num)]
  simp [integral_const_mul, cohortEst, N.integral_cohortLin, ha, sum_mul]

/-- Any linear cohort estimate with weights summing to one has error variance
`Var(Σₜ cₜ μⱼₜ - μⱼ) = Σₜ cₜ² σⱼₜ²`, the quantity minimised in eq. (23). -/
theorem var_cohortLin_err (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] = ∑ t, c t ^ 2 * M.σ j t ^ 2 := by
  have hX := N.memLp_cohortLin μ j c
  have hY := N.memLp_trueMean μ j
  have hXY : MemLp (fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω) 2 P := hX.sub hY
  rw [← covariance_self hXY.aestronglyMeasurable.aemeasurable,
    covariance_fun_sub_fun_sub hX hY hX hY, covariance_comm (N.trueMean μ j),
    cov_cohortLin_self, cov_cohortLin_trueMean, cov_trueMean, hc]
  simp

/-- Eq. (23) in true variance: among unbiased linear cohort estimates, `μ̂ⱼ`
has the smallest error variance. -/
theorem cohortEst_optimal [Nonempty T] (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortEst μ j ω - N.trueMean μ j ω; P]
      ≤ Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] := by
  have hσ : ∀ t, 0 < M.σ j t ^ 2 := fun t => pow_pos (M.σ_pos j t) 2
  have ha : ∑ t, M.a j t = 1 := sum_invVarWeight _ hσ
  rw [cohortEst, N.var_cohortLin_err μ j _ ha, N.var_cohortLin_err μ j c hc]
  exact invVarWeight_optimal _ hσ c hc

/-- Eq. (24) in true variance: among unbiased linear portfolio estimates built
from the `μ̂ⱼ`, the GLS one has the smallest variance, and it equals `s²`. -/
theorem portEst_optimal (hK : M.K.PosDef) (d : J → ℝ) (hd : ∑ j, d j = 1) :
    Var[N.portEst μ; P] = M.s2 ∧ M.s2 ≤ Var[N.portLin μ d; P] := by
  have : Nonempty J := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hd
  have hvar : ∀ d, Var[N.portLin μ d; P] = d ⬝ᵥ (M.K *ᵥ d) := fun d => by
    rw [← covariance_self (N.memLp_portLin μ d).aestronglyMeasurable.aemeasurable, cov_portLin]
  have hs2 : M.b ⬝ᵥ (M.K *ᵥ M.b) = M.s2 := glsWeight_value hK
  refine ⟨by rw [portEst, hvar, hs2], ?_⟩
  rw [hvar, ← hs2]
  exact glsWeight_optimal hK d hd

/-- Every field of `M.moments j` is the actual moment it names (§2.4). -/
theorem moments_eq [Nonempty T] (hK : M.K.PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.moments j).varCohort ∧
    Var[N.portEst μ; P] = (M.moments j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.moments j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.moments j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.moments j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.moments j).covPortfolioTarget := by
  sorry

/-- The blend is unbiased and its actual mean squared error is `errVar`,
eq. (6): `E[(z μ̂ⱼ + (1 - z) μ̂ - μⱼ)²] = errVar z`. -/
theorem mse_blend [Nonempty T] (hK : M.K.PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.moments j).errVar z := by
  sorry

/-- Eqs. (7)/(26) in true MSE: the credibility factor `zⱼ` minimises the actual
mean squared error of the blend, for every distribution with the assumed
moments. -/
theorem bestZ_mse_optimal [Nonempty T] (hK : M.K.PosDef) (j : J)
    (hgap : 0 < (M.moments j).gap) (z : ℝ) :
    P[fun ω => (N.blend μ j (M.moments j).bestZ ω - N.trueMean μ j ω) ^ 2]
      ≤ P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] := by
  sorry

end Noise

/-- The moment assumptions are consistent exactly when `ρ` is positive
semidefinite: some probability space carries random variables with the
moments of eq. (15) iff `ρ ⪰ 0`. (With no periods there is no noise to
constrain `ρ`, hence `Nonempty T`.) -/
theorem exists_noise_iff [Nonempty T] (M : Model J T) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.Noise P)) ↔ (Matrix.of M.ρ).PosSemidef := by
  sorry

end Model

end Credibility
