import Credibility.Expectation
import Credibility.UnequalMoments

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

Every cohort is observed in every period, so `Noise` is `Unequal.Noise` with
`Tⱼ = T` (`Noise.toUnequal`): the theorems here are corollaries of
`UnequalMoments.lean`.
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

/-- A noise for the thesis model is one for `Tⱼ = T`. -/
def toUnequal [Nonempty T] : M.toUnequal.Noise P where
  η := N.η
  ε := N.ε
  η_memLp := N.η_memLp
  ε_memLp := fun j t _ => N.ε_memLp j t
  η_mean := N.η_mean
  ε_mean := fun j t _ => N.ε_mean j t
  cov_η_η := N.cov_η_η
  cov_η_ε := fun i j t _ => N.cov_η_ε i j t
  cov_ε_ε := fun i j t _ s _ => N.cov_ε_ε i j t s

/-- …and conversely. -/
def ofUnequal [Nonempty T] (N : M.toUnequal.Noise P) : M.Noise P where
  η := N.η
  ε := N.ε
  η_memLp := N.η_memLp
  ε_memLp := fun j t => N.ε_memLp j t (mem_univ t)
  η_mean := N.η_mean
  ε_mean := fun j t => N.ε_mean j t (mem_univ t)
  cov_η_η := N.cov_η_η
  cov_η_ε := fun i j t => N.cov_η_ε i j t (mem_univ t)
  cov_ε_ε := fun i j t s => N.cov_ε_ε i j t (mem_univ t) s (mem_univ s)

section Full

variable [Nonempty T]

omit [Fintype J] in
lemma toUnequal_trueMean (j : J) : N.toUnequal.trueMean μ j = N.trueMean μ j := rfl

omit [Fintype J] in
lemma toUnequal_obsVal (j : J) (t : T) : N.toUnequal.obsVal μ j t = N.obs μ j t := rfl

omit [Fintype J] in
lemma toUnequal_cohortLin (j : J) (c : T → ℝ) :
    N.toUnequal.cohortLin μ j c = N.cohortLin μ j c := rfl

omit [Fintype J] in
lemma toUnequal_cohortEst (j : J) : N.toUnequal.cohortEst μ j = N.cohortEst μ j := by
  rw [Unequal.Noise.cohortEst, toUnequal_a, toUnequal_cohortLin]; rfl

lemma toUnequal_portLin (d : J → ℝ) : N.toUnequal.portLin μ d = N.portLin μ d := by
  show (fun ω => ∑ j, d j * N.toUnequal.cohortEst μ j ω) = _
  simp only [toUnequal_cohortEst]; rfl

lemma toUnequal_portEst : N.toUnequal.portEst μ = N.portEst μ := by
  rw [Unequal.Noise.portEst, toUnequal_b, toUnequal_portLin]; rfl

lemma toUnequal_blend (j : J) (z : ℝ) : N.toUnequal.blend μ j z = N.blend μ j z := by
  show (fun ω => z * N.toUnequal.cohortEst μ j ω + (1 - z) * N.toUnequal.portEst μ ω) = _
  simp only [toUnequal_cohortEst, toUnequal_portEst]; rfl

end Full

variable [IsProbabilityMeasure P]

omit [Fintype J] in
/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs μ j t] = μ := by
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.obsVal_mean μ j (mem_univ t)

omit [Fintype J] in
/-- Eq. (16) is the actual covariance: `cov(μᵢₜ, μⱼₛ) = K̄ᵢⱼᵗˢ`. -/
theorem cov_obs (i j : J) (t s : T) : cov[N.obs μ i t, N.obs μ j s; P] = M.obsCov i j t s := by
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.cov_obsVal μ i j (mem_univ t) (mem_univ s)

/-- §2.8 in true expectation: for any quadratic form `quad Q` of the data,
`E[Σₚ,q Qₚq μₚ μq] = M.E μ Q`. So `Unbiased f θ` means `E f(μ₁₁, …) = θ`
for any random variables with the moments of eq. (15). -/
theorem integral_quad (Q : J × T → J × T → ℝ) :
    P[fun ω => quad Q (fun p => N.obs μ p.1 p.2 ω)] = M.E μ Q := by
  have hL : ∀ p : J × T, MemLp (N.obs μ p.1 p.2) 2 P := fun p => by
    have : Nonempty T := ⟨p.2⟩
    exact N.toUnequal.memLp_obsVal μ p.1 (mem_univ p.2)
  have hI : ∀ p q : J × T, Integrable (fun ω => N.obs μ p.1 p.2 ω * N.obs μ q.1 q.2 ω) P :=
    fun p q => (hL p).integrable_mul (hL q)
  have hm : ∀ p q : J × T,
      P[fun ω => N.obs μ p.1 p.2 ω * N.obs μ q.1 q.2 ω] = M.cov p q + μ ^ 2 := fun p q => by
    have h := covariance_eq_sub (hL p) (hL q)
    rw [N.cov_obs, N.obs_mean, N.obs_mean] at h
    rw [cov, h]
    simp only [Pi.mul_def]
    ring
  simp only [quad, E, Ecov, mul_assoc]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => (hI p q).const_mul _]
  refine sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hI p q).const_mul _]
  refine sum_congr rfl fun q _ => ?_
  rw [integral_const_mul, hm]

omit [Fintype J] in
/-- Eq. (21) is the actual covariance: `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`. -/
theorem cov_cohortEst (i j : J) : cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.K i j := by
  rcases isEmpty_or_nonempty T with hT | hT
  · simp [cohortEst, cohortLin, K, covariance]
  · rw [← N.toUnequal_cohortEst, ← N.toUnequal_cohortEst, Unequal.Noise.cov_cohortEst,
      toUnequal_K]

omit [Fintype J] in
/-- Any linear cohort estimate with weights summing to one has error variance
`Var(Σₜ cₜ μⱼₜ - μⱼ) = Σₜ cₜ² σⱼₜ²`, the quantity minimised in eq. (23). -/
theorem var_cohortLin_err (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] = ∑ t, c t ^ 2 * M.σ j t ^ 2 := by
  obtain ⟨t, -, -⟩ := exists_ne_zero_of_sum_ne_zero (hc.trans_ne one_ne_zero)
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.var_cohortLin_err μ j c hc

omit [Fintype J] in
/-- Eq. (23) in true variance: among unbiased linear cohort estimates, `μ̂ⱼ`
has the smallest error variance. -/
theorem cohortEst_optimal [Nonempty T] (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortEst μ j ω - N.trueMean μ j ω; P]
      ≤ Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] := by
  rw [← N.toUnequal_cohortEst]
  exact N.toUnequal.cohortEst_optimal μ j c hc

/-- Eq. (24) in true variance: among unbiased linear portfolio estimates built
from the `μ̂ⱼ`, the GLS one has the smallest variance, and it equals `s²`. -/
theorem portEst_optimal (hK : M.K.PosDef) (d : J → ℝ) (hd : ∑ j, d j = 1) :
    Var[N.portEst μ; P] = M.s2 ∧ M.s2 ≤ Var[N.portLin μ d; P] := by
  -- `Σ dⱼ = 1` gives a cohort, and `K ≻ 0` then a period (`Tⱼ = T` needs `T ≠ ∅`).
  obtain ⟨j, -, -⟩ := exists_ne_zero_of_sum_ne_zero (hd.trans_ne one_ne_zero)
  have := M.nonempty_of_posDef hK j
  rw [← N.toUnequal_portEst, ← N.toUnequal_portLin, ← M.toUnequal_s2]
  exact N.toUnequal.portEst_optimal μ (by rw [toUnequal_K]; exact hK) d hd

/-- Every field of `M.moments j` is the actual moment it names (§2.4). -/
theorem moments_eq [Nonempty T] (hK : M.K.PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.moments j).varCohort ∧
    Var[N.portEst μ; P] = (M.moments j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.moments j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.moments j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.moments j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.moments j).covPortfolioTarget := by
  rw [← N.toUnequal_cohortEst, ← N.toUnequal_portEst, ← N.toUnequal_trueMean,
    ← M.toUnequal_moments]
  exact N.toUnequal.moments_eq μ (by rw [toUnequal_K]; exact hK) j

/-- The blend is unbiased and its actual mean squared error is `errVar`,
eq. (6): `E[(z μ̂ⱼ + (1 - z) μ̂ - μⱼ)²] = errVar z`. -/
theorem mse_blend [Nonempty T] (hK : M.K.PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.moments j).errVar z := by
  rw [← N.toUnequal_blend, ← N.toUnequal_trueMean, ← M.toUnequal_moments]
  exact N.toUnequal.mse_blend μ (by rw [toUnequal_K]; exact hK) j z

/-- Eqs. (7)/(26) in true MSE: the credibility factor `zⱼ` minimises the actual
mean squared error of the blend, for every distribution with the assumed
moments. -/
theorem bestZ_mse_optimal [Nonempty T] (hK : M.K.PosDef) (j : J)
    (hgap : 0 < (M.moments j).gap) (z : ℝ) :
    P[fun ω => (N.blend μ j (M.moments j).bestZ ω - N.trueMean μ j ω) ^ 2]
      ≤ P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] := by
  rw [← N.toUnequal_blend, ← N.toUnequal_blend, ← N.toUnequal_trueMean, ← M.toUnequal_moments]
  exact N.toUnequal.bestZ_mse_optimal μ (by rw [toUnequal_K]; exact hK) j
    (by rw [toUnequal_moments]; exact hgap) z

end Noise

omit [Fintype J] in
/-- With full series the witness table of `UnequalMoments` is `gram`. -/
lemma gram_eq_unequal [Nonempty T] (M : Model J T) : M.gram = M.toUnequal.gram := by
  funext u v
  cases u <;> cases v <;> simp [gram, Unequal.gram, Unequal.corrAt, toUnequal]

/-- The covariance table of the basic variables is positive semidefinite when `ρ` is. -/
theorem gram_posSemidef (M : Model J T) (hρ : (Matrix.of M.ρ).PosSemidef) :
    (Matrix.of M.gram).PosSemidef := by
  rcases isEmpty_or_nonempty T with hT | hT
  · -- No noise variables: `gram` is the identity on the `ηⱼ`.
    convert PosSemidef.one (n := J ⊕ (J × T)) (R := ℝ)
    ext u v
    rcases u with i | ⟨_, t⟩
    · rcases v with j | ⟨_, t⟩
      · simp [gram, Matrix.one_apply]
      · exact isEmptyElim t
    · exact isEmptyElim t
  · rw [gram_eq_unequal]
    exact M.toUnequal.gram_posSemidef fun _ => hρ.submatrix _

/-- The moment assumptions are consistent exactly when `ρ` is positive
semidefinite: some probability space carries random variables with the
moments of eq. (15) iff `ρ ⪰ 0`. (With no periods there is no noise to
constrain `ρ`, hence `Nonempty T`.) -/
theorem exists_noise_iff [Nonempty T] (M : Model J T) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.Noise P)) ↔ (Matrix.of M.ρ).PosSemidef := by
  -- Noises agree with those for `Tⱼ = T`, whose blocks are all of `ρ`.
  have hN : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω),
      Nonempty (M.Noise P) ↔ Nonempty (M.toUnequal.Noise P) :=
    fun _ => ⟨fun ⟨N⟩ => ⟨N.toUnequal⟩, fun ⟨N⟩ => ⟨Noise.ofUnequal N⟩⟩
  have hB : (∀ t, (M.toUnequal.block t).PosSemidef) ↔ (Matrix.of M.ρ).PosSemidef := by
    refine ⟨fun h => ?_, fun hρ t => hρ.submatrix _⟩
    obtain ⟨t⟩ := ‹Nonempty T›
    convert (h t).submatrix (fun j => (⟨j, mem_univ t⟩ : {j // t ∈ M.toUnequal.obs j}))
    ext i j; rfl
  simp only [hN]
  rw [Unequal.exists_noise_iff, hB]

end Model

end Credibility
