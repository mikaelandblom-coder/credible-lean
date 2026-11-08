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

/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs μ j t] = μ := by
  sorry

/-- Eq. (16) is the actual covariance: `cov(μᵢₜ, μⱼₛ) = K̄ᵢⱼᵗˢ`. -/
theorem cov_obs (i j : J) (t s : T) : cov[N.obs μ i t, N.obs μ j s; P] = M.obsCov i j t s := by
  sorry

/-- Eq. (21) is the actual covariance: `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`. -/
theorem cov_cohortEst (i j : J) : cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.K i j := by
  sorry

/-- Any linear cohort estimate with weights summing to one has error variance
`Var(Σₜ cₜ μⱼₜ - μⱼ) = Σₜ cₜ² σⱼₜ²`, the quantity minimised in eq. (23). -/
theorem var_cohortLin_err (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] = ∑ t, c t ^ 2 * M.σ j t ^ 2 := by
  sorry

/-- Eq. (23) in true variance: among unbiased linear cohort estimates, `μ̂ⱼ`
has the smallest error variance. -/
theorem cohortEst_optimal [Nonempty T] (j : J) (c : T → ℝ) (hc : ∑ t, c t = 1) :
    Var[fun ω => N.cohortEst μ j ω - N.trueMean μ j ω; P]
      ≤ Var[fun ω => N.cohortLin μ j c ω - N.trueMean μ j ω; P] := by
  sorry

/-- Eq. (24) in true variance: among unbiased linear portfolio estimates built
from the `μ̂ⱼ`, the GLS one has the smallest variance, and it equals `s²`. -/
theorem portEst_optimal (hK : M.K.PosDef) (d : J → ℝ) (hd : ∑ j, d j = 1) :
    Var[N.portEst μ; P] = M.s2 ∧ M.s2 ≤ Var[N.portLin μ d; P] := by
  sorry

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
