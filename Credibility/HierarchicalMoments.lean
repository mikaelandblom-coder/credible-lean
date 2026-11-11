import Credibility.Hierarchical
import Credibility.Moments

/-!
# The moment layer for group levels (extension, distribution-free)

`Hierarchical.lean` (Bridges 4 and 5) takes the level covariance `L_G` (`τ²` on
the diagonal, `φτ²` within a group, `0` across groups) as given numbers. Here
it is the actual covariance of the levels

  `μⱼ = μ + √((1-φ)τ²) ηⱼ + √(φτ²) γ_g`,  `g` the group of `j`,

for **any** square-integrable `η`, `ε` with the moments of eq. (15) (level
variance `(1-φ)τ²`) and any group effects `γ_g`: centred, of unit variance,
uncorrelated with each other, with `η` and with `ε`. Then `obsCovG` is the
covariance of the observations (so `UnbiasedG` is about the true expectation),
`cov(μ̂ᵢ, μ̂ⱼ) = (K_G)ᵢⱼ`, the six fields of `momentsG` are the moments they
name, and the factor of `bestZ_G_eq` minimises the true mean squared error.

Only the covariances are new: the group effect is a common component
(`Core.Estimates.addCommon`) on top of the thesis model with level variance
`(1-φ)τ²`, and the blend is the Core moment layer (`CoreMoments.lean`) for
`K_G` and `L_G`.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Model

variable {J T G : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
  [DecidableEq G]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Random variables with group levels, under `P`: cohort effects `η` and noise
`ε` as in the thesis model with level variance `(1-φ)τ²`, and group effects
`γ_g`, centred, of unit variance, uncorrelated with each other and with `η`
and `ε`. Only moments are assumed, no distribution. -/
structure NoiseG (M : Model J T) (grp : J → G) (φ : ℝ) (h1 : φ < 1) (P : Measure Ω)
    extends Noise (M.withLevel φ h1) P where
  /-- Group effect `γ_g`. -/
  γ : G → Ω → ℝ
  γ_memLp : ∀ g, MemLp (γ g) 2 P
  γ_mean : ∀ g, P[γ g] = 0
  cov_γ_γ : ∀ g g', cov[γ g, γ g'; P] = if g = g' then 1 else 0
  cov_γ_η : ∀ g j, cov[γ g, η j; P] = 0
  cov_γ_ε : ∀ g j t, cov[γ g, ε j t; P] = 0

namespace NoiseG

variable {M : Model J T} {grp : J → G} {φ : ℝ} {h1 : φ < 1} {P : Measure Ω}
  (N : M.NoiseG grp φ h1 P) (μ : ℝ)

/-- The group component `√(φτ²) γ_g` of cohort `j`, `g` its group. -/
noncomputable def common (j : J) : Ω → ℝ := fun ω => Real.sqrt (φ * M.τ2) * N.γ (grp j) ω

/-- The true key ratio `μⱼ = μ + √((1-φ)τ²) ηⱼ + √(φτ²) γ_g`. -/
noncomputable def trueMean (j : J) : Ω → ℝ :=
  fun ω => N.toNoise.trueMean μ j ω + N.common j ω

/-- The observed key ratio `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`. -/
noncomputable def obs (j : J) (t : T) : Ω → ℝ :=
  fun ω => N.toNoise.obs μ j t ω + N.common j ω

/-- The cohort estimate `μ̂ⱼ = Σₜ aⱼₜ μⱼₜ`, eq. (23). -/
noncomputable def cohortEst (j : J) : Ω → ℝ := fun ω => ∑ t, M.a j t * N.obs μ j t ω

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights of `K_G` (`Core.portEst`). -/
noncomputable abbrev portEst : Ω → ℝ := Core.portEst (M.KG grp φ) (N.cohortEst μ)

/-- The blend `z μ̂ⱼ + (1 - z) μ̂` (`Core.blend`). -/
noncomputable abbrev blend (j : J) (z : ℝ) : Ω → ℝ := Core.blend (M.KG grp φ) (N.cohortEst μ) j z

omit [Fintype J] in
/-- The group effect passes through the cohort weights (`Σₜ aⱼₜ = 1`): `μ̂ⱼ` is the
cohort estimate of the thesis model plus the group component. -/
lemma cohortEst_eq [Nonempty T] (j : J) :
    N.cohortEst μ j = fun ω => N.toNoise.cohortEst μ j ω + N.common j ω := by
  funext ω
  have ha : ∑ t, M.a j t = 1 := sum_invVarWeight _ fun t => pow_pos (M.σ_pos j t) 2
  simp only [cohortEst, obs, mul_add, sum_add_distrib, ← sum_mul, ha, one_mul]
  rfl

omit [Fintype J] [Fintype T] in
lemma memLp_common (j : J) : MemLp (N.common j) 2 P := (N.γ_memLp _).const_mul _

omit [Fintype J] [Fintype T] in
lemma integral_common (j : J) : P[N.common j] = 0 := by
  simp [common, integral_const_mul, N.γ_mean]

omit [Fintype J] [Fintype T] in
/-- `cov(√(φτ²)γ_{g(i)}, √(φτ²)γ_{g(j)}) = φτ²·[g(i) = g(j)]`. -/
lemma cov_common (h0 : 0 ≤ φ) (i j : J) :
    cov[N.common i, N.common j; P] = (φ * M.τ2) • sameGroup grp i j := by
  unfold common
  rw [covariance_const_mul_left, covariance_const_mul_right, N.cov_γ_γ, ← mul_assoc,
    Real.mul_self_sqrt (mul_nonneg h0 M.τ2_pos.le)]
  rfl

variable [IsProbabilityMeasure P]

omit [Fintype J] [Fintype T] in
lemma cov_γ_trueMean (g : G) (j : J) : cov[N.γ g, N.toNoise.trueMean μ j; P] = 0 := by
  rw [show N.toNoise.trueMean μ j
      = fun ω => μ + Real.sqrt (M.withLevel φ h1).τ2 * N.η j ω from rfl,
    covariance_const_add_right (((N.η_memLp j).const_mul _).integrable (by norm_num)),
    covariance_const_mul_right, N.cov_γ_η, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_γ_obs (g : G) (j : J) (t : T) : cov[N.γ g, N.toNoise.obs μ j t; P] = 0 := by
  rw [show N.toNoise.obs μ j t
      = N.toNoise.trueMean μ j + fun ω => M.σ j t * N.ε j t ω from rfl,
    covariance_add_right (N.γ_memLp g) (N.toNoise.memLp_trueMean μ j)
      ((N.ε_memLp j t).const_mul _),
    cov_γ_trueMean, covariance_const_mul_right, N.cov_γ_ε, mul_zero, add_zero]

omit [Fintype J] in
lemma cov_γ_cohortEst (g : G) (j : J) : cov[N.γ g, N.toNoise.cohortEst μ j; P] = 0 := by
  rw [show N.toNoise.cohortEst μ j
      = fun ω => ∑ t, (M.withLevel φ h1).a j t * N.toNoise.obs μ j t ω from rfl,
    covariance_fun_sum_right (fun t => (N.toNoise.memLp_obs μ j t).const_mul _) (N.γ_memLp g)]
  simp [covariance_const_mul_right, cov_γ_obs]

omit [Fintype J] [Fintype T] in
lemma cov_common_trueMean (i j : J) : cov[N.common i, N.toNoise.trueMean μ j; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, cov_γ_trueMean, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_common_obs (i j : J) (t : T) : cov[N.common i, N.toNoise.obs μ j t; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, cov_γ_obs, mul_zero]

omit [Fintype J] in
lemma cov_common_cohortEst (i j : J) : cov[N.common i, N.toNoise.cohortEst μ j; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, cov_γ_cohortEst, mul_zero]

omit [Fintype J] [Fintype T] in
lemma memLp_obs (j : J) (t : T) : MemLp (N.obs μ j t) 2 P :=
  (N.toNoise.memLp_obs μ j t).add (N.memLp_common j)

omit [Fintype J] in
/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs μ j t] = μ := by
  rw [show N.obs μ j t = fun ω => N.toNoise.obs μ j t ω + N.common j ω from rfl,
    integral_add ((N.toNoise.memLp_obs μ j t).integrable (by norm_num))
      ((N.memLp_common j).integrable (by norm_num)), N.toNoise.obs_mean, N.integral_common,
    add_zero]

omit [Fintype J] in
/-- Eq. (16) with group levels is the actual covariance:
`cov(μᵢₜ, μⱼₛ) = σᵢₜσⱼₛρᵢⱼδₜₛ + (L_G)ᵢⱼ`. -/
theorem cov_obs (h0 : 0 ≤ φ) (i j : J) (t s : T) :
    cov[N.obs μ i t, N.obs μ j s; P] = M.obsCovG grp φ i j t s := by
  rw [show N.obs μ i t = fun ω => N.toNoise.obs μ i t ω + N.common i ω from rfl,
    show N.obs μ j s = fun ω => N.toNoise.obs μ j s ω + N.common j ω from rfl,
    cov_add_add (N.toNoise.memLp_obs μ i t) (N.memLp_common i)
      (N.toNoise.memLp_obs μ j s) (N.memLp_common j),
    N.toNoise.cov_obs, covariance_comm (N.toNoise.obs μ i t), cov_common_obs, cov_common_obs,
    N.cov_common h0, obsCovG, levelCovG_apply']
  simp only [obsCov, sameGroup, of_apply, smul_eq_mul]
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  have hσ : (M.withLevel φ h1).σ = M.σ := rfl
  have hρ : (M.withLevel φ h1).ρ = M.ρ := rfl
  rw [hτ, hσ, hρ]
  ring

/-- §2.8 in true expectation with group levels: for any quadratic form of the
data, `E[Σₚ,q Qₚq μₚ μq] = M.EG grp φ μ Q`. So `UnbiasedG f θ` means
`E f = θ` for any random variables with these moments. -/
theorem integral_quad (h0 : 0 ≤ φ) (Q : J × T → J × T → ℝ) :
    P[fun ω => quad Q (fun p => N.obs μ p.1 p.2 ω)] = M.EG grp φ μ Q :=
  integral_quad_of_cov (fun p => N.obs μ p.1 p.2) _ μ Q (fun _ => True)
    (fun _ _ _ => ⟨trivial, trivial⟩) (fun p _ => N.memLp_obs μ p.1 p.2)
    (fun p _ => N.obs_mean μ p.1 p.2) (fun p q _ _ => N.cov_obs μ h0 p.1 q.1 p.2 q.2)

/-- The thesis estimates and levels for `(1-φ)τ²`, plus the group component:
estimates and levels for `K' + R` and `(1-φ)τ²·I + R`, `R = φτ²·[g(i) = g(j)]`. -/
noncomputable def addCommon [Nonempty T] (h0 : 0 ≤ φ) :
    Core.Estimates ((M.withLevel φ h1).K + (φ * M.τ2) • sameGroup grp)
      ((M.withLevel φ h1).τ2 • (1 : Matrix J J ℝ) + (φ * M.τ2) • sameGroup grp) μ P :=
  (N.toNoise.toEstimates μ).addCommon N.common _ N.memLp_common N.integral_common
    (N.cov_common h0) (N.cov_common_cohortEst μ) (N.cov_common_trueMean μ)

/-- The cohort estimates and levels with group levels as an instance of the Core
moment layer: `cov(μ̂ᵢ, μ̂ⱼ) = (K_G)ᵢⱼ` and level covariance `L_G`. -/
noncomputable def toEstimates [Nonempty T] (h0 : 0 ≤ φ) :
    Core.Estimates (M.KG grp φ) (levelCovG grp M.τ2 φ) μ P where
  est := N.cohortEst μ
  level := N.trueMean μ
  est_memLp j := by rw [N.cohortEst_eq]; exact (N.addCommon μ h0).est_memLp j
  level_memLp j := (N.addCommon μ h0).level_memLp j
  est_mean j := by rw [N.cohortEst_eq]; exact (N.addCommon μ h0).est_mean j
  level_mean j := (N.addCommon μ h0).level_mean j
  cov_est i j := by
    rw [N.cohortEst_eq, N.cohortEst_eq, M.KG_eq_add_sameGroup grp h1]
    exact (N.addCommon μ h0).cov_est i j
  cov_level_est i j := by
    rw [N.cohortEst_eq, levelCovG_eq_add_sameGroup]
    exact (N.addCommon μ h0).cov_level_est i j
  cov_level i j := by
    rw [levelCovG_eq_add_sameGroup]
    exact (N.addCommon μ h0).cov_level i j

omit [Fintype J] in
/-- `K_G` is the actual covariance of the cohort estimates: `cov(μ̂ᵢ, μ̂ⱼ) = (K_G)ᵢⱼ`. -/
theorem cov_cohortEst [Nonempty T] (h0 : 0 ≤ φ) (i j : J) :
    cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.KG grp φ i j :=
  (N.toEstimates μ h0).cov_est i j

omit [Fintype J] in
/-- `L_G` is the actual covariance of the levels: `cov(μᵢ, μⱼ) = (L_G)ᵢⱼ`. -/
theorem cov_trueMean [Nonempty T] (h0 : 0 ≤ φ) (i j : J) :
    cov[N.trueMean μ i, N.trueMean μ j; P] = levelCovG grp M.τ2 φ i j :=
  (N.toEstimates μ h0).cov_level i j

omit [DecidableEq T] in
/-- The blend moments with group levels are the Core ones with `Var(μ̂ⱼ) = (K_G)ⱼⱼ`. -/
lemma momentsG_eq_levelMoments' (M : Model J T) (grp : J → G) (φ : ℝ) (j : J) :
    M.momentsG grp φ j
      = Core.levelMoments (M.KG grp φ) (levelCovG grp M.τ2 φ) (M.KG grp φ j j) j := by
  rw [momentsG_eq_levelMoments]
  simp [KG, levelCovG_apply, errCov, M.ρ_self]

/-- Every field of `M.momentsG grp φ j` is the actual moment it names. -/
theorem moments_eq [Nonempty T] (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.momentsG grp φ j).varCohort ∧
    Var[N.portEst μ; P] = (M.momentsG grp φ j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.momentsG grp φ j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.momentsG grp φ j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.momentsG grp φ j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.momentsG grp φ j).covPortfolioTarget := by
  rw [momentsG_eq_levelMoments']
  exact (N.toEstimates μ h0).levelMoments_eq hK j

/-- With group levels the blend is unbiased and its actual mean squared error
is `errVar`, eq. (6), for the moments `momentsG`. -/
theorem mse_blend [Nonempty T] (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.momentsG grp φ j).errVar z := by
  rw [momentsG_eq_levelMoments']
  exact (N.toEstimates μ h0).mse_blend hK j z

/-- Eq. (26) with group levels, in true MSE: `zⱼ` (`bestZ_G_eq`) minimises the
actual mean squared error of the blend, for every distribution with the
assumed moments. -/
theorem bestZ_mse_optimal [Nonempty T] (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J)
    (hgap : 0 < (M.momentsG grp φ j).gap) (z : ℝ) :
    P[fun ω => (N.blend μ j (M.momentsG grp φ j).bestZ ω - N.trueMean μ j ω) ^ 2]
      ≤ P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] := by
  rw [N.mse_blend μ h0 hK j, N.mse_blend μ h0 hK j]
  exact (M.momentsG grp φ j).bestZ_optimal hgap z

end NoiseG

/-! ### Consistency: when do such random variables exist? -/

namespace Noise

variable {Ω' : Type*} [MeasurableSpace Ω'] {M : Model J T} {P : Measure Ω} {P' : Measure Ω'}

/-- The thesis noise read through a map `Z : Ω' → Ω` with law `P` under `P'`
(e.g. the first coordinate of a product space): the same moments. -/
noncomputable def comp (N : M.Noise P) {Z : Ω' → Ω} (hZ : HasLaw Z P P') : M.Noise P' where
  η j ω := N.η j (Z ω)
  ε j t ω := N.ε j t (Z ω)
  η_memLp j := hZ.memLp_comp (N.η_memLp j)
  ε_memLp j t := hZ.memLp_comp (N.ε_memLp j t)
  η_mean j := (hZ.integral_comp (f := N.η j) (N.η_memLp j).aestronglyMeasurable).trans
    (N.η_mean j)
  ε_mean j t := (hZ.integral_comp (f := N.ε j t) (N.ε_memLp j t).aestronglyMeasurable).trans
    (N.ε_mean j t)
  cov_η_η i j := by
    rw [hZ.covariance_fun_comp (N.η_memLp i).aemeasurable (N.η_memLp j).aemeasurable]
    exact N.cov_η_η i j
  cov_η_ε i j t := by
    rw [hZ.covariance_fun_comp (N.η_memLp i).aemeasurable (N.ε_memLp j t).aemeasurable]
    exact N.cov_η_ε i j t
  cov_ε_ε i j t s := by
    rw [hZ.covariance_fun_comp (N.ε_memLp i t).aemeasurable (N.ε_memLp j s).aemeasurable]
    exact N.cov_ε_ε i j t s

end Noise

/-- The group-level assumptions are consistent exactly when `ρ` is positive
semidefinite, as for the thesis model (`exists_noise_iff`): group effects add
no constraint. Witness: the thesis noise with level variance `(1-φ)τ²` on one
factor, independent standard normal `γ_g` on the other (a witness only; the
model stays distribution-free). Groups are labels in `Type`, like `Ω`. -/
theorem exists_noiseG_iff {G : Type} [DecidableEq G] [Nonempty T] (M : Model J T)
    (grp : J → G) (φ : ℝ) (h1 : φ < 1) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.NoiseG grp φ h1 P)) ↔ (Matrix.of M.ρ).PosSemidef := by
  constructor
  · -- Necessity: forget `γ`; the noise is that of the thesis model with the same `ρ`.
    rintro ⟨Ω, _, P, _, ⟨N⟩⟩
    exact (M.withLevel φ h1).exists_noise_iff.mp ⟨Ω, _, P, inferInstance, ⟨N.toNoise⟩⟩
  · -- Sufficiency: thesis noise on `Ω₀`, independent `γ_g ~ N(0,1)` on `G → ℝ`.
    intro hρ
    obtain ⟨Ω₀, _, P₀, _, ⟨N₀⟩⟩ := (M.withLevel φ h1).exists_noise_iff.mpr hρ
    set Q : Measure (G → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1 with hQdef
    have hγ : ∀ g, HasLaw (fun x : G → ℝ => x g) (gaussianReal 0 1) Q :=
      fun g => (measurePreserving_eval_infinitePi (fun _ : G => gaussianReal 0 1) g).hasLaw
    have hQ : IsProbabilityMeasure Q := by dsimp only [Q]; infer_instance
    have hind : iIndepFun (fun g (x : G → ℝ) => x g) Q := by
      rw [hQdef]; exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
    clear_value Q
    have hsnd : HasLaw Prod.snd Q (P₀.prod Q) := measurePreserving_snd.hasLaw
    have hfst : HasLaw Prod.fst P₀ (P₀.prod Q) := measurePreserving_fst.hasLaw
    have hm : ∀ g, MemLp (fun x : G → ℝ => x g) 2 Q :=
      fun g => (hγ g).memLp_comp (memLp_id_gaussianReal' 2 (by simp))
    have hm' : ∀ g, MemLp (fun p : Ω₀ × (G → ℝ) => p.2 g) 2 (P₀.prod Q) :=
      fun g => hsnd.memLp_comp (hm g)
    have hmean : ∀ g, ∫ p, p.2 g ∂(P₀.prod Q) = 0 := fun g =>
      (hsnd.integral_comp (f := fun x : G → ℝ => x g) (hm g).aestronglyMeasurable).trans
        ((hγ g).integral_eq.trans integral_id_gaussianReal)
    have hcov : ∀ g g', cov[fun p : Ω₀ × (G → ℝ) => p.2 g, fun p => p.2 g'; P₀.prod Q]
        = if g = g' then 1 else 0 := fun g g' => by
      rw [hsnd.covariance_fun_comp (f := fun x : G → ℝ => x g) (g := fun x => x g')
        (hm g).aemeasurable (hm g').aemeasurable]
      by_cases h : g = g'
      · subst h
        rw [covariance_self (hm g).aemeasurable, (hγ g).variance_eq, variance_id_gaussianReal]
        simp
      · simp only [h, ↓reduceIte]
        exact (hind.indepFun h).covariance_eq_zero (hm g) (hm g')
    have hη : ∀ g j, cov[fun p : Ω₀ × (G → ℝ) => p.2 g, fun p => N₀.η j p.1; P₀.prod Q] = 0 :=
      fun g j => by
        rw [covariance_comm]
        exact covariance_fst_snd_prod (μ := P₀) (ν := Q) (X := N₀.η j)
          (Y := fun x : G → ℝ => x g) (N₀.η_memLp j) (hm g)
    have hε : ∀ g j t,
        cov[fun p : Ω₀ × (G → ℝ) => p.2 g, fun p => N₀.ε j t p.1; P₀.prod Q] = 0 :=
      fun g j t => by
        rw [covariance_comm]
        exact covariance_fst_snd_prod (μ := P₀) (ν := Q) (X := N₀.ε j t)
          (Y := fun x : G → ℝ => x g) (N₀.ε_memLp j t) (hm g)
    let N := N₀.comp hfst
    exact ⟨Ω₀ × (G → ℝ), inferInstance, P₀.prod Q, inferInstance,
      ⟨{ toNoise := N
         γ := fun g p => p.2 g
         γ_memLp := hm'
         γ_mean := hmean
         cov_γ_γ := hcov
         cov_γ_η := hη
         cov_γ_ε := hε }⟩⟩

end Model
end Credibility
