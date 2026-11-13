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
(`Core.Estimates.addCommon`) on top of the model with level variance
`(1-φ)τ²`, and the blend is the Core moment layer (`CoreMoments.lean`) for
`K_G` and `L_G`.

This is proved once with unequal lengths (`Unequal.NoiseG`, on top of
`Unequal.Noise`; consistent iff every block `ρ_t ⪰ 0`,
`Unequal.exists_noiseG_iff`). The thesis model is the case `Tⱼ = T`
(`Model.NoiseG.toUnequal`): its results are corollaries.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

/-! ### Group levels with unequal lengths

Cohort `j` is observed only in `Tⱼ`, and the noise is assumed only on observed
cells (`Unequal.Noise`). The group effect passes through the cohort weights
(they sum to one over `Tⱼ`), so it is a common component on top of
`Unequal.Noise.toEstimates`. -/

namespace Unequal

variable {J T G : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
  [DecidableEq G]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Random variables with group levels and unequal lengths, under `P`: cohort
effects `η` and noise `ε` as in `Unequal.Noise` with level variance `(1-φ)τ²`
(noise only on observed cells), and group effects `γ_g`, centred, of unit
variance, uncorrelated with each other, with `η` and with the observed `ε`.
Only moments are assumed, no distribution. -/
structure NoiseG (M : Unequal J T) (grp : J → G) (φ : ℝ) (h1 : φ < 1) (P : Measure Ω)
    extends Noise (M.withLevel φ h1) P where
  /-- Group effect `γ_g`. -/
  γ : G → Ω → ℝ
  γ_memLp : ∀ g, MemLp (γ g) 2 P
  γ_mean : ∀ g, P[γ g] = 0
  cov_γ_γ : ∀ g g', cov[γ g, γ g'; P] = if g = g' then 1 else 0
  cov_γ_η : ∀ g j, cov[γ g, η j; P] = 0
  cov_γ_ε : ∀ g j, ∀ t ∈ M.obs j, cov[γ g, ε j t; P] = 0

namespace NoiseG

variable {M : Unequal J T} {grp : J → G} {φ : ℝ} {h1 : φ < 1} {P : Measure Ω}
  (N : M.NoiseG grp φ h1 P) (μ : ℝ)

/-- The group component `√(φτ²) γ_g` of cohort `j`, `g` its group. -/
noncomputable def common (j : J) : Ω → ℝ := fun ω => Real.sqrt (φ * M.τ2) * N.γ (grp j) ω

/-- The true key ratio `μⱼ = μ + √((1-φ)τ²) ηⱼ + √(φτ²) γ_g`. -/
noncomputable def trueMean (j : J) : Ω → ℝ :=
  fun ω => N.toNoise.trueMean μ j ω + N.common j ω

/-- The key ratio `μⱼₜ = μⱼ + σⱼₜ εⱼₜ` (observed for `t ∈ Tⱼ`). -/
noncomputable def obsVal (j : J) (t : T) : Ω → ℝ :=
  fun ω => N.toNoise.obsVal μ j t ω + N.common j ω

/-- The cohort estimate `μ̂ⱼ = Σ_{t∈Tⱼ} aⱼₜ μⱼₜ`, eq. (23) on `Tⱼ`. -/
noncomputable def cohortEst (j : J) : Ω → ℝ := fun ω => ∑ t ∈ M.obs j, M.a j t * N.obsVal μ j t ω

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights of `K_G` (`Core.portEst`). -/
noncomputable abbrev portEst : Ω → ℝ := Core.portEst (M.KG grp φ) (N.cohortEst μ)

/-- The blend `z μ̂ⱼ + (1 - z) μ̂` (`Core.blend`). -/
noncomputable abbrev blend (j : J) (z : ℝ) : Ω → ℝ := Core.blend (M.KG grp φ) (N.cohortEst μ) j z

omit [Fintype J] [Fintype T] in
/-- The group effect passes through the cohort weights (`Σ_{t∈Tⱼ} aⱼₜ = 1`). -/
lemma cohortEst_eq (j : J) :
    N.cohortEst μ j = fun ω => N.toNoise.cohortEst μ j ω + N.common j ω := by
  funext ω
  simp only [cohortEst, obsVal, mul_add, sum_add_distrib, ← sum_mul, M.sum_a, one_mul]
  rfl

omit [Fintype J] [Fintype T] in
lemma memLp_common (j : J) : MemLp (N.common j) 2 P := (N.γ_memLp _).const_mul _

omit [Fintype J] [Fintype T] in
lemma integral_common (j : J) : P[N.common j] = 0 := by
  simp [common, integral_const_mul, N.γ_mean]

omit [Fintype J] [Fintype T] in
/-- `cov(√(φτ²)γ_{g(i)}, √(φτ²)γ_{g(j)}) = φτ²·[g(i) = g(j)]`. -/
lemma cov_common (h0 : 0 ≤ φ) (i j : J) :
    cov[N.common i, N.common j; P] = (φ * M.τ2) • Model.sameGroup grp i j := by
  unfold common
  rw [covariance_const_mul_left, covariance_const_mul_right, N.cov_γ_γ, ← mul_assoc,
    Real.mul_self_sqrt (mul_nonneg h0 M.τ2_pos.le)]
  rfl

variable [IsProbabilityMeasure P]

omit [Fintype J] [Fintype T] in
lemma cov_γ_trueMean (g : G) (j : J) : cov[N.γ g, N.toNoise.trueMean μ j; P] = 0 := by
  rw [Noise.trueMean_def,
    covariance_const_add_right (((N.η_memLp j).const_mul _).integrable (by norm_num)),
    covariance_const_mul_right, N.cov_γ_η, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_γ_obsVal (g : G) (j : J) {t : T} (ht : t ∈ M.obs j) :
    cov[N.γ g, N.toNoise.obsVal μ j t; P] = 0 := by
  rw [show N.toNoise.obsVal μ j t
      = N.toNoise.trueMean μ j + fun ω => M.σ j t * N.ε j t ω from rfl,
    covariance_add_right (N.γ_memLp g) (N.toNoise.memLp_trueMean μ j)
      ((N.ε_memLp j t ht).const_mul _),
    cov_γ_trueMean, covariance_const_mul_right, N.cov_γ_ε g j t ht, mul_zero, add_zero]

omit [Fintype J] [Fintype T] in
lemma cov_γ_cohortEst (g : G) (j : J) : cov[N.γ g, N.toNoise.cohortEst μ j; P] = 0 := by
  rw [show N.toNoise.cohortEst μ j
      = fun ω => ∑ t ∈ M.obs j, M.a j t * N.toNoise.obsVal μ j t ω from rfl,
    covariance_fun_sum_right' (s := M.obs j)
      (X := fun t ω => M.a j t * N.toNoise.obsVal μ j t ω)
      (fun t ht => (N.toNoise.memLp_obsVal μ j ht).const_mul _) (N.γ_memLp g)]
  exact sum_eq_zero fun t ht => by rw [covariance_const_mul_right, N.cov_γ_obsVal μ g j ht, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_common_trueMean (i j : J) : cov[N.common i, N.toNoise.trueMean μ j; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, cov_γ_trueMean, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_common_obsVal (i j : J) {t : T} (ht : t ∈ M.obs j) :
    cov[N.common i, N.toNoise.obsVal μ j t; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, N.cov_γ_obsVal μ _ j ht, mul_zero]

omit [Fintype J] [Fintype T] in
lemma cov_common_cohortEst (i j : J) : cov[N.common i, N.toNoise.cohortEst μ j; P] = 0 := by
  unfold common
  rw [covariance_const_mul_left, cov_γ_cohortEst, mul_zero]

omit [Fintype J] [Fintype T] in
lemma memLp_obsVal (j : J) {t : T} (ht : t ∈ M.obs j) : MemLp (N.obsVal μ j t) 2 P :=
  (N.toNoise.memLp_obsVal μ j ht).add (N.memLp_common j)

omit [Fintype J] [Fintype T] in
/-- The observed key ratios are unbiased: `E[μⱼₜ] = μ` for `t ∈ Tⱼ`. -/
theorem obsVal_mean (j : J) {t : T} (ht : t ∈ M.obs j) : P[N.obsVal μ j t] = μ := by
  rw [show N.obsVal μ j t = fun ω => N.toNoise.obsVal μ j t ω + N.common j ω from rfl,
    integral_add ((N.toNoise.memLp_obsVal μ j ht).integrable (by norm_num))
      ((N.memLp_common j).integrable (by norm_num)), N.toNoise.obsVal_mean μ j ht,
    N.integral_common, add_zero]

omit [Fintype J] [Fintype T] in
/-- Eq. (16) with group levels on the observed cells is the actual covariance:
`cov(μᵢₜ, μⱼₛ) = σᵢₜσⱼₛρᵢⱼδₜₛ + (L_G)ᵢⱼ` for `t ∈ Tᵢ`, `s ∈ Tⱼ`. -/
theorem cov_obsVal (h0 : 0 ≤ φ) (i j : J) {t s : T} (ht : t ∈ M.obs i) (hs : s ∈ M.obs j) :
    cov[N.obsVal μ i t, N.obsVal μ j s; P] = M.toModel.obsCovG grp φ i j t s := by
  rw [show N.obsVal μ i t = fun ω => N.toNoise.obsVal μ i t ω + N.common i ω from rfl,
    show N.obsVal μ j s = fun ω => N.toNoise.obsVal μ j s ω + N.common j ω from rfl,
    cov_add_add (N.toNoise.memLp_obsVal μ i ht) (N.memLp_common i)
      (N.toNoise.memLp_obsVal μ j hs) (N.memLp_common j),
    N.toNoise.cov_obsVal μ i j ht hs, covariance_comm (N.toNoise.obsVal μ i t),
    N.cov_common_obsVal μ j i ht, N.cov_common_obsVal μ i j hs,
    N.cov_common h0, Model.obsCovG, Model.levelCovG_apply']
  simp only [Model.obsCov, Model.sameGroup, of_apply, smul_eq_mul]
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  have hσ : (M.withLevel φ h1).σ = M.σ := rfl
  have hρ : (M.withLevel φ h1).ρ = M.ρ := rfl
  rw [hτ, hσ, hρ]
  ring

/-- §2.8 in true expectation with group levels and unequal lengths: for a
quadratic form reading only observed cells,
`E[Σₚ,q Qₚq μₚ μq] = M.toModel.EG grp φ μ Q`. -/
theorem integral_quad (h0 : 0 ≤ φ) (Q : J × T → J × T → ℝ)
    (hQ : ∀ p q, Q p q ≠ 0 → p.2 ∈ M.obs p.1 ∧ q.2 ∈ M.obs q.1) :
    P[fun ω => Model.quad Q (fun p => N.obsVal μ p.1 p.2 ω)] = M.toModel.EG grp φ μ Q :=
  Model.integral_quad_of_cov (fun p => N.obsVal μ p.1 p.2) _ μ Q (fun p => p.2 ∈ M.obs p.1) hQ
    (fun p hp => N.memLp_obsVal μ p.1 hp) (fun p hp => N.obsVal_mean μ p.1 hp)
    (fun p q hp hq => N.cov_obsVal μ h0 p.1 q.1 hp hq)

omit [Fintype T] in
/-- The estimates and levels for `(1-φ)τ²`, plus the group component. -/
noncomputable def addCommon (h0 : 0 ≤ φ) :
    Core.Estimates ((M.withLevel φ h1).K + (φ * M.τ2) • Model.sameGroup grp)
      ((M.withLevel φ h1).τ2 • (1 : Matrix J J ℝ) + (φ * M.τ2) • Model.sameGroup grp) μ P :=
  (N.toNoise.toEstimates μ).addCommon N.common _ N.memLp_common N.integral_common
    (N.cov_common h0) (N.cov_common_cohortEst μ) (N.cov_common_trueMean μ)

omit [Fintype T] in
/-- The cohort estimates and levels with group levels and unequal lengths as an
instance of the Core moment layer: covariances `K_G` and `L_G`. -/
noncomputable def toEstimates (h0 : 0 ≤ φ) :
    Core.Estimates (M.KG grp φ) (Model.levelCovG grp M.τ2 φ) μ P where
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
    rw [N.cohortEst_eq, Model.levelCovG_eq_add_sameGroup]
    exact (N.addCommon μ h0).cov_level_est i j
  cov_level i j := by
    rw [Model.levelCovG_eq_add_sameGroup]
    exact (N.addCommon μ h0).cov_level i j

omit [Fintype J] [Fintype T] in
/-- `K_G` (unequal lengths) is the actual covariance of the cohort estimates. -/
theorem cov_cohortEst (h0 : 0 ≤ φ) (i j : J) :
    cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.KG grp φ i j :=
  (N.toEstimates μ h0).cov_est i j

omit [Fintype J] [Fintype T] in
/-- `L_G` is the actual covariance of the levels. -/
theorem cov_trueMean (h0 : 0 ≤ φ) (i j : J) :
    cov[N.trueMean μ i, N.trueMean μ j; P] = Model.levelCovG grp M.τ2 φ i j :=
  (N.toEstimates μ h0).cov_level i j

omit [Fintype T] in
/-- Every field of `M.momentsG grp φ j` is the actual moment it names. -/
theorem moments_eq (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.momentsG grp φ j).varCohort ∧
    Var[N.portEst μ; P] = (M.momentsG grp φ j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.momentsG grp φ j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.momentsG grp φ j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.momentsG grp φ j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.momentsG grp φ j).covPortfolioTarget := by
  rw [M.momentsG_eq_levelMoments']
  exact (N.toEstimates μ h0).levelMoments_eq hK j

omit [Fintype T] in
/-- With group levels and unequal lengths the blend is unbiased and its actual
mean squared error is `errVar`, eq. (6), for the moments `momentsG`. -/
theorem mse_blend (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.momentsG grp φ j).errVar z := by
  rw [M.momentsG_eq_levelMoments']
  exact (N.toEstimates μ h0).mse_blend hK j z

omit [Fintype T] in
/-- Eq. (26) with group levels and unequal lengths, in true MSE: `zⱼ`
(`Unequal.bestZ_G_eq`) minimises the actual mean squared error of the blend. -/
theorem bestZ_mse_optimal (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J)
    (hgap : 0 < (M.momentsG grp φ j).gap) (z : ℝ) :
    P[fun ω => (N.blend μ j (M.momentsG grp φ j).bestZ ω - N.trueMean μ j ω) ^ 2]
      ≤ P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] := by
  rw [N.mse_blend μ h0 hK j, N.mse_blend μ h0 hK j]
  exact (M.momentsG grp φ j).bestZ_optimal hgap z

end NoiseG

namespace Noise

variable {Ω' : Type*} [MeasurableSpace Ω'] {M : Unequal J T} {P : Measure Ω} {P' : Measure Ω'}

/-- The noise read through a map `Z : Ω' → Ω` with law `P` under `P'`: the same
moments. -/
noncomputable def comp (N : M.Noise P) {Z : Ω' → Ω} (hZ : HasLaw Z P P') : M.Noise P' where
  η j ω := N.η j (Z ω)
  ε j t ω := N.ε j t (Z ω)
  η_memLp j := hZ.memLp_comp (N.η_memLp j)
  ε_memLp j t ht := hZ.memLp_comp (N.ε_memLp j t ht)
  η_mean j := (hZ.integral_comp (f := N.η j) (N.η_memLp j).aestronglyMeasurable).trans
    (N.η_mean j)
  ε_mean j t ht := (hZ.integral_comp (f := N.ε j t)
    (N.ε_memLp j t ht).aestronglyMeasurable).trans (N.ε_mean j t ht)
  cov_η_η i j := by
    rw [hZ.covariance_fun_comp (N.η_memLp i).aemeasurable (N.η_memLp j).aemeasurable]
    exact N.cov_η_η i j
  cov_η_ε i j t ht := by
    rw [hZ.covariance_fun_comp (N.η_memLp i).aemeasurable (N.ε_memLp j t ht).aemeasurable]
    exact N.cov_η_ε i j t ht
  cov_ε_ε i j t ht s hs := by
    rw [hZ.covariance_fun_comp (N.ε_memLp i t ht).aemeasurable (N.ε_memLp j s hs).aemeasurable]
    exact N.cov_ε_ε i j t ht s hs

end Noise

/-- The group-level assumptions with unequal lengths are consistent exactly when
every block `ρ_t` (the correlations of the cohorts observed at `t`) is positive
semidefinite, as without groups (`Unequal.exists_noise_iff`): group effects add
no constraint. Witness: the noise of `exists_noise_iff` for level variance
`(1-φ)τ²` on one factor, independent standard normal `γ_g` on the other (a
witness only; the model stays distribution-free). -/
theorem exists_noiseG_iff {G : Type} [DecidableEq G] (M : Unequal J T)
    (grp : J → G) (φ : ℝ) (h1 : φ < 1) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.NoiseG grp φ h1 P)) ↔ ∀ t, (M.block t).PosSemidef := by
  constructor
  · -- Necessity: forget `γ`; the blocks of `M_φ` are those of `M`.
    rintro ⟨Ω, _, P, _, ⟨N⟩⟩
    exact (M.withLevel φ h1).exists_noise_iff.mp ⟨Ω, _, P, inferInstance, ⟨N.toNoise⟩⟩
  · -- Sufficiency: noise on `Ω₀`, independent `γ_g ~ N(0,1)` on `G → ℝ`.
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
    have hε : ∀ g j, ∀ t ∈ M.obs j,
        cov[fun p : Ω₀ × (G → ℝ) => p.2 g, fun p => N₀.ε j t p.1; P₀.prod Q] = 0 :=
      fun g j t ht => by
        rw [covariance_comm]
        exact covariance_fst_snd_prod (μ := P₀) (ν := Q) (X := N₀.ε j t)
          (Y := fun x : G → ℝ => x g) (N₀.ε_memLp j t ht) (hm g)
    let N := N₀.comp hfst
    exact ⟨Ω₀ × (G → ℝ), inferInstance, P₀.prod Q, inferInstance,
      ⟨{ toNoise := N
         γ := fun g p => p.2 g
         γ_memLp := hm'
         γ_mean := hmean
         cov_γ_γ := hcov
         cov_γ_η := hη
         cov_γ_ε := hε }⟩⟩

end Unequal

/-! ### The thesis model with group levels: the case `Tⱼ = T` -/

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

/-- A group-level noise for the thesis model is one for `Tⱼ = T`. -/
def toUnequal [Nonempty T] : M.toUnequal.NoiseG grp φ h1 P where
  toNoise := N.toNoise.toUnequal
  γ := N.γ
  γ_memLp := N.γ_memLp
  γ_mean := N.γ_mean
  cov_γ_γ := N.cov_γ_γ
  cov_γ_η := N.cov_γ_η
  cov_γ_ε := fun g j t _ => N.cov_γ_ε g j t

/-- …and conversely. -/
def ofUnequal [Nonempty T] (N : M.toUnequal.NoiseG grp φ h1 P) : M.NoiseG grp φ h1 P where
  toNoise := Noise.ofUnequal N.toNoise
  γ := N.γ
  γ_memLp := N.γ_memLp
  γ_mean := N.γ_mean
  cov_γ_γ := N.cov_γ_γ
  cov_γ_η := N.cov_γ_η
  cov_γ_ε := fun g j t => N.cov_γ_ε g j t (mem_univ t)

section Full

variable [Nonempty T]

omit [Fintype J] in
lemma toUnequal_trueMean (j : J) : N.toUnequal.trueMean μ j = N.trueMean μ j := rfl

omit [Fintype J] in
lemma toUnequal_obsVal (j : J) (t : T) : N.toUnequal.obsVal μ j t = N.obs μ j t := rfl

omit [Fintype J] in
lemma toUnequal_cohortEst (j : J) : N.toUnequal.cohortEst μ j = N.cohortEst μ j := by
  funext ω
  simp only [Unequal.NoiseG.cohortEst, cohortEst, toUnequal_a]
  rfl

lemma toUnequal_portEst : N.toUnequal.portEst μ = N.portEst μ := by
  rw [Unequal.NoiseG.portEst, ← KG_eq_toUnequal, funext (N.toUnequal_cohortEst μ)]

lemma toUnequal_blend (j : J) (z : ℝ) : N.toUnequal.blend μ j z = N.blend μ j z := by
  rw [Unequal.NoiseG.blend, ← KG_eq_toUnequal, funext (N.toUnequal_cohortEst μ)]

end Full

variable [IsProbabilityMeasure P]

omit [Fintype J] in
lemma memLp_obs (j : J) (t : T) : MemLp (N.obs μ j t) 2 P := by
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.memLp_obsVal μ j (mem_univ t)

omit [Fintype J] in
/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs μ j t] = μ := by
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.obsVal_mean μ j (mem_univ t)

omit [Fintype J] in
/-- Eq. (16) with group levels is the actual covariance:
`cov(μᵢₜ, μⱼₛ) = σᵢₜσⱼₛρᵢⱼδₜₛ + (L_G)ᵢⱼ`. -/
theorem cov_obs (h0 : 0 ≤ φ) (i j : J) (t s : T) :
    cov[N.obs μ i t, N.obs μ j s; P] = M.obsCovG grp φ i j t s := by
  have : Nonempty T := ⟨t⟩
  exact N.toUnequal.cov_obsVal μ h0 i j (mem_univ t) (mem_univ s)

/-- §2.8 in true expectation with group levels: for any quadratic form of the
data, `E[Σₚ,q Qₚq μₚ μq] = M.EG grp φ μ Q`. So `UnbiasedG f θ` means
`E f = θ` for any random variables with these moments. -/
theorem integral_quad (h0 : 0 ≤ φ) (Q : J × T → J × T → ℝ) :
    P[fun ω => quad Q (fun p => N.obs μ p.1 p.2 ω)] = M.EG grp φ μ Q := by
  -- `Unequal.NoiseG.integral_quad` with `Tⱼ = T`: every cell is observed.
  rcases isEmpty_or_nonempty T with hT | hT
  · simp [quad, EG, Ecov]
  exact N.toUnequal.integral_quad μ h0 Q fun p q _ => ⟨mem_univ _, mem_univ _⟩

omit [Fintype J] in
/-- `K_G` is the actual covariance of the cohort estimates: `cov(μ̂ᵢ, μ̂ⱼ) = (K_G)ᵢⱼ`. -/
theorem cov_cohortEst [Nonempty T] (h0 : 0 ≤ φ) (i j : J) :
    cov[N.cohortEst μ i, N.cohortEst μ j; P] = M.KG grp φ i j := by
  rw [← N.toUnequal_cohortEst, ← N.toUnequal_cohortEst, KG_eq_toUnequal]
  exact N.toUnequal.cov_cohortEst μ h0 i j

omit [Fintype J] in
/-- `L_G` is the actual covariance of the levels: `cov(μᵢ, μⱼ) = (L_G)ᵢⱼ`. -/
theorem cov_trueMean [Nonempty T] (h0 : 0 ≤ φ) (i j : J) :
    cov[N.trueMean μ i, N.trueMean μ j; P] = levelCovG grp M.τ2 φ i j :=
  N.toUnequal.cov_trueMean μ h0 i j

/-- Every field of `M.momentsG grp φ j` is the actual moment it names. -/
theorem moments_eq [Nonempty T] (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) :
    Var[N.cohortEst μ j; P] = (M.momentsG grp φ j).varCohort ∧
    Var[N.portEst μ; P] = (M.momentsG grp φ j).varPortfolio ∧
    Var[N.trueMean μ j; P] = (M.momentsG grp φ j).varTarget ∧
    cov[N.cohortEst μ j, N.portEst μ; P] = (M.momentsG grp φ j).covEst ∧
    cov[N.cohortEst μ j, N.trueMean μ j; P] = (M.momentsG grp φ j).covCohortTarget ∧
    cov[N.portEst μ, N.trueMean μ j; P] = (M.momentsG grp φ j).covPortfolioTarget := by
  rw [KG_eq_toUnequal] at hK
  rw [← N.toUnequal_cohortEst, ← N.toUnequal_portEst, momentsG_eq_toUnequal]
  exact N.toUnequal.moments_eq μ h0 hK j

/-- With group levels the blend is unbiased and its actual mean squared error
is `errVar`, eq. (6), for the moments `momentsG`. -/
theorem mse_blend [Nonempty T] (h0 : 0 ≤ φ) (hK : (M.KG grp φ).PosDef) (j : J) (z : ℝ) :
    P[fun ω => (N.blend μ j z ω - N.trueMean μ j ω) ^ 2] = (M.momentsG grp φ j).errVar z := by
  rw [KG_eq_toUnequal] at hK
  rw [← N.toUnequal_blend, momentsG_eq_toUnequal]
  exact N.toUnequal.mse_blend μ h0 hK j z

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

/-- The group-level assumptions are consistent exactly when `ρ` is positive
semidefinite, as for the thesis model (`exists_noise_iff`): group effects add
no constraint. The case `Tⱼ = T` of `Unequal.exists_noiseG_iff`, whose blocks
are then all of `ρ`. Groups are labels in `Type`, like `Ω`. -/
theorem exists_noiseG_iff {G : Type} [DecidableEq G] [Nonempty T] (M : Model J T)
    (grp : J → G) (φ : ℝ) (h1 : φ < 1) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.NoiseG grp φ h1 P)) ↔ (Matrix.of M.ρ).PosSemidef := by
  have hN : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω),
      Nonempty (M.NoiseG grp φ h1 P) ↔ Nonempty (M.toUnequal.NoiseG grp φ h1 P) :=
    fun _ => ⟨fun ⟨N⟩ => ⟨N.toUnequal⟩, fun ⟨N⟩ => ⟨NoiseG.ofUnequal N⟩⟩
  have hB : (∀ t, (M.toUnequal.block t).PosSemidef) ↔ (Matrix.of M.ρ).PosSemidef := by
    refine ⟨fun h => ?_, fun hρ t => hρ.submatrix _⟩
    obtain ⟨t⟩ := ‹Nonempty T›
    convert (h t).submatrix (fun j => (⟨j, mem_univ t⟩ : {j // t ∈ M.toUnequal.obs j}))
    ext i j; rfl
  simp only [hN]
  rw [Unequal.exists_noiseG_iff, hB]

end Model

end Credibility
