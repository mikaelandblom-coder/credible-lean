import Credibility.Core

/-!
# The moment layer at the level of `K` and `L` (extension, distribution-free)

`Core.lean` takes the covariance `K` of the cohort estimates and the covariance
`L` of the cohort levels as given matrices. Here they become actual
covariances: **any** square-integrable random variables `μ̂ⱼ` (`est`) and `μⱼ`
(`level`) with common mean `μ`, `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ` and
`cov(μᵢ, μ̂ⱼ) = cov(μᵢ, μⱼ) = Lᵢⱼ` (`Core.Estimates`). Then the six fields of
`Core.levelMoments` are the moments they name, the mean squared error of the
blend is `errVar`, and `bestZ` minimises it. No distribution is assumed, and
nothing about how the `μ̂ⱼ` are built from data.

The models supply only the two covariance statements: `Unequal.Noise`
(`L = τ²I`; `Model.Noise` is its case `Tⱼ = T`) and the group levels of
`HierarchicalMoments.lean` (`L = L_G`). A component common to estimates and
levels adds its covariance to both `K` and `L` (`Estimates.addCommon`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `cov(X + Y, Z + W)` expanded bilinearly. -/
lemma cov_add_add {P : Measure Ω} [IsProbabilityMeasure P] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) (hW : MemLp W 2 P) :
    cov[fun ω => X ω + Y ω, fun ω => Z ω + W ω; P]
      = cov[X, Z; P] + cov[X, W; P] + cov[Y, Z; P] + cov[Y, W; P] := by
  rw [show (fun ω => X ω + Y ω) = X + Y from rfl, show (fun ω => Z ω + W ω) = Z + W from rfl,
    covariance_add_left hX hY (hZ.add hW), covariance_add_right hX hZ hW,
    covariance_add_right hY hZ hW]
  ring

/-- Eq. (6) in true mean squared error: if `X`, `Y`, `Z` (cohort estimate,
portfolio estimate, target) have a common mean and the six second moments `m`,
then `E[(z X + (1 - z) Y - Z)²] = m.errVar z`. The blend is unbiased, so its
mean squared error is a variance, and that is bilinear. -/
theorem BlendMoments.integral_sq_blend_sub {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BlendMoments) {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    {μ : ℝ} (hXm : P[X] = μ) (hYm : P[Y] = μ) (hZm : P[Z] = μ)
    (h1 : Var[X; P] = m.varCohort) (h2 : Var[Y; P] = m.varPortfolio)
    (h3 : Var[Z; P] = m.varTarget) (h4 : cov[X, Y; P] = m.covEst)
    (h5 : cov[X, Z; P] = m.covCohortTarget) (h6 : cov[Y, Z; P] = m.covPortfolioTarget) (z : ℝ) :
    P[fun ω => (z * X ω + (1 - z) * Y ω - Z ω) ^ 2] = m.errVar z := by
  -- The error is a linear combination of `X`, `Y` and `Z`.
  set U : Fin 3 → Ω → ℝ := ![X, Y, Z] with hUdef
  set w : Fin 3 → ℝ := ![z, 1 - z, -1]
  have hD : (fun ω => z * X ω + (1 - z) * Y ω - Z ω) = fun ω => ∑ i, w i * U i ω := by
    funext ω; simp [Fin.sum_univ_three, w, U]; ring
  have hU : ∀ i, MemLp (U i) 2 P := fun i => by
    fin_cases i
    · exact hX
    · exact hY
    · exact hZ
  have hint : ∀ i, Integrable (fun ω => w i * U i ω) P :=
    fun i => ((hU i).const_mul (w i)).integrable (by norm_num)
  have hDm : MemLp (fun ω => ∑ i, w i * U i ω) 2 P :=
    memLp_finsetSum _ fun i _ => (hU i).const_mul (w i)
  -- It is unbiased.
  have hmean : P[fun ω => ∑ i, w i * U i ω] = 0 := by
    rw [integral_finsetSum _ fun i _ => hint i]
    simp only [integral_const_mul, Fin.sum_univ_three, w, U]
    simp [hXm, hYm, hZm]
    ring
  -- So the mean squared error is the variance; expand it bilinearly.
  have hsq : (fun ω => (z * X ω + (1 - z) * Y ω - Z ω) ^ 2)
      = fun ω => (fun ω => ∑ i, w i * U i ω) ω ^ 2 := by
    funext ω; exact congrArg (· ^ 2) (congrFun hD ω)
  rw [hsq, ← variance_of_integral_eq_zero hDm.aestronglyMeasurable.aemeasurable hmean,
    ← covariance_self hDm.aestronglyMeasurable.aemeasurable,
    covariance_fun_sum_fun_sum (fun i => (hU i).const_mul (w i))
      (fun i => (hU i).const_mul (w i))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, Fin.sum_univ_three]
  have hself : ∀ i, cov[U i, U i; P] = Var[U i; P] := fun i =>
    covariance_self (hU i).aestronglyMeasurable.aemeasurable
  simp only [hself]
  simp only [w, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [covariance_comm Y X, covariance_comm Z X, covariance_comm Z Y, h1, h2, h3, h4, h5, h6]
  simp only [BlendMoments.errVar]
  ring

namespace Core

variable {J : Type*}

/-- A linear portfolio estimate `Σⱼ dⱼ μ̂ⱼ` of cohort estimates `est`, with
arbitrary weights `d`. -/
noncomputable def portLin [Fintype J] (est : J → Ω → ℝ) (d : J → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, d j * est j ω

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights of `K`. -/
noncomputable def portEst [Fintype J] [DecidableEq J] (K : Matrix J J ℝ) (est : J → Ω → ℝ) :
    Ω → ℝ :=
  portLin est (glsWeight K)

/-- The blend `z μ̂ⱼ + (1 - z) μ̂` with the GLS portfolio estimate of `K`. -/
noncomputable def blend [Fintype J] [DecidableEq J] (K : Matrix J J ℝ) (est : J → Ω → ℝ)
    (j : J) (z : ℝ) : Ω → ℝ :=
  fun ω => z * est j ω + (1 - z) * portEst K est ω

/-- Cohort estimates `μ̂ⱼ` (`est`) and cohort levels `μⱼ` (`level`) under `P`:
square integrable, with common mean `μ`, `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ` and
`cov(μᵢ, μ̂ⱼ) = cov(μᵢ, μⱼ) = Lᵢⱼ` (an estimate differs from its level by noise
uncorrelated with all levels). Only moments are assumed, no distribution. -/
structure Estimates (K L : Matrix J J ℝ) (μ : ℝ) (P : Measure Ω) where
  /-- The cohort estimate `μ̂ⱼ`. -/
  est : J → Ω → ℝ
  /-- The cohort level `μⱼ`. -/
  level : J → Ω → ℝ
  est_memLp : ∀ j, MemLp (est j) 2 P
  level_memLp : ∀ j, MemLp (level j) 2 P
  est_mean : ∀ j, P[est j] = μ
  level_mean : ∀ j, P[level j] = μ
  cov_est : ∀ i j, cov[est i, est j; P] = K i j
  cov_level_est : ∀ i j, cov[level i, est j; P] = L i j
  cov_level : ∀ i j, cov[level i, level j; P] = L i j

namespace Estimates

variable [Fintype J] {K L : Matrix J J ℝ} {μ : ℝ} {P : Measure Ω} (E : Estimates K L μ P)

/-- A linear portfolio estimate `Σⱼ dⱼ μ̂ⱼ` with arbitrary weights `d`. -/
noncomputable abbrev portLin (d : J → ℝ) : Ω → ℝ := Core.portLin E.est d

/-- The portfolio estimate `μ̂ = Σⱼ bⱼ μ̂ⱼ` with the GLS weights of `K`. -/
noncomputable abbrev portEst [DecidableEq J] : Ω → ℝ := Core.portEst K E.est

/-- The blend `z μ̂ⱼ + (1 - z) μ̂`. -/
noncomputable abbrev blend [DecidableEq J] (j : J) (z : ℝ) : Ω → ℝ := Core.blend K E.est j z

lemma memLp_portLin (d : J → ℝ) : MemLp (E.portLin d) 2 P :=
  memLp_finsetSum _ fun j _ => (E.est_memLp j).const_mul (d j)

variable [IsProbabilityMeasure P]

/-- `E Σⱼ dⱼ μ̂ⱼ = (Σⱼ dⱼ) μ`. -/
lemma integral_portLin (d : J → ℝ) : P[E.portLin d] = (∑ j, d j) * μ := by
  unfold portLin Core.portLin
  rw [integral_finsetSum _ fun j _ => ((E.est_memLp j).const_mul (d j)).integrable
    (by norm_num)]
  simp [integral_const_mul, E.est_mean, sum_mul]

/-- `cov(Σᵢ dᵢ μ̂ᵢ, Σⱼ d'ⱼ μ̂ⱼ) = dᵀK d'`. -/
lemma cov_portLin (d d' : J → ℝ) :
    cov[E.portLin d, E.portLin d'; P] = d ⬝ᵥ (K *ᵥ d') := by
  unfold portLin Core.portLin
  rw [covariance_fun_sum_fun_sum (fun i => (E.est_memLp i).const_mul (d i))
    (fun j => (E.est_memLp j).const_mul (d' j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, E.cov_est,
    dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- `Var(Σⱼ dⱼ μ̂ⱼ) = dᵀK d`. -/
lemma variance_portLin (d : J → ℝ) : Var[E.portLin d; P] = d ⬝ᵥ (K *ᵥ d) := by
  rw [← covariance_self (E.memLp_portLin d).aestronglyMeasurable.aemeasurable, cov_portLin]

/-- `cov(μ̂ᵢ, Σⱼ dⱼ μ̂ⱼ) = (K d)ᵢ`. -/
lemma cov_est_portLin (i : J) (d : J → ℝ) :
    cov[E.est i, E.portLin d; P] = (K *ᵥ d) i := by
  unfold portLin Core.portLin
  rw [covariance_fun_sum_right (fun j => (E.est_memLp j).const_mul (d j)) (E.est_memLp i)]
  simp only [covariance_const_mul_right, E.cov_est, mulVec, dotProduct]
  exact sum_congr rfl fun j _ => by ring

/-- `cov(μᵢ, Σⱼ dⱼ μ̂ⱼ) = (L d)ᵢ`. -/
lemma cov_level_portLin (i : J) (d : J → ℝ) :
    cov[E.level i, E.portLin d; P] = (L *ᵥ d) i := by
  unfold portLin Core.portLin
  rw [covariance_fun_sum_right (fun j => (E.est_memLp j).const_mul (d j)) (E.level_memLp i)]
  simp only [covariance_const_mul_right, E.cov_level_est, mulVec, dotProduct]
  exact sum_congr rfl fun j _ => by ring

variable [DecidableEq J]

/-- Eq. (24) in true variance: among unbiased linear portfolio estimates built
from the `μ̂ⱼ`, the GLS one has the smallest variance, and it equals `s²`. -/
theorem portEst_optimal (hK : K.PosDef) (d : J → ℝ) (hd : ∑ j, d j = 1) :
    Var[E.portEst; P] = (invTotal K)⁻¹ ∧ (invTotal K)⁻¹ ≤ Var[E.portLin d; P] := by
  obtain ⟨j, -, -⟩ := exists_ne_zero_of_sum_ne_zero (hd.trans_ne one_ne_zero)
  have : Nonempty J := ⟨j⟩
  have hs2 : glsWeight K ⬝ᵥ (K *ᵥ glsWeight K) = (invTotal K)⁻¹ := glsWeight_value hK
  refine ⟨by rw [portEst, Core.portEst, variance_portLin, hs2], ?_⟩
  rw [variance_portLin, ← hs2]
  exact glsWeight_optimal hK d hd

/-- Every field of `levelMoments K L Kⱼⱼ j` is the actual moment it names (§2.4). -/
theorem levelMoments_eq (hK : K.PosDef) (j : J) :
    Var[E.est j; P] = (levelMoments K L (K j j) j).varCohort ∧
    Var[E.portEst; P] = (levelMoments K L (K j j) j).varPortfolio ∧
    Var[E.level j; P] = (levelMoments K L (K j j) j).varTarget ∧
    cov[E.est j, E.portEst; P] = (levelMoments K L (K j j) j).covEst ∧
    cov[E.est j, E.level j; P] = (levelMoments K L (K j j) j).covCohortTarget ∧
    cov[E.portEst, E.level j; P] = (levelMoments K L (K j j) j).covPortfolioTarget := by
  have : Nonempty J := ⟨j⟩
  have hvar : ∀ X, MemLp X 2 P → Var[X; P] = cov[X, X; P] := fun X hX =>
    (covariance_self hX.aestronglyMeasurable.aemeasurable).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvar _ (E.est_memLp j), E.cov_est]; rfl
  · rw [portEst, Core.portEst, variance_portLin]; exact glsWeight_value hK
  · rw [hvar _ (E.level_memLp j), E.cov_level]; rfl
  · exact E.cov_est_portLin j _
  · rw [covariance_comm, E.cov_level_est]; rfl
  · rw [covariance_comm]; exact E.cov_level_portLin j _

/-- The blend is unbiased and its actual mean squared error is `errVar`,
eq. (6), for the moments of `levelMoments`. -/
theorem mse_blend (hK : K.PosDef) (j : J) (z : ℝ) :
    P[fun ω => (E.blend j z ω - E.level j ω) ^ 2] = (levelMoments K L (K j j) j).errVar z := by
  have : Nonempty J := ⟨j⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := E.levelMoments_eq hK j
  have hP : P[E.portEst] = μ := by
    rw [portEst, Core.portEst, integral_portLin, sum_glsWeight hK, one_mul]
  exact BlendMoments.integral_sq_blend_sub _ (E.est_memLp j) (E.memLp_portLin _)
    (E.level_memLp j) (E.est_mean j) hP (E.level_mean j) h1 h2 h3 h4 h5 h6 z

/-- Eq. (26) for a level covariance `L`, in true MSE: `zⱼ`
(`levelMoments_bestZ_eq`) minimises the actual mean squared error of the
blend, for every distribution with these moments. -/
theorem bestZ_mse_optimal (hK : K.PosDef) (j : J)
    (hgap : 0 < (levelMoments K L (K j j) j).gap) (z : ℝ) :
    P[fun ω => (E.blend j (levelMoments K L (K j j) j).bestZ ω - E.level j ω) ^ 2]
      ≤ P[fun ω => (E.blend j z ω - E.level j ω) ^ 2] := by
  rw [E.mse_blend hK j, E.mse_blend hK j]
  exact (levelMoments K L (K j j) j).bestZ_optimal hgap z

/-- **Forecasting** (PLAN G6): next year's outcome is `Yⱼ = μⱼ + εⱼ`, with noise `εⱼ` of
mean `0` uncorrelated with all cohort estimates and with the level `μⱼ`. The mean
squared error of the blend for `Yⱼ` is its error for the level plus next year's
noise variance. -/
theorem mse_forecast (hK : K.PosDef) (j : J) {ε : Ω → ℝ} (hε : MemLp ε 2 P)
    (hε0 : P[ε] = 0) (hεest : ∀ i, cov[E.est i, ε; P] = 0) (hεlev : cov[E.level j, ε; P] = 0)
    (z : ℝ) :
    P[fun ω => (E.blend j z ω - (E.level j ω + ε ω)) ^ 2]
      = (levelMoments K L (K j j) j).errVar z + Var[ε; P] := by
  have : Nonempty J := ⟨j⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := E.levelMoments_eq hK j
  set m := levelMoments K L (K j j) j
  -- The target `Yⱼ` has the moments of `μⱼ`, with `Var(εⱼ)` added to its variance.
  let m' : BlendMoments := { m with varTarget := m.varTarget + Var[ε; P] }
  have hP : P[E.portEst] = μ := by
    rw [portEst, Core.portEst, integral_portLin, sum_glsWeight hK, one_mul]
  have hl := E.level_memLp j
  have hY : MemLp (fun ω => E.level j ω + ε ω) 2 P := hl.add hε
  have hYm : P[fun ω => E.level j ω + ε ω] = μ := by
    rw [integral_add (hl.integrable (by norm_num)) (hε.integrable (by norm_num)),
      E.level_mean, hε0, add_zero]
  have hvar : ∀ X, MemLp X 2 P → Var[X; P] = cov[X, X; P] := fun X hX =>
    (covariance_self hX.aestronglyMeasurable.aemeasurable).symm
  have hpm : MemLp E.portEst 2 P := E.memLp_portLin _
  have hpε : cov[E.portEst, ε; P] = 0 := by
    unfold portEst Core.portEst Core.portLin
    rw [covariance_fun_sum_left (fun i => (E.est_memLp i).const_mul _) hε]
    simp [covariance_const_mul_left, hεest]
  have hY3 : Var[fun ω => E.level j ω + ε ω; P] = m'.varTarget := by
    rw [hvar _ hY, cov_add_add hl hε hl hε, covariance_comm ε, hεlev, ← hvar _ hl,
      ← hvar _ hε, h3]
    simp [m']
  have hY5 : cov[E.est j, fun ω => E.level j ω + ε ω; P] = m'.covCohortTarget := by
    rw [show (fun ω => E.level j ω + ε ω) = E.level j + ε from rfl,
      covariance_add_right (E.est_memLp j) hl hε, hεest, h5, add_zero]
  have hY6 : cov[E.portEst, fun ω => E.level j ω + ε ω; P] = m'.covPortfolioTarget := by
    rw [show (fun ω => E.level j ω + ε ω) = E.level j + ε from rfl,
      covariance_add_right hpm hl hε, hpε, h6, add_zero]
  rw [show (levelMoments K L (K j j) j).errVar z + Var[ε; P] = m'.errVar z by
    simp only [m', BlendMoments.errVar]; ring]
  exact BlendMoments.integral_sq_blend_sub m' (E.est_memLp j) hpm hY
    (E.est_mean j) hP hYm h1 h2 hY3 h4 hY5 hY6 z

/-- **The same `z` is best for next year** (PLAN G6): under the assumptions of
`mse_forecast`, `zⱼ` of eq. (26) also minimises the actual mean squared error of the
blend as a forecast of next year's outcome `μⱼ + εⱼ`. -/
theorem bestZ_forecast_optimal (hK : K.PosDef) (j : J)
    (hgap : 0 < (levelMoments K L (K j j) j).gap) {ε : Ω → ℝ} (hε : MemLp ε 2 P)
    (hε0 : P[ε] = 0) (hεest : ∀ i, cov[E.est i, ε; P] = 0) (hεlev : cov[E.level j, ε; P] = 0)
    (z : ℝ) :
    P[fun ω => (E.blend j (levelMoments K L (K j j) j).bestZ ω - (E.level j ω + ε ω)) ^ 2]
      ≤ P[fun ω => (E.blend j z ω - (E.level j ω + ε ω)) ^ 2] := by
  rw [E.mse_forecast hK j hε hε0 hεest hεlev, E.mse_forecast hK j hε hε0 hεest hεlev]
  linarith [(levelMoments K L (K j j) j).bestZ_optimal hgap z]

/-- **The best balanced blend in true MSE** (PLAN G7): among the blends with the GLS
portfolio estimate that are balanced for the weights `uⱼ ≠ 0`, the factors
`zⱼ = 1 - c*·bⱼ/uⱼ` (`Core.bestBalanced_optimal`) minimise the weighted actual mean
squared error `Σⱼ φⱼ E[(μ̂ⱼᵇ - μⱼ)²]`, for every distribution with these moments. -/
theorem bestBalanced_mse_optimal (hK : K.PosDef) (φ u : J → ℝ) (hu : ∀ j, u j ≠ 0)
    (hφ : ∀ j, 0 ≤ φ j) (hgap : ∀ j, 0 < (levelMoments K L (K j j) j).gap)
    (z : J → ℝ) (hz : Balanced u z (glsWeight K)) :
    ∑ j, φ j * P[fun ω => (E.blend j (balancedZ u (glsWeight K)
        (bestBalancedC φ u (glsWeight K) fun j => levelMoments K L (K j j) j) j) ω
          - E.level j ω) ^ 2]
      ≤ ∑ j, φ j * P[fun ω => (E.blend j (z j) ω - E.level j ω) ^ 2] := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp
  simp only [E.mse_blend hK]
  exact (bestBalanced_optimal φ u _ _ (sum_glsWeight hK) hu hφ hgap).2 z hz

/-! ### The best balanced correction in true MSE (PLAN G7b) -/

/-- The imbalance `D = Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ)` of the blends with factors `z`, as the linear
combination `Σᵢ wᵢμ̂ᵢ` (`imbalance_eq`). -/
noncomputable abbrev imbalance (u z : J → ℝ) : Ω → ℝ :=
  E.portLin (imbalanceWeight u z (glsWeight K))

/-- The corrected estimate `θ̂ⱼ = μ̂ⱼᵇ + cD`. -/
noncomputable abbrev correct (u z : J → ℝ) (j : J) (c : ℝ) : Ω → ℝ :=
  fun ω => E.blend j (z j) ω + c * E.imbalance u z ω

omit [IsProbabilityMeasure P] in
/-- `D = Σⱼ uⱼ(μ̂ⱼ - μ̂ⱼᵇ)`. -/
theorem imbalance_eq (u z : J → ℝ) (ω : Ω) :
    E.imbalance u z ω = ∑ j, u j * (E.est j ω - E.blend j (z j) ω) := by
  simp only [imbalance, portLin, Core.portLin, blend, Core.blend]
  exact (sum_mul_sub_blend_eq u z _ fun j => E.est j ω).symm

omit [IsProbabilityMeasure P] in
/-- The corrections with `Σⱼ uⱼcⱼ = 1` are balanced: `Σⱼ uⱼ(μ̂ⱼ - θ̂ⱼ) = 0` for every outcome. -/
theorem balanced_correct (u z c : J → ℝ) (hc : ∑ j, u j * c j = 1) (ω : Ω) :
    ∑ j, u j * (E.est j ω - E.correct u z j (c j) ω) = 0 := by
  have h := E.imbalance_eq u z ω
  calc ∑ j, u j * (E.est j ω - E.correct u z j (c j) ω)
      = ∑ j, u j * (E.est j ω - E.blend j (z j) ω) - (∑ j, u j * c j) * E.imbalance u z ω := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by simp only [correct]; ring
    _ = 0 := by rw [hc, ← h]; ring

/-- The actual mean squared error of `θ̂ⱼ = μ̂ⱼᵇ + cD` is the parabola
`MSEⱼ(zⱼ) + 2cκⱼ + c²V` with `κⱼ = imbalanceCov` and `V = Var D = wᵀKw`. -/
theorem mse_correct (hK : K.PosDef) (u z : J → ℝ) (j : J) (c : ℝ) :
    P[fun ω => (E.correct u z j c ω - E.level j ω) ^ 2]
      = (levelMoments K L (K j j) j).errVar (z j)
        + 2 * c * imbalanceCov K L z (imbalanceWeight u z (glsWeight K)) j
        + c ^ 2 * (imbalanceWeight u z (glsWeight K) ⬝ᵥ
            (K *ᵥ imbalanceWeight u z (glsWeight K))) := by
  have : Nonempty J := ⟨j⟩
  set w := imbalanceWeight u z (glsWeight K)
  set X : Ω → ℝ := fun ω => E.blend j (z j) ω - E.level j ω
  set D := E.imbalance u z
  have hb : MemLp (Core.portEst K E.est) 2 P := E.memLp_portLin (glsWeight K)
  have hD : MemLp D 2 P := E.memLp_portLin w
  have h1 : MemLp (fun ω => z j * E.est j ω) 2 P := (E.est_memLp j).const_mul (z j)
  have h2 : MemLp (fun ω => (1 - z j) * Core.portEst K E.est ω) 2 P := hb.const_mul (1 - z j)
  have hBl : MemLp (fun ω => z j * E.est j ω + (1 - z j) * Core.portEst K E.est ω) 2 P :=
    h1.add h2
  have hX : MemLp X 2 P := hBl.sub (E.level_memLp j)
  have hP : P[Core.portEst K E.est] = μ := by
    rw [Core.portEst, show Core.portLin E.est (glsWeight K) = E.portLin (glsWeight K) from rfl,
      integral_portLin, sum_glsWeight hK, one_mul]
  have hXm : P[X] = 0 := by
    simp only [X, blend, Core.blend]
    rw [integral_sub (hBl.integrable (by norm_num)) ((E.level_memLp j).integrable (by norm_num)),
      integral_add (h1.integrable (by norm_num)) (h2.integrable (by norm_num)),
      integral_const_mul, integral_const_mul, E.est_mean, E.level_mean, hP]
    ring
  have hDm : P[D] = 0 := by
    rw [integral_portLin, sum_imbalanceWeight _ _ _ (sum_glsWeight hK), zero_mul]
  have hcD : MemLp (fun ω => c * D ω) 2 P := hD.const_mul c
  have hsum : MemLp (fun ω => X ω + c * D ω) 2 P := hX.add hcD
  have hsumm : P[fun ω => X ω + c * D ω] = 0 := by
    rw [integral_add (hX.integrable (by norm_num)) (hcD.integrable (by norm_num)),
      integral_const_mul, hXm, hDm]
    ring
  -- `E[(X + cD)²] = Var X + 2c cov(X, D) + c² Var D`.
  have hsq : (fun ω => (E.correct u z j c ω - E.level j ω) ^ 2)
      = fun ω => (fun ω => X ω + c * D ω) ω ^ 2 := by
    funext ω; simp only [correct, X, D]; ring
  rw [hsq, ← variance_of_integral_eq_zero hsum.aestronglyMeasurable.aemeasurable hsumm,
    variance_fun_add hX hcD, covariance_const_mul_right, variance_const_mul]
  -- `Var X` is the blend's MSE.
  have hVX : Var[X; P] = (levelMoments K L (K j j) j).errVar (z j) := by
    rw [variance_of_integral_eq_zero hX.aestronglyMeasurable.aemeasurable hXm]
    exact E.mse_blend hK j (z j)
  -- `cov(X, D) = zⱼ(Kw)ⱼ + (1 - zⱼ)cov(μ̂, D) - (Lw)ⱼ`, and `cov(μ̂, D) = s²Σw = 0`.
  have hbD : cov[Core.portEst K E.est, D; P] = 0 := by
    rw [Core.portEst, show Core.portLin E.est (glsWeight K) = E.portLin (glsWeight K)
      from rfl, covariance_comm, cov_portLin, mulVec_glsWeight hK]
    simp only [dotProduct, ← sum_mul, sum_imbalanceWeight _ _ _ (sum_glsWeight hK), zero_mul]
  have hXD : cov[X, D; P] = imbalanceCov K L z w j := by
    simp only [X, blend, Core.blend]
    rw [covariance_fun_sub_left hBl (E.level_memLp j) hD, ← Pi.add_def, covariance_add_left h1 h2 hD,
      covariance_const_mul_left, covariance_const_mul_left, hbD,
      E.cov_est_portLin, E.cov_level_portLin, imbalanceCov]
    ring
  rw [hVX, hXD, variance_portLin]
  ring

/-- **The best balanced correction in true MSE** (PLAN G7b, Wang–Fuller–Qu): among the
balanced corrections `μ̂ⱼᵇ + cⱼD` (`Σⱼ uⱼcⱼ = 1`), the factors `c* = bestCorrectionC`
minimise the weighted actual mean squared error `Σⱼ φⱼ E[(θ̂ⱼ - μⱼ)²]` (`φⱼ > 0`,
`Var D > 0`), for every distribution with these moments. -/
theorem bestCorrection_mse_optimal (hK : K.PosDef) (φ u z : J → ℝ) (hφ : ∀ j, 0 < φ j)
    (hV : 0 < imbalanceWeight u z (glsWeight K) ⬝ᵥ (K *ᵥ imbalanceWeight u z (glsWeight K)))
    (c : J → ℝ) (hc : ∑ j, u j * c j = 1) :
    ∑ j, φ j * P[fun ω => (E.correct u z j (bestCorrectionC φ u
        (imbalanceCov K L z (imbalanceWeight u z (glsWeight K)))
        (imbalanceWeight u z (glsWeight K) ⬝ᵥ (K *ᵥ imbalanceWeight u z (glsWeight K))) j) ω
          - E.level j ω) ^ 2]
      ≤ ∑ j, φ j * P[fun ω => (E.correct u z j (c j) ω - E.level j ω) ^ 2] := by
  obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero (hc.trans_ne one_ne_zero)
  simp only [E.mse_correct hK]
  exact (bestCorrection_optimal φ u _ _ _ hφ hV ⟨j, left_ne_zero_of_mul hj⟩).2 c hc

/-- **The common shift is the best balanced correction in true MSE** (PLAN G7b): for loss
weights equal to the balance weights (`φ = u > 0`), if `κⱼ = cov(μ̂ⱼᵇ - μⱼ, D)` is the same
for every cohort, then shifting every blend by `D/Σᵢuᵢ` minimises `Σⱼ uⱼ E[(θ̂ⱼ - μⱼ)²]`
among all balanced corrections `μ̂ⱼᵇ + cⱼD`, for every distribution with these moments. -/
theorem commonShift_mse_optimal (hK : K.PosDef) (u z : J → ℝ) (hu : ∀ j, 0 < u j)
    (hV : 0 < imbalanceWeight u z (glsWeight K) ⬝ᵥ (K *ᵥ imbalanceWeight u z (glsWeight K)))
    (k : ℝ) (hκ : ∀ j, imbalanceCov K L z (imbalanceWeight u z (glsWeight K)) j = k)
    (c : J → ℝ) (hc : ∑ j, u j * c j = 1) :
    ∑ j, u j * P[fun ω => (E.correct u z j (∑ i, u i)⁻¹ ω - E.level j ω) ^ 2]
      ≤ ∑ j, u j * P[fun ω => (E.correct u z j (c j) ω - E.level j ω) ^ 2] := by
  obtain ⟨j, -, -⟩ := exists_ne_zero_of_sum_ne_zero (hc.trans_ne one_ne_zero)
  have : Nonempty J := ⟨j⟩
  simp only [E.mse_correct hK]
  exact commonShift_optimal u _ _ _ k hu hV hκ c hc

/-- **Independent cohorts: the common shift is the best balanced correction** (Wang–Fuller–Qu):
for `K = diag(τ² + vⱼ)`, `L = τ²I`, `J ≥ 2` and the optimal factors `zⱼ*`, every `κⱼ = 0`, so
for any exposures `u > 0` shifting all blends by `D/Σᵢuᵢ` minimises `Σⱼ uⱼ E[(θ̂ⱼ - μⱼ)²]`
among the balanced corrections `μ̂ⱼᵇ + cⱼD`. -/
theorem commonShift_mse_optimal_of_diag {τ2 : ℝ} {v : J → ℝ} (E : Estimates K (τ2 • 1) μ P)
    (hK : K = diagonal fun j => τ2 + v j) (hd : ∀ j, 0 < τ2 + v j) (hJ : 1 < Fintype.card J)
    (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (hV : 0 < imbalanceWeight u (fun j => (moments K τ2 v j).bestZ) (glsWeight K) ⬝ᵥ
      (K *ᵥ imbalanceWeight u (fun j => (moments K τ2 v j).bestZ) (glsWeight K)))
    (c : J → ℝ) (hc : ∑ j, u j * c j = 1) :
    ∑ j, u j * P[fun ω => (E.correct u (fun j => (moments K τ2 v j).bestZ) j (∑ i, u i)⁻¹ ω
        - E.level j ω) ^ 2]
      ≤ ∑ j, u j * P[fun ω => (E.correct u (fun j => (moments K τ2 v j).bestZ) j (c j) ω
        - E.level j ω) ^ 2] :=
  E.commonShift_mse_optimal (by rw [hK, posDef_diagonal_iff]; exact hd) u _ hu hV 0
    (imbalanceCov_of_diag hK hd hJ _) c hc

/-! ### The best linear unbiased predictor in true MSE (Finding 18) -/

omit [DecidableEq J] in
/-- The actual mean squared error of an unbiased linear predictor `Σᵢ dᵢ μ̂ᵢ`
(`Σᵢ dᵢ = 1`) of `μⱼ` is `linMse`: `dᵀKd - 2 dᵀLⱼ + Lⱼⱼ`. -/
theorem mse_portLin (j : J) (d : J → ℝ) (hd : ∑ i, d i = 1) :
    P[fun ω => (E.portLin d ω - E.level j ω) ^ 2] = linMse K L j d := by
  have hp := E.memLp_portLin d
  have hl := E.level_memLp j
  have hX : MemLp (fun ω => E.portLin d ω - E.level j ω) 2 P := hp.sub hl
  have hXm : P[fun ω => E.portLin d ω - E.level j ω] = 0 := by
    rw [integral_sub (hp.integrable (by norm_num)) (hl.integrable (by norm_num)),
      integral_portLin, hd, E.level_mean]
    ring
  have hvar : ∀ X, MemLp X 2 P → Var[X; P] = cov[X, X; P] := fun X hX =>
    (covariance_self hX.aestronglyMeasurable.aemeasurable).symm
  rw [← variance_of_integral_eq_zero hX.aestronglyMeasurable.aemeasurable hXm,
    variance_fun_sub hp hl, variance_portLin, hvar _ hl, E.cov_level, covariance_comm,
    cov_level_portLin, linMse]
  simp only [mulVec, dotProduct_comm]

omit [IsProbabilityMeasure P] in
/-- The blend is the linear predictor with weights `z eⱼ + (1 - z) b`. -/
theorem blend_eq_portLin (j : J) (z : ℝ) : E.blend j z = E.portLin (blendWeight K j z) := by
  funext ω
  simp only [blend, Core.blend, Core.portEst, portLin, Core.portLin, blendWeight, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_assoc, ← mul_sum,
    Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- **The best linear unbiased predictor in true MSE**: among all `Σᵢ dᵢ μ̂ᵢ` with
`Σᵢ dᵢ = 1`, the weights `d* = blupWeight` minimise the actual mean squared error for
`μⱼ`, for every distribution with these moments. -/
theorem blup_mse_optimal (hK : K.PosDef) (j : J) (d : J → ℝ) (hd : ∑ i, d i = 1) :
    P[fun ω => (E.portLin (blupWeight K L j) ω - E.level j ω) ^ 2]
      ≤ P[fun ω => (E.portLin d ω - E.level j ω) ^ 2] := by
  have : Nonempty J := ⟨j⟩
  rw [E.mse_portLin j _ (sum_blupWeight hK L j), E.mse_portLin j d hd]
  exact blupWeight_optimal hK L j d hd

/-- **The price of the blend in true MSE**: the blend with factor `z` has the mean
squared error of the best linear unbiased predictor plus `(w - d*)ᵀK(w - d*)`,
`w = z eⱼ + (1 - z) b`. So no blend beats it, and the blend is as good only when
`w = d*` (`blendWeight_eq_blupWeight_iff`). -/
theorem mse_blend_eq_blup_add (hK : K.PosDef) (j : J) (z : ℝ) :
    P[fun ω => (E.blend j z ω - E.level j ω) ^ 2]
      = P[fun ω => (E.portLin (blupWeight K L j) ω - E.level j ω) ^ 2]
        + (blendWeight K j z - blupWeight K L j) ⬝ᵥ
            (K *ᵥ (blendWeight K j z - blupWeight K L j)) := by
  have : Nonempty J := ⟨j⟩
  rw [E.mse_blend hK j z, E.mse_portLin j _ (sum_blupWeight hK L j)]
  exact errVar_eq_blupWeight_add hK L j z

omit [Fintype J] [DecidableEq J] in
/-- A common component: add to every estimate and its level the same centred
`Cⱼ`, uncorrelated with all estimates and levels, with `cov(Cᵢ, Cⱼ) = Rᵢⱼ`.
Then `K` and `L` both gain `R`. -/
def addCommon (C : J → Ω → ℝ) (R : Matrix J J ℝ) (hC : ∀ j, MemLp (C j) 2 P)
    (hC0 : ∀ j, P[C j] = 0) (hCC : ∀ i j, cov[C i, C j; P] = R i j)
    (hCe : ∀ i j, cov[C i, E.est j; P] = 0) (hCl : ∀ i j, cov[C i, E.level j; P] = 0) :
    Estimates (K + R) (L + R) μ P where
  est j := fun ω => E.est j ω + C j ω
  level j := fun ω => E.level j ω + C j ω
  est_memLp j := (E.est_memLp j).add (hC j)
  level_memLp j := (E.level_memLp j).add (hC j)
  est_mean j := by
    rw [integral_add ((E.est_memLp j).integrable (by norm_num))
      ((hC j).integrable (by norm_num)), E.est_mean, hC0, add_zero]
  level_mean j := by
    rw [integral_add ((E.level_memLp j).integrable (by norm_num))
      ((hC j).integrable (by norm_num)), E.level_mean, hC0, add_zero]
  cov_est i j := by
    rw [cov_add_add (E.est_memLp i) (hC i) (E.est_memLp j) (hC j), E.cov_est,
      covariance_comm (E.est i), hCe, hCe, hCC]
    simp
  cov_level_est i j := by
    rw [cov_add_add (E.level_memLp i) (hC i) (E.est_memLp j) (hC j), E.cov_level_est,
      covariance_comm (E.level i), hCl, hCe, hCC]
    simp
  cov_level i j := by
    rw [cov_add_add (E.level_memLp i) (hC i) (E.level_memLp j) (hC j), E.cov_level,
      covariance_comm (E.level i), hCl, hCl, hCC]
    simp

end Estimates

end Core
end Credibility
