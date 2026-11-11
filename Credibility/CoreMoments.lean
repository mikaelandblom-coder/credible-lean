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
