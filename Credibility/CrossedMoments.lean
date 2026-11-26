import Credibility.CrossedEstimation
import Credibility.HierarchicalMoments

/-!
# The moment layer for crossed levels (extension, distribution-free)

`Crossed.lean` and `CrossedEstimation.lean` take the crossed covariances as given numbers.
Here they are the actual covariances of the random variables

  `μⱼ = μ + √γ² ηⱼ + √α² A_{row j} + √β² B_{col j}`,  `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`,

for **any** square-integrable `η`, `ε` with the moments of the thesis model `M` (eq. (15), with
level variance `M.τ2 = γ²`, the cell effect) and any row effects `A_a` and column effects `B_b`:
centred, of unit variance, uncorrelated with each other, with `η` and with `ε`. Then:

* `obsCovX` is the covariance of the observations, so `UnbiasedX` is about the true expectation
  (`integral_quad`), and the pair estimators of `α²`, `β²`, `γ²` are unbiased in fact
  (`crossed_integral`);
* `cov(μ̂ᵢ, μ̂ⱼ)` is the crossed `K` and `cov(μᵢ, μⱼ)` the crossed `L` (`toEstimates`), so the
  crossed best predictor has the smallest true mean squared error (`blup_mse_optimal`);
* such random variables exist iff `ρ ⪰ 0`, as in the thesis (`exists_noiseX_iff`): the row and
  column effects add no constraint.

As for groups (`HierarchicalMoments.lean`), the row and column effects are one common component
(`Core.Estimates.addCommon`) on top of the thesis moment layer (`Model.Noise.toEstimates`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Model

variable {J T A B : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Random variables with crossed levels, under `P`: cell effects `η` and noise `ε` as in the
thesis model `M` (`M.τ2` is the cell variance `γ²`), row effects `A_a` and column effects `B_b`,
centred, of unit variance, uncorrelated with each other, with `η` and with `ε`. Only moments
are assumed, no distribution. -/
structure NoiseX (M : Model J T) (row : J → A) (col : J → B) (P : Measure Ω)
    extends Noise M P where
  /-- Row effect `A_a`. -/
  rowEff : A → Ω → ℝ
  /-- Column effect `B_b`. -/
  colEff : B → Ω → ℝ
  rowEff_memLp : ∀ a, MemLp (rowEff a) 2 P
  colEff_memLp : ∀ b, MemLp (colEff b) 2 P
  rowEff_mean : ∀ a, P[rowEff a] = 0
  colEff_mean : ∀ b, P[colEff b] = 0
  cov_row_row : ∀ a a', cov[rowEff a, rowEff a'; P] = if a = a' then 1 else 0
  cov_col_col : ∀ b b', cov[colEff b, colEff b'; P] = if b = b' then 1 else 0
  cov_row_col : ∀ a b, cov[rowEff a, colEff b; P] = 0
  cov_row_η : ∀ a j, cov[rowEff a, η j; P] = 0
  cov_row_ε : ∀ a j t, cov[rowEff a, ε j t; P] = 0
  cov_col_η : ∀ b j, cov[colEff b, η j; P] = 0
  cov_col_ε : ∀ b j t, cov[colEff b, ε j t; P] = 0

namespace NoiseX

variable {M : Model J T} {row : J → A} {col : J → B} {P : Measure Ω}
  (N : M.NoiseX row col P) (α2 β2 μ : ℝ)

/-- The row and column component `√α² A_{row j} + √β² B_{col j}` of cell `j`. -/
noncomputable def common (j : J) : Ω → ℝ :=
  fun ω => Real.sqrt α2 * N.rowEff (row j) ω + Real.sqrt β2 * N.colEff (col j) ω

/-- The cell level `μⱼ = μ + √γ² ηⱼ + √α² A_{row j} + √β² B_{col j}`. -/
noncomputable def trueMean (j : J) : Ω → ℝ :=
  fun ω => N.toNoise.trueMean μ j ω + N.common α2 β2 j ω

/-- The observation `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`. -/
noncomputable def obs (j : J) (t : T) : Ω → ℝ :=
  fun ω => N.toNoise.obs μ j t ω + N.common α2 β2 j ω

/-- The cell estimate `μ̂ⱼ = Σₜ aⱼₜ μⱼₜ`, eq. (23). -/
noncomputable def cohortEst (j : J) : Ω → ℝ := fun ω => ∑ t, M.a j t * N.obs α2 β2 μ j t ω

/-- The row and column effects as one family over `A ⊕ B`. -/
def effects : A ⊕ B → Ω → ℝ := Sum.elim N.rowEff N.colEff

/-- The common component is `Core.common` with the two effects `inl (row j)`, `inr (col j)` and
loadings `√α²`, `√β²`. -/
lemma common_eq (j : J) :
    N.common α2 β2 j = Core.common (fun j => {Sum.inl (row j), Sum.inr (col j)})
      (fun _ => Sum.elim (fun _ => Real.sqrt α2) (fun _ => Real.sqrt β2)) N.effects j := by
  funext ω
  simp [common, Core.common, effects, Finset.sum_pair (Sum.inl_ne_inr)]

lemma effects_memLp (k : A ⊕ B) : MemLp (N.effects k) 2 P := by
  cases k
  exacts [N.rowEff_memLp _, N.colEff_memLp _]

/-- The row and column effects pass through the cell weights (`Σₜ aⱼₜ = 1`). -/
lemma cohortEst_eq [Nonempty T] (j : J) :
    N.cohortEst α2 β2 μ j = fun ω => N.toNoise.cohortEst μ j ω + N.common α2 β2 j ω := by
  have hs : ∑ t ∈ univ, M.a j t = 1 := by rw [← M.toUnequal_a]; exact M.toUnequal.sum_a_univ j
  exact Core.cohortEst_eq univ hs (fun t => N.toNoise.obs μ j t) (N.common α2 β2 j)

lemma memLp_common (j : J) : MemLp (N.common α2 β2 j) 2 P := by
  rw [common_eq]
  exact Core.memLp_common _ _ N.effects_memLp j

lemma integral_common [IsProbabilityMeasure P] (j : J) : P[N.common α2 β2 j] = 0 := by
  rw [common_eq]
  exact Core.integral_common _ _ N.effects_memLp
    (fun k => by cases k; exacts [N.rowEff_mean _, N.colEff_mean _]) j

variable [IsProbabilityMeasure P]

/-- The effects are orthonormal: `cov(Zₖ, Zₗ) = [k = l]` over `A ⊕ B`. -/
lemma cov_effects (k l : A ⊕ B) : cov[N.effects k, N.effects l; P] = if k = l then 1 else 0 := by
  cases k <;> cases l <;> simp [effects, N.cov_row_row, N.cov_col_col, N.cov_row_col,
    covariance_comm (N.colEff _) (N.rowEff _)]

/-- `cov(common i, common j) = α²[row i = row j] + β²[col i = col j]` (`Core.cov_common`). -/
lemma cov_common {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (i j : J) :
    cov[N.common α2 β2 i, N.common α2 β2 j; P]
      = (α2 • Model.sameGroup row + β2 • Model.sameGroup col) i j := by
  rw [common_eq, common_eq, Core.cov_common _ _ N.effects_memLp N.cov_effects]
  have ha := Real.mul_self_sqrt hα
  have hb := Real.mul_self_sqrt hβ
  simp only [Finset.sum_pair Sum.inl_ne_inr, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ite_false, mul_zero, add_zero, zero_add, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Model.sameGroup, of_apply]
  split_ifs <;> nlinarith

/-- The common component is uncorrelated with anything the row and column effects are. -/
lemma cov_common_of {Y : Ω → ℝ} (hY : MemLp Y 2 P) (h1 : ∀ a, cov[N.rowEff a, Y; P] = 0)
    (h2 : ∀ b, cov[N.colEff b, Y; P] = 0) (j : J) : cov[N.common α2 β2 j, Y; P] = 0 := by
  rw [common_eq]
  exact Core.cov_common_of _ _ N.effects_memLp hY (fun k => by cases k; exacts [h1 _, h2 _]) j

lemma cov_eff_trueMean {Z : Ω → ℝ} (hZ : MemLp Z 2 P) (hη : ∀ j, cov[Z, N.η j; P] = 0) (j : J) :
    cov[Z, N.toNoise.trueMean μ j; P] = 0 := by
  rw [show N.toNoise.trueMean μ j = fun ω => μ + Real.sqrt M.τ2 * N.η j ω from rfl,
    covariance_const_add_right (((N.η_memLp j).const_mul _).integrable (by norm_num)),
    covariance_const_mul_right, hη, mul_zero]

lemma cov_eff_obs {Z : Ω → ℝ} (hZ : MemLp Z 2 P) (hη : ∀ j, cov[Z, N.η j; P] = 0)
    (hε : ∀ j t, cov[Z, N.ε j t; P] = 0) (j : J) (t : T) :
    cov[Z, N.toNoise.obs μ j t; P] = 0 := by
  rw [show N.toNoise.obs μ j t = N.toNoise.trueMean μ j + fun ω => M.σ j t * N.ε j t ω from rfl,
    covariance_add_right hZ (N.toNoise.memLp_trueMean μ j) ((N.ε_memLp j t).const_mul _),
    N.cov_eff_trueMean μ hZ hη, covariance_const_mul_right, hε, mul_zero, add_zero]

lemma cov_eff_cohortEst {Z : Ω → ℝ} (hZ : MemLp Z 2 P) (hη : ∀ j, cov[Z, N.η j; P] = 0)
    (hε : ∀ j t, cov[Z, N.ε j t; P] = 0) (j : J) :
    cov[Z, N.toNoise.cohortEst μ j; P] = 0 := by
  rw [show N.toNoise.cohortEst μ j = fun ω => ∑ t, M.a j t * N.toNoise.obs μ j t ω from rfl,
    covariance_fun_sum_right' (s := univ) (X := fun t ω => M.a j t * N.toNoise.obs μ j t ω)
      (fun t _ => (N.toNoise.memLp_obs μ j t).const_mul _) hZ]
  exact sum_eq_zero fun t _ => by rw [covariance_const_mul_right, N.cov_eff_obs μ hZ hη hε, mul_zero]

lemma memLp_obs (j : J) (t : T) : MemLp (N.obs α2 β2 μ j t) 2 P :=
  (N.toNoise.memLp_obs μ j t).add (N.memLp_common α2 β2 j)

/-- The observations are unbiased: `E[μⱼₜ] = μ`. -/
theorem obs_mean (j : J) (t : T) : P[N.obs α2 β2 μ j t] = μ := by
  rw [show N.obs α2 β2 μ j t = fun ω => N.toNoise.obs μ j t ω + N.common α2 β2 j ω from rfl,
    integral_add ((N.toNoise.memLp_obs μ j t).integrable (by norm_num))
      ((N.memLp_common α2 β2 j).integrable (by norm_num)), N.toNoise.obs_mean μ j t,
    N.integral_common, add_zero]

/-- **Eq. (16) with crossed levels is the actual covariance**:
`cov(μᵢₜ, μⱼₛ) = σᵢₜσⱼₛρᵢⱼδₜₛ + α²[same row] + β²[same column] + γ²[i = j]`. -/
theorem cov_obs {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (i j : J) (t s : T) :
    cov[N.obs α2 β2 μ i t, N.obs α2 β2 μ j s; P] = M.obsCovX row col α2 β2 M.τ2 i j t s := by
  have hc : ∀ (k l : J) (u : T), cov[N.common α2 β2 k, N.toNoise.obs μ l u; P] = 0 :=
    fun k l u => N.cov_common_of α2 β2 (N.toNoise.memLp_obs μ l u)
      (fun a => N.cov_eff_obs μ (N.rowEff_memLp a) (N.cov_row_η a) (N.cov_row_ε a) l u)
      (fun b => N.cov_eff_obs μ (N.colEff_memLp b) (N.cov_col_η b) (N.cov_col_ε b) l u) k
  rw [show N.obs α2 β2 μ i t = fun ω => N.toNoise.obs μ i t ω + N.common α2 β2 i ω from rfl,
    show N.obs α2 β2 μ j s = fun ω => N.toNoise.obs μ j s ω + N.common α2 β2 j ω from rfl,
    cov_add_add (N.toNoise.memLp_obs μ i t) (N.memLp_common α2 β2 i)
      (N.toNoise.memLp_obs μ j s) (N.memLp_common α2 β2 j),
    N.toNoise.cov_obs μ i j t s, covariance_comm (N.toNoise.obs μ i t), hc, hc,
    N.cov_common hα hβ, obsCovX, obsCov, Crossed.levelCov_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Model.sameGroup, of_apply]
  ring

/-- §2.8 in true expectation with crossed levels: for any quadratic form of the data,
`E[Σₚ,q Qₚq μₚ μq]` is `Ecov` for the table `obsCovX`. So `UnbiasedX f θ` means `E f = θ`
for any random variables with these moments. -/
theorem integral_quad {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (Q : J × T → J × T → ℝ) :
    P[fun ω => quad Q (fun p => N.obs α2 β2 μ p.1 p.2 ω)]
      = Ecov (fun p q => M.obsCovX row col α2 β2 M.τ2 p.1 q.1 p.2 q.2) μ Q :=
  integral_quad_of_cov (fun p => N.obs α2 β2 μ p.1 p.2) _ μ Q (fun _ => True)
    (fun _ _ _ => ⟨trivial, trivial⟩) (fun p _ => N.memLp_obs α2 β2 μ p.1 p.2)
    (fun p _ => N.obs_mean α2 β2 μ p.1 p.2) (fun p q _ _ => N.cov_obs μ hα hβ p.1 q.1 p.2 q.2)

/-- An estimator unbiased with crossed levels (`UnbiasedX`) has that expectation in fact. -/
theorem integral_of_unbiasedX {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2)
    {f : (J × T → ℝ) → ℝ} {θ : ℝ} (hf : M.UnbiasedX row col α2 β2 M.τ2 f θ) :
    P[fun ω => f (fun p => N.obs α2 β2 μ p.1 p.2 ω)] = θ := by
  obtain ⟨Q, hQ, hE⟩ := hf
  simp only [← hQ]
  rw [N.integral_quad μ hα hβ, hE]

/-- **The crossed variances are estimated without bias, in fact**: for any random variables
with these moments, the pooled pair estimators of `CrossedEstimation.lean` have expectations
`α²`, `β²` and `γ²` (`= M.τ2`). -/
theorem crossed_integral {w : J → T → ℝ} (sig : J → ℝ)
    (hw : ∀ j t, 0 < w j t) (hσ : ∀ j t, M.σ j t = sig j / √(w j t)) (hT : 2 ≤ Fintype.card T)
    {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (r c n : J × J → ℝ)
    (hr : ∑ p ∈ sameRowPairs row col, r p = 1) (hc : ∑ p ∈ sameColPairs row col, c p = 1)
    (hn : ∑ p ∈ crossPairs row col, n p = 1) :
    P[fun ω => (pairPool w (crossPairs row col) n (fun p => N.obs α2 β2 μ p.1 p.2 ω)
        - pairPool w (sameRowPairs row col) r (fun p => N.obs α2 β2 μ p.1 p.2 ω)) / 2] = α2
      ∧ P[fun ω => (pairPool w (crossPairs row col) n (fun p => N.obs α2 β2 μ p.1 p.2 ω)
        - pairPool w (sameColPairs row col) c (fun p => N.obs α2 β2 μ p.1 p.2 ω)) / 2] = β2
      ∧ P[fun ω => (pairPool w (sameRowPairs row col) r (fun p => N.obs α2 β2 μ p.1 p.2 ω)
        + pairPool w (sameColPairs row col) c (fun p => N.obs α2 β2 μ p.1 p.2 ω)
        - pairPool w (crossPairs row col) n (fun p => N.obs α2 β2 μ p.1 p.2 ω)) / 2] = M.τ2 := by
  obtain ⟨h1, h2, h3⟩ := M.crossed_unbiasedX row col sig hw hσ hT α2 β2 M.τ2 r c n hr hc hn
  exact ⟨N.integral_of_unbiasedX μ hα hβ h1, N.integral_of_unbiasedX μ hα hβ h2,
    N.integral_of_unbiasedX μ hα hβ h3⟩

/-! ### The cell estimates and levels as a Core moment layer -/

/-- The crossed `K` with the thesis noise is `K + α²S_row + β²S_col`. -/
lemma K_eq [Nonempty T] (α2 β2 : ℝ) :
    Crossed.K row col α2 β2 M.τ2 M.errCov
      = M.K + (α2 • Model.sameGroup row + β2 • Model.sameGroup col) := by
  rw [Crossed.K, Crossed.levelCov, M.errCov_eq]
  abel

lemma levelCov_eq (α2 β2 : ℝ) :
    Crossed.levelCov row col α2 β2 M.τ2
      = M.τ2 • (1 : Matrix J J ℝ) + (α2 • Model.sameGroup row + β2 • Model.sameGroup col) := by
  rw [Crossed.levelCov]
  abel

/-- The thesis moment layer plus the row and column component. -/
noncomputable def addCommon [Nonempty T] {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) :
    Core.Estimates (M.K + (α2 • Model.sameGroup row + β2 • Model.sameGroup col))
      (M.τ2 • (1 : Matrix J J ℝ) + (α2 • Model.sameGroup row + β2 • Model.sameGroup col)) μ P :=
  (N.toNoise.toEstimates μ).addCommon (N.common α2 β2) _ (N.memLp_common α2 β2)
    (N.integral_common α2 β2) (N.cov_common hα hβ)
    (fun i j => N.cov_common_of α2 β2 (N.toNoise.toEstimates μ |>.est_memLp j)
      (fun a => N.cov_eff_cohortEst μ (N.rowEff_memLp a) (N.cov_row_η a) (N.cov_row_ε a) j)
      (fun b => N.cov_eff_cohortEst μ (N.colEff_memLp b) (N.cov_col_η b) (N.cov_col_ε b) j) i)
    (fun i j => N.cov_common_of α2 β2 (N.toNoise.memLp_trueMean μ j)
      (fun a => N.cov_eff_trueMean μ (N.rowEff_memLp a) (N.cov_row_η a) j)
      (fun b => N.cov_eff_trueMean μ (N.colEff_memLp b) (N.cov_col_η b) j) i)

/-- **The crossed `K` and `L` are the actual covariances**: the cell estimates and levels as an
instance of the Core moment layer, `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`, `cov(μᵢ, μ̂ⱼ) = cov(μᵢ, μⱼ) = Lᵢⱼ`. -/
noncomputable def toEstimates [Nonempty T] {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) :
    Core.Estimates (Crossed.K row col α2 β2 M.τ2 M.errCov) (Crossed.levelCov row col α2 β2 M.τ2)
      μ P where
  est := N.cohortEst α2 β2 μ
  level := N.trueMean α2 β2 μ
  est_memLp j := by rw [N.cohortEst_eq]; exact (N.addCommon μ hα hβ).est_memLp j
  level_memLp j := (N.addCommon μ hα hβ).level_memLp j
  est_mean j := by rw [N.cohortEst_eq]; exact (N.addCommon μ hα hβ).est_mean j
  level_mean j := (N.addCommon μ hα hβ).level_mean j
  cov_est i j := by
    rw [N.cohortEst_eq, N.cohortEst_eq, K_eq]
    exact (N.addCommon μ hα hβ).cov_est i j
  cov_level_est i j := by
    rw [N.cohortEst_eq, levelCov_eq]
    exact (N.addCommon μ hα hβ).cov_level_est i j
  cov_level i j := by
    rw [levelCov_eq]
    exact (N.addCommon μ hα hβ).cov_level i j

/-- **The crossed predictor in true mean squared error**: among all `Σᵢ dᵢμ̂ᵢ` with `Σᵢ dᵢ = 1`,
the best linear unbiased predictor for the crossed `K`, `L` minimises the actual mean squared
error for every cell level, for every distribution with these moments (`ρ ⪰ 0`). In the balanced
table with `σ²ᵢⱼρᵢⱼ = σ²δᵢⱼ` its weights are those of `Crossed.blup_balanced`. -/
theorem blup_mse_optimal [Nonempty T] {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2)
    (hρ : (Matrix.of M.ρ).PosSemidef) (j : J) (d : J → ℝ) (hd : ∑ i, d i = 1) :
    P[fun ω => ((N.toEstimates μ hα hβ).portLin
          (Core.blupWeight (Crossed.K row col α2 β2 M.τ2 M.errCov)
            (Crossed.levelCov row col α2 β2 M.τ2) j) ω - N.trueMean α2 β2 μ j ω) ^ 2]
      ≤ P[fun ω => ((N.toEstimates μ hα hβ).portLin d ω - N.trueMean α2 β2 μ j ω) ^ 2] :=
  (N.toEstimates μ hα hβ).blup_mse_optimal
    (Crossed.K_posDef_of_gamma row col hα hβ M.τ2_pos (M.errCov_posSemidef hρ)) j d hd

/-- …and the actual mean squared error of any such predictor is `linMse` for the crossed `K`,
`L`: the closed forms of `Crossed.lean` (`sum_linMse_blup`, `sum_linMse_blend`) are true errors. -/
theorem mse_portLin [Nonempty T] {α2 β2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (j : J) (d : J → ℝ)
    (hd : ∑ i, d i = 1) :
    P[fun ω => ((N.toEstimates μ hα hβ).portLin d ω - N.trueMean α2 β2 μ j ω) ^ 2]
      = Core.linMse (Crossed.K row col α2 β2 M.τ2 M.errCov)
          (Crossed.levelCov row col α2 β2 M.τ2) j d :=
  (N.toEstimates μ hα hβ).mse_portLin j d hd

end NoiseX

/-! ### Consistency: when do such random variables exist? -/

/-- The crossed assumptions are consistent exactly when `ρ` is positive semidefinite, as for the
thesis model (`exists_noise_iff`): row and column effects add no constraint. Witness: the noise
of `exists_noise_iff` on one factor, independent standard normal row and column effects on the
other (a witness only; the model stays distribution-free). Rows and columns are labels in
`Type`, like `Ω`. -/
theorem exists_noiseX_iff {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty T]
    (M : Model J T) (row : J → A) (col : J → B) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (M.NoiseX row col P)) ↔ (Matrix.of M.ρ).PosSemidef := by
  constructor
  · rintro ⟨Ω, _, P, _, ⟨N⟩⟩
    exact M.exists_noise_iff.mp ⟨Ω, _, P, inferInstance, ⟨N.toNoise⟩⟩
  · intro hρ
    obtain ⟨Ω₀, _, P₀, _, ⟨N₀⟩⟩ := M.exists_noise_iff.mpr hρ
    set Q : Measure (A ⊕ B → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1 with hQdef
    have hγ : ∀ k, HasLaw (fun x : A ⊕ B → ℝ => x k) (gaussianReal 0 1) Q :=
      fun k => (measurePreserving_eval_infinitePi (fun _ : A ⊕ B => gaussianReal 0 1) k).hasLaw
    have hQ : IsProbabilityMeasure Q := by dsimp only [Q]; infer_instance
    have hind : iIndepFun (fun k (x : A ⊕ B → ℝ) => x k) Q := by
      rw [hQdef]; exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
    clear_value Q
    have hsnd : HasLaw Prod.snd Q (P₀.prod Q) := measurePreserving_snd.hasLaw
    have hfst : HasLaw Prod.fst P₀ (P₀.prod Q) := measurePreserving_fst.hasLaw
    have hm : ∀ k, MemLp (fun x : A ⊕ B → ℝ => x k) 2 Q :=
      fun k => (hγ k).memLp_comp (memLp_id_gaussianReal' 2 (by simp))
    have hm' : ∀ k, MemLp (fun p : Ω₀ × (A ⊕ B → ℝ) => p.2 k) 2 (P₀.prod Q) :=
      fun k => hsnd.memLp_comp (hm k)
    have hmean : ∀ k, ∫ p, p.2 k ∂(P₀.prod Q) = 0 := fun k =>
      (hsnd.integral_comp (f := fun x : A ⊕ B → ℝ => x k) (hm k).aestronglyMeasurable).trans
        ((hγ k).integral_eq.trans integral_id_gaussianReal)
    have hcov : ∀ k k', cov[fun p : Ω₀ × (A ⊕ B → ℝ) => p.2 k, fun p => p.2 k'; P₀.prod Q]
        = if k = k' then 1 else 0 := fun k k' => by
      rw [hsnd.covariance_fun_comp (f := fun x : A ⊕ B → ℝ => x k) (g := fun x => x k')
        (hm k).aemeasurable (hm k').aemeasurable]
      by_cases h : k = k'
      · subst h
        rw [covariance_self (hm k).aemeasurable, (hγ k).variance_eq, variance_id_gaussianReal]
        simp
      · simp only [h, ↓reduceIte]
        exact (hind.indepFun h).covariance_eq_zero (hm k) (hm k')
    have hη : ∀ k j, cov[fun p : Ω₀ × (A ⊕ B → ℝ) => p.2 k, fun p => N₀.η j p.1; P₀.prod Q] = 0 :=
      fun k j => by
        rw [covariance_comm]
        exact covariance_fst_snd_prod (μ := P₀) (ν := Q) (X := N₀.η j)
          (Y := fun x : A ⊕ B → ℝ => x k) (N₀.η_memLp j) (hm k)
    have hε : ∀ k j t,
        cov[fun p : Ω₀ × (A ⊕ B → ℝ) => p.2 k, fun p => N₀.ε j t p.1; P₀.prod Q] = 0 :=
      fun k j t => by
        rw [covariance_comm]
        exact covariance_fst_snd_prod (μ := P₀) (ν := Q) (X := N₀.ε j t)
          (Y := fun x : A ⊕ B → ℝ => x k) (N₀.ε_memLp j t) (hm k)
    let N := (N₀.toUnequal.comp hfst)
    exact ⟨Ω₀ × (A ⊕ B → ℝ), inferInstance, P₀.prod Q, inferInstance,
      ⟨{ toNoise := Noise.ofUnequal N
         rowEff := fun a p => p.2 (Sum.inl a)
         colEff := fun b p => p.2 (Sum.inr b)
         rowEff_memLp := fun a => hm' _
         colEff_memLp := fun b => hm' _
         rowEff_mean := fun a => hmean _
         colEff_mean := fun b => hmean _
         cov_row_row := fun a a' => by rw [hcov]; simp
         cov_col_col := fun b b' => by rw [hcov]; simp
         cov_row_col := fun a b => by rw [hcov]; simp
         cov_row_η := fun a j => hη _ j
         cov_row_ε := fun a j t => hε _ j t
         cov_col_η := fun b j => hη _ j
         cov_col_ε := fun b j t => hε _ j t }⟩⟩

end Model
end Credibility
