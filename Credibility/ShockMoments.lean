import Credibility.Shock
import Credibility.CoreMoments

/-!
# The moment layer for shock plus process noise (extension, distribution-free)

The moment layer for `Shock.lean`: for **any** probability space and **any** square-integrable
cells `μⱼₜ` and levels `μⱼ` with mean `μ`, cell covariances given by the table `obsCov`
(`δₜₛ(Cᵢⱼ + δᵢⱼsᵢ²/wᵢₜ) + τ²δᵢⱼ`) and level covariances `τ²δᵢⱼ` with the levels and with the
cells, the cohort estimates `μ̂ⱼ = Σₜ aⱼₜμⱼₜ` are an instance of the Core moment layer
(`Cells.toEstimates`): `K` is their actual covariance, `zⱼ` minimises the actual mean squared
error of the blend (`Cells.bestZ_mse_optimal`), and the §2.8 estimators are unbiased in true
expectation (`Cells.integral_of_unbiasedCov`, `Cells.integral_KHat`). No distribution is
assumed.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

namespace Shock

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The blend moments are the Core ones for `L = τ²I` and `Var(μ̂ⱼ) = Kⱼⱼ`. -/
lemma moments_eq_levelMoments (M : Shock J T) {a : J → T → ℝ} (ha : ∀ j, ∑ t, a j t = 1) (j : J) :
    M.moments a j = Core.levelMoments (M.K a) (M.τ2 • (1 : Matrix J J ℝ)) (M.K a j j) j := by
  rw [moments, Core.moments_eq_levelMoments, M.K_eq_errCov ha]
  simp [add_comm]

/-- Random cells with the covariance table of shock plus process noise, under `P`: cells
`μⱼₜ` and levels `μⱼ` of mean `μ`, `cov(μᵢₜ, μⱼₛ) = obsCov i j t s`, and the level `μᵢ`
covaries only with its own cohort, by `τ²`. Only moments are assumed, no distribution. -/
structure Cells (M : Shock J T) (μ : ℝ) (P : Measure Ω) where
  /-- The cell `μⱼₜ`. -/
  cell : J → T → Ω → ℝ
  /-- The cohort level `μⱼ`. -/
  level : J → Ω → ℝ
  cell_memLp : ∀ j t, MemLp (cell j t) 2 P
  level_memLp : ∀ j, MemLp (level j) 2 P
  cell_mean : ∀ j t, P[cell j t] = μ
  level_mean : ∀ j, P[level j] = μ
  cov_cell : ∀ i j t s, cov[cell i t, cell j s; P] = M.obsCov i j t s
  cov_level_cell : ∀ i j s, cov[level i, cell j s; P] = M.τ2 * if i = j then 1 else 0
  cov_level : ∀ i j, cov[level i, level j; P] = M.τ2 * if i = j then 1 else 0

namespace Cells

variable {M : Shock J T} {μ : ℝ} {P : Measure Ω} (N : M.Cells μ P) (a : J → T → ℝ)

/-- The data at `ω`, indexed by cells `p = (j, t)`. -/
def data (ω : Ω) : J × T → ℝ := fun p => N.cell p.1 p.2 ω

/-- The cohort estimate `μ̂ⱼ = Σₜ aⱼₜμⱼₜ` (`muHat` of the data). -/
def est (j : J) : Ω → ℝ := fun ω => muHat a (N.data ω) j

omit [Fintype J] in
lemma est_def (j : J) : N.est a j = fun ω => ∑ t, a j t * N.cell j t ω := rfl

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] [Fintype J] in
lemma memLp_est (j : J) : MemLp (N.est a j) 2 P := by
  rw [est_def]; exact memLp_finsetSum _ fun t _ => (N.cell_memLp j t).const_mul (a j t)

omit [Fintype J] in
lemma integral_est (ha : ∀ j, ∑ t, a j t = 1) (j : J) : P[N.est a j] = μ := by
  rw [est_def, integral_finsetSum _ fun t _ => ((N.cell_memLp j t).const_mul _).integrable
    (by norm_num)]
  simp only [integral_const_mul, N.cell_mean, ← sum_mul, ha, one_mul]

omit [Fintype J] in
/-- Eq. (21) for shock plus process noise is the actual covariance: `cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ`. -/
theorem cov_est (i j : J) : cov[N.est a i, N.est a j; P] = M.K a i j := by
  rw [est_def, est_def, covariance_fun_sum_fun_sum' (fun t _ => (N.cell_memLp i t).const_mul _)
    (fun s _ => (N.cell_memLp j s).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, N.cov_cell, K, of_apply]
  exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

omit [Fintype J] in
lemma cov_level_est (ha : ∀ j, ∑ t, a j t = 1) (i j : J) :
    cov[N.level i, N.est a j; P] = M.τ2 * if i = j then 1 else 0 := by
  rw [est_def, covariance_fun_sum_right' (fun s _ => (N.cell_memLp j s).const_mul _)
    (N.level_memLp i)]
  simp only [covariance_const_mul_right, N.cov_level_cell, ← sum_mul, ha, one_mul]

/-- The cohort estimates and levels as an instance of the Core moment layer:
`cov(μ̂ᵢ, μ̂ⱼ) = Kᵢⱼ` and level covariance `L = τ²I`. -/
noncomputable def toEstimates (ha : ∀ j, ∑ t, a j t = 1) :
    Core.Estimates (M.K a) (M.τ2 • (1 : Matrix J J ℝ)) μ P where
  est := N.est a
  level := N.level
  est_memLp := N.memLp_est a
  level_memLp := N.level_memLp
  est_mean := N.integral_est a ha
  level_mean := N.level_mean
  cov_est := N.cov_est a
  cov_level_est i j := by
    rw [N.cov_level_est a ha]; by_cases h : i = j <;> simp [h]
  cov_level i j := by
    rw [N.cov_level]; by_cases h : i = j <;> simp [h]

/-- The blend `z μ̂ⱼ + (1 - z) μ̂` with the GLS portfolio estimate of `K` (`Core.blend`). -/
noncomputable abbrev blend (j : J) (z : ℝ) : Ω → ℝ := Core.blend (M.K a) (N.est a) j z

/-- The blend is unbiased and its actual mean squared error is `errVar`, eq. (6), with the
`K` of shock plus process noise. -/
theorem mse_blend (ha : ∀ j, ∑ t, a j t = 1) (j : J) (z : ℝ) :
    P[fun ω => (N.blend a j z ω - N.level j ω) ^ 2] = (M.moments a j).errVar z := by
  rw [M.moments_eq_levelMoments ha]
  exact (N.toEstimates a ha).mse_blend (M.K_posDef ha) j z

/-- Eq. (26) under shock plus process noise, in true MSE: `zⱼ` (`Shock.bestZ_eq`) minimises
the actual mean squared error of the blend, for every distribution with these moments. -/
theorem bestZ_mse_optimal (ha : ∀ j, ∑ t, a j t = 1) (j : J)
    (hgap : 0 < (M.moments a j).gap) (z : ℝ) :
    P[fun ω => (N.blend a j (M.moments a j).bestZ ω - N.level j ω) ^ 2]
      ≤ P[fun ω => (N.blend a j z ω - N.level j ω) ^ 2] := by
  rw [N.mse_blend a ha, N.mse_blend a ha]
  exact (M.moments a j).bestZ_optimal hgap z

/-- §2.8 in true expectation: an estimator unbiased under the table `Shock.cov` has
expectation `θ` for any random cells with that table. -/
theorem integral_of_unbiasedCov {f : (J × T → ℝ) → ℝ} {θ : ℝ}
    (h : Model.UnbiasedCov M.cov f θ) : P[fun ω => f (N.data ω)] = θ := by
  obtain ⟨Q, hQ, hE⟩ := h
  simp only [← hQ]
  exact (Model.integral_quad_of_cov (fun p => N.cell p.1 p.2) M.cov μ Q (fun _ => True)
    (fun _ _ _ => ⟨trivial, trivial⟩) (fun p _ => N.cell_memLp p.1 p.2)
    (fun p _ => N.cell_mean p.1 p.2) (fun p q _ _ => N.cov_cell p.1 q.1 p.2 q.2)).trans (hE μ)

/-- **`K̂` is unbiased in true expectation**: `E K̂ᵢⱼ = Kᵢⱼ` for any random cells with the
table of shock plus process noise (`KHat_unbiased`). -/
theorem integral_KHat (ha : ∀ j, ∑ t, a j t = 1) {u v : J → T → ℝ}
    (hd : ∀ i j, i ≠ j → ∑ t, d a i j t ≠ 0) (hdet : ∀ j, M.det a u v j ≠ 0)
    {x : J → ℝ} (hx : ∑ j, x j = 1) (hx2 : ∑ j, x j ^ 2 ≠ 1) (i j : J) :
    P[fun ω => M.KHat a u v x (N.data ω) i j] = M.K a i j :=
  N.integral_of_unbiasedCov (M.KHat_unbiased ha hd hdet hx hx2 i j)

end Cells

end Shock

end Credibility
