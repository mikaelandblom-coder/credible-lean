import Credibility.UnequalMoments

/-!
# A known common trend (extension, not in the thesis)

Step 1 and 2 of `notes/time-trends.md` §1. The world has a common claim trend `g`
(`x %` a year) with noise that grows with the level (constant coefficient of
variation): `Xⱼₜ = (1+g)^t (μⱼ + σⱼₜ εⱼₜ)`. Restated to the target year `n`
(usually `T + 1`), `X̃ⱼₜ = (1+g)^(n−t) Xⱼₜ = (1+g)^n (μⱼ + σⱼₜ εⱼₜ)`: the thesis
model (`Unequal`) with `τ` and every `σⱼₜ` multiplied by `c = (1+g)^n`
(`Unequal.detrend`). So nothing new is needed: all results apply to `X̃`.

* `Unequal.scale`: the model in a unit `c` times smaller. Cell weights `aⱼₜ`,
  GLS weights `bⱼ` and `zⱼ` are unchanged; `K`, `s²` and all blend moments scale by `c²`.
* `Unequal.detrend`: `c = (1+g)^n`, so `K̃ = (1+g)^(2n) K`.
* Moment layer: the restated data of a trended world are the observations of
  `M.detrend` (`Noise.detrend_obs`), and every estimate is `c` times the
  untrended one, so the fitted relativities `blendⱼ / μ̂` do not depend on `g`
  (`Noise.relativity_detrend`, step 2).
-/

open Finset Matrix MeasureTheory

namespace Credibility
namespace Unequal

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Unequal J T)

/-- The model in a unit `c > 0` times smaller: levels and noise multiplied by `c`
(`τ² ↦ c²τ²`, `σⱼₜ ↦ cσⱼₜ`); correlations and observed periods unchanged. -/
def scale (c : ℝ) (hc : 0 < c) : Unequal J T where
  τ2 := c ^ 2 * M.τ2
  σ j t := c * M.σ j t
  ρ := M.ρ
  τ2_pos := mul_pos (pow_pos hc 2) M.τ2_pos
  σ_pos j t := mul_pos hc (M.σ_pos j t)
  ρ_self := M.ρ_self
  ρ_symm := M.ρ_symm
  obs := M.obs
  obs_nonempty := M.obs_nonempty

/-- The model of the data restated to the target year `n` with a known common trend
`g > -1`, constant coefficient of variation: `M.scale ((1+g)^n)`. -/
def detrend (g : ℝ) (hg : -1 < g) (n : ℕ) : Unequal J T :=
  M.scale ((1 + g) ^ n) (pow_pos (by linarith) n)

variable {c : ℝ} (hc : 0 < c)

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- The cell weights `aⱼₜ` (eq. (23) on `Tⱼ`) are unit-free. -/
theorem a_scale : (M.scale c hc).a = M.a := by
  ext j t
  simp only [a, scale]
  by_cases h : t ∈ M.obs j
  · have hc2 : (c ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_pos hc 2).ne'
    simp only [h, ite_true, mul_pow, mul_inv]
    rw [← mul_sum, mul_div_mul_left _ _ hc2]
  · simp [h]

omit [Fintype J] [DecidableEq J] [Fintype T] in
theorem σ2_scale (i j : J) : (M.scale c hc).σ2 i j = c ^ 2 * M.σ2 i j := by
  simp only [σ2, overlap, a_scale]
  rw [mul_sum]
  exact sum_congr rfl fun t _ => by simp only [scale]; ring

omit [Fintype J] [Fintype T] in
/-- `K` scales by `c²`. -/
theorem K_scale : (M.scale c hc).K = c ^ 2 • M.K := by
  ext i j
  rw [K_apply, σ2_scale, Matrix.smul_apply, K_apply, smul_eq_mul]
  simp only [scale]
  ring

omit [Fintype T] in
/-- The GLS weights `bⱼ` are unit-free. -/
theorem b_scale : (M.scale c hc).b = M.b := by
  rw [b, b, K_scale, glsWeight_smul _ (pow_pos hc 2).ne']

omit [Fintype T] in
/-- `s²` scales by `c²`. -/
theorem s2_scale : (M.scale c hc).s2 = c ^ 2 * M.s2 := by
  rw [s2, s2, K_scale, invTotal_smul _ (pow_pos hc 2).ne', mul_inv, inv_inv]

omit [Fintype T] in
/-- All blend moments scale by `c²`. -/
theorem moments_scale (j : J) : (M.scale c hc).moments j = (M.moments j).smul (c ^ 2) := by
  have hv : (fun j => (M.scale c hc).σ2 j j) = c ^ 2 • fun j => M.σ2 j j := by
    ext j; simp [σ2_scale]
  rw [moments, moments, K_scale, hv]
  exact Core.moments_smul (pow_pos hc 2).ne' j

omit [Fintype T] in
/-- The best credibility factor `zⱼ` is unit-free. -/
theorem bestZ_scale (j : J) : ((M.scale c hc).moments j).bestZ = (M.moments j).bestZ := by
  rw [moments_scale, BlendMoments.bestZ_smul _ (pow_pos hc 2).ne']

omit [Fintype J] [Fintype T] in
theorem K_posDef_scale (hK : M.K.PosDef) : (M.scale c hc).K.PosDef := by
  rw [K_scale]; exact hK.smul (pow_pos hc 2)

/-! ### A known common trend -/

variable (g : ℝ) (hg : -1 < g) (n : ℕ)

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Restating to the target year does not move the cell weights `aⱼₜ`. -/
theorem a_detrend : (M.detrend g hg n).a = M.a := M.a_scale _

omit [Fintype J] [Fintype T] in
/-- The restated data have `K̃ = (1+g)^(2n) K` (`n = T + 1` for next year). -/
theorem K_detrend : (M.detrend g hg n).K = (1 + g) ^ (2 * n) • M.K := by
  rw [detrend, K_scale, ← pow_mul, mul_comm n 2]

omit [Fintype T] in
/-- …so the GLS weights `bⱼ` do not depend on the trend. -/
theorem b_detrend : (M.detrend g hg n).b = M.b := M.b_scale _

omit [Fintype T] in
theorem s2_detrend : (M.detrend g hg n).s2 = (1 + g) ^ (2 * n) * M.s2 := by
  rw [detrend, s2_scale, ← pow_mul, mul_comm n 2]

omit [Fintype T] in
/-- …nor does the best credibility factor `zⱼ`: trend first, then blend; the weights do not move. -/
theorem bestZ_detrend (j : J) : ((M.detrend g hg n).moments j).bestZ = (M.moments j).bestZ :=
  M.bestZ_scale _ j

omit [Fintype J] [Fintype T] in
theorem K_posDef_detrend (hK : M.K.PosDef) : (M.detrend g hg n).K.PosDef :=
  M.K_posDef_scale _ hK

/-! ### The moment layer: restated data and trend-free relativities -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M}

namespace Noise

variable (N : M.Noise P) (μ : ℝ)

/-- The same cohort effects and noise, read in the scaled model. -/
def scale (c : ℝ) (hc : 0 < c) : (M.scale c hc).Noise P where
  η := N.η
  ε := N.ε
  η_memLp := N.η_memLp
  ε_memLp := N.ε_memLp
  η_mean := N.η_mean
  ε_mean := N.ε_mean
  cov_η_η := N.cov_η_η
  cov_η_ε := N.cov_η_ε
  cov_ε_ε := N.cov_ε_ε

/-- The same cohort effects and noise, read in the restated model `M.detrend g hg n`. -/
def detrend : (M.detrend g hg n).Noise P := N.scale _ _

omit [Fintype J] [Fintype T] in
theorem obsVal_scale (j : J) (t : T) (ω : Ω) :
    (N.scale c hc).obsVal (c * μ) j t ω = c * N.obsVal μ j t ω := by
  have hs : Real.sqrt (c ^ 2 * M.τ2) = c * Real.sqrt M.τ2 := by
    rw [Real.sqrt_mul (pow_nonneg hc.le 2), Real.sqrt_sq hc.le]
  simp only [obsVal, trueMean, scale, Unequal.scale, hs]
  ring

omit [Fintype J] [Fintype T] in
theorem cohortEst_scale (j : J) (ω : Ω) :
    (N.scale c hc).cohortEst (c * μ) j ω = c * N.cohortEst μ j ω := by
  simp only [cohortEst, cohortLin, a_scale, obsVal_scale, mul_sum]
  exact sum_congr rfl fun t _ => by ring

theorem portEst_scale (ω : Ω) :
    (N.scale c hc).portEst (c * μ) ω = c * N.portEst μ ω := by
  simp only [portEst, Core.portEst, Core.portLin, K_scale, glsWeight_smul _ (pow_pos hc 2).ne',
    mul_sum]
  exact sum_congr rfl fun j _ => by rw [cohortEst_scale]; ring

theorem blend_scale (j : J) (z : ℝ) (ω : Ω) :
    (N.scale c hc).blend (c * μ) j z ω = c * N.blend μ j z ω := by
  simp only [blend, Core.blend]
  rw [cohortEst_scale, ← portEst, portEst_scale]
  ring

omit [Fintype J] [Fintype T] in
/-- **Restating to the target year.** In the world with a common trend `g` and constant
coefficient of variation, the observation of cell `(j, t)` in year `year t` is
`Xⱼₜ = (1+g)^(year t) μⱼₜ`. Restated to year `n`, `(1+g)^(n − year t) Xⱼₜ` is the
observation of the model `M.detrend g hg n` with mean `(1+g)^n μ`: the thesis model. -/
theorem detrend_obs (year : T → ℤ) (j : J) (t : T) (ω : Ω) :
    (1 + g) ^ ((n : ℤ) - year t) * ((1 + g) ^ year t * N.obsVal μ j t ω)
      = (N.detrend g hg n).obsVal ((1 + g) ^ n * μ) j t ω := by
  have h1 : (1 + g) ≠ 0 := by linarith
  have h := N.obsVal_scale (pow_pos (by linarith : (0 : ℝ) < 1 + g) n) μ j t ω
  rw [show (N.detrend g hg n).obsVal ((1 + g) ^ n * μ) j t ω = (1 + g) ^ n * N.obsVal μ j t ω
    from h, ← mul_assoc, ← zpow_add₀ h1, sub_add_cancel, zpow_natCast]

/-- **Step 2: relativities are trend-free.** The fitted relativity `blendⱼ / μ̂` of the
restated data, with the model's own best `zⱼ`, is that of the untrended world for the
same outcome `ω`: it does not depend on the trend `g` or the target year `n`. The trend
moves only the overall level `(1+g)^n`. -/
theorem relativity_detrend (j : J) (ω : Ω) :
    (N.detrend g hg n).blend ((1 + g) ^ n * μ) j ((M.detrend g hg n).moments j).bestZ ω
        / (N.detrend g hg n).portEst ((1 + g) ^ n * μ) ω
      = N.blend μ j (M.moments j).bestZ ω / N.portEst μ ω := by
  have hc : (0 : ℝ) < (1 + g) ^ n := pow_pos (by linarith) n
  have hb := N.blend_scale hc μ j (M.moments j).bestZ ω
  have hp := N.portEst_scale hc μ ω
  rw [bestZ_detrend]
  rw [show (N.detrend g hg n).blend ((1 + g) ^ n * μ) j (M.moments j).bestZ ω
      = (1 + g) ^ n * N.blend μ j (M.moments j).bestZ ω from hb,
    show (N.detrend g hg n).portEst ((1 + g) ^ n * μ) ω = (1 + g) ^ n * N.portEst μ ω from hp,
    mul_div_mul_left _ _ hc.ne']

end Noise
end Unequal
end Credibility
