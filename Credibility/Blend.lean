import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The best credibility factor (thesis §2.1.1, eqs. (6)–(7))

All second moments are taken as given real numbers here. A later
probabilistic layer can show they are the actual variances and covariances
of the estimators.
-/

namespace Credibility

/-- The second moments that determine the error variance of the blend
`z μ̂ⱼ + (1 - z) μ̂` as an estimator of `μⱼ`. -/
structure BlendMoments where
  /-- `Var(μ̂ⱼ)` -/
  varCohort : ℝ
  /-- `Var(μ̂)` -/
  varPortfolio : ℝ
  /-- `Var(μⱼ)` -/
  varTarget : ℝ
  /-- `cov(μ̂ⱼ, μ̂)` -/
  covEst : ℝ
  /-- `cov(μ̂ⱼ, μⱼ)` -/
  covCohortTarget : ℝ
  /-- `cov(μ̂, μⱼ)` -/
  covPortfolioTarget : ℝ

namespace BlendMoments

variable (m : BlendMoments)

/-- `Var(z μ̂ⱼ + (1 - z) μ̂ - μⱼ)`, eq. (6). -/
def errVar (z : ℝ) : ℝ :=
  z ^ 2 * m.varCohort + (1 - z) ^ 2 * m.varPortfolio + m.varTarget
    + 2 * z * (1 - z) * m.covEst - 2 * z * m.covCohortTarget
    - 2 * (1 - z) * m.covPortfolioTarget

/-- `Var(μ̂ⱼ - μ̂)`, the curvature of `errVar`. -/
def gap : ℝ := m.varPortfolio - 2 * m.covEst + m.varCohort

/-- The general credibility factor, eq. (7). -/
noncomputable def bestZ : ℝ :=
  (m.varPortfolio - m.covEst + m.covCohortTarget - m.covPortfolioTarget) / m.gap

/-- `errVar` is a parabola with its vertex at `bestZ`. -/
theorem errVar_eq (h : m.gap ≠ 0) (z : ℝ) :
    m.errVar z = m.errVar m.bestZ + m.gap * (z - m.bestZ) ^ 2 := by
  have hb : m.gap * m.bestZ =
      m.varPortfolio - m.covEst + m.covCohortTarget - m.covPortfolioTarget := by
    unfold bestZ; field_simp
  unfold errVar
  unfold gap at hb ⊢
  linear_combination (2 * (z - m.bestZ)) * hb

/-- Eq. (7) is optimal whenever `Var(μ̂ⱼ - μ̂) > 0`. -/
theorem bestZ_optimal (h : 0 < m.gap) (z : ℝ) : m.errVar m.bestZ ≤ m.errVar z := by
  rw [m.errVar_eq h.ne' z]
  have := mul_nonneg h.le (sq_nonneg (z - m.bestZ))
  linarith

/-- …and it is the unique optimum. -/
theorem bestZ_unique (h : 0 < m.gap) {z : ℝ} (hz : m.errVar z ≤ m.errVar m.bestZ) :
    z = m.bestZ := by
  rw [m.errVar_eq h.ne' z] at hz
  have hsq : (z - m.bestZ) ^ 2 = 0 := by
    have h0 : m.gap * (z - m.bestZ) ^ 2 ≤ 0 := by linarith
    have := mul_nonneg h.le (sq_nonneg (z - m.bestZ))
    have h1 : m.gap * (z - m.bestZ) ^ 2 = 0 := le_antisymm h0 this
    exact (mul_eq_zero.mp h1).resolve_left h.ne'
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-! ### Clipping `z` to `[0, 1]` (thesis eq. (34), PLAN G3) -/

/-- `z` clipped to `[0, 1]`, as in eq. (34). -/
def clipZ (z : ℝ) : ℝ := max 0 (min z 1)

lemma clipZ_mem (z : ℝ) : 0 ≤ clipZ z ∧ clipZ z ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clipZ_of_mem {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : clipZ z = z := by
  simp [clipZ, min_eq_left h1, max_eq_right h0]

/-- Clipping moves `z` towards every point of `[0, 1]`. -/
lemma sq_clipZ_sub_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) (z : ℝ) :
    (clipZ z - b) ^ 2 ≤ (z - b) ^ 2 := by
  unfold clipZ
  rcases le_total z 1 with hz | hz
  · rw [min_eq_left hz]
    rcases le_total 0 z with hz0 | hz0
    · rw [max_eq_right hz0]
    · rw [max_eq_left hz0]; nlinarith
  · rw [min_eq_right hz, max_eq_right zero_le_one]; nlinarith

/-- PLAN G3: if the best factor lies in `[0, 1]`, clipping any `z` to `[0, 1]` never increases
the error variance. -/
theorem errVar_clipZ_le (h : 0 < m.gap) (h0 : 0 ≤ m.bestZ) (h1 : m.bestZ ≤ 1) (z : ℝ) :
    m.errVar (clipZ z) ≤ m.errVar z := by
  rw [m.errVar_eq h.ne' z, m.errVar_eq h.ne' (clipZ z)]
  have := mul_le_mul_of_nonneg_left (sq_clipZ_sub_le h0 h1 z) h.le
  linarith

/-- The price of clipping the best factor: `Var(μ̂ⱼ - μ̂)` times its squared distance to
`[0, 1]`. -/
theorem errVar_clipZ_bestZ (h : m.gap ≠ 0) :
    m.errVar (clipZ m.bestZ) = m.errVar m.bestZ + m.gap * (clipZ m.bestZ - m.bestZ) ^ 2 :=
  m.errVar_eq h _

/-- PLAN G3: clipping is harmless for every `z` exactly when the best factor lies in `[0, 1]`.
Otherwise it already hurts at `z = bestZ` (Finding 36). -/
theorem errVar_clipZ_le_iff (h : 0 < m.gap) :
    (∀ z, m.errVar (clipZ z) ≤ m.errVar z) ↔ 0 ≤ m.bestZ ∧ m.bestZ ≤ 1 := by
  refine ⟨fun hc => ?_, fun hb z => m.errVar_clipZ_le h hb.1 hb.2 z⟩
  have e := m.bestZ_unique h (hc m.bestZ)
  rw [← e]
  exact clipZ_mem _

/-! ### Shifting all moments of the blend by a constant -/

/-- Add `c` to all six second moments of the blend: what a common component of
variance `c` in the cohort estimates, the portfolio estimate and the target does. -/
def shift (m : BlendMoments) (c : ℝ) : BlendMoments where
  varCohort := m.varCohort + c
  varPortfolio := m.varPortfolio + c
  varTarget := m.varTarget + c
  covEst := m.covEst + c
  covCohortTarget := m.covCohortTarget + c
  covPortfolioTarget := m.covPortfolioTarget + c

/-- A common component cancels in the error of the blend:
`z + (1 - z) - 1 = 0`, so the error variance is unchanged. -/
theorem errVar_shift (m : BlendMoments) (c z : ℝ) : (m.shift c).errVar z = m.errVar z := by
  simp only [errVar, shift]; ring

/-- …and so is `Var(μ̂ⱼ - μ̂)`. -/
theorem gap_shift (m : BlendMoments) (c : ℝ) : (m.shift c).gap = m.gap := by
  simp only [gap, shift]; ring

/-- …and so is the best credibility factor. -/
theorem bestZ_shift (m : BlendMoments) (c : ℝ) : (m.shift c).bestZ = m.bestZ := by
  rw [bestZ, gap_shift, bestZ]; simp only [shift]; ring_nf

/-! ### Scaling all moments by a constant -/

/-- Multiply all six second moments of the blend by `c`: what measuring every
quantity in a unit `√c` times smaller does (e.g. restating the data to a later year). -/
def smul (m : BlendMoments) (c : ℝ) : BlendMoments where
  varCohort := c * m.varCohort
  varPortfolio := c * m.varPortfolio
  varTarget := c * m.varTarget
  covEst := c * m.covEst
  covCohortTarget := c * m.covCohortTarget
  covPortfolioTarget := c * m.covPortfolioTarget

/-- The error variance scales by `c`. -/
theorem errVar_smul (m : BlendMoments) (c z : ℝ) : (m.smul c).errVar z = c * m.errVar z := by
  simp only [errVar, smul]; ring

/-- `Var(μ̂ⱼ - μ̂)` scales by `c`. -/
theorem gap_smul (m : BlendMoments) (c : ℝ) : (m.smul c).gap = c * m.gap := by
  simp only [gap, smul]; ring

/-- The best credibility factor is unit-free: scaling all moments by `c ≠ 0` leaves it unchanged. -/
theorem bestZ_smul (m : BlendMoments) {c : ℝ} (hc : c ≠ 0) : (m.smul c).bestZ = m.bestZ := by
  rw [bestZ, gap_smul, bestZ]
  simp only [smul]
  rw [show c * m.varPortfolio - c * m.covEst + c * m.covCohortTarget - c * m.covPortfolioTarget
      = c * (m.varPortfolio - m.covEst + m.covCohortTarget - m.covPortfolioTarget) by ring,
    mul_div_mul_left _ _ hc]

end BlendMoments
end Credibility
