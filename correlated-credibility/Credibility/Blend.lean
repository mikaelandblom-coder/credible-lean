import Mathlib

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
  sorry

/-- Eq. (7) is optimal whenever `Var(μ̂ⱼ - μ̂) > 0`. -/
theorem bestZ_optimal (h : 0 < m.gap) (z : ℝ) : m.errVar m.bestZ ≤ m.errVar z := by
  sorry

/-- …and it is the unique optimum. -/
theorem bestZ_unique (h : 0 < m.gap) {z : ℝ} (hz : m.errVar z ≤ m.errVar m.bestZ) :
    z = m.bestZ := by
  sorry

end BlendMoments
end Credibility
