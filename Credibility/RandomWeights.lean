import Credibility.CoreMoments

/-!
# Random weights: where the bias of a fitted blend comes from (extension, distribution-free)

A fitted blend uses weights `d̂` estimated from the same data as the estimates `μ̂ᵢ` they weight.
For the moments of `Core.Estimates` (any random `μ̂ᵢ`, `μⱼ` with common mean `μ`), two exact facts,
with no distribution assumed (Finding 35):

* (a) If `d̂ᵀ1 = 1` in every draw, the bias for cohort `j` is
  `E(d̂ᵀμ̂ - μⱼ) = Σᵢ cov(d̂ᵢ, μ̂ᵢ)` (`Estimates.integral_randomLin_sub`). So a fit is biased exactly
  when its weights covary with the estimates they weight; fixed weights never are.
* (b) If a fit is exposure balanced, `Σⱼ uⱼ θ̂ⱼ = Σⱼ uⱼ μ̂ⱼ` in every draw (as Bühlmann–Straub
  is, `bs_balance`, and the balanced corrections `Estimates.correct`), its portfolio bias
  `E Σⱼ uⱼ(θ̂ⱼ - μⱼ)` is `0`, however `θ̂` is built (`Estimates.integral_portfolio_sub_of_balanced`).

How large the covariances in (a) are is a third-moment question (Finding 35 (c), not formalized):
`0` under symmetric noise (`PlugInSymmetric.lean`), negative under right skew.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core
namespace Estimates

variable {Ω : Type*} [MeasurableSpace Ω] {J : Type*} [Fintype J] {K L : Matrix J J ℝ} {μ : ℝ}
  {P : Measure Ω} (E : Estimates K L μ P)

/-- The estimate `d̂ᵀμ̂ = Σᵢ d̂ᵢ μ̂ᵢ` with random weights `d̂ : Ω → J → ℝ`. -/
def randomLin (dh : Ω → J → ℝ) (ω : Ω) : ℝ := ∑ i, dh ω i * E.est i ω

variable [IsProbabilityMeasure P]

/-- **Finding 35 (a): the bias of random weights.** If the weights `d̂` are square integrable
and sum to one in every draw, then `E(d̂ᵀμ̂ - μⱼ) = Σᵢ cov(d̂ᵢ, μ̂ᵢ)`, for every distribution
with the moments of `Core.Estimates`. -/
theorem integral_randomLin_sub (dh : Ω → J → ℝ) (hdh : ∀ i, MemLp (fun ω => dh ω i) 2 P)
    (hsum : ∀ ω, ∑ i, dh ω i = 1) (j : J) :
    P[fun ω => E.randomLin dh ω - E.level j ω] = ∑ i, cov[fun ω => dh ω i, E.est i; P] := by
  have hint : ∀ i, Integrable (fun ω => dh ω i * E.est i ω) P := fun i =>
    (hdh i).integrable_mul (E.est_memLp i)
  -- `Σᵢ E d̂ᵢ = E Σᵢ d̂ᵢ = 1`.
  have hone : ∑ i, P[fun ω => dh ω i] = 1 := by
    rw [← integral_finsetSum _ fun i _ => (hdh i).integrable (by norm_num)]
    simp [hsum]
  have hcov : ∀ i, cov[fun ω => dh ω i, E.est i; P]
      = P[fun ω => dh ω i * E.est i ω] - P[fun ω => dh ω i] * μ := fun i => by
    rw [covariance_eq_sub (hdh i) (E.est_memLp i), E.est_mean]; rfl
  unfold randomLin
  rw [integral_sub (integrable_finsetSum _ fun i _ => hint i)
      ((E.level_memLp j).integrable (by norm_num)),
    integral_finsetSum _ fun i _ => hint i, E.level_mean]
  simp only [hcov, sum_sub_distrib, ← sum_mul, hone, one_mul]

/-- **Finding 35 (b): an exposure-balanced fit is unbiased at the portfolio level.** If the
fitted levels `θ̂` satisfy `Σⱼ uⱼ θ̂ⱼ = Σⱼ uⱼ μ̂ⱼ` in every draw, then
`E Σⱼ uⱼ(θ̂ⱼ - μⱼ) = 0`, however `θ̂` is built from the data and for every distribution with the
moments of `Core.Estimates`. -/
theorem integral_portfolio_sub_of_balanced (u : J → ℝ) (θh : J → Ω → ℝ)
    (hbal : ∀ ω, ∑ j, u j * θh j ω = ∑ j, u j * E.est j ω) :
    P[fun ω => ∑ j, u j * (θh j ω - E.level j ω)] = 0 := by
  have hpt : (fun ω => ∑ j, u j * (θh j ω - E.level j ω))
      = fun ω => ∑ j, (u j * E.est j ω - u j * E.level j ω) := by
    funext ω
    rw [sum_sub_distrib, ← hbal ω, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hint : ∀ j, Integrable (fun ω => u j * E.est j ω - u j * E.level j ω) P := fun j =>
    (((E.est_memLp j).const_mul (u j)).integrable (by norm_num)).sub
      (((E.level_memLp j).const_mul (u j)).integrable (by norm_num))
  rw [hpt, integral_finsetSum _ fun j _ => hint j]
  refine sum_eq_zero fun j _ => ?_
  rw [integral_sub (((E.est_memLp j).const_mul (u j)).integrable (by norm_num))
      (((E.level_memLp j).const_mul (u j)).integrable (by norm_num)),
    integral_const_mul, integral_const_mul, E.est_mean, E.level_mean, sub_self]

omit [IsProbabilityMeasure P] in
/-- The balanced corrections `θ̂ⱼ = μ̂ⱼᵇ + cⱼD` with `Σⱼ uⱼcⱼ = 1` (G7) are exposure balanced. -/
theorem correct_balanced [DecidableEq J] (u z c : J → ℝ) (hc : ∑ j, u j * c j = 1) (ω : Ω) :
    ∑ j, u j * E.correct u z j (c j) ω = ∑ j, u j * E.est j ω := by
  have h := E.balanced_correct u z c hc ω
  simp only [mul_sub, sum_sub_distrib] at h
  linarith

end Estimates
end Core
end Credibility
