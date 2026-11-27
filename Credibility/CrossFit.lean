import Credibility.PlugInMix

/-!
# Choosing cohorts on held-out years: the winner's curse and cross-fitting (distribution-free)

Not in the thesis: an extension for the paper's first open direction. A tariff groups its cohorts
(or merges a pair) from the same estimates it then blends. A risk estimate for fixed groups does
not see that the groups were chosen, so the chosen partition looks better than it is: the
winner's curse (S61: cutting the sorted estimates where SURE is smallest lost to one group in
every simulated world).

Write `p̂ⱼ` for any prediction of cohort `j`'s level `μⱼ` (any rule, the choice of the partition
included), `errⱼ = p̂ⱼ - μⱼ` for its error and `xⱼ = μⱼ + εⱼ` for an observation of the cohort with
noise `εⱼ` of mean `0`. For weights `wⱼ` the score `Σⱼ wⱼ(p̂ⱼ - xⱼ)²` has mean, for every
distribution,

`E Σⱼ wⱼ(p̂ⱼ - xⱼ)² = E Σⱼ wⱼ errⱼ² + Σⱼ wⱼ Var εⱼ - 2 Σⱼ wⱼ E[errⱼεⱼ]`  (`integral_score`):

the true weighted MSE, plus the noise's known price, minus the optimism `2Σⱼ wⱼ E[errⱼεⱼ]`
(Efron's covariance penalty; Ye's generalized degrees of freedom). In sample, where `p̂` is built
from `x`, the optimism is what the selection inflates. On a held-out year (`p̂` fitted and chosen
on the other years, `εⱼ` independent of `errⱼ`) it is `0` (`integral_heldOutScore`): the held-out
score minus the price is unbiased for the true MSE of the rule *as chosen*, whatever the choice
and the noise distribution. Two rules scored on the same held-out year differ in mean exactly by
their difference in MSE (`integral_heldOutScore_sub`), the price cancels; averaging the folds of
a cross-fit keeps this (`integral_crossFitScore`).

Two limits, both standard for cross-validation: the score is for the rule fitted on the training
years (fewer years than the final fit), and choosing *among* rules by their held-out scores puts
a second, smaller winner's curse on the winning score: the mean of the smaller of two scores is at
most the smaller mean (`integral_min_score_le`), so the chosen rule's score needs a further fold
(nested cross-fitting) to be honest.
-/

open MeasureTheory ProbabilityTheory

namespace Credibility
namespace CrossFit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {J : Type*} [Fintype J]

/-- The score `Σⱼ wⱼ(p̂ⱼ - xⱼ)²` of predictions `p̂` against observations `x`. -/
def score (w : J → ℝ) (ph x : J → Ω → ℝ) (ω : Ω) : ℝ := ∑ j, w j * (ph j ω - x j ω) ^ 2

/-- The weighted loss `Σⱼ wⱼ(p̂ⱼ - μⱼ)²` against the true levels. -/
def loss (w : J → ℝ) (ph lev : J → Ω → ℝ) (ω : Ω) : ℝ := ∑ j, w j * (ph j ω - lev j ω) ^ 2

/-- **The mean of a score** (Efron's covariance penalty): with `xⱼ = μⱼ + εⱼ`, `E εⱼ = 0`,

`E Σⱼ wⱼ(p̂ⱼ - xⱼ)² = E Σⱼ wⱼ(p̂ⱼ - μⱼ)² + Σⱼ wⱼ Var εⱼ - 2 Σⱼ wⱼ E[(p̂ⱼ - μⱼ)εⱼ]`,

for every distribution with second moments. -/
theorem integral_score (w : J → ℝ) {ph lev ε : J → Ω → ℝ} (hph : ∀ j, MemLp (ph j) 2 P)
    (hlev : ∀ j, MemLp (lev j) 2 P) (hε : ∀ j, MemLp (ε j) 2 P) (hm : ∀ j, P[ε j] = 0) :
    P[score w ph (fun j ω => lev j ω + ε j ω)]
      = P[loss w ph lev] + ∑ j, w j * Var[ε j; P]
        - 2 * ∑ j, w j * P[fun ω => (ph j ω - lev j ω) * ε j ω] := by
  have he : ∀ j, MemLp (fun ω => ph j ω - lev j ω) 2 P := fun j => (hph j).sub (hlev j)
  have hpt : score w ph (fun j ω => lev j ω + ε j ω)
      = fun ω => ∑ j, (w j * (ph j ω - lev j ω) ^ 2 + w j * ε j ω ^ 2
          - 2 * (w j * ((ph j ω - lev j ω) * ε j ω))) := by
    funext ω
    exact Finset.sum_congr rfl fun j _ => by ring
  have iA : ∀ j, Integrable (fun ω => w j * (ph j ω - lev j ω) ^ 2) P := fun j =>
    (he j).integrable_sq.const_mul _
  have iB : ∀ j, Integrable (fun ω => w j * ε j ω ^ 2) P := fun j =>
    (hε j).integrable_sq.const_mul _
  have iC : ∀ j, Integrable (fun ω => 2 * (w j * ((ph j ω - lev j ω) * ε j ω))) P := fun j =>
    (((he j).integrable_mul (hε j)).const_mul _).const_mul _
  unfold loss
  rw [hpt, integral_finsetSum _ fun j _ => by exact ((iA j).add (iB j)).sub (iC j),
    integral_finsetSum _ fun j _ => iA j, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := integral_sub ((iA j).add (iB j)) (iC j)
  have e2 := integral_add (iA j) (iB j)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    variance_of_integral_eq_zero ((hε j).aestronglyMeasurable.aemeasurable) (hm j)]

/-- **The held-out score is unbiased for the chosen rule's MSE, up to the known price.** If each
cohort's held-out noise `εⱼ` (mean `0`) is independent of the prediction's error `p̂ⱼ - μⱼ` (the
rule, partition and all, fitted and chosen on other years), then

`E Σⱼ wⱼ(p̂ⱼ - xⱼ)² = E Σⱼ wⱼ(p̂ⱼ - μⱼ)² + Σⱼ wⱼ Var εⱼ`,

for every distribution: the selection cannot inflate it. -/
theorem integral_heldOutScore (w : J → ℝ) {ph lev ε : J → Ω → ℝ} (hph : ∀ j, MemLp (ph j) 2 P)
    (hlev : ∀ j, MemLp (lev j) 2 P) (hε : ∀ j, MemLp (ε j) 2 P) (hm : ∀ j, P[ε j] = 0)
    (hind : ∀ j, IndepFun (fun ω => ph j ω - lev j ω) (ε j) P) :
    P[score w ph (fun j ω => lev j ω + ε j ω)] = P[loss w ph lev] + ∑ j, w j * Var[ε j; P] := by
  rw [integral_score w hph hlev hε hm]
  have h0 : ∀ j, P[fun ω => (ph j ω - lev j ω) * ε j ω] = 0 := fun j =>
    integral_mul_eq_zero_of_indepFun (hind j) ((hph j).sub (hlev j)).aestronglyMeasurable
      (hε j).aestronglyMeasurable (hm j)
  simp [h0]

/-- **Comparing two rules on the same held-out year**: the difference of the mean scores is the
difference of the true MSEs; the price cancels. -/
theorem integral_heldOutScore_sub (w : J → ℝ) {ph ph' lev ε : J → Ω → ℝ}
    (hph : ∀ j, MemLp (ph j) 2 P) (hph' : ∀ j, MemLp (ph' j) 2 P)
    (hlev : ∀ j, MemLp (lev j) 2 P) (hε : ∀ j, MemLp (ε j) 2 P) (hm : ∀ j, P[ε j] = 0)
    (hind : ∀ j, IndepFun (fun ω => ph j ω - lev j ω) (ε j) P)
    (hind' : ∀ j, IndepFun (fun ω => ph' j ω - lev j ω) (ε j) P) :
    P[score w ph (fun j ω => lev j ω + ε j ω)] - P[score w ph' (fun j ω => lev j ω + ε j ω)]
      = P[loss w ph lev] - P[loss w ph' lev] := by
  rw [integral_heldOutScore w hph hlev hε hm hind, integral_heldOutScore w hph' hlev hε hm hind']
  ring

/-- **Cross-fitting**: fold `s` predicts with `p̂⁽ˢ⁾` (fitted and chosen without fold `s`) and is
scored on fold `s`'s observations `μ + ε⁽ˢ⁾`. With fold weights `πₛ`, the mean of the averaged score
is the averaged true MSE of the fold rules plus the averaged price, for every distribution. -/
theorem integral_crossFitScore {S : Type*} [Fintype S] (π : S → ℝ) (w : J → ℝ)
    {ph ε : S → J → Ω → ℝ} {lev : J → Ω → ℝ} (hph : ∀ s j, MemLp (ph s j) 2 P)
    (hlev : ∀ j, MemLp (lev j) 2 P) (hε : ∀ s j, MemLp (ε s j) 2 P)
    (hm : ∀ s j, P[ε s j] = 0)
    (hind : ∀ s j, IndepFun (fun ω => ph s j ω - lev j ω) (ε s j) P) :
    P[fun ω => ∑ s, π s * score w (ph s) (fun j ω => lev j ω + ε s j ω) ω]
      = ∑ s, π s * P[loss w (ph s) lev] + ∑ s, π s * ∑ j, w j * Var[ε s j; P] := by
  have hi : ∀ s, Integrable (score w (ph s) (fun j ω => lev j ω + ε s j ω)) P := fun s =>
    integrable_finsetSum _ fun j _ =>
      (((hph s j).sub ((hlev j).add (hε s j))).integrable_sq).const_mul (w j)
  rw [integral_finsetSum _ fun s _ => (hi s).const_mul (π s), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, integral_heldOutScore w (hph s) hlev (hε s) (hm s) (hind s), mul_add]

/-- **The second winner's curse**: choosing the better of two rules by their scores, the mean of
the winning score is at most the smaller of the two mean scores,
`E min(score, score') ≤ min(E score, E score')`, for every distribution. So the winning held-out
score is optimistic for the chosen rule; an honest score for it needs a further fold. -/
theorem integral_min_score_le (w : J → ℝ) {ph ph' x : J → Ω → ℝ}
    (hi : Integrable (score w ph x) P) (hi' : Integrable (score w ph' x) P) :
    P[fun ω => min (score w ph x ω) (score w ph' x ω)]
      ≤ min (P[score w ph x]) (P[score w ph' x]) :=
  le_min (integral_mono (hi.inf hi') hi fun _ => min_le_left _ _)
    (integral_mono (hi.inf hi') hi' fun _ => min_le_right _ _)

end CrossFit
end Credibility
