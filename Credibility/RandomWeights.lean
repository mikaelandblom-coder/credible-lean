import Credibility.CoreMoments
import Credibility.Cumulants

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

How large the covariances in (a) are is a third-moment question (Finding 35 (c), first order):
`0` under symmetric noise (`PlugInSymmetric.lean`), negative under right skew. Its ingredient, the
exact `cov(σ̂², μ̂)` under skew, is `Cumulants.covariance_resVar_mean`.
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

/-- **Weights driven by fitted variances.** If the weights are affine in random statistics,
`d̂ᵢ = aᵢ + bᵢσ̂ᵢ²` (a fitted variance, say), with `Σᵢ d̂ᵢ = 1` in every draw, the bias of
Finding 35 (a) is `E(d̂ᵀμ̂ - μⱼ) = Σᵢ bᵢ cov(σ̂ᵢ², μ̂ᵢ)`. -/
theorem integral_randomLin_affine_sub (σh : J → Ω → ℝ) (a b : J → ℝ)
    (hσ : ∀ i, MemLp (σh i) 2 P) (hsum : ∀ ω, ∑ i, (a i + b i * σh i ω) = 1) (j : J) :
    P[fun ω => E.randomLin (fun ω i => a i + b i * σh i ω) ω - E.level j ω]
      = ∑ i, b i * cov[σh i, E.est i; P] := by
  have hdh : ∀ i, MemLp (fun ω => a i + b i * σh i ω) 2 P := fun i =>
    (memLp_const (a i)).add ((hσ i).const_mul (b i))
  rw [E.integral_randomLin_sub (fun ω i => a i + b i * σh i ω) hdh hsum]
  refine sum_congr rfl fun i _ => ?_
  rw [covariance_const_add_left (((hσ i).const_mul _).integrable one_le_two),
    covariance_const_mul_left]

/-- **Finding 35 (c), the bias of variance-driven weights, exactly.** Let each cohort's estimate be
a weighted mean `μ̂ᵢ = Σₛ wᵢₛXᵢₛ` (`Σₛ wᵢₛ = 1`) of cells `Xᵢₜ = Lᵢ + eᵢₜ` as in
`Cumulants.covariance_resVar_mean` (centred noise in `L³`, third moments `kᵢₜ` on the diagonal
only, squares uncorrelated with the level), and `σ̂ᵢ² = Σₜ cᵢₜ rᵢₜ²` from the residuals
`rᵢₜ = Xᵢₜ - μ̂ᵢ`. Then weights `d̂ᵢ = aᵢ + bᵢσ̂ᵢ²` summing to one have bias
`E(d̂ᵀμ̂ - μⱼ) = Σᵢ bᵢ Σₛ wᵢₛ kᵢₛ Σₜ cᵢₜ(δₜₛ - wᵢₛ)²`: zero under symmetric noise, of the sign of
`bᵢ` under right skew. -/
theorem integral_randomLin_resVar_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : J → ι → Ω → ℝ) (Lv : J → Ω → ℝ) (k w c : J → ι → ℝ) (a b : J → ℝ)
    (hL : ∀ i t, MemLp (e i t) 3 P) (hLv : ∀ i, MemLp (Lv i) 3 P)
    (h0 : ∀ i t, ∫ ω, e i t ω ∂P = 0)
    (h3 : ∀ i t u v, ∫ ω, e i t ω * e i u ω * e i v ω ∂P = if t = u ∧ u = v then k i t else 0)
    (hlev : ∀ i t u, ∫ ω, e i t ω * e i u ω * (Lv i ω - ∫ ω', Lv i ω' ∂P) ∂P = 0)
    (hw : ∀ i, ∑ t, w i t = 1)
    (hest : ∀ i, E.est i = fun ω => ∑ s, w i s * (Lv i ω + e i s ω))
    (σh : J → Ω → ℝ)
    (hσh : ∀ i, σh i = fun ω => ∑ t, c i t * (Lv i ω + e i t ω - ∑ s, w i s * (Lv i ω + e i s ω)) ^ 2)
    (hσ : ∀ i, MemLp (σh i) 2 P) (hsum : ∀ ω, ∑ i, (a i + b i * σh i ω) = 1) (j : J) :
    P[fun ω => E.randomLin (fun ω i => a i + b i * σh i ω) ω - E.level j ω]
      = ∑ i, b i * ∑ s, w i s * k i s * ∑ t, c i t * ((if t = s then 1 else 0) - w i s) ^ 2 := by
  rw [E.integral_randomLin_affine_sub σh a b hσ hsum j]
  refine sum_congr rfl fun i _ => ?_
  rw [hσh i, hest i]
  exact congrArg (b i * ·) (Cumulants.covariance_resVar_mean (e i) (Lv i) (hL i) (hLv i) (h0 i)
    (k i) (h3 i) (hlev i) (w i) (c i) (hw i))

/-- **The cross-fitted rate's bias** (S63, `studies/LOG.md`). Each year `s` gives
estimates `Xᵢₛ` (`E s`, any covariances `K s`) of the same levels `μᵢ`; the weights `d̂⁽ˢ⁾` for
year `s` sum to one and are independent of year `s`'s noise `Xᵢₛ - μᵢ` (fitted without year `s`).
With year weights `πₛ` common to all regions and summing to one, the cross-fitted rate
`Σₛ πₛ d̂⁽ˢ⁾ᵀXₛ` has bias

  `E(Σₛ πₛ d̂⁽ˢ⁾ᵀXₛ - μⱼ) = Σₛ πₛ Σᵢ cov(d̂ᵢ⁽ˢ⁾, μᵢ)`,

for every distribution with these moments: only the levels enter, so the bias is `0` for fixed
levels. A corollary of Finding 35 (a) (`integral_randomLin_sub`), year by year. With
region-specific year weights `aᵢₛ` the identity is not exact: `Σₛ Σᵢ aᵢₛd̂ᵢ⁽ˢ⁾ ≠ 1` in general,
so the rate is not translation equivariant and `μ` itself enters the bias. -/
theorem integral_crossFit_sub {S : Type*} [Fintype S] {K : S → Matrix J J ℝ}
    (E : ∀ s, Estimates (K s) L μ P) (lev : J → Ω → ℝ) (hlev : ∀ s, (E s).level = lev)
    (π : S → ℝ) (hπ : ∑ s, π s = 1) (dh : S → Ω → J → ℝ)
    (hdh : ∀ s i, MemLp (fun ω => dh s ω i) 2 P) (hsum : ∀ s ω, ∑ i, dh s ω i = 1)
    (hind : ∀ s i, IndepFun (fun ω => dh s ω i) (fun ω => (E s).est i ω - lev i ω) P) (j : J) :
    P[fun ω => ∑ s, π s * (E s).randomLin (dh s) ω - lev j ω]
      = ∑ s, π s * ∑ i, cov[fun ω => dh s ω i, lev i; P] := by
  have hint : ∀ s, Integrable (fun ω => (E s).randomLin (dh s) ω - lev j ω) P := by
    intro s
    have hl : MemLp (lev j) 2 P := by rw [← hlev s]; exact (E s).level_memLp j
    exact (integrable_finsetSum _ fun i _ => (hdh s i).integrable_mul ((E s).est_memLp i)).sub
      (hl.integrable (by norm_num))
  have hpt : (fun ω => ∑ s, π s * (E s).randomLin (dh s) ω - lev j ω)
      = fun ω => ∑ s, π s * ((E s).randomLin (dh s) ω - lev j ω) := by
    funext ω
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ, one_mul]
  rw [hpt, integral_finsetSum _ fun s _ => (hint s).const_mul (π s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  have h := (E s).integral_randomLin_sub (dh s) (hdh s) (hsum s) j
  rw [hlev s] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : MemLp (lev i) 2 P := by rw [← hlev s]; exact (E s).level_memLp i
  have hN : MemLp (fun ω => (E s).est i ω - lev i ω) 2 P := ((E s).est_memLp i).sub hL
  have hsplit : (E s).est i = lev i + fun ω => (E s).est i ω - lev i ω := by
    funext ω; simp
  rw [hsplit, covariance_add_right (hdh s i) hL hN,
    (hind s i).covariance_eq_zero (hdh s i) hN, add_zero]

/-- **Cross-fitting with weights blind to the levels is unbiased.** In the setting of
`integral_crossFit_sub`, if moreover each year's weights are uncorrelated with the levels
(e.g. built from within-region residuals only, `residual_eq_noise`, with noise independent of the
levels), the cross-fitted rate is unbiased: `E(Σₛ πₛ d̂⁽ˢ⁾ᵀμ̂⁽ˢ⁾ - μⱼ) = 0`, for every
distribution. Only a fit whose weights see the levels (`τ̂²`, from the between-region spread)
keeps a bias. -/
theorem integral_crossFit_sub_eq_zero {S : Type*} [Fintype S] {K : S → Matrix J J ℝ}
    (E : ∀ s, Estimates (K s) L μ P) (lev : J → Ω → ℝ) (hlev : ∀ s, (E s).level = lev)
    (π : S → ℝ) (hπ : ∑ s, π s = 1) (dh : S → Ω → J → ℝ)
    (hdh : ∀ s i, MemLp (fun ω => dh s ω i) 2 P) (hsum : ∀ s ω, ∑ i, dh s ω i = 1)
    (hind : ∀ s i, IndepFun (fun ω => dh s ω i) (fun ω => (E s).est i ω - lev i ω) P)
    (hblind : ∀ s i, cov[fun ω => dh s ω i, lev i; P] = 0) (j : J) :
    P[fun ω => ∑ s, π s * (E s).randomLin (dh s) ω - lev j ω] = 0 := by
  rw [integral_crossFit_sub E lev hlev π hπ dh hdh hsum hind j]
  simp [hblind]

omit [Fintype J] [IsProbabilityMeasure P] in
/-- **Residuals do not see the level**: for cells `Lᵢ + eᵢₜ` and year weights summing to one,
`(Lᵢ + eᵢₜ) - Σₛ wᵢₛ(Lᵢ + eᵢₛ) = eᵢₜ - Σₛ wᵢₛeᵢₛ`. So `ρ̂`, `σ̂²` and any weights built from
within-region residuals are functions of the noise alone. -/
theorem residual_eq_noise {ι : Type*} [Fintype ι] (Lv : ℝ) (e w : ι → ℝ) (hw : ∑ s, w s = 1)
    (t : ι) : (Lv + e t) - ∑ s, w s * (Lv + e s) = e t - ∑ s, w s * e s := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hw, one_mul]
  ring

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
