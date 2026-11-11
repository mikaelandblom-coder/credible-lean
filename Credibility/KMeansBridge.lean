import Credibility.KMeans

/-!
# The k-means bridge: exposure-weighted pooling is weighted k-means

Units `i` have fixed true levels `x i` and unbiased, uncorrelated estimates
with variances `1 / w i` (`w i` is the exposure). Labels `c : ι → κ` put them
into at most `|κ|` cohorts, and cohort `a` pools its units by inverse
variance: the pooled estimate has mean `x̄ₐ`, the `w`-weighted mean level
(`cohortMean`), and variance `1 / Wₐ` (`Wₐ = cohortWeight`). So a unit `i`
of cohort `a` predicted by the pooled estimate has MSE `(x̄ₐ - xᵢ)² + 1/Wₐ`.

* `pool_mse_eq_kmeansCost`: the exposure-weighted total MSE `poolLoss` is the
  weighted k-means cost of the levels at the cohort means plus the number of
  nonempty cohorts.
* `pool_optimal_contiguous`: hence an MSE-optimal labelling has interval
  cohorts, by `kmeans_contiguous` on the labels actually used.

Not in the thesis; `notes/kmeans-bridge.md`, Finding 14. Purely algebraic:
the levels are fixed numbers and the two moments of the pooled estimate are
taken as given.
-/

open Finset

namespace Credibility

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- Total weight (exposure) `Wₐ = ∑_{c i = a} wᵢ` of cohort `a`. -/
def cohortWeight (w : ι → ℝ) (c : ι → κ) (a : κ) : ℝ :=
  ∑ i with c i = a, w i

/-- The `w`-weighted mean level `x̄ₐ = ∑_{c i = a} wᵢ xᵢ / Wₐ` of cohort `a`. -/
noncomputable def cohortMean (w x : ι → ℝ) (c : ι → κ) (a : κ) : ℝ :=
  (∑ i with c i = a, w i * x i) / cohortWeight w c a

/-- Exposure-weighted total MSE of pooling: `∑ᵢ wᵢ E(X̄_{c i} - xᵢ)²`, with
`E X̄ₐ = x̄ₐ` and `Var X̄ₐ = 1/Wₐ`, i.e. `∑ᵢ wᵢ ((x̄_{c i} - xᵢ)² + 1/W_{c i})`. -/
noncomputable def poolLoss (w x : ι → ℝ) (c : ι → κ) : ℝ :=
  ∑ i, w i * ((cohortMean w x c (c i) - x i) ^ 2 + 1 / cohortWeight w c (c i))

/-- A used cohort has positive weight. -/
theorem cohortWeight_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) (i : ι) :
    0 < cohortWeight w c (c i) :=
  sum_pos (fun j _ => hw j) ⟨i, by simp⟩

/-- Each nonempty cohort contributes `∑_{i ∈ a} wᵢ / Wₐ = 1`. -/
theorem sum_div_cohortWeight {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) :
    ∑ i, w i / cohortWeight w c (c i) = (univ.image c).card := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image c) (g := c)
    (fun i _ => mem_image_of_mem c (mem_univ i)), card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  have hW := (cohortWeight_pos hw c i).ne'
  rw [sum_congr rfl (g := fun j => w j / cohortWeight w c (c i))
    (fun j hj => by rw [(mem_filter.mp hj).2]), ← sum_div]
  simpa [cohortWeight] using div_self hW

/-- Deviations from the cohort means are `w`-orthogonal to anything constant
on cohorts. -/
theorem sum_mul_sub_cohortMean {w : ι → ℝ} (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    (c : ι → κ) (g : κ → ℝ) :
    ∑ i, w i * (x i - cohortMean w x c (c i)) * g (c i) = 0 := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image c) (g := c)
    (fun i _ => mem_image_of_mem c (mem_univ i))]
  refine sum_eq_zero fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  have hW := (cohortWeight_pos hw c i).ne'
  rw [sum_congr rfl (g := fun j => (w j * x j - w j * cohortMean w x c (c i)) * g (c i))
    (fun j hj => by rw [(mem_filter.mp hj).2]; ring), ← sum_mul, sum_sub_distrib,
    ← sum_mul]
  have : (∑ j with c j = c i, w j) * cohortMean w x c (c i)
      = ∑ j with c j = c i, w j * x j := by
    unfold cohortMean
    rw [← cohortWeight]
    field_simp
  rw [this, sub_self, zero_mul]

/-- **The cohort means are the best centers**: for fixed labels, the weighted
k-means cost is smallest at the `w`-weighted cohort means. -/
theorem kmeansCost_cohortMean_le {w : ι → ℝ} (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    (c : ι → κ) (μ : κ → ℝ) :
    kmeansCost w x c (cohortMean w x c) ≤ kmeansCost w x c μ := by
  have h := sum_mul_sub_cohortMean hw x c (fun a => cohortMean w x c a - μ a)
  have hsplit : kmeansCost w x c μ = kmeansCost w x c (cohortMean w x c)
      + 2 * ∑ i, w i * (x i - cohortMean w x c (c i)) * (cohortMean w x c (c i) - μ (c i))
      + ∑ i, w i * (cohortMean w x c (c i) - μ (c i)) ^ 2 := by
    unfold kmeansCost
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hsplit, h]
  have : 0 ≤ ∑ i, w i * (cohortMean w x c (c i) - μ (c i)) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _)
  linarith

/-- **Pooling is weighted k-means** (`notes/kmeans-bridge.md`). For positive
exposures, the exposure-weighted total MSE of pooling cohorts by inverse
variance is the weighted k-means cost of the levels at the cohort means plus
the number of nonempty cohorts:
`∑ᵢ wᵢ ((x̄_{c i} - xᵢ)² + 1/W_{c i}) = ∑ᵢ wᵢ (xᵢ - x̄_{c i})² + #cohorts`. -/
theorem pool_mse_eq_kmeansCost {w : ι → ℝ} (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    (c : ι → κ) :
    poolLoss w x c = kmeansCost w x c (cohortMean w x c) + (univ.image c).card := by
  rw [← sum_div_cohortWeight hw c, poolLoss, kmeansCost, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- Relabelling cohorts injectively changes neither weights … -/
theorem cohortWeight_comp {κ' : Type*} [DecidableEq κ'] (w : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) (a : κ) :
    cohortWeight w (f ∘ c) (f a) = cohortWeight w c a := by
  simp [cohortWeight, hf.eq_iff]

/-- … nor means … -/
theorem cohortMean_comp {κ' : Type*} [DecidableEq κ'] (w x : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) (a : κ) :
    cohortMean w x (f ∘ c) (f a) = cohortMean w x c a := by
  simp [cohortMean, cohortWeight, hf.eq_iff]

/-- … nor the pooling loss. -/
theorem poolLoss_comp {κ' : Type*} [DecidableEq κ'] (w x : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) :
    poolLoss w x (f ∘ c) = poolLoss w x c := by
  unfold poolLoss
  refine sum_congr rfl fun i _ => ?_
  rw [Function.comp_apply, cohortMean_comp w x c hf, cohortWeight_comp w c hf]

/-- **Optimal pooled cohorts are intervals** (`notes/kmeans-bridge.md`).
For positive exposures, if the labelling `c` minimises the exposure-weighted
total MSE of pooling among all labellings into the labels `κ` (at most `|κ|`
cohorts), then a unit whose level lies strictly between two units of the same
cohort is in that cohort. -/
theorem pool_optimal_contiguous [DecidableEq ι] {w x : ι → ℝ} {c : ι → κ} (hw : ∀ i, 0 < w i)
    (hopt : ∀ c' : ι → κ, poolLoss w x c ≤ poolLoss w x c')
    {i j l : ι} (hij : x i < x j) (hjl : x j < x l) (hil : c i = c l) :
    c j = c i := by
  -- restrict the labels to the `m` used ones
  let S := univ.image c
  let cS : ι → S := fun m => ⟨c m, mem_image_of_mem c (mem_univ m)⟩
  have hval : (Subtype.val ∘ cS) = c := rfl
  have hm : (univ.image cS).card = S.card := by
    rw [← card_image_of_injective _ Subtype.val_injective, image_image, hval]
  have hopt' : ∀ (c' : ι → S) (μ' : S → ℝ),
      kmeansCost w x cS (cohortMean w x cS) ≤ kmeansCost w x c' μ' := by
    intro c' μ'
    have h1 := kmeansCost_cohortMean_le hw x c' μ'
    have h2 := pool_mse_eq_kmeansCost hw x c'
    have h3 := pool_mse_eq_kmeansCost hw x cS
    have h4 : poolLoss w x cS ≤ poolLoss w x c' := by
      rw [← poolLoss_comp w x cS Subtype.val_injective,
        ← poolLoss_comp w x c' Subtype.val_injective, hval]
      exact hopt _
    have h5 : ((univ.image c').card : ℝ) ≤ (univ.image cS).card := by
      rw [hm]
      exact_mod_cast (card_le_univ _).trans (Fintype.card_coe S).le
    linarith
  have := kmeans_contiguous hw hopt' (c := cS) hij hjl (Subtype.ext hil)
  exact congrArg Subtype.val this

end Credibility
