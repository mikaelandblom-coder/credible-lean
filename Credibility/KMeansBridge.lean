import Credibility.KMeans
import Credibility.GroupWeights
import Credibility.Weights
import Credibility.Blend

/-!
# The k-means bridge: exposure-weighted pooling is weighted k-means

Units `i` have fixed true levels `x i` and unbiased, uncorrelated estimates
with variances `1 / w i` (`w i` is the exposure). Labels `c : ι → κ` put them
into at most `|κ|` cohorts, and cohort `a` pools its units by inverse
variance: the pooled estimate has mean `x̄ₐ`, the `w`-weighted mean level
(`cohortMean`), and variance `1 / Wₐ` (`Wₐ = groupWeight c w a`, the total weight of `GroupWeights.lean`). So a unit `i`
of cohort `a` predicted by the pooled estimate has MSE `(x̄ₐ - xᵢ)² + 1/Wₐ`.

* `pool_mse_eq_kmeansCost`: the exposure-weighted total MSE `poolLoss` is the
  weighted k-means cost of the levels at the cohort means plus the number of
  nonempty cohorts.
* `pool_optimal_contiguous`: hence an MSE-optimal labelling has interval
  cohorts, by `kmeans_contiguous` on the labels actually used.

The pooled mean and variance use the inverse-variance weights eq. (23)
(`invVarWeight`), and the blend's credibility factor is eq. (7) (`bestZ`).

Not in the thesis; `notes/kmeans-bridge.md`, Finding 14. Purely algebraic:
the levels are fixed numbers and the two moments of the pooled estimate are
taken as given.
-/

open Finset

namespace Credibility

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- The mean level `x̄ₐ = E X̄ₐ` of cohort `a`, pooled with the inverse-variance
weights eq. (23) for the variances `1/wᵢ` of its units. -/
noncomputable def cohortMean (w x : ι → ℝ) (c : ι → κ) (a : κ) : ℝ :=
  ∑ i : {i // c i = a}, invVarWeight (fun i : {i // c i = a} => (w i.1)⁻¹) i * x i

/-- The variance `Var X̄ₐ = ∑ aᵢ² σᵢ²` of cohort `a`'s pooled estimate, with the
weights eq. (23) and `σᵢ² = 1/wᵢ`. -/
noncomputable def poolVar (w : ι → ℝ) (c : ι → κ) (a : κ) : ℝ :=
  ∑ i : {i // c i = a}, invVarWeight (fun i : {i // c i = a} => (w i.1)⁻¹) i ^ 2 * (w i.1)⁻¹

/-- **Pooling by exposure is the best unbiased pooling** (eq. (23)): within a
cohort, any weights `u` summing to one give the pooled estimate a variance
`∑ uᵢ²/wᵢ` at least `Var X̄ₐ`. -/
theorem poolVar_le {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) (a : κ)
    (u : {i // c i = a} → ℝ) (hu : ∑ i, u i = 1) :
    poolVar w c a ≤ ∑ i, u i ^ 2 * (w i.1)⁻¹ := by
  rw [poolVar]
  exact invVarWeight_optimal (fun i : {i // c i = a} => (w i.1)⁻¹)
    (fun i => inv_pos.mpr (hw i.1)) u hu

/-- Exposure-weighted total MSE of pooling: `∑ᵢ wᵢ E(X̄_{c i} - xᵢ)²`, with
`E X̄ₐ = x̄ₐ` and `Var X̄ₐ` as above, i.e. `∑ᵢ wᵢ ((x̄_{c i} - xᵢ)² + Var X̄_{c i})`. -/
noncomputable def poolLoss (w x : ι → ℝ) (c : ι → κ) : ℝ :=
  ∑ i, w i * ((cohortMean w x c (c i) - x i) ^ 2 + poolVar w c (c i))

/-- The weights eq. (23) for the variances `1/wᵢ` are `wᵢ/Wₐ`. -/
theorem invVarWeight_cohort (w : ι → ℝ) (c : ι → κ) (a : κ) (i : {i // c i = a}) :
    invVarWeight (fun i : {i // c i = a} => (w i.1)⁻¹) i = w i / groupWeight c w a := by
  simp only [invVarWeight, inv_inv, groupWeight_eq_filter]
  rw [sum_subtype (p := fun i => c i = a) (univ.filter fun i => c i = a) (fun i => by simp) w]

/-- So `x̄ₐ = ∑_{c i = a} wᵢ xᵢ / Wₐ`, the `w`-weighted mean level. -/
theorem cohortMean_eq (w x : ι → ℝ) (c : ι → κ) (a : κ) :
    cohortMean w x c a = (∑ i with c i = a, w i * x i) / groupWeight c w a := by
  simp only [cohortMean, invVarWeight_cohort]
  rw [sum_subtype (p := fun i => c i = a) (univ.filter fun i => c i = a) (fun i => by simp) (fun i => w i * x i),
    sum_div]
  exact sum_congr rfl fun i _ => by ring

/-- … and `Var X̄ₐ = ∑_{c i = a} (wᵢ/Wₐ)²/wᵢ`. -/
theorem poolVar_eq_sum (w : ι → ℝ) (c : ι → κ) (a : κ) :
    poolVar w c a = ∑ i with c i = a, (w i / groupWeight c w a) ^ 2 * (w i)⁻¹ := by
  simp only [poolVar, invVarWeight_cohort]
  rw [sum_subtype (p := fun i => c i = a) (univ.filter fun i => c i = a) (fun i => by simp)
    (fun i => (w i / groupWeight c w a) ^ 2 * (w i)⁻¹)]

/-- **The pooled variance is `1/Wₐ`**, the minimal value of eq. (23). -/
theorem poolVar_eq {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) (i : ι) :
    poolVar w c (c i) = (groupWeight c w (c i))⁻¹ := by
  have : Nonempty {j // c j = c i} := ⟨⟨i, rfl⟩⟩
  rw [poolVar, invVarWeight_value (fun j : {j // c j = c i} => (w j.1)⁻¹)
    (fun j => inv_pos.mpr (hw j.1))]
  simp only [inv_inv, groupWeight_eq_filter]
  rw [sum_subtype (p := fun j => c j = c i) (univ.filter fun j => c j = c i) (fun j => by simp) w]

/-- A used cohort has positive weight. -/
theorem groupWeight_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) (i : ι) :
    0 < groupWeight c w (c i) := by
  rw [groupWeight_eq_filter]
  exact sum_pos (fun j _ => hw j) ⟨i, by simp⟩

/-- Each nonempty cohort contributes `∑_{i ∈ a} wᵢ / Wₐ = 1`. -/
theorem sum_div_groupWeight {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → κ) :
    ∑ i, w i / groupWeight c w (c i) = (univ.image c).card := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image c) (g := c)
    (fun i _ => mem_image_of_mem c (mem_univ i)), card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  have hW := (groupWeight_pos hw c i).ne'
  rw [sum_congr rfl (g := fun j => w j / groupWeight c w (c i))
    (fun j hj => by rw [(mem_filter.mp hj).2]), ← sum_div]
  simpa [groupWeight_eq_filter] using div_self hW

/-- Deviations from the cohort means are `w`-orthogonal to anything constant
on cohorts. -/
theorem sum_mul_sub_cohortMean {w : ι → ℝ} (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    (c : ι → κ) (g : κ → ℝ) :
    ∑ i, w i * (x i - cohortMean w x c (c i)) * g (c i) = 0 := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image c) (g := c)
    (fun i _ => mem_image_of_mem c (mem_univ i))]
  refine sum_eq_zero fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  have hW := (groupWeight_pos hw c i).ne'
  rw [sum_congr rfl (g := fun j => (w j * x j - w j * cohortMean w x c (c i)) * g (c i))
    (fun j hj => by rw [(mem_filter.mp hj).2]; ring), ← sum_mul, sum_sub_distrib,
    ← sum_mul]
  have : (∑ j with c j = c i, w j) * cohortMean w x c (c i)
      = ∑ j with c j = c i, w j * x j := by
    rw [cohortMean_eq, ← groupWeight_eq_filter]
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
  rw [← sum_div_groupWeight hw c, poolLoss, kmeansCost, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by rw [poolVar_eq hw]; ring

/-- Relabelling cohorts injectively changes neither weights … -/
theorem groupWeight_comp {κ' : Type*} [DecidableEq κ'] (w : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) (a : κ) :
    groupWeight (f ∘ c) w (f a) = groupWeight c w a := by
  simp [groupWeight_eq_filter, hf.eq_iff]

/-- … nor means … -/
theorem cohortMean_comp {κ' : Type*} [DecidableEq κ'] (w x : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) (a : κ) :
    cohortMean w x (f ∘ c) (f a) = cohortMean w x c a := by
  simp [cohortMean_eq, groupWeight_eq_filter, hf.eq_iff]

/-- … nor the pooling loss. -/
theorem poolLoss_comp {κ' : Type*} [DecidableEq κ'] (w x : ι → ℝ) (c : ι → κ)
    {f : κ → κ'} (hf : Function.Injective f) :
    poolLoss w x (f ∘ c) = poolLoss w x c := by
  unfold poolLoss
  refine sum_congr rfl fun i _ => ?_
  rw [Function.comp_apply, cohortMean_comp w x c hf]
  simp [poolVar_eq_sum, groupWeight_comp w c hf, hf.eq_iff]

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

/-! ## Common variance: the credibility blend

With a common variance `V`, cohort `a` of `nₐ` units has pooled estimate with
mean `x̄ₐ` (plain mean) and variance `V/nₐ`, and credibility factor
`zₐ = nₐτ²/(nₐτ² + V)`. A swap argument shows that MSE-optimal cohorts for the
blend `μ + zₐ(X̄ₐ - μ)` are intervals (`notes/kmeans-bridge.md`). -/

/-- The moments of the blend `z X̄ₐ + (1 - z) μ` for a cohort of `n` units with
common variance `V` and known `μ`: `Var X̄ₐ = τ² + V/n` and
`cov(X̄ₐ, μₐ) = Var μₐ = τ²`; the collective `μ` is a constant. -/
noncomputable def sizeMoments (V τ2 n : ℝ) : BlendMoments where
  varCohort := τ2 + V / n
  varPortfolio := 0
  varTarget := τ2
  covEst := 0
  covCohortTarget := τ2
  covPortfolioTarget := 0

/-- Credibility factor of a cohort of `n` units with common variance `V`:
the best factor eq. (7) for the moments `sizeMoments`. -/
noncomputable def sizeZ (V τ2 n : ℝ) : ℝ := (sizeMoments V τ2 n).bestZ

/-- **`sizeZ` is `nτ²/(nτ² + V)`**: eq. (7) for a cohort of `n` units with common
variance `V` and known `μ`. -/
theorem sizeZ_eq {V τ2 n : ℝ} (hn : 0 < n) (hpos : 0 < n * τ2 + V) :
    sizeZ V τ2 n = n * τ2 / (n * τ2 + V) := by
  have h2 : τ2 + V / n ≠ 0 := by
    rw [show τ2 + V / n = (n * τ2 + V) / n by field_simp]
    exact div_ne_zero hpos.ne' hn.ne'
  simp only [sizeZ, BlendMoments.bestZ, BlendMoments.gap, sizeMoments]
  rw [div_eq_div_iff (by simpa using h2) hpos.ne']
  field_simp
  ring

/-- Hence `sizeZ` minimises the blend's error variance eq. (6) over all `z`. -/
theorem sizeZ_optimal {V τ2 n : ℝ} (hn : 0 < n) (hV : 0 ≤ V) (hτ : 0 < τ2) (z : ℝ) :
    (sizeMoments V τ2 n).errVar (sizeZ V τ2 n) ≤ (sizeMoments V τ2 n).errVar z := by
  exact BlendMoments.bestZ_optimal _ (by simp [BlendMoments.gap, sizeMoments]; positivity) z

/-- Total MSE of the credibility blend with common variance `V`, known `μ`
and `τ²`. Unit `i` of cohort `a` is predicted by `μ + zₐ(X̄ₐ - μ)` with
`E X̄ₐ = x̄ₐ`, `Var X̄ₐ = V/nₐ`, so its MSE is
`(μ + zₐ(x̄ₐ - μ) - xᵢ)² + zₐ² V/nₐ` (`nₐ = groupWeight c 1 a`). -/
noncomputable def blendLoss (V τ2 μ : ℝ) (x : ι → ℝ) (c : ι → κ) : ℝ :=
  ∑ i, ((μ + sizeZ V τ2 (groupWeight c 1 (c i)) * (cohortMean 1 x c (c i) - μ) - x i) ^ 2
    + sizeZ V τ2 (groupWeight c 1 (c i)) ^ 2 * (V / groupWeight c 1 (c i)))

/-- The part of the blend loss that depends on the cohorts: a cohort of size
`n` and summed deviation `S = Σ (xᵢ - μ)` contributes `z(2 - z)/n · S² - z²V`. -/
noncomputable def blendGain (V τ2 n S : ℝ) : ℝ :=
  sizeZ V τ2 n * (2 - sizeZ V τ2 n) / n * S ^ 2 - sizeZ V τ2 n ^ 2 * V

/-- **The blend loss depends on a cohort only through its size and sum**:
`blendLoss = Σᵢ (xᵢ - μ)² - Σₐ (fₐ Sₐ² - zₐ²V)`, `fₐ = zₐ(2 - zₐ)/nₐ`. -/
theorem blendLoss_eq (V τ2 μ : ℝ) (x : ι → ℝ) (c : ι → κ) :
    blendLoss V τ2 μ x c = ∑ i, (x i - μ) ^ 2 - ∑ a ∈ univ.image c,
      blendGain V τ2 (groupWeight c 1 a) (groupWeight c (fun i => x i - μ) a) := by
  have hmaps : ∀ i ∈ (univ : Finset ι), c i ∈ univ.image c :=
    fun i _ => mem_image_of_mem c (mem_univ i)
  rw [blendLoss, ← sum_fiberwise_of_maps_to hmaps,
    ← sum_fiberwise_of_maps_to (f := fun i => (x i - μ) ^ 2) hmaps, ← sum_sub_distrib]
  refine sum_congr rfl fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  have hN : 0 < groupWeight c 1 (c i) := groupWeight_pos (fun _ => one_pos) c i
  set N := groupWeight c 1 (c i) with hNdef
  set S := groupWeight c (fun i => x i - μ) (c i) with hSdef
  set z := sizeZ V τ2 N with hz
  have hmean : cohortMean 1 x c (c i) - μ = S / N := by
    rw [cohortMean_eq, ← hNdef, hSdef, groupWeight_eq_filter, sum_sub_distrib, sum_const, nsmul_eq_mul]
    have : ((univ.filter fun j => c j = c i).card : ℝ) = N := by
      rw [hNdef, groupWeight_eq_filter]; simp
    simp only [Pi.one_apply, one_mul]
    rw [this]; field_simp
  have hterm : ∀ j ∈ univ.filter (fun j => c j = c i),
      (μ + sizeZ V τ2 (groupWeight c 1 (c j)) * (cohortMean 1 x c (c j) - μ) - x j) ^ 2
        + sizeZ V τ2 (groupWeight c 1 (c j)) ^ 2 * (V / groupWeight c 1 (c j))
      = (x j - μ) ^ 2 + (z ^ 2 * S ^ 2 / N ^ 2 + z ^ 2 * V / N) * 1
        + (-2 * z * S / N) * (x j - μ) := by
    intro j hj
    rw [(mem_filter.mp hj).2, hmean, ← hNdef, ← hz]
    field_simp
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 : ∑ j with c j = c i, (1 : ℝ) = N := by rw [hNdef, groupWeight_eq_filter]; rfl
  have h2 : ∑ j with c j = c i, (x j - μ) = S := by rw [hSdef, groupWeight_eq_filter]
  rw [h1, h2, blendGain]
  field_simp
  ring

/-- Swapping two units of different cohorts moves their values between the
two cohort sums and leaves every other cohort sum unchanged. -/
theorem groupWeight_swap [DecidableEq ι] (y : ι → ℝ) (c : ι → κ) {i j : ι} (h : c i ≠ c j)
    (a : κ) :
    groupWeight (c ∘ Equiv.swap i j) y a = groupWeight c y a
      + (if c i = a then y j - y i else 0) + (if c j = a then y i - y j else 0) := by
  have hij : i ≠ j := fun e => h (congrArg c e)
  have hre : groupWeight (c ∘ Equiv.swap i j) y a
      = ∑ k, if c k = a then y (Equiv.swap i j k) else 0 := by
    rw [groupWeight_eq_filter, sum_filter, ← Equiv.sum_comp (Equiv.swap i j)]
    simp
  have hd : (∑ k, if c k = a then y (Equiv.swap i j k) else 0) - groupWeight c y a
      = (if c i = a then y j - y i else 0) + (if c j = a then y i - y j else 0) := by
    rw [groupWeight_eq_filter, sum_filter, ← sum_sub_distrib,
      sum_eq_add i j hij (fun k _ hk => by
        simp [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2])]
    · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
      split_ifs <;> ring
    · simp
    · simp
  linarith

/-- The weight `fₙ = zₙ(2 - zₙ)/n` of a squared cohort sum in `blendGain`. -/
noncomputable def blendF (V τ2 n : ℝ) : ℝ := sizeZ V τ2 n * (2 - sizeZ V τ2 n) / n

/-- A nonempty cohort has `fₙ > 0`. -/
theorem blendF_pos {V τ2 n : ℝ} (hV : 0 ≤ V) (hτ : 0 < τ2) (hn : 0 < n) :
    0 < blendF V τ2 n := by
  have hd : 0 < n * τ2 + V := by positivity
  rw [blendF, sizeZ_eq hn hd]
  have hz : 0 < n * τ2 / (n * τ2 + V) := div_pos (mul_pos hn hτ) hd
  have hz1 : n * τ2 / (n * τ2 + V) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have : 0 < n * τ2 / (n * τ2 + V) * (2 - n * τ2 / (n * τ2 + V)) := mul_pos hz (by linarith)
  positivity

/-- **Swapping two units** `i ∈ A`, `j ∈ B` of different cohorts changes the
blend loss by `-(2d(f_A S_A - f_B S_B) + (f_A + f_B)d²)`, `d = xⱼ - xᵢ`: the
sizes, hence `f` and `z`, are unchanged, and `d` moves from `S_B` to `S_A`. -/
theorem blendLoss_swap [DecidableEq ι] (V τ2 μ : ℝ) (x : ι → ℝ) (c : ι → κ) {i j : ι}
    (h : c i ≠ c j) :
    blendLoss V τ2 μ x (c ∘ Equiv.swap i j) - blendLoss V τ2 μ x c
      = -(2 * (x j - x i) * (blendF V τ2 (groupWeight c 1 (c i))
            * groupWeight c (fun k => x k - μ) (c i)
          - blendF V τ2 (groupWeight c 1 (c j)) * groupWeight c (fun k => x k - μ) (c j))
        + (blendF V τ2 (groupWeight c 1 (c i)) + blendF V τ2 (groupWeight c 1 (c j)))
          * (x j - x i) ^ 2) := by
  have himg : univ.image (c ∘ Equiv.swap i j) = univ.image c := by
    rw [← image_image, image_univ_equiv]
  have hN : ∀ a, groupWeight (c ∘ Equiv.swap i j) 1 a = groupWeight c 1 a := by
    intro a; rw [groupWeight_swap _ c h]; simp
  rw [blendLoss_eq, blendLoss_eq, himg]
  simp only [hN, groupWeight_swap _ c h]
  rw [sub_sub_sub_cancel_left, ← sum_sub_distrib,
    sum_eq_add_of_mem (c i) (c j) (mem_image_of_mem c (mem_univ i))
      (mem_image_of_mem c (mem_univ j)) h (fun a _ ha => by
        simp [Ne.symm ha.1, Ne.symm ha.2])]
  simp only [h, Ne.symm h, ite_true, ite_false, blendGain]
  unfold blendF
  ring

/-- **Optimal blend cohorts are intervals** (`notes/kmeans-bridge.md`). With a
common variance `V ≥ 0`, `τ² > 0` and known `μ`, if the labelling `c`
minimises the blend's total MSE among all labellings into `κ`, then a unit
whose level lies strictly between two units of the same cohort is in that
cohort. -/
theorem blend_optimal_contiguous [DecidableEq ι] {V τ2 μ : ℝ} {x : ι → ℝ} {c : ι → κ}
    (hV : 0 ≤ V) (hτ : 0 < τ2) (hopt : ∀ c' : ι → κ, blendLoss V τ2 μ x c ≤ blendLoss V τ2 μ x c')
    {i j l : ι} (hij : x i < x j) (hjl : x j < x l) (hil : c i = c l) :
    c j = c i := by
  by_contra hb
  have h1 := blendLoss_swap V τ2 μ x c (Ne.symm hb)
  have h2 := blendLoss_swap V τ2 μ x c (i := l) (Ne.symm (hil ▸ hb))
  rw [← hil] at h2
  have o1 := hopt (c ∘ Equiv.swap i j)
  have o2 := hopt (c ∘ Equiv.swap l j)
  have fA := blendF_pos hV hτ (groupWeight_pos (fun _ => one_pos) c i)
  have fB := blendF_pos hV hτ (groupWeight_pos (fun _ => one_pos) c j)
  set D := blendF V τ2 (groupWeight c 1 (c i)) * groupWeight c (fun k => x k - μ) (c i)
    - blendF V τ2 (groupWeight c 1 (c j)) * groupWeight c (fun k => x k - μ) (c j)
  set F := blendF V τ2 (groupWeight c 1 (c i)) + blendF V τ2 (groupWeight c 1 (c j))
  have hF : 0 < F := add_pos fA fB
  have d1 : 0 < x j - x i := by linarith
  have d2 : x j - x l < 0 := by linarith
  have e1 : 2 * (x j - x i) * D < 0 := by nlinarith [mul_pos hF (mul_pos d1 d1)]
  have e2 : 2 * (x j - x l) * D < 0 := by nlinarith [mul_pos hF (mul_pos_of_neg_of_neg d2 d2)]
  have : D < 0 := by nlinarith
  nlinarith

end Credibility
