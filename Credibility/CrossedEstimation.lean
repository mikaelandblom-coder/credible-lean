import Credibility.Crossed

/-!
# Crossed levels: estimating `α²`, `β²`, `γ²` from pairs

Extension, part 2 of `Crossed.lean` (`notes/crossed-2x2.md` §6). The cohorts `j` of a thesis
model `M` (noise `σⱼₜ`, correlations `ρᵢⱼ` within a period, weights `wⱼₜ`) are cells of a
table with rows `row j` and columns `col j`, and their levels are crossed:

  `cov(μᵢₜ, μⱼₛ) = σᵢₜσⱼₛρᵢⱼ[t = s] + α²[same row] + β²[same column] + γ²[i = j]`.

As in Bridge 5 (`Hierarchical.lean`), the level part is a sum of rank-one patterns, so every
estimator unbiased in the thesis model has, with crossed levels, an expectation shifted by its
values on the noise-free row, column and cell patterns (`unbiasedX_of`). Hence:

* `σ²ᵢⱼρᵢⱼ^` stays unbiased (it uses deviations within a cohort only);
* the pair estimator `P̂ᵢⱼ = (μ̂ᵢ - μ̂ⱼ)² - (noise estimate)` is unbiased for
  `2γ² + 2α²[different rows] + 2β²[different columns]`: `2(β² + γ²)` in the same row,
  `2(α² + γ²)` in the same column, `2(α² + β² + γ²)` for neither;
* pooling the pairs of each class with any weights summing to one, three linear combinations
  are unbiased for `α²`, `β²` and `γ²`: the three variances are identified as soon as each
  class has a pair.

This is the pair form of the analysis-of-variance estimators of Dannenburg (1995) (Goulet 1998,
§8.3, eqs. (67)–(69)): a weighted sum of squares about a mean is a weighted average of squared
pair differences (`sum_mul_sq_sub_eq_pairs`). Here the noise may be correlated across cells in
the same period. Only first and second moments are assumed.
-/

open Finset

namespace Credibility

/-- A sum over the ordered pairs of distinct elements: all pairs minus the diagonal. -/
lemma sum_offDiag_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ι → ℝ) :
    ∑ p ∈ s.offDiag, f p.1 p.2 = ∑ a ∈ s, ∑ b ∈ s, f a b - ∑ a ∈ s, f a a := by
  have h : ∀ a b, (if a ≠ b then f a b else 0) = f a b - if a = b then f a b else 0 := by
    intro a b; split_ifs <;> simp_all
  have hs : s.offDiag = (s ×ˢ s).filter fun p => p.1 ≠ p.2 := by
    ext p; simp [Finset.mem_offDiag, and_assoc]
  rw [hs, Finset.sum_filter, Finset.sum_product]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  congr 1
  exact Finset.sum_congr rfl fun a ha => by simp [ha]

/-- **A noise-corrected weighted sum of squares is a pool of noise-corrected pair differences.**
With weights `uₖ`, `U = Σₖ uₖ`, `x̄ = Σₖ uₖxₖ/U` and noise variances `vₖ`:

  `Σₖ (uₖ/U)(xₖ - x̄)² - Σₖ (uₖ/U)(1 - uₖ/U)vₖ = Σ_{k ≠ l} uₖuₗ/(2U²) · ((xₖ - xₗ)² - vₖ - vₗ)`.

With `vₖ = s²/uₖ` the correction is `(n - 1)s²/U`, that of the analysis-of-variance estimators of
crossed-classification credibility (Goulet 1998, eqs. (67)–(69)). -/
theorem sum_mul_sq_sub_noise_eq_pairs {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (u x v : ι → ℝ) (hU : ∑ k ∈ s, u k ≠ 0) :
    ∑ k ∈ s, u k / (∑ l ∈ s, u l) * (x k - ∑ l ∈ s, u l / (∑ l ∈ s, u l) * x l) ^ 2
        - ∑ k ∈ s, u k / (∑ l ∈ s, u l) * (1 - u k / ∑ l ∈ s, u l) * v k
      = ∑ p ∈ s.offDiag, u p.1 * u p.2 / (2 * (∑ l ∈ s, u l) ^ 2)
          * ((x p.1 - x p.2) ^ 2 - v p.1 - v p.2) := by
  rw [sum_offDiag_eq s fun a b => u a * u b / (2 * (∑ l ∈ s, u l) ^ 2)
    * ((x a - x b) ^ 2 - v a - v b)]
  set U := ∑ l ∈ s, u l
  have e1 : ∀ k, u k / U * (x k - ∑ l ∈ s, u l / U * x l) ^ 2
      = u k * x k ^ 2 / U - 2 * (∑ l ∈ s, u l * x l) / U ^ 2 * (u k * x k)
        + (∑ l ∈ s, u l * x l) ^ 2 / U ^ 3 * u k := fun k => by
    rw [show ∑ l ∈ s, u l / U * x l = (∑ l ∈ s, u l * x l) / U by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by ring]
    field_simp; ring
  have e2 : ∀ a b, u a * u b / (2 * U ^ 2) * ((x a - x b) ^ 2 - v a - v b)
      = (u b * (u a * x a ^ 2) + u a * (u b * x b ^ 2) - 2 * (u a * x a) * (u b * x b)
        - u b * (u a * v a) - u a * (u b * v b)) / (2 * U ^ 2) := fun a b => by ring
  have hUd : ∑ i ∈ s, u i = U := rfl
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_mul, ← Finset.mul_sum, hUd]
  rw [show ∑ k ∈ s, u k / U * (1 - u k / U) * v k
      = (∑ k ∈ s, u k * v k) / U - (∑ k ∈ s, u k ^ 2 * v k) / U ^ 2 by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by field_simp]
  field_simp
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

namespace Model

variable {J T A B : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable (M : Model J T) (row : J → A) (col : J → B)

/-- `cov(μᵢₜ, μⱼₛ)` with crossed levels: eq. (16) with the crossed `L` in place of `τ²δᵢⱼ`. -/
noncomputable def obsCovX (α2 β2 γ2 : ℝ) (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0)
    + Crossed.levelCov row col α2 β2 γ2 i j

/-- `f` is unbiased for `θ` with crossed levels, whatever the mean `μ`. -/
def UnbiasedX (α2 β2 γ2 : ℝ) (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  UnbiasedCov (fun p q => M.obsCovX row col α2 β2 γ2 p.1 q.1 p.2 q.2) f θ

omit [Fintype J] [Fintype T] [Fintype A] [Fintype B] in
/-- The table `obsCovX` is symmetric, so `UnbiasedX` fixes the value (`UnbiasedCov.unique`). -/
lemma obsCovX_symm (α2 β2 γ2 : ℝ) (p q : J × T) :
    M.obsCovX row col α2 β2 γ2 q.1 p.1 q.2 p.2 = M.obsCovX row col α2 β2 γ2 p.1 q.1 p.2 q.2 := by
  simp only [obsCovX, Crossed.levelCov_apply, M.ρ_symm q.1 p.1, eq_comm (a := q.2),
    eq_comm (a := q.1), eq_comm (a := row q.1), eq_comm (a := col q.1)]
  ring

/-- The crossed levels move an expectation by the estimator at the noise-free patterns:
`γ² - τ²` times the cell patterns, `α²` times the row patterns, `β²` times the column patterns. -/
lemma Ecov_obsCovX_eq (α2 β2 γ2 μ : ℝ) (Q : J × T → J × T → ℝ) :
    Ecov (fun p q => M.obsCovX row col α2 β2 γ2 p.1 q.1 p.2 q.2) μ Q
      = M.E μ Q + (γ2 - M.τ2) * ∑ j, quad Q (grpData id j)
        + α2 * ∑ a, quad Q (grpData row a) + β2 * ∑ b, quad Q (grpData col b) := by
  rw [sum_quad_grpData, sum_quad_grpData, sum_quad_grpData]
  simp only [E, Ecov, cov, obsCov, obsCovX, Crossed.levelCov_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, id]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- **From the thesis to crossed levels.** An estimator unbiased for `θ` in the thesis model
has, with crossed levels, expectation `θ + (γ² - τ²)Σⱼ f(1_{j}) + α²Σₐ f(1_{row a})
+ β²Σ_b f(1_{col b})`. -/
theorem unbiasedX_of {f : (J × T → ℝ) → ℝ} {θ : ℝ} (hf : M.Unbiased f θ) (α2 β2 γ2 : ℝ) :
    M.UnbiasedX row col α2 β2 γ2 f
      (θ + (γ2 - M.τ2) * ∑ j, f (grpData id j) + α2 * ∑ a, f (grpData row a)
        + β2 * ∑ b, f (grpData col b)) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  refine ⟨Q, hQ, fun μ => ?_⟩
  rw [Ecov_obsCovX_eq, show M.E μ Q = θ from hE μ]
  simp only [hQ]

variable {w : J → T → ℝ} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t)
  (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

/-- With crossed levels `σ²ᵢⱼρᵢⱼ^` is still unbiased: the levels cancel within a cohort. -/
theorem sigRhoHat_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (i j : J) :
    M.UnbiasedX row col α2 β2 γ2 (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedX_of row col (M.sigRhoHat_unbiased sig hw hσ hT i j) α2 β2 γ2
  simpa [sigRhoHat_grpData _ hw] using h

/-- **The pair estimator with crossed levels** (`i ≠ j`): `P̂ᵢⱼ` is unbiased for
`2γ² + 2α²[row i ≠ row j] + 2β²[col i ≠ col j]`. -/
theorem pairHat_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) {i j : J} (hij : i ≠ j) :
    M.UnbiasedX row col α2 β2 γ2 (fun X => pairHat w X i j)
      (2 * γ2 + 2 * α2 * (if row i = row j then 0 else 1)
        + 2 * β2 * (if col i = col j then 0 else 1)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedX_of row col (M.pairHat_unbiased sig hw hσ hT hij) α2 β2 γ2
  rw [sum_pairHat_grpData _ hw, sum_pairHat_grpData _ hw, sum_pairHat_grpData _ hw] at h
  refine h.congr (fun _ => rfl) ?_
  simp only [id, hij, ite_false]
  split_ifs <;> ring

/-- Pairs in the same row, in different columns. -/
def sameRowPairs : Finset (J × J) :=
  (Finset.univ : Finset J).offDiag.filter fun p => row p.1 = row p.2 ∧ col p.1 ≠ col p.2

/-- Pairs in the same column, in different rows. -/
def sameColPairs : Finset (J × J) :=
  (Finset.univ : Finset J).offDiag.filter fun p => row p.1 ≠ row p.2 ∧ col p.1 = col p.2

/-- Pairs sharing neither row nor column. -/
def crossPairs : Finset (J × J) :=
  (Finset.univ : Finset J).offDiag.filter fun p => row p.1 ≠ row p.2 ∧ col p.1 ≠ col p.2

/-- A weighted pool `Σₚ aₚP̂ₚ` of the pair estimators over a set of ordered pairs. -/
noncomputable def pairPool (w : J → T → ℝ) (S : Finset (J × J)) (a : J × J → ℝ)
    (X : J × T → ℝ) : ℝ :=
  ∑ p ∈ S, a p * pairHat w X p.1 p.2

/-- A pool over pairs of one class, with weights summing to one, is unbiased for the class's
value `v`. -/
lemma pairPool_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) {v : ℝ} (S : Finset (J × J))
    (hS : ∀ p ∈ S, p.1 ≠ p.2 ∧ 2 * γ2 + 2 * α2 * (if row p.1 = row p.2 then 0 else 1)
        + 2 * β2 * (if col p.1 = col p.2 then 0 else 1) = v) (a : J × J → ℝ) (ha : ∑ p ∈ S, a p = 1) :
    M.UnbiasedX row col α2 β2 γ2 (pairPool w S a) v := by
  refine (UnbiasedCov.sum S fun p hp =>
    (M.pairHat_unbiasedX row col sig hw hσ hT α2 β2 γ2 (hS p hp).1).const_mul (a p)).congr
    (fun X => rfl) ?_
  rw [Finset.sum_congr rfl fun p hp => by rw [(hS p hp).2], ← Finset.sum_mul, ha, one_mul]

/-- Same row: the pool is unbiased for `2(β² + γ²)`. -/
theorem sameRowPool_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (a : J × J → ℝ)
    (ha : ∑ p ∈ sameRowPairs row col, a p = 1) :
    M.UnbiasedX row col α2 β2 γ2 (pairPool w (sameRowPairs row col) a) (2 * (β2 + γ2)) :=
  M.pairPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 _ (fun p hp => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hp
    refine ⟨(Finset.mem_offDiag.mp h1).2.2, ?_⟩
    simp only [h2, h3, ite_true, ite_false]; ring) a ha

/-- Same column: the pool is unbiased for `2(α² + γ²)`. -/
theorem sameColPool_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (a : J × J → ℝ)
    (ha : ∑ p ∈ sameColPairs row col, a p = 1) :
    M.UnbiasedX row col α2 β2 γ2 (pairPool w (sameColPairs row col) a) (2 * (α2 + γ2)) :=
  M.pairPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 _ (fun p hp => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hp
    refine ⟨(Finset.mem_offDiag.mp h1).2.2, ?_⟩
    simp only [h2, h3, ite_true, ite_false]; ring) a ha

/-- Neither: the pool is unbiased for `2(α² + β² + γ²)`. -/
theorem crossPool_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (a : J × J → ℝ)
    (ha : ∑ p ∈ crossPairs row col, a p = 1) :
    M.UnbiasedX row col α2 β2 γ2 (pairPool w (crossPairs row col) a) (2 * (α2 + β2 + γ2)) :=
  M.pairPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 _ (fun p hp => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hp
    refine ⟨(Finset.mem_offDiag.mp h1).2.2, ?_⟩
    simp only [h2, h3, ite_false]; ring) a ha

/-- **The three variances are identified.** With weights `r`, `c`, `n` summing to one on the
same-row, same-column and neither pairs (any weights: equal, volume-based, …),

  `α̂² = (P̂_n - P̂_r)/2`, `β̂² = (P̂_n - P̂_c)/2`, `γ̂² = (P̂_r + P̂_c - P̂_n)/2`

are unbiased for `α²`, `β²`, `γ²`, whatever the mean and the noise correlations. -/
theorem crossed_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (r c n : J × J → ℝ)
    (hr : ∑ p ∈ sameRowPairs row col, r p = 1) (hc : ∑ p ∈ sameColPairs row col, c p = 1)
    (hn : ∑ p ∈ crossPairs row col, n p = 1) :
    M.UnbiasedX row col α2 β2 γ2
        (fun X => (pairPool w (crossPairs row col) n X - pairPool w (sameRowPairs row col) r X) / 2) α2
      ∧ M.UnbiasedX row col α2 β2 γ2
        (fun X => (pairPool w (crossPairs row col) n X - pairPool w (sameColPairs row col) c X) / 2) β2
      ∧ M.UnbiasedX row col α2 β2 γ2
        (fun X => (pairPool w (sameRowPairs row col) r X + pairPool w (sameColPairs row col) c X
          - pairPool w (crossPairs row col) n X) / 2) γ2 := by
  have hR := M.sameRowPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 r hr
  have hC := M.sameColPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 c hc
  have hN := M.crossPool_unbiasedX row col sig hw hσ hT α2 β2 γ2 n hn
  refine ⟨((hN.add (hR.const_mul (-1))).const_mul (1 / 2)).congr (fun X => by ring) (by ring),
    ((hN.add (hC.const_mul (-1))).const_mul (1 / 2)).congr (fun X => by ring) (by ring),
    (((hR.add hC).add (hN.const_mul (-1))).const_mul (1 / 2)).congr (fun X => by ring) (by ring)⟩


/-! ### The analysis-of-variance statistics of Dannenburg and Goulet

Goulet (1998, eqs. (67)–(69), from Dannenburg 1995) estimates the crossed variances from
volume-weighted sums of squares of the cell estimates about their weighted mean, minus a noise
correction. For a set `S` of cells with volumes `uₖ = Σₜ wₖₜ`, `U = Σ_S uₖ`, and noise estimates
`v̂ₖ` of `Var(noise of μ̂ₖ) = σ²ₖₖρₖₖ`, the statistic is

  `G = Σ_S (uₖ/U)(μ̂ₖ - μ̄)² - Σ_S (uₖ/U)(1 - uₖ/U)v̂ₖ`

(with `v̂ₖ = ŝ²/uₖ` the correction is Goulet's `(|S| - 1)ŝ²/U`). It is the pool of the pairs
`(μ̂ₖ - μ̂ₗ)² - v̂ₖ - v̂ₗ` with weights `uₖuₗ/(2U²)` (`sum_mul_sq_sub_noise_eq_pairs`), whose noise
correction omits the cross term `+2σ²ₖₗρₖₗ` of the pair estimator `P̂ₖₗ`. -/

/-- The analysis-of-variance statistic of crossed-classification credibility for a set `S` of
cells, with noise estimates `v`. -/
noncomputable def anovaStat (w : J → T → ℝ) (S : Finset J) (v : J → (J × T → ℝ) → ℝ)
    (X : J × T → ℝ) : ℝ :=
  ∑ k ∈ S, wtot w k / (∑ l ∈ S, wtot w l)
      * (muHat w X k - ∑ l ∈ S, wtot w l / (∑ l ∈ S, wtot w l) * muHat w X l) ^ 2
    - ∑ k ∈ S, wtot w k / (∑ l ∈ S, wtot w l) * (1 - wtot w k / ∑ l ∈ S, wtot w l) * v k X

/-- **The exact expectation of the ANOVA statistic** with crossed levels and any noise
correlations: with `cₖₗ = uₖuₗ/(2U²)`,

  `E G = Σ_{k ≠ l ∈ S} cₖₗ (2γ² + 2α²[rows differ] + 2β²[columns differ] - 2σ²ₖₗρₖₗ)`,

for any unbiased noise estimates `v̂ₖ`. -/
theorem anovaStat_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (S : Finset J)
    (hS : S.Nonempty) (v : J → (J × T → ℝ) → ℝ)
    (hv : ∀ k, M.UnbiasedX row col α2 β2 γ2 (v k) (M.σ2 k k * M.ρ k k)) :
    M.UnbiasedX row col α2 β2 γ2 (anovaStat w S v)
      (∑ p ∈ S.offDiag, wtot w p.1 * wtot w p.2 / (2 * (∑ l ∈ S, wtot w l) ^ 2)
        * (2 * γ2 + 2 * α2 * (if row p.1 = row p.2 then 0 else 1)
          + 2 * β2 * (if col p.1 = col p.2 then 0 else 1) - 2 * (M.σ2 p.1 p.2 * M.ρ p.1 p.2))) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hU : ∑ l ∈ S, wtot w l ≠ 0 :=
    (Finset.sum_pos (fun l _ => wtot_pos hw l) hS).ne'
  have hs := M.sigRhoHat_unbiasedX row col sig hw hσ hT α2 β2 γ2
  refine (UnbiasedCov.sum S.offDiag fun p hp =>
    ((((M.pairHat_unbiasedX row col sig hw hσ hT α2 β2 γ2 (Finset.mem_offDiag.mp hp).2.2).add
      ((hs p.1 p.1).add ((hv p.1).const_mul (-1)))).add
      ((hs p.2 p.2).add ((hv p.2).const_mul (-1)))).add
      ((hs p.1 p.2).const_mul (-2))).const_mul
      (wtot w p.1 * wtot w p.2 / (2 * (∑ l ∈ S, wtot w l) ^ 2))).congr (fun X => ?_) ?_
  · rw [anovaStat, sum_mul_sq_sub_noise_eq_pairs S (wtot w) (fun k => muHat w X k)
      (fun k => v k X) hU]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [pairHat]
    ring
  · exact Finset.sum_congr rfl fun p _ => by ring

omit [Fintype J] [DecidableEq T] hw hσ in
/-- `Σ_{k ≠ l ∈ S} uₖuₗ/U² = 1 - Σ_S (uₖ/U)²`. -/
lemma sum_offDiag_wtot (S : Finset J) (hU : ∑ l ∈ S, wtot w l ≠ 0) :
    ∑ p ∈ S.offDiag, wtot w p.1 * wtot w p.2 / (∑ l ∈ S, wtot w l) ^ 2
      = 1 - ∑ k ∈ S, (wtot w k / ∑ l ∈ S, wtot w l) ^ 2 := by
  rw [sum_offDiag_eq S fun a b => wtot w a * wtot w b / (∑ l ∈ S, wtot w l) ^ 2]
  simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, div_pow]
  field_simp

/-- **Goulet's within-row equation, exactly, and its bias under correlated noise** (Finding 42).
If the cells of `S` lie in one row, in different columns, the ANOVA statistic has expectation

  `(β² + γ²)(1 - Σ_S (uₖ/U)²) - Σ_{k ≠ l ∈ S} (uₖuₗ/U²) σ²ₖₗρₖₗ`.

The first term is Goulet's eq. (67) (two-way); the second is missing from it: noise correlated
across cells in the same period biases the statistic, downward when the correlations are
positive. -/
theorem anovaStat_row_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (S : Finset J)
    (hS : S.Nonempty) (hrow : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → row k = row l ∧ col k ≠ col l)
    (v : J → (J × T → ℝ) → ℝ)
    (hv : ∀ k, M.UnbiasedX row col α2 β2 γ2 (v k) (M.σ2 k k * M.ρ k k)) :
    M.UnbiasedX row col α2 β2 γ2 (anovaStat w S v)
      ((β2 + γ2) * (1 - ∑ k ∈ S, (wtot w k / ∑ l ∈ S, wtot w l) ^ 2)
        - ∑ p ∈ S.offDiag, wtot w p.1 * wtot w p.2 / (∑ l ∈ S, wtot w l) ^ 2
          * (M.σ2 p.1 p.2 * M.ρ p.1 p.2)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hU : ∑ l ∈ S, wtot w l ≠ 0 :=
    (Finset.sum_pos (fun l _ => wtot_pos hw l) hS).ne'
  refine (M.anovaStat_unbiasedX row col sig hw hσ hT α2 β2 γ2 S hS v hv).congr (fun _ => rfl) ?_
  rw [← sum_offDiag_wtot S hU, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hr, hc⟩ := hrow p.1 h1 p.2 h2 h3
  simp only [hr, hc, ite_true, ite_false]
  field_simp
  ring

/-- …so with noise uncorrelated across the cells of `S` the ANOVA statistic is unbiased for
Goulet's `(β² + γ²)(1 - Σ_S (uₖ/U)²)`: the exact match with eq. (67). -/
theorem anovaStat_row_unbiasedX_of_uncorr (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ)
    (S : Finset J) (hS : S.Nonempty)
    (hrow : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → row k = row l ∧ col k ≠ col l)
    (hρ : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → M.ρ k l = 0) (v : J → (J × T → ℝ) → ℝ)
    (hv : ∀ k, M.UnbiasedX row col α2 β2 γ2 (v k) (M.σ2 k k * M.ρ k k)) :
    M.UnbiasedX row col α2 β2 γ2 (anovaStat w S v)
      ((β2 + γ2) * (1 - ∑ k ∈ S, (wtot w k / ∑ l ∈ S, wtot w l) ^ 2)) := by
  refine (M.anovaStat_row_unbiasedX row col sig hw hσ hT α2 β2 γ2 S hS hrow v hv).congr
    (fun _ => rfl) ?_
  rw [Finset.sum_eq_zero (s := S.offDiag) fun p hp => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    rw [hρ p.1 h1 p.2 h2 h3, mul_zero, mul_zero], sub_zero]


/-- The volume of the cells of `S` in group `g` (a row or a column): `U_g = Σ_{k ∈ S, g(k) = g} uₖ`. -/
noncomputable def grpVolume {G : Type*} (w : J → T → ℝ) (S : Finset J) (grp : J → G)
    [DecidableEq G] (g : G) : ℝ :=
  ∑ k ∈ S, if grp k = g then wtot w k else 0

omit [Fintype J] [DecidableEq T] hw hσ in
omit [DecidableEq J] in
/-- `Σ_g U_g² = Σ_{k, l ∈ S} uₖuₗ[g(k) = g(l)]`. -/
lemma sum_grpVolume_sq {G : Type*} [Fintype G] [DecidableEq G] (S : Finset J) (grp : J → G) :
    ∑ g, grpVolume w S grp g ^ 2
      = ∑ a ∈ S, ∑ b ∈ S, wtot w a * wtot w b * (if grp a = grp b then 1 else 0) := by
  simp only [grpVolume, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : grp a = grp b
  · simp [h]
  · simp only [h, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun g _ => ?_
    by_cases ha : grp a = g
    · have : ¬grp b = g := fun e => h (ha.trans e.symm)
      simp [ha, this]
    · simp [ha]

omit [Fintype J] [DecidableEq T] hw hσ in
/-- The weighted share of pairs in different groups: `Σ_{k ≠ l ∈ S} uₖuₗ[g(k) ≠ g(l)]/U²
= 1 - Σ_g (U_g/U)²`. -/
lemma sum_offDiag_wtot_ne {G : Type*} [Fintype G] [DecidableEq G] (S : Finset J)
    (grp : J → G) (hU : ∑ l ∈ S, wtot w l ≠ 0) :
    ∑ p ∈ S.offDiag, wtot w p.1 * wtot w p.2 / (∑ l ∈ S, wtot w l) ^ 2
        * (if grp p.1 = grp p.2 then 0 else 1)
      = 1 - ∑ g, (grpVolume w S grp g / ∑ l ∈ S, wtot w l) ^ 2 := by
  rw [sum_offDiag_eq S fun a b => wtot w a * wtot w b / (∑ l ∈ S, wtot w l) ^ 2
    * (if grp a = grp b then 0 else 1)]
  simp only [div_pow, ← Finset.sum_div, sum_grpVolume_sq, ite_true, mul_zero,
    Finset.sum_const_zero, sub_zero]
  have : ∀ a b, wtot w a * wtot w b / (∑ l ∈ S, wtot w l) ^ 2 * (if grp a = grp b then 0 else 1)
      = (wtot w a * wtot w b - wtot w a * wtot w b * (if grp a = grp b then 1 else 0))
        / (∑ l ∈ S, wtot w l) ^ 2 := fun a b => by split_ifs <;> ring
  simp only [this, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp

/-- **Goulet's grand equation (69), two-way, and its bias** (Finding 42). For any nonempty set `S`
of cells, the ANOVA statistic about the grand mean has expectation

  `α²(1 - Σₐ(U_a/U)²) + β²(1 - Σ_b(U_b/U)²) + γ²(1 - Σₖ(uₖ/U)²) - Σ_{k ≠ l}(uₖuₗ/U²)σ²ₖₗρₖₗ`,

`U_a`, `U_b` the row and column volumes. The first three terms are eq. (69) (two-way); the last is
the bias of correlated noise. -/
theorem anovaStat_grand_unbiasedX (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ) (S : Finset J)
    (hS : S.Nonempty) (v : J → (J × T → ℝ) → ℝ)
    (hv : ∀ k, M.UnbiasedX row col α2 β2 γ2 (v k) (M.σ2 k k * M.ρ k k)) :
    M.UnbiasedX row col α2 β2 γ2 (anovaStat w S v)
      (α2 * (1 - ∑ a, (grpVolume w S row a / ∑ l ∈ S, wtot w l) ^ 2)
        + β2 * (1 - ∑ b, (grpVolume w S col b / ∑ l ∈ S, wtot w l) ^ 2)
        + γ2 * (1 - ∑ k ∈ S, (wtot w k / ∑ l ∈ S, wtot w l) ^ 2)
        - ∑ p ∈ S.offDiag, wtot w p.1 * wtot w p.2 / (∑ l ∈ S, wtot w l) ^ 2
          * (M.σ2 p.1 p.2 * M.ρ p.1 p.2)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hU : ∑ l ∈ S, wtot w l ≠ 0 :=
    (Finset.sum_pos (fun l _ => wtot_pos hw l) hS).ne'
  refine (M.anovaStat_unbiasedX row col sig hw hσ hT α2 β2 γ2 S hS v hv).congr (fun _ => rfl) ?_
  rw [← sum_offDiag_wtot_ne S row hU, ← sum_offDiag_wtot_ne S col hU, ← sum_offDiag_wtot S hU,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  field_simp
  ring

/-- …so with noise uncorrelated across the cells of `S` the grand statistic is unbiased for
Goulet's eq. (69) (two-way) exactly. -/
theorem anovaStat_grand_unbiasedX_of_uncorr (hT : 2 ≤ Fintype.card T) (α2 β2 γ2 : ℝ)
    (S : Finset J) (hS : S.Nonempty) (hρ : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → M.ρ k l = 0)
    (v : J → (J × T → ℝ) → ℝ)
    (hv : ∀ k, M.UnbiasedX row col α2 β2 γ2 (v k) (M.σ2 k k * M.ρ k k)) :
    M.UnbiasedX row col α2 β2 γ2 (anovaStat w S v)
      (α2 * (1 - ∑ a, (grpVolume w S row a / ∑ l ∈ S, wtot w l) ^ 2)
        + β2 * (1 - ∑ b, (grpVolume w S col b / ∑ l ∈ S, wtot w l) ^ 2)
        + γ2 * (1 - ∑ k ∈ S, (wtot w k / ∑ l ∈ S, wtot w l) ^ 2)) := by
  refine (M.anovaStat_grand_unbiasedX row col sig hw hσ hT α2 β2 γ2 S hS v hv).congr
    (fun _ => rfl) ?_
  rw [Finset.sum_eq_zero (s := S.offDiag) fun p hp => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    rw [hρ p.1 h1 p.2 h2 h3, mul_zero, mul_zero], sub_zero]

end Model

/-- **A weighted sum of squares is a weighted average of squared pair differences.** With
`W = Σₖ wₖ` and `x̄ = Σₖ wₖxₖ/W`: `Σₖ wₖ(xₖ - x̄)² = Σₖ Σₗ wₖwₗ(xₖ - xₗ)²/(2W)`. So the
analysis-of-variance statistics of crossed-classification credibility (Goulet 1998,
eqs. (67)–(69)) are pools of squared pair differences with weights `∝ wₖwₗ`. -/
theorem sum_mul_sq_sub_eq_pairs {ι : Type*} [Fintype ι] (w x : ι → ℝ) (hW : ∑ k, w k ≠ 0) :
    ∑ k, w k * (x k - (∑ l, w l * x l) / ∑ l, w l) ^ 2
      = (∑ k, ∑ l, w k * w l * (x k - x l) ^ 2) / (2 * ∑ l, w l) := by
  set W := ∑ l, w l
  set S := ∑ l, w l * x l
  have h1 : ∑ k, w k * (x k - S / W) ^ 2 = ∑ k, w k * x k ^ 2 - S ^ 2 / W := by
    have : ∀ k, w k * (x k - S / W) ^ 2
        = w k * x k ^ 2 - 2 * (S / W) * (w k * x k) + (S / W) ^ 2 * w k := fun k => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  have h2 : ∑ k, ∑ l, w k * w l * (x k - x l) ^ 2 = 2 * W * ∑ k, w k * x k ^ 2 - 2 * S ^ 2 := by
    have : ∀ k l, w k * w l * (x k - x l) ^ 2
        = w l * (w k * x k ^ 2) + w k * (w l * x l ^ 2) - 2 * (w k * x k) * (w l * x l) :=
      fun k l => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    ring
  rw [h1, h2]
  field_simp

end Credibility
