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
