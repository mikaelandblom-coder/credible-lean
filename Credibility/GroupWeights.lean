import Mathlib

/-!
# Weights of groups and the share of same-group pairs (extension)

Combinatorics for the group levels of `Hierarchical.lean` (Bridges 4–5):
the indicator `1_g` of a group, the total weight `B_g` a weight vector gives
to it, and the weighted share `π` of same-group pairs among pairs of distinct
cohorts, which is the bias of `τ̂²` with group levels (Finding 13).
-/

namespace Credibility

variable {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G] (grp : J → G)

/-- Indicator `1_g` of group `g`. -/
def grpOne (g : G) : J → ℝ := fun j => if grp j = g then 1 else 0

/-- Total weight `B_g = Σ_{grp i = g} bᵢ` that `b` gives to group `g`. -/
def groupWeight (b : J → ℝ) (g : G) : ℝ := ∑ i, if grp i = g then b i else 0

/-! #### Weighted share of same-group pairs -/

lemma groupWeight_id (b : J → ℝ) (j : J) : groupWeight id b j = b j := by
  simp [groupWeight]

omit [DecidableEq J] in
lemma sum_groupWeight (b : J → ℝ) : ∑ g, groupWeight grp b g = ∑ i, b i := by
  simp only [groupWeight]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq J] in
/-- `Σ_g W_g² = Σ_{g(i) = g(j)} WᵢWⱼ`. -/
lemma sum_groupWeight_sq (W : J → ℝ) :
    ∑ g, groupWeight grp W g ^ 2 = ∑ i, ∑ j, if grp i = grp j then W i * W j else 0 := by
  have h : ∀ g, groupWeight grp W g ^ 2
      = ∑ i, ∑ j, if grp i = g ∧ grp j = g then W i * W j else 0 := fun g => by
    simp only [groupWeight, sq, Finset.sum_mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases hi : grp i = g <;> by_cases hj : grp j = g <;> simp [hi, hj]
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : grp i = grp j
  · simp [hij]
  · simp only [hij, ite_false]
    exact Finset.sum_eq_zero fun g _ => by
      rw [ite_eq_right_iff]; exact fun hg => absurd (hg.1.trans hg.2.symm) hij

omit [DecidableEq J] in
/-- `(Σ Wᵢ)² - Σ_g W_g² = Σ_{g(i) ≠ g(j)} WᵢWⱼ`: the pairs across groups. -/
lemma sq_sum_sub_sum_groupWeight_sq (W : J → ℝ) :
    (∑ i, W i) ^ 2 - ∑ g, groupWeight grp W g ^ 2
      = ∑ i, ∑ j, if grp i = grp j then 0 else W i * W j := by
  rw [sum_groupWeight_sq, sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- The weighted share of same-group pairs among pairs of distinct cohorts,
`π = Σ_{i≠j, g(i)=g(j)} WᵢWⱼ / Σ_{i≠j} WᵢWⱼ` (`withinShare_eq_pairs`). -/
noncomputable def withinShare (W : J → ℝ) : ℝ :=
  (∑ g, groupWeight grp W g ^ 2 - ∑ j, W j ^ 2) / ((∑ j, W j) ^ 2 - ∑ j, W j ^ 2)

lemma withinShare_eq_pairs (W : J → ℝ) :
    withinShare grp W = (∑ i, ∑ j, if i ≠ j ∧ grp i = grp j then W i * W j else 0)
      / ∑ i, ∑ j, if i ≠ j then W i * W j else 0 := by
  have hd := sq_sum_sub_sum_groupWeight_sq (id : J → J) W
  have hn := sq_sum_sub_sum_groupWeight_sq grp W
  simp only [groupWeight_id, id] at hd
  rw [withinShare]
  congr 1
  · have : ∑ g, groupWeight grp W g ^ 2 - ∑ j, W j ^ 2
        = ((∑ i, W i) ^ 2 - ∑ j, W j ^ 2) - ((∑ i, W i) ^ 2 - ∑ g, groupWeight grp W g ^ 2) := by
      ring
    rw [this, hd, hn, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · subst h; simp
    · by_cases hg : grp i = grp j <;> simp [h, hg]
  · rw [hd]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases h : i = j <;> simp [h]

omit [Fintype G] [DecidableEq G] in
/-- With positive weights and two cohorts, the pairs of distinct cohorts have positive weight. -/
lemma sq_sum_sub_sum_sq_pos {W : J → ℝ} (hW : ∀ j, 0 < W j) (hJ : 2 ≤ Fintype.card J) :
    0 < (∑ j, W j) ^ 2 - ∑ j, W j ^ 2 := by
  have hd := sq_sum_sub_sum_groupWeight_sq (id : J → J) W
  simp only [groupWeight_id, id] at hd
  rw [hd]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card J)
  have hnn : ∀ i j, 0 ≤ (if i = j then 0 else W i * W j) := fun i j => by
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hW i) (hW j)).le
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) ⟨a, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun j _ => hnn a j) ⟨b, Finset.mem_univ _, ?_⟩
  simp [hab, mul_pos (hW a) (hW b)]

/-- `π = 1` (no pairs across groups) exactly when there is one group. -/
lemma withinShare_eq_one_iff {W : J → ℝ} (hW : ∀ j, 0 < W j) (hJ : 2 ≤ Fintype.card J) :
    withinShare grp W = 1 ↔ ∀ i j, grp i = grp j := by
  have hD := sq_sum_sub_sum_sq_pos hW hJ
  have hn := sq_sum_sub_sum_groupWeight_sq grp W
  have hnn : ∀ i j, 0 ≤ (if grp i = grp j then 0 else W i * W j) := fun i j => by
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hW i) (hW j)).le
  rw [withinShare, div_eq_one_iff_eq hD.ne']
  constructor
  · intro h i j
    have h0 : ∑ i, ∑ j, (if grp i = grp j then 0 else W i * W j) = 0 := by
      rw [← hn]; linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hnn i j).mp h0 i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j).mp hi j (Finset.mem_univ _)
    by_contra hg
    simp only [hg, ite_false] at hij
    exact (mul_pos (hW i) (hW j)).ne' hij
  · intro h
    have h0 : ∑ i, ∑ j, (if grp i = grp j then 0 else W i * W j) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [h i j]
    linarith

end Credibility
