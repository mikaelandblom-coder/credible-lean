import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Optimal one-dimensional weighted k-means groups are intervals

Points `x i ∈ ℝ` with positive weights `w i` are given labels `c i` and each
label `a` a center `μ a`; the cost is `∑ i, w i * (x i - μ (c i))^2`. In a
jointly optimal labelling and choice of centers, every group is an interval of
the sorted values: if `x i < x j < x l` and `i`, `l` share a group, so does `j`.
Hence optimal groups can be found exactly by dynamic programming over the
sorted values (Fisher 1958; Nielsen & Nock, arXiv:1403.2485).

Not in the thesis; README "Later goals → Small lemmas" (a).

Proof: every point sits at a nearest center (else moving it lowers the cost).
`t ↦ (t - μ a)^2 - (t - μ b)^2` is affine, so `j` between `i` and `l` cannot be
closer to `μ b` unless `μ a = μ b`. Then merging `a` and `b` is free and the
freed label can isolate a point off its center, lowering the cost strictly.
-/

open Finset

namespace Credibility

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- Weighted k-means cost of labels `c` with centers `μ`. -/
def kmeansCost (w x : ι → ℝ) (c : ι → κ) (μ : κ → ℝ) : ℝ :=
  ∑ i, w i * (x i - μ (c i)) ^ 2

omit [DecidableEq κ] in
/-- Relabelling one point changes the cost only in its own term. -/
theorem kmeansCost_update (w x : ι → ℝ) (c : ι → κ) (μ : κ → ℝ) (j : ι) (b : κ) :
    kmeansCost w x (Function.update c j b) μ - kmeansCost w x c μ
      = w j * ((x j - μ b) ^ 2 - (x j - μ (c j)) ^ 2) := by
  unfold kmeansCost
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp; ring
  · intro m _ hm; simp [Function.update_of_ne hm]
  · simp

omit [DecidableEq κ] in
/-- In an optimal clustering every point sits at a nearest center. -/
theorem kmeans_nearest {w x : ι → ℝ} {c : ι → κ} {μ : κ → ℝ} (hw : ∀ i, 0 < w i)
    (hopt : ∀ (c' : ι → κ) (μ' : κ → ℝ), kmeansCost w x c μ ≤ kmeansCost w x c' μ')
    (j : ι) (b : κ) : (x j - μ (c j)) ^ 2 ≤ (x j - μ b) ^ 2 := by
  have h := kmeansCost_update w x c μ j b
  have := hopt (Function.update c j b) μ
  have h' : 0 ≤ w j * ((x j - μ b) ^ 2 - (x j - μ (c j)) ^ 2) := by linarith
  have := (mul_nonneg_iff_of_pos_left (hw j)).mp h'
  linarith

/-- **Optimal 1-D weighted k-means groups are contiguous.** For positive
weights, in a jointly optimal choice of labels `c` and centers `μ`, a point
lying strictly between two points of the same group belongs to that group. -/
theorem kmeans_contiguous {w x : ι → ℝ} {c : ι → κ} {μ : κ → ℝ} (hw : ∀ i, 0 < w i)
    (hopt : ∀ (c' : ι → κ) (μ' : κ → ℝ), kmeansCost w x c μ ≤ kmeansCost w x c' μ')
    {i j l : ι} (hij : x i < x j) (hjl : x j < x l) (hil : c i = c l) :
    c j = c i := by
  by_contra hb
  set a := c i
  set b := c j
  have hl : c l = a := hil.symm
  by_cases hμ : μ a = μ b
  · -- equal centers: merge `b` into `a`, isolate an off-center point of `a`
    obtain ⟨p, hpa, hp⟩ : ∃ p, c p = a ∧ x p ≠ μ a := by
      by_cases h : x i = μ a
      · exact ⟨l, hl, by linarith⟩
      · exact ⟨i, rfl, h⟩
    have hab : a ≠ b := Ne.symm hb
    let c' : ι → κ := fun m => if m = p then b else if c m = b then a else c m
    let μ' : κ → ℝ := Function.update μ b (x p)
    have hle : ∀ m ∈ univ, w m * (x m - μ' (c' m)) ^ 2 ≤ w m * (x m - μ (c m)) ^ 2 := by
      intro m _
      by_cases hm : m = p
      · subst hm
        simp [c', μ']
        exact mul_nonneg (hw m).le (sq_nonneg _)
      · by_cases hcm : c m = b
        · simp [c', μ', hm, hcm, Function.update_of_ne hab, hμ]
        · simp [c', μ', hm, hcm]
    have hlt : w p * (x p - μ' (c' p)) ^ 2 < w p * (x p - μ (c p)) ^ 2 := by
      simp only [c', μ', ↓reduceIte, Function.update_self, sub_self, hpa]
      have : 0 < (x p - μ a) ^ 2 := by
        have : x p - μ a ≠ 0 := sub_ne_zero.mpr hp
        positivity
      simpa using mul_pos (hw p) this
    have := Finset.sum_lt_sum hle ⟨p, mem_univ _, hlt⟩
    have := hopt c' μ'
    unfold kmeansCost at *
    linarith
  · -- distinct centers: the affine comparison function changes sign twice
    have h1 := kmeans_nearest hw hopt i b
    have h2 := kmeans_nearest hw hopt l b
    have h3 := kmeans_nearest hw hopt j a
    rw [hl] at h2
    change (x i - μ a) ^ 2 ≤ (x i - μ b) ^ 2 at h1
    change (x j - μ b) ^ 2 ≤ (x j - μ a) ^ 2 at h3
    rcases lt_or_gt_of_ne hμ with h | h
    · -- μ a < μ b forces `2 x l ≤ μ a + μ b ≤ 2 x j`
      nlinarith
    · -- μ b < μ a forces `2 x j ≤ μ a + μ b ≤ 2 x i`
      nlinarith

end Credibility
