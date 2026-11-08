import Mathlib

/-!
# Shrinking the off-diagonal entries of a positive semidefinite matrix

Multiplying the off-diagonal entries of a positive semidefinite matrix `A` by
`ρ ∈ [0,1]` keeps it positive semidefinite, and positive definite if `ρ < 1`
and the diagonal is positive. The new matrix is `ρ • A + (1 - ρ) • diag(A)`,
a convex combination of two positive semidefinite matrices; for `ρ < 1` the
diagonal part is positive definite.

Not in the thesis; README "Later goals → Small lemmas" (b), from the
clustering paper (a covariance matrix `τ` with damped correlations).
-/

open Matrix

namespace Credibility

variable {n : Type*} [DecidableEq n]

/-- `A` with its off-diagonal entries multiplied by `ρ`. -/
def shrinkOffDiag (ρ : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if i = j then A i j else ρ * A i j

/-- The shrunk matrix is `ρ • A + (1 - ρ) • diag(A)`. -/
theorem shrinkOffDiag_eq (ρ : ℝ) (A : Matrix n n ℝ) :
    shrinkOffDiag ρ A = ρ • A + (1 - ρ) • diagonal A.diag := by
  ext i j
  by_cases h : i = j
  · subst h; simp [shrinkOffDiag]; ring
  · simp [shrinkOffDiag, h]

/-- Shrinking the off-diagonal entries by `ρ ∈ [0,1]` keeps a matrix positive
semidefinite. -/
theorem posSemidef_shrinkOffDiag {A : Matrix n n ℝ} (hA : A.PosSemidef) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : (shrinkOffDiag ρ A).PosSemidef := by
  rw [shrinkOffDiag_eq]
  exact (hA.smul h0).add
    ((PosSemidef.diagonal fun i => hA.diag_nonneg).smul (sub_nonneg.mpr h1))

/-- …and positive definite if `ρ < 1` and the diagonal is positive. -/
theorem posDef_shrinkOffDiag {A : Matrix n n ℝ} (hA : A.PosSemidef) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hd : ∀ i, 0 < A i i) : (shrinkOffDiag ρ A).PosDef := by
  rw [shrinkOffDiag_eq]
  exact PosDef.posSemidef_add (hA.smul h0) ((PosDef.diagonal hd).smul (sub_pos.mpr h1))

end Credibility
