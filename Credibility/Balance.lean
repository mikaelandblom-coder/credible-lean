import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# The balance property of Bühlmann–Straub weights (thesis §2.9)

Pure algebra about the credibility-weighted mean, for any data. Used by the
Bühlmann–Straub case (`BuhlmannStraub.lean`) and its version with unequal
lengths (`UnequalEstimation.lean`).
-/

open Finset

namespace Credibility

variable {J : Type*} [Fintype J]

/-- The balance property (§2.9) holds for Bühlmann–Straub weights for any data,
whether or not the model assumptions hold. Here `W j = wⱼ*`, `κ = σ²/τ²`,
and `m j` is the cohort estimate `μ̂ⱼ`. -/
theorem bs_balance [Nonempty J] (W : J → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ∀ j, 0 < W j)
    (m : J → ℝ) :
    let z := fun j => W j / (W j + κ)
    let mhat := (∑ j, z j * m j) / ∑ j, z j
    ∑ j, W j * (1 - z j) * (m j - mhat) = 0 := by
  intro z mhat
  -- `Wⱼ(1 - zⱼ) = κ zⱼ`, so the sum is `κ(Σ zⱼmⱼ - μ̂ Σ zⱼ) = 0`.
  have hz : ∀ j, W j * (1 - z j) = κ * z j := fun j => by
    have := (hW j).ne'; have : W j + κ ≠ 0 := (add_pos (hW j) hκ).ne'
    simp only [z]; field_simp; ring
  have hpos : 0 < ∑ j, z j :=
    sum_pos (fun j _ => div_pos (hW j) (add_pos (hW j) hκ)) univ_nonempty
  simp only [hz, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul, mhat]
  field_simp
  simp only [mul_assoc, ← mul_sum]
  ring

end Credibility
