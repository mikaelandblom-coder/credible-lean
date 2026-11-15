import Credibility.Core

/-!
# The balance property of Bühlmann–Straub weights (thesis §2.9)

Pure algebra about the credibility-weighted mean, for any data: the Bühlmann–Straub
case of the general balance lemma `Core.balanced_iff`. Used by the
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
  -- With `bⱼ = zⱼ/z*`, `Wⱼ(1 - zⱼ) = κzⱼ = κz*·bⱼ`, so `Core.balanced_iff` applies.
  have hz : ∀ j, W j * (1 - z j) = κ * z j := fun j => by
    have := (hW j).ne'; have : W j + κ ≠ 0 := (add_pos (hW j) hκ).ne'
    simp only [z]; field_simp; ring
  have hpos : 0 < ∑ j, z j :=
    sum_pos (fun j _ => div_pos (hW j) (add_pos (hW j) hκ)) univ_nonempty
  set b := fun j => z j / ∑ i, z i
  have hb : ∑ j, b j = 1 := by simp only [b, ← sum_div]; exact div_self hpos.ne'
  have hm : ∑ i, b i * m i = mhat := by simp only [b, mhat, div_mul_eq_mul_div, ← sum_div]
  have key := (Core.balanced_iff W z b hb).mpr
    ⟨κ * ∑ i, z i, fun j => by rw [hz]; simp only [b]; field_simp⟩ m
  rwa [Core.sum_mul_sub_blend, hm] at key

end Credibility
