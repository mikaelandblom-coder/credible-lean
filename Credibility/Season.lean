import Credibility.BlupMoments
import Credibility.Core
import Credibility.Unequal

/-!
# The season and the 12-month target (extension, `notes/card-data.md` Step 2)

The season is additive on the rate: a cell `i` (card × month) has mean `β_{m(i)}`, one fixed
effect per calendar month `m`, and the target has mean `Σₘ cₘβₘ` (`cₘ = 1`: the total over
the next 12 months). This is `Core.blup` with the season design `X = design mon` (cell ↦ its
month). An unbiased predictor needs each month's weights to sum to `cₘ` (`monthSum`).

* **When the season drops out** (`blup_eq_iff`): the seasonal predictor is the one-mean
  predictor iff the one-mean `d*` already has month sums `cₘ`; the general form is
  `Core.blup_eq_blup_iff_of_nested`. Sufficient: the months are interchangeable
  (`blup_eq_of_interchangeable`), e.g. whole years and a model unchanged by a calendar shift.
* **It does not in general** (`blup_ne_of_volume`, Finding 24): whole years of one card and
  independent noise, but more volume in one month. The one-mean predictor overweights that month,
  so it is biased whenever the season is real (`Target.integral_bias`).
* **A known index `cₜ`** (multiplicative) is not a fixed effect: divide the data by `cₜ` and the
  thesis model `Unequal` applies. Under Poisson-type variance the cell weights are expected
  claims `cₜwⱼₜ`, not cards in force (`Unequal.a_eq_of_volume`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory Credibility.Core

namespace Credibility
namespace Season

variable {n Mo : Type*} [Fintype n] [Fintype Mo] [DecidableEq n] [DecidableEq Mo]

/-- The season design: cell `i` has the indicator of its calendar month `mon i`. -/
def design (mon : n → Mo) : Matrix n Mo ℝ := fun i m => if mon i = m then 1 else 0

/-- The sum of the weights on the cells of month `m`. -/
def monthSum (mon : n → Mo) (d : n → ℝ) (m : Mo) : ℝ := ∑ i, if mon i = m then d i else 0

omit [Fintype Mo] [DecidableEq n] in
/-- `Xᵀd` for the season design is the vector of month sums: an unbiased predictor of
`Σₘ cₘβₘ` has `monthSum = c`. -/
theorem design_transpose_mulVec (mon : n → Mo) (d : n → ℝ) :
    (design mon)ᵀ *ᵥ d = monthSum mon d := by
  funext m
  simp [mulVec, dotProduct, design, monthSum, ite_mul]

omit [Fintype n] [DecidableEq n] in
/-- One common mean is the season design with all months equal: `X₁ = X₂ 1`. -/
theorem design_mul_one (mon : n → Mo) :
    design mon * replicateCol Unit (1 : Mo → ℝ) = replicateCol Unit (1 : n → ℝ) := by
  ext i u
  simp [design, Matrix.mul_apply, replicateCol]

omit [Fintype n] [DecidableEq n] in
/-- With every month observed, the season design has full column rank. -/
theorem design_mulVec_injective {mon : n → Mo} (hmon : Function.Surjective mon) :
    Function.Injective (design mon).mulVec := by
  intro x y h
  funext m
  obtain ⟨i, rfl⟩ := hmon m
  simpa [mulVec, dotProduct, design] using congrFun h i

omit [DecidableEq n] in
/-- The month sums add up to the total weight. -/
theorem sum_monthSum (mon : n → Mo) (d : n → ℝ) : ∑ m, monthSum mon d m = ∑ i, d i := by
  simp only [monthSum]
  rw [Finset.sum_comm]
  simp

/-- **When the season drops out**: the predictor with an estimated season equals the one-mean
predictor (target mean `Σₘ cₘ` times the common mean) iff the one-mean `d*` already has month
sums `cₘ`. -/
theorem blup_eq_iff {K : Matrix n n ℝ} (hK : K.PosDef) {mon : n → Mo}
    (hmon : Function.Surjective mon) (ℓ : n → ℝ) (c : Mo → ℝ) :
    blup K (design mon) ℓ c = blup K (replicateCol Unit 1) ℓ (fun _ => ∑ m, c m)
      ↔ ∀ m, monthSum mon (blup K (replicateCol Unit 1) ℓ (fun _ => ∑ m, c m)) m = c m := by
  have h := blup_eq_blup_iff_of_nested hK (design_mulVec_injective hmon)
    (replicateCol Unit (1 : Mo → ℝ)) ℓ c
  rw [design_mul_one, replicateCol_one_transpose_mulVec] at h
  rw [h, design_transpose_mulVec, funext_iff]

/-- **Interchangeable months**: if for any two months some relabelling of the cells maps
the first month's cells onto the second's and leaves `K` and `ℓ` unchanged, the season drops
out of the predictor of an equally weighted target (e.g. the 12-month total). -/
theorem blup_eq_of_interchangeable [Nonempty n] {K : Matrix n n ℝ} (hK : K.PosDef)
    {mon : n → Mo} (hmon : Function.Surjective mon) (ℓ : n → ℝ) (c₀ : ℝ)
    (hσ : ∀ m m', ∃ σ : n ≃ n, (∀ i j, K (σ i) (σ j) = K i j) ∧ (∀ i, ℓ (σ i) = ℓ i) ∧
      ∀ i, (mon (σ i) = m' ↔ mon i = m)) :
    blup K (design mon) ℓ (fun _ => c₀)
      = blup K (replicateCol Unit 1) ℓ (fun _ => ∑ _m : Mo, c₀) := by
  set e := blup K (replicateCol Unit (1 : n → ℝ)) ℓ (fun _ => ∑ _m : Mo, c₀)
  -- The relabellings leave `e` unchanged, so all months carry the same weight.
  have hS : ∀ m m', monthSum mon e m' = monthSum mon e m := by
    intro m m'
    obtain ⟨σ, hKσ, hℓσ, hmσ⟩ := hσ m m'
    have he : e ∘ σ = e := blup_comp_equiv hK replicateCol_one_mulVec_injective ℓ _ σ hKσ hℓσ
      (fun i => by funext u; simp [replicateCol])
    simp only [monthSum]
    rw [← Equiv.sum_comp σ (fun i => if mon i = m' then e i else 0)]
    refine sum_congr rfl fun i _ => ?_
    simp only [hmσ, show e (σ i) = e i from congrFun he i]
  -- The weights add up to `|months| c₀`, so each month carries `c₀`.
  have htot : ∑ i, e i = ∑ _m : Mo, c₀ := by
    have := congrFun (transpose_mulVec_blup hK replicateCol_one_mulVec_injective ℓ
      (fun _ : Unit => ∑ _m : Mo, c₀)) ()
    rwa [replicateCol_one_transpose_mulVec] at this
  refine (blup_eq_iff hK hmon ℓ (fun _ => c₀)).mpr fun m => ?_
  have h := sum_monthSum mon e
  have : Nonempty Mo := ⟨m⟩
  have hm : Fintype.card Mo ≠ 0 := Fintype.card_ne_zero
  simp only [hS m, htot, sum_const, card_univ, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hm) h

/-- **The season does not drop out** (Finding 24). One card, two years of two months, whole
years, independent noise; the first month has twice the volume (variance `1` against `2`). The
target is next year's total (`c = 1`), with no random effect (`ℓ = 0`). The one-mean
predictor puts `4/3` on the first month and `2/3` on the second, so it differs from the seasonal
one (and is biased by `(β₁ - β₂)/3` when the season is real). -/
theorem blup_ne_of_volume :
    blup (diagonal ![1, 2, 1, 2]) (design ![(0 : Fin 2), 1, 0, 1]) 0 1
      ≠ blup (diagonal ![1, 2, 1, 2]) (replicateCol Unit 1) 0 (fun _ => ∑ m, (1 : Fin 2 → ℝ) m) := by
  have hK : (diagonal ![(1 : ℝ), 2, 1, 2]).PosDef := by
    rw [posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have hmon : Function.Surjective ![(0 : Fin 2), 1, 0, 1] := by
    intro m; fin_cases m
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  -- The one-mean weights are `(2/3, 1/3, 2/3, 1/3)`: `Kd = (2/3)1` and `Σ d = 2`.
  have he : ![(2 / 3 : ℝ), 1 / 3, 2 / 3, 1 / 3]
      = blup (diagonal ![1, 2, 1, 2]) (replicateCol Unit 1) 0
          (fun _ => ∑ m, (1 : Fin 2 → ℝ) m) := by
    refine eq_blup_of_normal hK replicateCol_one_mulVec_injective 0 _ (c := fun _ => 2 / 3) ?_ ?_
    · funext i
      rw [Pi.sub_apply, mulVec_diagonal]
      fin_cases i <;> simp [mulVec, dotProduct, replicateCol] <;> norm_num
    · rw [replicateCol_one_transpose_mulVec]
      funext u
      simp [Fin.sum_univ_four]
      norm_num
  intro h
  have h0 := (blup_eq_iff hK hmon 0 1).mp h 0
  rw [← he] at h0
  simp [monthSum, Fin.sum_univ_four] at h0
  norm_num at h0

end Season

namespace Core.Target

open Season

variable {Ω : Type*} [MeasurableSpace Ω] {n Mo : Type*} [Fintype n] [Fintype Mo]
  [DecidableEq Mo] {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {mon : n → Mo} {c β : Mo → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The bias of ignoring the season**: in a world with season `β`, a linear predictor `dᵀx`
of `Y` has bias `Σₘ (monthSum d m - cₘ) βₘ`. -/
theorem integral_bias (T : Target K ℓ v (design mon) c β P) (d : n → ℝ) :
    P[portLin T.x d] - P[T.Y] = ∑ m, (monthSum mon d m - c m) * β m := by
  rw [T.integral_portLin, T.Y_mean, design_transpose_mulVec]
  simp only [dotProduct, ← sum_sub_distrib, sub_mul]

end Core.Target

namespace Unequal

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- **A known index, Poisson-type variance**: if the noise variance of cohort `j` is
`σⱼₜ² = s²/volₜ` (for a deseasoned rate `Xⱼₜ/cₜ` with Poisson-type counts: `volₜ = cₜwⱼₜ`,
expected claims), the cell weights of eq. (23) are `volₜ / Σ_{s∈Tⱼ} vol_s`. -/
theorem a_eq_of_volume (M : Unequal J T) (j : J) {s2 : ℝ} {vol : T → ℝ}
    (hvol : ∀ t ∈ M.obs j, 0 < vol t) (hσ : ∀ t ∈ M.obs j, M.σ j t ^ 2 = s2 / vol t)
    {t : T} (ht : t ∈ M.obs j) : M.a j t = vol t / ∑ s ∈ M.obs j, vol s := by
  have hs2 : 0 < s2 := by
    have h := hσ t ht
    rw [eq_div_iff (hvol t ht).ne'] at h
    rw [← h]
    exact mul_pos (pow_pos (M.σ_pos j t) 2) (hvol t ht)
  have hinv : ∀ s ∈ M.obs j, (M.σ j s ^ 2)⁻¹ = vol s / s2 := fun s hs => by
    rw [hσ s hs, inv_div]
  unfold a
  rw [ite_eq_left ht, hinv t ht, sum_congr rfl hinv, ← sum_div,
    div_div_div_cancel_right₀ hs2.ne']

end Unequal

end Credibility
