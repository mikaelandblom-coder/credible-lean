import Mathlib.Tactic

/-!
# Damping as shrinkage (PLAN G2)

Damping multiplies the off-diagonal estimates `ŝᵢⱼ` by `θ`, i.e. shrinks them linearly towards
the target `0`. Take each estimate's mean `sᵢⱼ` and variance `Vᵢⱼ` as given numbers (they need
fourth moments, `studies/damping-theta.md` S7). Then the stand-in loss
`E Σ (θŝᵢⱼ - sᵢⱼ)² = Σ (θ²(sᵢⱼ² + Vᵢⱼ) - 2θsᵢⱼ² + sᵢⱼ²)` is a parabola in `θ` with vertex
`θ* = Σs²/(Σs² + ΣV)`, the zero-target shrinkage intensity of Ledoit–Wolf (2004) and
Schäfer–Strimmer (2005). A `θ` beats both no damping (`θ = 1`) and dropping the correlations
(`θ = 0`) exactly when `|θ - θ*| ≤ min(θ*, 1 - θ*)`. This is about the covariance table; its link
to the rates' MSE is numerical only (S12).
-/

open Finset

namespace Credibility.Damping

variable {ι : Type*} (S : Finset ι) (s V : ι → ℝ)

/-- `E Σ (θŝᵢ - sᵢ)²` for estimates `ŝᵢ` with mean `sᵢ` and variance `Vᵢ`. -/
def loss (θ : ℝ) : ℝ := ∑ i ∈ S, (θ ^ 2 * (s i ^ 2 + V i) - 2 * θ * s i ^ 2 + s i ^ 2)

/-- `Σ sᵢ²`, the signal. -/
def signal : ℝ := ∑ i ∈ S, s i ^ 2

/-- `Σ Vᵢ`, the noise. -/
def noise : ℝ := ∑ i ∈ S, V i

/-- The optimal intensity `θ* = Σs²/(Σs² + ΣV)`. -/
noncomputable def bestTheta : ℝ := signal S s / (signal S s + noise S V)

lemma loss_eq_poly (θ : ℝ) :
    loss S s V θ = θ ^ 2 * (signal S s + noise S V) - 2 * θ * signal S s + signal S s := by
  simp only [loss, signal, noise, sum_add_distrib, sum_sub_distrib, ← mul_sum, mul_add]

/-- The loss is a parabola with vertex `θ*`. -/
theorem loss_eq (h : signal S s + noise S V ≠ 0) (θ : ℝ) :
    loss S s V θ = loss S s V (bestTheta S s V)
      + (signal S s + noise S V) * (θ - bestTheta S s V) ^ 2 := by
  rw [loss_eq_poly, loss_eq_poly, bestTheta]
  field_simp
  ring

/-- `θ*` minimises the loss. -/
theorem bestTheta_optimal (h : 0 < signal S s + noise S V) (θ : ℝ) :
    loss S s V (bestTheta S s V) ≤ loss S s V θ := by
  rw [loss_eq S s V h.ne' θ]
  nlinarith [sq_nonneg (θ - bestTheta S s V)]

/-- With nonnegative variances, `θ* ∈ [0, 1]`. -/
theorem bestTheta_mem (hV : ∀ i ∈ S, 0 ≤ V i) : 0 ≤ bestTheta S s V ∧ bestTheta S s V ≤ 1 := by
  have hs : 0 ≤ signal S s := sum_nonneg fun i _ => sq_nonneg (s i)
  have hn : 0 ≤ noise S V := sum_nonneg hV
  refine ⟨div_nonneg hs (add_nonneg hs hn), div_le_one_of_le₀ (by linarith) (add_nonneg hs hn)⟩

/-- The minimum loss `Σs²·ΣV/(Σs² + ΣV)`, at most the loss of either extreme. -/
theorem loss_bestTheta (h : signal S s + noise S V ≠ 0) :
    loss S s V (bestTheta S s V)
      = signal S s * noise S V / (signal S s + noise S V) := by
  rw [loss_eq_poly, bestTheta]
  field_simp
  ring

lemma loss_one : loss S s V 1 = noise S V := by rw [loss_eq_poly]; ring

lemma loss_zero : loss S s V 0 = signal S s := by rw [loss_eq_poly]; ring

/-- Damping by `θ` is no worse than no damping (`θ = 1`) iff `θ ∈ [2θ* - 1, 1]`. -/
theorem loss_le_one_iff (h : 0 < signal S s + noise S V) (hV : ∀ i ∈ S, 0 ≤ V i) (θ : ℝ) :
    loss S s V θ ≤ loss S s V 1 ↔ 2 * bestTheta S s V - 1 ≤ θ ∧ θ ≤ 1 := by
  have hb := (bestTheta_mem S s V hV).2
  rw [loss_eq S s V h.ne' θ, loss_eq S s V h.ne' 1, add_le_add_iff_left,
    mul_le_mul_iff_of_pos_left h, sq_le_sq, abs_le, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - _)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Damping by `θ` is no worse than dropping the correlations (`θ = 0`) iff `θ ∈ [0, 2θ*]`. -/
theorem loss_le_zero_iff (h : 0 < signal S s + noise S V) (hV : ∀ i ∈ S, 0 ≤ V i) (θ : ℝ) :
    loss S s V θ ≤ loss S s V 0 ↔ 0 ≤ θ ∧ θ ≤ 2 * bestTheta S s V := by
  have hb := (bestTheta_mem S s V hV).1
  rw [loss_eq S s V h.ne' θ, loss_eq S s V h.ne' 0, add_le_add_iff_left,
    mul_le_mul_iff_of_pos_left h, sq_le_sq, abs_le, zero_sub, abs_neg, abs_of_nonneg hb]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- PLAN G2, the safe `θ`: it beats both extremes iff it lies within `min(θ*, 1 - θ*)` of `θ*`.
Such `θ` always exist (`θ*` itself). -/
theorem safe_iff (h : 0 < signal S s + noise S V) (hV : ∀ i ∈ S, 0 ≤ V i) (θ : ℝ) :
    (loss S s V θ ≤ loss S s V 1 ∧ loss S s V θ ≤ loss S s V 0)
      ↔ |θ - bestTheta S s V| ≤ min (bestTheta S s V) (1 - bestTheta S s V) := by
  rw [loss_le_one_iff S s V h hV, loss_le_zero_iff S s V h hV, abs_le]
  rcases min_cases (bestTheta S s V) (1 - bestTheta S s V) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
    constructor
  all_goals first
    | (rintro ⟨⟨h1, h2⟩, h3, h4⟩; constructor <;> linarith)
    | (rintro ⟨h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)

/-- One entry: `θ* = s²/(s² + V)`. With `s = ρ` and the normal-theory `V = (1 - ρ²)²/(T - 1)` of
a sample correlation this is the app's rule `θ̂ = r̄²/(r̄² + (1 - r̄²)²/(T - 1))`, with `r̄` for
`ρ`. -/
theorem bestTheta_single (i : ι) : bestTheta {i} s V = s i ^ 2 / (s i ^ 2 + V i) := by
  simp [bestTheta, signal, noise]

end Credibility.Damping
