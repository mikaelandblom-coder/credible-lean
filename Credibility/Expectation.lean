import Credibility.Model

/-!
# Expectation of quadratic estimators (thesis §2.8)

Second moments are given numbers, as elsewhere. Observations `μⱼₜ` have mean `μ`
and covariance `Model.obsCov`, so `E[μᵢₜ μⱼₛ] = obsCov + μ²` is our *definition*
of the second moment (`mom2`). The estimators of §2.8 are quadratic forms in the
data, so their expectation is a finite sum (`E`), and `Unbiased f θ` says that `f`
is such a form with expectation `θ` for every `μ`. `E_congr` shows that this
expectation depends only on the function `f`, not on the matrix chosen for it.

Data are indexed by `p = (j, t) : J × T`. Used by `Estimation.lean` and
`UnequalEstimation.lean`.
-/

open Finset

namespace Credibility.Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-! ### Expectation of quadratic estimators -/

/-- The quadratic form `Σₚ,q Qₚq Xₚ Xq` in the data `X`. -/
def quad (Q : J × T → J × T → ℝ) (X : J × T → ℝ) : ℝ := ∑ p, ∑ q, Q p q * X p * X q

/-- Second moment `E[μᵢₜ μⱼₛ] = cov(μᵢₜ, μⱼₛ) + μ²`, eq. (16) plus the mean `μ`. -/
def mom2 (μ : ℝ) (p q : J × T) : ℝ := M.obsCov p.1 q.1 p.2 q.2 + μ ^ 2

/-- Expectation of the quadratic form `quad Q`. -/
def E (μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ := ∑ p, ∑ q, Q p q * M.mom2 μ p q

/-- The expectation depends only on the estimator, not on the matrix representing it. -/
lemma E_congr (μ : ℝ) {Q Q' : J × T → J × T → ℝ} (h : ∀ X, quad Q X = quad Q' X) :
    M.E μ Q = M.E μ Q' := by
  set D : J × T → J × T → ℝ := fun p q => Q p q - Q' p q with hD
  have h0 : ∀ X, quad D X = 0 := fun X => by
    have := h X
    simp only [quad, hD, sub_mul, sum_sub_distrib] at *
    linarith
  -- Polarization: `D` is antisymmetric.
  have hanti : ∀ p q, D q p = -D p q := by
    intro p q
    have h1 := h0 (Pi.single p 1 + Pi.single q 1)
    have h2 := h0 (Pi.single p 1)
    have h3 := h0 (Pi.single q 1)
    simp only [quad, Pi.add_apply, Pi.single_apply, mul_add, sum_add_distrib, mul_ite,
      mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h1 h2 h3
    linarith
  have hsymm : ∀ p q, M.mom2 μ q p = M.mom2 μ p q := by
    intro p q
    simp only [mom2, obsCov, M.ρ_symm q.1 p.1, eq_comm (a := q.2), eq_comm (a := q.1)]
    ring
  have hE : M.E μ D = -M.E μ D := by
    conv_lhs => rw [E, sum_comm]
    simp only [E, ← sum_neg_distrib]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    rw [hanti, hsymm]; ring
  have : M.E μ D = 0 := by linarith
  simp only [E, hD, sub_mul, sum_sub_distrib] at this
  simp only [E]; linarith

/-- `f` is unbiased for `θ`: a quadratic form in the data whose expectation is
`θ` whatever the mean `μ`. -/
def Unbiased (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ μ, M.E μ Q = θ

variable {M} in
/-- Unbiasedness is about the function and the value, not their presentation. -/
lemma Unbiased.congr {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (h : M.Unbiased f θ)
    (hf : ∀ X, f X = g X) (hθ : θ = θ') : M.Unbiased g θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨Q, fun X => (hQ X).trans (hf X), fun μ => (hE μ).trans hθ⟩

variable {M} in
/-- Linearity: sums. -/
lemma Unbiased.add {f g : (J × T → ℝ) → ℝ} {θ φ : ℝ} (hf : M.Unbiased f θ)
    (hg : M.Unbiased g φ) : M.Unbiased (fun X => f X + g X) (θ + φ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hg
  refine ⟨fun p q => Q p q + Q' p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ, ← hQ']; simp only [quad, add_mul, sum_add_distrib]
  · rw [← hE μ, ← hE' μ]; simp only [E, add_mul, sum_add_distrib]

variable {M} in
/-- Linearity: scalar multiples. -/
lemma Unbiased.const_mul {f : (J × T → ℝ) → ℝ} {θ : ℝ} (c : ℝ) (hf : M.Unbiased f θ) :
    M.Unbiased (fun X => c * f X) (c * θ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  refine ⟨fun p q => c * Q p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ]; simp only [quad, mul_sum, mul_assoc]
  · rw [← hE μ]; simp only [E, mul_sum, mul_assoc]

variable {M} in
/-- Linearity: finite sums. -/
lemma Unbiased.sum {ι : Type*} (s : Finset ι) {f : ι → (J × T → ℝ) → ℝ} {θ : ι → ℝ}
    (hf : ∀ k ∈ s, M.Unbiased (f k) (θ k)) :
    M.Unbiased (fun X => ∑ k ∈ s, f k X) (∑ k ∈ s, θ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun X => by simp [quad], fun μ => by simp [E]⟩
  | insert k s hk ih =>
    simp only [sum_insert hk]
    exact (hf k (mem_insert_self k s)).add (ih fun k' hk' => hf k' (mem_insert_of_mem hk'))

/-- The product of two linear forms, the first with coefficients summing to `0`
(so the mean `μ` drops out), has expectation `cov(ℓᵀX, mᵀX)`. -/
lemma unbiased_mul (ℓ m : J × T → ℝ) (hℓ : ∑ p, ℓ p = 0) :
    M.Unbiased (fun X => (∑ p, ℓ p * X p) * (∑ q, m q * X q))
      (∑ p, ∑ q, ℓ p * m q * M.obsCov p.1 q.1 p.2 q.2) := by
  refine ⟨fun p q => ℓ p * m q, fun X => ?_, fun μ => ?_⟩
  · simp only [quad, sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  · have h0 : ∑ p, ∑ q, ℓ p * m q * μ ^ 2 = 0 := by
      simp_rw [mul_assoc, ← mul_sum, ← sum_mul, hℓ, zero_mul]
    simp only [E, mom2, mul_add, sum_add_distrib, h0, add_zero]

end Credibility.Model
