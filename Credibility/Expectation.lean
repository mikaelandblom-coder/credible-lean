import Credibility.Model

/-!
# Expectation of quadratic estimators (thesis §2.8)

Second moments are given numbers, as elsewhere. The estimators of §2.8 are
quadratic forms in the data, so for data with mean `μ` and covariance table
`C` their expectation is a finite sum (`Ecov`): `E[Xₚ X_q] = C p q + μ²` is our
*definition* of the second moment. `UnbiasedCov C f θ` says that `f` is such a
form with expectation `θ` for every `μ`. Everything here is proved once for a
symmetric table `C`: the expectation depends only on the function, not on the
matrix chosen for it (`Ecov_congr`), so an estimator has one expectation
(`UnbiasedCov.unique`), and unbiasedness is linear.

The thesis is `C = obsCov`, eq. (16) (`Model.E`, `Model.Unbiased`); the
hierarchical bridges (`Hierarchical.lean`) use other tables. `Moments.lean`
shows that `Model.E` is the actual expectation for any random variables with
the moments of eq. (15) (`Noise.integral_quad`).

Data are indexed by `p = (j, t) : J × T`. Used by `Estimation.lean`,
`UnequalEstimation.lean` and `Hierarchical.lean`.
-/

open Finset

namespace Credibility.Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-! ### Expectation for a covariance table -/

/-- The quadratic form `Σₚ,q Qₚq Xₚ Xq` in the data `X`. -/
def quad (Q : J × T → J × T → ℝ) (X : J × T → ℝ) : ℝ := ∑ p, ∑ q, Q p q * X p * X q

/-- Expectation of the quadratic form `quad Q` for data with mean `μ` and
covariance table `C`: `Σₚ,q Qₚq (Cₚq + μ²)`. -/
def Ecov (C : J × T → J × T → ℝ) (μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (C p q + μ ^ 2)

/-- `f` is unbiased for `θ` under the covariance table `C`: a quadratic form in
the data whose expectation is `θ` whatever the mean `μ`. -/
def UnbiasedCov (C : J × T → J × T → ℝ) (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ μ, Ecov C μ Q = θ

variable {C : J × T → J × T → ℝ}

/-- For a symmetric table, the expectation depends only on the estimator, not
on the matrix representing it. -/
lemma Ecov_congr (hC : ∀ p q, C q p = C p q) (μ : ℝ) {Q Q' : J × T → J × T → ℝ}
    (h : ∀ X, quad Q X = quad Q' X) : Ecov C μ Q = Ecov C μ Q' := by
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
  have hE : Ecov C μ D = -Ecov C μ D := by
    conv_lhs => rw [Ecov, sum_comm]
    simp only [Ecov, ← sum_neg_distrib]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    rw [hanti, hC]; ring
  have : Ecov C μ D = 0 := by linarith
  simp only [Ecov, hD, sub_mul, sum_sub_distrib] at this
  simp only [Ecov]; linarith

/-- An estimator has one expectation: for a symmetric table, unbiasedness fixes the value. -/
lemma UnbiasedCov.unique (hC : ∀ p q, C q p = C p q) {f : (J × T → ℝ) → ℝ} {θ θ' : ℝ}
    (h : UnbiasedCov C f θ) (h' : UnbiasedCov C f θ') : θ = θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  obtain ⟨Q', hQ', hE'⟩ := h'
  rw [← hE 0, ← hE' 0, Ecov_congr hC 0 fun X => (hQ X).trans (hQ' X).symm]

omit [DecidableEq J] [DecidableEq T] in
/-- Unbiasedness is about the function and the value, not their presentation. -/
lemma UnbiasedCov.congr {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (h : UnbiasedCov C f θ)
    (hf : ∀ X, f X = g X) (hθ : θ = θ') : UnbiasedCov C g θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨Q, fun X => (hQ X).trans (hf X), fun μ => (hE μ).trans hθ⟩

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: sums. -/
lemma UnbiasedCov.add {f g : (J × T → ℝ) → ℝ} {θ φ : ℝ} (hf : UnbiasedCov C f θ)
    (hg : UnbiasedCov C g φ) : UnbiasedCov C (fun X => f X + g X) (θ + φ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hg
  refine ⟨fun p q => Q p q + Q' p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ, ← hQ']; simp only [quad, add_mul, sum_add_distrib]
  · rw [← hE μ, ← hE' μ]; simp only [Ecov, add_mul, sum_add_distrib]

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: scalar multiples. -/
lemma UnbiasedCov.const_mul {f : (J × T → ℝ) → ℝ} {θ : ℝ} (c : ℝ) (hf : UnbiasedCov C f θ) :
    UnbiasedCov C (fun X => c * f X) (c * θ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  refine ⟨fun p q => c * Q p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ]; simp only [quad, mul_sum, mul_assoc]
  · rw [← hE μ]; simp only [Ecov, mul_sum, mul_assoc]

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: finite sums. -/
lemma UnbiasedCov.sum {ι : Type*} (s : Finset ι) {f : ι → (J × T → ℝ) → ℝ} {θ : ι → ℝ}
    (hf : ∀ k ∈ s, UnbiasedCov C (f k) (θ k)) :
    UnbiasedCov C (fun X => ∑ k ∈ s, f k X) (∑ k ∈ s, θ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun X => by simp [quad], fun μ => by simp [Ecov]⟩
  | insert k s hk ih =>
    simp only [sum_insert hk]
    exact (hf k (mem_insert_self k s)).add (ih fun k' hk' => hf k' (mem_insert_of_mem hk'))

omit [DecidableEq J] [DecidableEq T] in
/-- The product of two linear forms, the first with coefficients summing to `0`
(so the mean `μ` drops out), has expectation `cov(ℓᵀX, mᵀX)`. -/
lemma unbiasedCov_mul (C : J × T → J × T → ℝ) (ℓ m : J × T → ℝ) (hℓ : ∑ p, ℓ p = 0) :
    UnbiasedCov C (fun X => (∑ p, ℓ p * X p) * (∑ q, m q * X q))
      (∑ p, ∑ q, ℓ p * m q * C p q) := by
  refine ⟨fun p q => ℓ p * m q, fun X => ?_, fun μ => ?_⟩
  · simp only [quad, sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  · have h0 : ∑ p, ∑ q, ℓ p * m q * μ ^ 2 = 0 := by
      simp_rw [mul_assoc, ← mul_sum, ← sum_mul, hℓ, zero_mul]
    simp only [Ecov, mul_add, sum_add_distrib, h0, add_zero]

/-! ### The thesis: `C = obsCov` -/

variable (M : Model J T)

/-- The covariance table of the data, eq. (16), indexed by cells `p = (j, t)`. -/
def cov (p q : J × T) : ℝ := M.obsCov p.1 q.1 p.2 q.2

omit [Fintype J] [Fintype T] in
lemma cov_symm (p q : J × T) : M.cov q p = M.cov p q := by
  simp only [cov, obsCov, M.ρ_symm q.1 p.1, eq_comm (a := q.2), eq_comm (a := q.1)]
  ring

/-- Second moment `E[μᵢₜ μⱼₛ] = cov(μᵢₜ, μⱼₛ) + μ²`, eq. (16) plus the mean `μ`. -/
def mom2 (μ : ℝ) (p q : J × T) : ℝ := M.obsCov p.1 q.1 p.2 q.2 + μ ^ 2

/-- Expectation of the quadratic form `quad Q`. -/
def E (μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ := Ecov M.cov μ Q

lemma E_eq_sum_mom2 (μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.E μ Q = ∑ p, ∑ q, Q p q * M.mom2 μ p q := rfl

/-- The expectation depends only on the estimator, not on the matrix representing it. -/
lemma E_congr (μ : ℝ) {Q Q' : J × T → J × T → ℝ} (h : ∀ X, quad Q X = quad Q' X) :
    M.E μ Q = M.E μ Q' :=
  Ecov_congr M.cov_symm μ h

/-- `f` is unbiased for `θ`: a quadratic form in the data whose expectation is
`θ` whatever the mean `μ`. -/
def Unbiased (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop := UnbiasedCov M.cov f θ

/-- The product of two linear forms, the first with coefficients summing to `0`
(so the mean `μ` drops out), has expectation `cov(ℓᵀX, mᵀX)`. -/
lemma unbiased_mul (ℓ m : J × T → ℝ) (hℓ : ∑ p, ℓ p = 0) :
    M.Unbiased (fun X => (∑ p, ℓ p * X p) * (∑ q, m q * X q))
      (∑ p, ∑ q, ℓ p * m q * M.obsCov p.1 q.1 p.2 q.2) :=
  unbiasedCov_mul M.cov ℓ m hℓ

end Credibility.Model
