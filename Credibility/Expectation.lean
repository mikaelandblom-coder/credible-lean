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

With fixed effects the mean is `Dβ` for a design `D` (`EcovMean`, `UnbiasedMean`): a form is
unbiased for every `β` iff it vanishes on the column space of `D` (`ecovMean_eq_iff`). The
one-mean case is the design with one column of ones (`unbiasedCov_iff_unbiasedMean`), so the
linearity of `UnbiasedCov` is a corollary.

The thesis is `C = obsCov`, eq. (16) (`Model.E`, `Model.Unbiased`); the
hierarchical bridges (`Hierarchical.lean`) use other tables. `Moments.lean`
shows that `Model.E` is the actual expectation for any random variables with
the moments of eq. (15) (`Noise.integral_quad`), a case of
`integral_quad_of_cov` below.

Data are indexed by `p = (j, t) : J × T`. Used by `Estimation.lean`,
`UnequalEstimation.lean` and `Hierarchical.lean`.
-/

open Finset Matrix

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

/-! ### Means from a design: `E X = Dβ`

The mean need not be one number `μ`: with fixed effects (a card mean, a season) it is
`E X = Dβ` for a design `D` and unknown `β`. Then `E[XₚX_q] = Cₚq + mₚm_q` with `m = Dβ`
(`EcovMean`), and an estimator is unbiased if this holds for every `β` (`UnbiasedMean`).
The one-mean case `UnbiasedCov` is the design with one column of ones
(`unbiasedCov_iff_unbiasedMean`). -/

section Design

variable {B : Type*} [Fintype B]

omit [DecidableEq J] [DecidableEq T] in
/-- Expectation of the quadratic form `quad Q` for data with means `m` and covariance table
`C`: `Σₚ,q Qₚq (Cₚq + mₚm_q)`. -/
def EcovMean (C : J × T → J × T → ℝ) (m : J × T → ℝ) (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (C p q + m p * m q)

omit [DecidableEq J] [DecidableEq T] in
/-- `f` is unbiased for `θ` under the table `C` and the design `D`: a quadratic form in the
data whose expectation is `θ` whatever the fixed effects `β` (means `Dβ`). -/
def UnbiasedMean (C : J × T → J × T → ℝ) (D : Matrix (J × T) B ℝ) (f : (J × T → ℝ) → ℝ)
    (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ β, EcovMean C (D *ᵥ β) Q = θ

omit [DecidableEq J] [DecidableEq T] in
/-- The expectation splits into the covariance part and the form at the means:
`Σₚ,q QₚqCₚq + quad Q m`. -/
lemma EcovMean_eq (m : J × T → ℝ) (Q : J × T → J × T → ℝ) :
    EcovMean C m Q = ∑ p, ∑ q, Q p q * C p q + quad Q m := by
  simp only [EcovMean, quad, mul_add, sum_add_distrib]
  congr 1
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

omit [DecidableEq J] [DecidableEq T] in
/-- One mean `μ` is the constant mean vector. -/
lemma Ecov_eq_EcovMean (μ : ℝ) (Q : J × T → J × T → ℝ) :
    Ecov C μ Q = EcovMean C (fun _ => μ) Q := by
  simp only [Ecov, EcovMean, sq]

omit [DecidableEq J] [DecidableEq T] in
/-- The form at the means `Dβ` is `βᵀ(DᵀQD)β`. -/
lemma quad_mulVec (D : Matrix (J × T) B ℝ) (Q : J × T → J × T → ℝ) (β : B → ℝ) :
    quad Q (D *ᵥ β) = β ⬝ᵥ ((Dᵀ * Matrix.of Q * D) *ᵥ β) := by
  have h : ∀ X : J × T → ℝ, quad Q X = X ⬝ᵥ (Matrix.of Q *ᵥ X) := fun X => by
    simp only [quad, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec β Dᵀ,
    Matrix.vecMul_transpose]

omit [Fintype B] in
/-- Polarization: a quadratic form `βᵀAβ` vanishes for all `β` iff `A + Aᵀ = 0`. -/
lemma dotProduct_mulVec_self_eq_zero_iff [Fintype B] [DecidableEq B] (A : Matrix B B ℝ) :
    (∀ β, β ⬝ᵥ (A *ᵥ β) = 0) ↔ A + Aᵀ = 0 := by
  constructor
  · intro h
    ext a b
    have h1 := h (Pi.single a 1 + Pi.single b 1)
    have h2 := h (Pi.single a 1)
    have h3 := h (Pi.single b 1)
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single,
      single_dotProduct, MulOpposite.op_one, one_smul, Matrix.col_apply, one_mul]
      at h1 h2 h3
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply]
    linarith
  · intro h β
    have hA : Aᵀ = -A := eq_neg_of_add_eq_zero_right h
    have : β ⬝ᵥ (A *ᵥ β) = β ⬝ᵥ (Aᵀ *ᵥ β) := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
    rw [hA, Matrix.neg_mulVec, dotProduct_neg] at this
    linarith

omit [DecidableEq J] [DecidableEq T] in
/-- **Unbiased for every `β` iff the form annihilates the design**: a quadratic form with
matrix `Q` has expectation `θ` for all means `Dβ` iff `Σₚ,q QₚqCₚq = θ` and
`Dᵀ(Q + Qᵀ)D = 0` (the form vanishes on the column space of `D`). -/
theorem ecovMean_eq_iff [DecidableEq B] (D : Matrix (J × T) B ℝ) (Q : J × T → J × T → ℝ)
    (θ : ℝ) :
    (∀ β, EcovMean C (D *ᵥ β) Q = θ) ↔
      ∑ p, ∑ q, Q p q * C p q = θ ∧ Dᵀ * (Matrix.of Q + (Matrix.of Q)ᵀ) * D = 0 := by
  have hA : Dᵀ * (Matrix.of Q + (Matrix.of Q)ᵀ) * D
      = Dᵀ * Matrix.of Q * D + (Dᵀ * Matrix.of Q * D)ᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [hA, ← dotProduct_mulVec_self_eq_zero_iff]
  simp only [EcovMean_eq, quad_mulVec]
  constructor
  · intro h
    have h0 := h 0
    simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero] at h0
    exact ⟨h0, fun β => by have := h β; linarith⟩
  · rintro ⟨h0, h⟩ β
    rw [h β, add_zero, h0]

omit [DecidableEq J] [DecidableEq T] in
/-- **The one-mean case**: `UnbiasedCov` is `UnbiasedMean` for the design with one column of
ones. -/
theorem unbiasedCov_iff_unbiasedMean {f : (J × T → ℝ) → ℝ} {θ : ℝ} :
    UnbiasedCov C f θ ↔ UnbiasedMean C (Matrix.of fun _ (_ : Unit) => (1 : ℝ)) f θ := by
  have h : ∀ (μ : ℝ) Q, Ecov C μ Q
      = EcovMean C ((Matrix.of fun _ (_ : Unit) => (1 : ℝ)) *ᵥ fun _ => μ) Q := by
    intro μ Q
    rw [Ecov_eq_EcovMean]
    congr 1
    funext p
    simp [Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨Q, hQ, hE⟩
    refine ⟨Q, hQ, fun β => ?_⟩
    have hβ : β = fun _ => β () := funext fun u => rfl
    rw [hβ, ← h]; exact hE _
  · rintro ⟨Q, hQ, hE⟩
    exact ⟨Q, hQ, fun μ => by rw [h]; exact hE _⟩

/-- For a symmetric table, an estimator has one expectation under a design too. -/
lemma UnbiasedMean.unique (hC : ∀ p q, C q p = C p q) {D : Matrix (J × T) B ℝ}
    {f : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (h : UnbiasedMean C D f θ)
    (h' : UnbiasedMean C D f θ') : θ = θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  obtain ⟨Q', hQ', hE'⟩ := h'
  have h0 : ∀ Q : J × T → J × T → ℝ, EcovMean C (D *ᵥ 0) Q = Ecov C 0 Q := fun Q => by
    rw [Ecov_eq_EcovMean, Matrix.mulVec_zero]; rfl
  rw [← hE 0, ← hE' 0, h0, h0, Ecov_congr hC 0 fun X => (hQ X).trans (hQ' X).symm]

omit [DecidableEq J] [DecidableEq T] in
/-- Unbiasedness is about the function and the value, not their presentation. -/
lemma UnbiasedMean.congr {D : Matrix (J × T) B ℝ} {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ}
    (h : UnbiasedMean C D f θ) (hf : ∀ X, f X = g X) (hθ : θ = θ') :
    UnbiasedMean C D g θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨Q, fun X => (hQ X).trans (hf X), fun β => (hE β).trans hθ⟩

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: sums. -/
lemma UnbiasedMean.add {D : Matrix (J × T) B ℝ} {f g : (J × T → ℝ) → ℝ} {θ φ : ℝ}
    (hf : UnbiasedMean C D f θ) (hg : UnbiasedMean C D g φ) :
    UnbiasedMean C D (fun X => f X + g X) (θ + φ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hg
  refine ⟨fun p q => Q p q + Q' p q, fun X => ?_, fun β => ?_⟩
  · beta_reduce; rw [← hQ, ← hQ']; simp only [quad, add_mul, sum_add_distrib]
  · rw [← hE β, ← hE' β]; simp only [EcovMean, add_mul, sum_add_distrib]

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: scalar multiples. -/
lemma UnbiasedMean.const_mul {D : Matrix (J × T) B ℝ} {f : (J × T → ℝ) → ℝ} {θ : ℝ} (c : ℝ)
    (hf : UnbiasedMean C D f θ) : UnbiasedMean C D (fun X => c * f X) (c * θ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  refine ⟨fun p q => c * Q p q, fun X => ?_, fun β => ?_⟩
  · beta_reduce; rw [← hQ]; simp only [quad, mul_sum, mul_assoc]
  · rw [← hE β]; simp only [EcovMean, mul_sum, mul_assoc]

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: finite sums. -/
lemma UnbiasedMean.sum {ι : Type*} (s : Finset ι) {D : Matrix (J × T) B ℝ}
    {f : ι → (J × T → ℝ) → ℝ} {θ : ι → ℝ} (hf : ∀ k ∈ s, UnbiasedMean C D (f k) (θ k)) :
    UnbiasedMean C D (fun X => ∑ k ∈ s, f k X) (∑ k ∈ s, θ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun X => by simp [quad], fun β => by simp [EcovMean]⟩
  | insert k s hk ih =>
    simp only [sum_insert hk]
    exact (hf k (mem_insert_self k s)).add (ih fun k' hk' => hf k' (mem_insert_of_mem hk'))

omit [DecidableEq J] [DecidableEq T] in
/-- **The product of two linear forms, the first annihilating the design** (`Dᵀℓ = 0`, so the
fixed effects drop out), has expectation `cov(ℓᵀX, mᵀX)` for every `β`. -/
lemma unbiasedMean_mul (C : J × T → J × T → ℝ) (D : Matrix (J × T) B ℝ) (ℓ m : J × T → ℝ)
    (hℓ : Dᵀ *ᵥ ℓ = 0) :
    UnbiasedMean C D (fun X => (∑ p, ℓ p * X p) * (∑ q, m q * X q))
      (∑ p, ∑ q, ℓ p * m q * C p q) := by
  refine ⟨fun p q => ℓ p * m q, fun X => ?_, fun β => ?_⟩
  · simp only [quad, sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  · have h0 : ∑ p, ℓ p * (D *ᵥ β) p = 0 := by
      have : ℓ ⬝ᵥ (D *ᵥ β) = (Dᵀ *ᵥ ℓ) ⬝ᵥ β := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rw [hℓ, zero_dotProduct] at this
      exact this
    have h1 : ∑ p, ∑ q, ℓ p * m q * ((D *ᵥ β) p * (D *ᵥ β) q) = 0 := by
      have : ∀ p q, ℓ p * m q * ((D *ᵥ β) p * (D *ᵥ β) q)
          = (ℓ p * (D *ᵥ β) p) * (m q * (D *ᵥ β) q) := fun p q => by ring
      simp_rw [this, ← mul_sum, ← sum_mul, h0, zero_mul]
    simp only [EcovMean, mul_add, sum_add_distrib, h1, add_zero]

omit [DecidableEq J] [DecidableEq T] in
/-- **Differences of cells with the same design row annihilate the design**: if
`Dₚ = D_{p'}` and `D_q = D_{q'}`, then `(Xₚ - X_{p'})(X_q - X_{q'})` is unbiased for
`Cₚq - C_{pq'} - C_{p'q} + C_{p'q'}` whatever `β`. -/
theorem unbiasedMean_diff_mul [DecidableEq (J × T)] (C : J × T → J × T → ℝ)
    (D : Matrix (J × T) B ℝ) {p p' q q' : J × T} (hp : D p = D p') :
    UnbiasedMean C D (fun X => (X p - X p') * (X q - X q'))
      (C p q - C p q' - C p' q + C p' q') := by
  have hℓ : Dᵀ *ᵥ (Pi.single p 1 - Pi.single p' 1 : J × T → ℝ) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_single, Matrix.mulVec_single, sub_eq_zero]
    funext b
    simp [hp]
  refine (unbiasedMean_mul C D _ (Pi.single q 1 - Pi.single q' 1) hℓ).congr
    (fun X => ?_) ?_
  · simp [Pi.single_apply, sub_mul]
  · simp [Pi.single_apply, sub_mul, mul_sub]
    ring

omit [DecidableEq J] [DecidableEq T] in
/-- `EcovMean` is the actual expectation: for random variables `Zₚ` and a quadratic form
reading only cells in `S`, if on `S` the `Zₚ` are square integrable with means `mₚ` and
`cov(Zₚ, Z_q) = C p q`, then `E[Σₚ,q Qₚq Zₚ Z_q] = EcovMean C m Q`. No distribution is
assumed, and nothing about cells outside `S`. -/
theorem integral_quad_of_mean {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (Z : J × T → Ω → ℝ) (C : J × T → J × T → ℝ)
    (m : J × T → ℝ) (Q : J × T → J × T → ℝ) (S : J × T → Prop)
    (hQ : ∀ p q, Q p q ≠ 0 → S p ∧ S q) (hZ : ∀ p, S p → MeasureTheory.MemLp (Z p) 2 P)
    (hm : ∀ p, S p → ∫ ω, Z p ω ∂P = m p)
    (hc : ∀ p q, S p → S q → ProbabilityTheory.covariance (Z p) (Z q) P = C p q) :
    ∫ ω, quad Q (fun p => Z p ω) ∂P = EcovMean C m Q := by
  -- Each term is `0` or a product of two square-integrable cells,
  -- with `E[ZₚZ_q] = cov(Zₚ, Z_q) + mₚm_q`.
  have hI : ∀ p q : J × T, MeasureTheory.Integrable (fun ω => Q p q * (Z p ω * Z q ω)) P := by
    intro p q
    by_cases h : Q p q = 0
    · simp [h]
    obtain ⟨hp, hq⟩ := hQ p q h
    exact ((hZ p hp).integrable_mul (hZ q hq)).const_mul _
  have hE : ∀ p q : J × T,
      ∫ ω, Q p q * (Z p ω * Z q ω) ∂P = Q p q * (C p q + m p * m q) := by
    intro p q
    by_cases h : Q p q = 0
    · simp [h]
    obtain ⟨hp, hq⟩ := hQ p q h
    have hcov := ProbabilityTheory.covariance_eq_sub (hZ p hp) (hZ q hq)
    rw [hc p q hp hq, hm p hp, hm q hq] at hcov
    rw [MeasureTheory.integral_const_mul, hcov]
    simp only [Pi.mul_def]
    ring
  simp only [quad, EcovMean, mul_assoc]
  rw [MeasureTheory.integral_finsetSum _ fun p _ =>
    MeasureTheory.integrable_finsetSum _ fun q _ => hI p q]
  refine sum_congr rfl fun p _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun q _ => hI p q]
  exact sum_congr rfl fun q _ => hE p q

omit [DecidableEq J] [DecidableEq T] in
/-- `Ecov` is the actual expectation: for random variables `Zₚ` and a quadratic
form reading only cells in `S` (`Qₚq ≠ 0` only if `p, q ∈ S`), if on `S` the
`Zₚ` are square integrable with mean `μ` and `cov(Zₚ, Z_q) = C p q`, then
`E[Σₚ,q Qₚq Zₚ Z_q] = Ecov C μ Q`. No distribution is assumed, and nothing
about cells outside `S`. -/
theorem integral_quad_of_cov {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (Z : J × T → Ω → ℝ) (C : J × T → J × T → ℝ) (μ : ℝ)
    (Q : J × T → J × T → ℝ) (S : J × T → Prop) (hQ : ∀ p q, Q p q ≠ 0 → S p ∧ S q)
    (hZ : ∀ p, S p → MeasureTheory.MemLp (Z p) 2 P) (hm : ∀ p, S p → ∫ ω, Z p ω ∂P = μ)
    (hc : ∀ p q, S p → S q → ProbabilityTheory.covariance (Z p) (Z q) P = C p q) :
    ∫ ω, quad Q (fun p => Z p ω) ∂P = Ecov C μ Q := by
  rw [Ecov_eq_EcovMean]
  exact integral_quad_of_mean Z C _ Q S hQ hZ hm hc

omit [DecidableEq J] [DecidableEq T] in
/-- **A smaller design**: unbiased for every `β` under `D` stays so under any design `DE`
whose columns lie in the column space of `D` (e.g. a common season from a per-card one). -/
lemma UnbiasedMean.of_mul {B' : Type*} [Fintype B'] {D : Matrix (J × T) B ℝ}
    {f : (J × T → ℝ) → ℝ} {θ : ℝ} (h : UnbiasedMean C D f θ) (E : Matrix B B' ℝ) :
    UnbiasedMean C (D * E) f θ := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨Q, hQ, fun β => by rw [← Matrix.mulVec_mulVec]; exact hE _⟩

omit [DecidableEq J] [DecidableEq T] in
/-- **Unbiased is about the true expectation**: if `f` is unbiased for `θ` under `C` and `D`,
then for any square-integrable random cells with means `Dβ` and covariances `C`,
`E f(Z) = θ`. No distribution is assumed. -/
theorem UnbiasedMean.integral_eq {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {D : Matrix (J × T) B ℝ} {f : (J × T → ℝ) → ℝ}
    {θ : ℝ} (h : UnbiasedMean C D f θ) (Z : J × T → Ω → ℝ) (β : B → ℝ)
    (hZ : ∀ p, MeasureTheory.MemLp (Z p) 2 P) (hm : ∀ p, ∫ ω, Z p ω ∂P = (D *ᵥ β) p)
    (hc : ∀ p q, ProbabilityTheory.covariance (Z p) (Z q) P = C p q) :
    ∫ ω, f (fun p => Z p ω) ∂P = θ := by
  obtain ⟨Q, hQ, hE⟩ := h
  simp_rw [← hQ]
  rw [integral_quad_of_mean Z C _ Q (fun _ => True) (fun _ _ _ => ⟨trivial, trivial⟩)
    (fun p _ => hZ p) (fun p _ => hm p) (fun p q _ _ => hc p q)]
  exact hE β

end Design

/-! ### The one-mean case as corollaries -/

/-- An estimator has one expectation: for a symmetric table, unbiasedness fixes the value. -/
lemma UnbiasedCov.unique (hC : ∀ p q, C q p = C p q) {f : (J × T → ℝ) → ℝ} {θ θ' : ℝ}
    (h : UnbiasedCov C f θ) (h' : UnbiasedCov C f θ') : θ = θ' :=
  UnbiasedMean.unique hC (unbiasedCov_iff_unbiasedMean.1 h) (unbiasedCov_iff_unbiasedMean.1 h')

omit [DecidableEq J] [DecidableEq T] in
/-- Unbiasedness is about the function and the value, not their presentation. -/
lemma UnbiasedCov.congr {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (h : UnbiasedCov C f θ)
    (hf : ∀ X, f X = g X) (hθ : θ = θ') : UnbiasedCov C g θ' :=
  unbiasedCov_iff_unbiasedMean.2 ((unbiasedCov_iff_unbiasedMean.1 h).congr hf hθ)

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: sums. -/
lemma UnbiasedCov.add {f g : (J × T → ℝ) → ℝ} {θ φ : ℝ} (hf : UnbiasedCov C f θ)
    (hg : UnbiasedCov C g φ) : UnbiasedCov C (fun X => f X + g X) (θ + φ) :=
  unbiasedCov_iff_unbiasedMean.2
    ((unbiasedCov_iff_unbiasedMean.1 hf).add (unbiasedCov_iff_unbiasedMean.1 hg))

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: scalar multiples. -/
lemma UnbiasedCov.const_mul {f : (J × T → ℝ) → ℝ} {θ : ℝ} (c : ℝ) (hf : UnbiasedCov C f θ) :
    UnbiasedCov C (fun X => c * f X) (c * θ) :=
  unbiasedCov_iff_unbiasedMean.2 ((unbiasedCov_iff_unbiasedMean.1 hf).const_mul c)

omit [DecidableEq J] [DecidableEq T] in
/-- Linearity: finite sums. -/
lemma UnbiasedCov.sum {ι : Type*} (s : Finset ι) {f : ι → (J × T → ℝ) → ℝ} {θ : ι → ℝ}
    (hf : ∀ k ∈ s, UnbiasedCov C (f k) (θ k)) :
    UnbiasedCov C (fun X => ∑ k ∈ s, f k X) (∑ k ∈ s, θ k) :=
  unbiasedCov_iff_unbiasedMean.2
    (UnbiasedMean.sum s fun k hk => unbiasedCov_iff_unbiasedMean.1 (hf k hk))


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
