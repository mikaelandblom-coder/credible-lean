import Credibility.Model

/-!
# Parameter estimation (thesis §2.8, eqs. (37)–(41))

Special case `σⱼₜ = σⱼ/√wⱼₜ` with known volumes `wⱼₜ > 0`: Bühlmann–Straub, but
with a cohort-dependent base variance `σⱼ²` and correlations `ρᵢⱼ`.

Second moments are given numbers, as elsewhere. Observations `μⱼₜ` have mean `μ`
and covariance `Model.obsCov`, so `E[μᵢₜ μⱼₛ] = obsCov + μ²` is our *definition*
of the second moment (`mom2`). The estimators are quadratic forms in the data,
so their expectation is a finite sum (`E`), and `Unbiased f θ` says that `f` is
such a form with expectation `θ` for every `μ`. `E_congr` shows that this
expectation depends only on the function `f`, not on the matrix chosen for it.

Data are indexed by `p = (j, t) : J × T`.
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

/-- The display before (37): `E[(μᵢₜ - μ̂ᵢ)(μⱼₜ - μ̂ⱼ)] = (1 - aᵢₜ - aⱼₜ)σᵢₜσⱼₜρᵢⱼ + σ²ᵢⱼρᵢⱼ`,
for any `σⱼₜ`. -/
theorem unbiased_dev (i j : J) (t : T) :
    M.Unbiased (fun X => (X (i, t) - ∑ s, M.a i s * X (i, s)) * (X (j, t) - ∑ s, M.a j s * X (j, s)))
      ((1 - M.a i t - M.a j t) * M.σ i t * M.σ j t * M.ρ i j + M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := ⟨t⟩
  have ha : ∀ k, ∑ s, M.a k s = 1 := fun k =>
    sum_invVarWeight _ (fun s => pow_pos (M.σ_pos k s) 2)
  -- Coefficients of `μₖₜ - μ̂ₖ`.
  let ℓ : J → J × T → ℝ := fun k p => if p.1 = k then (if p.2 = t then 1 else 0) - M.a k p.2 else 0
  have hlin : ∀ (k : J) (F : J × T → ℝ), ∑ p, ℓ k p * F p = F (k, t) - ∑ s, M.a k s * F (k, s) := by
    intro k F
    rw [Fintype.sum_prod_type, Finset.sum_eq_single k (fun b _ hb => by simp [ℓ, hb]) (by simp)]
    simp [ℓ, sub_mul, sum_sub_distrib, ite_mul]
  have hsum : ∑ p, ℓ i p = 0 := by
    have := hlin i (fun _ => 1)
    simp only [mul_one, ha] at this
    rw [this]; ring
  refine (M.unbiased_mul (ℓ i) (ℓ j) hsum).congr (fun X => by rw [hlin, hlin]) ?_
  simp_rw [mul_assoc, ← mul_sum, hlin]
  -- Four terms; `K̄ᵢⱼʳˢ = σᵢᵣσⱼₛρᵢⱼδᵣₛ + τ²δᵢⱼ`.
  simp only [obsCov, mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, ite_true]
  rw [σ2, sum_mul]
  split_ifs <;>
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite, mul_zero, add_zero,
    sum_ite_eq', mem_univ, ite_true, ← sum_mul, ha, sum_const_zero] <;>
  ring_nf <;> rw [mul_sum] <;> ring_nf

/-! ### The special case `σⱼₜ = σⱼ/√wⱼₜ` -/

variable (w : J → T → ℝ)

/-- `wⱼ* = Σₜ wⱼₜ`. -/
def wtot (j : J) : ℝ := ∑ t, w j t

/-- `w** = Σⱼ wⱼ*`. -/
def wall : ℝ := ∑ j, wtot w j

/-- `Sᵢⱼ = Σₜ √(wᵢₜwⱼₜ)`. -/
noncomputable def sqrtSum (i j : J) : ℝ := ∑ t, √(w i t * w j t)

/-- `μ̂ⱼ = Σₜ (wⱼₜ/wⱼ*) μⱼₜ`. -/
noncomputable def muHat (X : J × T → ℝ) (j : J) : ℝ := ∑ t, w j t / wtot w j * X (j, t)

/-- The estimator of `σ²ᵢⱼρᵢⱼ`, first line of eq. (39). -/
noncomputable def sigRhoHat (X : J × T → ℝ) (i j : J) : ℝ :=
  (∑ t, √(w i t * w j t) * (X (i, t) - muHat w X i) * (X (j, t) - muHat w X j))
    / (sqrtSum w i j + ((Fintype.card T : ℝ) - 2) * wtot w i * wtot w j / sqrtSum w i j)

/-- `ĉⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ^`, eq. (39). -/
noncomputable def cHat (X : J × T → ℝ) (j : J) : ℝ :=
  ∑ i, ((if i = j then 1 else 0) - wtot w i / wall w) * sigRhoHat w X i j

/-- The estimator of `τ²`, eq. (39). -/
noncomputable def tauHat (X : J × T → ℝ) : ℝ :=
  (∑ j, wtot w j * ((muHat w X j - ∑ i, wtot w i / wall w * muHat w X i) ^ 2 - cHat w X j))
    / (wall w - ∑ i, wtot w i ^ 2 / wall w)

/-- `K̂ᵢⱼ = σ²ᵢⱼρᵢⱼ^ + τ̂²δᵢⱼ`, last line of eq. (39). -/
noncomputable def KHat (X : J × T → ℝ) (i j : J) : ℝ :=
  sigRhoHat w X i j + tauHat w X * (if i = j then 1 else 0)

variable {w} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t) (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- §2.8, from eq. (29): the special case still gives `aⱼₜ = wⱼₜ/wⱼ*`. -/
theorem a_special (j : J) (t : T) : M.a j t = w j t / wtot w j := by
  have hs : sig j ≠ 0 := by
    intro h; have := M.σ_pos j t; rw [hσ, h, zero_div] at this; exact lt_irrefl _ this
  have hsq : ∀ s, M.σ j s ^ 2 = sig j ^ 2 / w j s := fun s => by
    rw [hσ, div_pow, Real.sq_sqrt (hw j s).le]
  have hW : wtot w j ≠ 0 := (sum_pos (fun s _ => hw j s) ⟨t, mem_univ _⟩).ne'
  simp only [a, invVarWeight, hsq, inv_div]
  rw [← sum_div, div_div_div_cancel_right₀ (pow_ne_zero 2 hs), wtot]

/-- Eq. (37): `σ²ᵢⱼρᵢⱼ = (Sᵢⱼ/(wᵢ*wⱼ*)) σᵢσⱼρᵢⱼ`. -/
theorem σ2ρ_special (i j : J) :
    M.σ2 i j * M.ρ i j = sqrtSum w i j / (wtot w i * wtot w j) * (sig i * sig j * M.ρ i j) := by
  sorry

/-- Eq. (39), first line: `σ²ᵢⱼρᵢⱼ^` is unbiased. Needs `T ≥ 2`: with one
period the denominator is `0`. -/
theorem sigRhoHat_unbiased (hT : 2 ≤ Fintype.card T) (i j : J) :
    M.Unbiased (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  sorry

/-- `ĉⱼ` is unbiased for `cⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ`. -/
theorem cHat_unbiased (hT : 2 ≤ Fintype.card T) (j : J) :
    M.Unbiased (fun X => cHat w X j)
      (∑ i, ((if i = j then 1 else 0) - wtot w i / wall w) * (M.σ2 i j * M.ρ i j)) := by
  sorry

/-- Eq. (39): `τ̂²` is unbiased. Needs `T ≥ 2` and `J ≥ 2`: with one cohort
the denominator `w** - Σᵢ wᵢ*²/w**` is `0`. -/
theorem tauHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) :
    M.Unbiased (tauHat w) M.τ2 := by
  sorry

/-- Eq. (39), last line: `K̂ᵢⱼ` is unbiased for `Kᵢⱼ`. -/
theorem KHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (i j : J) :
    M.Unbiased (fun X => KHat w X i j) (M.K i j) := by
  sorry

omit hσ in
/-- Eq. (41): on the diagonal the estimator is the Bühlmann–Straub one,
`σ²ⱼⱼ^ = σ̂ⱼ²/wⱼ*` with `σ̂ⱼ² = Σₜ wⱼₜ(μⱼₜ - μ̂ⱼ)²/(T - 1)` from eq. (13). -/
theorem sigRhoHat_self (X : J × T → ℝ) (j : J) :
    sigRhoHat w X j j
      = (∑ t, w j t * (X (j, t) - muHat w X j) ^ 2 / ((Fintype.card T : ℝ) - 1)) / wtot w j := by
  sorry

end Credibility.Model
