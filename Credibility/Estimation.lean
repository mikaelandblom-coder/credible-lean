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

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Eq. (37): `σ²ᵢⱼρᵢⱼ = (Sᵢⱼ/(wᵢ*wⱼ*)) σᵢσⱼρᵢⱼ`. -/
theorem σ2ρ_special (i j : J) :
    M.σ2 i j * M.ρ i j = sqrtSum w i j / (wtot w i * wtot w j) * (sig i * sig j * M.ρ i j) := by
  -- `aᵢₜσᵢₜ = σᵢ√wᵢₜ/wᵢ*`.
  have key : ∀ k t, M.a k t * M.σ k t = sig k * √(w k t) / wtot w k := fun k t => by
    rw [M.a_special sig hw hσ, hσ]
    have := Real.sqrt_pos.mpr (hw k t)
    rw [← Real.sq_sqrt (hw k t).le]
    field_simp
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]; ring
  simp only [σ2, sqrtSum, sum_mul, div_mul_eq_mul_div, sum_div]
  refine sum_congr rfl fun t _ => ?_
  rw [Real.sqrt_mul (hw i t).le,
    show M.a i t * M.a j t * M.σ i t * M.σ j t = (M.a i t * M.σ i t) * (M.a j t * M.σ j t) by ring,
    key, key]
  ring

/-- Eq. (39), first line: `σ²ᵢⱼρᵢⱼ^` is unbiased. Needs `T ≥ 2`: with one
period the denominator is `0`. -/
theorem sigRhoHat_unbiased (hT : 2 ≤ Fintype.card T) (i j : J) :
    M.Unbiased (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hW : ∀ k, 0 < wtot w k := fun k => sum_pos (fun s _ => hw k s) univ_nonempty
  have hS : 0 < sqrtSum w i j :=
    sum_pos (fun t _ => Real.sqrt_pos.mpr (mul_pos (hw i t) (hw j t))) univ_nonempty
  have hT' : (0 : ℝ) ≤ (Fintype.card T : ℝ) - 2 := by
    rw [sub_nonneg]; exact_mod_cast hT
  set den := sqrtSum w i j + ((Fintype.card T : ℝ) - 2) * wtot w i * wtot w j / sqrtSum w i j
  have hden : 0 < den := by
    have := mul_nonneg (mul_nonneg hT' (hW i).le) (hW j).le
    positivity
  have hmu : ∀ X k, muHat w X k = ∑ s, M.a k s * X (k, s) := fun X k => by
    simp only [muHat, M.a_special sig hw hσ]
  -- The estimator is a combination of the residual products of `unbiased_dev`.
  refine (Unbiased.const_mul den⁻¹ (Unbiased.sum univ fun t _ =>
    (M.unbiased_dev i j t).const_mul √(w i t * w j t))).congr (fun X => ?_) ?_
  · simp only [sigRhoHat, hmu, div_eq_mul_inv, sum_mul, mul_sum, den]
    exact sum_congr rfl fun t _ => by ring
  · -- `√(wᵢₜwⱼₜ) σᵢₜσⱼₜ = σᵢσⱼ`, and `Σₜ (1 - aᵢₜ - aⱼₜ) = T - 2`.
    have hterm : ∀ t, √(w i t * w j t) * ((1 - M.a i t - M.a j t) * M.σ i t * M.σ j t * M.ρ i j
          + M.σ2 i j * M.ρ i j)
        = (1 - w i t / wtot w i - w j t / wtot w j) * (sig i * sig j * M.ρ i j)
          + √(w i t * w j t) * (M.σ2 i j * M.ρ i j) := fun t => by
      rw [M.a_special sig hw hσ, M.a_special sig hw hσ, hσ, hσ, Real.sqrt_mul (hw i t).le]
      have := Real.sqrt_pos.mpr (hw i t)
      have := Real.sqrt_pos.mpr (hw j t)
      field_simp
    have hcount : ∑ t, (1 - w i t / wtot w i - w j t / wtot w j) = (Fintype.card T : ℝ) - 2 := by
      simp only [sum_sub_distrib, ← sum_div, sum_const, card_univ, nsmul_eq_mul, mul_one]
      rw [show ∑ t, w i t = wtot w i from rfl, show ∑ t, w j t = wtot w j from rfl,
        div_self (hW i).ne', div_self (hW j).ne']
      ring
    simp only [hterm, sum_add_distrib, ← sum_mul, hcount]
    rw [show ∑ t, √(w i t * w j t) = sqrtSum w i j from rfl, M.σ2ρ_special sig hw hσ, inv_mul_eq_iff_eq_mul₀ hden.ne']
    simp only [den]
    have := (hW i).ne'; have := (hW j).ne'; have := hS.ne'
    field_simp
    ring

/-- `ĉⱼ` is unbiased for `cⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ`. -/
theorem cHat_unbiased (hT : 2 ≤ Fintype.card T) (j : J) :
    M.Unbiased (fun X => cHat w X j)
      (∑ i, ((if i = j then 1 else 0) - wtot w i / wall w) * (M.σ2 i j * M.ρ i j)) :=
  Unbiased.sum univ fun i _ => (M.sigRhoHat_unbiased sig hw hσ hT i j).const_mul _

/-- Eq. (39): `τ̂²` is unbiased. Needs `T ≥ 2` and `J ≥ 2`: with one cohort
the denominator `w** - Σᵢ wᵢ*²/w**` is `0`. -/
theorem tauHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) :
    M.Unbiased (tauHat w) M.τ2 := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hW : ∀ k, 0 < wtot w k := fun k => sum_pos (fun s _ => hw k s) univ_nonempty
  have : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have pull1 : ∀ (j : J) (g : J → T → ℝ),
      ∑ k, ∑ s, (if k = j then g k s else 0) = ∑ s, g j s := fun j g => by
    rw [sum_comm]; simp [sum_ite_eq']
  have hWall : 0 < wall w := sum_pos (fun k _ => hW k) univ_nonempty
  -- Cohort shares `xₖ = wₖ*/w**`, summing to one.
  set x : J → ℝ := fun k => wtot w k / wall w with hx_def
  have hx : ∑ k, x k = 1 := by rw [hx_def, ← sum_div]; exact div_self hWall.ne'
  have hxpos : ∀ k, 0 < x k := fun k => div_pos (hW k) hWall
  -- `J ≥ 2` gives `Σ xₖ² < 1`, so the denominator `w**(1 - Σ xₖ²)` is positive.
  have hx1 : ∀ k, x k < 1 := fun k => by
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) k
    rw [← hx, ← add_sum_erase _ _ (mem_univ k)]
    have : 0 < ∑ m ∈ univ.erase k, x m :=
      sum_pos (fun m _ => hxpos m) ⟨l, mem_erase.mpr ⟨hl, mem_univ _⟩⟩
    linarith
  have hQ : ∑ k, x k ^ 2 < 1 := by
    rw [← hx]
    exact sum_lt_sum_of_nonempty univ_nonempty fun k _ => by
      nlinarith [hxpos k, hx1 k]
  have hden : wall w - ∑ i, wtot w i ^ 2 / wall w = wall w * (1 - ∑ k, x k ^ 2) := by
    simp only [hx_def, div_pow, ← sum_div, mul_sub, mul_one]
    field_simp
  have hden_pos : 0 < wall w * (1 - ∑ k, x k ^ 2) := mul_pos hWall (by linarith)
  have hmu : ∀ X k, muHat w X k = ∑ s, M.a k s * X (k, s) := fun X k => by
    simp only [muHat, M.a_special sig hw hσ]
  -- Coefficients of `μ̂ⱼ - Σᵢ xᵢμ̂ᵢ`.
  let ℓ : J → J × T → ℝ := fun j p => ((if p.1 = j then 1 else 0) - x p.1) * M.a p.1 p.2
  have ha : ∀ k, ∑ s, M.a k s = 1 := fun k =>
    sum_invVarWeight _ (fun s => pow_pos (M.σ_pos k s) 2)
  have hlin : ∀ j (X : J × T → ℝ), ∑ p, ℓ j p * X p
      = muHat w X j - ∑ i, wtot w i / wall w * muHat w X i := fun j X => by
    simp only [ℓ, hmu, Fintype.sum_prod_type, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib,
      mul_assoc, ← mul_sum, hx_def, pull1]
  have hsum : ∀ j, ∑ p, ℓ j p = 0 := fun j => by
    have h1 : ∀ k, ∑ s, ((if k = j then 1 else 0) - x k) * M.a k s
        = (if k = j then 1 else 0) - x k := fun k => by rw [← mul_sum, ha, mul_one]
    rw [Fintype.sum_prod_type]
    simp only [ℓ, h1]
    simp [sum_sub_distrib, hx]
  have hcov : ∀ j, ∑ p, ∑ q, ℓ j p * ℓ j q * M.obsCov p.1 q.1 p.2 q.2
      = ∑ k, ∑ l, ((if k = j then 1 else 0) - x k) * ((if l = j then 1 else 0) - x l) * M.K k l :=
    fun j => by
      simp only [ℓ, Fintype.sum_prod_type, K, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ => sum_congr rfl fun s _ => sum_congr rfl fun r _ => by ring
  have hsq : ∀ j, M.Unbiased (fun X => (muHat w X j - ∑ i, wtot w i / wall w * muHat w X i) ^ 2)
      (∑ k, ∑ l, ((if k = j then 1 else 0) - x k) * ((if l = j then 1 else 0) - x l) * M.K k l) :=
    fun j => (M.unbiased_mul (ℓ j) (ℓ j) (hsum j)).congr (fun X => by rw [hlin, sq]) (hcov j)
  have hc : ∀ j, M.Unbiased (fun X => cHat w X j)
      (∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j)) :=
    fun j => M.cHat_unbiased sig hw hσ hT j
  refine (Unbiased.const_mul (wall w * (1 - ∑ k, x k ^ 2))⁻¹ (Unbiased.sum univ fun j _ =>
    ((hsq j).const_mul (wtot w j)).add ((hc j).const_mul (-wtot w j)))).congr
    (fun X => ?_) ?_
  · rw [tauHat, hden, div_eq_inv_mul]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  · -- The algebra: `Σⱼ xⱼ (E[dⱼ²] - cⱼ) = τ²(1 - Σ xₖ²)`.
    have key : ∑ j, x j * ((∑ k, ∑ l, ((if k = j then 1 else 0) - x k)
          * ((if l = j then 1 else 0) - x l) * M.K k l)
          - ∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j))
        = M.τ2 * (1 - ∑ k, x k ^ 2) := by
      have pull : ∀ (j : J) (g : J → J → ℝ),
          ∑ k, ∑ l, (if k = j then g k l else 0) = ∑ l, g j l := fun j g => by
        rw [sum_comm]; simp [sum_ite_eq']
      simp only [M.K_apply]
      simp only [mul_add, sum_add_distrib]
      simp only [sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
        mul_zero, sum_ite_eq', sum_ite_eq, mem_univ, ite_true, sum_add_distrib, mul_add, pull]
      simp only [← sum_mul, hx, mul_sum]
      have h3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * M.σ2 b c * M.ρ b c
          = ∑ b, ∑ c, x b * x c * M.σ2 b c * M.ρ b c := by
        calc _ = ∑ a, x a * ∑ b, ∑ c, x b * x c * M.σ2 b c * M.ρ b c := by
                simp only [mul_sum, mul_assoc]
          _ = _ := by rw [← sum_mul, hx, one_mul]
      ring_nf
      rw [h3, mul_sum]
      ring
    have hWj : ∀ j, wtot w j = wall w * x j := fun j => by
      simp only [hx_def]; field_simp
    rw [inv_mul_eq_iff_eq_mul₀ hden_pos.ne']
    calc _ = wall w * ∑ j, x j * ((∑ k, ∑ l, ((if k = j then 1 else 0) - x k)
          * ((if l = j then 1 else 0) - x l) * M.K k l)
          - ∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j)) := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [hWj]; ring
      _ = _ := by rw [key]; ring

/-- Eq. (39), last line: `K̂ᵢⱼ` is unbiased for `Kᵢⱼ`. -/
theorem KHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (i j : J) :
    M.Unbiased (fun X => KHat w X i j) (M.K i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  refine ((M.sigRhoHat_unbiased sig hw hσ hT i j).add
    ((M.tauHat_unbiased sig hw hσ hT hJ).const_mul (if i = j then 1 else 0))).congr
    (fun X => by simp only [KHat]; ring) ?_
  rw [M.K_apply]; ring

omit hσ [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Eq. (41): on the diagonal the estimator is the Bühlmann–Straub one,
`σ²ⱼⱼ^ = σ̂ⱼ²/wⱼ*` with `σ̂ⱼ² = Σₜ wⱼₜ(μⱼₜ - μ̂ⱼ)²/(T - 1)` from eq. (13). -/
theorem sigRhoHat_self (X : J × T → ℝ) (j : J) :
    sigRhoHat w X j j
      = (∑ t, w j t * (X (j, t) - muHat w X j) ^ 2 / ((Fintype.card T : ℝ) - 1)) / wtot w j := by
  sorry

end Credibility.Model
