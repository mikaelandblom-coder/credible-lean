import Mathlib

/-!
# The best linear unbiased predictor for a general target, with fixed effects

Core level, extension (`notes/card-data.md`, Step 1). The data `x` are indexed by observed
cells `n`, with `K = Cov(x)`. The target is a random `Y` with `ℓ = Cov(x, Y)` and `v = Var Y`.
The means are fixed effects: `E x = Xβ` and `E Y = x₀ᵀβ` for an unknown `β` (one mean:
`X = 1`; a season: one `β` per calendar month). A linear predictor `dᵀx` is unbiased for every
`β` iff `Xᵀd = x₀`, and then its mean squared error is `dᵀKd - 2dᵀℓ + v`.

The best one has the universal-kriging (Goldberger 1962) weights
`d* = K⁻¹ℓ + K⁻¹X(XᵀK⁻¹X)⁻¹(x₀ - XᵀK⁻¹ℓ)`, and every other unbiased `d` loses exactly
`(d - d*)ᵀK(d - d*)`. Its own error is `v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r` with
`r = x₀ - XᵀK⁻¹ℓ`: the error with `β` known, plus the price of estimating `β`.

Second moments are given numbers here; `Core.linMse` (`X = 1`, target a level) and
`CoreVector.linMse` (`X = U`, one mean per component) are special cases.
-/

open Matrix

namespace Credibility
namespace Core

variable {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q]

/-- The mean squared error `dᵀKd - 2dᵀℓ + v` of the linear predictor `dᵀx` of a target `Y`,
when `K = Cov(x)`, `ℓ = Cov(x, Y)`, `v = Var Y` and `dᵀx` is unbiased. -/
def predMse (K : Matrix n n ℝ) (ℓ : n → ℝ) (v : ℝ) (d : n → ℝ) : ℝ :=
  d ⬝ᵥ (K *ᵥ d) - 2 * (d ⬝ᵥ ℓ) + v

omit [DecidableEq n] [DecidableEq q] in
/-- **Unbiasedness with fixed effects**: if `E x = Xβ` and `E Y = x₀ᵀβ`, then
`E(dᵀx) = E Y` for every `β` iff `Xᵀd = x₀`. -/
theorem unbiased_iff (X : Matrix n q ℝ) (x₀ : q → ℝ) (d : n → ℝ) :
    (∀ β : q → ℝ, d ⬝ᵥ (X *ᵥ β) = x₀ ⬝ᵥ β) ↔ Xᵀ *ᵥ d = x₀ := by
  classical
  simp only [dotProduct_mulVec, ← mulVec_transpose]
  refine ⟨fun h => funext fun i => ?_, fun h β => by rw [h]⟩
  simpa [dotProduct_single] using h (Pi.single i 1)

omit [DecidableEq n] [DecidableEq q] in
/-- **Pythagoras for linear predictors**: if `Ke - ℓ` lies in the column space of `X`
(the first-order condition), then any `d` with `Xᵀd = Xᵀe` loses exactly
`(d - e)ᵀK(d - e)` against `e`. -/
theorem predMse_eq_add_of_normal {K : Matrix n n ℝ} (hK : K.IsHermitian) (ℓ : n → ℝ) (v : ℝ)
    (X : Matrix n q ℝ) {e : n → ℝ} {c : q → ℝ} (he : K *ᵥ e - ℓ = X *ᵥ c) {d : n → ℝ}
    (hd : Xᵀ *ᵥ d = Xᵀ *ᵥ e) :
    predMse K ℓ v d = predMse K ℓ v e + (d - e) ⬝ᵥ (K *ᵥ (d - e)) := by
  -- `(d - e)ᵀ(Ke - ℓ) = (Xᵀ(d - e))ᵀc = 0`.
  have h0 : (d - e) ⬝ᵥ (K *ᵥ e - ℓ) = 0 := by
    rw [he, dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, hd, sub_self, zero_dotProduct]
  have hs : e ⬝ᵥ (K *ᵥ d) = d ⬝ᵥ (K *ᵥ e) := by
    have hsymm : Kᵀ = K := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hK
    rw [dotProduct_mulVec, ← hsymm, vecMul_transpose, hsymm, dotProduct_comm]
  simp only [predMse, mulVec_sub, dotProduct_sub, sub_dotProduct] at h0 ⊢
  linarith

/-- The weights of the best linear unbiased predictor of `Y` (universal kriging):
`d* = K⁻¹ℓ + K⁻¹X(XᵀK⁻¹X)⁻¹(x₀ - XᵀK⁻¹ℓ)`. -/
noncomputable def blup (K : Matrix n n ℝ) (X : Matrix n q ℝ) (ℓ : n → ℝ) (x₀ : q → ℝ) :
    n → ℝ :=
  K⁻¹ *ᵥ (ℓ + X *ᵥ ((Xᵀ * K⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ))))

omit [DecidableEq q] in
/-- With `K ≻ 0` and `X` of full column rank, `XᵀK⁻¹X ≻ 0`. -/
theorem info_posDef {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) : (Xᵀ * K⁻¹ * X).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hK.inv.conjTranspose_mul_mul_same hX

/-- The first-order condition: `Kd* - ℓ = X(XᵀK⁻¹X)⁻¹(x₀ - XᵀK⁻¹ℓ)`. -/
theorem mulVec_blup {K : Matrix n n ℝ} (hK : K.PosDef) (X : Matrix n q ℝ) (ℓ : n → ℝ)
    (x₀ : q → ℝ) :
    K *ᵥ blup K X ℓ x₀ - ℓ = X *ᵥ ((Xᵀ * K⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ))) := by
  rw [blup, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hK.det_pos.ne'), one_mulVec,
    add_sub_cancel_left]

/-- The best predictor is unbiased: `Xᵀd* = x₀`. -/
theorem transpose_mulVec_blup {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (x₀ : q → ℝ) :
    Xᵀ *ᵥ blup K X ℓ x₀ = x₀ := by
  have hM : IsUnit (Xᵀ * K⁻¹ * X).det := isUnit_iff_ne_zero.2 (info_posDef hK hX).det_pos.ne'
  have h : Xᵀ *ᵥ (K⁻¹ *ᵥ (X *ᵥ ((Xᵀ * K⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)))))
      = x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ) := by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hM,
      one_mulVec]
  rw [blup, mulVec_add, mulVec_add, h, add_sub_cancel]

/-- **MSE decomposition**: any unbiased weights `d` (`Xᵀd = x₀`) lose exactly
`(d - d*)ᵀK(d - d*)` against the best predictor. -/
theorem predMse_eq_blup_add {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (v : ℝ) (x₀ : q → ℝ) {d : n → ℝ}
    (hd : Xᵀ *ᵥ d = x₀) :
    predMse K ℓ v d = predMse K ℓ v (blup K X ℓ x₀)
      + (d - blup K X ℓ x₀) ⬝ᵥ (K *ᵥ (d - blup K X ℓ x₀)) :=
  predMse_eq_add_of_normal hK.isHermitian ℓ v X (mulVec_blup hK X ℓ x₀)
    (hd.trans (transpose_mulVec_blup hK hX ℓ x₀).symm)

/-- **The best linear unbiased predictor** of a general target with fixed effects:
`d*` has the smallest mean squared error among all weights with `Xᵀd = x₀`. -/
theorem blup_optimal {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (v : ℝ) (x₀ : q → ℝ) {d : n → ℝ}
    (hd : Xᵀ *ᵥ d = x₀) : predMse K ℓ v (blup K X ℓ x₀) ≤ predMse K ℓ v d := by
  rw [predMse_eq_blup_add hK hX ℓ v x₀ hd]
  have := hK.posSemidef.dotProduct_mulVec_nonneg (d - blup K X ℓ x₀)
  simp only [star_trivial] at this
  linarith

/-- …and it is the only one. -/
theorem blup_unique {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (v : ℝ) (x₀ : q → ℝ) {d : n → ℝ}
    (hd : Xᵀ *ᵥ d = x₀) (h : predMse K ℓ v d ≤ predMse K ℓ v (blup K X ℓ x₀)) :
    d = blup K X ℓ x₀ := by
  rw [predMse_eq_blup_add hK hX ℓ v x₀ hd] at h
  by_contra hne
  have := hK.dotProduct_mulVec_pos (x := d - blup K X ℓ x₀) (sub_ne_zero.mpr hne)
  simp only [star_trivial] at this
  linarith

/-- Unbiased weights that satisfy the first-order condition (`Ke - ℓ` in the column space of
`X`) are the best predictor's weights. -/
theorem eq_blup_of_normal {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (x₀ : q → ℝ) {e : n → ℝ} {c : q → ℝ}
    (he : K *ᵥ e - ℓ = X *ᵥ c) (hex : Xᵀ *ᵥ e = x₀) : e = blup K X ℓ x₀ := by
  refine blup_unique hK hX ℓ 0 x₀ hex ?_
  rw [predMse_eq_add_of_normal hK.isHermitian ℓ 0 X he
    ((transpose_mulVec_blup hK hX ℓ x₀).trans hex.symm)]
  have := hK.posSemidef.dotProduct_mulVec_nonneg (blup K X ℓ x₀ - e)
  simp only [star_trivial] at this
  linarith

/-- **Its error**: `MSE(d*) = v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r` with `r = x₀ - XᵀK⁻¹ℓ`. The first
two terms are the error of the best linear predictor when `β` is known; the last is the
price of estimating `β`. -/
theorem predMse_blup {K : Matrix n n ℝ} (hK : K.PosDef) {X : Matrix n q ℝ}
    (hX : Function.Injective X.mulVec) (ℓ : n → ℝ) (v : ℝ) (x₀ : q → ℝ) :
    predMse K ℓ v (blup K X ℓ x₀)
      = v - ℓ ⬝ᵥ (K⁻¹ *ᵥ ℓ)
        + (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)) ⬝ᵥ ((Xᵀ * K⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ))) := by
  set r := x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)
  set g := (Xᵀ * K⁻¹ * X)⁻¹ *ᵥ r
  set d := blup K X ℓ x₀ with hd
  have hKd : K *ᵥ d = ℓ + X *ᵥ g := by rw [← mulVec_blup hK X ℓ x₀]; abel
  -- `dᵀXg = (Xᵀd)ᵀg = x₀ᵀg`.
  have h1 : d ⬝ᵥ (X *ᵥ g) = x₀ ⬝ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mulVec_blup hK hX]
  -- `dᵀℓ = ℓᵀK⁻¹ℓ + gᵀXᵀK⁻¹ℓ`, by symmetry of `K⁻¹`.
  have hsymm : (K⁻¹)ᵀ = K⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hK.inv.isHermitian
  have h2 : d ⬝ᵥ ℓ = ℓ ⬝ᵥ (K⁻¹ *ᵥ ℓ) + g ⬝ᵥ (Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)) := by
    have hb : d = K⁻¹ *ᵥ ℓ + K⁻¹ *ᵥ (X *ᵥ g) := by rw [hd, blup, mulVec_add]
    have h3 : (K⁻¹ *ᵥ (X *ᵥ g)) ⬝ᵥ ℓ = g ⬝ᵥ (Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)) := by
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_mulVec,
        ← mulVec_transpose, dotProduct_comm]
    rw [hb, add_dotProduct, h3, dotProduct_comm (K⁻¹ *ᵥ ℓ)]
  have hr : g ⬝ᵥ r = r ⬝ᵥ g := dotProduct_comm _ _
  simp only [predMse, hKd, dotProduct_add, h1, h2] at hr ⊢
  simp only [r, sub_dotProduct, dotProduct_comm g] at hr ⊢
  linarith

end Core
end Credibility
