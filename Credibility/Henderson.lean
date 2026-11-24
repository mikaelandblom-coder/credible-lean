import Mathlib

/-!
# The push-through identity and Henderson's mixed-model equations

General matrix lemmas for a covariance of the form `V = Z G Zᵀ + R` (a few random
effects `G` seen through a design `Z`, plus noise `R`), stated as if in Mathlib:

* `Matrix.inv_mul_mul_transpose_add` (binomial inverse, Woodbury form):
  `(Z G Zᵀ + R)⁻¹ = R⁻¹ − R⁻¹ Z (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`. With `R` easy to invert
  (diagonal) and few effects, only a `q × q` matrix is inverted: the *small form* of `V⁻¹`.
* `Matrix.pushThrough`: `G Zᵀ (Z G Zᵀ + R)⁻¹ = (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`, the covariance
  form of the BLUP weight equals its precision form.
* `Matrix.hendersonMME`: `(β̂, b̂)` solves Henderson's mixed-model equations iff `b̂` is the
  BLUP `G Zᵀ V⁻¹ (y − Xβ̂)` and `β̂` solves the GLS normal equations in `V`.

Pure finite matrix algebra: no distribution, no estimation.

**Attribution.** Ported from Stat-Lean (github.com/StatLean/Stat-Lean,
`StatLean/StatisticalModels/MixedEffects/Henderson.lean`, Apache License 2.0), read
2026-11-24 (`studies/literature.md` §10n). Changes: index types are any finite types
instead of `Fin n`; the design is given by the matrices `X`, `Z` instead of Stat-Lean's
`LMMDesign`; the binomial inverse is public; the measure-theoretic `lmmLaw_dirac` is not
ported. The proofs follow the original.

References: C. R. Henderson, O. Kempthorne, S. R. Searle and C. M. von Krosigk (1959),
*Biometrics* 15, 192–218; S. R. Searle, G. Casella and C. E. McCulloch (1992),
*Variance Components*, Wiley.
-/

open Matrix

namespace Matrix

variable {m q p : Type*} [Fintype m] [DecidableEq m] [Fintype q] [DecidableEq q] [Fintype p]

omit [DecidableEq m] [DecidableEq q] in
/-- `Z G Zᵀ + R` is positive definite for `G`, `R` positive definite. -/
theorem PosDef.mul_mul_transpose_add {Z : Matrix m q ℝ} {G : Matrix q q ℝ} {R : Matrix m m ℝ}
    (hG : G.PosDef) (hR : R.PosDef) : (Z * G * Zᵀ + R).PosDef := by
  refine Matrix.PosDef.posSemidef_add ?_ hR
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hG.posSemidef.mul_mul_conjTranspose_same Z

/-- The precision block `Zᵀ R⁻¹ Z + G⁻¹` is positive definite. -/
theorem PosDef.transpose_mul_inv_mul_add_inv {Z : Matrix m q ℝ} {G : Matrix q q ℝ}
    {R : Matrix m m ℝ} (hG : G.PosDef) (hR : R.PosDef) : (Zᵀ * R⁻¹ * Z + G⁻¹).PosDef := by
  refine Matrix.PosDef.posSemidef_add ?_ hG.inv
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hR.inv.posSemidef.mul_mul_conjTranspose_same Zᵀ

/-- **The push-through identity**: `G Zᵀ (Z G Zᵀ + R)⁻¹ = (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`. -/
theorem pushThrough (Z : Matrix m q ℝ) {G : Matrix q q ℝ} {R : Matrix m m ℝ}
    (hG : G.PosDef) (hR : R.PosDef) :
    G * Zᵀ * (Z * G * Zᵀ + R)⁻¹ = (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹ := by
  have hV := PosDef.mul_mul_transpose_add (Z := Z) hG hR
  have hP := PosDef.transpose_mul_inv_mul_add_inv (Z := Z) hG hR
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hPd := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hVd := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hkey : (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ) = Zᵀ * R⁻¹ * (Z * G * Zᵀ + R) := by
    have e1 : G⁻¹ * (G * Zᵀ) = Zᵀ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGd, Matrix.one_mul]
    have e2 : Zᵀ * (R⁻¹ * R) = Zᵀ := by rw [Matrix.nonsing_inv_mul _ hRd, Matrix.mul_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, e1, e2]
  have h2 : G * Zᵀ = (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * (Zᵀ * R⁻¹ * (Z * G * Zᵀ + R)) := by
    rw [← hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul]
  calc G * Zᵀ * (Z * G * Zᵀ + R)⁻¹
      = ((Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * (Zᵀ * R⁻¹ * (Z * G * Zᵀ + R))) * (Z * G * Zᵀ + R)⁻¹ := by
        rw [← h2]
    _ = (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹ := by
        rw [Matrix.mul_assoc _ (Zᵀ * R⁻¹ * (Z * G * Zᵀ + R)), Matrix.mul_assoc (Zᵀ * R⁻¹),
          Matrix.mul_nonsing_inv _ hVd, Matrix.mul_one, ← Matrix.mul_assoc]

/-- **The binomial inverse** (small form of `V⁻¹`):
`(Z G Zᵀ + R)⁻¹ = R⁻¹ − R⁻¹ Z (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`. -/
theorem inv_mul_mul_transpose_add (Z : Matrix m q ℝ) {G : Matrix q q ℝ} {R : Matrix m m ℝ}
    (hG : G.PosDef) (hR : R.PosDef) :
    (Z * G * Zᵀ + R)⁻¹ = R⁻¹ - R⁻¹ * Z * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹ := by
  have hP := PosDef.transpose_mul_inv_mul_add_inv (Z := Z) hG hR
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hPd := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRd
  have hGinv : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGd
  have hPinv : (Zᵀ * R⁻¹ * Z + G⁻¹) * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hPd
  refine Matrix.inv_eq_right_inv ?_
  have e1 : (Z * G * Zᵀ + R) * R⁻¹ = Z * G * Zᵀ * R⁻¹ + 1 := by rw [Matrix.add_mul, hRinv]
  have hA : (Z * G * Zᵀ + R) * (R⁻¹ * Z) = Z * G * (Zᵀ * R⁻¹ * Z + G⁻¹) := by
    have f1 : R * (R⁻¹ * Z) = Z := by rw [← Matrix.mul_assoc, hRinv, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, f1, hGinv, Matrix.mul_one]
  have e2 : (Z * G * Zᵀ + R) * (R⁻¹ * Z * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹)
      = Z * G * Zᵀ * R⁻¹ := by
    calc (Z * G * Zᵀ + R) * (R⁻¹ * Z * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹)
        = ((Z * G * Zᵀ + R) * (R⁻¹ * Z)) * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Z * G * (Zᵀ * R⁻¹ * Z + G⁻¹)) * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * Zᵀ * R⁻¹ := by rw [hA]
      _ = Z * G * Zᵀ * R⁻¹ := by rw [Matrix.mul_assoc (Z * G), hPinv, Matrix.mul_one]
  rw [Matrix.mul_sub, e1, e2]
  abel

/-- **Henderson's mixed-model equations**: `(β̂, b̂)` solves
`[XᵀR⁻¹X, XᵀR⁻¹Z; ZᵀR⁻¹X, ZᵀR⁻¹Z + G⁻¹] (β̂, b̂) = (XᵀR⁻¹y, ZᵀR⁻¹y)` iff `b̂` is the BLUP
`G Zᵀ V⁻¹ (y − Xβ̂)` and `β̂` solves the GLS normal equations `XᵀV⁻¹X β̂ = XᵀV⁻¹y`, with
`V = Z G Zᵀ + R`. -/
theorem hendersonMME (X : Matrix m p ℝ) (Z : Matrix m q ℝ) {G : Matrix q q ℝ}
    {R : Matrix m m ℝ} (hG : G.PosDef) (hR : R.PosDef)
    (βh : p → ℝ) (bh : q → ℝ) (y : m → ℝ) :
    ((Xᵀ * R⁻¹ * X) *ᵥ βh + (Xᵀ * R⁻¹ * Z) *ᵥ bh = (Xᵀ * R⁻¹) *ᵥ y
        ∧ (Zᵀ * R⁻¹ * X) *ᵥ βh + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ bh = (Zᵀ * R⁻¹) *ᵥ y)
      ↔ (bh = (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ (y - X *ᵥ βh)
          ∧ (Xᵀ * (Z * G * Zᵀ + R)⁻¹ * X) *ᵥ βh = (Xᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ y) := by
  have hP := PosDef.transpose_mul_inv_mul_add_inv (Z := Z) hG hR
  have hPd := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hPl : (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ * (Zᵀ * R⁻¹ * Z + G⁻¹) = 1 :=
    Matrix.nonsing_inv_mul _ hPd
  have hPr : (Zᵀ * R⁻¹ * Z + G⁻¹) * (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hPd
  have hpt := pushThrough Z hG hR
  -- the precision block is injective on vectors
  have hinj : ∀ v : q → ℝ, (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : (Zᵀ * R⁻¹ * Z + G⁻¹)⁻¹ *ᵥ ((Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ v) = 0 := by
      rw [hv, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hPl, Matrix.one_mulVec] at h0
  -- the BLUP weight is a left inverse of the precision block against `Zᵀ R⁻¹`
  have hPW : (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹) = Zᵀ * R⁻¹ := by
    rw [hpt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPr, Matrix.one_mul]
  -- the second block row is exactly the BLUP equation
  have hE2 : ((Zᵀ * R⁻¹ * X) *ᵥ βh + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ bh = (Zᵀ * R⁻¹) *ᵥ y)
      ↔ bh = (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ (y - X *ᵥ βh) := by
    have hstep : ((Zᵀ * R⁻¹ * X) *ᵥ βh + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ bh) - (Zᵀ * R⁻¹) *ᵥ y
        = (Zᵀ * R⁻¹ * Z + G⁻¹)
            *ᵥ (bh - (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ (y - X *ᵥ βh)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPW, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec]
      abel
    rw [← sub_eq_zero (a := (Zᵀ * R⁻¹ * X) *ᵥ βh + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ bh),
      hstep, ← sub_eq_zero (a := bh)]
    exact ⟨fun h => hinj _ h, fun h => by rw [h, Matrix.mulVec_zero]⟩
  -- the binomial inverse turns the `R`-form of the first block row into the `V`-form
  have hkey : Xᵀ * R⁻¹ * Z * (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹)
      = Xᵀ * R⁻¹ - Xᵀ * (Z * G * Zᵀ + R)⁻¹ := by
    rw [hpt, inv_mul_mul_transpose_add Z hG hR]
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have main : bh = (G * Zᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ (y - X *ᵥ βh) →
      ((Xᵀ * R⁻¹ * X) *ᵥ βh + (Xᵀ * R⁻¹ * Z) *ᵥ bh = (Xᵀ * R⁻¹) *ᵥ y
        ↔ (Xᵀ * (Z * G * Zᵀ + R)⁻¹ * X) *ᵥ βh = (Xᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ y) := by
    intro hT1
    have hshape : ((Xᵀ * R⁻¹ * X) *ᵥ βh + (Xᵀ * R⁻¹ * Z) *ᵥ bh) - (Xᵀ * R⁻¹) *ᵥ y
        = (Xᵀ * (Z * G * Zᵀ + R)⁻¹ * X) *ᵥ βh - (Xᵀ * (Z * G * Zᵀ + R)⁻¹) *ᵥ y := by
      rw [hT1, Matrix.mulVec_mulVec, hkey, Matrix.sub_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      abel
    rw [← sub_eq_zero (a := (Xᵀ * R⁻¹ * X) *ᵥ βh + (Xᵀ * R⁻¹ * Z) *ᵥ bh), hshape, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hT1 := hE2.mp h2
    exact ⟨hT1, (main hT1).mp h1⟩
  · rintro ⟨hT1, hT2⟩
    exact ⟨(main hT1).mpr hT2, hE2.mpr hT1⟩

end Matrix
