import Credibility.Season
import Credibility.Shock

/-!
# The common factor model (extension, `notes/card-data.md` Step 3)

Monthly cells `Xⱼₜ` (cohort `j`, month `t`) share a latent demand factor `Fₜ` with loadings `λⱼ`
and an autocovariance `Γ ⪰ 0` over all months, past and future. On top of it sit the period
shock and process noise of `Shock` and the cohort level with variance `τ²`:

`cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼΓₜₛ + δₜₛCᵢⱼ + δₜₛδᵢⱼsᵢ²/wᵢₜ + τ²δᵢⱼ`  (`obsCov`).

Distribution-free: only these second moments are assumed. The data are the observed cells, any
injective map `c : n → J × T` (cohorts enter and leave: `n = {(j, t) | t ∈ obs j}`).

* **`K ≻ 0`** for any observed cells (`K_posDef`): the factor part is `BᵀΓB`, the shock part a
  weighted sum as in `Shock`, the level part `τ²` times a same-card indicator, and the process
  noise a positive diagonal.
* **Instances of `Γ`**: `Γ = 0` is `Shock` (`obsCov_eq_shock`); `C = 0`, `Γ = I` is `Shock` with
  the rank-one shock `C = λλᵀ` (`obsCov_eq_shock_loadings`); AR(1) `Γₜₛ = γφ^|t-s|` with
  `|φ| ≤ 1` (`ar1_posSemidef`); a break at known dates, a block `Γ` with no correlation across
  regimes (`block_posSemidef`, a constant level per regime: `regime_posSemidef`).
* **The target** `Y = Σₜ bₜX_{j₀t}` (`bₜ = 1` on the next 12 months): `ℓ = Cov(x, Y)` (`ell`) and
  `v = Var Y` (`var`). For months not yet observed, `ℓ` only sees the factor and the cohort level:
  `ℓ_{(i,t)} = λᵢλ_{j₀}(Γb)ₜ + τ²δ_{ij₀}Σₛbₛ` (`ell_apply_of_future`); `v` in `var_eq`.
* **The predictor** is Step 1's best linear unbiased predictor for this `K`, `ℓ`, `v`
  (`blup_optimal`, `predMse_blup`), with the season design of Step 2 (`blup_season_optimal`).
* **Valid fitted tables** (`tableK`, no `τ²`): `≻ 0` when every `sⱼ² > 0` (`tableK_posDef`);
  with some `sⱼ² = 0`, `Z = {j : sⱼ² = 0}`, iff `(A + C)_ZZ ≻ 0` when `Φ ≻ 0` and `Z` shares an
  observed month (`tableK_posDef_iff`; both conditions needed, Finding 34).
* **Negative weights** (Finding 25, `blup_neg_of_ar1`): two cohorts, two months, AR(1) with
  `φ = 1/2`; the predictor of cohort 0's next month puts `-1/30` on cohort 1's first month.
-/

open Finset Matrix

namespace Credibility

/-- The common factor model: a latent factor with loadings `λⱼ` and autocovariance `Γ ⪰ 0`
over all months, past and future, on top of the shock and process noise of `Shock` and cohort
levels with variance `τ²`. Distribution-free: only these second moments are assumed. -/
structure Factor (J T : Type*) where
  /-- Heterogeneity between cohorts. -/
  τ2 : ℝ
  /-- Covariance of the period shock across cohorts (independent between months). -/
  C : Matrix J J ℝ
  /-- Process noise per unit of volume. -/
  s2 : J → ℝ
  /-- Volume of cohort `j` in month `t`. -/
  w : J → T → ℝ
  /-- Loadings `λⱼ` on the common factor. -/
  load : J → ℝ
  /-- Autocovariance of the common factor over all months. -/
  Γ : Matrix T T ℝ
  τ2_pos : 0 < τ2
  C_posSemidef : C.PosSemidef
  s2_pos : ∀ j, 0 < s2 j
  w_pos : ∀ j t, 0 < w j t
  Γ_posSemidef : Γ.PosSemidef

namespace Factor

variable {J T n : Type*} (M : Factor J T)

/-- The shock and process noise without the factor. -/
def toShock : Shock J T :=
  ⟨M.τ2, M.C, M.s2, M.w, M.τ2_pos, M.C_posSemidef, M.s2_pos, M.w_pos⟩

variable [DecidableEq J] [DecidableEq T]

/-- `cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼΓₜₛ + δₜₛ(Cᵢⱼ + δᵢⱼsᵢ²/wᵢₜ) + τ²δᵢⱼ`: the factor on top of `Shock`. -/
noncomputable def obsCov (i j : J) (t s : T) : ℝ :=
  M.load i * M.load j * M.Γ t s + M.toShock.obsCov i j t s

/-! ### Instances: `Shock` -/

/-- **`Γ = 0` is `Shock`**. -/
theorem obsCov_eq_shock (hΓ : M.Γ = 0) (i j : J) (t s : T) :
    M.obsCov i j t s = M.toShock.obsCov i j t s := by
  simp [obsCov, hΓ]

/-- **One factor, independent months, no shock, is `Shock` with the rank-one shock
`C = λλᵀ`**: `C = 0` and `Γ = I`. -/
theorem obsCov_eq_shock_loadings [Fintype J] (hC : M.C = 0) (hΓ : M.Γ = 1) (i j : J) (t s : T) :
    M.obsCov i j t s
      = (⟨M.τ2, vecMulVec M.load M.load, M.s2, M.w, M.τ2_pos, posSemidef_loadings M.load,
          M.s2_pos, M.w_pos⟩ : Shock J T).obsCov i j t s := by
  simp only [obsCov, Shock.obsCov, toShock, hC, hΓ, vecMulVec_apply]
  by_cases ht : t = s
  · subst ht; by_cases hij : i = j <;> simp [hij]
    ring
  · by_cases hij : i = j <;> simp [ht, hij]

/-! ### The covariance of the observed cells and its positive definiteness -/

variable (c : n → J × T)

/-- `K = Cov(x)` for the observed cells `c : n → J × T`. -/
noncomputable def K : Matrix n n ℝ := of fun p q => M.obsCov (c p).1 (c q).1 (c p).2 (c q).2

/-- The factor part `λᵢλⱼΓₜₛ` of `K`. -/
noncomputable def factorPart : Matrix n n ℝ :=
  of fun p q => M.load (c p).1 * M.load (c q).1 * M.Γ (c p).2 (c q).2

/-- The shock part `δₜₛCᵢⱼ` of `K`. -/
noncomputable def shockPart : Matrix n n ℝ :=
  of fun p q => if (c p).2 = (c q).2 then M.C (c p).1 (c q).1 else 0

/-- The level part `τ²δᵢⱼ` of `K`. -/
noncomputable def levelPart : Matrix n n ℝ :=
  of fun p q => M.τ2 * if (c p).1 = (c q).1 then 1 else 0

/-- The process noise `sᵢ²/wᵢₜ` of each cell. -/
noncomputable def cellNoise (p : n) : ℝ := M.s2 (c p).1 / M.w (c p).1 (c p).2

variable {c}

/-- `K` splits into the factor, the shock, the level and the process noise. -/
theorem K_eq_parts [DecidableEq n] (hc : Function.Injective c) :
    M.K c = diagonal (M.cellNoise c) + (M.factorPart c + M.shockPart c + M.levelPart c) := by
  ext p q
  simp only [K, factorPart, shockPart, levelPart, obsCov, Shock.obsCov, toShock, of_apply]
  by_cases hpq : p = q
  · subst hpq; simp [cellNoise]; ring
  · have : ¬((c p).2 = (c q).2 ∧ (c p).1 = (c q).1) := fun h =>
      hpq (hc (Prod.ext h.2 h.1))
    by_cases ht : (c p).2 = (c q).2
    · have hj : (c p).1 ≠ (c q).1 := fun h => this ⟨ht, h⟩
      simp [hpq, ht, hj]
    · simp [hpq, ht]

variable (c)

omit [DecidableEq J] in
/-- The factor part is `BᵀΓB` with `B_{t,(j,s)} = δₜₛλⱼ`, so it is `⪰ 0`. -/
theorem factorPart_posSemidef [Fintype n] [Fintype T] : (M.factorPart c).PosSemidef := by
  set B : Matrix T n ℝ := of fun t p => if (c p).2 = t then M.load (c p).1 else 0
  have h : M.factorPart c = Bᴴ * M.Γ * B := by
    ext p q
    simp [factorPart, B, Matrix.mul_apply, ite_mul, mul_ite]
    ring
  rw [h]
  exact M.Γ_posSemidef.conjTranspose_mul_mul_same B

omit [DecidableEq J] in
/-- The shock part is a weighted sum of `C` over months, as in `Shock`: `⪰ 0`. -/
theorem shockPart_posSemidef [Fintype n] [Fintype T] : (M.shockPart c).PosSemidef := by
  have h := posSemidef_weightedSum (fun _ : T => M.C.submatrix (fun p => (c p).1)
    (fun p => (c p).1)) (fun _ => M.C_posSemidef.submatrix _)
    (fun p t => if (c p).2 = t then 1 else 0)
  convert h using 1
  ext p q
  simp [shockPart, ite_mul]

omit [DecidableEq T] in
/-- The level part is `τ²` times a same-card indicator: `⪰ 0`. -/
theorem levelPart_posSemidef [Fintype n] [Fintype J] : (M.levelPart c).PosSemidef := by
  have h := ((PosSemidef.one (n := J) (R := ℝ)).submatrix (fun p : n => (c p).1)).smul
    M.τ2_pos.le
  convert h using 1
  ext p q
  by_cases h : (c p).1 = (c q).1 <;> simp [levelPart, h, Matrix.one_apply]

/-! ### Fitted tables: any factor table `A ⪰ 0`, no level -/

omit [DecidableEq J] in
/-- The covariance table the app builds from fitted parameters, at the observed cells
`c : n → J × T`: `Aᵢⱼ Φₜₛ + δₜₛ Cᵢⱼ + δ_{pq} sᵢ²/wᵢₜ`. The factor table `A` is any matrix (a
projection of `γλλᵀ` onto the positive semidefinite cone need not be rank one) and the level
`τ²` is left out. -/
noncomputable def tableK [DecidableEq n] (A : Matrix J J ℝ) (Φ : Matrix T T ℝ) (C : Matrix J J ℝ)
    (s2 : J → ℝ) (w : J → T → ℝ) (c : n → J × T) : Matrix n n ℝ :=
  of fun p q => A (c p).1 (c q).1 * Φ (c p).2 (c q).2
    + (if (c p).2 = (c q).2 then C (c p).1 (c q).1 else 0)
    + (if p = q then s2 (c p).1 / w (c p).1 (c p).2 else 0)

omit [DecidableEq J] in
/-- **Valid fitted tables give `K̂ ≻ 0`.** If `A ⪰ 0`, `Φ ⪰ 0`, `C ⪰ 0` and every `sⱼ² > 0`
(volumes `w > 0`), the fitted table is positive definite, for any observed cells and without
the level `τ²`: the factor and shock parts are Hadamard products of positive semidefinite
matrices (Schur), the process noise a positive diagonal. -/
theorem tableK_posDef [Fintype n] [DecidableEq n] {A : Matrix J J ℝ} {Φ : Matrix T T ℝ}
    {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} (hA : A.PosSemidef) (hΦ : Φ.PosSemidef)
    (hC : C.PosSemidef) (hs : ∀ j, 0 < s2 j) (hw : ∀ j t, 0 < w j t) (c : n → J × T) :
    (tableK A Φ C s2 w c).PosDef := by
  have h : tableK A Φ C s2 w c = diagonal (fun p => s2 (c p).1 / w (c p).1 (c p).2)
      + (A.submatrix (fun p => (c p).1) (fun p => (c p).1) ⊙
          Φ.submatrix (fun p => (c p).2) (fun p => (c p).2)
        + C.submatrix (fun p => (c p).1) (fun p => (c p).1) ⊙
          (1 : Matrix T T ℝ).submatrix (fun p => (c p).2) (fun p => (c p).2)) := by
    ext p q
    by_cases ht : (c p).2 = (c q).2 <;> by_cases hpq : p = q <;>
      simp [tableK, hadamard, Matrix.one_apply, ht, hpq] <;> ring
  rw [h]
  exact (PosDef.diagonal fun p => div_pos (hs _) (hw _ _)).add_posSemidef
    (((hA.submatrix _).hadamard (hΦ.submatrix _)).add
      ((hC.submatrix _).hadamard (PosSemidef.one.submatrix _)))

omit [DecidableEq J] in
/-- **`ŝ² ≥ 0` is not enough.** If a cohort `j` has `Aⱼⱼ = Cⱼⱼ = sⱼ² = 0` (all three of its
variances clipped to zero) and is observed in some cell, the fitted table is singular: that
cell has variance zero. So `tableK_posDef` needs `sⱼ² > 0`, not just `≥ 0`. -/
theorem tableK_not_posDef [Fintype n] [DecidableEq n] {A : Matrix J J ℝ} {Φ : Matrix T T ℝ}
    {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} {c : n → J × T} {p : n}
    (hA : A (c p).1 (c p).1 = 0) (hC : C (c p).1 (c p).1 = 0) (hs : s2 (c p).1 = 0) :
    ¬(tableK A Φ C s2 w c).PosDef := fun h => by
  have := h.diag_pos (i := p)
  simp [tableK, hA, hC, hs] at this

section ValidTables

open scoped Kronecker

/-! #### Valid tables with some `ŝⱼ² = 0` -/

/-- The fitted table over the full panel `J × T` (every cell observed). -/
noncomputable def panelK (A : Matrix J J ℝ) (Φ : Matrix T T ℝ) (C : Matrix J J ℝ) (s2 : J → ℝ)
    (w : J → T → ℝ) : Matrix (J × T) (J × T) ℝ :=
  of fun x y => A x.1 y.1 * Φ x.2 y.2 + (if x.2 = y.2 then C x.1 y.1 else 0)
    + (if x = y then s2 x.1 / w x.1 x.2 else 0)

/-- For distinct observed cells, the fitted table is the panel table at those cells. -/
theorem tableK_eq_submatrix [DecidableEq n] {A : Matrix J J ℝ} {Φ : Matrix T T ℝ}
    {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} {c : n → J × T}
    (hc : Function.Injective c) :
    tableK A Φ C s2 w c = (panelK A Φ C s2 w).submatrix c c := by
  ext p q
  simp [tableK, panelK, hc.eq_iff]

/-- The panel table is `diag(s²/w) + A ⊗ Φ + C ⊗ I`. -/
theorem panelK_eq [Fintype J] [Fintype T] (A : Matrix J J ℝ) (Φ : Matrix T T ℝ)
    (C : Matrix J J ℝ) (s2 : J → ℝ) (w : J → T → ℝ) :
    panelK A Φ C s2 w = diagonal (fun x => s2 x.1 / w x.1 x.2)
      + (A ⊗ₖ Φ + C ⊗ₖ (1 : Matrix T T ℝ)) := by
  ext x y
  simp only [panelK, of_apply, Matrix.add_apply, diagonal_apply, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]
  ring

variable [Fintype J] [Fintype T]

/-- **Valid tables with some `ŝⱼ² = 0`, full panel.** If `A ⪰ 0`, `Φ ≻ 0`, `C ⪰ 0`, `s² ≥ 0`
and `(A + C)_ZZ ≻ 0` on `Z = {j : sⱼ² = 0}`, the panel table is `≻ 0`. -/
theorem panelK_posDef {A : Matrix J J ℝ} {Φ : Matrix T T ℝ} {C : Matrix J J ℝ} {s2 : J → ℝ}
    {w : J → T → ℝ} (hA : A.PosSemidef) (hΦ : Φ.PosDef) (hC : C.PosSemidef)
    (hs : ∀ j, 0 ≤ s2 j) (hw : ∀ j t, 0 < w j t)
    (hZ : ((A + C).submatrix (Subtype.val : {j // s2 j = 0} → J) Subtype.val).PosDef) :
    (panelK A Φ C s2 w).PosDef := by
  classical
  rw [panelK_eq]
  have hD : (diagonal fun x : J × T => s2 x.1 / w x.1 x.2).PosSemidef :=
    posSemidef_diagonal_iff.2 fun x => div_nonneg (hs _) (hw _ _).le
  have h1 : (A ⊗ₖ Φ).PosSemidef := hA.kronecker hΦ.posSemidef
  have h2 : (C ⊗ₖ (1 : Matrix T T ℝ)).PosSemidef := hC.kronecker PosSemidef.one
  refine PosDef.of_dotProduct_mulVec_pos (hD.add (h1.add h2)).1 fun x hx => ?_
  by_contra hle
  push Not at hle
  rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add] at hle
  have q0 := hD.dotProduct_mulVec_nonneg x
  have q1 := h1.dotProduct_mulVec_nonneg x
  have q2 := h2.dotProduct_mulVec_nonneg x
  have e := (add_eq_zero_iff_of_nonneg q0 (add_nonneg q1 q2)).1
    (le_antisymm hle (add_nonneg q0 (add_nonneg q1 q2)))
  have e' := (add_eq_zero_iff_of_nonneg q1 q2).1 e.2
  have k0 := hD.dotProduct_mulVec_zero_iff.1 e.1
  have k1 := h1.dotProduct_mulVec_zero_iff.1 e'.1
  have k2 := h2.dotProduct_mulVec_zero_iff.1 e'.2
  have hx0 : ∀ j t, s2 j ≠ 0 → x (j, t) = 0 := fun j t h => by
    have := congrFun k0 (j, t)
    simp only [mulVec_diagonal, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (div_ne_zero h (hw j t).ne')
  have hA1 : (A ⊗ₖ (1 : Matrix T T ℝ)) *ᵥ x = 0 := by
    have hu : IsUnit ((1 : Matrix J J ℝ) ⊗ₖ Φ) := isUnit_one.kronecker hΦ.isUnit
    have : ((1 : Matrix J J ℝ) ⊗ₖ Φ) *ᵥ ((A ⊗ₖ (1 : Matrix T T ℝ)) *ᵥ x)
        = ((1 : Matrix J J ℝ) ⊗ₖ Φ) *ᵥ 0 := by
      rw [mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, k1, mulVec_zero]
    exact mulVec_injective_iff_isUnit.2 hu this
  have hcol : ∀ (j : J) (t : T), ∑ k, (A + C) j k * x (k, t) = 0 := fun j t => by
    have e1 := congrFun hA1 (j, t)
    have e2 := congrFun k2 (j, t)
    simp only [mulVec, dotProduct, kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul, Fintype.sum_prod_type, sum_ite_eq, mem_univ, ite_true,
      Pi.zero_apply] at e1 e2
    simp only [Matrix.add_apply, add_mul, sum_add_distrib, e1, e2, add_zero]
  apply hx
  funext ⟨j, t⟩
  by_cases hj : s2 j = 0
  · let Z := {k // s2 k = 0}
    let v : Z → ℝ := fun k => x (k.1, t)
    have hv : (A + C).submatrix (Subtype.val : Z → J) Subtype.val *ᵥ v
        = (A + C).submatrix (Subtype.val : Z → J) Subtype.val *ᵥ (0 : Z → ℝ) := by
      rw [mulVec_zero]
      funext i
      simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply, v]
      refine (Fintype.sum_of_injective (Subtype.val : Z → J) Subtype.val_injective _
        (fun k => (A + C) i.1 k * x (k, t))
        (fun k hk => by
          have : s2 k ≠ 0 := fun h => hk ⟨⟨k, h⟩, rfl⟩
          rw [hx0 k t this, mul_zero]) (fun _ => rfl)).trans (hcol i.1 t)
    have := congrFun (mulVec_injective_iff_isUnit.2 hZ.isUnit hv) ⟨j, hj⟩
    simpa [v] using this
  · exact hx0 j t hj

/-- **The "if" for observed cells**: distinct observed cells, `A ⪰ 0`, `Φ ≻ 0`, `C ⪰ 0`,
`s² ≥ 0` and `(A + C)_ZZ ≻ 0` give `K̂ ≻ 0`. -/
theorem tableK_posDef_of_zero [Fintype n] [DecidableEq n] {A : Matrix J J ℝ}
    {Φ : Matrix T T ℝ} {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} {c : n → J × T}
    (hc : Function.Injective c) (hA : A.PosSemidef) (hΦ : Φ.PosDef) (hC : C.PosSemidef)
    (hs : ∀ j, 0 ≤ s2 j) (hw : ∀ j t, 0 < w j t)
    (hZ : ((A + C).submatrix (Subtype.val : {j // s2 j = 0} → J) Subtype.val).PosDef) :
    (tableK A Φ C s2 w c).PosDef := by
  rw [tableK_eq_submatrix hc]
  exact (panelK_posDef hA hΦ hC hs hw hZ).submatrix hc

/-- **The "only if"**: if `K̂ ≻ 0` at distinct observed cells and every cohort with `sⱼ² = 0` is
observed in a common month `t₀`, then `(A + C)_ZZ ≻ 0`. (No condition on `Φ` is needed.) -/
theorem posDef_zero_of_tableK [Fintype n] [DecidableEq n] {A : Matrix J J ℝ}
    {Φ : Matrix T T ℝ} {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} {c : n → J × T}
    (hc : Function.Injective c) (hA : A.PosSemidef) (hC : C.PosSemidef) {t₀ : T}
    (ht : ∀ j, s2 j = 0 → ∃ p, c p = (j, t₀)) (hK : (tableK A Φ C s2 w c).PosDef) :
    ((A + C).submatrix (Subtype.val : {j // s2 j = 0} → J) Subtype.val).PosDef := by
  classical
  let Z := {k // s2 k = 0}
  have hS := (hA.add hC).submatrix (Subtype.val : Z → J)
  refine PosDef.of_dotProduct_mulVec_pos hS.1 fun v hv => ?_
  by_contra hle
  push Not at hle
  let u : J → ℝ := fun j => if h : s2 j = 0 then v ⟨j, h⟩ else 0
  have hu : ∀ k : Z, u k.1 = v k := fun k => by simp [u, k.2]
  have hu0 : ∀ j, u j ≠ 0 → s2 j = 0 := fun j h => by
    by_contra h'; exact h (by simp [u, h'])
  have hre : ∀ f : J → ℝ, ∑ k : Z, f k.1 * v k = ∑ j, f j * u j := fun f =>
    Fintype.sum_of_injective (Subtype.val : Z → J) Subtype.val_injective _ _
      (fun j hj => by
        have : u j = 0 := by_contra fun h => hj ⟨⟨j, hu0 j h⟩, rfl⟩
        rw [this, mul_zero]) (fun k => by rw [hu])
  have hq : star v ⬝ᵥ ((A + C).submatrix (Subtype.val : Z → J) Subtype.val *ᵥ v)
      = star u ⬝ᵥ (A *ᵥ u) + star u ⬝ᵥ (C *ᵥ u) := by
    calc star v ⬝ᵥ ((A + C).submatrix (Subtype.val : Z → J) Subtype.val *ᵥ v)
        = ∑ i : Z, ((A + C) *ᵥ u) i.1 * v i := by
          simp only [star_trivial, dotProduct]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_comm]
          congr 1
          simp only [mulVec, dotProduct, submatrix_apply]
          exact hre (fun k => (A + C) i.1 k)
      _ = ∑ j, ((A + C) *ᵥ u) j * u j := hre _
      _ = _ := by
          rw [← dotProduct_add, ← add_mulVec, star_trivial, dotProduct_comm]
          rfl
  have qA := hA.dotProduct_mulVec_nonneg u
  have qC := hC.dotProduct_mulVec_nonneg u
  rw [hq] at hle
  have e := (add_eq_zero_iff_of_nonneg qA qC).1 (le_antisymm hle (add_nonneg qA qC))
  have kA := hA.dotProduct_mulVec_zero_iff.1 e.1
  have kC := hC.dotProduct_mulVec_zero_iff.1 e.2
  let y : J × T → ℝ := fun x => if x.2 = t₀ then u x.1 else 0
  have hy : panelK A Φ C s2 w *ᵥ y = 0 := by
    rw [panelK_eq]
    funext ⟨j, t⟩
    have eA := congrFun kA j
    have eC := congrFun kC j
    simp only [mulVec, dotProduct, Pi.zero_apply] at eA eC
    simp only [mulVec, dotProduct, Matrix.add_apply, diagonal_apply, kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, y, mul_ite, mul_zero, ite_mul, zero_mul,
      mul_one, add_mul, Pi.zero_apply, Prod.mk.injEq]
    simp only [sum_ite_eq', mem_univ, ite_true, sum_add_distrib]
    have e1 : ∑ x, (if j = x ∧ t = t₀ then s2 j / w j t * u x else 0) = 0 := by
      rw [sum_eq_single j (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      by_cases h : t = t₀
      · by_cases hj : u j = 0
        · simp [hj]
        · simp [h, hu0 j hj]
      · simp [h]
    have e2 : ∑ x, A j x * Φ t t₀ * u x = Φ t t₀ * ∑ x, A j x * u x := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have e3 : ∑ x, (if t = t₀ then C j x * u x else 0) = if t = t₀ then ∑ x, C j x * u x
        else 0 := by split_ifs <;> simp
    rw [e1, e2, e3, eA, eC]
    simp
  have hx : (fun p => y (c p)) ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h'; push Not at h'; exact hv (funext h')
    obtain ⟨p, hp⟩ := ht i.1 i.2
    have := congrFun h p
    simp only [y, hp, ite_true, Pi.zero_apply, hu] at this
    exact hi this
  have hKx : tableK A Φ C s2 w c *ᵥ (fun p => y (c p)) = 0 := by
    rw [tableK_eq_submatrix hc]
    funext p
    have := congrFun hy (c p)
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at this ⊢
    refine (Fintype.sum_of_injective c hc _ (fun x => panelK A Φ C s2 w (c p) x * y x)
      (fun x hx => ?_) (fun _ => rfl)).trans this
    by_cases h : x.2 = t₀ ∧ u x.1 ≠ 0
    · obtain ⟨q, hq⟩ := ht x.1 (hu0 x.1 h.2)
      exact absurd ⟨q, by rw [hq, ← h.1]⟩ hx
    · have : y x = 0 := by
        simp only [y]; split_ifs with h1
        · by_contra h2; exact h ⟨h1, h2⟩
        · rfl
      rw [this, mul_zero]
  have := hK.dotProduct_mulVec_pos hx
  rw [hKx, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- **Valid tables: `K̂ ≻ 0` iff `(A + C)_ZZ ≻ 0`**, `Z = {j : sⱼ² = 0}`, for distinct observed
cells, `A ⪰ 0`, `Φ ≻ 0`, `C ⪰ 0`, `s² ≥ 0`, when the cohorts in `Z` are observed in a common
month (e.g. a full panel). Both extra conditions are needed (Finding 34). -/
theorem tableK_posDef_iff [Fintype n] [DecidableEq n] {A : Matrix J J ℝ}
    {Φ : Matrix T T ℝ} {C : Matrix J J ℝ} {s2 : J → ℝ} {w : J → T → ℝ} {c : n → J × T}
    (hc : Function.Injective c) (hA : A.PosSemidef) (hΦ : Φ.PosDef) (hC : C.PosSemidef)
    (hs : ∀ j, 0 ≤ s2 j) (hw : ∀ j t, 0 < w j t) {t₀ : T}
    (ht : ∀ j, s2 j = 0 → ∃ p, c p = (j, t₀)) :
    (tableK A Φ C s2 w c).PosDef
      ↔ ((A + C).submatrix (Subtype.val : {j // s2 j = 0} → J) Subtype.val).PosDef :=
  ⟨posDef_zero_of_tableK hc hA hC ht, tableK_posDef_of_zero hc hA hΦ hC hs hw⟩

omit [Fintype J] [Fintype T] in
/-- **The "if" needs `Φ ≻ 0`** (Finding 34): with no factor dynamics (`Φ = 0`), `A = I`,
`C = 0`, `s² = 0`, `(A + C)_ZZ = I ≻ 0` but every cell has variance zero. -/
theorem tableK_counter_phi [Fintype n] [DecidableEq n] [Nonempty n] (w : J → T → ℝ)
    (c : n → J × T) :
    ((1 + 0 : Matrix J J ℝ).submatrix (Subtype.val : {j // (0 : J → ℝ) j = 0} → J)
        Subtype.val).PosDef
      ∧ ¬(tableK 1 0 0 0 w c).PosDef := by
  refine ⟨by rw [add_zero]; exact PosDef.one.submatrix Subtype.val_injective, fun h => ?_⟩
  have := h.diag_pos (i := Classical.arbitrary n)
  simp [tableK] at this

/-- **The "only if" needs a common month** (Finding 34): two cohorts with `s² = 0` observed in
different months, `A = 0`, `Φ = I`, `C = vvᵀ`, `v = (1, -1)` (all valid): `K̂ = I ≻ 0`, but
`(A + C)_ZZ = C` is singular. -/
theorem tableK_counter_month :
    (tableK (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (vecMulVec ![1, -1] ![1, -1]) 0 (fun _ _ => 1) ![((0 : Fin 2), (0 : Fin 2)), (1, 1)]).PosDef
      ∧ ¬((0 + vecMulVec ![1, -1] ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ).submatrix
          (Subtype.val : {j // (0 : Fin 2 → ℝ) j = 0} → Fin 2) Subtype.val).PosDef := by
  refine ⟨?_, fun h => ?_⟩
  · have : tableK (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (vecMulVec ![1, -1] ![1, -1]) 0 (fun _ _ => 1) ![((0 : Fin 2), (0 : Fin 2)), (1, 1)]
        = 1 := by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [tableK, vecMulVec_apply, Matrix.one_apply]
    rw [this]; exact PosDef.one
  · have h2 := h.submatrix (e := fun j : Fin 2 => (⟨j, rfl⟩ : {j // (0 : Fin 2 → ℝ) j = 0}))
      fun a b hab => by simpa using hab
    have hx : (![1, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
    have := h2.dotProduct_mulVec_pos hx
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this

end ValidTables

/-- **`K ≻ 0`** for any observed cells: the fitted-table case (`tableK_posDef`) with
`A = λλᵀ`, `Φ = Γ`, plus the level part `τ²δᵢⱼ ⪰ 0`. -/
theorem K_posDef [Fintype n] [DecidableEq n] [Fintype J] [Fintype T] {c : n → J × T}
    (hc : Function.Injective c) : (M.K c).PosDef := by
  have h : M.K c = tableK (vecMulVec M.load M.load) M.Γ M.C M.s2 M.w c + M.levelPart c := by
    ext p q
    simp only [K, tableK, levelPart, obsCov, Shock.obsCov, toShock, of_apply,
      vecMulVec_apply]
    by_cases hpq : p = q
    · subst hpq; simp; ring
    · have : ¬((c p).2 = (c q).2 ∧ (c p).1 = (c q).1) := fun h =>
        hpq (hc (Prod.ext h.2 h.1))
      by_cases ht : (c p).2 = (c q).2
      · have hj : (c p).1 ≠ (c q).1 := fun h => this ⟨ht, h⟩
        simp [hpq, ht, hj]
      · simp [hpq, ht]
  rw [h]
  exact (tableK_posDef (posSemidef_loadings M.load) M.Γ_posSemidef M.C_posSemidef M.s2_pos
    M.w_pos c).add_posSemidef (M.levelPart_posSemidef c)

/-! ### Instances of `Γ`: AR(1) and a break at known dates -/

/-- The AR(1) autocovariance `Γₜₛ = γφ^|t-s|` over months `0, …, N-1`. -/
def ar1 (N : ℕ) (γ φ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  of fun t s => γ * φ ^ (if (t : ℕ) ≤ s then (s : ℕ) - t else (t : ℕ) - s)

/-- `Σ_{k≤t} (φ^{t-k})²dₖ = 1` with `d₀ = 1`, `dₖ = 1 - φ²`: an AR(1) started in its stationary
law, `Fₜ = φF_{t-1} + eₜ`, has variance `1` at every `t`. -/
lemma ar1_sum_sq (φ : ℝ) (t : ℕ) :
    ∑ k ∈ range (t + 1), φ ^ (t - k) * φ ^ (t - k) * (if k = 0 then 1 else 1 - φ ^ 2) = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, Nat.sub_self]
    have h : ∑ k ∈ range (t + 1),
        φ ^ (t + 1 - k) * φ ^ (t + 1 - k) * (if k = 0 then 1 else 1 - φ ^ 2)
        = φ ^ 2 * ∑ k ∈ range (t + 1),
          φ ^ (t - k) * φ ^ (t - k) * (if k = 0 then 1 else 1 - φ ^ 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [Nat.sub_add_comm (Nat.lt_succ_iff.mp (mem_range.mp hk)), pow_succ]
      ring
    rw [h, ih]
    simp

/-- The entries of `LDLᵀ` with `L_{tk} = φ^{t-k}` (`k ≤ t`): `φ^{s-t}` for `t ≤ s`. -/
lemma ar1_sum_eq (φ : ℝ) {N t s : ℕ} (hts : t ≤ s) (hs : s < N) :
    ∑ k ∈ range N, (if k ≤ t then φ ^ (t - k) else 0) * (if k = 0 then 1 else 1 - φ ^ 2)
      * (if k ≤ s then φ ^ (s - k) else 0) = φ ^ (s - t) := by
  rw [← sum_range_add_sum_Ico _ (show t + 1 ≤ N by omega)]
  have h2 : ∑ k ∈ Ico (t + 1) N, (if k ≤ t then φ ^ (t - k) else 0)
      * (if k = 0 then 1 else 1 - φ ^ 2) * (if k ≤ s then φ ^ (s - k) else 0) = 0 :=
    sum_eq_zero fun k hk => by
      have : ¬k ≤ t := by have := (mem_Ico.mp hk).1; omega
      simp [this]
  rw [h2, add_zero]
  trans φ ^ (s - t)
    * ∑ k ∈ range (t + 1), φ ^ (t - k) * φ ^ (t - k) * (if k = 0 then 1 else 1 - φ ^ 2)
  · rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [hk, hk.trans hts, ite_true, show s - k = (s - t) + (t - k) by omega, pow_add]
    ring
  · rw [ar1_sum_sq, mul_one]

/-- The innovation loadings `L_{tk} = φ^{t-k}` for `k ≤ t`. -/
def ar1L (N : ℕ) (φ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  of fun t k => if (k : ℕ) ≤ t then φ ^ ((t : ℕ) - k) else 0

/-- The innovation variances `1, 1 - φ², 1 - φ², …`. -/
def ar1D (N : ℕ) (φ : ℝ) : Fin N → ℝ := fun k => if (k : ℕ) = 0 then 1 else 1 - φ ^ 2

/-- `ar1 N 1 φ = LDLᵀ`: the AR(1) factor written in its innovations. -/
theorem ar1_eq (N : ℕ) (φ : ℝ) : ar1 N 1 φ = ar1L N φ * diagonal (ar1D N φ) * (ar1L N φ)ᵀ := by
  refine Matrix.ext fun t s => ?_
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, ar1L, ar1D, ar1, of_apply, transpose_apply, one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k ≤ (t : ℕ) then φ ^ ((t : ℕ) - k) else 0)
    * (if k = 0 then 1 else 1 - φ ^ 2) * (if k ≤ (s : ℕ) then φ ^ ((s : ℕ) - k) else 0)) N]
  split_ifs with h
  · exact (ar1_sum_eq φ h s.2).symm
  · rw [← ar1_sum_eq φ (le_of_not_ge h) t.2]
    exact sum_congr rfl fun k _ => by ring

/-- **AR(1) is a valid `Γ`**: `γφ^|t-s| ⪰ 0` for `γ ≥ 0` and `|φ| ≤ 1`. -/
theorem ar1_posSemidef (N : ℕ) {γ φ : ℝ} (hγ : 0 ≤ γ) (hφ : |φ| ≤ 1) :
    (ar1 N γ φ).PosSemidef := by
  have h1 : (ar1 N 1 φ).PosSemidef := by
    rw [ar1_eq, ← conjTranspose_eq_transpose_of_trivial]
    refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun k => ?_) _
    simp only [ar1D]
    split_ifs
    · exact zero_le_one
    · have := (sq_le_one_iff_abs_le_one φ).mpr hφ
      simp only [Pi.zero_apply]; linarith
  have h : ar1 N γ φ = γ • ar1 N 1 φ := by ext t s; simp [ar1]
  rw [h]
  exact h1.smul hγ

omit [DecidableEq J] [DecidableEq T] in
/-- **The app's fitted table is positive definite**: AR(1) correlation `Φₜₛ = φ^|t-s|` with
`|φ| ≤ 1`, a factor table `A ⪰ 0`, `C ⪰ 0` and every `sⱼ² > 0`, as the projection of the
unbiased fit onto valid tables (`ConeProjection`) gives when `ŝ² > 0`. -/
theorem tableK_ar1_posDef {N : ℕ} [Fintype n] [DecidableEq n] {A C : Matrix J J ℝ} {φ : ℝ}
    {s2 : J → ℝ} {w : J → Fin N → ℝ} (hA : A.PosSemidef) (hφ : |φ| ≤ 1) (hC : C.PosSemidef)
    (hs : ∀ j, 0 < s2 j) (hw : ∀ j t, 0 < w j t) (c : n → J × Fin N) :
    (tableK A (ar1 N 1 φ) C s2 w c).PosDef :=
  tableK_posDef hA (ar1_posSemidef N zero_le_one hφ) hC hs hw c

/-- A break at known dates: months in regime `r t`, a block `G_r` within each regime and no
correlation across regimes. -/
def block {B : Type*} [DecidableEq B] (r : T → B) (G : B → Matrix T T ℝ) : Matrix T T ℝ :=
  of fun t s => if r t = r s then G (r t) t s else 0

omit [DecidableEq T] in
/-- **A block `Γ` is valid** when every block is: `G_r ⪰ 0` gives `Γ ⪰ 0`, a weighted sum as
in `Shock`. -/
theorem block_posSemidef [Fintype T] {B : Type*} [Fintype B] [DecidableEq B] (r : T → B)
    {G : B → Matrix T T ℝ} (hG : ∀ b, (G b).PosSemidef) : (block r G).PosSemidef := by
  convert posSemidef_weightedSum G hG (fun t b => if r t = b then 1 else 0) using 1
  ext t s
  by_cases h : r t = r s
  · simp [block, h, ite_mul]
  · simp [block, h, ite_mul]

omit [DecidableEq T] in
/-- **A level per regime**: `Γₜₛ = γ_r` when `t`, `s` lie in the same regime `r`, else `0`
(the factor is constant within a regime, independent across). -/
theorem regime_posSemidef [Fintype T] {B : Type*} [Fintype B] [DecidableEq B] (r : T → B)
    {γ : B → ℝ} (hγ : ∀ b, 0 ≤ γ b) :
    (of fun t s => if r t = r s then γ (r t) else 0 : Matrix T T ℝ).PosSemidef := by
  convert block_posSemidef r (G := fun b => γ b • vecMulVec (1 : T → ℝ) 1)
    fun b => (posSemidef_loadings 1).smul (hγ b) using 1
  ext t s
  simp [block]

/-! ### The target: the next 12 months of cohort `j₀` -/

variable [Fintype T]

/-- `ℓ = Cov(x, Y)` for the target `Y = Σₜ bₜX_{j₀t}` (`bₜ = 1` on the next 12 months). -/
noncomputable def ell (j₀ : J) (b : T → ℝ) : n → ℝ :=
  fun p => ∑ t, b t * M.obsCov (c p).1 j₀ (c p).2 t

/-- `v = Var Y` for the target `Y = Σₜ bₜX_{j₀t}`. -/
noncomputable def var (j₀ : J) (b : T → ℝ) : ℝ :=
  ∑ t, ∑ s, b t * b s * M.obsCov j₀ j₀ t s

/-- **`ℓ` for months not yet observed** (`b = 0` on the cell's month): only the factor and the
cohort level link the data to the target, `ℓ_{(i,t)} = λᵢλ_{j₀}(Γb)ₜ + τ²δ_{ij₀}Σₛbₛ`. -/
theorem ell_apply_of_future (j₀ : J) {b : T → ℝ} {p : n} (hb : b (c p).2 = 0) :
    M.ell c j₀ b p = M.load (c p).1 * M.load j₀ * (M.Γ *ᵥ b) (c p).2
      + M.τ2 * (if (c p).1 = j₀ then 1 else 0) * ∑ t, b t := by
  simp only [ell, obsCov, Shock.obsCov, toShock, mul_add, sum_add_distrib, mulVec, dotProduct,
    mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, hb, zero_mul, zero_add, mul_sum]
  congr 1
  · exact sum_congr rfl fun t _ => by ring
  · by_cases h : (c p).1 = j₀ <;> simp [h, mul_comm]

/-- **`v` for the target**: `v = λ_{j₀}²bᵀΓb + Σₜbₜ²(C_{j₀j₀} + s_{j₀}²/w_{j₀t}) + τ²(Σₜbₜ)²`. -/
theorem var_eq (j₀ : J) (b : T → ℝ) :
    M.var j₀ b = M.load j₀ ^ 2 * (b ⬝ᵥ (M.Γ *ᵥ b))
      + ∑ t, b t ^ 2 * (M.C j₀ j₀ + M.s2 j₀ / M.w j₀ t) + M.τ2 * (∑ t, b t) ^ 2 := by
  have h : ∀ t s, M.obsCov j₀ j₀ t s = M.load j₀ ^ 2 * M.Γ t s
      + (if t = s then M.C j₀ j₀ + M.s2 j₀ / M.w j₀ t else 0) + M.τ2 := fun t s => by
    simp [obsCov, Shock.obsCov, toShock, sq]; ring
  simp only [var, h, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, mem_univ,
    ite_true, dotProduct, mulVec, mul_sum, sq, sum_mul]
  congr 1
  · congr 1
    exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring
  · exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

/-! ### The predictor: Step 1 and Step 2 for this `K`, `ℓ`, `v` -/

variable [Fintype n] [DecidableEq n] [Fintype J] {c}

/-- **The best linear unbiased predictor** of cohort `j₀`'s next 12 months under the common
factor model, for any design `X` of fixed effects (`Core.blup_optimal`). -/
theorem blup_optimal (hc : Function.Injective c) {q : Type*} [Fintype q] [DecidableEq q]
    {X : Matrix n q ℝ} (hX : Function.Injective X.mulVec) (j₀ : J) (b : T → ℝ) (x₀ : q → ℝ)
    {d : n → ℝ} (hd : Xᵀ *ᵥ d = x₀) :
    Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) (Core.blup (M.K c) X (M.ell c j₀ b) x₀)
      ≤ Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) d :=
  Core.blup_optimal (M.K_posDef hc) hX _ _ x₀ hd

/-- **Its error** `v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r`, `r = x₀ - XᵀK⁻¹ℓ` (`Core.predMse_blup`). -/
theorem predMse_blup (hc : Function.Injective c) {q : Type*} [Fintype q] [DecidableEq q]
    {X : Matrix n q ℝ} (hX : Function.Injective X.mulVec) (j₀ : J) (b : T → ℝ) (x₀ : q → ℝ) :
    Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) (Core.blup (M.K c) X (M.ell c j₀ b) x₀)
      = M.var j₀ b - M.ell c j₀ b ⬝ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b)
        + (x₀ - Xᵀ *ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b))
          ⬝ᵥ ((Xᵀ * (M.K c)⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b))) :=
  Core.predMse_blup (M.K_posDef hc) hX _ _ x₀

/-- **With an estimated season** (Step 2): the season design on the cells' calendar months;
the target `Σₜ bₜX_{j₀t}` has mean `Σₘ Sₘ(b)βₘ`, so the predictor is unbiased iff its month
sums are those of `b`. -/
theorem blup_season_optimal (hc : Function.Injective c) {Mo : Type*} [Fintype Mo]
    [DecidableEq Mo] {mon : T → Mo} (hmon : Function.Surjective fun p => mon (c p).2) (j₀ : J)
    (b : T → ℝ) {d : n → ℝ}
    (hd : ∀ m, Season.monthSum (fun p => mon (c p).2) d m = Season.monthSum mon b m) :
    Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b)
        (Core.blup (M.K c) (Season.design fun p => mon (c p).2) (M.ell c j₀ b)
          (Season.monthSum mon b))
      ≤ Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) d :=
  M.blup_optimal hc (Season.design_mulVec_injective hmon) j₀ b _
    (by rw [Season.design_transpose_mulVec]; exact funext hd)

/-! ### Per-card dynamics: a `Γ` block per cohort

Each cohort's own deviation evolves over time with autocovariance `Gⱼ ⪰ 0` (e.g. per-cohort AR(1),
Rao & Yu 1994; Pinquet 2020), independent across cohorts: the table gets `δᵢⱼ(Gᵢ)ₜₛ` on top of
the common factor (`G = 0` is the model above). -/

section PerCohort

variable (G : J → Matrix T T ℝ)

/-- `cov(Xᵢₜ, Xⱼₛ)` with per-cohort dynamics: `obsCov + δᵢⱼ(Gᵢ)ₜₛ`. -/
noncomputable def obsCovG (i j : J) (t s : T) : ℝ :=
  M.obsCov i j t s + if i = j then G i t s else 0

variable (c)

/-- `K` with per-cohort dynamics. -/
noncomputable def KG : Matrix n n ℝ := of fun p q => M.obsCovG G (c p).1 (c q).1 (c p).2 (c q).2

/-- The per-cohort part `δᵢⱼ(Gᵢ)ₜₛ` of `K`. -/
noncomputable def cohortPart : Matrix n n ℝ :=
  of fun p q => if (c p).1 = (c q).1 then G (c p).1 (c p).2 (c q).2 else 0

/-- `ℓ` with per-cohort dynamics, for the target `Σₜ bₜX_{j₀t}`. -/
noncomputable def ellG (j₀ : J) (b : T → ℝ) : n → ℝ :=
  fun p => ∑ t, b t * M.obsCovG G (c p).1 j₀ (c p).2 t

/-- `v` with per-cohort dynamics. -/
noncomputable def varG (j₀ : J) (b : T → ℝ) : ℝ :=
  ∑ t, ∑ s, b t * b s * M.obsCovG G j₀ j₀ t s

omit [Fintype T] [Fintype n] [DecidableEq n] [Fintype J] in
theorem KG_eq_add : M.KG c G = M.K c + cohortPart c G := by
  ext p q
  simp [KG, K, cohortPart, obsCovG]

omit [Fintype n] [DecidableEq n] [Fintype J] in
/-- `ℓ` gains cohort `j₀`'s own dynamics on its own cells: `δ_{ij₀}(G_{j₀}b)ₜ`. -/
theorem ellG_eq (j₀ : J) (b : T → ℝ) :
    M.ellG c G j₀ b = M.ell c j₀ b + fun p => if (c p).1 = j₀ then (G j₀ *ᵥ b) (c p).2 else 0 := by
  funext p
  simp only [ellG, ell, obsCovG, mul_add, sum_add_distrib, Pi.add_apply]
  congr 1
  split_ifs with h
  · subst h; simp [mulVec, dotProduct, mul_comm]
  · simp

omit [Fintype J] in
/-- `v` gains `bᵀG_{j₀}b`. -/
theorem varG_eq (j₀ : J) (b : T → ℝ) : M.varG G j₀ b = M.var j₀ b + b ⬝ᵥ (G j₀ *ᵥ b) := by
  simp only [varG, var, obsCovG, ite_true, mul_add, sum_add_distrib, dotProduct, mulVec,
    mul_sum]
  congr 1
  exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

omit [DecidableEq T] [Fintype T] [DecidableEq n] in
/-- The per-cohort part is a weighted sum of the `Gⱼ`, as in `Shock`: `⪰ 0`. -/
theorem cohortPart_posSemidef (hG : ∀ j, (G j).PosSemidef) :
    (cohortPart c G).PosSemidef := by
  have h := posSemidef_weightedSum (fun j => (G j).submatrix (fun p : n => (c p).2)
    (fun p => (c p).2)) (fun j => (hG j).submatrix _) (fun p j => if (c p).1 = j then 1 else 0)
  convert h using 1
  ext p q
  by_cases hpq : (c p).1 = (c q).1
  · simp [cohortPart, hpq, ite_mul]
  · simp [cohortPart, hpq, ite_mul]

variable {c}

/-- **`K ≻ 0` with per-cohort dynamics**: the per-cohort part is `⪰ 0`. -/
theorem KG_posDef (hc : Function.Injective c)
    {G : J → Matrix T T ℝ} (hG : ∀ j, (G j).PosSemidef) : (M.KG c G).PosDef := by
  rw [M.KG_eq_add]
  exact (M.K_posDef hc).add_posSemidef (cohortPart_posSemidef c G hG)

/-- **The predictor with per-cohort dynamics** (`Core.blup_optimal`); per-cohort AR(1) is
`Gⱼ = ar1 N γⱼ φⱼ` (`ar1_posSemidef`). -/
theorem blupG_optimal (hc : Function.Injective c)
    {G : J → Matrix T T ℝ} (hG : ∀ j, (G j).PosSemidef) {q : Type*} [Fintype q]
    [DecidableEq q] {X : Matrix n q ℝ} (hX : Function.Injective X.mulVec) (j₀ : J)
    (b : T → ℝ) (x₀ : q → ℝ) {d : n → ℝ} (hd : Xᵀ *ᵥ d = x₀) :
    Core.predMse (M.KG c G) (M.ellG c G j₀ b) (M.varG G j₀ b)
        (Core.blup (M.KG c G) X (M.ellG c G j₀ b) x₀)
      ≤ Core.predMse (M.KG c G) (M.ellG c G j₀ b) (M.varG G j₀ b) d :=
  Core.blup_optimal (M.KG_posDef hc hG) hX _ _ x₀ hd

end PerCohort

/-! ### Finding 25: negative weights under AR(1) -/

/-- The example of Finding 25: two cohorts, months `0, 1, 2`, an AR(1) factor with `γ = 1`,
`φ = 1/2` and loadings `1`, no shock, process noise `1/2` and `τ² = 1`. -/
noncomputable def exAR1 : Factor (Fin 2) (Fin 3) where
  τ2 := 1
  C := 0
  s2 := fun _ => 1 / 2
  w := fun _ _ => 1
  load := fun _ => 1
  Γ := ar1 3 1 (1 / 2)
  τ2_pos := one_pos
  C_posSemidef := PosSemidef.zero
  s2_pos := fun _ => by norm_num
  w_pos := fun _ _ => one_pos
  Γ_posSemidef := ar1_posSemidef 3 zero_le_one (by rw [abs_of_pos (by norm_num)]; norm_num)

/-- Both cohorts observed in months `0` and `1`. -/
def exCells : Fin 4 → Fin 2 × Fin 3 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

/-- The predictor of cohort `0` in month `2` (one common mean) has the weights
`(11/30, 8/15, -1/30, 2/15)` on the cells `(0,0), (0,1), (1,0), (1,1)`. -/
theorem blup_exAR1 :
    Core.blup (exAR1.K exCells) (replicateCol Unit 1) (exAR1.ell exCells 0 (Pi.single 2 1))
      (fun _ => 1) = ![11 / 30, 8 / 15, -1 / 30, 2 / 15] := by
  have hc : Function.Injective exCells := by decide
  refine (Core.eq_blup_of_normal (exAR1.K_posDef hc) Core.replicateCol_one_mulVec_injective _ _
    (c := fun _ => 1 / 2) ?_ ?_).symm
  · funext p
    fin_cases p <;>
      simp [mulVec, dotProduct, Fin.sum_univ_three, K, ell, obsCov, exAR1,
        exCells, Shock.obsCov, toShock, ar1, replicateCol, Pi.single_apply, vecHead, vecTail]
      <;> norm_num
  · funext u
    rw [Core.replicateCol_one_transpose_mulVec]
    simp [Fin.sum_univ_four]
    norm_num

/-- **Negative weights under AR(1)** (Finding 25): a balanced panel, positive autocorrelation,
and still the predictor of cohort `0`'s next month puts weight `-1/30` on cohort `1`'s first month.
Cohort `1`'s change from month `0` to `1` tracks the factor, which persists into month `2`. -/
theorem blup_neg_of_ar1 :
    Core.blup (exAR1.K exCells) (replicateCol Unit 1) (exAR1.ell exCells 0 (Pi.single 2 1))
      (fun _ => 1) 2 < 0 := by
  rw [blup_exAR1]
  norm_num

end Factor
end Credibility
