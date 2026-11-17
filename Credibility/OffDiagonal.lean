import Mathlib

/-!
# Tapering a positive semidefinite matrix

Multiplying a covariance matrix `K` entrywise by a *correlation matrix* `R`
(positive semidefinite with unit diagonal) keeps the variances and keeps `K`
positive semidefinite, and positive definite if `K` is: this is the Schur
product theorem (Mathlib's `Matrix.PosSemidef.hadamard`), plus an
Oppenheim-type strengthening for the definite case (`R` need not be
definite). Covariance tapering (Furrer–Genton–Nychka 2006) is this operation.

Two tapers are corollaries:
* **damping**: multiplying the off-diagonal entries by `ρ ∈ [0,1]`
  (`shrinkOffDiag`), the taper `R = ρ·11ᵀ + (1-ρ)·I`. README "Later goals →
  Small lemmas" (b), from the clustering paper (a covariance matrix with
  damped correlations);
* **distance taper**: `ρ^|tᵢ - tⱼ|` for cohorts at positions `tᵢ ∈ ℕ`
  (`distTaper`). With `t = id` on `Fin n` it is the Kac–Murdock–Szegő
  matrix, but its proof uses no KMS algebra: it is a Hadamard product of
  two-block matrices, one per gap between consecutive positions, so the
  Schur product theorem applies once more. Ties are allowed.

Not in the thesis.
-/

open Matrix

/-- A positive definite matrix dominates a positive multiple of the identity:
`A - c • 1 ⪰ 0` for some `c > 0` (the least eigenvalue). -/
theorem Matrix.PosDef.exists_posSemidef_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  cases isEmpty_or_nonempty n
  · exact ⟨1, one_pos, by rw [Subsingleton.elim (A - (1 : ℝ) • (1 : Matrix n n ℝ)) 0]; exact PosSemidef.zero⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
  refine ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, ?_⟩
  rw [posSemidef_iff_isHermitian_and_spectrum_nonneg]
  refine ⟨hA.1.sub (isHermitian_one.smul (IsSelfAdjoint.all _)), fun x hx => ?_⟩
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq] at hx
  obtain ⟨y, hy, z, rfl, rfl⟩ := hx
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hy
  obtain ⟨i, rfl⟩ := hy
  exact sub_nonneg.mpr (hi₀ i (Finset.mem_univ i))

namespace Credibility

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The general result: a correlation matrix as taper -/

/-- **Oppenheim-type Schur product theorem**: if `A ≻ 0` and `B ⪰ 0` has a
positive diagonal, then `A ⊙ B ≻ 0`. Write `A = (A - c·1) + c·1` with
`A - c·1 ⪰ 0`; then `A ⊙ B = (A - c·1) ⊙ B + c·diag(B)`, a positive
semidefinite plus a positive definite diagonal matrix. -/
theorem posDef_hadamard_of_diag_pos {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosSemidef)
    (hd : ∀ i, 0 < B i i) : (A ⊙ B).PosDef := by
  obtain ⟨c, hc, hAc⟩ := hA.exists_posSemidef_sub_smul_one
  have h : A ⊙ B = (A - c • 1) ⊙ B + c • diagonal B.diag := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hadamard]; ring
    · simp [hadamard, h, Matrix.one_apply_ne h]
  rw [h]
  exact PosDef.posSemidef_add (hAc.hadamard hB) ((PosDef.diagonal hd).smul hc)

omit [Fintype n] [DecidableEq n] in
/-- Tapering by a correlation matrix keeps the variances. -/
theorem hadamard_diag_of_corr {R K : Matrix n n ℝ} (hR1 : ∀ i, R i i = 1) (i : n) :
    (R ⊙ K) i i = K i i := by
  simp [hadamard, hR1]

omit [Fintype n] [DecidableEq n] in
/-- **Tapering keeps positive semidefiniteness**: if `R ⪰ 0` (a correlation
matrix, say) and `K ⪰ 0`, then `R ⊙ K ⪰ 0` (Schur product theorem). -/
theorem posSemidef_hadamard_of_corr {R K : Matrix n n ℝ} (hR : R.PosSemidef)
    (hK : K.PosSemidef) : (R ⊙ K).PosSemidef :=
  hR.hadamard hK

/-- **…and positive definiteness**: if `R ⪰ 0` has unit diagonal and `K ≻ 0`,
then `R ⊙ K ≻ 0`. `R` itself need not be definite (e.g. `R = 11ᵀ`). -/
theorem posDef_hadamard_of_corr {R K : Matrix n n ℝ} (hR : R.PosSemidef) (hR1 : ∀ i, R i i = 1)
    (hK : K.PosDef) : (R ⊙ K).PosDef := by
  rw [hadamard_comm]
  exact posDef_hadamard_of_diag_pos hK hR fun i => by rw [hR1]; exact one_pos

/-! ### Damping: multiplying the off-diagonal entries by `ρ` -/

omit [Fintype n] in
/-- `A` with its off-diagonal entries multiplied by `ρ`. -/
def shrinkOffDiag (ρ : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if i = j then A i j else ρ * A i j

omit [Fintype n] in
/-- The shrunk matrix is `ρ • A + (1 - ρ) • diag(A)`. -/
theorem shrinkOffDiag_eq (ρ : ℝ) (A : Matrix n n ℝ) :
    shrinkOffDiag ρ A = ρ • A + (1 - ρ) • diagonal A.diag := by
  ext i j
  by_cases h : i = j
  · subst h; simp [shrinkOffDiag]; ring
  · simp [shrinkOffDiag, h]

omit [Fintype n] in
/-- Damping is tapering by `R = ρ·11ᵀ + (1-ρ)·I` (`1` on the diagonal, `ρ`
off it). -/
theorem shrinkOffDiag_eq_hadamard (ρ : ℝ) (A : Matrix n n ℝ) :
    shrinkOffDiag ρ A = shrinkOffDiag ρ (of fun _ _ => 1) ⊙ A := by
  ext i j
  by_cases h : i = j <;> simp [shrinkOffDiag, hadamard, h]

omit [Fintype n] in
/-- The damping taper is `ρ·11ᵀ + (1-ρ)·I`. -/
lemma shrinkOffDiag_one_eq (ρ : ℝ) :
    shrinkOffDiag ρ (of fun _ _ => (1 : ℝ) : Matrix n n ℝ)
      = ρ • (of fun _ _ => (1 : ℝ)) + (1 - ρ) • (1 : Matrix n n ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [shrinkOffDiag, h]

omit [DecidableEq n] in
/-- The all-ones matrix `11ᵀ` is positive semidefinite. -/
lemma posSemidef_ones : (of fun _ _ => (1 : ℝ) : Matrix n n ℝ).PosSemidef := by
  simpa [vecMulVec] using posSemidef_vecMulVec_self_star (1 : n → ℝ)

/-- Shrinking the off-diagonal entries by `ρ ∈ [0,1]` keeps a matrix positive
semidefinite. -/
theorem posSemidef_shrinkOffDiag {A : Matrix n n ℝ} (hA : A.PosSemidef) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : (shrinkOffDiag ρ A).PosSemidef := by
  rw [shrinkOffDiag_eq_hadamard, shrinkOffDiag_one_eq]
  exact posSemidef_hadamard_of_corr
    ((posSemidef_ones.smul h0).add (PosSemidef.one.smul (sub_nonneg.mpr h1))) hA

/-- …and positive definite if `ρ < 1` and the diagonal is positive. -/
theorem posDef_shrinkOffDiag {A : Matrix n n ℝ} (hA : A.PosSemidef) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hd : ∀ i, 0 < A i i) : (shrinkOffDiag ρ A).PosDef := by
  rw [shrinkOffDiag_eq_hadamard, shrinkOffDiag_one_eq]
  exact posDef_hadamard_of_diag_pos
    (PosDef.posSemidef_add (posSemidef_ones.smul h0) (PosDef.one.smul (sub_pos.mpr h1))) hA hd

/-! ### The distance taper `ρ^|tᵢ - tⱼ|` -/

omit [Fintype n] [DecidableEq n] in
/-- The distance taper: cohorts at positions `t i ∈ ℕ`, correlation
`ρ^|tᵢ - tⱼ|`. With `t = id` it is the Kac–Murdock–Szegő matrix. -/
def distTaper (ρ : ℝ) (t : n → ℕ) : Matrix n n ℝ :=
  of fun i j => ρ ^ Nat.dist (t i) (t j)

omit [Fintype n] [DecidableEq n] in
/-- Unit diagonal. -/
@[simp] lemma distTaper_self (ρ : ℝ) (t : n → ℕ) (i : n) : distTaper ρ t i i = 1 := by
  simp [distTaper]

omit [DecidableEq n] in
/-- A two-block matrix (`1` within a side, `ρ` across) is positive semidefinite
for `ρ ∈ [0,1]`: it is `ρ·11ᵀ + (1-ρ)(uuᵀ + vvᵀ)` with `u`, `v` the side
indicators. -/
lemma posSemidef_twoBlock (s : n → Bool) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (of fun i j => if s i = s j then 1 else ρ : Matrix n n ℝ).PosSemidef := by
  set u : n → ℝ := fun i => if s i then 1 else 0
  set v : n → ℝ := fun i => if s i then 0 else 1
  have h : (of fun i j => if s i = s j then 1 else ρ : Matrix n n ℝ)
      = ρ • (of fun _ _ => (1 : ℝ)) + (1 - ρ) • (vecMulVec u u + vecMulVec v v) := by
    ext i j
    cases hi : s i <;> cases hj : s j <;> simp [u, v, vecMulVec_apply, hi, hj]
  have hu := posSemidef_vecMulVec_self_star u
  have hv := posSemidef_vecMulVec_self_star v
  simp only [star_trivial] at hu hv
  rw [h]
  exact (posSemidef_ones.smul h0).add ((hu.add hv).smul (sub_nonneg.mpr h1))

omit [DecidableEq n] in
/-- A Hadamard product of two-block matrices is positive semidefinite (Schur). -/
lemma posSemidef_prod_twoBlock (s : ℕ → n → Bool) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (N : ℕ) :
    (of fun i j => ∏ k ∈ Finset.range N, if s k i = s k j then 1 else ρ :
      Matrix n n ℝ).PosSemidef := by
  induction N with
  | zero => simpa using posSemidef_ones
  | succ N ih =>
    have h : (of fun i j => ∏ k ∈ Finset.range (N + 1), if s k i = s k j then 1 else ρ :
        Matrix n n ℝ) = (of fun i j => ∏ k ∈ Finset.range N, if s k i = s k j then 1 else ρ)
          ⊙ (of fun i j => if s N i = s N j then 1 else ρ) := by
      ext i j; simp [hadamard, Finset.prod_range_succ]
    rw [h]
    exact ih.hadamard (posSemidef_twoBlock (s N) h0 h1)

/-- The gaps `k < N` that separate `a` and `b` (`a ≤ k` but not `b ≤ k`, or
the reverse) are the `|a - b|` gaps between them. -/
lemma card_separating (a b N : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    ((Finset.range N).filter fun k => ¬decide (a ≤ k) = decide (b ≤ k)).card = Nat.dist a b := by
  have h : ((Finset.range N).filter fun k => ¬decide (a ≤ k) = decide (b ≤ k))
      = Finset.Ico a b ∪ Finset.Ico b a := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
      decide_eq_decide]
    omega
  rw [h, Finset.card_union_of_disjoint, Nat.card_Ico, Nat.card_Ico, Nat.dist, add_comm]
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [Finset.mem_Ico] at hk hk'
  omega

omit [Fintype n] [DecidableEq n] in
/-- `ρ^|tᵢ - tⱼ|` is the product over the gaps `k` of `1` (same side of `k`)
or `ρ` (opposite sides). -/
lemma distTaper_eq_prod (ρ : ℝ) (t : n → ℕ) {N : ℕ} (hN : ∀ i, t i ≤ N) :
    distTaper ρ t = of fun i j =>
      ∏ k ∈ Finset.range N, if decide (t i ≤ k) = decide (t j ≤ k) then 1 else ρ := by
  ext i j
  rw [distTaper, of_apply, of_apply, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const, card_separating _ _ _ (hN i) (hN j)]

omit [DecidableEq n] in
/-- **The distance taper is a correlation matrix**: `ρ^|tᵢ - tⱼ| ⪰ 0` for
`ρ ∈ [0,1]`, for any positions (ties allowed). No Kac–Murdock–Szegő algebra is
needed: it is a Hadamard product of two-block matrices. -/
theorem distTaper_posSemidef (t : n → ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (distTaper ρ t).PosSemidef := by
  rw [distTaper_eq_prod ρ t (N := Finset.univ.sup t) fun i => Finset.le_sup (Finset.mem_univ i)]
  exact posSemidef_prod_twoBlock (fun k i => decide (t i ≤ k)) h0 h1 _

omit [DecidableEq n] in
/-- Tapering a covariance matrix by distance keeps it positive semidefinite… -/
theorem posSemidef_distTaper_hadamard {K : Matrix n n ℝ} (hK : K.PosSemidef) (t : n → ℕ)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : (distTaper ρ t ⊙ K).PosSemidef :=
  posSemidef_hadamard_of_corr (distTaper_posSemidef t h0 h1) hK

/-- …and positive definite if it was, whatever the positions (ties allowed). -/
theorem posDef_distTaper_hadamard {K : Matrix n n ℝ} (hK : K.PosDef) (t : n → ℕ)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : (distTaper ρ t ⊙ K).PosDef :=
  posDef_hadamard_of_corr (distTaper_posSemidef t h0 h1) (distTaper_self ρ t) hK

end Credibility
