import Credibility.Cumulants
import Credibility.Crossed
import Credibility.FactorHenderson

/-!
# Crossed levels: a 2×2 table cannot estimate its variances

Moment layer for `Crossed.lean` and `CrossedEstimation.lean` (paper, open directions, "Small
crossed tables"; S70). In a 2×2 table the four cell means `μ̂` span the mean, one row contrast
`r = (1, 1, −1, −1)`, one column contrast `c` and one interaction contrast `v = rc`
(`sameRow_eq`, `sameCol_eq`, `one_eq`): each variance has one degree of freedom. Hence:

* `sq_mul_trace_le`: dropping positive semidefinite parts of `K` lowers `tr(AKAK)` (from
  `tr(XY) ≥ 0` for `X, Y ⪰ 0`, `trace_mul_nonneg`);
* `sq_le_trace_row`, `sq_le_trace_col`, `sq_le_trace_cell`: **every estimator `μ̂ᵀAμ̂ − c` that does not
  depend on the common mean (`A1 = 0`) and is unbiased for `α²` (or `β²`, `γ²`) whatever the three
  variances has Gaussian variance `2 tr(AKAK) ≥ 2α⁴`** (or `2β⁴`, `2γ⁴`), for any noise covariance
  `Σ ⪰ 0` and any volumes;
* `two_mul_sq_le_variance_cell`: the actual variance, for random cell means with Gaussian third and
  fourth cumulants (`Cumulants.variance_quad_of_cumulants`);
* `bestMultiple_le_third`: so the MSE-best multiple `θ²/(θ² + V)` of such an estimate is at most `1/3`.

The pair pools of `CrossedEstimation.lean` with weights fixed in advance are such estimators
(`Model.crossed_unbiasedX`, with the noise known). More volume shrinks only `Σ`; the bound does
not move. Finding 44.
-/

open Finset Matrix

namespace Credibility
namespace CrossedSmall

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `tr(XY) ≥ 0` for positive semidefinite `X`, `Y`. -/
lemma trace_mul_nonneg {X Y : Matrix n n ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ trace (X * Y) := by
  obtain ⟨B, rfl⟩ := Model.PosSemidef.exists_eq_transpose_mul_self hY
  rw [← Matrix.mul_assoc, trace_mul_comm]
  have := (hX.mul_mul_conjTranspose_same B).trace_nonneg
  simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this

/-- `tr(AXAY) ≥ 0` for symmetric `A` and positive semidefinite `X`, `Y`. -/
lemma trace_mul_mul_mul_nonneg {A X Y : Matrix n n ℝ} (hA : Aᵀ = A) (hX : X.PosSemidef)
    (hY : Y.PosSemidef) : 0 ≤ trace (A * X * A * Y) := by
  have h := hX.conjTranspose_mul_mul_same A
  rw [conjTranspose_eq_transpose_of_trivial, hA] at h
  exact trace_mul_nonneg h hY

/-- Dropping positive semidefinite parts of `K` lowers `tr(AKAK)`: for `K = θG + R`, `θ ≥ 0`,
`G, R ⪰ 0` and symmetric `A`, `θ² tr(AGAG) ≤ tr(AKAK)`. -/
theorem sq_mul_trace_le {A G R : Matrix n n ℝ} {θ : ℝ} (hA : Aᵀ = A) (hθ : 0 ≤ θ)
    (hG : G.PosSemidef) (hR : R.PosSemidef) :
    θ ^ 2 * trace (A * G * A * G) ≤ trace (A * (θ • G + R) * A * (θ • G + R)) := by
  have e : A * (θ • G + R) * A * (θ • G + R)
      = θ ^ 2 • (A * G * A * G) + θ • (A * G * A * R) + θ • (A * R * A * G) + A * R * A * R := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul, sq]
    abel
  have hc : trace (A * R * A * G) = trace (A * G * A * R) := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, hc]
  simp only [smul_eq_mul]
  have h1 := trace_mul_mul_mul_nonneg hA hG hR
  have h2 := trace_mul_mul_mul_nonneg hA hR hR
  nlinarith

omit [DecidableEq n] in
/-- `tr(A·xyᵀ) = (Ax)·y`. -/
lemma trace_mul_vecMulVec (A : Matrix n n ℝ) (x y : n → ℝ) :
    trace (A * vecMulVec x y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [mul_vecMulVec, trace_vecMulVec]

/-! ### The 2×2 table -/

/-- The cells of a 2×2 table: (row, column). -/
abbrev Cell := Fin 2 × Fin 2

/-- The row contrast `r = (1, 1, −1, −1)`. -/
def rowC : Cell → ℝ := fun p => if p.1 = 0 then 1 else -1
/-- The column contrast `c = (1, −1, 1, −1)`. -/
def colC : Cell → ℝ := fun p => if p.2 = 0 then 1 else -1
/-- The interaction contrast `v = rc = (1, −1, −1, 1)`. -/
def intC : Cell → ℝ := fun p => rowC p * colC p

/-- Same row: `½(11ᵀ + rrᵀ)`. -/
lemma sameRow_eq : Model.sameGroup (Prod.fst : Cell → Fin 2)
    = (1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec rowC rowC) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    norm_num [Model.sameGroup, rowC, vecMulVec_apply]

/-- Same column: `½(11ᵀ + ccᵀ)`. -/
lemma sameCol_eq : Model.sameGroup (Prod.snd : Cell → Fin 2)
    = (1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec colC colC) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    norm_num [Model.sameGroup, colC, vecMulVec_apply]

/-- The identity: `¼(11ᵀ + rrᵀ + ccᵀ + vvᵀ)`. -/
lemma one_eq : (1 : Matrix Cell Cell ℝ)
    = (1 / 4 : ℝ) • (vecMulVec 1 1 + vecMulVec rowC rowC + vecMulVec colC colC
      + vecMulVec intC intC) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    norm_num [rowC, colC, intC, vecMulVec_apply, Matrix.one_apply]

lemma trace_mul_sameRow {A : Matrix Cell Cell ℝ} (h1 : A *ᵥ 1 = 0) :
    trace (A * Model.sameGroup Prod.fst) = (A *ᵥ rowC) ⬝ᵥ rowC / 2 := by
  rw [sameRow_eq, Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, trace_mul_vecMulVec,
    trace_mul_vecMulVec, h1, smul_eq_mul]
  simp; ring

lemma trace_mul_sameCol {A : Matrix Cell Cell ℝ} (h1 : A *ᵥ 1 = 0) :
    trace (A * Model.sameGroup Prod.snd) = (A *ᵥ colC) ⬝ᵥ colC / 2 := by
  rw [sameCol_eq, Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, trace_mul_vecMulVec,
    trace_mul_vecMulVec, h1, smul_eq_mul]
  simp; ring

/-- `4 tr A = rᵀAr + cᵀAc + vᵀAv` when `A1 = 0`. -/
lemma four_mul_trace {A : Matrix Cell Cell ℝ} (h1 : A *ᵥ 1 = 0) :
    4 * trace A = (A *ᵥ rowC) ⬝ᵥ rowC + (A *ᵥ colC) ⬝ᵥ colC + (A *ᵥ intC) ⬝ᵥ intC := by
  conv_lhs => rw [← Matrix.mul_one A, one_eq]
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, trace_smul, trace_add,
    trace_add, trace_add, trace_mul_vecMulVec, trace_mul_vecMulVec, trace_mul_vecMulVec,
    trace_mul_vecMulVec, h1, smul_eq_mul]
  simp

/-- With one contrast `x`: `tr(ASAS) = (tr AS)²` for `S = ½(11ᵀ + xxᵀ)`, when `A1 = 0`. -/
lemma trace_half_sq {A : Matrix Cell Cell ℝ} (h1 : A *ᵥ 1 = 0) (x : Cell → ℝ) :
    trace (A * ((1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec x x)) * A
        * ((1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec x x)))
      = trace (A * ((1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec x x))) ^ 2 := by
  have hAS : A * ((1 / 2 : ℝ) • (vecMulVec 1 1 + vecMulVec x x))
      = (1 / 2 : ℝ) • vecMulVec (A *ᵥ x) x := by
    rw [Matrix.mul_smul, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, h1]
    simp
  rw [Matrix.mul_assoc (A * _), hAS, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  simp only [trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct_smul, dotProduct_comm x]
  ring

omit [DecidableEq n] in
/-- Frobenius Cauchy–Schwarz: `(vᵀAv)² ≤ tr(AAᵀ)·‖v‖⁴`, here for symmetric `A`. -/
lemma dotProduct_sq_le {A : Matrix n n ℝ} (hA : Aᵀ = A) (v : n → ℝ) :
    ((A *ᵥ v) ⬝ᵥ v) ^ 2 ≤ trace (A * A) * (v ⬝ᵥ v) ^ 2 := by
  have e1 : (A *ᵥ v) ⬝ᵥ v = ∑ p : n × n, A p.1 p.2 * (v p.1 * v p.2) := by
    simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : trace (A * A) = ∑ p : n × n, A p.1 p.2 ^ 2 := by
    simp only [trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : A j i = A i j := by rw [← transpose_apply A i j, hA]
    rw [this, sq]
  have e3 : (v ⬝ᵥ v) ^ 2 = ∑ p : n × n, (v p.1 * v p.2) ^ 2 := by
    simp only [dotProduct, sq, Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### Unbiased estimators of the three variances -/

variable {S : Matrix Cell Cell ℝ}

/-- `E(μ̂ᵀAμ̂) − μ²1ᵀA1 = tr(AK)` splits by layer: `α² tr(A·[row]) + β² tr(A·[col]) + γ² tr A + tr(AΣ)`. -/
lemma trace_mul_K (A : Matrix Cell Cell ℝ) (α2 β2 γ2 : ℝ) :
    trace (A * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S)
      = α2 * trace (A * Model.sameGroup Prod.fst) + β2 * trace (A * Model.sameGroup Prod.snd)
        + γ2 * trace A + trace (A * S) := by
  simp only [Crossed.K, Crossed.levelCov, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul,
    smul_eq_mul, Matrix.mul_one]

/-- `Σ ⪰ 0` and nonnegative variances: the parts of `K` are positive semidefinite. -/
lemma K_eq_row (α2 β2 γ2 : ℝ) : Crossed.K Prod.fst Prod.snd α2 β2 γ2 S
    = α2 • Model.sameGroup Prod.fst
      + (β2 • Model.sameGroup Prod.snd + γ2 • (1 : Matrix Cell Cell ℝ) + S) := by
  simp only [Crossed.K, Crossed.levelCov]; abel

lemma K_eq_col (α2 β2 γ2 : ℝ) : Crossed.K Prod.fst Prod.snd α2 β2 γ2 S
    = β2 • Model.sameGroup Prod.snd
      + (α2 • Model.sameGroup Prod.fst + γ2 • (1 : Matrix Cell Cell ℝ) + S) := by
  simp only [Crossed.K, Crossed.levelCov]; abel

lemma K_eq_cell (α2 β2 γ2 : ℝ) : Crossed.K Prod.fst Prod.snd α2 β2 γ2 S
    = γ2 • (1 : Matrix Cell Cell ℝ)
      + (α2 • Model.sameGroup Prod.fst + β2 • Model.sameGroup Prod.snd + S) := by
  simp only [Crossed.K, Crossed.levelCov]; abel

/-- **A 2×2 table cannot estimate its row variance well.** Let `μ̂ᵀAμ̂ − c` (symmetric `A`, `A1 = 0`:
it does not depend on the common mean) be unbiased for `α²` whatever `α², β², γ² ≥ 0`, for the
known noise covariance `Σ ⪰ 0`. Then its Gaussian variance `2 tr(AKAK)` is at least `2α⁴`: the
standard deviation is at least `√2·α²`, at every volume. -/
theorem sq_le_trace_row {A : Matrix Cell Cell ℝ} (hA : Aᵀ = A) (h1 : A *ᵥ 1 = 0)
    (hS : S.PosSemidef)
    (hu : ∀ a b g, 0 ≤ a → 0 ≤ b → 0 ≤ g →
      trace (A * Crossed.K Prod.fst Prod.snd a b g S) = a + trace (A * S))
    {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) :
    α2 ^ 2 ≤ trace (A * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S * A
      * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S) := by
  have hr : trace (A * Model.sameGroup Prod.fst) = 1 := by
    have := hu 1 0 0 zero_le_one le_rfl le_rfl; rw [trace_mul_K] at this; linarith
  have hR : (β2 • Model.sameGroup Prod.snd + γ2 • (1 : Matrix Cell Cell ℝ) + S).PosSemidef :=
    (((Model.sameGroup_posSemidef _).smul hβ).add (PosSemidef.one.smul hγ)).add hS
  have h := sq_mul_trace_le hA hα (Model.sameGroup_posSemidef Prod.fst) hR
  rw [← K_eq_row] at h
  have h2 : trace (A * Model.sameGroup Prod.fst * A * Model.sameGroup Prod.fst) = 1 := by
    have := trace_half_sq h1 rowC
    rw [← sameRow_eq] at this; rw [this, hr]; norm_num
  rw [h2, mul_one] at h; exact h

/-- **The same for the column variance**: `2 tr(AKAK) ≥ 2β⁴` (`sq_le_trace_row` with rows and
columns swapped). -/
theorem sq_le_trace_col {A : Matrix Cell Cell ℝ} (hA : Aᵀ = A) (h1 : A *ᵥ 1 = 0)
    (hS : S.PosSemidef)
    (hu : ∀ a b g, 0 ≤ a → 0 ≤ b → 0 ≤ g →
      trace (A * Crossed.K Prod.fst Prod.snd a b g S) = b + trace (A * S))
    {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) :
    β2 ^ 2 ≤ trace (A * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S * A
      * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S) := by
  have hc : trace (A * Model.sameGroup Prod.snd) = 1 := by
    have := hu 0 1 0 le_rfl zero_le_one le_rfl; rw [trace_mul_K] at this; linarith
  have hR : (α2 • Model.sameGroup Prod.fst + γ2 • (1 : Matrix Cell Cell ℝ) + S).PosSemidef :=
    (((Model.sameGroup_posSemidef _).smul hα).add (PosSemidef.one.smul hγ)).add hS
  have h := sq_mul_trace_le hA hβ (Model.sameGroup_posSemidef Prod.snd) hR
  rw [← K_eq_col] at h
  have h2 : trace (A * Model.sameGroup Prod.snd * A * Model.sameGroup Prod.snd) = 1 := by
    have := trace_half_sq h1 colC
    rw [← sameCol_eq] at this; rw [this, hc]; norm_num
  rw [h2, mul_one] at h; exact h

/-- **The same for the cell variance**: `2 tr(AKAK) ≥ 2γ⁴`. With `A1 = 0` and no weight on the row
and column patterns, `A` must put `vᵀAv = 4` on the interaction contrast `v` (`‖v‖² = 4`), and
`tr(A²) ≥ (vᵀAv/‖v‖²)² = 1` (Cauchy–Schwarz). -/
theorem sq_le_trace_cell {A : Matrix Cell Cell ℝ} (hA : Aᵀ = A) (h1 : A *ᵥ 1 = 0)
    (hS : S.PosSemidef)
    (hu : ∀ a b g, 0 ≤ a → 0 ≤ b → 0 ≤ g →
      trace (A * Crossed.K Prod.fst Prod.snd a b g S) = g + trace (A * S))
    {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) :
    γ2 ^ 2 ≤ trace (A * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S * A
      * Crossed.K Prod.fst Prod.snd α2 β2 γ2 S) := by
  have hr : trace (A * Model.sameGroup Prod.fst) = 0 := by
    have := hu 1 0 0 zero_le_one le_rfl le_rfl; rw [trace_mul_K] at this; linarith
  have hc : trace (A * Model.sameGroup Prod.snd) = 0 := by
    have := hu 0 1 0 le_rfl zero_le_one le_rfl; rw [trace_mul_K] at this; linarith
  have hg : trace A = 1 := by
    have := hu 0 0 1 le_rfl le_rfl zero_le_one; rw [trace_mul_K] at this; linarith
  have hR : (α2 • Model.sameGroup Prod.fst + β2 • Model.sameGroup Prod.snd + S).PosSemidef :=
    (((Model.sameGroup_posSemidef _).smul hα).add ((Model.sameGroup_posSemidef _).smul hβ)).add hS
  have h := sq_mul_trace_le hA hγ PosSemidef.one hR
  rw [← K_eq_cell, Matrix.mul_one, Matrix.mul_one] at h
  have hv : (A *ᵥ intC) ⬝ᵥ intC = 4 := by
    have := four_mul_trace h1
    rw [trace_mul_sameRow h1] at hr; rw [trace_mul_sameCol h1] at hc
    linarith
  have hvv : intC ⬝ᵥ intC = 4 := by
    simp [dotProduct, intC, rowC, colC, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num
  have hcs := dotProduct_sq_le hA intC
  rw [hv, hvv] at hcs
  have : 1 ≤ trace (A * A) := by nlinarith
  nlinarith [sq_nonneg γ2]

/-! ### As random variables -/

/-- With a common mean, `varQuad` of a translation-invariant `A` with Gaussian third and fourth
cumulants is the Gaussian variance `2 tr(AKAK)`. -/
lemma varQuad_of_gaussian {ι : Type*} [Fintype ι] {A K : Matrix ι ι ℝ} (h1 : A *ᵥ 1 = 0) (μ : ℝ) :
    Cumulants.varQuad A K (fun _ => μ) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      = 2 * trace (A * K * A * K) := by
  have hm : A *ᵥ (fun _ => μ) = 0 := by
    have : (fun _ => μ : ι → ℝ) = μ • (1 : ι → ℝ) := by ext; simp
    rw [this, mulVec_smul, h1, smul_zero]
  simp [Cumulants.varQuad, hm]

/-- **Finding 44: in a 2×2 table the variance estimates are noisier than their values, at any
volume.** Let the cell means `μ̂` be random with a common mean `μ`, covariance
`K = α²[same row] + β²[same column] + γ²I + Σ` (any `Σ ⪰ 0`), and Gaussian third and fourth
cumulants (zero; e.g. normal noise and levels). Any estimator `μ̂ᵀAμ̂ − c` that does not depend on
`μ` (`A1 = 0`) and is unbiased for `γ²` whatever `α², β², γ² ≥ 0` has variance at least `2γ⁴`:
its coefficient of variation is at least `√2`, so its MSE-best multiple is below `1/3`
(`bestMultiple_le_third`). The same holds for `α²` and `β²` (`sq_le_trace_row`, `_col`). -/
theorem two_mul_sq_le_variance_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (Z : Cell → Ω → ℝ) {A : Matrix Cell Cell ℝ} (hA : Aᵀ = A) (h1 : A *ᵥ 1 = 0)
    (hS : S.PosSemidef)
    (hu : ∀ a b g, 0 ≤ a → 0 ≤ b → 0 ≤ g →
      trace (A * Crossed.K Prod.fst Prod.snd a b g S) = g + trace (A * S))
    {α2 β2 γ2 μ : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2)
    (hZ : ∀ i, MeasureTheory.MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, ProbabilityTheory.covariance (Z i) (Z j) P
      = Crossed.K Prod.fst Prod.snd α2 β2 γ2 S i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) ∂P = 0)
    (h4 : Cumulants.HasFourthCumulant Z (fun _ => μ) (Crossed.K Prod.fst Prod.snd α2 β2 γ2 S)
      (fun _ _ _ _ => 0) P) :
    2 * γ2 ^ 2 ≤ ProbabilityTheory.variance (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω) P := by
  have hAs : ∀ i j, A j i = A i j := fun i j => by rw [← transpose_apply A i j, hA]
  rw [Cumulants.variance_quad_of_cumulants Z A _ _ _ _ hAs hZ hm hc h3 h4, varQuad_of_gaussian h1]
  linarith [sq_le_trace_cell hA h1 hS hu hα hβ hγ]

/-- The MSE-best multiple `c = θ²/(θ² + V)` of an unbiased estimate (`E(cθ̂ − θ)² = (1 − c)²θ² + c²V`)
is at most `1/3` when `V ≥ 2θ²`. -/
lemma bestMultiple_le_third {θ V : ℝ} (hV : 2 * θ ^ 2 ≤ V) (hpos : 0 < θ ^ 2 + V) :
    θ ^ 2 / (θ ^ 2 + V) ≤ 1 / 3 := by
  rw [div_le_iff₀ hpos]; linarith

end CrossedSmall
end Credibility
