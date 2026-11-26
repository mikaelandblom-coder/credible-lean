import Credibility.FitStatistics
import Credibility.CrossedEstimation

/-!
# Crossed levels: the best pool of pair estimators within a class

Moment layer for `CrossedEstimation.lean` (`studies/PLAN.md`, crossed entry, general targets
(1) and (3)). Every pool `Σₚ aₚP̂ₚ` of the pair estimators of one class with `Σₚ aₚ = 1` is
unbiased (`pairPool_unbiasedX`); which has the least variance?

* `Cumulants.variance_sum_quad`: the variance of `Σₚ aₚ xᵀAₚx` is `aᵀVa`, `V` the table of
  `Cumulants.covQuad` (moments up to order four, distribution-free); so the minimum-variance
  combination with `Σ a = 1` is GLS on `V` (`Cumulants.quadPool_gls_optimal`);
* `isQuadForm_pairHat`, `symMat`: each `P̂ₚ` is a quadratic form, with a symmetric matrix by
  polarization; `variance_pairPool`, `pairPool_gls_optimal`: **the minimum-variance unbiased pool
  within a class is GLS on the pair estimators' covariance table**;
* `equalWeight_optimal`, `mulVec_one_eq_of_transitive`: if the rows of a covariance table have
  equal sums, equal weights are optimal, and a symmetry group acting transitively forces that;
* `pairPool_equal_optimal_of_balanced`: **in a balanced table equal weights are exactly optimal**
  when the moment tables are invariant under permuting rows and columns.

Only moments up to order four are assumed; the normal case is `CrossedPoolNormal.lean`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Credibility

namespace Cumulants

variable {ι I : Type*} [Fintype ι] [Fintype I]

/-- The covariance table of a family `(xᵀAₚx)ₚ` of quadratic estimators. -/
noncomputable def quadCovTable (A : I → Matrix ι ι ℝ) (C : Matrix ι ι ℝ) (m : ι → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ) : Matrix I I ℝ :=
  Matrix.of fun p q => covQuad (A p) (A q) C m κ₃ κ₄

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The variance of a combination of quadratic estimators** is `aᵀVa`, `Vₚ_q = covQuad Aₚ A_q`.
For random cells with mean, covariance, third and fourth cumulant tables `m`, `C`, `κ₃`, `κ₄`
and symmetric `Aₚ`. -/
theorem variance_sum_quad (Z : ι → Ω → ℝ) (A : I → Matrix ι ι ℝ) (C : Matrix ι ι ℝ)
    (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (hA : ∀ p i j, A p j i = A p i j)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) (a : I → ℝ) :
    Var[fun ω => ∑ p, a p * ∑ i, ∑ j, A p i j * Z i ω * Z j ω; P]
      = a ⬝ᵥ (quadCovTable A C m κ₃ κ₄ *ᵥ a) := by
  have hL : ∀ p, MemLp (fun ω => a p * ∑ i, ∑ j, A p i j * Z i ω * Z j ω) 2 P := fun p =>
    (memLp_quadForm hZ (A p)).const_mul (a p)
  rw [← covariance_self (memLp_finsetSum _ fun p _ => hL p).aemeasurable,
    covariance_fun_sum_fun_sum hL hL]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    covariance_quad_of_cumulants Z _ _ C m κ₃ κ₄ (hA _) (hA _) hZ hm hc h3 h4]
  simp only [dotProduct, mulVec, quadCovTable, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- **The minimum-variance combination of quadratic estimators with weights summing to one is
GLS on their covariance table** (`glsWeight_optimal`), when that table is positive definite. -/
theorem quadPool_gls_optimal (Z : ι → Ω → ℝ) (A : I → Matrix ι ι ℝ) (C : Matrix ι ι ℝ)
    (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (hA : ∀ p i j, A p j i = A p i j)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    [DecidableEq I] (hV : (quadCovTable A C m κ₃ κ₄).PosDef) (b : I → ℝ) (hb : ∑ p, b p = 1) :
    Var[fun ω => ∑ p, glsWeight (quadCovTable A C m κ₃ κ₄) p
        * ∑ i, ∑ j, A p i j * Z i ω * Z j ω; P]
      ≤ Var[fun ω => ∑ p, b p * ∑ i, ∑ j, A p i j * Z i ω * Z j ω; P] := by
  rw [variance_sum_quad Z A C m κ₃ κ₄ hA hZ hm hc h3 h4,
    variance_sum_quad Z A C m κ₃ κ₄ hA hZ hm hc h3 h4]
  exact glsWeight_optimal hV b hb

end Cumulants

section EqualWeights

variable {I : Type*} [Fintype I]

/-- **Equal weights are optimal when the rows of `V` have equal sums.** For a symmetric positive
semidefinite `V` with `V1 = c1`, the weights `1/n` minimize `bᵀVb` subject to `Σ b = 1`
(no `V ≻ 0` needed): `b = 1/n + d` with `Σ d = 0`, and `dᵀV1 = c Σ d = 0`. -/
theorem equalWeight_optimal (V : Matrix I I ℝ) (hsymm : ∀ p q, V q p = V p q)
    (hpsd : ∀ d, 0 ≤ d ⬝ᵥ (V *ᵥ d)) {c : ℝ} (hc : V *ᵥ 1 = c • 1) (b : I → ℝ)
    (hb : ∑ p, b p = 1) :
    (fun _ => (Fintype.card I : ℝ)⁻¹) ⬝ᵥ (V *ᵥ fun _ => (Fintype.card I : ℝ)⁻¹)
      ≤ b ⬝ᵥ (V *ᵥ b) := by
  have hne : Nonempty I := by
    by_contra h; rw [not_nonempty_iff] at h; simp at hb
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set e : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹
  set d := b - e
  have hd : ∑ p, d p = 0 := by
    simp only [d, e, Pi.sub_apply, Finset.sum_sub_distrib, hb, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp; ring
  have hVe : V *ᵥ e = fun _ => (Fintype.card I : ℝ)⁻¹ * c := by
    have : e = (Fintype.card I : ℝ)⁻¹ • (1 : I → ℝ) := by ext; simp [e]
    rw [this, mulVec_smul, hc]; ext; simp
  have hdVe : d ⬝ᵥ (V *ᵥ e) = 0 := by
    rw [hVe]; simp only [dotProduct, ← Finset.sum_mul, hd, zero_mul]
  have heVd : e ⬝ᵥ (V *ᵥ d) = 0 := by
    rw [dotProduct_mulVec, ← hdVe, dotProduct_comm, ← mulVec_transpose]
    congr 2; ext p q; exact hsymm p q
  have hbd : b = e + d := by simp [d]
  rw [hbd, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hdVe, heVd]
  linarith [hpsd d]

/-- If a permutation of `I` carries any index to any other and leaves `V` invariant, every row
of `V` has the same sum. -/
theorem mulVec_one_eq_of_transitive (V : Matrix I I ℝ)
    (htrans : ∀ p q, ∃ σ : Equiv.Perm I, σ p = q ∧ ∀ a b, V (σ a) (σ b) = V a b) (p₀ : I) :
    V *ᵥ 1 = (V *ᵥ 1) p₀ • 1 := by
  ext q
  obtain ⟨σ, hσ, hV⟩ := htrans p₀ q
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.smul_apply, smul_eq_mul]
  rw [← hσ, ← Equiv.sum_comp σ]
  simp only [hV]

end EqualWeights

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-! ### Quadratic and linear estimators -/

/-- `f` is a quadratic form in the data. -/
def IsQuadForm (f : (J × T → ℝ) → ℝ) : Prop := ∃ Q : J × T → J × T → ℝ, ∀ X, quad Q X = f X

/-- `f` is a linear form in the data. -/
def IsLinForm (f : (J × T → ℝ) → ℝ) : Prop := ∃ ℓ : J × T → ℝ, ∀ X, ∑ p, ℓ p * X p = f X

omit [DecidableEq J] [DecidableEq T] in
lemma IsLinForm.add {f g : (J × T → ℝ) → ℝ} (hf : IsLinForm f) (hg : IsLinForm g) :
    IsLinForm fun X => f X + g X := by
  obtain ⟨ℓ, hℓ⟩ := hf; obtain ⟨ℓ', hℓ'⟩ := hg
  exact ⟨ℓ + ℓ', fun X => by simp [add_mul, Finset.sum_add_distrib, hℓ, hℓ']⟩

omit [DecidableEq J] [DecidableEq T] in
lemma IsLinForm.const_mul {f : (J × T → ℝ) → ℝ} (hf : IsLinForm f) (c : ℝ) :
    IsLinForm fun X => c * f X := by
  obtain ⟨ℓ, hℓ⟩ := hf
  exact ⟨c • ℓ, fun X => by simp [← hℓ, Finset.mul_sum, mul_assoc]⟩

omit [DecidableEq J] [DecidableEq T] in
lemma IsLinForm.sub {f g : (J × T → ℝ) → ℝ} (hf : IsLinForm f) (hg : IsLinForm g) :
    IsLinForm fun X => f X - g X := by
  simpa [sub_eq_add_neg] using hf.add (hg.const_mul (-1))

lemma isLinForm_eval (q : J × T) : IsLinForm fun X => X q :=
  ⟨Pi.single q 1, fun X => by simp [Pi.single_apply]⟩

omit [DecidableEq J] [DecidableEq T] in
lemma isLinForm_sum {K : Type*} (s : Finset K) {f : K → (J × T → ℝ) → ℝ}
    (hf : ∀ k ∈ s, IsLinForm (f k)) : IsLinForm fun X => ∑ k ∈ s, f k X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun X => by simp⟩
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self k s)).add (ih fun k' h => hf k' (Finset.mem_insert_of_mem h))

omit [DecidableEq J] [DecidableEq T] in
lemma IsQuadForm.add {f g : (J × T → ℝ) → ℝ} (hf : IsQuadForm f) (hg : IsQuadForm g) :
    IsQuadForm fun X => f X + g X := by
  obtain ⟨Q, hQ⟩ := hf; obtain ⟨Q', hQ'⟩ := hg
  exact ⟨Q + Q', fun X => by simp [quad, add_mul, Finset.sum_add_distrib, ← hQ, ← hQ']⟩

omit [DecidableEq J] [DecidableEq T] in
lemma IsQuadForm.const_mul {f : (J × T → ℝ) → ℝ} (hf : IsQuadForm f) (c : ℝ) :
    IsQuadForm fun X => c * f X := by
  obtain ⟨Q, hQ⟩ := hf
  exact ⟨c • Q, fun X => by simp [quad, ← hQ, Finset.mul_sum, mul_assoc]⟩

omit [DecidableEq J] [DecidableEq T] in
lemma IsQuadForm.sub {f g : (J × T → ℝ) → ℝ} (hf : IsQuadForm f) (hg : IsQuadForm g) :
    IsQuadForm fun X => f X - g X := by
  simpa [sub_eq_add_neg] using hf.add (hg.const_mul (-1))

omit [DecidableEq J] [DecidableEq T] in
lemma isQuadForm_sum {K : Type*} (s : Finset K) {f : K → (J × T → ℝ) → ℝ}
    (hf : ∀ k ∈ s, IsQuadForm (f k)) : IsQuadForm fun X => ∑ k ∈ s, f k X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun X => by simp [quad]⟩
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self k s)).add (ih fun k' h => hf k' (Finset.mem_insert_of_mem h))

omit [DecidableEq J] [DecidableEq T] in
lemma IsLinForm.mul {f g : (J × T → ℝ) → ℝ} (hf : IsLinForm f) (hg : IsLinForm g) :
    IsQuadForm fun X => f X * g X := by
  obtain ⟨ℓ, hℓ⟩ := hf; obtain ⟨ℓ', hℓ'⟩ := hg
  refine ⟨fun p q => ℓ p * ℓ' q, fun X => ?_⟩
  show _ = f X * g X
  rw [← hℓ, ← hℓ', Finset.sum_mul_sum]
  simp only [quad]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

lemma isLinForm_muHat (w : J → T → ℝ) (j : J) : IsLinForm fun X => muHat w X j :=
  isLinForm_sum _ fun t _ => (isLinForm_eval (j, t)).const_mul _

lemma isQuadForm_sigRhoHat (w : J → T → ℝ) (i j : J) : IsQuadForm fun X => sigRhoHat w X i j := by
  have h := (isQuadForm_sum Finset.univ fun t _ =>
    (((isLinForm_eval (i, t)).sub (isLinForm_muHat w i)).mul
      ((isLinForm_eval (j, t)).sub (isLinForm_muHat w j))).const_mul (√(w i t * w j t))).const_mul
    (sqrtSum w i j + ((Fintype.card T : ℝ) - 2) * wtot w i * wtot w j / sqrtSum w i j)⁻¹
  refine h.imp fun Q hQ X => (hQ X).trans ?_
  simp only [sigRhoHat, div_eq_inv_mul, mul_assoc]

/-- The pair estimator `P̂ᵢⱼ` is a quadratic form in the data. -/
lemma isQuadForm_pairHat (w : J → T → ℝ) (i j : J) : IsQuadForm fun X => pairHat w X i j := by
  have hd := (isLinForm_muHat w i).sub (isLinForm_muHat w j)
  have h := (hd.mul hd).sub (((isQuadForm_sigRhoHat w i i).add (isQuadForm_sigRhoHat w j j)).sub
    ((isQuadForm_sigRhoHat w i j).const_mul 2))
  refine h.imp fun Q hQ X => (hQ X).trans ?_
  simp only [pairHat, sq]

/-! ### The symmetric matrix of a quadratic estimator -/

/-- The symmetric matrix of a quadratic form `f`, by polarization:
`Aₐ_b = (f(1ₐ + 1_b) - f(1ₐ) - f(1_b))/2`. -/
noncomputable def symMat (f : (J × T → ℝ) → ℝ) : Matrix (J × T) (J × T) ℝ :=
  Matrix.of fun a b => (f (Pi.single a 1 + Pi.single b 1) - f (Pi.single a 1) - f (Pi.single b 1)) / 2

omit [Fintype J] [Fintype T] in
lemma symMat_symm (f : (J × T → ℝ) → ℝ) (a b : J × T) : symMat f b a = symMat f a b := by
  simp only [symMat, Matrix.of_apply]
  rw [add_comm (Pi.single b (1 : ℝ) : J × T → ℝ)]; ring

lemma quad_symMat {f : (J × T → ℝ) → ℝ} (hf : IsQuadForm f) (X : J × T → ℝ) :
    quad (symMat f) X = f X := by
  obtain ⟨Q, hQ⟩ := hf
  have hs : ∀ a b, symMat f a b = (Q a b + Q b a) / 2 := fun a b => by
    simp only [symMat, Matrix.of_apply, ← hQ, quad, Pi.add_apply, Pi.single_apply]
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [← hQ]
  simp only [quad, hs, add_div, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => Q y x / 2 * X x * X y), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ### The minimum-variance pool within a class -/

/-- The covariance table of the pair estimators of `S`, from the moment tables of the cells
(`Cumulants.covQuad`). -/
noncomputable def pairCovTable (w : J → T → ℝ) (S : Finset (J × J))
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ) : Matrix S S ℝ :=
  Cumulants.quadCovTable (fun p : S => symMat fun X => pairHat w X p.1.1 p.1.2) C m κ₃ κ₄

/-- The GLS weights on the pair covariance table, as weights on all pairs (zero outside `S`). -/
noncomputable def pairGLS (w : J → T → ℝ) (S : Finset (J × J)) (C : Matrix (J × T) (J × T) ℝ)
    (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ) (p : J × J) : ℝ :=
  if h : p ∈ S then glsWeight (pairCovTable w S C m κ₃ κ₄) ⟨p, h⟩ else 0

lemma pairPool_eq_sum_subtype (w : J → T → ℝ) (S : Finset (J × J)) (a : J × J → ℝ)
    (X : J × T → ℝ) :
    pairPool w S a X = ∑ p : S, a p.1 * ∑ i, ∑ j,
      symMat (fun X => pairHat w X p.1.1 p.1.2) i j * X i * X j := by
  rw [pairPool, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun p _ =>
    congrArg (a p.1 * ·) (quad_symMat (isQuadForm_pairHat w _ _) X).symm

lemma sum_pairGLS (w : J → T → ℝ) {S : Finset (J × J)} (hS : S.Nonempty)
    {C : Matrix (J × T) (J × T) ℝ} {m : J × T → ℝ} {κ₃ : J × T → J × T → J × T → ℝ}
    {κ₄ : J × T → J × T → J × T → J × T → ℝ} (hV : (pairCovTable w S C m κ₃ κ₄).PosDef) :
    ∑ p ∈ S, pairGLS w S C m κ₃ κ₄ p = 1 := by
  have : Nonempty S := hS.to_subtype
  rw [← Finset.sum_coe_sort S, ← sum_glsWeight hV]
  exact Finset.sum_congr rfl fun p _ => by simp [pairGLS, p.2]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The variance of a pair pool** is `aᵀVa`, `V` the covariance table of the pair estimators
(from the mean, covariance, third and fourth cumulant tables of the cells; distribution-free). -/
theorem variance_pairPool (w : J → T → ℝ) (S : Finset (J × J)) (Z : J × T → Ω → ℝ)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) (a : J × J → ℝ) :
    Var[fun ω => pairPool w S a (Z · ω); P]
      = (fun p : S => a p.1) ⬝ᵥ (pairCovTable w S C m κ₃ κ₄ *ᵥ fun p : S => a p.1) := by
  rw [show (fun ω => pairPool w S a (Z · ω)) = fun ω => ∑ p : S, a p.1 * ∑ i, ∑ j,
      symMat (fun X => pairHat w X p.1.1 p.1.2) i j * Z i ω * Z j ω from
    funext fun ω => pairPool_eq_sum_subtype w S a _]
  exact Cumulants.variance_sum_quad Z (fun p : S => symMat fun X => pairHat w X p.1.1 p.1.2)
    C m κ₃ κ₄ (fun p i j => symMat_symm _ i j) hZ hm hc h3 h4 (fun p : S => a p.1)

/-- **The minimum-variance unbiased pool within a class is GLS on the pair estimators'
covariance table.** Among weights summing to one on `S` (the pools unbiased for the class's
value, `pairPool_unbiasedX`), the GLS weights `V⁻¹1/1ᵀV⁻¹1` of the table `V` of
`cov(P̂ₚ, P̂_q)` (`Cumulants.covQuad`, from the moment tables of the cells) have the least
variance. Distribution-free: only moments up to order four enter. -/
theorem pairPool_gls_optimal (w : J → T → ℝ) (S : Finset (J × J)) (Z : J × T → Ω → ℝ)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hV : (pairCovTable w S C m κ₃ κ₄).PosDef) (b : J × J → ℝ) (hb : ∑ p ∈ S, b p = 1) :
    Var[fun ω => pairPool w S (pairGLS w S C m κ₃ κ₄) (Z · ω); P]
      ≤ Var[fun ω => pairPool w S b (Z · ω); P] := by
  rw [variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4,
    variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4]
  have hg : (fun p : S => pairGLS w S C m κ₃ κ₄ p.1) = glsWeight (pairCovTable w S C m κ₃ κ₄) := by
    ext p; simp [pairGLS, p.2]
  rw [hg]
  exact glsWeight_optimal hV _ (by rw [Finset.sum_coe_sort S b]; exact hb)

/-- `cov(P̂ₚ, P̂_q) = V_pq` for any random cells with these moment tables. -/
lemma pairCovTable_eq_covariance (w : J → T → ℝ) (S : Finset (J × J)) (Z : J × T → Ω → ℝ)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) (p q : S) :
    pairCovTable w S C m κ₃ κ₄ p q
      = covariance (fun ω => pairHat w (Z · ω) p.1.1 p.1.2)
          (fun ω => pairHat w (Z · ω) q.1.1 q.1.2) P := by
  simp only [pairCovTable, Cumulants.quadCovTable, Matrix.of_apply]
  rw [← Cumulants.covariance_quad_of_cumulants Z _ _ C m κ₃ κ₄ (fun i j => symMat_symm _ i j)
    (fun i j => symMat_symm _ i j) hZ hm hc h3 h4]
  congr 1 <;> funext ω
  · exact quad_symMat (isQuadForm_pairHat w _ _) _
  · exact quad_symMat (isQuadForm_pairHat w _ _) _

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Relabelling the cohorts by `π`, with volumes invariant under `π`, relabels the pair
estimators. -/
lemma pairHat_comp_perm {w : J → T → ℝ} (π : Equiv.Perm J) (hw : ∀ j t, w (π j) t = w j t)
    (X : J × T → ℝ) (i j : J) :
    pairHat w (fun q => X (π q.1, q.2)) i j = pairHat w X (π i) (π j) := by
  simp only [pairHat, sigRhoHat, muHat, wtot, sqrtSum, hw]

end Model

/-- Two points can be carried to any two points with the same coincidence pattern. -/
lemma exists_perm_two {A : Type*} [DecidableEq A] (x x' y y' : A) (h : x = x' ↔ y = y') :
    ∃ σ : Equiv.Perm A, σ x = y ∧ σ x' = y' := by
  by_cases hx : x = x'
  · subst hx
    exact ⟨Equiv.swap x y, by simp, by simp [(h.mp rfl).symm]⟩
  · have hy : y ≠ y' := fun e => hx (h.mpr e)
    set τ := Equiv.swap x y
    have h1 : τ x' ≠ y := by
      intro e; apply hx
      have : τ x' = τ x := by rw [e]; simp [τ]
      exact (τ.injective this).symm
    refine ⟨Equiv.swap (τ x') y' * τ, ?_, by simp⟩
    simp only [Equiv.Perm.mul_apply]
    rw [show τ x = y by simp [τ]]
    exact Equiv.swap_apply_of_ne_of_ne h1.symm hy

namespace Model

variable {A B T : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T]

/-- A permutation of the rows and one of the columns, acting on the cells `(a, b)` of every
period. -/
def cellPerm (σA : Equiv.Perm A) (σB : Equiv.Perm B) : Equiv.Perm ((A × B) × T) :=
  Equiv.prodCongr (Equiv.prodCongr σA σB) (Equiv.refl T)

/-- Each of the three classes of a full table is given by its coincidence pattern. -/
lemma mem_class_iff {S : Finset ((A × B) × (A × B))}
    (hS : S = sameRowPairs Prod.fst Prod.snd ∨ S = sameColPairs Prod.fst Prod.snd
      ∨ S = crossPairs Prod.fst Prod.snd) :
    ∃ R Cc : Prop, ¬(R ∧ Cc) ∧
      ∀ p, p ∈ S ↔ (p.1.1 = p.2.1 ↔ R) ∧ (p.1.2 = p.2.2 ↔ Cc) := by
  rcases hS with rfl | rfl | rfl
  · refine ⟨True, False, by simp, fun p => ?_⟩
    simp only [sameRowPairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      iff_true, iff_false]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e => h2 (by rw [e]), h1, h2⟩
  · refine ⟨False, True, by simp, fun p => ?_⟩
    simp only [sameColPairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      iff_true, iff_false]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 (by rw [e]), h1, h2⟩
  · refine ⟨False, False, by simp, fun p => ?_⟩
    simp only [crossPairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      iff_false]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 (by rw [e]), h1, h2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Balanced table: equal weights are exactly the minimum-variance pool** (symmetry). In a
full table of rows `A` × columns `B` with the same volumes in every cell, if the moment tables of
the cells (mean, covariance, third and fourth cumulants) do not change when rows are permuted
among themselves and columns among themselves, then within each class (same row, same column,
neither) the pool with equal weights `1/|S|` has the least variance among all unbiased pools.
Why: a row-and-column permutation carries any pair of a class to any other and leaves the pair
covariance table invariant, so its rows all have the same sum, and then `1/|S|` solves the GLS
equations. Distribution-free. -/
theorem pairPool_equal_optimal_of_balanced {w : A × B → T → ℝ} (hw : ∀ i j t, w i t = w j t)
    {S : Finset ((A × B) × (A × B))}
    (hS : S = sameRowPairs Prod.fst Prod.snd ∨ S = sameColPairs Prod.fst Prod.snd
      ∨ S = crossPairs Prod.fst Prod.snd)
    (Z : (A × B) × T → Ω → ℝ) (C : Matrix ((A × B) × T) ((A × B) × T) ℝ) (m : (A × B) × T → ℝ)
    (κ₃ : (A × B) × T → (A × B) × T → (A × B) × T → ℝ)
    (κ₄ : (A × B) × T → (A × B) × T → (A × B) × T → (A × B) × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hCs : ∀ σA σB i j, C (cellPerm σA σB i) (cellPerm σA σB j) = C i j)
    (hms : ∀ σA σB i, m (cellPerm σA σB i) = m i)
    (h3s : ∀ σA σB i j k,
      κ₃ (cellPerm σA σB i) (cellPerm σA σB j) (cellPerm σA σB k) = κ₃ i j k)
    (h4s : ∀ σA σB i j k l, κ₄ (cellPerm σA σB i) (cellPerm σA σB j) (cellPerm σA σB k)
      (cellPerm σA σB l) = κ₄ i j k l)
    (b : (A × B) × (A × B) → ℝ) (hb : ∑ p ∈ S, b p = 1) :
    Var[fun ω => pairPool w S (fun _ => 1 / (S.card : ℝ)) (Z · ω); P]
      ≤ Var[fun ω => pairPool w S b (Z · ω); P] := by
  obtain ⟨V, hV⟩ : ∃ V, V = pairCovTable w S C m κ₃ κ₄ := ⟨_, rfl⟩
  have hcov : ∀ p q : S, V p q = _ := fun p q =>
    hV ▸ pairCovTable_eq_covariance w S Z C m κ₃ κ₄ hZ hm hc h3 h4 p q
  -- the relabelled cells have the same moment tables, so the same table `V`
  have hcov' : ∀ (σA : Equiv.Perm A) (σB : Equiv.Perm B) (p q : S), V p q = covariance
      (fun ω => pairHat w (fun i => Z (cellPerm σA σB i) ω) p.1.1 p.1.2)
      (fun ω => pairHat w (fun i => Z (cellPerm σA σB i) ω) q.1.1 q.1.2) P := fun σA σB =>
    hV ▸ pairCovTable_eq_covariance w S (fun i => Z (cellPerm σA σB i)) C m κ₃ κ₄
      (fun i => hZ _) (fun i => by rw [hm, hms]) (fun i j => by rw [hc, hCs])
      (fun i j k => by rw [← hms σA σB i, ← hms σA σB j, ← hms σA σB k, h3, h3s])
      (fun i j k l => by
        rw [← hms σA σB i, ← hms σA σB j, ← hms σA σB k, ← hms σA σB l, h4, h4s, hCs, hCs, hCs,
          hCs, hCs, hCs])
  obtain ⟨R, Cc, hRC, hmem⟩ := mem_class_iff hS
  -- the row-and-column permutations act on `S`
  have hact : ∀ (σA : Equiv.Perm A) (σB : Equiv.Perm B) (p : (A × B) × (A × B)),
      p ∈ S ↔ (Equiv.prodCongr (Equiv.prodCongr σA σB) (Equiv.prodCongr σA σB)) p ∈ S :=
    fun σA σB p => by
      simp only [hmem, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, σA.injective.eq_iff,
        σB.injective.eq_iff]
  let act : Equiv.Perm A → Equiv.Perm B → Equiv.Perm S := fun σA σB =>
    (Equiv.prodCongr (Equiv.prodCongr σA σB) (Equiv.prodCongr σA σB)).subtypeEquiv
      (hact σA σB)
  have hinv : ∀ (σA : Equiv.Perm A) (σB : Equiv.Perm B) (p q : S), V (act σA σB p) (act σA σB q) = V p q := fun σA σB p q => by
    rw [hcov, hcov' σA σB p q]
    simp only [act, Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
    have hw' : ∀ j t, w (Equiv.prodCongr σA σB j) t = w j t := fun j t => hw _ _ t
    congr 1 <;> funext ω
    · exact (pairHat_comp_perm (Equiv.prodCongr σA σB) hw' (Z · ω) _ _).symm
    · exact (pairHat_comp_perm (Equiv.prodCongr σA σB) hw' (Z · ω) _ _).symm
  have htrans : ∀ p q : S, ∃ σ : Equiv.Perm S, σ p = q ∧ ∀ a b, V (σ a) (σ b) = V a b := by
    intro p q
    have hp := (hmem p.1).mp p.2
    have hq := (hmem q.1).mp q.2
    obtain ⟨σA, hA1, hA2⟩ := exists_perm_two p.1.1.1 p.1.2.1 q.1.1.1 q.1.2.1
      (hp.1.trans hq.1.symm)
    obtain ⟨σB, hB1, hB2⟩ := exists_perm_two p.1.1.2 p.1.2.2 q.1.1.2 q.1.2.2
      (hp.2.trans hq.2.symm)
    refine ⟨act σA σB, ?_, hinv σA σB⟩
    apply Subtype.ext
    simp only [act, Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map, hA1, hA2, hB1, hB2]
  have hne : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; simp [h] at hb
  obtain ⟨p₀, hp₀⟩ := hne
  have hc1 := mulVec_one_eq_of_transitive V htrans ⟨p₀, hp₀⟩
  have hsymm : ∀ p q, V q p = V p q := fun p q => by rw [hcov, hcov, covariance_comm]
  have hpsd : ∀ d : S → ℝ, 0 ≤ d ⬝ᵥ (V *ᵥ d) := fun d => by
    rw [hV]
    show 0 ≤ d ⬝ᵥ (Cumulants.quadCovTable _ C m κ₃ κ₄ *ᵥ d)
    rw [← Cumulants.variance_sum_quad Z (fun p : S => symMat fun X => pairHat w X p.1.1 p.1.2)
      C m κ₃ κ₄ (fun p i j => symMat_symm _ i j) hZ hm hc h3 h4 d]
    exact variance_nonneg _ _
  have key := equalWeight_optimal V hsymm hpsd hc1 (fun p : S => b p.1)
    (by rw [Finset.sum_coe_sort S b]; exact hb)
  rw [variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4,
    variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4, ← hV]
  simpa [Fintype.card_coe, one_div] using key

end Model

end Credibility
