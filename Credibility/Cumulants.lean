import Mathlib

/-!
# Cumulant layer: variance of a quadratic estimator

The second-moment core gives the expectation of any quadratic estimator
(`Expectation.integral_quad_of_mean`). Its variance needs moments up to order four. Here they
enter as given tables, as the covariance table `C` does elsewhere: the third cumulant `κ₃`
(the third central moment) and the fourth cumulant `κ₄` (the fourth central moment minus its
three Gaussian pairings). Nothing is assumed about the distribution: the tables are *defined*
by the moments, and `κ₃ = κ₄ = 0` is the Gaussian case.

* `varQuad A C m κ₃ κ₄ = 2 tr(ACAC) + 4 (Am)ᵀC(Am) + 4 Σ Aᵢⱼ (Am)ₖ κ₃ᵢⱼₖ + Σ Aᵢⱼ Aₖₗ κ₄ᵢⱼₖₗ`;
* `variance_quad_of_cumulants`: it is the actual variance of `xᵀAx` for any random cells in
  `L⁴` with these moments (`A` symmetric).

Plan and literature: `notes/fourth-moments.md` (Atiqullah 1962; Seber & Lee 2003, Thm 1.6).
Cells are indexed by any finite type `ι`; the models use `ι = J × T`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Credibility.Cumulants

variable {ι : Type*} [Fintype ι]

/-- The variance of `xᵀAx` from the mean `m`, covariance `C`, third cumulants `κ₃` and fourth
cumulants `κ₄` of the cells: `2 tr(ACAC) + 4 (Am)ᵀC(Am) + 4 Σ Aᵢⱼ (Am)ₖ κ₃ᵢⱼₖ + Σ Aᵢⱼ Aₖₗ κ₄ᵢⱼₖₗ`.
The first two terms are the Gaussian variance; the others vanish for Gaussian cells. -/
noncomputable def varQuad (A C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (κ₄ : ι → ι → ι → ι → ℝ) : ℝ :=
  2 * trace (A * C * A * C) + 4 * (A *ᵥ m) ⬝ᵥ (C *ᵥ (A *ᵥ m))
    + 4 * ∑ i, ∑ j, ∑ k, A i j * (A *ᵥ m) k * κ₃ i j k
    + ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * κ₄ i j k l

/-- `4|abcd| ≤ a⁴ + b⁴ + c⁴ + d⁴` (AM–GM). -/
lemma abs_mul4_le (a b c d : ℝ) : |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h2 : |c| * |d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
  have h3 : (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
    nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2), sq_nonneg (a ^ 2 - b ^ 2),
      sq_nonneg (c ^ 2 - d ^ 2)]
  calc |a| * |b| * |c| * |d| = (|a| * |b|) * (|c| * |d|) := by ring
    _ ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ _ := h3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
lemma integrable_pow4 {u : Ω → ℝ} (hu : MemLp u 4 P) : Integrable (fun ω => u ω ^ 4) P := by
  have hu' : MemLp u ((4 : ℕ) : ENNReal) P := by exact_mod_cast hu
  simpa [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩] using hu'.integrable_norm_pow (by norm_num)

omit [Fintype ι] in
/-- A product of four `L⁴` functions is integrable. -/
lemma integrable_mul4 {f g h k : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) (hh : MemLp h 4 P)
    (hk : MemLp k 4 P) : Integrable (fun ω => f ω * g ω * h ω * k ω) P := by
  refine Integrable.mono' ((((integrable_pow4 hf).add (integrable_pow4 hg)).add
    ((integrable_pow4 hh).add (integrable_pow4 hk))).div_const 4) ?_ ?_
  · exact ((hf.aestronglyMeasurable.mul hg.aestronglyMeasurable).mul
      hh.aestronglyMeasurable).mul hk.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith [abs_mul4_le (f ω) (g ω) (h ω) (k ω)]

omit [Fintype ι] in
lemma integrable_mul3 [IsFiniteMeasure P] {f g h : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P)
    (hh : MemLp h 4 P) : Integrable (fun ω => f ω * g ω * h ω) P := by
  simpa using integrable_mul4 hf hg hh (memLp_const 1)

omit [Fintype ι] in
lemma integrable_mul2 [IsFiniteMeasure P] {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    Integrable (fun ω => f ω * g ω) P := by
  simpa using integrable_mul3 hf hg (memLp_const 1)

omit [Fintype ι] [MeasurableSpace Ω] in
lemma sum_mul_sum_eq {α β : Type*} (s : Finset α) (t : Finset β) (a : α → ℝ) (b : β → ℝ)
    (g : α → Ω → ℝ) (h : β → Ω → ℝ) (ω : Ω) :
    (∑ p ∈ s, a p * g p ω) * (∑ q ∈ t, b q * h q ω)
      = ∑ p ∈ s, ∑ q ∈ t, a p * b q * (g p ω * h q ω) := by
  rw [sum_mul_sum]; exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

omit [Fintype ι] in
/-- A product of two finite linear combinations is integrable. -/
lemma integrable_sum_mul_sum {α β : Type*} (s : Finset α) (t : Finset β) (a : α → ℝ)
    (b : β → ℝ) (g : α → Ω → ℝ) (h : β → Ω → ℝ)
    (hgh : ∀ p q, Integrable (fun ω => g p ω * h q ω) P) :
    Integrable (fun ω => (∑ p ∈ s, a p * g p ω) * (∑ q ∈ t, b q * h q ω)) P := by
  simp_rw [sum_mul_sum_eq]
  exact integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => (hgh p q).const_mul _

omit [Fintype ι] in
/-- The integral of a product of two finite linear combinations. -/
lemma integral_sum_mul_sum {α β : Type*} (s : Finset α) (t : Finset β) (a : α → ℝ) (b : β → ℝ)
    (g : α → Ω → ℝ) (h : β → Ω → ℝ) (hgh : ∀ p q, Integrable (fun ω => g p ω * h q ω) P) :
    ∫ ω, (∑ p ∈ s, a p * g p ω) * (∑ q ∈ t, b q * h q ω) ∂P
      = ∑ p ∈ s, ∑ q ∈ t, a p * b q * ∫ ω, g p ω * h q ω ∂P := by
  simp_rw [sum_mul_sum_eq]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => (hgh p q).const_mul _]
  refine sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hgh p q).const_mul _]
  exact sum_congr rfl fun q _ => integral_const_mul _ _

variable [IsProbabilityMeasure P]

/-- **Variance of a quadratic estimator** from moments up to order four. For random cells
`Zᵢ` in `L⁴` with means `mᵢ`, covariances `C`, third central moments `κ₃` and fourth central
moments `κ₄ᵢⱼₖₗ + CᵢⱼCₖₗ + CᵢₖCⱼₗ + CᵢₗCⱼₖ` (so `κ₄` is the fourth cumulant), and a symmetric `A`,
`Var(Σᵢⱼ Aᵢⱼ Zᵢ Zⱼ) = varQuad A C m κ₃ κ₄`. No distribution and no independence is assumed. -/
theorem variance_quad_of_cumulants (Z : ι → Ω → ℝ) (A C : Matrix ι ι ℝ) (m : ι → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ) (hA : ∀ i j, A j i = A i j)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) :
    variance (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω) P = varQuad A C m κ₃ κ₄ := by
  obtain ⟨e, he⟩ : ∃ e : ι → Ω → ℝ, e = fun i ω => Z i ω - m i := ⟨_, rfl⟩
  have hZe : ∀ i ω, Z i ω = e i ω + m i := fun i ω => by simp [he]
  have hL : ∀ i, MemLp (e i) 4 P := fun i => by subst he; exact (hZ i).sub (memLp_const _)
  have e1 : ∀ i, ∫ ω, e i ω ∂P = 0 := fun i => by
    subst he
    rw [integral_sub ((hZ i).integrable (by norm_num)) (integrable_const _), hm, integral_const]
    simp
  have e2 : ∀ i j, ∫ ω, e i ω * e j ω ∂P = C i j := fun i j => by
    subst he; rw [← hc]; simp only [covariance, hm]
  have e3 : ∀ i j k, ∫ ω, e i ω * e j ω * e k ω ∂P = κ₃ i j k := by subst he; exact h3
  have e4 : ∀ i j k l, ∫ ω, e i ω * e j ω * e k ω * e l ω ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k := by subst he; exact h4
  have hCs : ∀ i j, C j i = C i j := fun i j => by rw [← hc, ← hc, covariance_comm]
  -- integrability of the products of centred cells
  have i1 : ∀ i, Integrable (e i) P := fun i => (hL i).integrable (by norm_num)
  have i2 : ∀ i j, Integrable (fun ω => e i ω * e j ω) P := fun i j => integrable_mul2 (hL i) (hL j)
  have i3 : ∀ i j k, Integrable (fun ω => e i ω * e j ω * e k ω) P := fun i j k =>
    integrable_mul3 (hL i) (hL j) (hL k)
  have i4 : ∀ i j k l, Integrable (fun ω => e i ω * e j ω * e k ω * e l ω) P := fun i j k l =>
    integrable_mul4 (hL i) (hL j) (hL k) (hL l)
  -- `X − EX = U + V`: a centred quadratic part and a linear part
  let g : ι × ι → Ω → ℝ := fun p ω => e p.1 ω * e p.2 ω - C p.1 p.2
  let b : ι → ℝ := fun k => 2 * (A *ᵥ m) k
  let U : Ω → ℝ := fun ω => ∑ p : ι × ι, A p.1 p.2 * g p ω
  let V : Ω → ℝ := fun ω => ∑ k, b k * e k ω
  have gg : ∀ p q, Integrable (fun ω => g p ω * g q ω) P := fun p q => by
    have : (fun ω => g p ω * g q ω) = fun ω => e p.1 ω * e p.2 ω * e q.1 ω * e q.2 ω
        - C q.1 q.2 * (e p.1 ω * e p.2 ω) - C p.1 p.2 * (e q.1 ω * e q.2 ω)
        + C p.1 p.2 * C q.1 q.2 := by funext ω; simp only [g]; ring
    rw [this]
    exact (((i4 _ _ _ _).sub ((i2 _ _).const_mul _)).sub ((i2 _ _).const_mul _)).add
      (integrable_const _)
  have ge : ∀ p k, Integrable (fun ω => g p ω * e k ω) P := fun p k => by
    have : (fun ω => g p ω * e k ω) = fun ω => e p.1 ω * e p.2 ω * e k ω
        - C p.1 p.2 * e k ω := by funext ω; simp only [g]; ring
    rw [this]; exact (i3 _ _ _).sub ((i1 _).const_mul _)
  have Egg : ∀ p q, ∫ ω, g p ω * g q ω ∂P
      = κ₄ p.1 p.2 q.1 q.2 + C p.1 q.1 * C p.2 q.2 + C p.1 q.2 * C p.2 q.1 := fun p q => by
    have : (fun ω => g p ω * g q ω) = fun ω => e p.1 ω * e p.2 ω * e q.1 ω * e q.2 ω
        - C q.1 q.2 * (e p.1 ω * e p.2 ω) - C p.1 p.2 * (e q.1 ω * e q.2 ω)
        + C p.1 p.2 * C q.1 q.2 := by funext ω; simp only [g]; ring
    rw [this, integral_add _ (integrable_const _), integral_sub, integral_sub, integral_const_mul,
      integral_const_mul, e4, e2, e2, integral_const]
    · simp; ring
    · exact (i4 _ _ _ _)
    · exact (i2 _ _).const_mul _
    · exact (i4 _ _ _ _).sub ((i2 _ _).const_mul _)
    · exact (i2 _ _).const_mul _
    · exact ((i4 _ _ _ _).sub ((i2 _ _).const_mul _)).sub ((i2 _ _).const_mul _)
  have Ege : ∀ p k, ∫ ω, g p ω * e k ω ∂P = κ₃ p.1 p.2 k := fun p k => by
    have : (fun ω => g p ω * e k ω) = fun ω => e p.1 ω * e p.2 ω * e k ω
        - C p.1 p.2 * e k ω := by funext ω; simp only [g]; ring
    rw [this, integral_sub (i3 _ _ _) ((i1 _).const_mul _), integral_const_mul, e3, e1]
    ring
  have key : (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω)
      = fun ω => (U ω + V ω) + ∑ i, ∑ j, A i j * (C i j + m i * m j) := by
    funext ω
    have hV : V ω = ∑ i, ∑ j, (A i j * m j * e i ω + A i j * m i * e j ω) := by
      simp only [V, b, sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => A i j * m i * e j ω)]
      simp only [mulVec, dotProduct]
      rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib]; simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [hA i j]; ring
    rw [hV]; simp only [U, g, hZe, Fintype.sum_prod_type, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have ig : ∀ p, Integrable (g p) P := fun p => (i2 _ _).sub (integrable_const _)
  have iU : Integrable U P := integrable_finsetSum _ fun p _ => (ig p).const_mul _
  have iV : Integrable V P := integrable_finsetSum _ fun k _ => (i1 k).const_mul _
  have EU : ∫ ω, U ω ∂P = 0 := by
    simp only [U]
    rw [integral_finsetSum _ fun p _ => (ig p).const_mul _]
    refine sum_eq_zero fun p _ => ?_
    rw [integral_const_mul, integral_sub (i2 _ _) (integrable_const _), e2, integral_const]
    simp
  have EV : ∫ ω, V ω ∂P = 0 := by
    simp only [V]
    rw [integral_finsetSum _ fun k _ => (i1 k).const_mul _]
    exact sum_eq_zero fun k _ => by rw [integral_const_mul, e1, mul_zero]
  have iUU := integrable_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2)
    (fun p : ι × ι => A p.1 p.2) g g gg
  have iUV := integrable_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2) b g e ge
  have iVV := integrable_sum_mul_sum (P := P) univ univ b b e e i2
  have EUU := integral_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2)
    (fun p : ι × ι => A p.1 p.2) g g gg
  have EUV := integral_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2) b g e ge
  have EVV := integral_sum_mul_sum (P := P) univ univ b b e e i2
  have sq : (fun ω => (U ω + V ω) ^ 2) = fun ω => (U ω * U ω + 2 * (U ω * V ω)) + V ω * V ω := by
    funext ω; ring
  have hvar : variance (fun ω => U ω + V ω) P = ∫ ω, (U ω + V ω) ^ 2 ∂P :=
    variance_of_integral_eq_zero (iU.add iV).aemeasurable (by
      change ∫ ω, U ω + V ω ∂P = 0
      rw [integral_add iU iV, EU, EV]; simp)
  rw [key, variance_add_const (X := fun ω => U ω + V ω) (iU.add iV).aestronglyMeasurable, hvar,
    sq]
  simp only [U, V]
  rw [integral_add, integral_add, integral_const_mul, EUU, EUV, EVV]
  rotate_left
  · exact iUU
  · exact iUV.const_mul 2
  · exact iUU.add (iUV.const_mul 2)
  · exact iVV
  simp only [Egg, Ege, e2, Fintype.sum_prod_type, b, mul_add, sum_add_distrib]
  have tr : trace (A * C * A * C) = ∑ i, ∑ j, ∑ k, ∑ l, A i j * C j k * A k l * C l i := by
    simp only [trace, Matrix.diag, Matrix.mul_apply, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    calc _ = ∑ l, ∑ j, ∑ k, A i j * C j k * A k l * C l i :=
          sum_congr rfl fun l _ => sum_comm
      _ = ∑ j, ∑ l, ∑ k, A i j * C j k * A k l * C l i := sum_comm
      _ = _ := sum_congr rfl fun j _ => sum_comm
  have t1 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (C i l * C j k) = trace (A * C * A * C) := by
    rw [tr]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
      sum_congr rfl fun l _ => by rw [hCs i l]; ring
  have t2 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (C i k * C j l) = trace (A * C * A * C) := by
    rw [tr]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by rw [hA l k, hCs i l]; ring
  have t3 : ∑ k, ∑ l, 2 * (A *ᵥ m) k * (2 * (A *ᵥ m) l) * C k l
      = 4 * (A *ᵥ m) ⬝ᵥ (C *ᵥ (A *ᵥ m)) := by
    generalize A *ᵥ m = w
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  have t4 : 2 * ∑ i, ∑ j, ∑ k, A i j * (2 * (A *ᵥ m) k) * κ₃ i j k
      = 4 * ∑ i, ∑ j, ∑ k, A i j * (A *ᵥ m) k * κ₃ i j k := by
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [varQuad, t1, t2, t3, t4]
  ring

end Credibility.Cumulants
