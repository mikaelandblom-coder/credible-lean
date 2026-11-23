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

section ThirdMoments

/-! ### Third moments

The expectation of a cubic form needs the third cumulant (for `κ̂ⱼ` in the app's noise
diagnostics), and so does the covariance of a quadratic and a linear estimator (the bias
`Σᵢ cov(d̂ᵢ, μ̂ᵢ)` of Finding 35 when the weights are quadratic). Both need only `L³` cells. -/

omit [Fintype ι] in
/-- `3|abc| ≤ |a|³ + |b|³ + |c|³` (AM–GM). -/
lemma abs_mul3_le (a b c : ℝ) : |a * b * c| ≤ (|a| ^ 3 + |b| ^ 3 + |c| ^ 3) / 3 := by
  rw [abs_mul, abs_mul]
  have ha := abs_nonneg a; have hb := abs_nonneg b; have hc := abs_nonneg c
  nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
    (add_nonneg (add_nonneg (sq_nonneg (|a| - |b|)) (sq_nonneg (|b| - |c|)))
      (sq_nonneg (|c| - |a|)))]

omit [Fintype ι] [IsProbabilityMeasure P] in
lemma integrable_abs_pow3 {u : Ω → ℝ} (hu : MemLp u 3 P) :
    Integrable (fun ω => |u ω| ^ 3) P := by
  have hu' : MemLp u ((3 : ℕ) : ENNReal) P := by exact_mod_cast hu
  simpa [Real.norm_eq_abs] using hu'.integrable_norm_pow (by norm_num)

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- A product of three `L³` functions is integrable. -/
lemma integrable_mul3_of_L3 {f g h : Ω → ℝ} (hf : MemLp f 3 P) (hg : MemLp g 3 P)
    (hh : MemLp h 3 P) : Integrable (fun ω => f ω * g ω * h ω) P := by
  refine Integrable.mono' ((((integrable_abs_pow3 hf).add (integrable_abs_pow3 hg)).add
    (integrable_abs_pow3 hh)).div_const 3) ?_ ?_
  · exact (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable).mul hh.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith [abs_mul3_le (f ω) (g ω) (h ω)]

omit [Fintype ι] in
lemma integrable_mul2_of_L3 {f g : Ω → ℝ} (hf : MemLp f 3 P)
    (hg : MemLp g 3 P) : Integrable (fun ω => f ω * g ω) P := by
  simpa using integrable_mul3_of_L3 hf hg (memLp_const 1)

/-- The expectation of the cubic form `Σ Tᵢⱼₖ ZᵢZⱼZₖ` from the mean `m`, covariance `C` and third
cumulants `κ₃`: `Σ Tᵢⱼₖ (κ₃ᵢⱼₖ + mᵢCⱼₖ + mⱼCᵢₖ + mₖCᵢⱼ + mᵢmⱼmₖ)`. -/
def eCubic (T : ι → ι → ι → ℝ) (C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k
    * (κ₃ i j k + m i * C j k + m j * C i k + m k * C i j + m i * m j * m k)

/-- **Expectation of a cubic estimator.** For random cells in `L³` with means `m`, covariances `C`
and third central moments `κ₃`, `E[Σ Tᵢⱼₖ ZᵢZⱼZₖ] = eCubic T C m κ₃`. No distribution is assumed. -/
theorem integral_cubic_of_cumulants (Z : ι → Ω → ℝ)
    (T : ι → ι → ι → ℝ) (C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (hZ : ∀ i, MemLp (Z i) 3 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k) :
    ∫ ω, ∑ i, ∑ j, ∑ k, T i j k * Z i ω * Z j ω * Z k ω ∂P = eCubic T C m κ₃ := by
  obtain ⟨e, he⟩ : ∃ e : ι → Ω → ℝ, e = fun i ω => Z i ω - m i := ⟨_, rfl⟩
  have hZe : ∀ i ω, Z i ω = e i ω + m i := fun i ω => by simp [he]
  have hL : ∀ i, MemLp (e i) 3 P := fun i => by subst he; exact (hZ i).sub (memLp_const _)
  have e1 : ∀ i, ∫ ω, e i ω ∂P = 0 := fun i => by
    subst he
    rw [integral_sub ((hZ i).integrable (by norm_num)) (integrable_const _), hm, integral_const]
    simp
  have e2 : ∀ i j, ∫ ω, e i ω * e j ω ∂P = C i j := fun i j => by
    subst he; rw [← hc]; simp only [covariance, hm]
  have e3 : ∀ i j k, ∫ ω, e i ω * e j ω * e k ω ∂P = κ₃ i j k := by subst he; exact h3
  have i1 : ∀ i, Integrable (e i) P := fun i => (hL i).integrable (by norm_num)
  have i2 : ∀ i j, Integrable (fun ω => e i ω * e j ω) P := fun i j =>
    integrable_mul2_of_L3 (hL i) (hL j)
  have i3 : ∀ i j k, Integrable (fun ω => e i ω * e j ω * e k ω) P := fun i j k =>
    integrable_mul3_of_L3 (hL i) (hL j) (hL k)
  have term : ∀ i j k, ∫ ω, T i j k * Z i ω * Z j ω * Z k ω ∂P
      = T i j k * (κ₃ i j k + m i * C j k + m j * C i k + m k * C i j + m i * m j * m k) := by
    intro i j k
    have : (fun ω => T i j k * Z i ω * Z j ω * Z k ω) = fun ω => T i j k *
        (e i ω * e j ω * e k ω + m i * (e j ω * e k ω) + m j * (e i ω * e k ω)
          + m k * (e i ω * e j ω) + m i * m j * e k ω + m i * m k * e j ω + m j * m k * e i ω
          + m i * m j * m k) := by
      funext ω; simp only [hZe]; ring
    rw [this, integral_const_mul, integral_add, integral_add, integral_add, integral_add,
      integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, e3, e2, e2,
      e2, e1, e1, e1, integral_const]
    · simp
    all_goals repeat' first
      | with_reducible exact i3 _ _ _ | with_reducible exact i2 _ _
      | with_reducible exact i1 _ | with_reducible exact integrable_const _
      | with_reducible apply Integrable.fun_add | with_reducible apply Integrable.const_mul
  have iT : ∀ i j k, Integrable (fun ω => T i j k * Z i ω * Z j ω * Z k ω) P := fun i j k =>
    integrable_mul3_of_L3 ((hZ i).const_mul _) (hZ j) (hZ k)
  simp only [eCubic]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => iT i j k]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => iT i j k]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => iT i j k]
  exact sum_congr rfl fun k _ => term i j k

/-- The covariance of `xᵀAx` and `bᵀx` from the mean `m`, covariance `C` and third cumulants:
`2 (Am)ᵀCb + Σ Aᵢⱼ bₖ κ₃ᵢⱼₖ`. The second term vanishes for symmetric cells. -/
noncomputable def covQuadLin (A C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (b : ι → ℝ) : ℝ :=
  2 * (A *ᵥ m) ⬝ᵥ (C *ᵥ b) + ∑ i, ∑ j, ∑ k, A i j * b k * κ₃ i j k

/-- **Covariance of a quadratic and a linear estimator.** For random cells in `L³` with means
`m`, covariances `C`, third central moments `κ₃` and a symmetric `A`,
`cov(Σ Aᵢⱼ ZᵢZⱼ, Σ bₖZₖ) = covQuadLin A C m κ₃ b`. No distribution is assumed. -/
theorem covariance_quad_lin_of_cumulants (Z : ι → Ω → ℝ) (A C : Matrix ι ι ℝ) (m : ι → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (b : ι → ℝ) (hA : ∀ i j, A j i = A i j)
    (hZ : ∀ i, MemLp (Z i) 3 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k) :
    covariance (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω) (fun ω => ∑ k, b k * Z k ω) P
      = covQuadLin A C m κ₃ b := by
  obtain ⟨e, he⟩ : ∃ e : ι → Ω → ℝ, e = fun i ω => Z i ω - m i := ⟨_, rfl⟩
  have hZe : ∀ i ω, Z i ω = e i ω + m i := fun i ω => by simp [he]
  have hL : ∀ i, MemLp (e i) 3 P := fun i => by subst he; exact (hZ i).sub (memLp_const _)
  have e1 : ∀ i, ∫ ω, e i ω ∂P = 0 := fun i => by
    subst he
    rw [integral_sub ((hZ i).integrable (by norm_num)) (integrable_const _), hm, integral_const]
    simp
  have e2 : ∀ i j, ∫ ω, e i ω * e j ω ∂P = C i j := fun i j => by
    subst he; rw [← hc]; simp only [covariance, hm]
  have e3 : ∀ i j k, ∫ ω, e i ω * e j ω * e k ω ∂P = κ₃ i j k := by subst he; exact h3
  have i1 : ∀ i, Integrable (e i) P := fun i => (hL i).integrable (by norm_num)
  have i2 : ∀ i j, Integrable (fun ω => e i ω * e j ω) P := fun i j =>
    integrable_mul2_of_L3 (hL i) (hL j)
  have i3 : ∀ i j k, Integrable (fun ω => e i ω * e j ω * e k ω) P := fun i j k =>
    integrable_mul3_of_L3 (hL i) (hL j) (hL k)
  let g : ι × ι → Ω → ℝ := fun p ω => e p.1 ω * e p.2 ω - C p.1 p.2
  let a : ι → ℝ := fun k => 2 * (A *ᵥ m) k
  let U : Ω → ℝ := fun ω => ∑ p : ι × ι, A p.1 p.2 * g p ω
  let V : Ω → ℝ := fun ω => ∑ k, a k * e k ω
  let W : Ω → ℝ := fun ω => ∑ k, b k * e k ω
  have ge : ∀ p k, Integrable (fun ω => g p ω * e k ω) P := fun p k => by
    have : (fun ω => g p ω * e k ω) = fun ω => e p.1 ω * e p.2 ω * e k ω
        - C p.1 p.2 * e k ω := by funext ω; simp only [g]; ring
    rw [this]; exact (i3 _ _ _).sub ((i1 _).const_mul _)
  have Ege : ∀ p k, ∫ ω, g p ω * e k ω ∂P = κ₃ p.1 p.2 k := fun p k => by
    have : (fun ω => g p ω * e k ω) = fun ω => e p.1 ω * e p.2 ω * e k ω
        - C p.1 p.2 * e k ω := by funext ω; simp only [g]; ring
    rw [this, integral_sub (i3 _ _ _) ((i1 _).const_mul _), integral_const_mul, e3, e1]
    ring
  have key : (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω)
      = fun ω => (U ω + V ω) + ∑ i, ∑ j, A i j * (C i j + m i * m j) := by
    funext ω
    have hV : V ω = ∑ i, ∑ j, (A i j * m j * e i ω + A i j * m i * e j ω) := by
      simp only [V, a, sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => A i j * m i * e j ω)]
      simp only [mulVec, dotProduct]
      rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib]; simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [hA i j]; ring
    rw [hV]; simp only [U, g, hZe, Fintype.sum_prod_type, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have keyW : (fun ω => ∑ k, b k * Z k ω) = fun ω => W ω + ∑ k, b k * m k := by
    funext ω; simp only [W, hZe, mul_add, sum_add_distrib]
  have ig : ∀ p, Integrable (g p) P := fun p => (i2 _ _).sub (integrable_const _)
  have iU : Integrable U P := integrable_finsetSum _ fun p _ => (ig p).const_mul _
  have iV : Integrable V P := integrable_finsetSum _ fun k _ => (i1 k).const_mul _
  have iW : Integrable W P := integrable_finsetSum _ fun k _ => (i1 k).const_mul _
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
  have EW : ∫ ω, W ω ∂P = 0 := by
    simp only [W]
    rw [integral_finsetSum _ fun k _ => (i1 k).const_mul _]
    exact sum_eq_zero fun k _ => by rw [integral_const_mul, e1, mul_zero]
  have iUW := integrable_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2) b g e ge
  have iVW := integrable_sum_mul_sum (P := P) univ univ a b e e i2
  have EUW := integral_sum_mul_sum (P := P) univ univ (fun p : ι × ι => A p.1 p.2) b g e ge
  have EVW := integral_sum_mul_sum (P := P) univ univ a b e e i2
  have hcov : covariance (fun ω => (U ω + V ω) + ∑ i, ∑ j, A i j * (C i j + m i * m j))
      (fun ω => W ω + ∑ k, b k * m k) P = ∫ ω, U ω * W ω + V ω * W ω ∂P := by
    rw [covariance_add_const_left (X := fun ω => U ω + V ω) (iU.add iV),
      covariance_add_const_right (Y := W) iW]
    simp only [covariance]
    have : ∫ ω, U ω + V ω ∂P = 0 := by rw [integral_add iU iV, EU, EV, add_zero]
    rw [this, EW]
    simp only [sub_zero, add_mul]
  rw [key, keyW, hcov]
  simp only [U, V, W]
  rw [integral_add, EUW, EVW]
  rotate_left
  · exact iUW
  · exact iVW
  simp only [Ege, e2, Fintype.sum_prod_type, a, covQuadLin, dotProduct, mulVec, mul_sum]
  rw [add_comm]; congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [← mul_sum]; ring

end ThirdMoments

section Sources

omit [Fintype ι]

/-- Move the last of four sums to the front. -/
lemma sum_comm_last3 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := sum_congr rfl fun a _ => sum_comm
    _ = _ := sum_comm

/-- Move the last of five sums to the front. -/
lemma sum_comm_last4 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (f : α → β → γ → δ → ε → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d e := by
  calc _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, f a b c d e :=
        sum_congr rfl fun a _ => sum_comm_last3 _
    _ = _ := sum_comm

variable [Fintype ι] {S : Type*} [Fintype S]

omit [Fintype S] in
lemma diag_transpose_mul_mul (A : Matrix ι ι ℝ) (B : Matrix ι S ℝ) (s : S) :
    (Bᵀ * A * B) s s = ∑ i, ∑ j, B i s * A i j * B j s := by
  simp only [Matrix.mul_apply, transpose_apply, sum_mul]
  exact sum_comm

/-- **Independent sources.** If the cells are `m + Bξ` for independent sources `ξₛ` with third
cumulants `c₃ₛ` and fourth cumulants `c₄ₛ`, the cumulant tables of the cells are
`κ₃ᵢⱼₖ = Σₛ c₃ₛ BᵢₛBⱼₛBₖₛ` and `κ₄ᵢⱼₖₗ = Σₛ c₄ₛ BᵢₛBⱼₛBₖₛBₗₛ`. Then the non-Gaussian part of the
variance needs one number of each order per source:
`varQuad = 2 tr(ACAC) + 4 (Am)ᵀC(Am) + 4 Σₛ c₃ₛ Mₛₛ aₛ + Σₛ c₄ₛ Mₛₛ²`, `M = BᵀAB`, `a = BᵀAm`. -/
theorem varQuad_sources (A C : Matrix ι ι ℝ) (m : ι → ℝ) (B : Matrix ι S ℝ) (c₃ c₄ : S → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (h₃ : ∀ i j k, κ₃ i j k = ∑ s, c₃ s * B i s * B j s * B k s)
    (h₄ : ∀ i j k l, κ₄ i j k l = ∑ s, c₄ s * B i s * B j s * B k s * B l s) :
    varQuad A C m κ₃ κ₄ = 2 * trace (A * C * A * C) + 4 * (A *ᵥ m) ⬝ᵥ (C *ᵥ (A *ᵥ m))
      + 4 * ∑ s, c₃ s * (Bᵀ * A * B) s s * (Bᵀ *ᵥ (A *ᵥ m)) s
      + ∑ s, c₄ s * (Bᵀ * A * B) s s ^ 2 := by
  have t3 : ∑ i, ∑ j, ∑ k, A i j * (A *ᵥ m) k * κ₃ i j k
      = ∑ s, c₃ s * (Bᵀ * A * B) s s * (Bᵀ *ᵥ (A *ᵥ m)) s := by
    generalize A *ᵥ m = w
    simp only [h₃, mul_sum]
    rw [sum_comm_last3]
    refine sum_congr rfl fun s _ => ?_
    rw [diag_transpose_mul_mul]
    simp only [mulVec, dotProduct, transpose_apply]
    rw [mul_assoc]
    simp only [sum_mul]
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  have t4 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * κ₄ i j k l
      = ∑ s, c₄ s * (Bᵀ * A * B) s s ^ 2 := by
    simp only [h₄, mul_sum]
    rw [sum_comm_last4]
    refine sum_congr rfl fun s _ => ?_
    rw [diag_transpose_mul_mul, sq]
    simp only [mul_sum, sum_mul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
      sum_congr rfl fun l _ => by ring
  rw [varQuad, t3, t4]

end Sources

section IndependentSources

/-! ### Independent sources give the source form of the tables -/

variable {S : Type*} [DecidableEq S]

omit [IsProbabilityMeasure P] in
/-- A source that appears once makes a product of four centred independent sources vanish. -/
lemma integral_mul4_indep_of_ne (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) {s t u w : S} (ht : s ≠ t) (hu : s ≠ u) (hw : s ≠ w) :
    ∫ ω, ξ s ω * ξ t ω * ξ u ω * ξ w ω ∂P = 0 := by
  have hd : Disjoint ({s} : Finset S) {t, u, w} := by simp [ht, hu, hw]
  have hφ : Measurable fun x : ((i : ({s} : Finset S)) → ℝ) => x ⟨s, mem_singleton_self s⟩ :=
    measurable_pi_apply _
  have hψ : Measurable fun x : ((i : ({t, u, w} : Finset S)) → ℝ) =>
      x ⟨t, by simp⟩ * x ⟨u, by simp⟩ * x ⟨w, by simp⟩ := by fun_prop
  have h := (hind.indepFun_finset {s} {t, u, w} hd hmeas).comp hφ hψ
  have := h.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  simp only [Function.comp] at this
  have e : (fun ω => ξ s ω * ξ t ω * ξ u ω * ξ w ω)
      = fun ω => ξ s ω * (ξ t ω * ξ u ω * ξ w ω) := by funext ω; ring
  rw [e, this]
  simp [h0 s]

omit [IsProbabilityMeasure P] in
/-- The same for three sources. -/
lemma integral_mul3_indep_of_ne (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) {s t u : S} (ht : s ≠ t) (hu : s ≠ u) :
    ∫ ω, ξ s ω * ξ t ω * ξ u ω ∂P = 0 := by
  have hd : Disjoint ({s} : Finset S) {t, u} := by simp [ht, hu]
  have hφ : Measurable fun x : ((i : ({s} : Finset S)) → ℝ) => x ⟨s, mem_singleton_self s⟩ :=
    measurable_pi_apply _
  have hψ : Measurable fun x : ((i : ({t, u} : Finset S)) → ℝ) =>
      x ⟨t, by simp⟩ * x ⟨u, by simp⟩ := by fun_prop
  have h := (hind.indepFun_finset {s} {t, u} hd hmeas).comp hφ hψ
  have := h.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  simp only [Function.comp] at this
  have e : (fun ω => ξ s ω * ξ t ω * ξ u ω) = fun ω => ξ s ω * (ξ t ω * ξ u ω) := by
    funext ω; ring
  rw [e, this]
  simp [h0 s]

omit [IsProbabilityMeasure P] [DecidableEq S] in
/-- Independent centred sources are uncorrelated. -/
lemma integral_mul2_indep_of_ne (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) {s t : S} (ht : s ≠ t) :
    ∫ ω, ξ s ω * ξ t ω ∂P = 0 := by
  rw [(hind.indepFun ht).integral_fun_mul_eq_mul_integral (hmeas s).aestronglyMeasurable
    (hmeas t).aestronglyMeasurable]
  simp [h0 s]

omit [IsProbabilityMeasure P] [DecidableEq S] in
/-- Two pairs of different independent sources. -/
lemma integral_mul4_indep_pair (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    {s u : S} (hu : s ≠ u) :
    ∫ ω, ξ s ω * ξ s ω * ξ u ω * ξ u ω ∂P
      = (∫ ω, ξ s ω * ξ s ω ∂P) * ∫ ω, ξ u ω * ξ u ω ∂P := by
  have hm : Measurable fun x : ℝ => x * x := by fun_prop
  have h := (hind.indepFun hu).comp hm hm
  have := h.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  simp only [Function.comp] at this
  have e : (fun ω => ξ s ω * ξ s ω * ξ u ω * ξ u ω)
      = fun ω => ξ s ω * ξ s ω * (ξ u ω * ξ u ω) := by funext ω; ring
  rw [e, this]

omit [IsProbabilityMeasure P] in
/-- The fourth moments of independent centred sources. -/
lemma integral_mul4_indep (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) (v c₄ : S → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = c₄ s + 3 * v s ^ 2) (s t u w : S) :
    ∫ ω, ξ s ω * ξ t ω * ξ u ω * ξ w ω ∂P
      = (if s = t ∧ t = u ∧ u = w then c₄ s else 0) + (if s = t ∧ u = w then v s * v u else 0)
        + (if s = u ∧ t = w then v s * v t else 0) + (if s = w ∧ t = u then v s * v t else 0) := by
  have L : ∀ {s t u w : S}, s ≠ t → s ≠ u → s ≠ w →
      ∫ ω, ξ s ω * ξ t ω * ξ u ω * ξ w ω ∂P = 0 := fun h1 h2 h3 => integral_mul4_indep_of_ne ξ hind hmeas h0 h1 h2 h3
  by_cases hst : s = t
  · subst hst
    by_cases hsu : s = u
    · subst hsu
      by_cases hsw : s = w
      · subst hsw; rw [h4]; simp; ring
      · have := L (s := w) (t := s) (u := s) (w := s) (Ne.symm hsw) (Ne.symm hsw) (Ne.symm hsw)
        rw [show (fun ω => ξ s ω * ξ s ω * ξ s ω * ξ w ω)
          = fun ω => ξ w ω * ξ s ω * ξ s ω * ξ s ω from funext fun ω => by ring, this]
        simp [hsw]
    · by_cases huw : u = w
      · subst huw; rw [integral_mul4_indep_pair ξ hind hmeas hsu, hv, hv]; simp [hsu]
      · have := L (s := u) (t := s) (u := s) (w := w) (Ne.symm hsu) (Ne.symm hsu) huw
        rw [show (fun ω => ξ s ω * ξ s ω * ξ u ω * ξ w ω)
          = fun ω => ξ u ω * ξ s ω * ξ s ω * ξ w ω from funext fun ω => by ring, this]
        simp [hsu, huw]
  · by_cases hsu : s = u
    · subst hsu
      by_cases htw : t = w
      · subst htw
        rw [show (fun ω => ξ s ω * ξ t ω * ξ s ω * ξ t ω)
          = fun ω => ξ s ω * ξ s ω * ξ t ω * ξ t ω from funext fun ω => by ring,
          integral_mul4_indep_pair ξ hind hmeas hst, hv, hv]
        simp [hst]
      · have := L (s := t) (t := s) (u := s) (w := w) (Ne.symm hst) (Ne.symm hst) htw
        rw [show (fun ω => ξ s ω * ξ t ω * ξ s ω * ξ w ω)
          = fun ω => ξ t ω * ξ s ω * ξ s ω * ξ w ω from funext fun ω => by ring, this]
        simp [hst, htw, Ne.symm hst]
    · by_cases hsw : s = w
      · subst hsw
        by_cases htu : t = u
        · subst htu
          rw [show (fun ω => ξ s ω * ξ t ω * ξ t ω * ξ s ω)
            = fun ω => ξ s ω * ξ s ω * ξ t ω * ξ t ω from funext fun ω => by ring,
            integral_mul4_indep_pair ξ hind hmeas hst, hv, hv]
          simp [hst]
        · have := L (s := t) (t := s) (u := u) (w := s) (Ne.symm hst) htu (Ne.symm hst)
          rw [show (fun ω => ξ s ω * ξ t ω * ξ u ω * ξ s ω)
            = fun ω => ξ t ω * ξ s ω * ξ u ω * ξ s ω from funext fun ω => by ring, this]
          simp [hst, hsu, htu]
      · rw [L hst hsu hsw]; simp [hst, hsu, hsw]

omit [IsProbabilityMeasure P] in
/-- The third moments of independent centred sources. -/
lemma integral_mul3_indep (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) (c₃ : S → ℝ)
    (h3 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω ∂P = c₃ s) (s t u : S) :
    ∫ ω, ξ s ω * ξ t ω * ξ u ω ∂P = if s = t ∧ t = u then c₃ s else 0 := by
  have L : ∀ {s t u : S}, s ≠ t → s ≠ u → ∫ ω, ξ s ω * ξ t ω * ξ u ω ∂P = 0 :=
    fun h1 h2 => integral_mul3_indep_of_ne ξ hind hmeas h0 h1 h2
  by_cases hst : s = t
  · subst hst
    by_cases hsu : s = u
    · subst hsu; simp [h3]
    · rw [show (fun ω => ξ s ω * ξ s ω * ξ u ω) = fun ω => ξ u ω * ξ s ω * ξ s ω from
        funext fun ω => by ring, L (Ne.symm hsu) (Ne.symm hsu)]
      simp [hsu]
  · by_cases hsu : s = u
    · subst hsu
      rw [show (fun ω => ξ s ω * ξ t ω * ξ s ω) = fun ω => ξ t ω * ξ s ω * ξ s ω from
        funext fun ω => by ring, L (Ne.symm hst) (Ne.symm hst)]
      simp [hst]
    · rw [L hst hsu]; simp [hst]

omit [IsProbabilityMeasure P] in
/-- The second moments of independent centred sources. -/
lemma integral_mul2_indep (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s))
    (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0) (v : S → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (s t : S) : ∫ ω, ξ s ω * ξ t ω ∂P = if s = t then v s else 0 := by
  by_cases hst : s = t
  · subst hst; simp [hv]
  · rw [integral_mul2_indep_of_ne ξ hind hmeas h0 hst]; simp [hst]

variable [Fintype S]

/-- **Variance of a quadratic estimator under independent sources.** Let the cells be
`Zᵢ = mᵢ + Σₛ Bᵢₛ ξₛ` for independent centred sources `ξₛ` in `L⁴` with variances `vₛ`, third
moments `c₃ₛ` and fourth cumulants `c₄ₛ` (fourth moment `c₄ₛ + 3vₛ²`): e.g. the levels, each
year's shock and each cell's noise, or the innovations of an AR(1) factor. With `C = B diag(v) Bᵀ`,
`M = BᵀAB` and `a = BᵀAm`,
`Var(Σ Aᵢⱼ ZᵢZⱼ) = 2 tr(ACAC) + 4 (Am)ᵀC(Am) + 4 Σₛ c₃ₛ Mₛₛ aₛ + Σₛ c₄ₛ Mₛₛ²`.
Only one third and one fourth cumulant per source enter. -/
theorem variance_quad_of_sources (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v c₃ c₄ : S → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h3 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω ∂P = c₃ s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = c₄ s + 3 * v s ^ 2)
    (B : Matrix ι S ℝ) (m : ι → ℝ) (A : Matrix ι ι ℝ) (hA : ∀ i j, A j i = A i j) :
    variance (fun ω => ∑ i, ∑ j, A i j * (m i + ∑ s, B i s * ξ s ω)
      * (m j + ∑ s, B j s * ξ s ω)) P
      = 2 * trace (A * (B * diagonal v * Bᵀ) * A * (B * diagonal v * Bᵀ))
        + 4 * (A *ᵥ m) ⬝ᵥ ((B * diagonal v * Bᵀ) *ᵥ (A *ᵥ m))
        + 4 * ∑ s, c₃ s * (Bᵀ * A * B) s s * (Bᵀ *ᵥ (A *ᵥ m)) s
        + ∑ s, c₄ s * (Bᵀ * A * B) s s ^ 2 := by
  set C : Matrix ι ι ℝ := B * diagonal v * Bᵀ with hCdef
  have hC : ∀ i j, C i j = ∑ s, B i s * B j s * v s := fun i j => by
    rw [hCdef, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply]
    exact sum_congr rfl fun s _ => by ring
  let e : ι → Ω → ℝ := fun i ω => ∑ s, B i s * ξ s ω
  let Z : ι → Ω → ℝ := fun i ω => m i + e i ω
  have i2 : ∀ a b, Integrable (fun ω => ξ a ω * ξ b ω) P := fun a b =>
    integrable_mul2 (hL a) (hL b)
  have i3 : ∀ a b c, Integrable (fun ω => ξ a ω * ξ b ω * ξ c ω) P := fun a b c =>
    integrable_mul3 (hL a) (hL b) (hL c)
  have i4 : ∀ a b c d, Integrable (fun ω => ξ a ω * ξ b ω * (ξ c ω * ξ d ω)) P :=
    fun a b c d => by simpa only [mul_assoc] using integrable_mul4 (hL a) (hL b) (hL c) (hL d)
  have hpair : ∀ i j ω, e i ω * e j ω
      = ∑ p : S × S, B i p.1 * B j p.2 * (ξ p.1 ω * ξ p.2 ω) := fun i j ω => by
    simp only [e]; rw [sum_mul_sum_eq, ← Fintype.sum_prod_type']
  have E1 : ∀ i, ∫ ω, e i ω ∂P = 0 := fun i => by
    simp only [e]
    rw [integral_finsetSum _ fun s _ => ((hL s).integrable (by norm_num)).const_mul _]
    exact sum_eq_zero fun s _ => by rw [integral_const_mul, h0, mul_zero]
  have E2 : ∀ i j, ∫ ω, e i ω * e j ω ∂P = C i j := fun i j => by
    simp only [e]
    rw [integral_sum_mul_sum _ _ _ _ _ _ i2]
    simp only [integral_mul2_indep ξ hind hmeas h0 v hv, mul_ite, mul_zero, sum_ite_eq,
      mem_univ, ite_true, hC]
  have E3 : ∀ i j k, ∫ ω, e i ω * e j ω * e k ω ∂P = ∑ s, c₃ s * B i s * B j s * B k s :=
    fun i j k => by
    simp only [hpair]
    rw [integral_sum_mul_sum _ _ _ _ _ _ fun p u => i3 p.1 p.2 u]
    simp only [integral_mul3_indep ξ hind hmeas h0 c₃ h3, Fintype.sum_prod_type, mul_ite,
      mul_zero, ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ite_true]
    exact sum_congr rfl fun s _ => by ring
  have E4 : ∀ i j k l, ∫ ω, e i ω * e j ω * e k ω * e l ω ∂P
      = ∑ s, c₄ s * B i s * B j s * B k s * B l s + C i j * C k l + C i k * C j l
        + C i l * C j k := fun i j k l => by
    have : (fun ω => e i ω * e j ω * e k ω * e l ω) = fun ω => (e i ω * e j ω) * (e k ω * e l ω) :=
      funext fun ω => by ring
    rw [this]
    simp only [hpair]
    rw [integral_sum_mul_sum _ _ _ _ _ _ fun p q => i4 p.1 p.2 q.1 q.2]
    simp only [show ∀ a b c d, ∫ ω, ξ a ω * ξ b ω * (ξ c ω * ξ d ω) ∂P
        = ∫ ω, ξ a ω * ξ b ω * ξ c ω * ξ d ω ∂P from fun a b c d => by simp only [mul_assoc],
      integral_mul4_indep ξ hind hmeas h0 v c₄ hv h4, Fintype.sum_prod_type, hC]
    simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, ite_and, sum_ite_irrel,
      sum_const_zero, sum_ite_eq, mem_univ, ite_true, sum_mul_sum]
    refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_
    · exact sum_congr rfl fun s _ => by ring
    all_goals exact sum_congr rfl fun s _ => sum_congr rfl fun t _ => by ring
  have hZL : ∀ i, MemLp (Z i) 4 P := fun i =>
    (memLp_const _).add (memLp_finsetSum _ fun s _ => (hL s).const_mul _)
  have hm : ∀ i, ∫ ω, Z i ω ∂P = m i := fun i => by
    simp only [Z]
    rw [integral_add (integrable_const _) (integrable_finsetSum _ fun s _ =>
      ((hL s).integrable (by norm_num)).const_mul _), E1]
    simp
  have hc : ∀ i j, covariance (Z i) (Z j) P = C i j := fun i j => by
    simp only [covariance, hm]; simp only [Z, add_sub_cancel_left]; exact E2 i j
  have h3' : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P
      = ∑ s, c₃ s * B i s * B j s * B k s := fun i j k => by
    simp only [Z, add_sub_cancel_left]; exact E3 i j k
  have h4' : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = ∑ s, c₄ s * B i s * B j s * B k s * B l s + C i j * C k l + C i k * C j l
        + C i l * C j k := fun i j k l => by
    simp only [Z, add_sub_cancel_left]; exact E4 i j k l
  have := variance_quad_of_cumulants Z A C m _ _ hA hZL hm hc h3' h4'
  rw [varQuad_sources A C m B c₃ c₄ _ _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)] at this
  exact this

/-- **Expectation of a quadratic estimator under independent sources**: with the cells
`Zᵢ = mᵢ + Σₛ Bᵢₛ ξₛ` as in `variance_quad_of_sources`, `E[Σ Aᵢⱼ ZᵢZⱼ] = Σ Aᵢⱼ (mᵢmⱼ + Cᵢⱼ)`,
`C = B diag(v) Bᵀ`. -/
theorem integral_quad_of_sources (ξ : S → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v : S → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (B : Matrix ι S ℝ) (m : ι → ℝ) (A : Matrix ι ι ℝ) :
    ∫ ω, ∑ i, ∑ j, A i j * (m i + ∑ s, B i s * ξ s ω) * (m j + ∑ s, B j s * ξ s ω) ∂P
      = ∑ i, ∑ j, A i j * (m i * m j + (B * diagonal v * Bᵀ) i j) := by
  let e : ι → Ω → ℝ := fun i ω => ∑ s, B i s * ξ s ω
  have i2 : ∀ a b, Integrable (fun ω => ξ a ω * ξ b ω) P := fun a b =>
    integrable_mul2 (hL a) (hL b)
  have ie : ∀ i, Integrable (e i) P := fun i =>
    integrable_finsetSum _ fun s _ => ((hL s).integrable (by norm_num)).const_mul _
  have iee : ∀ i j, Integrable (fun ω => e i ω * e j ω) P := fun i j =>
    integrable_sum_mul_sum _ _ _ _ _ _ i2
  have E1 : ∀ i, ∫ ω, e i ω ∂P = 0 := fun i => by
    simp only [e]
    rw [integral_finsetSum _ fun s _ => ((hL s).integrable (by norm_num)).const_mul _]
    exact sum_eq_zero fun s _ => by rw [integral_const_mul, h0, mul_zero]
  have E2 : ∀ i j, ∫ ω, e i ω * e j ω ∂P = (B * diagonal v * Bᵀ) i j := fun i j => by
    simp only [e]
    rw [integral_sum_mul_sum _ _ _ _ _ _ i2, Matrix.mul_apply]
    simp only [integral_mul2_indep ξ hind hmeas h0 v hv, mul_ite, mul_zero, sum_ite_eq,
      mem_univ, ite_true, Matrix.mul_diagonal, transpose_apply]
    exact sum_congr rfl fun s _ => by ring
  have term : ∀ i j, ∫ ω, A i j * (m i + e i ω) * (m j + e j ω) ∂P
      = A i j * (m i * m j + (B * diagonal v * Bᵀ) i j) := fun i j => by
    have : (fun ω => A i j * (m i + e i ω) * (m j + e j ω)) = fun ω => A i j *
        (m i * m j + (m i * e j ω + (m j * e i ω + e i ω * e j ω))) := funext fun ω => by ring
    rw [this, integral_const_mul, integral_add, integral_add, integral_add]
    · simp [integral_const_mul, E1, E2]
    all_goals repeat' first
      | with_reducible exact iee _ _ | with_reducible exact ie _
      | with_reducible exact integrable_const _
      | with_reducible apply Integrable.fun_add | with_reducible apply Integrable.const_mul
  have iT : ∀ i j, Integrable (fun ω => A i j * (m i + e i ω) * (m j + e j ω)) P := fun i j => by
    have : (fun ω => A i j * (m i + e i ω) * (m j + e j ω)) = fun ω => A i j *
        (m i * m j + (m i * e j ω + (m j * e i ω + e i ω * e j ω))) := funext fun ω => by ring
    rw [this]
    repeat' first
      | with_reducible exact iee _ _ | with_reducible exact ie _
      | with_reducible exact integrable_const _
      | with_reducible apply Integrable.fun_add | with_reducible apply Integrable.const_mul
  change ∫ ω, ∑ i, ∑ j, A i j * (m i + e i ω) * (m j + e j ω) ∂P = _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iT i j]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => iT i j]
  exact sum_congr rfl fun j _ => term i j

end IndependentSources

end Credibility.Cumulants
