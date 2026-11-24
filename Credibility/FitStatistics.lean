import Credibility.Cumulants
import Credibility.Core
import Credibility.BuhlmannStraub

/-!
# The statistics of the pooled fits: exact variances and covariances

The pooled fits (Bühlmann–Straub, corrBS and the BLUP on corrBS's `K̂`, all with one pooled
variance) depend on the data only through three quadratic statistics
(`studies/damping-theta.md` S53, `studies/price-formula.js`): the pooled within-region variance
`P`, the cross-region residual products `Qn` and the volume-weighted spread of the region means
`B`. Their first-order price (Prasad–Rao `g₃`) needs their variances and covariances. Here:

* `covQuad`, `covariance_quad_of_cumulants`: the covariance of two quadratic forms from moments up
  to order four, by polarization of `variance_quad_of_cumulants`;
* `symQuad`: the matrix of a statistic `Σₖ cₖ (uₖ·x)(vₖ·x)`, and `statP`, `statQn`, `statB`
  as such statistics, so their variances and covariances are `covQuad` of their matrices;
* `covariance_meanStat_resStat`: a statistic of the region means and one of the residuals
  covary only through the fourth cumulant, when the means and the residuals are uncorrelated and
  the third cumulants vanish (so `cov(B, P) = cov(B, Qn) = 0` under normal cells);
  `meanCoef_dot_resCoef_eq_zero`: the means and the residuals are uncorrelated for a level
  covariance plus year noise `Dₜ` with `aᵢₜ Dₜᵢⱼ` constant in `t`;
* `bsZ_bsTau2Hat_of_balanced`, `bsPrice_of_balanced`: with equal region volumes the fitted
  Bühlmann–Straub factor is exactly `1 - v̂/S²`, and its first-order price has a closed form (S56);
* `Core.linMse_lineWeight`, `Core.linMse_lineWeight_sub`: the mean squared error of a blend
  `z eⱼ + (1 - z) b` and the gap between two blends with the same `z`, as exact quadratics in `z`.

Nothing is assumed about the distribution beyond the moment tables.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Credibility.Cumulants

variable {ι : Type*} [Fintype ι]

/-! ### The covariance of two quadratic forms -/

/-- The covariance of `xᵀAx` and `xᵀBx` from the mean `m`, covariance `C`, third cumulants `κ₃`
and fourth cumulants `κ₄` of the cells:
`2 tr(ACBC) + 4 (Am)ᵀC(Bm) + 2 Σ Aᵢⱼ (Bm)ₖ κ₃ᵢⱼₖ + 2 Σ Bᵢⱼ (Am)ₖ κ₃ᵢⱼₖ + Σ Aᵢⱼ Bₖₗ κ₄ᵢⱼₖₗ`. -/
noncomputable def covQuad (A B C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (κ₄ : ι → ι → ι → ι → ℝ) : ℝ :=
  2 * trace (A * C * B * C) + 4 * (A *ᵥ m) ⬝ᵥ (C *ᵥ (B *ᵥ m))
    + 2 * ∑ i, ∑ j, ∑ k, A i j * (B *ᵥ m) k * κ₃ i j k
    + 2 * ∑ i, ∑ j, ∑ k, B i j * (A *ᵥ m) k * κ₃ i j k
    + ∑ i, ∑ j, ∑ k, ∑ l, A i j * B k l * κ₄ i j k l

/-- `covQuad A A = varQuad A`. -/
lemma covQuad_self (A C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (κ₄ : ι → ι → ι → ι → ℝ) : covQuad A A C m κ₃ κ₄ = varQuad A C m κ₃ κ₄ := by
  unfold covQuad varQuad; ring

/-- Polarization: `varQuad (A + B) = varQuad A + 2 covQuad A B + varQuad B` for a symmetric `C`
and `κ₄` symmetric under swapping its two pairs. -/
lemma varQuad_add (A B C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₃ : ι → ι → ι → ℝ)
    (κ₄ : ι → ι → ι → ι → ℝ) (hC : ∀ i j, C j i = C i j)
    (h4 : ∀ i j k l, κ₄ k l i j = κ₄ i j k l) :
    varQuad (A + B) C m κ₃ κ₄ = varQuad A C m κ₃ κ₄ + 2 * covQuad A B C m κ₃ κ₄
      + varQuad B C m κ₃ κ₄ := by
  have htr : trace (B * C * A * C) = trace (A * C * B * C) := by
    rw [show B * C * A * C = (B * C) * (A * C) by simp [Matrix.mul_assoc],
      show A * C * B * C = (A * C) * (B * C) by simp [Matrix.mul_assoc], trace_mul_comm]
  have hCt : Cᵀ = C := by ext i j; exact hC i j
  have hdot : (B *ᵥ m) ⬝ᵥ (C *ᵥ (A *ᵥ m)) = (A *ᵥ m) ⬝ᵥ (C *ᵥ (B *ᵥ m)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hCt, dotProduct_comm]
  have hk : ∑ i, ∑ j, ∑ k, ∑ l, B i j * A k l * κ₄ i j k l
      = ∑ i, ∑ j, ∑ k, ∑ l, A i j * B k l * κ₄ i j k l := by
    have : ∀ f : ι → ι → ι → ι → ℝ,
        ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
      intro f
      calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ p : ι × ι, ∑ q : ι × ι, f p.1 p.2 q.1 q.2 := by
            simp only [Fintype.sum_prod_type]
        _ = ∑ q : ι × ι, ∑ p : ι × ι, f p.1 p.2 q.1 q.2 := sum_comm
        _ = _ := by simp only [Fintype.sum_prod_type]
    rw [this]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => sum_congr rfl fun i _ =>
      sum_congr rfl fun j _ => by rw [h4]; ring
  simp only [varQuad, covQuad, add_mul, mul_add, trace_add, add_mulVec, mulVec_add, dotProduct_add,
    add_dotProduct, Matrix.add_apply, Pi.add_apply, sum_add_distrib, htr, hdot, hk]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Covariance of two quadratic estimators** from moments up to order four. For random cells
`Zᵢ` in `L⁴` with means `m`, covariances `C`, third central moments `κ₃` and fourth central
moments `κ₄ᵢⱼₖₗ + CᵢⱼCₖₗ + CᵢₖCⱼₗ + CᵢₗCⱼₖ`, and symmetric `A`, `B`,
`cov(Σᵢⱼ Aᵢⱼ ZᵢZⱼ, Σᵢⱼ Bᵢⱼ ZᵢZⱼ) = covQuad A B C m κ₃ κ₄`. No distribution is assumed.
A corollary of `variance_quad_of_cumulants` (polarization). -/
theorem covariance_quad_of_cumulants (Z : ι → Ω → ℝ) (A B C : Matrix ι ι ℝ) (m : ι → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ) (hA : ∀ i j, A j i = A i j)
    (hB : ∀ i j, B j i = B i j)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) :
    covariance (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω)
      (fun ω => ∑ i, ∑ j, B i j * Z i ω * Z j ω) P = covQuad A B C m κ₃ κ₄ := by
  have hCs : ∀ i j, C j i = C i j := fun i j => by rw [← hc, ← hc, covariance_comm]
  have h4s : ∀ i j k l, κ₄ k l i j = κ₄ i j k l := fun i j k l => by
    have e1 := h4 i j k l
    have e2 := h4 k l i j
    have : ∫ ω, (Z k ω - m k) * (Z l ω - m l) * (Z i ω - m i) * (Z j ω - m j) ∂P
        = ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [this, e1] at e2
    rw [hCs k i, hCs l i, hCs k j, hCs l j] at e2
    linarith
  have hsum : (fun ω => ∑ i, ∑ j, (A + B) i j * Z i ω * Z j ω)
      = (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω) + fun ω => ∑ i, ∑ j, B i j * Z i ω * Z j ω := by
    funext ω
    simp only [Matrix.add_apply, add_mul, sum_add_distrib, Pi.add_apply]
  have hv := variance_add (memLp_quadForm hZ A) (memLp_quadForm hZ B)
  rw [← hsum, variance_quad_of_cumulants Z (A + B) C m κ₃ κ₄
      (fun i j => by simp [hA, hB]) hZ hm hc h3 h4,
    variance_quad_of_cumulants Z A C m κ₃ κ₄ hA hZ hm hc h3 h4,
    variance_quad_of_cumulants Z B C m κ₃ κ₄ hB hZ hm hc h3 h4,
    varQuad_add A B C m κ₃ κ₄ hCs h4s] at hv
  linarith

/-! ### Statistics that are sums of products of linear statistics -/

section SymQuad

variable {K : Type*} [Fintype K]

/-- The symmetric matrix of the statistic `Σₖ cₖ (uₖ·x)(vₖ·x)`. -/
noncomputable def symQuad (c : K → ℝ) (u v : K → ι → ℝ) : Matrix ι ι ℝ :=
  of fun p q => ∑ k, c k * (u k p * v k q + v k p * u k q) / 2

omit [Fintype ι] in
lemma symQuad_symm (c : K → ℝ) (u v : K → ι → ℝ) (p q : ι) :
    symQuad c u v q p = symQuad c u v p q := by
  simp only [symQuad, of_apply]
  exact sum_congr rfl fun k _ => by ring

/-- `xᵀ (symQuad c u v) x = Σₖ cₖ (uₖ·x)(vₖ·x)`. -/
lemma sum_symQuad (c : K → ℝ) (u v : K → ι → ℝ) (x : ι → ℝ) :
    ∑ p, ∑ q, symQuad c u v p q * x p * x q = ∑ k, c k * (u k ⬝ᵥ x) * (v k ⬝ᵥ x) := by
  simp only [symQuad, of_apply, sum_mul]
  rw [sum_congr rfl fun p _ => sum_comm, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have h1 : ∑ p, ∑ q, c k * (u k p * v k q + v k p * u k q) / 2 * x p * x q
      = c k / 2 * (∑ p, ∑ q, (u k p * x p) * (v k q * x q))
        + c k / 2 * (∑ p, ∑ q, (v k p * x p) * (u k q * x q)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun q _ => by ring
  rw [h1, ← sum_mul_sum, ← sum_mul_sum]
  simp only [dotProduct]
  ring

/-- `(symQuad c u v) y = Σₖ (cₖ/2) ((vₖ·y) uₖ + (uₖ·y) vₖ)`. -/
lemma symQuad_mulVec (c : K → ℝ) (u v : K → ι → ℝ) (y : ι → ℝ) :
    symQuad c u v *ᵥ y = ∑ k, (c k / 2) • ((v k ⬝ᵥ y) • u k + (u k ⬝ᵥ y) • v k) := by
  funext p
  simp only [mulVec, dotProduct, symQuad, of_apply, sum_mul, Finset.sum_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun q _ => by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {K' : Type*} [Fintype K']

/-- **Covariance of two statistics `Σₖ cₖ (uₖ·Z)(vₖ·Z)`** from moments up to order four: `covQuad`
of their matrices. -/
theorem covariance_symQuad (Z : ι → Ω → ℝ) (c : K → ℝ) (u v : K → ι → ℝ) (c' : K' → ℝ)
    (u' v' : K' → ι → ℝ) (C : Matrix ι ι ℝ) (m : ι → ℝ)
    (κ₃ : ι → ι → ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) :
    covariance (fun ω => ∑ k, c k * (u k ⬝ᵥ fun i => Z i ω) * (v k ⬝ᵥ fun i => Z i ω))
      (fun ω => ∑ k, c' k * (u' k ⬝ᵥ fun i => Z i ω) * (v' k ⬝ᵥ fun i => Z i ω)) P
      = covQuad (symQuad c u v) (symQuad c' u' v') C m κ₃ κ₄ := by
  have e : (fun ω => ∑ k, c k * (u k ⬝ᵥ fun i => Z i ω) * (v k ⬝ᵥ fun i => Z i ω))
      = fun ω => ∑ i, ∑ j, symQuad c u v i j * Z i ω * Z j ω := by
    funext ω; exact (sum_symQuad c u v _).symm
  have e' : (fun ω => ∑ k, c' k * (u' k ⬝ᵥ fun i => Z i ω) * (v' k ⬝ᵥ fun i => Z i ω))
      = fun ω => ∑ i, ∑ j, symQuad c' u' v' i j * Z i ω * Z j ω := by
    funext ω; exact (sum_symQuad c' u' v' _).symm
  rw [e, e']
  exact covariance_quad_of_cumulants Z _ _ C m κ₃ κ₄ (symQuad_symm c u v)
    (symQuad_symm c' u' v') hZ hm hc h3 h4

end SymQuad

/-! ### The statistics `P`, `Qn`, `B` of the pooled fits

Cells `xⱼₜ` (region `j`, year `t`) with volumes `wⱼₜ`; `aⱼₜ = wⱼₜ / Wⱼ` with `Wⱼ = Σₜ wⱼₜ`, the
region means `x̄ⱼ = Σₜ aⱼₜ xⱼₜ`, the residuals `rⱼₜ = xⱼₜ - x̄ⱼ = resCoef a j t · x`. -/

section Stats

universe uJ

variable {J T : Type uJ} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- The volume shares `aⱼₜ = wⱼₜ / Wⱼ` within a region. -/
noncomputable def shares (w : J → T → ℝ) (j : J) (t : T) : ℝ := w j t / ∑ s, w j s

/-- The region mean `x̄ⱼ = Σₜ aⱼₜ xⱼₜ`. -/
noncomputable def regionMean (w : J → T → ℝ) (x : J × T → ℝ) (j : J) : ℝ :=
  ∑ t, shares w j t * x (j, t)

/-- The coefficients of the region mean `x̄ⱼ` on the cells. -/
def meanCoef (a : J → T → ℝ) (j : J) (p : J × T) : ℝ := if p.1 = j then a j p.2 else 0

/-- The coefficients of `Σᵢ βᵢ x̄ᵢ` on the cells. -/
def meanComb (a : J → T → ℝ) (β : J → ℝ) (p : J × T) : ℝ := β p.1 * a p.1 p.2

/-- The pooled within-region variance `P = Σⱼₜ wⱼₜ (xⱼₜ - x̄ⱼ)² / (|J|(|T| - 1))`. -/
noncomputable def statP (w : J → T → ℝ) (x : J × T → ℝ) : ℝ :=
  (∑ j, ∑ t, w j t * (x (j, t) - regionMean w x j) ^ 2)
    / (Fintype.card J * ((Fintype.card T : ℝ) - 1))

/-- The cross-region residual products `Qn = Σ_{i<j} Σₜ √(wᵢₜwⱼₜ) rᵢₜ rⱼₜ`, written as half the
sum over `i ≠ j`. -/
noncomputable def statQn (w : J → T → ℝ) (x : J × T → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ t, (if i = j then 0 else Real.sqrt (w i t * w j t) / 2)
    * (x (i, t) - regionMean w x i) * (x (j, t) - regionMean w x j)

/-- The volume-weighted spread of the region means `B = Σⱼ Wⱼ (x̄ⱼ - x̄)²`,
`x̄ = Σⱼ Wⱼ x̄ⱼ / Σⱼ Wⱼ`. -/
noncomputable def statB (w : J → T → ℝ) (x : J × T → ℝ) : ℝ :=
  ∑ j, (∑ t, w j t) * (regionMean w x j
    - (∑ i, (∑ t, w i t) * regionMean w x i) / ∑ i, ∑ t, w i t) ^ 2

/-- The residual is `resCoef a j t · x`. -/
lemma resCoef_dotProduct (w : J → T → ℝ) (x : J × T → ℝ) (j : J) (t : T) :
    resCoef (shares w) j t ⬝ᵥ x = x (j, t) - regionMean w x j := by
  simp only [dotProduct, resCoef, regionMean, Fintype.sum_prod_type, ite_mul, zero_mul,
    sum_ite_irrel, sum_const_zero, sum_ite_eq', sum_ite_eq, mem_univ, ite_true, sub_mul, one_mul,
    sum_sub_distrib]

omit [DecidableEq T] in
/-- `(Σᵢ βᵢ x̄ᵢ coefficients)·y = Σᵢ βᵢ (x̄ᵢ coefficients)·y`. -/
lemma meanComb_dotProduct (a : J → T → ℝ) (β : J → ℝ) (y : J × T → ℝ) :
    meanComb a β ⬝ᵥ y = ∑ i, β i * (meanCoef a i ⬝ᵥ y) := by
  simp only [dotProduct, meanComb, meanCoef, Fintype.sum_prod_type, ite_mul, zero_mul,
    sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun t _ => by ring

/-- The weights `δᵢⱼ - Wᵢ/W` of `x̄ⱼ - x̄` on the region means. -/
noncomputable def spreadWeight (w : J → T → ℝ) (j i : J) : ℝ :=
  (if i = j then 1 else 0) - (∑ t, w i t) / ∑ i, ∑ t, w i t

omit [DecidableEq T] in
lemma meanComb_spread_dotProduct (w : J → T → ℝ) (x : J × T → ℝ) (j : J) :
    meanComb (shares w) (spreadWeight w j) ⬝ᵥ x
      = regionMean w x j - (∑ i, (∑ t, w i t) * regionMean w x i) / ∑ i, ∑ t, w i t := by
  have hm : ∀ i, meanCoef (shares w) i ⬝ᵥ x = regionMean w x i := fun i => by
    simp only [dotProduct, meanCoef, regionMean, Fintype.sum_prod_type, ite_mul, zero_mul,
      sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  simp only [meanComb_dotProduct, hm, spreadWeight, sub_mul, sum_sub_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq', mem_univ, ite_true, div_mul_eq_mul_div, ← sum_div]

/-- The three statistics. -/
inductive Stat
  | P | Qn | B
  deriving DecidableEq

/-- The value of a statistic on the cells `x`. -/
noncomputable def Stat.eval (w : J → T → ℝ) : Stat → (J × T → ℝ) → ℝ
  | .P => statP w
  | .Qn => statQn w
  | .B => statB w

/-- The index type of the products in a statistic. -/
abbrev Stat.Idx (J T : Type uJ) : Stat → Type uJ
  | .P => J × T
  | .Qn => J × J × T
  | .B => J

instance (s : Stat) : Fintype (Stat.Idx J T s) := by cases s <;> unfold Stat.Idx <;> infer_instance

/-- The coefficients `cₖ` of a statistic as `Σₖ cₖ (uₖ·x)(vₖ·x)`. -/
noncomputable def Stat.coef (w : J → T → ℝ) : (s : Stat) → Stat.Idx J T s → ℝ
  | .P => fun k => w k.1 k.2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
  | .Qn => fun k => if k.1 = k.2.1 then 0 else Real.sqrt (w k.1 k.2.2 * w k.2.1 k.2.2) / 2
  | .B => fun j => ∑ t, w j t

/-- The left factors `uₖ`. -/
noncomputable def Stat.left (w : J → T → ℝ) : (s : Stat) → Stat.Idx J T s → J × T → ℝ
  | .P => fun k => resCoef (shares w) k.1 k.2
  | .Qn => fun k => resCoef (shares w) k.1 k.2.2
  | .B => fun j => meanComb (shares w) (spreadWeight w j)

/-- The right factors `vₖ`. -/
noncomputable def Stat.right (w : J → T → ℝ) : (s : Stat) → Stat.Idx J T s → J × T → ℝ
  | .P => fun k => resCoef (shares w) k.1 k.2
  | .Qn => fun k => resCoef (shares w) k.2.1 k.2.2
  | .B => fun j => meanComb (shares w) (spreadWeight w j)

/-- The matrix `A` of a statistic: `s(x) = xᵀAx`. -/
noncomputable def Stat.mat (w : J → T → ℝ) (s : Stat) : Matrix (J × T) (J × T) ℝ :=
  symQuad (s.coef w) (s.left w) (s.right w)

/-- Each statistic is `Σₖ cₖ (uₖ·x)(vₖ·x)`. -/
lemma Stat.eval_eq (w : J → T → ℝ) (s : Stat) (x : J × T → ℝ) :
    s.eval w x = ∑ k, s.coef w k * (s.left w k ⬝ᵥ x) * (s.right w k ⬝ᵥ x) := by
  cases s
  · simp only [Stat.eval, statP, Stat.coef, Stat.left, Stat.right, resCoef_dotProduct,
      Fintype.sum_prod_type, sum_div]
    exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring
  · simp only [Stat.eval, statQn, Stat.coef, Stat.left, Stat.right, resCoef_dotProduct,
      Fintype.sum_prod_type]
  · simp only [Stat.eval, statB, Stat.coef, Stat.left, Stat.right, meanComb_spread_dotProduct]
    exact sum_congr rfl fun j _ => by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Exact covariances of `P`, `Qn`, `B`** (S53): for cells `Zⱼₜ` in `L⁴` with means `m`,
covariances `C`, third cumulants `κ₃` and fourth cumulants `κ₄`, any two of the statistics
have `cov(s(Z), s'(Z)) = covQuad (s.mat w) (s'.mat w) C m κ₃ κ₄`. No distribution is assumed;
under normal cells (`κ₃ = κ₄ = 0`) these are the trace formulas
`2 tr(ACA'C) + 4 (Am)ᵀC(A'm)`. -/
theorem covariance_stat (Z : J × T → Ω → ℝ) (w : J → T → ℝ) (s s' : Stat)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ)
    (κ₃ : J × T → J × T → J × T → ℝ) (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) :
    covariance (fun ω => s.eval w fun i => Z i ω) (fun ω => s'.eval w fun i => Z i ω) P
      = covQuad (s.mat w) (s'.mat w) C m κ₃ κ₄ := by
  simp only [Stat.eval_eq]
  exact covariance_symQuad Z _ _ _ _ _ _ C m κ₃ κ₄ hZ hm hc h3 h4

/-- **Exact variances of `P`, `Qn`, `B`** (S53): `Var s(Z) = varQuad (s.mat w) C m κ₃ κ₄`. -/
theorem variance_stat (Z : J × T → Ω → ℝ) (w : J → T → ℝ) (s : Stat)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ)
    (κ₃ : J × T → J × T → J × T → ℝ) (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k) :
    variance (fun ω => s.eval w fun i => Z i ω) P = varQuad (s.mat w) C m κ₃ κ₄ := by
  have hX : MemLp (fun ω => s.eval w fun i => Z i ω) 2 P := by
    have e : (fun ω => s.eval w fun i => Z i ω)
        = fun ω => ∑ i, ∑ j, s.mat w i j * Z i ω * Z j ω := by
      funext ω; rw [Stat.eval_eq, Stat.mat, sum_symQuad]
    rw [e]; exact memLp_quadForm hZ _
  rw [← covariance_self hX.aemeasurable, covariance_stat Z w s s C m κ₃ κ₄ hZ hm hc h3 h4,
    covQuad_self]

end Stats

/-! ### The balanced world: Bühlmann–Straub's fitted factor and its first-order price (S56)

Equal region volumes `Wⱼ = W₀`. Then the fitted factor is exactly `ẑ = 1 - v̂/S²` with
`v̂ = P/W₀` and the sample variance `S² = B/((J - 1)W₀)` of the region means, and the first-order
(delta-method) price of fitting it has a closed form (law (a) of `studies/damping-theta.md`). -/

section Balanced

universe uB

variable {J T : Type uB} [Fintype J] [Fintype T]

/-- Bühlmann–Straub's between-region estimator from the statistics:
`τ̂² = (B - (J - 1)P) / (W - Σⱼ Wⱼ²/W)`, `W = Σⱼ Wⱼ` (`studies/price-formula.js`). -/
noncomputable def bsTau2Hat (w : J → T → ℝ) (P B : ℝ) : ℝ :=
  (B - (Fintype.card J - 1) * P)
    / (∑ j, ∑ t, w j t - (∑ j, (∑ t, w j t) ^ 2) / ∑ j, ∑ t, w j t)

/-- **The balanced identity** (S56): with equal region volumes `W₀`, Bühlmann–Straub's fitted
factor `ẑ = W₀/(W₀ + P/τ̂²)` is `1 - v̂/S²`, `v̂ = P/W₀`, `S² = B/((J - 1)W₀)`, whenever
`τ̂² ≠ 0` and `B ≠ 0`. -/
theorem bsZ_bsTau2Hat_of_balanced (w : J → T → ℝ) (W₀ : ℝ) (hW : ∀ j, ∑ t, w j t = W₀)
    (hW0 : W₀ ≠ 0) (hJ : 2 ≤ Fintype.card J) (P B : ℝ) (hB : B ≠ 0)
    (hτ : bsTau2Hat w P B ≠ 0) (j : J) :
    bsZ (bsTau2Hat w P B) P w j = 1 - (P / W₀) / (B / ((Fintype.card J - 1) * W₀)) := by
  have hn : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hn1 : (Fintype.card J : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (Fintype.card J : ℝ) ≠ 0 := by linarith
  have hc0 : ∑ j, ∑ t, w j t - (∑ j, (∑ t, w j t) ^ 2) / ∑ j, ∑ t, w j t
      = (Fintype.card J - 1) * W₀ := by
    simp only [hW, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hτ' : B - (Fintype.card J - 1) * P ≠ 0 := by
    intro h; apply hτ; rw [bsTau2Hat, h, zero_div]
  have hτ3 : P - P * Fintype.card J + B ≠ 0 := by
    convert hτ' using 1; ring
  rw [bsZ, bsTau2Hat, hc0, hW]
  have hden : W₀ + P / ((B - (Fintype.card J - 1) * P) / ((Fintype.card J - 1) * W₀))
      = W₀ * B / (B - (Fintype.card J - 1) * P) := by
    field_simp
    linear_combination (-1 : ℝ) * mul_inv_cancel₀ hτ3
  rw [hden, div_div_eq_mul_div]
  field_simp

/-- With equal volumes, `B = W₀ Σⱼ (x̄ⱼ - x̄)²` with the plain average `x̄ = Σⱼ x̄ⱼ / J`, so
`B/((J - 1)W₀)` is the sample variance of the region means. -/
theorem statB_of_balanced (w : J → T → ℝ) (W₀ : ℝ) (hW : ∀ j, ∑ t, w j t = W₀)
    (hW0 : W₀ ≠ 0) [Nonempty J] (x : J × T → ℝ) :
    statB w x = W₀ * ∑ j, (regionMean w x j - (∑ i, regionMean w x i) / Fintype.card J) ^ 2 := by
  have hn0 : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [statB, hW, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  congr 2
  field_simp

/-- The first-order (delta-method) variance of `ẑ = 1 - v̂/S²` at `(v, s)`: with gradient
`(-1/s, v/s²)`, `(1/s)² Var v̂ - 2 (1/s)(v/s²) cov(v̂, S²) + (v/s²)² Var S²`. -/
noncomputable def zHatVar (v s Vv VS Cvs : ℝ) : ℝ :=
  (1 / s) ^ 2 * Vv - 2 * (1 / s) * (v / s ^ 2) * Cvs + (v / s ^ 2) ^ 2 * VS

/-- With `cov(v̂, S²) = 0` (`covariance_statB_eq_zero`), the first-order variance of `ẑ` is
`(1 - z)² (CV²(v̂) + CV²(S²))`, `z = 1 - v/s`. -/
theorem zHatVar_eq (v s Vv VS : ℝ) (hv : v ≠ 0) (hs : s ≠ 0) :
    zHatVar v s Vv VS 0 = (1 - (1 - v / s)) ^ 2 * (Vv / v ^ 2 + VS / s ^ 2) := by
  unfold zHatVar; field_simp; ring

/-- **Law (a), the first-order price of fitting Bühlmann–Straub** (S56). In the balanced world
with `n = J` regions, `T` years, `s = τ² + v`, `z = τ²/s`, normal-theory coefficients of variation
`CV²(v̂) = 2/(J(T - 1))` and `CV²(S²) = 2/(J - 1)` (`Cumulants.variance_sampleCov` with `κ₄ = 0`)
and `cov(v̂, S²) = 0`, the curvature `(1 - 1/J)s` of the blend's error (`BlendMoments.errVar_eq`)
times the first-order variance of `ẑ`, relative to `(1 - z)τ²`, is
`(2/J)(1 + (J - 1)/(J(T - 1)))(1 - z)/z`. -/
theorem bsPrice_of_balanced (n T τ2 v : ℝ) (hn : 2 ≤ n) (hT : 2 ≤ T) (hτ : 0 < τ2) (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v)
        * zHatVar v (τ2 + v) (2 / (n * (T - 1)) * v ^ 2) (2 / (n - 1) * (τ2 + v) ^ 2) 0
        / ((1 - τ2 / (τ2 + v)) * τ2)
      = 2 / n * (1 + (n - 1) / (n * (T - 1))) * (1 - τ2 / (τ2 + v)) / (τ2 / (τ2 + v)) := by
  have hs : τ2 + v ≠ 0 := by positivity
  have hn1 : n - 1 ≠ 0 := by linarith
  have hT1 : T - 1 ≠ 0 := by linarith
  have hn0 : n ≠ 0 := by linarith
  have hv0 : v ≠ 0 := hv.ne'
  rw [zHatVar_eq v _ _ _ hv.ne' hs]
  field_simp
  linear_combination (n * T - 1) * v * (mul_inv_cancel₀ hv0)

/-- …which is at most `(2/J)·T/(T - 1)·(1 - z)/z`, the form of law (a) in the study. -/
theorem bsPrice_le_of_balanced (n T τ2 v : ℝ) (hn : 2 ≤ n) (hT : 2 ≤ T) (hτ : 0 < τ2)
    (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v)
        * zHatVar v (τ2 + v) (2 / (n * (T - 1)) * v ^ 2) (2 / (n - 1) * (τ2 + v) ^ 2) 0
        / ((1 - τ2 / (τ2 + v)) * τ2)
      ≤ 2 / n * (T / (T - 1)) * (1 - τ2 / (τ2 + v)) / (τ2 / (τ2 + v)) := by
  rw [bsPrice_of_balanced n T τ2 v hn hT hτ hv]
  have hz : 0 ≤ (1 - τ2 / (τ2 + v)) / (τ2 / (τ2 + v)) := by
    have : τ2 / (τ2 + v) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact div_nonneg (by linarith) (by positivity)
  have hk : 1 + (n - 1) / (n * (T - 1)) ≤ T / (T - 1) := by
    have hT1 : 0 < T - 1 := by linarith
    rw [show T / (T - 1) = 1 + 1 / (T - 1) by field_simp; ring]
    have : (n - 1) / (n * (T - 1)) ≤ 1 / (T - 1) := by
      rw [div_le_div_iff₀ (by positivity) hT1]; nlinarith
    linarith
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity)) hz

end Balanced

/-! ### Means and residuals: only the fourth cumulant links them -/

section MeanResidual

universe uJ'

variable {J T : Type uJ'} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- Residuals annihilate region-constant vectors: `resCoef a j t · (μ ∘ region) = 0` when
`Σₜ aⱼₜ = 1`. -/
lemma resCoef_dotProduct_regionConst (a : J → T → ℝ) (ha : ∀ j, ∑ t, a j t = 1) (μ : J → ℝ)
    (j : J) (t : T) : resCoef a j t ⬝ᵥ (fun p => μ p.1) = 0 := by
  simp only [dotProduct, resCoef, Fintype.sum_prod_type, ite_mul, zero_mul, sum_ite_irrel,
    sum_const_zero, sum_ite_eq', sum_ite_eq, mem_univ, ite_true, sub_mul, one_mul,
    sum_sub_distrib, ← sum_mul, ha]
  ring

/-- **The region means and the residuals are uncorrelated** for a level covariance `Λ` plus
year noise `Dₜ` (`C = Λ ⊗ 11ᵀ + ⊕ₜ Dₜ`) whenever `aᵢₜ Dₜᵢⱼ` does not depend on the year `t`:
`cov(x̄ᵢ, rⱼₜ) = 0`. Examples: uncorrelated regions with `Dₜᵢᵢ = σᵢ²/wᵢₜ`; or any
`Dₜᵢⱼ = Vᵢⱼ/√(wᵢₜwⱼₜ)` with proportional volumes `wᵢₜ = Wᵢvₜ`. It fails for correlated regions
with non-proportional volumes (Finding 37). -/
theorem meanCoef_dotProduct_resCoef_eq_zero (a : J → T → ℝ) (ha : ∀ j, ∑ t, a j t = 1)
    (Λ : Matrix J J ℝ) (D : T → J → J → ℝ) (c : J → J → ℝ) (hD : ∀ i j t, a i t * D t i j = c i j)
    (C : Matrix (J × T) (J × T) ℝ)
    (hC : ∀ p q, C p q = Λ p.1 q.1 + if p.2 = q.2 then D p.2 p.1 q.1 else 0) (i j : J) (t : T) :
    meanCoef a i ⬝ᵥ (C *ᵥ resCoef a j t) = 0 := by
  have h1 : ∀ p : J × T, (C *ᵥ resCoef a j t) p
      = D p.2 p.1 j * ((if t = p.2 then 1 else 0) - a j p.2) := fun p => by
    simp only [mulVec, dotProduct, hC, resCoef, Fintype.sum_prod_type, mul_ite, mul_zero,
      sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
    simp only [add_mul, sum_add_distrib, ← mul_sum, sum_sub_distrib, ha, ite_mul, zero_mul]
    simp only [sum_ite_eq, mem_univ, ite_true, sub_self, mul_zero, zero_add]
  simp only [dotProduct, h1, meanCoef, Fintype.sum_prod_type, ite_mul, zero_mul, sum_ite_irrel,
    sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  have : ∀ u, a i u * (D u i j * ((if t = u then 1 else 0) - a j u))
      = (if t = u then c i j else 0) - c i j * a j u := fun u => by
    rw [← hD i j u]; split_ifs <;> ring
  simp only [this, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ha]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {K K' : Type*} [Fintype K] [Fintype K']

/-- **A statistic of the region means and one of the residuals covary only through the fourth
cumulant.** Cells `Zⱼₜ` in `L⁴` with region-constant means `μⱼ`, covariance `C`, no third
cumulants, fourth cumulants `κ₄`, and region means uncorrelated with the residuals
(`meanCoef_dotProduct_resCoef_eq_zero`). Then for `S = Σₖ cₖ (Σᵢβₖᵢx̄ᵢ)(Σᵢγₖᵢx̄ᵢ)` and
`R = Σₗ c'ₗ r_{ρ₁ₗ} r_{ρ₂ₗ}`, `cov(S, R) = Σ A_S A_R κ₄`: the Gaussian terms and the skewness
terms vanish. -/
theorem covariance_meanStat_resStat (Z : J × T → Ω → ℝ) (a : J → T → ℝ)
    (ha : ∀ j, ∑ t, a j t = 1) (c : K → ℝ) (β γ : K → J → ℝ) (c' : K' → ℝ)
    (ρ₁ ρ₂ : K' → J × T) (C : Matrix (J × T) (J × T) ℝ) (μ : J → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ i.1)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1)
        * (Z l ω - μ l.1) ∂P = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hres : ∀ i j t, meanCoef a i ⬝ᵥ (C *ᵥ resCoef a j t) = 0) :
    covariance
      (fun ω => ∑ k, c k * (meanComb a (β k) ⬝ᵥ fun i => Z i ω)
        * (meanComb a (γ k) ⬝ᵥ fun i => Z i ω))
      (fun ω => ∑ l, c' l * (resCoef a (ρ₁ l).1 (ρ₁ l).2 ⬝ᵥ fun i => Z i ω)
        * (resCoef a (ρ₂ l).1 (ρ₂ l).2 ⬝ᵥ fun i => Z i ω)) P
      = ∑ p, ∑ q, ∑ r, ∑ s, symQuad c (fun k => meanComb a (β k)) (fun k => meanComb a (γ k)) p q
          * symQuad c' (fun l => resCoef a (ρ₁ l).1 (ρ₁ l).2)
              (fun l => resCoef a (ρ₂ l).1 (ρ₂ l).2) r s * κ₄ p q r s := by
  set AS := symQuad c (fun k => meanComb a (β k)) (fun k => meanComb a (γ k))
  set AR := symQuad c' (fun l => resCoef a (ρ₁ l).1 (ρ₁ l).2)
    (fun l => resCoef a (ρ₂ l).1 (ρ₂ l).2)
  rw [covariance_symQuad Z c _ _ c' _ _ C (fun p => μ p.1) (fun _ _ _ => 0) κ₄ hZ hm hc h3 h4]
  change covQuad AS AR C _ _ κ₄ = _
  have hRm : AR *ᵥ (fun p => μ p.1) = 0 := by
    simp only [AR, symQuad_mulVec, resCoef_dotProduct_regionConst a ha, zero_smul, add_zero,
      smul_zero, sum_const_zero]
  -- the residual part of any `AR y` is uncorrelated with every region mean
  have hR : ∀ y i, meanCoef a i ⬝ᵥ (C *ᵥ (AR *ᵥ y)) = 0 := fun y i => by
    simp only [AR, symQuad_mulVec, mulVec_sum, mulVec_smul, mulVec_add, dotProduct_sum,
      dotProduct_smul, dotProduct_add, hres, smul_zero, add_zero, sum_const_zero]
  have hSCR : AS * C * AR = 0 := by
    refine ext_of_mulVec_single fun q => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
    simp only [AS, symQuad_mulVec, meanComb_dotProduct, hR, mul_zero, sum_const_zero, zero_smul,
      add_zero, smul_zero]
  simp only [covQuad, hSCR, hRm, zero_mul, trace_zero, mulVec_zero, dotProduct_zero, mul_zero,
    sum_const_zero, add_zero, zero_add]

/-- **`cov(B, P) = cov(B, Qn)` is the fourth-cumulant term alone** (S53): cells with
region-constant means, no third cumulants, and region means uncorrelated with the residuals
(`meanCoef_dotProduct_resCoef_eq_zero`), positive region volumes. -/
theorem covariance_statB_eq (Z : J × T → Ω → ℝ) (w : J → T → ℝ) (hw : ∀ j, ∑ t, w j t ≠ 0)
    (s : Stat) (hs : s ≠ .B) (C : Matrix (J × T) (J × T) ℝ) (μ : J → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ i.1)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1)
        * (Z l ω - μ l.1) ∂P = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hres : ∀ i j t, meanCoef (shares w) i ⬝ᵥ (C *ᵥ resCoef (shares w) j t) = 0) :
    covariance (fun ω => Stat.B.eval w fun i => Z i ω) (fun ω => s.eval w fun i => Z i ω) P
      = ∑ p, ∑ q, ∑ r, ∑ t, Stat.B.mat w p q * s.mat w r t * κ₄ p q r t := by
  have ha : ∀ j, ∑ t, shares w j t = 1 := fun j => by
    simp only [shares, ← sum_div, div_self (hw j)]
  cases s
  · simp only [Stat.eval_eq, Stat.mat, Stat.coef, Stat.left, Stat.right]
    exact covariance_meanStat_resStat Z (shares w) ha _ _ _ _ (fun k => k) (fun k => k) C μ κ₄
      hZ hm hc h3 h4 hres
  · simp only [Stat.eval_eq, Stat.mat, Stat.coef, Stat.left, Stat.right]
    exact covariance_meanStat_resStat (K' := J × J × T) Z (shares w) ha (fun j => ∑ t, w j t)
      (spreadWeight w) (spreadWeight w)
      (fun k => if k.1 = k.2.1 then 0 else Real.sqrt (w k.1 k.2.2 * w k.2.1 k.2.2) / 2)
      (fun k => (k.1, k.2.2)) (fun k => (k.2.1, k.2.2)) C μ κ₄ hZ hm hc h3 h4 hres
  · exact absurd rfl hs

/-- **`cov(B, P) = cov(B, Qn) = 0`** (S53) when also the fourth cumulants vanish (e.g. normal
cells), the region means are uncorrelated with the residuals and the means are region-constant.
Neither condition can be dropped (Finding 37). -/
theorem covariance_statB_eq_zero (Z : J × T → Ω → ℝ) (w : J → T → ℝ)
    (hw : ∀ j, ∑ t, w j t ≠ 0) (s : Stat) (hs : s ≠ .B) (C : Matrix (J × T) (J × T) ℝ)
    (μ : J → ℝ) (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ i.1)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ i.1) * (Z j ω - μ j.1) * (Z k ω - μ k.1)
        * (Z l ω - μ l.1) ∂P = C i j * C k l + C i k * C j l + C i l * C j k)
    (hres : ∀ i j t, meanCoef (shares w) i ⬝ᵥ (C *ᵥ resCoef (shares w) j t) = 0) :
    covariance (fun ω => Stat.B.eval w fun i => Z i ω) (fun ω => s.eval w fun i => Z i ω) P
      = 0 := by
  rw [covariance_statB_eq Z w hw s hs C μ (fun _ _ _ _ => 0) hZ hm hc h3
    (fun i j k l => by rw [h4]; ring) hres]
  simp

end MeanResidual

end Credibility.Cumulants

/-! ### The gap between two blends as a quadratic in `z` -/

namespace Credibility.Core

open Finset Matrix

variable {J : Type*} [Fintype J] [DecidableEq J] {K : Matrix J J ℝ}

/-- **The mean squared error of a blend is a quadratic in `z`.** For any collective weights `b`
and `c = eⱼ - b`, the weights `z eⱼ + (1 - z) b = b + z c` have
`linMse = linMse b + 2z cᵀ(Kb - Lⱼ) + z² cᵀKc`. -/
theorem linMse_lineWeight (hK : K.IsHermitian) (L : Matrix J J ℝ) (j : J) (b : J → ℝ) (z : ℝ) :
    linMse K L j (z • Pi.single j 1 + (1 - z) • b)
      = linMse K L j b + 2 * z * ((Pi.single j 1 - b) ⬝ᵥ (K *ᵥ b - L j))
        + z ^ 2 * ((Pi.single j 1 - b) ⬝ᵥ (K *ᵥ (Pi.single j 1 - b))) := by
  set e : J → ℝ := Pi.single j 1 - b
  have hd : z • Pi.single j 1 + (1 - z) • b = b + z • e := by
    funext i; simp only [e, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hs := dotProduct_mulVec_comm_of_isHermitian hK b e
  rw [hd]
  simp only [linMse, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, dotProduct_sub, hs]
  ring

/-- **The gap between two blends with the same `z`** (S53) is an exact quadratic in `z`:
with `c = eⱼ - b`, `c' = eⱼ - b'`,
`linMse(z eⱼ + (1-z) b) - linMse(z eⱼ + (1-z) b') = Δ₀ + 2z Δ₁ + z² Δ₂`,
`Δ₀ = linMse b - linMse b'`, `Δ₁ = cᵀ(Kb - Lⱼ) - c'ᵀ(Kb' - Lⱼ)`, `Δ₂ = cᵀKc - c'ᵀKc'`;
at `z = 1` it is `0`. -/
theorem linMse_lineWeight_sub (hK : K.IsHermitian) (L : Matrix J J ℝ) (j : J) (b b' : J → ℝ)
    (z : ℝ) :
    linMse K L j (z • Pi.single j 1 + (1 - z) • b) - linMse K L j (z • Pi.single j 1 + (1 - z) • b')
      = (linMse K L j b - linMse K L j b')
        + 2 * z * ((Pi.single j 1 - b) ⬝ᵥ (K *ᵥ b - L j)
          - (Pi.single j 1 - b') ⬝ᵥ (K *ᵥ b' - L j))
        + z ^ 2 * ((Pi.single j 1 - b) ⬝ᵥ (K *ᵥ (Pi.single j 1 - b))
          - (Pi.single j 1 - b') ⬝ᵥ (K *ᵥ (Pi.single j 1 - b'))) := by
  rw [linMse_lineWeight hK, linMse_lineWeight hK]
  ring

end Credibility.Core
