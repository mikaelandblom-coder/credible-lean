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
* `variance_statP_of_balanced`, `variance_statB_of_balanced`, `bsPrice_of_balanced_cells`: in the
  balanced world the exact variances of `P` and `B` from the cells, and law (a) with no other input;
* `crossTerm_of_balanced_cumulants`: the first-order cross term `2E[AB]` of the plug-in
  (`PlugIn.lean`) in the balanced world with fourth cumulants, `D` estimated:
  `-2(1 - 1/J)z(1 - z)(γL + γN/T)/J` relative to `(1 - z)τ²`; with `D` known
  (`crossTerm_of_balanced_cumulants_known`) the noise part changes sign (Finding 38);
  `crossTerm_bs_of_cumulants`: the same for any volumes `wᵢₜ`, as finite sums over the regions,
  with `bsAlpha_hasDerivAt` (the first-order direction is the derivative of BS's weights); both
  balanced theorems are its equal-volumes corollaries;
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

/-- The first-order (delta-method) variance of a region's own factor `ẑ = τ²/(τ² + v̂)` at `v`
(`τ²` held fixed): with derivative `-τ²/(τ² + v)²`, `(τ²/(τ² + v)²)² Var v̂`. -/
noncomputable def zOwnVar (τ2 v Vv : ℝ) : ℝ := (τ2 / (τ2 + v) ^ 2) ^ 2 * Vv

/-- `∂z/∂log v = -z(1 - z)`: the first-order variance of the own factor is
`z²(1 - z)² CV²(v̂)`, `z = τ²/(τ² + v)`. -/
theorem zOwnVar_eq (τ2 v Vv : ℝ) (hs : τ2 + v ≠ 0) (hv : v ≠ 0) :
    zOwnVar τ2 v Vv
      = (τ2 / (τ2 + v)) ^ 2 * (1 - τ2 / (τ2 + v)) ^ 2 * (Vv / v ^ 2) := by
  unfold zOwnVar; field_simp; ring

/-- The first-order price of a region's own factor when its `v̂` has `CV²(v̂) = c`: the curvature
`(1 - 1/J)s` of the blend's error (`BlendMoments.errVar_eq`) times `zOwnVar`, relative to
`(1 - z)τ²`, is `(1 - 1/J)·z(1 - z)·c`. -/
theorem ownPrice_eq (n τ2 v c : ℝ) (hτ : 0 < τ2) (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (c * v ^ 2) / ((1 - τ2 / (τ2 + v)) * τ2)
      = (1 - 1 / n) * (τ2 / (τ2 + v)) * (1 - τ2 / (τ2 + v)) * c := by
  have hs : τ2 + v ≠ 0 := by positivity
  have h1 : 1 - τ2 / (τ2 + v) = v / (τ2 + v) := by field_simp; ring
  rw [zOwnVar_eq τ2 v _ hs hv.ne', h1]
  field_simp

/-- **An own factor against Bühlmann–Straub's.** The price of the noise in `v̂` (`CV²(v̂) = c`) for an
own factor at fixed `τ²` is `z²` times its price in law (a), where `ẑ = 1 - v̂/S²` at fixed `S²`
(`zHatVar` with `Var S² = 0`): `∂z/∂log v` is `-z(1 - z)` against `-(1 - z)`. -/
theorem ownPrice_eq_sq_mul_bsPrice (n τ2 v c : ℝ) (hτ : 0 < τ2) (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (c * v ^ 2) / ((1 - τ2 / (τ2 + v)) * τ2)
      = (τ2 / (τ2 + v)) ^ 2 * ((1 - 1 / n) * (τ2 + v) * zHatVar v (τ2 + v) (c * v ^ 2) 0 0
          / ((1 - τ2 / (τ2 + v)) * τ2)) := by
  have hs : τ2 + v ≠ 0 := by positivity
  have h1 : 1 - τ2 / (τ2 + v) = v / (τ2 + v) := by field_simp; ring
  rw [ownPrice_eq n τ2 v c hτ hv, zHatVar_eq v _ _ _ hv.ne' hs, h1]
  have h2 : 1 - (1 - v / (τ2 + v)) = v / (τ2 + v) := by ring
  rw [h2]
  field_simp
  ring

/-- **Law (b), the price of own variances** (S56). In the balanced world with `n = J` regions
and `T` years, each region's own `v̂ⱼ` has the normal-theory `CV² = 2/(T - 1)`, one pooled `v̂`
has `CV² = 2/(J(T - 1))`. The extra first-order price of own factors over pooled ones, relative to
`(1 - z)τ²`, is exactly `(1 - 1/J)²·z(1 - z)·2/(T - 1)`. -/
theorem ownPrice_sub_pooled_of_balanced (n T τ2 v : ℝ) (hn : 2 ≤ n) (hτ : 0 < τ2)
    (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (2 / (T - 1) * v ^ 2) / ((1 - τ2 / (τ2 + v)) * τ2)
      - (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (2 / (n * (T - 1)) * v ^ 2)
          / ((1 - τ2 / (τ2 + v)) * τ2)
      = (1 - 1 / n) ^ 2 * (τ2 / (τ2 + v)) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1)) := by
  have hn0 : n ≠ 0 := by linarith
  rw [ownPrice_eq n τ2 v _ hτ hv, ownPrice_eq n τ2 v _ hτ hv]
  field_simp

/-- …which is at most the study's `z(1 - z)·2/(T - 1)`, itself at most `1/(2(T - 1))`. -/
theorem ownPrice_sub_pooled_le_of_balanced (n T τ2 v : ℝ) (hn : 2 ≤ n) (hT : 2 ≤ T)
    (hτ : 0 < τ2) (hv : 0 < v) :
    (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (2 / (T - 1) * v ^ 2) / ((1 - τ2 / (τ2 + v)) * τ2)
      - (1 - 1 / n) * (τ2 + v) * zOwnVar τ2 v (2 / (n * (T - 1)) * v ^ 2)
          / ((1 - τ2 / (τ2 + v)) * τ2)
      ≤ (τ2 / (τ2 + v)) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1))
    ∧ (τ2 / (τ2 + v)) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1)) ≤ 1 / (2 * (T - 1)) := by
  rw [ownPrice_sub_pooled_of_balanced n T τ2 v hn hτ hv]
  have hT1 : 0 < T - 1 := by linarith
  have hz0 : 0 ≤ τ2 / (τ2 + v) := by positivity
  have hz1 : τ2 / (τ2 + v) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hzz : 0 ≤ τ2 / (τ2 + v) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1)) :=
    mul_nonneg (mul_nonneg hz0 (by linarith)) (by positivity)
  have hn0 : 0 < 1 / n := by have : (0 : ℝ) < n := by linarith
                             positivity
  have hn1 : 0 ≤ 1 - 1 / n := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hn2 : (1 - 1 / n) ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hn2 hzz
    calc (1 - 1 / n) ^ 2 * (τ2 / (τ2 + v)) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1))
        = (1 - 1 / n) ^ 2 * (τ2 / (τ2 + v) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1))) := by ring
      _ ≤ _ := by linarith
  · have hq : τ2 / (τ2 + v) * (1 - τ2 / (τ2 + v)) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (τ2 / (τ2 + v) - 1 / 2)]
    calc τ2 / (τ2 + v) * (1 - τ2 / (τ2 + v)) * (2 / (T - 1))
        ≤ 1 / 4 * (2 / (T - 1)) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = 1 / (2 * (T - 1)) := by field_simp; ring

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

/-- `C rⱼₜ` for a level covariance plus year noise: `(C rⱼₜ)ᵢᵤ = Dᵤᵢⱼ (δₜᵤ - aⱼᵤ)`; the level part
cancels because `Σᵤ aⱼᵤ = 1`. -/
lemma mulVec_resCoef (a : J → T → ℝ) (ha : ∀ j, ∑ t, a j t = 1) (Λ : Matrix J J ℝ)
    (D : T → J → J → ℝ) (C : Matrix (J × T) (J × T) ℝ)
    (hC : ∀ p q, C p q = Λ p.1 q.1 + if p.2 = q.2 then D p.2 p.1 q.1 else 0) (j : J) (t : T)
    (p : J × T) :
    (C *ᵥ resCoef a j t) p = D p.2 p.1 j * ((if t = p.2 then 1 else 0) - a j p.2) := by
  simp only [mulVec, dotProduct, hC, resCoef, Fintype.sum_prod_type, mul_ite, mul_zero,
    sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  simp only [add_mul, sum_add_distrib, ← mul_sum, sum_sub_distrib, ha, ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_univ, ite_true, sub_self, mul_zero, zero_add]

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
  have h1 := mulVec_resCoef a ha Λ D C hC j t
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

/-! ### The balanced world from the cells: exact variances of `P` and `B` (law (a)) -/

section BalancedMoments

universe uM

variable {J T : Type uM} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Variance of a weighted sum of squared linear statistics** that annihilate the mean:
`Var Σₖ cₖ (uₖ·Z)² = Σₖₖ' cₖcₖ' (2 (uₖᵀCuₖ')² + κ₄(uₖ, uₖ, uₖ', uₖ'))`. A corollary of
`variance_sum_mul_lin`. -/
theorem variance_sum_sq_lin {ι K : Type*} [Fintype ι] [Fintype K] (Z : ι → Ω → ℝ)
    (C : Matrix ι ι ℝ) (m : ι → ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (c : K → ℝ) (u : K → ι → ℝ) (hu : ∀ k, u k ⬝ᵥ m = 0) :
    variance (fun ω => ∑ k, c k * (u k ⬝ᵥ fun i => Z i ω) ^ 2) P
      = ∑ k, ∑ k', c k * c k' * (2 * (u k ⬝ᵥ (C *ᵥ u k')) ^ 2
          + ∑ p, ∑ q, ∑ r, ∑ s, u k p * u k q * u k' r * u k' s * κ₄ p q r s) := by
  set e : ι → Ω → ℝ := fun i ω => Z i ω - m i with he
  have hL : ∀ i, MemLp (e i) 4 P := fun i => (hZ i).sub (memLp_const _)
  have h2 : ∀ p q, ∫ ω, e p ω * e q ω ∂P = C p q := fun p q => by
    rw [← hc]; simp only [e, covariance, hm]
  have hue : ∀ k ω, (u k ⬝ᵥ fun i => Z i ω) = ∑ p, u k p * e p ω := fun k ω => by
    have := hu k
    simp only [dotProduct] at this ⊢
    simp only [e, mul_sub, sum_sub_distrib, this, sub_zero]
  have hfun : (fun ω => ∑ k, c k * (u k ⬝ᵥ fun i => Z i ω) ^ 2)
      = fun ω => ∑ k, (∑ p, (c k * u k p) * e p ω) * (∑ q, u k q * e q ω) := by
    funext ω
    refine sum_congr rfl fun k _ => ?_
    rw [hue, sq, ← mul_assoc]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  rw [hfun, variance_sum_mul_lin e hL C κ₄ h2 h4 (fun k p => c k * u k p) u]
  refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => ?_
  have hd : ∀ k k' : K, (fun p => c k * u k p) ⬝ᵥ (C *ᵥ u k') = c k * (u k ⬝ᵥ (C *ᵥ u k')) :=
    fun k k' => by
      rw [show (fun p => c k * u k p) = c k • u k from rfl, smul_dotProduct, smul_eq_mul]
  have hd' : ∀ k k' : K, u k ⬝ᵥ (C *ᵥ fun p => c k' * u k' p) = c k' * (u k ⬝ᵥ (C *ᵥ u k')) :=
    fun k k' => by
      rw [show (fun p => c k' * u k' p) = c k' • u k' from rfl, mulVec_smul, dotProduct_smul,
        smul_eq_mul]
  have hk : ∑ p, ∑ q, ∑ r, ∑ s, c k * u k p * u k q * (c k' * u k' r) * u k' s * κ₄ p q r s
      = c k * c k' * ∑ p, ∑ q, ∑ r, ∑ s, u k p * u k q * u k' r * u k' s * κ₄ p q r s := by
    simp only [mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => sum_congr rfl fun r _ =>
      sum_congr rfl fun s _ => by ring
  have hdd : (fun p => c k * u k p) ⬝ᵥ (C *ᵥ fun p => c k' * u k' p)
      = c k * c k' * (u k ⬝ᵥ (C *ᵥ u k')) := by
    rw [show (fun p => c k' * u k' p) = c k' • u k' from rfl, mulVec_smul, dotProduct_smul,
      smul_eq_mul, hd]; ring
  rw [hdd, hd, hd', hk]
  ring

/-- The balanced Bühlmann–Straub covariance table of the cells: independent regions, level
variance `τ²`, noise variance `σ²/w` per cell, uncorrelated across years. -/
noncomputable def bsCov (τ2 σsq w : ℝ) : Matrix (J × T) (J × T) ℝ :=
  of fun p q => (if p.1 = q.1 then τ2 else 0)
    + if p.2 = q.2 then (if p.1 = q.1 then σsq / w else 0) else 0

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Equal volumes have equal shares `1/|T|`. -/
lemma shares_const [Nonempty T] (w : ℝ) (hw : w ≠ 0) :
    shares (fun (_ : J) (_ : T) => w) = fun _ _ => 1 / (Fintype.card T : ℝ) := by
  have hn : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  funext j t
  simp only [shares, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- In the balanced table the residuals of different regions are uncorrelated and
`cov(rⱼₜ, rⱼₜ') = (σ²/w)(δₜₜ' - 1/|T|)`. -/
lemma resCoef_dotProduct_bsCov [Nonempty T] (τ2 σsq w : ℝ) (j j' : J) (t t' : T) :
    resCoef (fun _ _ => 1 / (Fintype.card T : ℝ)) j t
        ⬝ᵥ (bsCov τ2 σsq w *ᵥ resCoef (fun _ _ => 1 / (Fintype.card T : ℝ)) j' t')
      = if j = j' then σsq / w * ((if t = t' then 1 else 0) - 1 / Fintype.card T) else 0 := by
  have hn : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : ∀ j : J, ∑ t : T, (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) j t = 1 :=
    fun j => by simp only [sum_const, card_univ, nsmul_eq_mul]; field_simp
  have h1 := mulVec_resCoef _ ha (fun i j => if i = j then τ2 else 0)
    (fun _ i j => if i = j then σsq / w else 0) (bsCov τ2 σsq w) (fun p q => rfl) j' t'
  simp only [dotProduct, h1, resCoef, Fintype.sum_prod_type, ite_mul, zero_mul, sum_ite_irrel,
    sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  by_cases hj : j = j'
  · subst hj
    simp only [ite_true]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
      sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
      nsmul_eq_mul]
    split_ifs <;> field_simp <;> ring
  · simp [hj]

/-- In the balanced table, `cov(Σᵢβᵢx̄ᵢ, Σᵢγᵢx̄ᵢ) = (τ² + σ²/(w|T|)) Σᵢ βᵢγᵢ`. -/
lemma meanComb_dotProduct_bsCov [Nonempty T] (τ2 σsq w : ℝ) (β γ : J → ℝ) :
    meanComb (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) β
        ⬝ᵥ (bsCov τ2 σsq w *ᵥ meanComb (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) γ)
      = (τ2 + σsq / (w * Fintype.card T)) * ∑ i, β i * γ i := by
  have hn : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ p : J × T, (bsCov τ2 σsq w *ᵥ meanComb (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) γ) p
      = γ p.1 * (τ2 + σsq / (w * Fintype.card T)) := fun p => by
    simp only [mulVec, dotProduct, bsCov, meanComb, of_apply, Fintype.sum_prod_type, add_mul,
      ite_mul, zero_mul, sum_add_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq,
      mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
    by_cases hw : w = 0
    · subst hw; simp; field_simp
    · field_simp
  simp only [dotProduct, h1, meanComb, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
    mul_sum]
  refine sum_congr rfl fun i _ => ?_
  field_simp

/-- `Σₜₜ' (δₜₜ' - 1/|T|)² = |T| - 1`. -/
lemma sum_centering_sq (hT : 0 < Fintype.card T) :
    ∑ t : T, ∑ t' : T, ((if t = t' then (1 : ℝ) else 0) - 1 / Fintype.card T) ^ 2
      = (Fintype.card T : ℝ) - 1 := by
  simpa [Matrix.trace, Matrix.mul_apply, centering, sq, eq_comm] using trace_centering_sq (T := T) hT

omit [DecidableEq T] in
/-- Equal volumes: the spread weights are `δᵢⱼ - 1/|J|`. -/
lemma spreadWeight_const [Nonempty J] [Nonempty T] (w : ℝ) (hw : w ≠ 0) (j i : J) :
    spreadWeight (fun (_ : J) (_ : T) => w) j i = (if i = j then 1 else 0) - 1 / Fintype.card J := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hT : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [spreadWeight, sum_const, card_univ, nsmul_eq_mul]
  congr 1
  field_simp

omit [DecidableEq T] [Fintype T] in
/-- `Σᵢ (δᵢⱼ - 1/|J|)(δᵢⱼ' - 1/|J|) = δⱼⱼ' - 1/|J|`. -/
lemma sum_centering_mul [Nonempty J] (j j' : J) :
    ∑ i : J, ((if i = j then (1 : ℝ) else 0) - 1 / Fintype.card J)
        * ((if i = j' then 1 else 0) - 1 / Fintype.card J)
      = (if j = j' then 1 else 0) - 1 / Fintype.card J := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
  by_cases h : j = j'
  · subst h; simp
  · simp [h, Ne.symm h]


end BalancedMoments

/-! ### The balanced world with fourth cumulants (the corrected price) -/

section BalancedCumulants

universe uK

variable {J T : Type uK} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The fourth-cumulant table of balanced cells `xⱼₜ = μ + Lⱼ + eⱼₜ` with independent levels of
fourth cumulant `κL` and independent noise of fourth cumulant `κN/w²` per cell:
`κL` when all four cells are in one region, plus `κN/w²` when they are one cell. -/
noncomputable def bsK4 (κL κN w : ℝ) (p q r s : J × T) : ℝ :=
  ∑ i : J, κL * ((if p.1 = i then 1 else 0) * (if q.1 = i then 1 else 0)
      * (if r.1 = i then 1 else 0) * (if s.1 = i then 1 else 0))
    + ∑ c : J × T, κN / w ^ 2 * ((if p = c then 1 else 0) * (if q = c then 1 else 0)
      * (if r = c then 1 else 0) * (if s = c then 1 else 0))

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- `Σ_{pqrs} aₚ b_q c_r d_s fₚf_qf_rf_s = (a·f)(b·f)(c·f)(d·f)`. -/
lemma sum_mul4_indicator {ι : Type*} [Fintype ι] (a b c d f : ι → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * c r * d s * (f p * f q * f r * f s)
      = (∑ p, a p * f p) * (∑ q, b q * f q) * (∑ r, c r * f r) * (∑ s, d s * f s) := by
  have e : ∀ p q r s, a p * b q * c r * d s * (f p * f q * f r * f s)
      = (a p * f p) * ((b q * f q) * ((c r * f r) * (d s * f s))) := fun _ _ _ _ => by ring
  simp only [e, ← mul_sum, ← sum_mul]
  ring

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- Move an inner sum out of four outer ones. -/
lemma sum4_sum_comm {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → ι → ι → ι → κ → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, ∑ i, F p q r s i = ∑ i, ∑ p, ∑ q, ∑ r, ∑ s, F p q r s i := by
  rw [sum_congr rfl fun p _ => sum_congr rfl fun q _ => sum_congr rfl fun r _ => sum_comm]
  rw [sum_congr rfl fun p _ => sum_congr rfl fun q _ => sum_comm]
  rw [sum_congr rfl fun p _ => sum_comm]
  rw [sum_comm]

/-- **The fourth-cumulant term of `bsK4`**:
`Σ u u u' u' κ₄ = κL Σᵢ (Σₜ uᵢₜ)²(Σₜ u'ᵢₜ)² + (κN/w²) Σ_c u_c² u'_c²`. -/
lemma sum_bsK4 (κL κN w : ℝ) (u u' : J × T → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, u p * u q * u' r * u' s * bsK4 κL κN w p q r s
      = κL * ∑ i, (∑ t, u (i, t)) ^ 2 * (∑ t, u' (i, t)) ^ 2
        + κN / w ^ 2 * ∑ c, u c ^ 2 * u' c ^ 2 := by
  simp only [bsK4, mul_add, sum_add_distrib, mul_sum]
  rw [sum4_sum_comm, sum4_sum_comm]
  have h1 : ∀ i : J, ∑ p, ∑ q, ∑ r, ∑ s, u p * u q * u' r * u' s
      * (κL * ((if p.1 = i then 1 else 0) * (if q.1 = i then 1 else 0)
        * (if r.1 = i then 1 else 0) * (if s.1 = i then 1 else 0)))
      = κL * ((∑ t, u (i, t)) ^ 2 * (∑ t, u' (i, t)) ^ 2) := fun i => by
    have := sum_mul4_indicator u u u' u' (fun p : J × T => if p.1 = i then 1 else 0)
    have hf : ∀ v : J × T → ℝ, ∑ p, v p * (if p.1 = i then 1 else 0) = ∑ t, v (i, t) :=
      fun v => by
        simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
        rw [sum_comm]; simp
    rw [hf, hf] at this
    rw [show κL * ((∑ t, u (i, t)) ^ 2 * (∑ t, u' (i, t)) ^ 2)
      = κL * ((∑ t, u (i, t)) * (∑ t, u (i, t)) * (∑ t, u' (i, t)) * (∑ t, u' (i, t))) by ring,
      ← this, mul_sum]
    exact sum_congr rfl fun p _ => by
      rw [mul_sum]; exact sum_congr rfl fun q _ => by
        rw [mul_sum]; exact sum_congr rfl fun r _ => by
          rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  have h2 : ∀ c : J × T, ∑ p, ∑ q, ∑ r, ∑ s, u p * u q * u' r * u' s
      * (κN / w ^ 2 * ((if p = c then 1 else 0) * (if q = c then 1 else 0)
        * (if r = c then 1 else 0) * (if s = c then 1 else 0)))
      = κN / w ^ 2 * (u c ^ 2 * u' c ^ 2) := fun c => by
    have := sum_mul4_indicator u u u' u' (fun p : J × T => if p = c then 1 else 0)
    have hf : ∀ v : J × T → ℝ, ∑ p, v p * (if p = c then 1 else 0) = v c :=
      fun v => by simp [mul_ite]
    rw [hf, hf] at this
    rw [show κN / w ^ 2 * (u c ^ 2 * u' c ^ 2) = κN / w ^ 2 * (u c * u c * u' c * u' c) by ring,
      ← this, mul_sum]
    exact sum_congr rfl fun p _ => by
      rw [mul_sum]; exact sum_congr rfl fun q _ => by
        rw [mul_sum]; exact sum_congr rfl fun r _ => by
          rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  simp only [h1, h2, ← mul_sum]

omit [Fintype J] in
/-- A residual sums to zero over the years of any region. -/
lemma sum_resCoef_region (a : J → T → ℝ) (ha : ∀ j, ∑ t, a j t = 1) (j i : J) (t : T) :
    ∑ u, resCoef a j t (i, u) = 0 := by
  simp only [resCoef]
  split_ifs with h
  · subst h; simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, ha, sub_self]
  · simp

/-- `Σ_{(j,t)} rⱼₜ(c)² = 1 - 1/|T|` for equal shares. -/
lemma sum_resCoef_sq [Nonempty T] (c : J × T) :
    ∑ k : J × T, resCoef (fun _ _ => 1 / (Fintype.card T : ℝ)) k.1 k.2 c ^ 2
      = ((Fintype.card T : ℝ) - 1) / Fintype.card T := by
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [resCoef, Fintype.sum_prod_type, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ite_true]
  simp only [sub_sq, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, sum_add_distrib, sum_sub_distrib,
    sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **The variance of `P` in the balanced world with fourth cumulants** (`bsK4`: levels `κL`,
noise `κN/w²` per cell), no other distributional assumption:
`Var P = 2σ⁴/(J(T - 1)) + κN/(JT)`. The levels cancel. -/
theorem variance_statP_of_balanced_cumulants [Nonempty J] (Z : J × T → Ω → ℝ)
    (τ2 σsq w μ κL κN : ℝ) (hw : w ≠ 0) (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 κL κN w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    variance (fun ω => statP (fun _ _ => w) fun i => Z i ω) P
      = 2 * σsq ^ 2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
        + κN / (Fintype.card J * Fintype.card T) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hn2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by linarith
  set a : J → T → ℝ := fun _ _ => 1 / (Fintype.card T : ℝ)
  have ha : ∀ j, ∑ t, a j t = 1 := fun j => by
    simp only [a, sum_const, card_univ, nsmul_eq_mul]; field_simp
  set c0 : ℝ := w / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
  have e : (fun ω => statP (fun _ _ => w) fun i => Z i ω)
      = fun ω => ∑ k : J × T, c0 * (resCoef a k.1 k.2 ⬝ᵥ fun i => Z i ω) ^ 2 := by
    funext ω
    rw [show statP (fun _ _ => w) (fun i => Z i ω)
      = Stat.P.eval (fun _ _ => w) (fun i => Z i ω) from rfl, Stat.eval_eq]
    simp only [Stat.coef, Stat.left, Stat.right, shares_const w hw, sq, mul_assoc, a, c0]
  rw [e, variance_sum_sq_lin Z (bsCov τ2 σsq w) (fun _ => μ) (bsK4 κL κN w) hZ hm hc h4
    (fun (_ : J × T) => c0) (fun (k : J × T) => resCoef a k.1 k.2)
    (fun (k : J × T) => resCoef_dotProduct_regionConst a ha (fun _ => μ) k.1 k.2)]
  simp only [mul_add, sum_add_distrib]
  have g : ∑ k : J × T, ∑ k' : J × T, c0 * c0
      * (2 * (resCoef a k.1 k.2 ⬝ᵥ (bsCov τ2 σsq w *ᵥ resCoef a k'.1 k'.2)) ^ 2)
      = 2 * σsq ^ 2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) := by
    simp only [a, resCoef_dotProduct_bsCov, Fintype.sum_prod_type, ite_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, mul_ite, sum_ite_irrel,
      sum_const_zero, sum_ite_eq, mem_univ, ite_true, mul_pow]
    have hs := sum_centering_sq (T := T) (by omega)
    simp only [← mul_sum, hs, sum_const, card_univ, nsmul_eq_mul, c0]
    field_simp
  have k4 : ∑ k : J × T, ∑ k' : J × T, c0 * c0
      * ∑ p, ∑ q, ∑ r, ∑ s, resCoef a k.1 k.2 p * resCoef a k.1 k.2 q * resCoef a k'.1 k'.2 r
        * resCoef a k'.1 k'.2 s * bsK4 κL κN w p q r s
      = κN / (Fintype.card J * Fintype.card T) := by
    simp only [sum_bsK4, sum_resCoef_region a ha, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_const_zero, mul_zero, zero_add, mul_sum]
    rw [sum_congr rfl fun k _ => sum_comm, sum_comm]
    have hA := sum_resCoef_sq (J := J) (T := T)
    have : ∀ x : J × T, ∑ k : J × T, ∑ k' : J × T, c0 * c0 * (κN / w ^ 2
        * (resCoef a k.1 k.2 x ^ 2 * resCoef a k'.1 k'.2 x ^ 2))
        = c0 * c0 * (κN / w ^ 2) * (((Fintype.card T : ℝ) - 1) / Fintype.card T) ^ 2 := by
      intro x
      rw [sq (((Fintype.card T : ℝ) - 1) / Fintype.card T), ← hA x, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun k _ => by
        rw [mul_sum]; exact sum_congr rfl fun k' _ => by ring
    simp only [this, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, c0]
    field_simp
  rw [g, k4]

/-- `Σⱼ (δᵢⱼ - 1/|J|)² = 1 - 1/|J|`. -/
lemma sum_centering_sq_col [Nonempty J] (i : J) :
    ∑ j : J, ((if i = j then (1 : ℝ) else 0) - 1 / Fintype.card J) ^ 2
      = ((Fintype.card J : ℝ) - 1) / Fintype.card J := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [sub_sq, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, sum_add_distrib, sum_sub_distrib,
    sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **The variance of `B` in the balanced world with fourth cumulants** (`bsK4`):
`Var B = 2(wT)²s²(J - 1) + (wT)²(κL + κN/(w²T³))(J - 1)²/J`, `s = τ² + σ²/(wT)`; `κL + κN/(w²T³)`
is the fourth cumulant of a region mean. So `Var S² = 2s²/(J - 1) + (κL + κN/(w²T³))/J`. -/
theorem variance_statB_of_balanced_cumulants [Nonempty J] (Z : J × T → Ω → ℝ)
    (τ2 σsq w μ κL κN : ℝ) (hw : w ≠ 0) (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 κL κN w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    variance (fun ω => statB (fun _ _ => w) fun i => Z i ω) P
      = 2 * (Fintype.card T * w) ^ 2 * (τ2 + σsq / (w * Fintype.card T)) ^ 2
          * ((Fintype.card J : ℝ) - 1)
        + (Fintype.card T * w) ^ 2 * (κL + κN / (w ^ 2 * Fintype.card T ^ 3))
          * ((Fintype.card J : ℝ) - 1) ^ 2 / Fintype.card J := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set a : J → T → ℝ := fun _ _ => 1 / (Fintype.card T : ℝ)
  set β : J → J → ℝ := fun j i => (if i = j then 1 else 0) - 1 / Fintype.card J
  have e : (fun ω => statB (fun _ _ => w) fun i => Z i ω)
      = fun ω => ∑ j : J, (Fintype.card T * w) * (meanComb a (β j) ⬝ᵥ fun i => Z i ω) ^ 2 := by
    funext ω
    rw [show statB (fun _ _ => w) (fun i => Z i ω)
      = Stat.B.eval (fun _ _ => w) (fun i => Z i ω) from rfl, Stat.eval_eq]
    have hβ : spreadWeight (fun (_ : J) (_ : T) => w) = β := by
      funext j i; exact spreadWeight_const w hw j i
    simp only [Stat.coef, Stat.left, Stat.right, shares_const w hw, hβ, sq, mul_assoc, a,
      sum_const, card_univ, nsmul_eq_mul]
  have hmc : ∀ i, meanCoef a i ⬝ᵥ (fun _ => μ) = μ := fun i => by
    simp only [dotProduct, meanCoef, a, Fintype.sum_prod_type, ite_mul, zero_mul]
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hu : ∀ j, meanComb a (β j) ⬝ᵥ (fun _ => μ) = 0 := fun j => by
    have hβ0 : ∑ i : J, β j i = 0 := by
      simp only [β, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
        nsmul_eq_mul]; field_simp; ring
    rw [meanComb_dotProduct]
    simp only [hmc, ← sum_mul, hβ0, zero_mul]
  rw [e, variance_sum_sq_lin Z (bsCov τ2 σsq w) (fun _ => μ) (bsK4 κL κN w) hZ hm hc h4
    (fun (_ : J) => Fintype.card T * w) (fun (j : J) => meanComb a (β j)) hu]
  simp only [mul_add, sum_add_distrib]
  have g : ∑ j : J, ∑ j' : J, Fintype.card T * w * (Fintype.card T * w)
      * (2 * (meanComb a (β j) ⬝ᵥ (bsCov τ2 σsq w *ᵥ meanComb a (β j'))) ^ 2)
      = 2 * (Fintype.card T * w) ^ 2 * (τ2 + σsq / (w * Fintype.card T)) ^ 2
          * ((Fintype.card J : ℝ) - 1) := by
    simp only [a, meanComb_dotProduct_bsCov, β, sum_centering_mul, mul_pow]
    have hs := sum_centering_sq (T := J) Fintype.card_pos
    simp only [← mul_sum, hs]
    ring
  have hreg : ∀ j i, ∑ t, meanComb a (β j) (i, t) = β j i := fun j i => by
    simp only [meanComb, a, sum_const, card_univ, nsmul_eq_mul]; field_simp
  have hcell : ∀ j j', ∑ x : J × T, meanComb a (β j) x ^ 2 * meanComb a (β j') x ^ 2
      = 1 / (Fintype.card T : ℝ) ^ 3 * ∑ i, β j i ^ 2 * β j' i ^ 2 := fun j j' => by
    simp only [meanComb, a, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  have k4 : ∑ j : J, ∑ j' : J, Fintype.card T * w * (Fintype.card T * w)
      * ∑ p, ∑ q, ∑ r, ∑ s, meanComb a (β j) p * meanComb a (β j) q * meanComb a (β j') r
        * meanComb a (β j') s * bsK4 κL κN w p q r s
      = (Fintype.card T * w) ^ 2 * (κL + κN / (w ^ 2 * Fintype.card T ^ 3))
          * ((Fintype.card J : ℝ) - 1) ^ 2 / Fintype.card J := by
    simp only [sum_bsK4, hreg, hcell]
    have hb : ∀ j j' : J, Fintype.card T * w * (Fintype.card T * w)
        * (κL * ∑ i, β j i ^ 2 * β j' i ^ 2
          + κN / w ^ 2 * (1 / (Fintype.card T : ℝ) ^ 3 * ∑ i, β j i ^ 2 * β j' i ^ 2))
        = ∑ i, Fintype.card T * w * (Fintype.card T * w)
          * ((κL + κN / (w ^ 2 * Fintype.card T ^ 3)) * (β j i ^ 2 * β j' i ^ 2)) :=
      fun j j' => by
        simp only [← mul_sum]
        field_simp
    rw [sum_congr rfl fun j _ => sum_congr rfl fun j' _ => hb j j']
    rw [sum_congr rfl fun j _ => sum_comm, sum_comm]
    have hcol : ∀ i, ∑ j, β j i ^ 2 = ((Fintype.card J : ℝ) - 1) / Fintype.card J :=
      fun i => sum_centering_sq_col i
    have : ∀ i : J, ∑ j : J, ∑ j' : J, Fintype.card T * w * (Fintype.card T * w)
        * ((κL + κN / (w ^ 2 * Fintype.card T ^ 3)) * (β j i ^ 2 * β j' i ^ 2))
        = (Fintype.card T * w) ^ 2 * (κL + κN / (w ^ 2 * Fintype.card T ^ 3))
          * (((Fintype.card J : ℝ) - 1) / Fintype.card J) ^ 2 := fun i => by
      rw [sq (((Fintype.card J : ℝ) - 1) / Fintype.card J), ← hcol i, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun j _ => by
        rw [mul_sum]; exact sum_congr rfl fun j' _ => by ring
    simp only [this, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [g, k4]
  ring

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- `Σ A A' κ₄` for `A = Σₖ cₖuₖuₖᵀ`, `A' = Σₗ c'ₗu'ₗu'ₗᵀ` is `Σₖₗ cₖc'ₗ κ₄(uₖ, uₖ, u'ₗ, u'ₗ)`. -/
lemma sum_symQuad_mul_symQuad {ι K K' : Type*} [Fintype ι] [Fintype K] [Fintype K']
    (c : K → ℝ) (u : K → ι → ℝ) (c' : K' → ℝ) (u' : K' → ι → ℝ)
    (κ : ι → ι → ι → ι → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, symQuad c u u p q * symQuad c' u' u' r s * κ p q r s
      = ∑ k, ∑ l, c k * c' l
          * ∑ p, ∑ q, ∑ r, ∑ s, u k p * u k q * u' l r * u' l s * κ p q r s := by
  have hsK : ∀ p q, symQuad c u u p q = ∑ k, c k * (u k p * u k q) := fun p q => by
    simp only [symQuad, of_apply]
    exact sum_congr rfl fun k _ => by ring
  have hsK' : ∀ p q, symQuad c' u' u' p q = ∑ l, c' l * (u' l p * u' l q) := fun p q => by
    simp only [symQuad, of_apply]
    exact sum_congr rfl fun k _ => by ring
  conv_lhs => simp only [hsK, hsK', sum_mul, mul_sum]
  rw [sum4_sum_comm, sum_congr rfl fun l _ => sum4_sum_comm _, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  refine sum_congr rfl fun l _ => ?_
  simp only [mul_sum]
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => sum_congr rfl fun r _ =>
    sum_congr rfl fun s _ => by ring

/-- **`cov(B, P)` in the balanced world with fourth cumulants** (`bsK4`; no third cumulants):
`κN (J - 1)/(JT)`. It vanishes exactly when the noise has no fourth cumulant (Finding 37); the
levels do not enter. -/
theorem covariance_statB_statP_of_balanced_cumulants [Nonempty J] (Z : J × T → Ω → ℝ)
    (τ2 σsq w μ κL κN : ℝ) (hw : 0 < w) (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 κL κN w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    covariance (fun ω => statB (fun _ _ => w) fun i => Z i ω)
      (fun ω => statP (fun _ _ => w) fun i => Z i ω) P
      = κN * ((Fintype.card J : ℝ) - 1) / (Fintype.card J * Fintype.card T) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hn2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by linarith
  have hw0 : w ≠ 0 := hw.ne'
  have ha : ∀ j, ∑ t, (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) j t = 1 := fun j => by
    simp only [sum_const, card_univ, nsmul_eq_mul]; field_simp
  set β : J → J → ℝ := fun j i => (if i = j then 1 else 0) - 1 / Fintype.card J
  have hres : ∀ i j t, meanCoef (shares (fun (_ : J) (_ : T) => w)) i
      ⬝ᵥ (bsCov τ2 σsq w *ᵥ resCoef (shares (fun (_ : J) (_ : T) => w)) j t) = 0 := by
    rw [shares_const w hw0]
    exact meanCoef_dotProduct_resCoef_eq_zero _ ha
      (fun i j => if i = j then τ2 else 0) (fun _ i j => if i = j then σsq / w else 0)
      (fun i j => 1 / Fintype.card T * (if i = j then σsq / w else 0)) (fun _ _ _ => rfl)
      _ (fun _ _ => rfl)
  rw [show (fun ω => statB (fun _ _ => w) fun i => Z i ω)
      = fun ω => Stat.B.eval (fun _ _ => w) fun i => Z i ω from rfl,
    show (fun ω => statP (fun _ _ => w) fun i => Z i ω)
      = fun ω => Stat.P.eval (fun _ _ => w) fun i => Z i ω from rfl,
    covariance_statB_eq Z (fun _ _ => w)
      (fun j => by simp only [sum_const, card_univ, nsmul_eq_mul]; positivity) Stat.P (by decide)
      (bsCov τ2 σsq w) (fun _ => μ) (bsK4 κL κN w) hZ hm hc h3 h4 hres]
  have hβ : spreadWeight (fun (_ : J) (_ : T) => w) = β := by
    funext j i; exact spreadWeight_const w hw0 j i
  simp only [Stat.mat, Stat.coef, Stat.left, Stat.right, shares_const w hw0, hβ,
    sum_const, card_univ, nsmul_eq_mul]
  rw [sum_symQuad_mul_symQuad]
  simp only [sum_bsK4, sum_resCoef_region _ ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, sum_const_zero, zero_add, mul_sum]
  rw [sum_congr rfl fun j _ => sum_comm, sum_comm]
  have hA := sum_resCoef_sq (J := J) (T := T)
  have hG : ∀ x : J × T, ∑ j, meanComb (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) (β j) x ^ 2
      = ((Fintype.card J : ℝ) - 1) / Fintype.card J / (Fintype.card T : ℝ) ^ 2 := fun x => by
    simp only [meanComb, mul_pow, ← sum_mul, sum_centering_sq_col x.1, β]
    field_simp
  have : ∀ x : J × T, ∑ j : J, ∑ k : J × T, Fintype.card T * w
      * (w / (Fintype.card J * ((Fintype.card T : ℝ) - 1)))
      * (κN / w ^ 2 * (meanComb (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) (β j) x ^ 2 * resCoef (fun (_ : J) (_ : T) => 1 / (Fintype.card T : ℝ)) k.1 k.2 x ^ 2))
      = Fintype.card T * w * (w / (Fintype.card J * ((Fintype.card T : ℝ) - 1))) * (κN / w ^ 2)
        * ((((Fintype.card J : ℝ) - 1) / Fintype.card J / (Fintype.card T : ℝ) ^ 2)
          * (((Fintype.card T : ℝ) - 1) / Fintype.card T)) := fun x => by
    rw [← hG x, ← hA x, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun j _ => by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  simp only [this, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- **Law (a) with fourth cumulants: the corrected price** (S56). In the balanced world with
levels of fourth cumulant `κL`, noise of fourth cumulant `κN/w²` per cell and no third
cumulants, the first-order price of Bühlmann–Straub's fitted factor, from the actual moments of
`v̂ = P/(wT)` and `S² = B/((J - 1)wT)`, is, relative to `(1 - z)τ²`,
`(1 - 1/J)(1 - z)/z · [2/(J(T - 1)) + 2/(J - 1) + κL/(J s²) + γN z²/(JT)]`, `γN = κN/σ⁴` the
excess kurtosis of the noise, `s = τ² + σ²/(wT)`, `z = τ²/s`. Noise kurtosis enters through
`Var v̂`, `Var S²` and `cov(v̂, S²)`, which together leave `γN z²`. -/
theorem bsPrice_of_balanced_cumulants [Nonempty J] (Z : J × T → Ω → ℝ) (τ2 σsq w μ κL κN : ℝ)
    (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : 0 < w) (hJ : 2 ≤ Fintype.card J)
    (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 κL κN w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    (1 - 1 / (Fintype.card J : ℝ)) * (τ2 + σsq / (w * Fintype.card T))
        * zHatVar (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (variance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w)) P)
          (variance (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P)
          (covariance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w))
            (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
              / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P)
        / ((1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) * τ2)
      = (1 - 1 / (Fintype.card J : ℝ)) * (1 - τ2 / (τ2 + σsq / (w * Fintype.card T)))
          / (τ2 / (τ2 + σsq / (w * Fintype.card T)))
        * (2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) + 2 / ((Fintype.card J : ℝ) - 1)
          + κL / (Fintype.card J * (τ2 + σsq / (w * Fintype.card T)) ^ 2)
          + κN / σsq ^ 2 * (τ2 / (τ2 + σsq / (w * Fintype.card T))) ^ 2
            / (Fintype.card J * Fintype.card T)) := by
  have hn2 : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hJ1 : (Fintype.card J : ℝ) - 1 ≠ 0 := by linarith
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by linarith
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by linarith
  have hw0 : w ≠ 0 := hw.ne'
  have hσ0 : σsq ≠ 0 := hσ.ne'
  have hτ0 : τ2 ≠ 0 := hτ.ne'
  have hs0 : τ2 + σsq / (w * Fintype.card T) ≠ 0 := by positivity
  have hVP := variance_statP_of_balanced_cumulants Z τ2 σsq w μ κL κN hw0 hT hZ hm hc h4
  have hVB := variance_statB_of_balanced_cumulants Z τ2 σsq w μ κL κN hw0 hT hZ hm hc h4
  have hBP := covariance_statB_statP_of_balanced_cumulants Z τ2 σsq w μ κL κN hw hT hZ hm hc h3 h4
  have hv : variance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w)) P
      = (2 * σsq ^ 2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
        + κN / (Fintype.card J * Fintype.card T)) / (Fintype.card T * w) ^ 2 := by
    simp_rw [div_eq_mul_inv _ ((Fintype.card T : ℝ) * w)]
    rw [variance_mul_const, hVP, inv_pow, div_eq_mul_inv _ (((Fintype.card T : ℝ) * w) ^ 2)]
  have hS : variance (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
        / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P
      = (2 * (Fintype.card T * w) ^ 2 * (τ2 + σsq / (w * Fintype.card T)) ^ 2
          * ((Fintype.card J : ℝ) - 1)
        + (Fintype.card T * w) ^ 2 * (κL + κN / (w ^ 2 * Fintype.card T ^ 3))
          * ((Fintype.card J : ℝ) - 1) ^ 2 / Fintype.card J)
        / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w)) ^ 2 := by
    simp_rw [div_eq_mul_inv _ (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))]
    rw [variance_mul_const, hVB, inv_pow,
      div_eq_mul_inv _ ((((Fintype.card J : ℝ) - 1) * (Fintype.card T * w)) ^ 2)]
  have hcov : covariance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w))
      (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
        / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P
      = κN * ((Fintype.card J : ℝ) - 1) / (Fintype.card J * Fintype.card T)
        / ((Fintype.card T * w) * (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) := by
    simp_rw [div_eq_mul_inv _ ((Fintype.card T : ℝ) * w),
      div_eq_mul_inv _ (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))]
    rw [covariance_mul_const_left, covariance_mul_const_right, covariance_comm, hBP]
    field_simp
  have hz : 1 - τ2 / (τ2 + σsq / (w * Fintype.card T))
      = σsq / (w * Fintype.card T) / (τ2 + σsq / (w * Fintype.card T)) := by
    field_simp; ring
  rw [hv, hS, hcov, hz]
  unfold zHatVar
  field_simp
  ring

/-- **The variance of `P` in the balanced world**: equal volumes `w`, independent regions,
level variance `τ²`, noise variance `σ²/w` uncorrelated across years, cells in `L⁴` with a
common mean and no fourth cumulants: `Var P = 2σ⁴/(J(T - 1))`. -/
theorem variance_statP_of_balanced [Nonempty J] (Z : J × T → Ω → ℝ) (τ2 σsq w μ : ℝ)
    (hw : w ≠ 0) (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    variance (fun ω => statP (fun _ _ => w) fun i => Z i ω) P
      = 2 * σsq ^ 2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) := by
  have h4' : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 0 0 w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k := fun i j k l => by rw [h4]; simp [bsK4]
  rw [variance_statP_of_balanced_cumulants Z τ2 σsq w μ 0 0 hw hT hZ hm hc h4']
  simp

/-- **The variance of `B` in the balanced world** (same assumptions):
`Var B = 2 (wT)² (τ² + σ²/(wT))² (J - 1)`, so the sample variance `S² = B/((J - 1)wT)` of the
region means has `Var S² = 2 s²/(J - 1)`, `s = τ² + σ²/(wT)`. -/
theorem variance_statB_of_balanced [Nonempty J] (Z : J × T → Ω → ℝ) (τ2 σsq w μ : ℝ)
    (hw : w ≠ 0) (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    variance (fun ω => statB (fun _ _ => w) fun i => Z i ω) P
      = 2 * (Fintype.card T * w) ^ 2 * (τ2 + σsq / (w * Fintype.card T)) ^ 2
        * ((Fintype.card J : ℝ) - 1) := by
  have h4' : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 0 0 w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k := fun i j k l => by rw [h4]; simp [bsK4]
  rw [variance_statB_of_balanced_cumulants Z τ2 σsq w μ 0 0 hw hT hZ hm hc h4']
  simp

/-- **Law (a) from the cells** (S56). In the balanced world (equal volumes `w`, independent
regions, level variance `τ²`, noise variance `σ²/w` uncorrelated across years, a common mean, no
third and fourth cumulants), the first-order price of Bühlmann–Straub's fitted factor
`ẑ = 1 - v̂/S²`, computed from the actual variances and covariance of `v̂ = P/(wT)` and
`S² = B/((J - 1)wT)`, is `(2/J)(1 + (J - 1)/(J(T - 1)))(1 - z)/z` relative to `(1 - z)τ²`, with
`v = σ²/(wT)`, `z = τ²/(τ² + v)`. -/
theorem bsPrice_of_balanced_cells [Nonempty J] (Z : J × T → Ω → ℝ) (τ2 σsq w μ : ℝ)
    (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : 0 < w) (hJ : 2 ≤ Fintype.card J)
    (hT : 2 ≤ Fintype.card T)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = μ)
    (hc : ∀ i j, covariance (Z i) (Z j) P = bsCov τ2 σsq w i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) ∂P = 0)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k) :
    (1 - 1 / (Fintype.card J : ℝ)) * (τ2 + σsq / (w * Fintype.card T))
        * zHatVar (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (variance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w)) P)
          (variance (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P)
          (covariance (fun ω => (statP (fun _ _ => w) fun i => Z i ω) / (Fintype.card T * w))
            (fun ω => (statB (fun _ _ => w) fun i => Z i ω)
              / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) P)
        / ((1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) * τ2)
      = 2 / Fintype.card J * (1 + ((Fintype.card J : ℝ) - 1)
          / (Fintype.card J * ((Fintype.card T : ℝ) - 1)))
        * (1 - τ2 / (τ2 + σsq / (w * Fintype.card T)))
        / (τ2 / (τ2 + σsq / (w * Fintype.card T))) := by
  have h4' : ∀ i j k l, ∫ ω, (Z i ω - μ) * (Z j ω - μ) * (Z k ω - μ) * (Z l ω - μ) ∂P
      = bsK4 0 0 w i j k l
        + bsCov τ2 σsq w i j * bsCov τ2 σsq w k l + bsCov τ2 σsq w i k * bsCov τ2 σsq w j l
        + bsCov τ2 σsq w i l * bsCov τ2 σsq w j k := fun i j k l => by rw [h4]; simp [bsK4]
  have hn2 : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hJ1 : (Fintype.card J : ℝ) - 1 ≠ 0 := by linarith
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by linarith
  rw [bsPrice_of_balanced_cumulants Z τ2 σsq w μ 0 0 hτ hσ hw hJ hT hZ hm hc h3 h4']
  simp only [zero_div, zero_mul, add_zero]
  field_simp
  ring

end BalancedCumulants


/-! ### The cross term of the plug-in at first order (fourth cumulants, `D` estimated) -/

section LinLinSumSq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- `(a·X)(b·X) Σₖ cₖ(uₖ·X)²` as a sum of fourfold products. -/
lemma lin_lin_sumSq_eq {ι K : Type*} [Fintype ι] [Fintype K] (X : ι → Ω → ℝ)
    (a b : ι → ℝ) (c : K → ℝ) (u : K → ι → ℝ) (ω : Ω) :
    (a ⬝ᵥ fun p => X p ω) * (b ⬝ᵥ fun p => X p ω) * ∑ k, c k * (u k ⬝ᵥ fun p => X p ω) ^ 2
      = ∑ k, ∑ p, ∑ q, ∑ r, ∑ s, c k * (a p * b q * u k r * u k s)
          * (X p ω * X q ω * X r ω * X s ω) := by
  simp only [dotProduct, sq, mul_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl fun s _ => sum_congr rfl fun r _ => sum_comm]
  rw [sum_congr rfl fun s _ => sum_comm, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_congr rfl fun s _ => sum_comm, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun r _ => sum_congr rfl fun s _ => by ring

/-- `(a·X)(b·X) Σₖ cₖ(uₖ·X)²` is integrable for `X` in `L⁴`. -/
lemma integrable_lin_lin_sumSq {ι K : Type*} [Fintype ι] [Fintype K] (X : ι → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (a b : ι → ℝ) (c : K → ℝ) (u : K → ι → ℝ) :
    Integrable (fun ω => (a ⬝ᵥ fun p => X p ω) * (b ⬝ᵥ fun p => X p ω)
      * ∑ k, c k * (u k ⬝ᵥ fun p => X p ω) ^ 2) P := by
  simp only [lin_lin_sumSq_eq]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun s _ =>
        (integrable_mul4 (hX p) (hX q) (hX r) (hX s)).const_mul _

/-- **Two linear statistics times a sum of squares**, from the raw fourth moments
`κ₄ + CC + CC + CC`: `E[(a·X)(b·X) Σₖ cₖ(uₖ·X)²] = Σₖ cₖ((aᵀCb)(uₖᵀCuₖ) + 2(aᵀCuₖ)(bᵀCuₖ)
+ κ₄(a, b, uₖ, uₖ))`. No distribution is assumed. -/
theorem integral_lin_lin_sumSq {ι K : Type*} [Fintype ι] [Fintype K] (X : ι → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (C : Matrix ι ι ℝ) (κ₄ : ι → ι → ι → ι → ℝ)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = κ₄ p q r s + C p q * C r s + C p r * C q s + C p s * C q r)
    (a b : ι → ℝ) (c : K → ℝ) (u : K → ι → ℝ) :
    ∫ ω, (a ⬝ᵥ fun p => X p ω) * (b ⬝ᵥ fun p => X p ω)
        * ∑ k, c k * (u k ⬝ᵥ fun p => X p ω) ^ 2 ∂P
      = ∑ k, c k * ((a ⬝ᵥ (C *ᵥ b)) * (u k ⬝ᵥ (C *ᵥ u k))
          + 2 * ((a ⬝ᵥ (C *ᵥ u k)) * (b ⬝ᵥ (C *ᵥ u k)))
          + ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * u k r * u k s * κ₄ p q r s) := by
  have i4 := fun p q r s => integrable_mul4 (hX p) (hX q) (hX r) (hX s)
  simp only [lin_lin_sumSq_eq]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun s _ => (i4 p q r s).const_mul _]
  refine sum_congr rfl fun k _ => ?_
  have dpm : ∀ x y : ι → ℝ, x ⬝ᵥ (C *ᵥ y) = ∑ p, ∑ q, x p * C p q * y q := fun x y => by
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  have E : ∫ ω, ∑ p, ∑ q, ∑ r, ∑ s, c k * (a p * b q * u k r * u k s)
          * (X p ω * X q ω * X r ω * X s ω) ∂P
      = ∑ p, ∑ q, ∑ r, ∑ s, c k * (a p * b q * u k r * u k s)
          * (κ₄ p q r s + C p q * C r s + C p r * C q s + C p s * C q r) := by
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
      integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ =>
        (i4 p q r s).const_mul _]
    refine sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun r _ =>
        integrable_finsetSum _ fun s _ => (i4 p q r s).const_mul _]
    refine sum_congr rfl fun q _ => ?_
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ =>
        (i4 p q r s).const_mul _]
    refine sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum _ fun s _ => (i4 p q r s).const_mul _]
    refine sum_congr rfl fun s _ => ?_
    rw [integral_const_mul, h4]
  rw [E]
  have P1 : ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * u k r * u k s * (C p q * C r s)
      = (a ⬝ᵥ (C *ᵥ b)) * (u k ⬝ᵥ (C *ᵥ u k)) := by
    rw [dpm, dpm, sum_mul_sum]; simp only [sum_mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun q _ => sum_congr rfl fun r _ => sum_congr rfl fun s _ => by ring
  have P2 : ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * u k r * u k s * (C p r * C q s)
      = (a ⬝ᵥ (C *ᵥ u k)) * (b ⬝ᵥ (C *ᵥ u k)) := by
    rw [dpm, dpm, sum_mul_sum]; simp only [sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => sum_congr rfl fun r _ =>
      sum_congr rfl fun s _ => by ring
  have P3 : ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * u k r * u k s * (C p s * C q r)
      = (a ⬝ᵥ (C *ᵥ u k)) * (b ⬝ᵥ (C *ᵥ u k)) := by
    rw [dpm, dpm, sum_mul_sum]; simp only [sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun r _ => sum_congr rfl fun s _ => by ring
  have hsplit : ∀ p q r s, c k * (a p * b q * u k r * u k s)
      * (κ₄ p q r s + C p q * C r s + C p r * C q s + C p s * C q r)
      = c k * (a p * b q * u k r * u k s * κ₄ p q r s)
        + c k * (a p * b q * u k r * u k s * (C p q * C r s))
        + c k * (a p * b q * u k r * u k s * (C p r * C q s))
        + c k * (a p * b q * u k r * u k s * (C p s * C q r)) := fun p q r s => by ring
  simp only [hsplit, sum_add_distrib, ← mul_sum, P1, P2, P3]
  ring

end LinLinSumSq

section Prim
universe uX
variable {J T : Type uX} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- The cells `xⱼₜ = μ + Lⱼ + eⱼₜ` from the primitives `x = (L, e)` on `J ⊕ (J × T)`. -/
def cellsOf (μ : ℝ) (x : J ⊕ (J × T) → ℝ) : J × T → ℝ :=
  fun c => μ + x (Sum.inl c.1) + x (Sum.inr c)

/-- A linear statistic `u` of the cells as one of the primitives: `(Σₜ uᵢₜ)` on `Lᵢ`, `uᵢₜ` on `eᵢₜ`. -/
def pullCoef (u : J × T → ℝ) : J ⊕ (J × T) → ℝ := Sum.elim (fun i => ∑ t, u (i, t)) u

/-- The variances of the primitives: `τ²` for a level, `σ²/w` for a noise cell. -/
noncomputable def primVar (τ2 σsq w : ℝ) : J ⊕ (J × T) → ℝ := Sum.elim (fun _ => τ2) (fun _ => σsq / w)

/-- The fourth-cumulant table of uncorrelated primitives: `κL` for a level, `κN/w²` for a noise
cell, on the diagonal `p = q = r = s` only. -/
noncomputable def primK4 (κL κN w : ℝ) (p q r s : J ⊕ (J × T)) : ℝ :=
  if s = p then if r = p then if q = p then Sum.elim (fun _ => κL) (fun _ => κN / w ^ 2) p
    else 0 else 0 else 0

omit [DecidableEq J] [DecidableEq T] in
/-- `u·x = μ Σu + (pullCoef u)·(L, e)`. -/
lemma dotProduct_cellsOf (μ : ℝ) (u : J × T → ℝ) (x : J ⊕ (J × T) → ℝ) :
    u ⬝ᵥ cellsOf μ x = μ * ∑ c, u c + pullCoef u ⬝ᵥ x := by
  have h1 : ∑ c : J × T, u c * x (Sum.inl c.1) = ∑ i, (∑ t, u (i, t)) * x (Sum.inl i) := by
    rw [Fintype.sum_prod_type]; simp only [sum_mul]
  simp only [dotProduct, cellsOf, pullCoef, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_add, sum_add_distrib, ← sum_mul, h1]
  ring

end Prim

section CrossIntegrals

universe uY
variable {J T : Type uY} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- `E[(a·X)(b·X)] = aᵀCb` from the second moments `C`. -/
lemma integral_lin_mul_lin {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ p, MemLp (X p) 4 P)
    (C : Matrix ι ι ℝ) (h2 : ∀ p q, ∫ ω, X p ω * X q ω ∂P = C p q) (a b : ι → ℝ) :
    ∫ ω, (a ⬝ᵥ fun p => X p ω) * (b ⬝ᵥ fun p => X p ω) ∂P = a ⬝ᵥ (C *ᵥ b) := by
  simp only [dotProduct]
  rw [integral_sum_mul_sum _ _ _ _ _ _ fun p q => integrable_mul2 (hX p) (hX q)]
  simp only [h2, mulVec, dotProduct, mul_sum]
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring


/-- The first-order (delta-method) error of `ẑ = 1 - v̂/S²` at `(v, s)`:
`-(v̂ - v)/s + (v/s²)(S² - s)`; `zHatVar` is its variance. -/
noncomputable def zHatLin (v s vh Sh : ℝ) : ℝ := -(vh - v) / s + v / s ^ 2 * (Sh - s)

end CrossIntegrals


/-! ### The cross term of the plug-in at first order, any volumes -/

section CrossGeneral

universe uG
variable {J T : Type uG} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- Variances of the primitives with volumes `wᵢₜ`: `τ²` for a level, `σ²/wᵢₜ` for a noise cell. -/
noncomputable def primVarW (τ2 σsq : ℝ) (w : J → T → ℝ) : J ⊕ (J × T) → ℝ :=
  Sum.elim (fun _ => τ2) (fun c => σsq / w c.1 c.2)

/-- A diagonal fourth-cumulant table: `kd p` when `p = q = r = s`, else `0`. -/
noncomputable def diagK4 {ι : Type*} [DecidableEq ι] (kd : ι → ℝ) (p q r s : ι) : ℝ :=
  if s = p then if r = p then if q = p then kd p else 0 else 0 else 0

/-- Fourth cumulants of the primitives with volumes: `κL` for a level, `κN/wᵢₜ²` for a noise cell. -/
noncomputable def primK4W (κL κN : ℝ) (w : J → T → ℝ) : J ⊕ (J × T) → J ⊕ (J × T) → J ⊕ (J × T) → J ⊕ (J × T) → ℝ :=
  diagK4 (Sum.elim (fun _ => κL) (fun c => κN / w c.1 c.2 ^ 2))

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- The fourth-cumulant term of a diagonal table: `Σₚ aₚbₚuₚ² kdₚ`. -/
lemma sum_diagK4 {ι : Type*} [Fintype ι] [DecidableEq ι] (kd a b u : ι → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, a p * b q * u r * u s * diagK4 kd p q r s
      = ∑ p, a p * b p * u p ^ 2 * kd p := by
  simp only [diagK4, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact sum_congr rfl fun _ _ => by ring

/-- `xᵀ diag(primVarW) y`, split into levels and noise. -/
lemma dotProduct_diagonal_primVarW (τ2 σsq : ℝ) (w : J → T → ℝ) (x y : J ⊕ (J × T) → ℝ) :
    x ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ y)
      = τ2 * ∑ i, x (Sum.inl i) * y (Sum.inl i)
        + ∑ c, σsq / w c.1 c.2 * (x (Sum.inr c) * y (Sum.inr c)) := by
  simp only [dotProduct, mulVec_diagonal, Fintype.sum_sum_type, primVarW, Sum.elim_inl,
    Sum.elim_inr, mul_sum]
  congr 1 <;> exact sum_congr rfl fun _ _ => by ring

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- The shares of a region sum to one. -/
lemma sum_shares (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (i : J) : ∑ t, shares w i t = 1 := by
  simp only [shares, ← sum_div]; exact div_self (hW i)

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- `shares/w = 1/W`. -/
lemma shares_div (w : J → T → ℝ) (hw : ∀ i t, w i t ≠ 0) (i : J) (t : T) :
    shares w i t / w i t = 1 / ∑ s, w i s := by
  simp only [shares]; have := hw i t; field_simp

omit [DecidableEq T] in
/-- `Σᵢ βᵢx̄ᵢ` is the dot product with `meanComb`. -/
lemma sum_mul_regionMean (w : J → T → ℝ) (β : J → ℝ) (x : J × T → ℝ) :
    ∑ i, β i * regionMean w x i = meanComb (shares w) β ⬝ᵥ x := by
  rw [meanComb_dotProduct]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  simp only [dotProduct, meanCoef, regionMean, Fintype.sum_prod_type, ite_mul, zero_mul,
    sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]

omit [DecidableEq J] [DecidableEq T] in
/-- The coefficients of `Σᵢβᵢx̄ᵢ` sum to `Σβ`. -/
lemma sum_meanComb (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (β : J → ℝ) :
    ∑ c, meanComb (shares w) β c = ∑ i, β i := by
  simp only [meanComb, Fintype.sum_prod_type, ← mul_sum, sum_shares w hW, mul_one]

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- `Σᵢβᵢx̄ᵢ` loads `βᵢ` on `Lᵢ` and `βᵢaᵢₜ` on `eᵢₜ`. -/
lemma pullCoef_meanComb_shares (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (β : J → ℝ) :
    pullCoef (meanComb (shares w) β) = Sum.elim β (fun c => β c.1 * shares w c.1 c.2) := by
  funext p
  cases p with
  | inl i => simp only [pullCoef, meanComb, Sum.elim_inl, ← mul_sum, sum_shares w hW, mul_one]
  | inr c => simp only [pullCoef, meanComb, Sum.elim_inr]


/-- `Σᵢ βᵢx̄ᵢ` on the primitives: `βᵢ` on `Lᵢ`, `βᵢaᵢₜ` on `eᵢₜ`. -/
noncomputable def linW (w : J → T → ℝ) (β : J → ℝ) : J ⊕ (J × T) → ℝ :=
  Sum.elim β (fun c => β c.1 * shares w c.1 c.2)

/-- The error `Σᵢ αᵢx̄ᵢ - (μ + Lⱼ)` on the primitives. -/
noncomputable def errW (w : J → T → ℝ) (α : J → ℝ) (j : J) : J ⊕ (J × T) → ℝ :=
  linW w α - Pi.single (Sum.inl j) 1

omit [DecidableEq T] in
/-- `Σᵢβᵢx̄ᵢ = μΣβ + linW β·(L, e)`. -/
lemma sum_mul_regionMean_cellsOf (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (β : J → ℝ)
    (μ : ℝ) (y : J ⊕ (J × T) → ℝ) :
    ∑ i, β i * regionMean w (cellsOf μ y) i = μ * ∑ i, β i + linW w β ⬝ᵥ y := by
  rw [sum_mul_regionMean, dotProduct_cellsOf, sum_meanComb w hW, pullCoef_meanComb_shares w hW]
  rfl

/-- The error `Σᵢαᵢx̄ᵢ - (μ + Lⱼ)` is `errW α j·(L, e)` when `Σα = 1`. -/
lemma errW_dotProduct (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (α : J → ℝ)
    (hα : ∑ i, α i = 1) (j : J) (μ : ℝ) (y : J ⊕ (J × T) → ℝ) :
    ∑ i, α i * regionMean w (cellsOf μ y) i - (μ + y (Sum.inl j)) = errW w α j ⬝ᵥ y := by
  rw [sum_mul_regionMean_cellsOf w hW, hα, errW, sub_dotProduct, single_dotProduct]
  ring

/-- `P` as a sum of squared residuals of the primitives, any volumes. -/
lemma statP_cellsOfW (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (μ : ℝ)
    (y : J ⊕ (J × T) → ℝ) :
    statP w (cellsOf μ y)
      = ∑ k : J × T, w k.1 k.2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
          * (pullCoef (resCoef (shares w) k.1 k.2) ⬝ᵥ y) ^ 2 := by
  rw [show statP w (cellsOf μ y) = Stat.P.eval w (cellsOf μ y) from rfl, Stat.eval_eq]
  simp only [Stat.coef, Stat.left, Stat.right, dotProduct_cellsOf]
  refine sum_congr rfl fun k _ => ?_
  have h0 : ∑ c : J × T, resCoef (shares w) k.1 k.2 c = 0 := by
    rw [Fintype.sum_prod_type]
    exact sum_eq_zero fun i _ => sum_resCoef_region _ (sum_shares w hW) k.1 i k.2
  rw [h0]; ring

omit [DecidableEq T] in
/-- The spread weights sum to zero. -/
lemma sum_spreadWeight (w : J → T → ℝ) (hW : ∑ i, ∑ t, w i t ≠ 0) (k : J) :
    ∑ i, spreadWeight w k i = 0 := by
  simp only [spreadWeight, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, ← sum_div,
    div_self hW, sub_self]

/-- `B` as a sum of squared spreads of the primitives, any volumes. -/
lemma statB_cellsOfW (w : J → T → ℝ) (hW : ∀ i, ∑ t, w i t ≠ 0) (hW' : ∑ i, ∑ t, w i t ≠ 0)
    (μ : ℝ) (y : J ⊕ (J × T) → ℝ) :
    statB w (cellsOf μ y)
      = ∑ k : J, (∑ t, w k t) * (linW w (spreadWeight w k) ⬝ᵥ y) ^ 2 := by
  rw [show statB w (cellsOf μ y) = Stat.B.eval w (cellsOf μ y) from rfl, Stat.eval_eq]
  simp only [Stat.coef, Stat.left, Stat.right, dotProduct_cellsOf, sum_meanComb w hW,
    sum_spreadWeight w hW', pullCoef_meanComb_shares w hW]
  refine sum_congr rfl fun k _ => ?_
  simp only [linW]; ring

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Positive volumes give a positive region volume. -/
lemma sum_pos_of_pos [Nonempty T] (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t) (i : J) :
    0 < ∑ t, w i t := sum_pos (fun t _ => hw i t) univ_nonempty

/-- `cov(Σβᵢx̄ᵢ, Σγᵢx̄ᵢ) = Σᵢ βᵢγᵢ(τ² + σ²/Wᵢ)`. -/
lemma linW_cov_linW [Nonempty T] (τ2 σsq : ℝ) (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (β γ : J → ℝ) :
    linW w β ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w γ)
      = ∑ i, β i * γ i * (τ2 + σsq / ∑ t, w i t) := by
  have hW : ∀ i, ∑ t, w i t ≠ 0 := fun i => (sum_pos_of_pos w hw i).ne'
  have hw0 : ∀ i t, w i t ≠ 0 := fun i t => (hw i t).ne'
  rw [dotProduct_diagonal_primVarW]
  simp only [linW, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ t, σsq / w i t * (β i * shares w i t * (γ i * shares w i t))
      = β i * γ i * (σsq / ∑ s, w i s) * shares w i t := fun t => by
    rw [show σsq / w i t * (β i * shares w i t * (γ i * shares w i t))
      = β i * γ i * σsq * shares w i t * (shares w i t / w i t) by ring, shares_div w hw0]
    ring
  simp only [e, ← mul_sum, sum_shares w hW]
  ring

/-- Region means and residuals are uncorrelated, for any volumes. -/
lemma linW_cov_res [Nonempty T] (τ2 σsq : ℝ) (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (β : J → ℝ) (k : J × T) :
    linW w β ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ pullCoef (resCoef (shares w) k.1 k.2)) = 0 := by
  have hW : ∀ i, ∑ t, w i t ≠ 0 := fun i => (sum_pos_of_pos w hw i).ne'
  have hw0 : ∀ i t, w i t ≠ 0 := fun i t => (hw i t).ne'
  have h0 : ∀ i, pullCoef (resCoef (shares w) k.1 k.2) (Sum.inl i) = 0 := fun i =>
    sum_resCoef_region _ (sum_shares w hW) k.1 i k.2
  rw [dotProduct_diagonal_primVarW]
  simp only [h0, mul_zero, sum_const_zero, zero_add]
  simp only [pullCoef, Sum.elim_inr, Fintype.sum_prod_type, linW, resCoef]
  refine sum_eq_zero fun i _ => ?_
  split_ifs with h
  · subst h
    have e : ∀ t, σsq / w k.1 t * (β k.1 * shares w k.1 t
        * ((if k.2 = t then 1 else 0) - shares w k.1 t))
        = β k.1 * (σsq / ∑ s, w k.1 s) * ((if k.2 = t then 1 else 0) - shares w k.1 t) := fun t => by
      rw [show σsq / w k.1 t * (β k.1 * shares w k.1 t
        * ((if k.2 = t then 1 else 0) - shares w k.1 t))
        = β k.1 * σsq * (shares w k.1 t / w k.1 t) * ((if k.2 = t then 1 else 0) - shares w k.1 t)
          by ring, shares_div w hw0]
      ring
    simp only [e, ← mul_sum, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true,
      sum_shares w hW, sub_self, mul_zero]
  · simp

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- Swap the statistic's sum and the diagonal cumulant sum. -/
lemma sum_mul_sum_diag {ι K : Type*} [Fintype ι] [Fintype K] (c : K → ℝ) (u : K → ι → ℝ)
    (a b kd : ι → ℝ) :
    ∑ k, c k * ∑ p, a p * b p * u k p ^ 2 * kd p = ∑ p, a p * b p * kd p * ∑ k, c k * u k p ^ 2 := by
  simp only [mul_sum]; rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- `cov(A, y·X) = cov(α·x̄, y·X) - τ² y_{Lⱼ}`. -/
lemma errW_cov (τ2 σsq : ℝ) (w : J → T → ℝ) (α : J → ℝ) (j : J) (y : J ⊕ (J × T) → ℝ) :
    errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ y)
      = linW w α ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ y) - τ2 * y (Sum.inl j) := by
  rw [errW, sub_dotProduct, single_dotProduct, mulVec_diagonal]
  simp [primVarW]

/-- The residual weights of `P` on a noise cell: `Σₖ cₖ rₖ(c)² = w_c(1 - a_c)/(J(T - 1))`. -/
lemma sum_resCoef_sq_w [Nonempty T] (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t) (c : J × T) :
    ∑ k : J × T, w k.1 k.2 / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
        * resCoef (shares w) k.1 k.2 c ^ 2
      = w c.1 c.2 * (1 - shares w c.1 c.2) / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) := by
  have hW := (sum_pos_of_pos w hw c.1).ne'
  have hs : shares w c.1 c.2 * ∑ s, w c.1 s = w c.1 c.2 := by
    simp only [shares]; field_simp
  simp only [resCoef, Fintype.sum_prod_type, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_ite, mul_zero, sum_ite_irrel, sum_const_zero, sum_ite_eq,
    mem_univ, ite_true]
  have e : ∀ t, w c.1 t / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
      * ((if t = c.2 then 1 else 0) - shares w c.1 c.2) ^ 2
      = ((if t = c.2 then w c.1 t else 0) * (1 - 2 * shares w c.1 c.2)
        + shares w c.1 c.2 ^ 2 * w c.1 t) / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) :=
    fun t => by split_ifs <;> ring
  simp only [e, ← sum_div, sum_add_distrib, ← sum_mul, ← mul_sum, sum_ite_eq', mem_univ, ite_true]
  congr 1
  linear_combination (shares w c.1 c.2) * hs

omit [DecidableEq T] in
/-- The spread weights of `B` on a level: `Σₖ Wₖ βₖᵢ² = Wᵢ(1 - Wᵢ/W)`. -/
lemma sum_spreadWeight_sq (w : J → T → ℝ) (hW : ∑ i, ∑ t, w i t ≠ 0) (i : J) :
    ∑ k, (∑ t, w k t) * spreadWeight w k i ^ 2
      = (∑ t, w i t) * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t) := by
  simp only [spreadWeight, sub_sq, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, mul_add,
    mul_sub, sum_add_distrib, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, ← sum_mul]
  field_simp
  ring

/-- Bühlmann–Straub's factors as functions of `k = σ²/τ²`: `zᵢ = Wᵢ/(Wᵢ + k)`. -/
noncomputable def bsZk (W : J → ℝ) (k : ℝ) (i : J) : ℝ := W i / (W i + k)

/-- Bühlmann–Straub's prediction weights for region `j` on the region means:
`αᵢ = zⱼδᵢⱼ + (1 - zⱼ)zᵢ/Z`, `Z = Σzᵢ`. -/
noncomputable def bsAlpha (W : J → ℝ) (k : ℝ) (j i : J) : ℝ :=
  bsZk W k j * (if i = j then 1 else 0) + (1 - bsZk W k j) * (bsZk W k i / ∑ l, bsZk W k l)

/-- Their derivative in `log k` (`bsAlpha_hasDerivAt`):
`λᵢ = -(zⱼ(1 - zⱼ)(δᵢⱼ - bᵢ) + (1 - zⱼ)(zᵢ(1 - zᵢ) - S bᵢ)/Z)`, `b = z/Z`, `S = Σ z(1 - z)`. -/
noncomputable def bsLambda (W : J → ℝ) (k : ℝ) (j i : J) : ℝ :=
  -(bsZk W k j * (1 - bsZk W k j) * ((if i = j then 1 else 0) - bsZk W k i / ∑ l, bsZk W k l)
    + (1 - bsZk W k j) / (∑ l, bsZk W k l) * (bsZk W k i * (1 - bsZk W k i)
      - (∑ l, bsZk W k l * (1 - bsZk W k l)) * (bsZk W k i / ∑ l, bsZk W k l)))

/-- The first-order direction of the fitted `k̂ = σ̂²/τ̂²`: `ε̂ = σ̂²/σ² - τ̂²/τ²` (`≈ log(k̂/k)`),
with `σ̂² = P`, `τ̂² = bsTau2Hat`. Zero mean when both estimators are unbiased. -/
noncomputable def bsEps (w : J → T → ℝ) (τ2 σsq P B : ℝ) : ℝ := P / σsq - bsTau2Hat w P B / τ2

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- The factors are positive. -/
lemma bsZk_pos (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (i : J) : 0 < bsZk W k i :=
  div_pos (hW i) (by linarith [hW i])

omit [Fintype T] [DecidableEq T] in
/-- The prediction weights sum to one. -/
lemma sum_bsAlpha [Nonempty J] (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (j : J) :
    ∑ i, bsAlpha W k j i = 1 := by
  have hZ : ∑ l, bsZk W k l ≠ 0 :=
    (sum_pos (fun i _ => bsZk_pos W hW k hk i) univ_nonempty).ne'
  simp only [bsAlpha, sum_add_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
    ite_true, ← mul_sum, ← sum_div, div_self hZ]
  ring

omit [Fintype T] [DecidableEq T] in
/-- Their derivative sums to zero. -/
lemma sum_bsLambda [Nonempty J] (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (j : J) :
    ∑ i, bsLambda W k j i = 0 := by
  have hZ : ∑ l, bsZk W k l ≠ 0 :=
    (sum_pos (fun i _ => bsZk_pos W hW k hk i) univ_nonempty).ne'
  simp only [bsLambda, sum_neg_distrib, sum_add_distrib, ← mul_sum, sum_sub_distrib,
    sum_ite_eq', mem_univ, ite_true, ← sum_div, div_self hZ]
  field_simp
  ring

omit [Fintype T] [DecidableEq T] in
/-- At the true `k = σ²/τ²`, `zᵢ(τ² + σ²/Wᵢ) = τ²`, so `αᵢ(τ² + σ²/Wᵢ) - τ²δᵢⱼ = (1 - zⱼ)τ²/Z` for
every `i`: the error has the same covariance with every region mean. -/
lemma bsAlpha_mul_var (W : J → ℝ) (hW : ∀ i, 0 < W i) (τ2 σsq : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq)
    (j i : J) :
    bsAlpha W (σsq / τ2) j i * (τ2 + σsq / W i) - τ2 * (if i = j then 1 else 0)
      = (1 - bsZk W (σsq / τ2) j) * τ2 / ∑ l, bsZk W (σsq / τ2) l := by
  have hk : 0 < σsq / τ2 := div_pos hσ hτ
  have hz : ∀ i, bsZk W (σsq / τ2) i * (τ2 + σsq / W i) = τ2 := fun i => by
    have := hW i; simp only [bsZk]; field_simp
  have : Nonempty J := ⟨j⟩
  have hZ : ∑ l, bsZk W (σsq / τ2) l ≠ 0 :=
    (sum_pos (fun i _ => bsZk_pos W hW _ hk i) univ_nonempty).ne'
  simp only [bsAlpha]
  have := hz i
  split_ifs with h
  · subst h
    have := hz i
    field_simp
    linear_combination (∑ l, bsZk W (σsq / τ2) l) * this
      + (1 - bsZk W (σsq / τ2) i) * this
  · field_simp
    linear_combination (1 - bsZk W (σsq / τ2) j) * this

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- `dzᵢ/dk = -zᵢ(1 - zᵢ)/k`. -/
lemma bsZk_hasDerivAt (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (i : J) :
    HasDerivAt (fun k => bsZk W k i) (-(bsZk W k i * (1 - bsZk W k i)) / k) k := by
  have hne : W i + k ≠ 0 := by linarith [hW i]
  have := (hasDerivAt_const k (W i)).div ((hasDerivAt_id k).const_add (W i)) hne
  convert this using 1
  · funext x; simp only [bsZk, Pi.div_apply, id]
  · simp only [bsZk, id]; field_simp; ring

omit [Fintype T] [DecidableEq T] in
/-- **`λ` is the derivative of Bühlmann–Straub's weights in `log k`**: `dαᵢ/dk = λᵢ/k`. So with
`k̂ = σ̂²/τ̂²`, the fit's weights are `α + (log k̂ - log k) λ` to first order, and
`log k̂ - log k = ε̂ = σ̂²/σ² - τ̂²/τ²` to first order (`bsEps`). -/
theorem bsAlpha_hasDerivAt [Nonempty J] (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k)
    (j i : J) :
    HasDerivAt (fun k => bsAlpha W k j i) (bsLambda W k j i / k) k := by
  have hz := bsZk_hasDerivAt W hW k hk
  have hZ := HasDerivAt.sum (u := univ) fun l _ => hz l
  rw [Finset.sum_fn] at hZ
  have hZne : ∑ l, bsZk W k l ≠ 0 := (sum_pos (fun l _ => bsZk_pos W hW k hk l) univ_nonempty).ne'
  have hZne' : (fun k => ∑ l, bsZk W k l) k ≠ 0 := hZne
  have := ((hz j).mul_const (if i = j then (1 : ℝ) else 0)).add
    (((hasDerivAt_const k (1 : ℝ)).sub (hz j)).mul ((hz i).div hZ hZne'))
  convert this using 1
  · funext k'; simp only [bsAlpha, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
  · simp only [bsLambda, Pi.div_apply, Pi.sub_apply, neg_div, sum_neg_distrib, ← sum_div]
    have hk0 := hk.ne'
    split_ifs <;> field_simp <;> ring

/-- **At the true `z` the error is uncorrelated with every contrast** `Σγᵢx̄ᵢ` (`Σγ = 0`), any
volumes: `errW α j` against `linW γ` vanishes for Bühlmann–Straub's weights `α` (`bsAlpha_mul_var`). -/
lemma bsAlpha_errW_cov [Nonempty T] (τ2 σsq : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq) (w : J → T → ℝ)
    (hw : ∀ i t, 0 < w i t) (j : J) (γ : J → ℝ) (hγ : ∑ i, γ i = 0) :
    errW w (bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j) j
      ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w γ) = 0 := by
  have hWp : ∀ i, 0 < ∑ t, w i t := sum_pos_of_pos w hw
  set W : J → ℝ := fun i => ∑ t, w i t with hWdef
  set α := bsAlpha W (σsq / τ2) j
  rw [errW_cov, linW_cov_linW τ2 σsq w hw]
  have e : ∑ i, α i * γ i * (τ2 + σsq / ∑ t, w i t) - τ2 * linW w γ (Sum.inl j)
      = ∑ i, γ i * (α i * (τ2 + σsq / W i) - τ2 * (if i = j then 1 else 0)) := by
    simp only [linW, Sum.elim_inl, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true, hWdef]
    congr 1
    · exact sum_congr rfl fun i _ => by ring
    · ring
  rw [e]
  simp only [α, bsAlpha_mul_var W hWp τ2 σsq hτ hσ j, ← sum_mul, hγ, zero_mul]

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The error and a spread against `P`, any volumes**: only the noise kurtosis enters,
`E[A(λ·x̄)P] = κN/(J(T - 1)) Σᵢ αᵢλᵢ(1 - hᵢ)/Wᵢ`, `hᵢ = Σₜ aᵢₜ²`, when `A` and `λ·x̄` are
uncorrelated. -/
theorem integral_errW_linW_statP [Nonempty T] (X : J ⊕ (J × T) → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (τ2 σsq κL κN μ : ℝ) (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4W κL κN w p q r s
        + diagonal (primVarW τ2 σsq w) p q * diagonal (primVarW τ2 σsq w) r s
        + diagonal (primVarW τ2 σsq w) p r * diagonal (primVarW τ2 σsq w) q s
        + diagonal (primVarW τ2 σsq w) p s * diagonal (primVarW τ2 σsq w) q r)
    (α β : J → ℝ) (j : J)
    (h0 : errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w β) = 0) :
    ∫ ω, (errW w α j ⬝ᵥ fun p => X p ω) * (linW w β ⬝ᵥ fun p => X p ω)
        * statP w (cellsOf μ fun p => X p ω) ∂P
      = κN / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
        * ∑ i, α i * β i * (1 - ∑ t, shares w i t ^ 2) / ∑ t, w i t := by
  have hW : ∀ i, ∑ t, w i t ≠ 0 := fun i => (sum_pos_of_pos w hw i).ne'
  have hw0 : ∀ i t, w i t ≠ 0 := fun i t => (hw i t).ne'
  have hinl : ∀ (k : J × T) i, pullCoef (resCoef (shares w) k.1 k.2) (Sum.inl i) = 0 :=
    fun k i => sum_resCoef_region _ (sum_shares w hW) k.1 i k.2
  have hres : ∀ k : J × T, errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w)
      *ᵥ pullCoef (resCoef (shares w) k.1 k.2)) = 0 := fun k => by
    rw [errW_cov, linW_cov_res τ2 σsq w hw, hinl]; ring
  simp_rw [statP_cellsOfW w hW μ]
  rw [integral_lin_lin_sumSq X hX _ _ h4]
  simp only [h0, hres, zero_mul, mul_zero, add_zero, zero_add, primK4W, sum_diagK4]
  rw [sum_mul_sum_diag]
  simp only [Fintype.sum_sum_type, hinl, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sum_const_zero, zero_add]
  simp only [errW, linW, Pi.sub_apply, Sum.elim_inr, pullCoef, Pi.single_apply, reduceCtorEq,
    ite_false, sub_zero]
  simp only [sum_resCoef_sq_w w hw, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ t, α i * shares w i t * (β i * shares w i t) * (κN / w i t ^ 2)
      * (w i t * (1 - shares w i t) / (Fintype.card J * ((Fintype.card T : ℝ) - 1)))
      = κN / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) * (α i * β i
        * (shares w i t - shares w i t ^ 2) / ∑ s, w i s) := fun t => by
    have := shares_div w hw0 i t
    have hwt := hw0 i t
    rw [div_eq_iff hwt] at this
    rw [show α i * shares w i t * (β i * shares w i t) * (κN / w i t ^ 2)
      * (w i t * (1 - shares w i t) / (Fintype.card J * ((Fintype.card T : ℝ) - 1)))
      = κN / (Fintype.card J * ((Fintype.card T : ℝ) - 1)) * (α i * β i
        * (shares w i t * (shares w i t / w i t)) * (1 - shares w i t)) by field_simp,
      shares_div w hw0]
    ring
  simp only [e, ← mul_sum]
  congr 1
  simp only [← sum_div, ← mul_sum, sum_sub_distrib, sum_shares w hW]

/-- **The error and a spread against `B`, any volumes**:
`E[A(λ·x̄)B] = Σᵢ λᵢ(1 - Wᵢ/W)(κL Wᵢ(αᵢ - δᵢⱼ) + κN hᵢαᵢ/Wᵢ)`, `hᵢ = Σₜ aᵢₜ²`, when `A` is
uncorrelated with `λ·x̄` and with every spread `x̄ₖ - x̄`. -/
theorem integral_errW_linW_statB [Nonempty T] (X : J ⊕ (J × T) → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (τ2 σsq κL κN μ : ℝ) (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4W κL κN w p q r s
        + diagonal (primVarW τ2 σsq w) p q * diagonal (primVarW τ2 σsq w) r s
        + diagonal (primVarW τ2 σsq w) p r * diagonal (primVarW τ2 σsq w) q s
        + diagonal (primVarW τ2 σsq w) p s * diagonal (primVarW τ2 σsq w) q r)
    (α β : J → ℝ) (j : J)
    (h0 : errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w β) = 0)
    (hB0 : ∀ k, errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w (spreadWeight w k)) = 0) :
    ∫ ω, (errW w α j ⬝ᵥ fun p => X p ω) * (linW w β ⬝ᵥ fun p => X p ω)
        * statB w (cellsOf μ fun p => X p ω) ∂P
      = ∑ i, β i * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t)
          * (κL * (∑ t, w i t) * (α i - if i = j then 1 else 0)
            + κN * (∑ t, shares w i t ^ 2) * α i / ∑ t, w i t) := by
  have hW : ∀ i, ∑ t, w i t ≠ 0 := fun i => (sum_pos_of_pos w hw i).ne'
  have hw0 : ∀ i t, w i t ≠ 0 := fun i t => (hw i t).ne'
  have : Nonempty J := ⟨j⟩
  have hW' : ∑ i, ∑ t, w i t ≠ 0 :=
    (sum_pos (fun i _ => sum_pos_of_pos w hw i) univ_nonempty).ne'
  simp_rw [statB_cellsOfW w hW hW' μ]
  rw [integral_lin_lin_sumSq X hX _ _ h4]
  simp only [h0, hB0, zero_mul, mul_zero, add_zero, zero_add, primK4W, sum_diagK4]
  rw [sum_mul_sum_diag]
  simp only [Fintype.sum_sum_type, errW, linW, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false, sub_zero, mul_pow]
  simp only [← mul_assoc _ _ (shares w _ _ ^ 2)]
  simp only [← sum_mul, sum_spreadWeight_sq w hW', Fintype.sum_prod_type, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ t, α i * shares w i t * (β i * shares w i t) * (κN / w i t ^ 2)
      * ((∑ t, w i t) * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t) * shares w i t ^ 2)
      = β i * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t) * (κN * shares w i t ^ 2 * α i / ∑ t, w i t)
      := fun t => by
    have := shares_div w hw0 i t
    rw [show α i * shares w i t * (β i * shares w i t) * (κN / w i t ^ 2)
      * ((∑ t, w i t) * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t) * shares w i t ^ 2)
      = β i * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t) * (κN * α i * shares w i t ^ 2
        * (shares w i t / w i t) ^ 2 * (∑ t, w i t)) by field_simp, this]
    field_simp
  simp only [e, ← mul_sum, ← sum_div, ← sum_mul]
  ring

/-- **The first-order cross term of the Bühlmann–Straub plug-in, any volumes** (`PlugIn.lean`'s
`2E[AB]`). Cells `xⱼₜ = μ + Lⱼ + eⱼₜ` from primitives `X = (L, e)` with second moments
`diag(τ², σ²/wᵢₜ)` and fourth moments `primK4W κL κN w` plus the pairings (uncorrelated levels and
noise; no other distributional assumption). BS's weights depend on `(σ̂², τ̂²)` only through
`k = σ²/τ²`, so at first order `B = ε̂ (λ·x̄)` with `ε̂ = σ̂²/σ² - τ̂²/τ²` (`bsEps`) and `λ` the
derivative of the weights `α` in `log k` (`bsLambda`, `bsAlpha_hasDerivAt`). With `A = α·x̄ - (μ + Lⱼ)`,
`Wᵢ = Σₜwᵢₜ`, `hᵢ = Σₜaᵢₜ²`, `c = W - ΣWᵢ²/W`:
`2E[A ε̂ (λ·x̄)] = 2((1/σ² + (J - 1)/(cτ²)) T_P - T_B/(cτ²))`,
`T_P = κN/(J(T - 1)) Σᵢ αᵢλᵢ(1 - hᵢ)/Wᵢ`, `T_B = Σᵢ λᵢ(1 - Wᵢ/W)(κL Wᵢ(αᵢ - δᵢⱼ) + κN hᵢαᵢ/Wᵢ)`.
Only fourth cumulants enter. -/
theorem crossTerm_bs_of_cumulants [Nonempty T] (X : J ⊕ (J × T) → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (τ2 σsq κL κN μ : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq)
    (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4W κL κN w p q r s
        + diagonal (primVarW τ2 σsq w) p q * diagonal (primVarW τ2 σsq w) r s
        + diagonal (primVarW τ2 σsq w) p r * diagonal (primVarW τ2 σsq w) q s
        + diagonal (primVarW τ2 σsq w) p s * diagonal (primVarW τ2 σsq w) q r) (j : J) :
    2 * ∫ ω, (∑ i, bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
            * regionMean w (cellsOf μ fun p => X p ω) i - (μ + X (Sum.inl j) ω))
        * (∑ i, bsLambda (fun i => ∑ t, w i t) (σsq / τ2) j i
            * regionMean w (cellsOf μ fun p => X p ω) i)
        * bsEps w τ2 σsq (statP w (cellsOf μ fun p => X p ω))
            (statB w (cellsOf μ fun p => X p ω)) ∂P
      = 2 * ((1 / σsq + ((Fintype.card J : ℝ) - 1)
            / ((∑ i, ∑ t, w i t - (∑ i, (∑ t, w i t) ^ 2) / ∑ i, ∑ t, w i t) * τ2))
          * (κN / (Fintype.card J * ((Fintype.card T : ℝ) - 1))
            * ∑ i, bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
              * bsLambda (fun i => ∑ t, w i t) (σsq / τ2) j i
              * (1 - ∑ t, shares w i t ^ 2) / ∑ t, w i t)
        - 1 / ((∑ i, ∑ t, w i t - (∑ i, (∑ t, w i t) ^ 2) / ∑ i, ∑ t, w i t) * τ2)
          * ∑ i, bsLambda (fun i => ∑ t, w i t) (σsq / τ2) j i
            * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t)
            * (κL * (∑ t, w i t) * (bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
                - if i = j then 1 else 0)
              + κN * (∑ t, shares w i t ^ 2) * bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
                / ∑ t, w i t)) := by
  have : Nonempty J := ⟨j⟩
  have hWp : ∀ i, 0 < ∑ t, w i t := sum_pos_of_pos w hw
  have hW : ∀ i, ∑ t, w i t ≠ 0 := fun i => (hWp i).ne'
  have hk : 0 < σsq / τ2 := div_pos hσ hτ
  set W : J → ℝ := fun i => ∑ t, w i t with hWdef
  set α := bsAlpha W (σsq / τ2) j
  set β := bsLambda W (σsq / τ2) j
  have hα : ∑ i, α i = 1 := sum_bsAlpha W hWp _ hk j
  have hβ : ∑ i, β i = 0 := sum_bsLambda W hWp _ hk j
  have hcov := bsAlpha_errW_cov τ2 σsq hτ hσ w hw j
  have h0 := hcov β hβ
  have hB0 : ∀ k, errW w α j ⬝ᵥ (diagonal (primVarW τ2 σsq w) *ᵥ linW w (spreadWeight w k)) = 0 :=
    fun k => hcov _ (sum_spreadWeight w (sum_pos (fun i _ => hWp i) univ_nonempty).ne' k)
  set F : Ω → ℝ := fun ω => (errW w α j ⬝ᵥ fun p => X p ω) * (linW w β ⬝ᵥ fun p => X p ω)
  set cc : ℝ := ∑ i, ∑ t, w i t - (∑ i, (∑ t, w i t) ^ 2) / ∑ i, ∑ t, w i t
  have hpt : ∀ ω, (∑ i, α i * regionMean w (cellsOf μ fun p => X p ω) i - (μ + X (Sum.inl j) ω))
        * (∑ i, β i * regionMean w (cellsOf μ fun p => X p ω) i)
        * bsEps w τ2 σsq (statP w (cellsOf μ fun p => X p ω)) (statB w (cellsOf μ fun p => X p ω))
      = (1 / σsq + ((Fintype.card J : ℝ) - 1) / (cc * τ2))
          * (F ω * statP w (cellsOf μ fun p => X p ω))
        - 1 / (cc * τ2) * (F ω * statB w (cellsOf μ fun p => X p ω)) := fun ω => by
    rw [errW_dotProduct w hW α hα, sum_mul_regionMean_cellsOf w hW, hβ]
    have ht : ∀ P' B', bsTau2Hat w P' B' = (B' - ((Fintype.card J : ℝ) - 1) * P') / cc :=
      fun _ _ => rfl
    simp only [F, bsEps, ht]
    ring_nf
  simp_rw [hpt]
  have iP : Integrable (fun ω => F ω * statP w (cellsOf μ fun p => X p ω)) P := by
    simp only [F]; simp_rw [statP_cellsOfW w hW μ]; exact integrable_lin_lin_sumSq X hX _ _ _ _
  have iB : Integrable (fun ω => F ω * statB w (cellsOf μ fun p => X p ω)) P := by
    simp only [F]
    simp_rw [statB_cellsOfW w hW (sum_pos (fun i _ => hWp i) univ_nonempty).ne' μ]
    exact integrable_lin_lin_sumSq X hX _ _ _ _
  rw [integral_sub (iP.const_mul _) (iB.const_mul _), integral_const_mul, integral_const_mul]
  simp only [F]
  rw [integral_errW_linW_statP X hX τ2 σsq κL κN μ w hw h4 α β j h0,
    integral_errW_linW_statB X hX τ2 σsq κL κN μ w hw h4 α β j h0 hB0]

end Integrals

end CrossGeneral

section CrossBalanced

universe uZ
variable {J T : Type uZ} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [Fintype T] [DecidableEq T] in
/-- With equal volumes Bühlmann–Straub's weights are the plain blend: `αᵢ = zδᵢⱼ + (1 - z)/J`. -/
lemma bsAlpha_const [Nonempty J] (W0 k : ℝ) (hW : 0 < W0) (hk : 0 < k) (j i : J) :
    bsAlpha (fun _ : J => W0) k j i
      = W0 / (W0 + k) * (if i = j then 1 else 0) + (1 - W0 / (W0 + k)) / Fintype.card J := by
  have hJ : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hz : W0 / (W0 + k) ≠ 0 := (div_pos hW (by linarith)).ne'
  simp only [bsAlpha, bsZk, sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Fintype T] [DecidableEq T] in
/-- …and their direction is the spread: `λᵢ = -z(1 - z)(δᵢⱼ - 1/J)`. -/
lemma bsLambda_const [Nonempty J] (W0 k : ℝ) (hW : 0 < W0) (hk : 0 < k) (j i : J) :
    bsLambda (fun _ : J => W0) k j i
      = -(W0 / (W0 + k) * (1 - W0 / (W0 + k)) * ((if i = j then 1 else 0) - 1 / Fintype.card J)) := by
  have hJ : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hz : W0 / (W0 + k) ≠ 0 := (div_pos hW (by linarith)).ne'
  simp only [bsLambda, bsZk, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

set_option linter.unusedSectionVars false in
/-- **The first-order cross term of the Bühlmann–Straub plug-in** (`PlugIn.lean`'s `2E[AB]`), in the
balanced world with fourth cumulants and `D = σ²/(wT)` estimated. Cells `xⱼₜ = μ + Lⱼ + eⱼₜ` from
primitives `X = (L, e)` with second moments `diag(τ², σ²/w)` and fourth moments `primK4 κL κN w`
plus the pairings (uncorrelated levels and noise, no other distributional assumption).
With `A = z x̄ⱼ + (1 - z)x̄ - (μ + Lⱼ)` and `B ≈ (ẑ - z)(x̄ⱼ - x̄)`, `ẑ - z` linearized at `(v, s)`
(`zHatLin`), relative to `(1 - z)τ²`:
`2E[AB] = -2(1 - 1/J) z(1 - z)(γL + γN/T)/J`, `γL = κL/τ⁴`, `γN = κN/σ⁴`.
The level part is Chen–Lahiri–Rao's; the noise part has the opposite sign of theirs, because
`D` is estimated (Finding 38). The equal-volumes case of `crossTerm_bs_of_cumulants`. -/
theorem crossTerm_of_balanced_cumulants [Nonempty J] (X : J ⊕ (J × T) → Ω → ℝ)
    (τ2 σsq w μ κL κN : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : 0 < w)
    (hJ : 2 ≤ Fintype.card J) (hT : 2 ≤ Fintype.card T) (hX : ∀ p, MemLp (X p) 4 P)
    (_h2 : ∀ p q, ∫ ω, X p ω * X q ω ∂P = diagonal (primVar τ2 σsq w) p q)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4 κL κN w p q r s
        + diagonal (primVar τ2 σsq w) p q * diagonal (primVar τ2 σsq w) r s
        + diagonal (primVar τ2 σsq w) p r * diagonal (primVar τ2 σsq w) q s
        + diagonal (primVar τ2 σsq w) p s * diagonal (primVar τ2 σsq w) q r) (j : J) :
    2 * (∫ ω, (τ2 / (τ2 + σsq / (w * Fintype.card T))
          * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        + (1 - τ2 / (τ2 + σsq / (w * Fintype.card T)))
          * (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J
        - (μ + X (Sum.inl j) ω))
      * (regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        - (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J)
      * zHatLin (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (statP (fun _ _ => w) (cellsOf μ fun p => X p ω) / (Fintype.card T * w))
          (statB (fun _ _ => w) (cellsOf μ fun p => X p ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) ∂P)
        / ((1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) * τ2)
      = -2 * (1 - 1 / (Fintype.card J : ℝ)) * (τ2 / (τ2 + σsq / (w * Fintype.card T)))
          * (1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) / Fintype.card J
        * (κL / τ2 ^ 2 + κN / σsq ^ 2 / Fintype.card T) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hn2 : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hJ1 : (Fintype.card J : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by linarith
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by linarith
  have hw0 : w ≠ 0 := hw.ne'
  have hσ0 : σsq ≠ 0 := hσ.ne'
  have hτ0 : τ2 ≠ 0 := hτ.ne'
  have hs0 : τ2 + σsq / (w * Fintype.card T) ≠ 0 := by positivity
  have hk : 0 < σsq / τ2 := div_pos hσ hτ
  have hW0 : 0 < (Fintype.card T : ℝ) * w := by positivity
  have hWfun : (fun i : J => ∑ t, (fun (_ : J) (_ : T) => w) i t)
      = fun _ => (Fintype.card T : ℝ) * w := by
    funext i; simp only [sum_const, card_univ, nsmul_eq_mul]
  set z := τ2 / (τ2 + σsq / (w * Fintype.card T)) with hzdef
  have hzW : (Fintype.card T : ℝ) * w / ((Fintype.card T : ℝ) * w + σsq / τ2) = z := by
    rw [hzdef]; field_simp
  have hV : primVarW τ2 σsq (fun (_ : J) (_ : T) => w) = primVar τ2 σsq w := by
    funext p; cases p <;> rfl
  have hK : primK4W κL κN (fun (_ : J) (_ : T) => w) = primK4 κL κN w := rfl
  have G := crossTerm_bs_of_cumulants X hX τ2 σsq κL κN μ hτ hσ (fun _ _ => w) (fun _ _ => hw)
    (by rw [hV, hK]; exact h4) j
  rw [hWfun] at G
  simp only [bsAlpha_const _ _ hW0 hk, bsLambda_const _ _ hW0 hk, hzW] at G
  have hA : ∀ x : J → ℝ, ∑ i, ((z * if i = j then 1 else 0) + (1 - z) / Fintype.card J) * x i
      = z * x j + (1 - z) * (∑ i, x i) / Fintype.card J := fun x => by
    have e : ∀ i, ((z * if i = j then 1 else 0) + (1 - z) / Fintype.card J) * x i
        = (if i = j then z * x i else 0) + (1 - z) / Fintype.card J * x i := fun i => by
      split_ifs <;> ring
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq', ← mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  have hL : ∀ x : J → ℝ, ∑ i, -(z * (1 - z) * ((if i = j then 1 else 0) - 1 / Fintype.card J)) * x i
      = -(z * (1 - z)) * (x j - (∑ i, x i) / Fintype.card J) := fun x => by
    have e : ∀ i, -(z * (1 - z) * ((if i = j then 1 else 0) - 1 / Fintype.card J)) * x i
        = -(z * (1 - z)) * ((if i = j then x i else 0) - x i / Fintype.card J) := fun i => by
      split_ifs <;> ring
    rw [sum_congr rfl fun i _ => e i, ← mul_sum, sum_sub_distrib, sum_ite_eq', ← sum_div]
    simp only [mem_univ, ↓reduceIte]
  have hε : ∀ P' B' : ℝ, zHatLin (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
        (P' / (Fintype.card T * w)) (B' / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w)))
      = -(z * (1 - z)) * bsEps (J := J) (T := T) (fun _ _ => w) τ2 σsq P' B' := fun P' B' => by
    simp only [zHatLin, bsEps, bsTau2Hat, sum_const, card_univ, nsmul_eq_mul, hzdef]
    field_simp
    ring
  have hpt : ∀ ω, (z * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        + (1 - z) * (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J
        - (μ + X (Sum.inl j) ω))
      * (regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        - (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J)
      * zHatLin (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (statP (fun _ _ => w) (cellsOf μ fun p => X p ω) / (Fintype.card T * w))
          (statB (fun _ _ => w) (cellsOf μ fun p => X p ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w)))
      = ((∑ x, ((z * if x = j then 1 else 0) + (1 - z) / Fintype.card J)
            * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) x - (μ + X (Sum.inl j) ω))
          * ∑ x, -(z * (1 - z) * ((if x = j then 1 else 0) - 1 / Fintype.card J))
            * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) x)
        * bsEps (fun _ _ => w) τ2 σsq (statP (fun _ _ => w) (cellsOf μ fun p => X p ω))
            (statB (fun _ _ => w) (cellsOf μ fun p => X p ω)) := fun ω => by
    rw [hA, hL, hε]; ring
  simp_rw [hpt]
  simp only [G]
  simp only [shares_const w hw0, sum_const, card_univ, nsmul_eq_mul, div_pow, one_pow]
  have split : ∀ g : J → ℝ, ∑ x, g x = g j + ∑ x ∈ univ.erase j, g x := fun g =>
    (add_sum_erase _ _ (mem_univ j)).symm
  have hcard : ((univ.erase j).card : ℝ) = Fintype.card J - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Nat.cast_sub Fintype.card_pos]; simp
  have off : ∀ g : J → ℝ, ∀ c : ℝ, (∀ x, x ≠ j → g x = c) →
      ∑ x ∈ univ.erase j, g x = (Fintype.card J - 1) * c := fun g c hg => by
    rw [sum_congr rfl fun x hx => hg x (ne_of_mem_erase hx), sum_const, nsmul_eq_mul, hcard]
  rw [split, split, off _ _ (fun x hx => by simp only [hx, ↓reduceIte]; rfl),
    off _ _ (fun x hx => by simp only [hx, ↓reduceIte]; rfl)]
  simp only [ite_true]
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  rw [hzdef]
  field_simp
  ring_nf
  field_simp

/-- …and with the noise variance `D = σ²/(wT)` known (`v̂ = v`, Chen–Lahiri–Rao's setting). -/
theorem crossTerm_of_balanced_cumulants_known [Nonempty J] (X : J ⊕ (J × T) → Ω → ℝ)
    (τ2 σsq w μ κL κN : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq) (hw : 0 < w)
    (hJ : 2 ≤ Fintype.card J) (hT : 2 ≤ Fintype.card T) (hX : ∀ p, MemLp (X p) 4 P)
    (h2 : ∀ p q, ∫ ω, X p ω * X q ω ∂P = diagonal (primVar τ2 σsq w) p q)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4 κL κN w p q r s
        + diagonal (primVar τ2 σsq w) p q * diagonal (primVar τ2 σsq w) r s
        + diagonal (primVar τ2 σsq w) p r * diagonal (primVar τ2 σsq w) q s
        + diagonal (primVar τ2 σsq w) p s * diagonal (primVar τ2 σsq w) q r) (j : J) :
    2 * (∫ ω, (τ2 / (τ2 + σsq / (w * Fintype.card T))
          * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        + (1 - τ2 / (τ2 + σsq / (w * Fintype.card T)))
          * (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J
        - (μ + X (Sum.inl j) ω))
      * (regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        - (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J)
      * zHatLin (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (σsq / (w * Fintype.card T))
          (statB (fun _ _ => w) (cellsOf μ fun p => X p ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))) ∂P)
        / ((1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) * τ2)
      = 2 * (1 - 1 / (Fintype.card J : ℝ)) * (1 - τ2 / (τ2 + σsq / (w * Fintype.card T)))
          / Fintype.card J
        * (-(τ2 / (τ2 + σsq / (w * Fintype.card T))) * (κL / τ2 ^ 2)
          + (1 - τ2 / (τ2 + σsq / (w * Fintype.card T))) * (κN / σsq ^ 2 / Fintype.card T)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hn2 : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hJ1 : (Fintype.card J : ℝ) - 1 ≠ 0 := by linarith
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by linarith
  have hT0 : (Fintype.card T : ℝ) ≠ 0 := by linarith
  have hT1 : (Fintype.card T : ℝ) - 1 ≠ 0 := by linarith
  have hw0 : w ≠ 0 := hw.ne'
  have hσ0 : σsq ≠ 0 := hσ.ne'
  have hτ0 : τ2 ≠ 0 := hτ.ne'
  have hs0 : τ2 + σsq / (w * Fintype.card T) ≠ 0 := by positivity
  have hk : 0 < σsq / τ2 := div_pos hσ hτ
  have hW0 : 0 < (Fintype.card T : ℝ) * w := by positivity
  have hW : ∀ i, ∑ t, (fun (_ : J) (_ : T) => w) i t ≠ 0 := fun i => by
    simp only [sum_const, card_univ, nsmul_eq_mul]; positivity
  have hW' : ∑ i, ∑ t, (fun (_ : J) (_ : T) => w) i t ≠ 0 := by
    simp only [sum_const, card_univ, nsmul_eq_mul]; positivity
  have hWfun : (fun i : J => ∑ t, (fun (_ : J) (_ : T) => w) i t)
      = fun _ => (Fintype.card T : ℝ) * w := by
    funext i; simp only [sum_const, card_univ, nsmul_eq_mul]
  set z := τ2 / (τ2 + σsq / (w * Fintype.card T)) with hzdef
  have hzW : (Fintype.card T : ℝ) * w / ((Fintype.card T : ℝ) * w + σsq / τ2) = z := by
    rw [hzdef]; field_simp
  have hV : primVarW τ2 σsq (fun (_ : J) (_ : T) => w) = primVar τ2 σsq w := by
    funext p; cases p <;> rfl
  have hK : primK4W κL κN (fun (_ : J) (_ : T) => w) = primK4 κL κN w := rfl
  set α : J → ℝ := fun i => (z * if i = j then 1 else 0) + (1 - z) / Fintype.card J with hαdef
  set β : J → ℝ := fun i => (if i = j then 1 else 0) - 1 / Fintype.card J with hβdef
  have hαb : bsAlpha (fun i => ∑ t, (fun (_ : J) (_ : T) => w) i t) (σsq / τ2) j = α := by
    rw [hWfun]; funext i; rw [bsAlpha_const _ _ hW0 hk, hzW]
  have hα1 : ∑ i, α i = 1 := by
    rw [← hαb]
    exact sum_bsAlpha (J := J) _ (fun _ => by simp only [sum_const, card_univ, nsmul_eq_mul]; positivity)
      _ hk j
  have hβ0 : ∑ i, β i = 0 := by
    simp only [hβdef, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
      nsmul_eq_mul]
    field_simp; ring
  have hcov := bsAlpha_errW_cov τ2 σsq hτ hσ (fun (_ : J) (_ : T) => w) (fun _ _ => hw) j
  rw [hαb] at hcov
  have h0 := hcov β hβ0
  have hB0 := fun k => hcov _ (sum_spreadWeight _ hW' k)
  have h2' : ∀ p q, ∫ ω, X p ω * X q ω ∂P
      = diagonal (primVarW τ2 σsq (fun (_ : J) (_ : T) => w)) p q := by rw [hV]; exact h2
  have h4' := h4
  rw [← hV, ← hK] at h4'
  have hA : ∀ x : J → ℝ, z * x j + (1 - z) * (∑ i, x i) / Fintype.card J = ∑ i, α i * x i :=
    fun x => by
    have e : ∀ i, α i * x i
        = (if i = j then z * x i else 0) + (1 - z) / Fintype.card J * x i := fun i => by
      simp only [hαdef]; split_ifs <;> ring
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq', ← mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  have hD : ∀ x : J → ℝ, x j - (∑ i, x i) / Fintype.card J = ∑ i, β i * x i := fun x => by
    have e : ∀ i, β i * x i = (if i = j then x i else 0) - x i / Fintype.card J := fun i => by
      simp only [hβdef]; split_ifs <;> ring
    rw [sum_congr rfl fun i _ => e i, sum_sub_distrib, sum_ite_eq', ← sum_div]
    simp only [mem_univ, ↓reduceIte]
  set F : Ω → ℝ := fun ω => (errW (fun _ _ => w) α j ⬝ᵥ fun p => X p ω)
    * (linW (fun (_ : J) (_ : T) => w) β ⬝ᵥ fun p => X p ω)
  have hpt : ∀ ω, (z * regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        + (1 - z) * (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J
        - (μ + X (Sum.inl j) ω))
      * (regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) j
        - (∑ i, regionMean (fun _ _ => w) (cellsOf μ fun p => X p ω) i) / Fintype.card J)
      * zHatLin (σsq / (w * Fintype.card T)) (τ2 + σsq / (w * Fintype.card T))
          (σsq / (w * Fintype.card T))
          (statB (fun _ _ => w) (cellsOf μ fun p => X p ω)
            / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w)))
      = σsq / (w * Fintype.card T) / (τ2 + σsq / (w * Fintype.card T)) ^ 2
          / (((Fintype.card J : ℝ) - 1) * (Fintype.card T * w))
          * (F ω * statB (fun _ _ => w) (cellsOf μ fun p => X p ω))
        - σsq / (w * Fintype.card T) / (τ2 + σsq / (w * Fintype.card T)) * F ω := fun ω => by
    rw [hA, hD, errW_dotProduct _ hW α hα1, sum_mul_regionMean_cellsOf _ hW, hβ0]
    simp only [F, zHatLin]
    field_simp
    ring
  simp_rw [hpt]
  have iB : Integrable (fun ω => F ω * statB (fun _ _ => w) (cellsOf μ fun p => X p ω)) P := by
    simp only [F]; simp_rw [statB_cellsOfW _ hW hW' μ]; exact integrable_lin_lin_sumSq X hX _ _ _ _
  have i0 : Integrable F P := by
    simp only [F, dotProduct]
    exact integrable_sum_mul_sum _ _ _ _ _ _ fun p q => integrable_mul2 (hX p) (hX q)
  rw [integral_sub (iB.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul]
  simp only [F]
  rw [integral_errW_linW_statB X hX τ2 σsq κL κN μ _ (fun _ _ => hw) h4' α β j h0 hB0,
    integral_lin_mul_lin X hX _ h2', h0]
  simp only [shares_const w hw0, sum_const, card_univ, nsmul_eq_mul, div_pow, one_pow]
  have split : ∀ g : J → ℝ, ∑ x, g x = g j + ∑ x ∈ univ.erase j, g x := fun g =>
    (add_sum_erase _ _ (mem_univ j)).symm
  have hcard : ((univ.erase j).card : ℝ) = Fintype.card J - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Nat.cast_sub Fintype.card_pos]; simp
  have off : ∀ g : J → ℝ, ∀ c : ℝ, (∀ x, x ≠ j → g x = c) →
      ∑ x ∈ univ.erase j, g x = (Fintype.card J - 1) * c := fun g c hg => by
    rw [sum_congr rfl fun x hx => hg x (ne_of_mem_erase hx), sum_const, nsmul_eq_mul, hcard]
  rw [split, off _ _ (fun x hx => by simp only [hαdef, hβdef, hx, ↓reduceIte]; rfl)]
  simp only [hαdef, hβdef, ↓reduceIte]
  rw [hzdef]
  field_simp
  ring_nf
  field_simp

end CrossBalanced

/-! ### A counterexample to the sign of the noise part -/

/-- Volumes of the counterexample: region 0 has `(1, 8)`, region 1 has `(10, 10)`. -/
def wce : Fin 2 → Fin 2 → ℝ := ![![1, 8], ![10, 10]]

/-- The right-hand side of `crossTerm_bs_of_cumulants` at the counterexample is positive. -/
lemma crossTerm_bs_noise_pos_value :
    0 < 2 * ((1 / (20 : ℝ) + ((Fintype.card (Fin 2) : ℝ) - 1)
            / ((∑ i, ∑ t, wce i t - (∑ i, (∑ t, wce i t) ^ 2) / ∑ i, ∑ t, wce i t) * (1 : ℝ)))
          * ((1 : ℝ) / (Fintype.card (Fin 2) * ((Fintype.card (Fin 2) : ℝ) - 1))
            * ∑ i, bsAlpha (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
              * bsLambda (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
              * (1 - ∑ t, shares wce i t ^ 2) / ∑ t, wce i t)
        - 1 / ((∑ i, ∑ t, wce i t - (∑ i, (∑ t, wce i t) ^ 2) / ∑ i, ∑ t, wce i t) * (1 : ℝ))
          * ∑ i, bsLambda (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
            * (1 - (∑ t, wce i t) / ∑ l, ∑ t, wce l t)
            * ((0 : ℝ) * (∑ t, wce i t) * (bsAlpha (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
                - if i = (0 : Fin 2) then 1 else 0)
              + (1 : ℝ) * (∑ t, shares wce i t ^ 2) * bsAlpha (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
                / ∑ t, wce i t)) := by
  simp only [wce, bsAlpha, bsLambda, bsZk, shares, Fin.sum_univ_two, Fintype.card_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  norm_num

/-- **Finding 39: heavy-tailed noise can raise the plug-in's MSE.** Two regions, two years, volumes
`(1, 8)` and `(10, 10)`, `τ² = 1`, `σ² = 20` (`z = 0.31, 0.5`), normal-like levels (`κL = 0`) and noise
of fourth cumulant `1/wᵢₜ²`: for any random cells with these moments the first-order cross term of
Bühlmann–Straub's plug-in for region 0 is positive (about `+0.46(1 - z₀)τ²` per unit `γN`). Region 0
has `8/9` of its volume in one year, so its mean is nearly one cell: its noise kurtosis reaches `S²`
fully but the pooled `σ̂²` hardly, and the negative term through `σ̂²` (Finding 38) no longer wins. -/
theorem crossTerm_bs_pos_example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Fin 2 ⊕ (Fin 2 × Fin 2) → Ω → ℝ) (hX : ∀ p, MemLp (X p) 4 P) (μ : ℝ)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4W 0 1 wce p q r s
        + diagonal (primVarW 1 20 wce) p q * diagonal (primVarW 1 20 wce) r s
        + diagonal (primVarW 1 20 wce) p r * diagonal (primVarW 1 20 wce) q s
        + diagonal (primVarW 1 20 wce) p s * diagonal (primVarW 1 20 wce) q r) :
    0 < 2 * ∫ ω, (∑ i, bsAlpha (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
            * regionMean wce (cellsOf μ fun p => X p ω) i - (μ + X (Sum.inl 0) ω))
        * (∑ i, bsLambda (fun i => ∑ t, wce i t) ((20 : ℝ) / (1 : ℝ)) 0 i
            * regionMean wce (cellsOf μ fun p => X p ω) i)
        * bsEps wce (1 : ℝ) (20 : ℝ) (statP wce (cellsOf μ fun p => X p ω))
            (statB wce (cellsOf μ fun p => X p ω)) ∂P := by
  have hw : ∀ i t, 0 < wce i t := by
    intro i t; fin_cases i <;> fin_cases t <;> norm_num [wce]
  rw [crossTerm_bs_of_cumulants X hX 1 20 0 1 μ one_pos (by norm_num) wce hw h4 0]
  exact crossTerm_bs_noise_pos_value

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
