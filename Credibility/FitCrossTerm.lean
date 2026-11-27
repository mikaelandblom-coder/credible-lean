import Credibility.FitStatistics

/-!
# The cross term of the plug-in at first order

The first-order cross term `2E[AB]` of the plug-in predictor (`PlugIn.lean`), where `A` is the
error of the blend with the true factor and `B` the linearized effect of estimating it, from
moments up to order four (`Cumulants`), with the noise variance `D` estimated. Split from
`FitStatistics`, whose statistics `P` and `B` it uses. Here:

* `crossTerm_bs_of_cumulants`: for any volumes `wᵢₜ`, as finite sums over the regions, with
  `bsAlpha_hasDerivAt` (the first-order direction is the derivative of Bühlmann–Straub's
  weights); `crossTerm_bs_level_nonpos`: its level part is never positive;
* `crossTerm_of_balanced_cumulants`: its equal-volumes corollary,
  `-2(1 - 1/J)z(1 - z)(γL + γN/T)/J` relative to `(1 - z)τ²`; with `D` known
  (`crossTerm_of_balanced_cumulants_known`) the noise part changes sign (Finding 38);
* `crossTerm_bs_pos_example`: unequal volumes where the noise part is positive;
* `Core.linMse_lineWeight`, `Core.linMse_lineWeight_sub`: the mean squared error of a blend
  `z eⱼ + (1 - z) b` and the gap between two blends with the same `z`, as exact quadratics in `z`.

Nothing is assumed about the distribution beyond the moment tables.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Credibility.Cumulants

variable {ι : Type*} [Fintype ι]

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

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
/-- **Chebyshev's sum inequality, weighted**: if `a` and `z` are similarly ordered on `s` and
`z ≥ 0`, then `(Σ z)(Σ a z²) ≥ (Σ a z)(Σ z²)`. -/
lemma sum_mul_sum_sq_le_of_monovary {ι : Type*} (s : Finset ι) (a z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (ha : ∀ i ∈ s, ∀ l ∈ s, 0 ≤ (a i - a l) * (z i - z l)) :
    (∑ i ∈ s, a i * z i) * (∑ i ∈ s, z i ^ 2)
      ≤ (∑ i ∈ s, z i) * (∑ i ∈ s, a i * z i ^ 2) := by
  have key : ∑ i ∈ s, ∑ l ∈ s, z i * z l * ((a i - a l) * (z i - z l))
      = 2 * ((∑ i ∈ s, z i) * (∑ i ∈ s, a i * z i ^ 2)
        - (∑ i ∈ s, a i * z i) * (∑ i ∈ s, z i ^ 2)) := by
    have e : ∑ i ∈ s, ∑ l ∈ s, z i * z l * ((a i - a l) * (z i - z l))
        = ∑ i ∈ s, ∑ l ∈ s, (z l * (a i * z i ^ 2) - a i * z i * z l ^ 2)
          + ∑ i ∈ s, ∑ l ∈ s, (z i * (a l * z l ^ 2) - a l * z l * z i ^ 2) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun l _ => by ring
    rw [e, sum_comm (s := s) (t := s) (f := fun i l => z i * (a l * z l ^ 2) - a l * z l * z i ^ 2)]
    simp only [sum_sub_distrib, ← sum_mul, ← mul_sum]
    ring
  have : 0 ≤ ∑ i ∈ s, ∑ l ∈ s, z i * z l * ((a i - a l) * (z i - z l)) :=
    sum_nonneg fun i hi => sum_nonneg fun l hl =>
      mul_nonneg (mul_nonneg (hz i hi) (hz l hl)) (ha i hi l hl)
  linarith

omit [Fintype T] [DecidableEq T] in
/-- The exposure-spread weights `mᵢ = Wᵢ(1 - Wᵢ/W)` times the factors `zᵢ` are ordered as the
factors: `(mᵢzᵢ - mₗzₗ)(zᵢ - zₗ) ≥ 0`. -/
lemma bsZk_spread_monovary (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (i l : J) :
    0 ≤ (W i * (1 - W i / ∑ p, W p) * bsZk W k i - W l * (1 - W l / ∑ p, W p) * bsZk W k l)
      * (bsZk W k i - bsZk W k l) := by
  by_cases hil : i = l
  · subst hil; simp
  set S := ∑ p, W p
  have hS : 0 < S := sum_pos (fun p _ => hW p) ⟨i, mem_univ i⟩
  have hpair : W i + W l ≤ S := by
    rw [← sum_pair hil]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => (hW p).le
  have hi := hW i
  have hl := hW l
  have e1 : W i * (1 - W i / S) - W l * (1 - W l / S) = (W i - W l) * (S - W i - W l) / S := by
    field_simp; ring
  have e2 : bsZk W k i - bsZk W k l = k * (W i - W l) / ((W i + k) * (W l + k)) := by
    simp only [bsZk]; field_simp; ring
  have h1 : 0 ≤ (W i * (1 - W i / S) - W l * (1 - W l / S)) * (bsZk W k i - bsZk W k l) := by
    rw [e1, e2, show (W i - W l) * (S - W i - W l) / S * (k * (W i - W l) / ((W i + k) * (W l + k)))
      = (W i - W l) ^ 2 * (S - W i - W l) * k / (S * ((W i + k) * (W l + k))) by
        field_simp]
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hk.le) (by positivity)
  have hm : 0 ≤ W l * (1 - W l / S) := mul_nonneg hl.le (by
    rw [sub_nonneg, div_le_one hS]; linarith)
  have hz := bsZk_pos W hW k hk i
  rw [show (W i * (1 - W i / S) * bsZk W k i - W l * (1 - W l / S) * bsZk W k l)
      * (bsZk W k i - bsZk W k l)
      = (W i * (1 - W i / S) - W l * (1 - W l / S)) * (bsZk W k i - bsZk W k l) * bsZk W k i
        + W l * (1 - W l / S) * (bsZk W k i - bsZk W k l) ^ 2 by ring]
  exact add_nonneg (mul_nonneg h1 hz.le) (mul_nonneg hm (sq_nonneg _))

omit [Fintype T] [DecidableEq T] in
/-- **The level part of the Bühlmann–Straub cross term has a sign**:
`Σᵢ λᵢ (1 - Wᵢ/W) Wᵢ (αᵢ - δᵢⱼ) ≥ 0` for any positive volumes and `k > 0`. In `z`:
`(1 - zⱼ)²/Z³ (mⱼzⱼR(R² + s') + Σᵢ≠ⱼ mᵢzᵢ²(Zzⱼ + Zzᵢ - Σz²))`, `R = Σᵢ≠ⱼ zᵢ`, `s' = Σᵢ≠ⱼ zᵢ²`,
and the last sum is `zⱼΣᵢ≠ⱼ mᵢzᵢ²(R + zᵢ)` plus Chebyshev's `R Σ mᵢzᵢ³ - s' Σ mᵢzᵢ² ≥ 0`
(`mᵢzᵢ` increases with `zᵢ`: `bsZk_spread_monovary`). -/
theorem bsLevel_sum_nonneg (W : J → ℝ) (hW : ∀ i, 0 < W i) (k : ℝ) (hk : 0 < k) (j : J) :
    0 ≤ ∑ i, bsLambda W k j i * (1 - W i / ∑ l, W l)
      * (W i * (bsAlpha W k j i - if i = j then 1 else 0)) := by
  have hzp := bsZk_pos W hW k hk
  have hS : 0 < ∑ p, W p := sum_pos (fun p _ => hW p) ⟨j, mem_univ j⟩
  have hm : ∀ i, 0 ≤ W i * (1 - W i / ∑ p, W p) := fun i => mul_nonneg (hW i).le (by
    rw [sub_nonneg, div_le_one hS]; exact single_le_sum (fun p _ => (hW p).le) (mem_univ i))
  simp only [bsLambda, bsAlpha]
  set z := bsZk W k with hzdef
  set S := ∑ p, W p
  set Z := ∑ l, z l with hZdef
  set Q := ∑ l, z l ^ 2 with hQdef
  have hZ : 0 < Z := sum_pos (fun l _ => hzp l) ⟨j, mem_univ j⟩
  have hZ0 := hZ.ne'
  have hSS : ∑ l, z l * (1 - z l) = Z - Q := by
    simp only [mul_sub, mul_one, sum_sub_distrib, sq, Z, Q]
  set R := ∑ i ∈ univ.erase j, z i
  set s' := ∑ i ∈ univ.erase j, z i ^ 2
  have hZR : Z = z j + R := (add_sum_erase _ _ (mem_univ j)).symm
  have hQs : Q = z j ^ 2 + s' := (add_sum_erase _ (fun i => z i ^ 2) (mem_univ j)).symm
  have hR : 0 ≤ R := sum_nonneg fun i _ => (hzp i).le
  rw [hSS, ← add_sum_erase _ _ (mem_univ j)]
  have tj : -(z j * (1 - z j) * ((if j = j then (1 : ℝ) else 0) - z j / Z)
        + (1 - z j) / Z * (z j * (1 - z j) - (Z - Q) * (z j / Z))) * (1 - W j / S)
        * (W j * (z j * (if j = j then 1 else 0) + (1 - z j) * (z j / Z)
          - if j = j then 1 else 0))
      = (1 - z j) ^ 2 / Z ^ 3 * (W j * (1 - W j / S) * z j * (Z - z j)
          * ((Z - z j) ^ 2 + (Q - z j ^ 2))) := by
    simp only [ite_true]
    field_simp
    ring
  have ti : ∀ i ∈ univ.erase j, -(z j * (1 - z j) * ((if i = j then (1 : ℝ) else 0) - z i / Z)
        + (1 - z j) / Z * (z i * (1 - z i) - (Z - Q) * (z i / Z))) * (1 - W i / S)
        * (W i * (z j * (if i = j then 1 else 0) + (1 - z j) * (z i / Z)
          - if i = j then 1 else 0))
      = (1 - z j) ^ 2 / Z ^ 3 * (W i * (1 - W i / S) * z i ^ 2 * (Z * z j + Z * z i - Q)) := by
    intro i hi
    simp only [ne_of_mem_erase hi, ite_false]
    field_simp
    ring
  rw [tj, sum_congr rfl ti, ← mul_sum]
  have hc : 0 ≤ (1 - z j) ^ 2 / Z ^ 3 := by positivity
  refine add_nonneg (mul_nonneg hc ?_) (mul_nonneg hc ?_)
  · have e1 : Z - z j = R := by linarith
    have e2 : Q - z j ^ 2 = s' := by linarith
    rw [e1, e2]
    have : 0 ≤ s' := sum_nonneg fun i _ => sq_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (hm j) (hzp j).le) hR) (by positivity)
  have e : ∑ i ∈ univ.erase j, W i * (1 - W i / S) * z i ^ 2 * (Z * z j + Z * z i - Q)
      = ∑ i ∈ univ.erase j, (W i * (1 - W i / S) * z i ^ 2 * (z j * (R + z i))
        + (R * (W i * (1 - W i / S) * z i * z i ^ 2) - W i * (1 - W i / S) * z i * z i * s')) :=
    sum_congr rfl fun i _ => by rw [hZR, hQs]; ring
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul] at e
  rw [e]
  refine add_nonneg (sum_nonneg fun i _ => ?_) (sub_nonneg.mpr ?_)
  · exact mul_nonneg (mul_nonneg (hm i) (sq_nonneg _))
      (mul_nonneg (hzp j).le (by linarith [hzp i]))
  · exact sum_mul_sum_sq_le_of_monovary _ (fun i => W i * (1 - W i / S) * z i) z
      (fun i _ => (hzp i).le) fun i _ l _ => bsZk_spread_monovary W hW k hk i l


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


/-- **The level part of the cross term is `≤ 0`, any volumes**: with leptokurtic levels
(`κL ≥ 0`) and mesokurtic noise (`κN = 0`), the first-order cross term `2E[AB]` of the
Bühlmann–Straub plug-in (`crossTerm_bs_of_cumulants`) is `≤ 0` for any positive volumes `wᵢₜ`:
its level part is `-2κL/(cτ²)` times the sum of `bsLevel_sum_nonneg`, and `c ≥ 0`. -/
theorem crossTerm_bs_level_nonpos [Nonempty T] (X : J ⊕ (J × T) → Ω → ℝ)
    (hX : ∀ p, MemLp (X p) 4 P) (τ2 σsq κL μ : ℝ) (hτ : 0 < τ2) (hσ : 0 < σsq) (hκ : 0 ≤ κL)
    (w : J → T → ℝ) (hw : ∀ i t, 0 < w i t)
    (h4 : ∀ p q r s, ∫ ω, X p ω * X q ω * X r ω * X s ω ∂P
      = primK4W κL 0 w p q r s
        + diagonal (primVarW τ2 σsq w) p q * diagonal (primVarW τ2 σsq w) r s
        + diagonal (primVarW τ2 σsq w) p r * diagonal (primVarW τ2 σsq w) q s
        + diagonal (primVarW τ2 σsq w) p s * diagonal (primVarW τ2 σsq w) q r) (j : J) :
    2 * ∫ ω, (∑ i, bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
            * regionMean w (cellsOf μ fun p => X p ω) i - (μ + X (Sum.inl j) ω))
        * (∑ i, bsLambda (fun i => ∑ t, w i t) (σsq / τ2) j i
            * regionMean w (cellsOf μ fun p => X p ω) i)
        * bsEps w τ2 σsq (statP w (cellsOf μ fun p => X p ω))
            (statB w (cellsOf μ fun p => X p ω)) ∂P ≤ 0 := by
  rw [crossTerm_bs_of_cumulants X hX τ2 σsq κL 0 μ hτ hσ w hw h4 j]
  have hWp : ∀ i, 0 < ∑ t, w i t := sum_pos_of_pos w hw
  set W : J → ℝ := fun i => ∑ t, w i t with hWdef
  have hS : 0 < ∑ i, W i := sum_pos (fun i _ => hWp i) ⟨j, mem_univ j⟩
  have hc : 0 ≤ ∑ i, W i - (∑ i, W i ^ 2) / ∑ i, W i := by
    rw [sub_nonneg, div_le_iff₀ hS, mul_comm, mul_sum]
    exact sum_le_sum fun i _ => by
      rw [sq]; exact mul_le_mul_of_nonneg_right
        (single_le_sum (fun p _ => (hWp p).le) (mem_univ i)) (hWp i).le
  have hsum := bsLevel_sum_nonneg W hWp (σsq / τ2) (div_pos hσ hτ) j
  have e : ∑ i, bsLambda W (σsq / τ2) j i * (1 - W i / ∑ l, W l)
        * (κL * W i * (bsAlpha W (σsq / τ2) j i - if i = j then 1 else 0)
          + 0 * (∑ t, shares w i t ^ 2) * bsAlpha W (σsq / τ2) j i / W i)
      = κL * ∑ i, bsLambda W (σsq / τ2) j i * (1 - W i / ∑ l, W l)
        * (W i * (bsAlpha W (σsq / τ2) j i - if i = j then 1 else 0)) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  simp only [hWdef] at e hc hsum ⊢
  rw [e]
  simp only [zero_div, mul_zero, zero_mul, zero_sub]
  have : 0 ≤ 1 / ((∑ i, ∑ t, w i t - (∑ i, (∑ t, w i t) ^ 2) / ∑ i, ∑ t, w i t) * τ2)
      * (κL * ∑ i, bsLambda (fun i => ∑ t, w i t) (σsq / τ2) j i
        * (1 - (∑ t, w i t) / ∑ l, ∑ t, w l t)
        * ((∑ t, w i t) * (bsAlpha (fun i => ∑ t, w i t) (σsq / τ2) j i
          - if i = j then 1 else 0))) :=
    mul_nonneg (div_nonneg zero_le_one (mul_nonneg hc hτ.le)) (mul_nonneg hκ hsum)
  linarith

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

omit [Fintype T] [DecidableEq T] in
/-- The plain blend row `zδᵢⱼ + (1 - z)/J` applied to `x`: `z xⱼ + (1 - z) x̄`. -/
lemma sum_blendRow_mul (z : ℝ) (j : J) (x : J → ℝ) :
    ∑ i, ((z * if i = j then 1 else 0) + (1 - z) / Fintype.card J) * x i
      = z * x j + (1 - z) * (∑ i, x i) / Fintype.card J := by
  have e : ∀ i, ((z * if i = j then 1 else 0) + (1 - z) / Fintype.card J) * x i
      = (if i = j then z * x i else 0) + (1 - z) / Fintype.card J * x i := fun i => by
    split_ifs <;> ring
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq', ← mul_sum]
  simp only [mem_univ, ↓reduceIte]
  ring

omit [Fintype T] [DecidableEq T] in
/-- The spread row `δᵢⱼ - 1/J` applied to `x`: `xⱼ - x̄`. -/
lemma sum_spreadRow_mul (j : J) (x : J → ℝ) :
    ∑ i, ((if i = j then 1 else 0) - 1 / Fintype.card J) * x i
      = x j - (∑ i, x i) / Fintype.card J := by
  have e : ∀ i, ((if i = j then 1 else 0) - 1 / Fintype.card J) * x i
      = (if i = j then x i else 0) - x i / Fintype.card J := fun i => by
    split_ifs <;> ring
  rw [sum_congr rfl fun i _ => e i, sum_sub_distrib, sum_ite_eq', ← sum_div]
  simp only [mem_univ, ↓reduceIte]

omit [Fintype T] [DecidableEq T] in
/-- A sum whose terms off `j` all equal `c`: `gⱼ + (J - 1)c`. -/
lemma sum_eq_add_card_sub_one_mul (g : J → ℝ) (j : J) (c : ℝ) (hg : ∀ x, x ≠ j → g x = c) :
    ∑ x, g x = g j + (Fintype.card J - 1) * c := by
  have hcard : ((univ.erase j).card : ℝ) = Fintype.card J - 1 := by
    have : Nonempty J := ⟨j⟩
    rw [card_erase_of_mem (mem_univ j), card_univ, Nat.cast_sub Fintype.card_pos]; simp
  rw [← add_sum_erase _ _ (mem_univ j),
    sum_congr rfl fun x hx => hg x (ne_of_mem_erase hx), sum_const, nsmul_eq_mul, hcard]

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
  have hA := sum_blendRow_mul z j
  have hL : ∀ x : J → ℝ, ∑ i, -(z * (1 - z) * ((if i = j then 1 else 0) - 1 / Fintype.card J)) * x i
      = -(z * (1 - z)) * (x j - (∑ i, x i) / Fintype.card J) := fun x => by
    rw [← sum_spreadRow_mul j x, mul_sum]
    exact sum_congr rfl fun i _ => by ring
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
  rw [sum_eq_add_card_sub_one_mul _ j _ (fun x hx => by simp only [hx, ↓reduceIte]; rfl),
    sum_eq_add_card_sub_one_mul _ j _ (fun x hx => by simp only [hx, ↓reduceIte]; rfl)]
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
    fun x => (sum_blendRow_mul z j x).symm
  have hD : ∀ x : J → ℝ, x j - (∑ i, x i) / Fintype.card J = ∑ i, β i * x i :=
    fun x => (sum_spreadRow_mul j x).symm
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
  rw [sum_eq_add_card_sub_one_mul _ j _
    (fun x hx => by simp only [hαdef, hβdef, hx, ↓reduceIte]; rfl)]
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
