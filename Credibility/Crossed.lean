import Credibility.Hierarchical

/-!
# Crossed levels: two groupings at once

Extension, not in the thesis (`notes/crossed-2x2.md`; paper, open directions). The cells
`j` of a table carry a row `row j` (e.g. the country) and a column `col j` (e.g. the car
type). Their levels are

  `μⱼ = μ + α A_{row j} + β B_{col j} + γ Cⱼ`

with `A`, `B`, `C` uncorrelated, mean `0` and variance `1`. So the level covariance is

  `L = α²·[same row] + β²·[same column] + γ²·I`,

and `K = L + Σ` for any noise covariance `Σ ⪰ 0`. With `β² = 0` this is Bridge 4 of
`Hierarchical.lean` with the rows as groups; with `α² = β² = 0` it is the thesis.

What is new here is only the model: `L` and `K` for any cell set and any `Σ`, `K ≻ 0`, `K` as
a mixed-model covariance (so Henderson's equations give the row and column effects), and,
in the balanced table with `Σ = σ²I`, the closed form of the best linear unbiased predictor
(`Core.blupWeight`, a corollary of `Core.blup_optimal`):

  `μ̃ₐₜ = X̄ + z_c(X̄ₐ. − X̄) + z_t(X̄.ₜ − X̄) + z_i(Xₐₜ − X̄ₐ. − X̄.ₜ + X̄)`,

one credibility factor `zₖ = λₖ/(λₖ + σ²)` per layer, with `λ_c = n_T α² + γ²`,
`λ_t = n_A β² + γ²`, `λ_i = γ²`. The blend with one common `z` loses exactly
`Σₖ mₖ(λₖ + σ²)(z − zₖ)²` in total over the cells (`mₖ` the dimension of layer `k`).
A cell without data is predicted from its row and column (`missing_blup`, the 2×2 table).

Second moments are given numbers; only first and second moments are assumed.
-/

open Matrix Finset

namespace Credibility
namespace Crossed

variable {n A T : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
  [Fintype T] [DecidableEq T]
variable (row : n → A) (col : n → T)

/-! ### The crossed level covariance and `K` -/

/-- The crossed level covariance `L = α²·[same row] + β²·[same column] + γ²·I`. -/
noncomputable def levelCov (α2 β2 γ2 : ℝ) : Matrix n n ℝ :=
  α2 • Model.sameGroup row + β2 • Model.sameGroup col + γ2 • (1 : Matrix n n ℝ)

/-- The covariance of the cell estimates, `K = L + Σ`. -/
noncomputable def K (α2 β2 γ2 : ℝ) (S : Matrix n n ℝ) : Matrix n n ℝ :=
  levelCov row col α2 β2 γ2 + S

omit [Fintype n] [Fintype A] [Fintype T] in
lemma levelCov_apply (α2 β2 γ2 : ℝ) (i j : n) :
    levelCov row col α2 β2 γ2 i j
      = α2 * (if row i = row j then 1 else 0) + β2 * (if col i = col j then 1 else 0)
        + γ2 * (if i = j then 1 else 0) := by
  simp [levelCov, Model.sameGroup, Matrix.one_apply]

/-- `L ⪰ 0` when the three variances are nonnegative. -/
theorem levelCov_posSemidef {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) :
    (levelCov row col α2 β2 γ2).PosSemidef :=
  ((Model.sameGroup_posSemidef row).smul hα).add ((Model.sameGroup_posSemidef col).smul hβ)
    |>.add (PosSemidef.one.smul hγ)

/-- **`K ≻ 0` for positive definite noise**, whatever the cells and `α², β², γ² ≥ 0`. -/
theorem K_posDef {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) {S : Matrix n n ℝ}
    (hS : S.PosDef) : (K row col α2 β2 γ2 S).PosDef :=
  PosDef.posSemidef_add (levelCov_posSemidef row col hα hβ hγ) hS

/-- **`K ≻ 0` with a cell effect**: `γ² > 0` and `Σ ⪰ 0` suffice. -/
theorem K_posDef_of_gamma {α2 β2 γ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 < γ2)
    {S : Matrix n n ℝ} (hS : S.PosSemidef) : (K row col α2 β2 γ2 S).PosDef := by
  have hL : (levelCov row col α2 β2 γ2).PosDef :=
    PosDef.posSemidef_add (((Model.sameGroup_posSemidef row).smul hα).add
      ((Model.sameGroup_posSemidef col).smul hβ)) (PosDef.one.smul hγ)
  exact hL.add_posSemidef hS

/-! ### `K` as a mixed-model covariance: Henderson's equations -/

/-- The crossed design `Z = [Z_row | Z_col]`: one random effect per row and one per column. -/
def design : Matrix n (A ⊕ T) ℝ :=
  of fun j k => Sum.elim (fun a => if row j = a then 1 else 0) (fun t => if col j = t then 1 else 0) k

/-- The covariance of the effects: `α²` for every row effect, `β²` for every column effect. -/
noncomputable def effectCov (α2 β2 : ℝ) : Matrix (A ⊕ T) (A ⊕ T) ℝ :=
  diagonal (Sum.elim (fun _ => α2) (fun _ => β2))

/-- `K = Z G Zᵀ + R` with the crossed design `Z`, `G = diag(α², β²)` and `R = γ²·I + Σ`. -/
lemma K_eq_mixed (α2 β2 γ2 : ℝ) (S : Matrix n n ℝ) :
    K row col α2 β2 γ2 S
      = (design row col * effectCov α2 β2 : Matrix n (A ⊕ T) ℝ) * (design row col)ᵀ
        + (γ2 • (1 : Matrix n n ℝ) + S) := by
  have hD : design row col * effectCov α2 β2
      = of fun j k => design row col j k * Sum.elim (fun _ => α2) (fun _ => β2) k := by
    ext j k
    exact Matrix.mul_diagonal _ _ j k
  rw [hD]
  ext i j
  rw [K, Matrix.add_apply, Matrix.add_apply, levelCov_apply]
  simp [design, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Function.swap, eq_comm]
  ring

/-- The covariance of the cells with row effect `a` (`Z G e_a`): `α²·[row j = a]`. -/
lemma design_effect_inl (α2 β2 : ℝ) (a : A) :
    design row col *ᵥ (effectCov α2 β2 *ᵥ Pi.single (Sum.inl a) 1) = α2 • grpOne row a := by
  ext j
  simp [design, effectCov, mulVec, dotProduct, Fintype.sum_sum_type, grpOne,
    Pi.single_apply, diagonal, eq_comm]

/-- The covariance of the cells with column effect `t`: `β²·[col j = t]`. -/
lemma design_effect_inr (α2 β2 : ℝ) (t : T) :
    design row col *ᵥ (effectCov α2 β2 *ᵥ Pi.single (Sum.inr t) 1) = β2 • grpOne col t := by
  ext j
  simp [design, effectCov, mulVec, dotProduct, Fintype.sum_sum_type, grpOne,
    Pi.single_apply, diagonal, eq_comm]

lemma effectCov_posDef {α2 β2 : ℝ} (hα : 0 < α2) (hβ : 0 < β2) :
    (effectCov (A := A) (T := T) α2 β2).PosDef :=
  posDef_diagonal_iff.2 fun k => by cases k <;> simp [hα, hβ]

/-- **Crossed credibility by Henderson's equations.** Solve the mixed-model equations with the
collective mean as fixed effect, the row and column effects as random effects (crossed design,
`G = diag(α², β²)`) and `R = γ²·I + Σ`. Then the estimated effect of row `a` is the best linear
unbiased predictor (`Core.blup`) of `α A_a`, with `Cov(x, αA_a) = α²·[row j = a]`. -/
theorem rowEffect_eq_blup [Nonempty n] {α2 β2 γ2 : ℝ} (hα : 0 < α2) (hβ : 0 < β2)
    {S : Matrix n n ℝ} (hR : (γ2 • (1 : Matrix n n ℝ) + S).PosDef) {m : Unit → ℝ}
    {b : A ⊕ T → ℝ} {x : n → ℝ}
    (h : Core.MMESolution (Unequal.onesCol n) (design row col) (effectCov α2 β2)
      (γ2 • (1 : Matrix n n ℝ) + S) m b x) (a : A) :
    b (Sum.inl a) = Core.blup (K row col α2 β2 γ2 S) (Unequal.onesCol n) (α2 • grpOne row a) 0
      ⬝ᵥ x := by
  rw [← design_effect_inl row col α2 β2 a, K_eq_mixed]
  exact Core.hendersonMME_eq_blup _ Unequal.onesCol_injective _ (effectCov_posDef hα hβ) hR h _

/-- …and likewise the estimated effect of column `t` predicts `β B_t` best. -/
theorem colEffect_eq_blup [Nonempty n] {α2 β2 γ2 : ℝ} (hα : 0 < α2) (hβ : 0 < β2)
    {S : Matrix n n ℝ} (hR : (γ2 • (1 : Matrix n n ℝ) + S).PosDef) {m : Unit → ℝ}
    {b : A ⊕ T → ℝ} {x : n → ℝ}
    (h : Core.MMESolution (Unequal.onesCol n) (design row col) (effectCov α2 β2)
      (γ2 • (1 : Matrix n n ℝ) + S) m b x) (t : T) :
    b (Sum.inr t) = Core.blup (K row col α2 β2 γ2 S) (Unequal.onesCol n) (β2 • grpOne col t) 0
      ⬝ᵥ x := by
  rw [← design_effect_inr row col α2 β2 t, K_eq_mixed]
  exact Core.hendersonMME_eq_blup _ Unequal.onesCol_injective _ (effectCov_posDef hα hβ) hR h _

/-! ### No column effect: Bridge 4 with the rows as groups -/

/-- With `β² = 0` the crossed `L` is the group level covariance `L_G` of Bridge 4 with the
rows as groups, `τ² = α² + γ²` and `φ = α²/(α² + γ²)`. -/
theorem levelCov_beta_zero {α2 γ2 : ℝ} (h : α2 + γ2 ≠ 0) :
    levelCov row col α2 0 γ2 = Model.levelCovG row (α2 + γ2) (α2 / (α2 + γ2)) := by
  rw [Model.levelCovG_eq_add_sameGroup, levelCov]
  have h1 : (1 - α2 / (α2 + γ2)) * (α2 + γ2) = γ2 := by field_simp; ring
  have h2 : α2 / (α2 + γ2) * (α2 + γ2) = α2 := by field_simp
  rw [h1, h2, zero_smul, add_zero, add_comm]

/-- …so for a thesis model `M` with `τ² = α² + γ²` and its noise `Σ`, the crossed `K` is
`K_G` (`Model.KG`), and every Bridge 4 result (`Model.glsWeight_KG`, `Model.bestZ_G_eq`,
`Unequal.groupEffect_eq_blup`) applies to it. -/
theorem K_beta_zero {J Tm : Type*} [Fintype J] [DecidableEq J] [Fintype Tm] [DecidableEq Tm]
    (M : Model J Tm) (grp : J → A) (col : J → T) {α2 γ2 : ℝ} (hτ : M.τ2 = α2 + γ2) :
    K grp col α2 0 γ2 M.errCov = M.KG grp (α2 / M.τ2) := by
  rw [K, Model.KG, levelCov_beta_zero grp col (hτ ▸ M.τ2_pos.ne'), hτ]

/-- **Bridge 4 as a corollary**: with `β² = 0` the crossed best predictor of every cell level
is the group one (`Core.blupWeight` for `K_G`, `L_G`), rows as groups. -/
theorem blupWeight_beta_zero {J Tm : Type*} [Fintype J] [DecidableEq J] [Fintype Tm]
    [DecidableEq Tm] (M : Model J Tm) (grp : J → A) (col : J → T) {α2 γ2 : ℝ}
    (hτ : M.τ2 = α2 + γ2) (j : J) :
    Core.blupWeight (K grp col α2 0 γ2 M.errCov) (levelCov grp col α2 0 γ2) j
      = Core.blupWeight (M.KG grp (α2 / M.τ2)) (Model.levelCovG grp M.τ2 (α2 / M.τ2)) j := by
  rw [K_beta_zero M grp col hτ, levelCov_beta_zero grp col (hτ ▸ M.τ2_pos.ne'), hτ]

end Crossed

namespace Core

/-- Unbiased weights `e` that satisfy the first-order condition (`K e - Lⱼ` constant) are the
best predictor's weights. -/
lemma eq_blupWeight_of_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    {K : Matrix J J ℝ} (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) {e : J → ℝ} {c : ℝ}
    (he : ∀ i, (K *ᵥ e) i - L j i = c) (hs : ∑ i, e i = 1) : e = Core.blupWeight K L j := by
  have : Nonempty J := ⟨j⟩
  refine Core.blupWeight_unique hK L j hs ?_
  rw [Core.linMse_eq_add_of_mulVec hK.isHermitian L j he (Core.blupWeight K L j)
    (by rw [Core.sum_blupWeight hK, hs])]
  have := hK.posSemidef.dotProduct_mulVec_nonneg (Core.blupWeight K L j - e)
  simp only [star_trivial] at this
  linarith


/-- A rank-one term along `1` does not change the best predictor: noise (or level) shared by
all cohorts cancels, `d*(K + c·11ᵀ) = d*(K)` (cf. `glsWeight_add_rankOne`). -/
theorem blupWeight_add_rankOne {J : Type*} [Fintype J] [DecidableEq J] {K : Matrix J J ℝ}
    (hK : K.PosDef) (c : ℝ) (hK' : (K + c • vecMulVec 1 1).PosDef) (L : Matrix J J ℝ) (j : J) :
    blupWeight (K + c • vecMulVec 1 1) L j = blupWeight K L j := by
  have : Nonempty J := ⟨j⟩
  symm
  refine eq_blupWeight_of_mulVec hK' L j
    (c := (1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹ + c) (fun i => ?_) (sum_blupWeight hK L j)
  have h := mulVec_blupWeight hK L j i
  have hs := sum_blupWeight hK L j
  have : ((K + c • vecMulVec 1 1) *ᵥ blupWeight K L j) i
      = (K *ᵥ blupWeight K L j) i + c * ∑ k, blupWeight K L j k := by
    simp [mulVec, dotProduct, vecMulVec, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [this, hs]
  linarith

/-- …and it adds `c(Σᵢdᵢ)²` to the error of any weights. -/
lemma linMse_add_rankOne {J : Type*} [Fintype J] (K L : Matrix J J ℝ) (c : ℝ) (j : J)
    (d : J → ℝ) :
    linMse (K + c • vecMulVec 1 1) L j d = linMse K L j d + c * (∑ i, d i) ^ 2 := by
  have : d ⬝ᵥ ((K + c • vecMulVec 1 1) *ᵥ d) = d ⬝ᵥ (K *ᵥ d) + c * (∑ i, d i) ^ 2 := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    congr 1
    simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.one_apply, mul_one, one_mul, sq,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [linMse, this]
  ring

end Core

namespace Crossed

variable {n A T : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
  [Fintype T] [DecidableEq T]
variable (row : n → A) (col : n → T)

/-! ### The balanced table with uncorrelated noise

All cells `(a, t) ∈ A × T` observed, rows `Prod.fst`, columns `Prod.snd`, `Σ = σ²I`. Every
weight vector met here is a *layer vector* `w₁ + w_r[same row] + w_c[same column] + w_d[same
cell]` around the target cell, and `K` maps layer vectors to layer vectors
(`mulVec_layer`): the problem lives in four dimensions. -/

section Balanced

variable {A T : Type*} [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

/-- `K` of the balanced table: `L + σ²I` over `A × T`. -/
noncomputable def KBal (α2 β2 γ2 σ2 : ℝ) : Matrix (A × T) (A × T) ℝ :=
  K Prod.fst Prod.snd α2 β2 γ2 (σ2 • 1)

/-- `L` of the balanced table. -/
noncomputable def LBal (α2 β2 γ2 : ℝ) : Matrix (A × T) (A × T) ℝ :=
  levelCov Prod.fst Prod.snd α2 β2 γ2

/-- The layer vector `w₁ + w_r[p.1 = c.1] + w_c[p.2 = c.2] + w_d[p = c]` around the cell `c`. -/
def layer (c : A × T) (w1 wr wc wd : ℝ) : A × T → ℝ := fun p =>
  w1 + wr * (if p.1 = c.1 then 1 else 0) + wc * (if p.2 = c.2 then 1 else 0)
    + wd * (if p = c then 1 else 0)

/-- `K` acts cell by cell as `α²·(row sum) + β²·(column sum) + (γ² + σ²)·(the cell)`. -/
lemma mulVec_KBal (α2 β2 γ2 σ2 : ℝ) (v : A × T → ℝ) (p : A × T) :
    (KBal α2 β2 γ2 σ2 *ᵥ v) p
      = α2 * ∑ t, v (p.1, t) + β2 * ∑ a, v (a, p.2) + (γ2 + σ2) * v p := by
  have h : ∀ q : A × T, KBal α2 β2 γ2 σ2 p q * v q
      = α2 * (if p.1 = q.1 then v q else 0) + β2 * (if p.2 = q.2 then v q else 0)
        + (γ2 + σ2) * (if p = q then v q else 0) := by
    intro q
    simp only [KBal, K, Matrix.add_apply, levelCov_apply, smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> by_cases h3 : p = q <;>
      simp [h1, h2, h3] <;> ring
  have hr : ∑ q : A × T, (if p.1 = q.1 then v q else 0) = ∑ t, v (p.1, t) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have hc : ∑ q : A × T, (if p.2 = q.2 then v q else 0) = ∑ a, v (a, p.2) := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [mulVec, dotProduct, h, Finset.sum_add_distrib, ← Finset.mul_sum, hr, hc,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma sum_row_layer (c : A × T) (w1 wr wc wd : ℝ) (a : A) :
    ∑ t, layer c w1 wr wc wd (a, t)
      = Fintype.card T * w1 + (Fintype.card T * wr + wd) * (if a = c.1 then 1 else 0) + wc := by
  by_cases ha : a = c.1
  · subst ha
    simp [layer, Finset.sum_add_distrib, Prod.ext_iff, Finset.sum_ite_eq']
    ring
  · simp [layer, Finset.sum_add_distrib, Prod.ext_iff, ha, Finset.sum_ite_eq']

lemma sum_col_layer (c : A × T) (w1 wr wc wd : ℝ) (t : T) :
    ∑ a, layer c w1 wr wc wd (a, t)
      = Fintype.card A * w1 + wr + (Fintype.card A * wc + wd) * (if t = c.2 then 1 else 0) := by
  by_cases ht : t = c.2
  · subst ht
    simp [layer, Finset.sum_add_distrib, Prod.ext_iff, Finset.sum_ite_eq']
    ring
  · simp [layer, Finset.sum_add_distrib, Prod.ext_iff, ht, Finset.sum_ite_eq']

/-- `K` maps layer vectors to layer vectors. -/
lemma mulVec_layer (α2 β2 γ2 σ2 : ℝ) (c : A × T) (w1 wr wc wd : ℝ) :
    KBal α2 β2 γ2 σ2 *ᵥ layer c w1 wr wc wd
      = layer c ((α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2) * w1 + α2 * wc + β2 * wr)
          (α2 * (Fintype.card T * wr + wd) + (γ2 + σ2) * wr)
          (β2 * (Fintype.card A * wc + wd) + (γ2 + σ2) * wc) ((γ2 + σ2) * wd) := by
  funext p
  rw [mulVec_KBal, sum_row_layer, sum_col_layer]
  simp only [layer]
  ring

/-- Row `c` of `L` is the layer vector `(0, α², β², γ²)`. -/
lemma LBal_eq_layer (α2 β2 γ2 : ℝ) (c : A × T) :
    LBal α2 β2 γ2 c = layer c 0 α2 β2 γ2 := by
  funext p
  simp [LBal, levelCov_apply, layer, eq_comm]

lemma sum_layer (c : A × T) (w1 wr wc wd : ℝ) :
    ∑ p, layer c w1 wr wc wd p
      = Fintype.card A * Fintype.card T * w1 + Fintype.card T * wr + Fintype.card A * wc + wd := by
  rw [Fintype.sum_prod_type]
  simp only [sum_row_layer, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- A layer vector against data `x`: grand total, row total, column total and the cell. -/
lemma layer_dotProduct (c : A × T) (w1 wr wc wd : ℝ) (x : A × T → ℝ) :
    layer c w1 wr wc wd ⬝ᵥ x
      = w1 * ∑ p, x p + wr * ∑ t, x (c.1, t) + wc * ∑ a, x (a, c.2) + wd * x c := by
  simp only [dotProduct, layer, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  simp [Fintype.sum_prod_type, Prod.ext_iff, ite_and, Finset.sum_ite_eq']
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

/-- The credibility factor of the row layer, `z_r = λ_r/(λ_r + σ²)` with `λ_r = n_T α² + γ²`. -/
noncomputable def zRow (T : Type*) [Fintype T] (α2 γ2 σ2 : ℝ) : ℝ :=
  (Fintype.card T * α2 + γ2) / (Fintype.card T * α2 + γ2 + σ2)

/-- The credibility factor of the column layer, `z_c = λ_c/(λ_c + σ²)` with `λ_c = n_A β² + γ²`. -/
noncomputable def zCol (A : Type*) [Fintype A] (β2 γ2 σ2 : ℝ) : ℝ :=
  (Fintype.card A * β2 + γ2) / (Fintype.card A * β2 + γ2 + σ2)

/-- The credibility factor of the cell (interaction) layer, `z_i = γ²/(γ² + σ²)`. -/
noncomputable def zCell (γ2 σ2 : ℝ) : ℝ := γ2 / (γ2 + σ2)

/-- The weights of the best linear unbiased predictor of `μ_c` in the balanced table: the layer
vector `((1 - z_r - z_c + z_i)/(n_A n_T), (z_r - z_i)/n_T, (z_c - z_i)/n_A, z_i)`. -/
theorem blupWeight_KBal [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (c : A × T) :
    Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
      = layer c ((1 - zRow T α2 γ2 σ2 - zCol A β2 γ2 σ2 + zCell γ2 σ2)
            / (Fintype.card A * Fintype.card T))
          ((zRow T α2 γ2 σ2 - zCell γ2 σ2) / Fintype.card T)
          ((zCol A β2 γ2 σ2 - zCell γ2 σ2) / Fintype.card A) (zCell γ2 σ2) := by
  have hK : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have h1 : 0 < Fintype.card T * α2 + γ2 + σ2 := by positivity
  have h2 : 0 < Fintype.card A * β2 + γ2 + σ2 := by positivity
  have h3 : 0 < γ2 + σ2 := by positivity
  symm
  set w1 := (1 - zRow T α2 γ2 σ2 - zCol A β2 γ2 σ2 + zCell γ2 σ2)
    / (Fintype.card A * Fintype.card T)
  refine Core.eq_blupWeight_of_mulVec hK _ c
    (c := (α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2) * w1
      + α2 * ((zCol A β2 γ2 σ2 - zCell γ2 σ2) / Fintype.card A)
      + β2 * ((zRow T α2 γ2 σ2 - zCell γ2 σ2) / Fintype.card T)) (fun i => ?_) ?_
  · rw [mulVec_layer, LBal_eq_layer]
    have er : α2 * (Fintype.card T * ((zRow T α2 γ2 σ2 - zCell γ2 σ2) / Fintype.card T)
        + zCell γ2 σ2) + (γ2 + σ2) * ((zRow T α2 γ2 σ2 - zCell γ2 σ2) / Fintype.card T)
        = α2 := by
      simp only [zRow, zCell]; field_simp; ring
    have ec : β2 * (Fintype.card A * ((zCol A β2 γ2 σ2 - zCell γ2 σ2) / Fintype.card A)
        + zCell γ2 σ2) + (γ2 + σ2) * ((zCol A β2 γ2 σ2 - zCell γ2 σ2) / Fintype.card A)
        = β2 := by
      simp only [zCol, zCell]; field_simp; ring
    have ed : (γ2 + σ2) * zCell γ2 σ2 = γ2 := by simp only [zCell]; field_simp
    rw [er, ec, ed]
    simp only [layer]
    ring
  · rw [sum_layer]
    simp only [w1]
    field_simp
    ring

/-- **The crossed credibility formula** (balanced table, `Σ = σ²I`). The best linear unbiased
predictor of the level of cell `c = (a, t)` is

  `X̄ + z_r(X̄ₐ. - X̄) + z_c(X̄.ₜ - X̄) + z_i(Xₐₜ - X̄ₐ. - X̄.ₜ + X̄)`,

grand mean plus the row effect, the column effect and what is left for the cell, each shrunk
by its own factor `zₖ = λₖ/(λₖ + σ²)`: `λ_r = n_T α² + γ²`, `λ_c = n_A β² + γ²`, `λ_i = γ²`.
It has the least mean squared error among all `Σᵢ dᵢXᵢ` with `Σᵢ dᵢ = 1`
(`Core.blupWeight_optimal`). The thesis blend is the same formula with one `z` for all three. -/
theorem blup_balanced [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (x : A × T → ℝ) (c : A × T) :
    Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c ⬝ᵥ x
      = (∑ p, x p) / (Fintype.card A * Fintype.card T)
        + zRow T α2 γ2 σ2 * ((∑ t, x (c.1, t)) / Fintype.card T
            - (∑ p, x p) / (Fintype.card A * Fintype.card T))
        + zCol A β2 γ2 σ2 * ((∑ a, x (a, c.2)) / Fintype.card A
            - (∑ p, x p) / (Fintype.card A * Fintype.card T))
        + zCell γ2 σ2 * (x c - (∑ t, x (c.1, t)) / Fintype.card T
            - (∑ a, x (a, c.2)) / Fintype.card A
            + (∑ p, x p) / (Fintype.card A * Fintype.card T)) := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [blupWeight_KBal hα hβ hγ hσ, layer_dotProduct]
  field_simp
  ring

/-- In the balanced table `1` is an eigenvector of `K`, so the GLS weights are equal:
`bⱼ = 1/(n_A n_T)` and the collective estimate is `X̄`. -/
theorem glsWeight_KBal [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (p : A × T) :
    glsWeight (KBal α2 β2 γ2 σ2) p = 1 / (Fintype.card A * Fintype.card T) := by
  have hK : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  set κ := α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2
  have hκ : 0 < κ := by positivity
  have hx : KBal α2 β2 γ2 σ2 *ᵥ layer p κ⁻¹ 0 0 0 = 1 := by
    rw [mulVec_layer]
    funext q
    simp [layer, κ, hκ.ne']
  rw [Core.glsWeight_of_mulVec hK hx, sum_layer]
  simp [layer]
  field_simp

/-- The blend `z X_c + (1 - z) X̄` is the layer vector `((1 - z)/(n_A n_T), 0, 0, z)`. -/
lemma blendWeight_KBal [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (c : A × T) (z : ℝ) :
    Core.blendWeight (KBal α2 β2 γ2 σ2) c z
      = layer c ((1 - z) / (Fintype.card A * Fintype.card T)) 0 0 z := by
  funext p
  simp only [Core.blendWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    glsWeight_KBal hα hβ hγ hσ, layer, Pi.single_apply]
  ring

lemma layer_sub (c : A × T) (u1 ur uc ud v1 vr vc vd : ℝ) :
    layer c u1 ur uc ud - layer c v1 vr vc vd = layer c (u1 - v1) (ur - vr) (uc - vc) (ud - vd) := by
  funext p; simp only [layer, Pi.sub_apply]; ring

/-- The inner product of two layer vectors around the same cell. -/
lemma layer_dotProduct_layer (c : A × T) (u1 ur uc ud v1 vr vc vd : ℝ) :
    layer c u1 ur uc ud ⬝ᵥ layer c v1 vr vc vd
      = u1 * (Fintype.card A * Fintype.card T * v1 + Fintype.card T * vr
          + Fintype.card A * vc + vd)
        + ur * (Fintype.card T * v1 + Fintype.card T * vr + vd + vc)
        + uc * (Fintype.card A * v1 + vr + Fintype.card A * vc + vd)
        + ud * (v1 + vr + vc + vd) := by
  rw [layer_dotProduct, sum_layer, sum_row_layer, sum_col_layer]
  simp [layer]
  ring

/-- **What the thesis blend loses** (balanced table, `Σ = σ²I`). Summed over all cells, the
blend `z X_c + (1 - z) X̄` with one common `z` has mean squared error

  `Σ_c mse(blend) = Σ_c mse(best) + (n_A - 1)(λ_r + σ²)(z - z_r)²
      + (n_T - 1)(λ_c + σ²)(z - z_c)² + (n_A - 1)(n_T - 1)(λ_i + σ²)(z - z_i)²`:

each layer costs its dimension times `(λₖ + σ²)(z - zₖ)²`. In the 2×2 table all three
dimensions are `1` (`notes/crossed-2x2.md` §3). The loss is zero iff `z` equals every
`zₖ` of a layer that is present. -/
theorem sum_linMse_blend [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (z : ℝ) :
    ∑ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
        (Core.blendWeight (KBal α2 β2 γ2 σ2) c z)
      = ∑ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
          (Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c)
        + ((Fintype.card A - 1) * (Fintype.card T * α2 + γ2 + σ2) * (z - zRow T α2 γ2 σ2) ^ 2
          + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2 + σ2) * (z - zCol A β2 γ2 σ2) ^ 2
          + (Fintype.card A - 1) * (Fintype.card T - 1) * (γ2 + σ2) * (z - zCell γ2 σ2) ^ 2) := by
  have hK : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ c : A × T,
      Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c (Core.blendWeight (KBal α2 β2 γ2 σ2) c z)
        = Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
            (Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c)
          + ((Fintype.card A - 1) * (Fintype.card T * α2 + γ2 + σ2) * (z - zRow T α2 γ2 σ2) ^ 2
            + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2 + σ2) * (z - zCol A β2 γ2 σ2) ^ 2
            + (Fintype.card A - 1) * (Fintype.card T - 1) * (γ2 + σ2) * (z - zCell γ2 σ2) ^ 2)
          / (Fintype.card A * Fintype.card T) := by
    intro c
    have hs : ∑ i, Core.blendWeight (KBal α2 β2 γ2 σ2) c z i = 1 := by
      rw [blendWeight_KBal hα hβ hγ hσ, sum_layer]; field_simp; ring
    rw [Core.linMse_eq_blupWeight_add hK _ c _ hs, blendWeight_KBal hα hβ hγ hσ,
      blupWeight_KBal hα hβ hγ hσ, layer_sub, mulVec_layer, layer_dotProduct_layer]
    congr 1
    field_simp
    ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  congr 1
  field_simp



/-! #### The best common factor and the price of the blend -/

/-- `Σₖ mₖλₖ`: the layer signal variances times the layer dimensions
`m_r = n_A - 1`, `m_c = n_T - 1`, `m_i = (n_A - 1)(n_T - 1)`. -/
noncomputable def layerSignal (A T : Type*) [Fintype A] [Fintype T] (α2 β2 γ2 : ℝ) : ℝ :=
  (Fintype.card A - 1) * (Fintype.card T * α2 + γ2) + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2)
    + (Fintype.card A - 1) * (Fintype.card T - 1) * γ2

/-- The best common credibility factor of the blend in the balanced table:
`z̄ = Σₖmₖλₖ / (Σₖmₖλₖ + (n_An_T - 1)σ²) = λ̄/(λ̄ + σ²)`, `λ̄` the dimension-weighted mean of the
layer variances. -/
noncomputable def zBlend (A T : Type*) [Fintype A] [Fintype T] (α2 β2 γ2 σ2 : ℝ) : ℝ :=
  layerSignal A T α2 β2 γ2 / (layerSignal A T α2 β2 γ2 + (Fintype.card A * Fintype.card T - 1) * σ2)

/-- `1ᵀK⁻¹1 = n_An_T/κ` with `κ = n_Tα² + n_Aβ² + γ² + σ²`, the eigenvalue of `1`. -/
lemma invTotal_KBal [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2)
    (hγ : 0 ≤ γ2) (hσ : 0 < σ2) :
    invTotal (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ)
      = Fintype.card A * Fintype.card T
        / (α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2) := by
  have hK : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  set κ := α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2
  have hκ : 0 < κ := by positivity
  obtain ⟨p⟩ : Nonempty (A × T) := inferInstance
  have hx : KBal α2 β2 γ2 σ2 *ᵥ layer p κ⁻¹ 0 0 0 = 1 := by
    rw [mulVec_layer]; funext q; simp [layer, κ, hκ.ne']
  have hdet : IsUnit (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit
  have : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ)⁻¹ *ᵥ 1 = layer p κ⁻¹ 0 0 0 := by
    rw [← hx, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  rw [invTotal, this, one_dotProduct, sum_layer]
  field_simp
  ring

/-- **The best common factor** (Core's eq. (26) for the crossed `K`, `L`): in the balanced table
every cell has `z = z̄` (`zBlend`). In the 2×2 table `z̄ = D/(D + 3σ²)` with
`D = 2α² + 2β² + 3γ²` (`notes/crossed-2x2.md` §3). -/
theorem bestZ_KBal [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2)
    (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (hN : 1 < Fintype.card A * Fintype.card T) (c : A × T) :
    (Core.levelMoments (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) (KBal α2 β2 γ2 σ2 c c) c).bestZ
      = zBlend A T α2 β2 γ2 σ2 := by
  have hK : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hN' : (1 : ℝ) < Fintype.card A * Fintype.card T := by exact_mod_cast hN
  have hb : glsWeight (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ)
      = layer c (1 / (Fintype.card A * Fintype.card T)) 0 0 0 := by
    funext p; rw [glsWeight_KBal hα hβ hγ hσ]; simp [layer]
  have hL : (LBal α2 β2 γ2 *ᵥ glsWeight (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ)) c
      = (Fintype.card T * α2 + Fintype.card A * β2 + γ2) / (Fintype.card A * Fintype.card T) := by
    rw [hb, mulVec, LBal_eq_layer, layer_dotProduct_layer]
    field_simp; ring
  have hcc : LBal α2 β2 γ2 c c = α2 + β2 + γ2 := by simp [LBal, levelCov_apply]
  have hKcc : (KBal α2 β2 γ2 σ2 : Matrix (A × T) (A × T) ℝ) c c = α2 + β2 + γ2 + σ2 := by
    simp [KBal, K, levelCov_apply]
  rw [Core.levelMoments_bestZ_eq hK, hL, hcc, hKcc, invTotal_KBal hα hβ hγ hσ, zBlend,
    layerSignal]
  have h1 : 0 < (Fintype.card A * Fintype.card T - 1) * σ2 := mul_pos (by linarith) hσ
  have h2 : 0 ≤ (Fintype.card A - 1) * (Fintype.card T * α2 + γ2)
      + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2)
      + (Fintype.card A - 1) * (Fintype.card T - 1) * γ2 := by
    have := sub_nonneg.mpr hA; have := sub_nonneg.mpr hT; positivity
  have hκ : 0 < α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2 := by positivity
  have hd : α2 + β2 + γ2 + σ2 - (Fintype.card A * Fintype.card T
      / (α2 * Fintype.card T + β2 * Fintype.card A + γ2 + σ2))⁻¹
      = ((Fintype.card A - 1) * (Fintype.card T * α2 + γ2)
        + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2)
        + (Fintype.card A - 1) * (Fintype.card T - 1) * γ2
        + (Fintype.card A * Fintype.card T - 1) * σ2) / (Fintype.card A * Fintype.card T) := by
    field_simp; ring
  rw [hd]
  field_simp
  ring

/-- **The blend at its best common factor**, summed over the table: `z̄` minimizes the total
error of `z X_c + (1 - z) X̄`, and any other `z` costs `W(z - z̄)²` more,
`W = Σₖ mₖ(λₖ + σ²)`. -/
theorem sum_linMse_blend_zBlend [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2) (hN : 1 < Fintype.card A * Fintype.card T)
    (z : ℝ) :
    ∑ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
        (Core.blendWeight (KBal α2 β2 γ2 σ2) c z)
      = ∑ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
          (Core.blendWeight (KBal α2 β2 γ2 σ2) c (zBlend A T α2 β2 γ2 σ2))
        + (layerSignal A T α2 β2 γ2 + (Fintype.card A * Fintype.card T - 1) * σ2)
          * (z - zBlend A T α2 β2 γ2 σ2) ^ 2 := by
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hN' : (1 : ℝ) < Fintype.card A * Fintype.card T := by exact_mod_cast hN
  have hW : 0 < layerSignal A T α2 β2 γ2 + (Fintype.card A * Fintype.card T - 1) * σ2 := by
    have := sub_nonneg.mpr hA; have := sub_nonneg.mpr hT
    have h1 : 0 < (Fintype.card A * Fintype.card T - 1) * σ2 := mul_pos (by linarith) hσ
    unfold layerSignal; positivity
  have h1 : 0 < Fintype.card T * α2 + γ2 + σ2 := by positivity
  have h2 : 0 < Fintype.card A * β2 + γ2 + σ2 := by positivity
  have h3 : 0 < γ2 + σ2 := by positivity
  rw [sum_linMse_blend hα hβ hγ hσ, sum_linMse_blend hα hβ hγ hσ]
  simp only [zBlend, zRow, zCol, zCell]
  unfold layerSignal at hW ⊢
  field_simp
  ring

/-- **The error of the crossed predictor**, summed over the table:
`σ² + Σₖ mₖλₖσ²/(λₖ + σ²)`. The grand mean costs `σ²`; each layer is shrunk by its own `zₖ`
(`notes/crossed-2x2.md` §3). -/
theorem sum_linMse_blup [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2)
    (hγ : 0 ≤ γ2) (hσ : 0 < σ2) :
    ∑ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
        (Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c)
      = σ2 + (Fintype.card A - 1) * ((Fintype.card T * α2 + γ2) * σ2
            / (Fintype.card T * α2 + γ2 + σ2))
        + (Fintype.card T - 1) * ((Fintype.card A * β2 + γ2) * σ2
            / (Fintype.card A * β2 + γ2 + σ2))
        + (Fintype.card A - 1) * (Fintype.card T - 1) * (γ2 * σ2 / (γ2 + σ2)) := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have h1 : 0 < Fintype.card T * α2 + γ2 + σ2 := by positivity
  have h2 : 0 < Fintype.card A * β2 + γ2 + σ2 := by positivity
  have h3 : 0 < γ2 + σ2 := by positivity
  have hterm : ∀ c : A × T, Core.linMse (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c
      (Core.blupWeight (KBal α2 β2 γ2 σ2) (LBal α2 β2 γ2) c)
      = (σ2 + (Fintype.card A - 1) * ((Fintype.card T * α2 + γ2) * σ2
            / (Fintype.card T * α2 + γ2 + σ2))
        + (Fintype.card T - 1) * ((Fintype.card A * β2 + γ2) * σ2
            / (Fintype.card A * β2 + γ2 + σ2))
        + (Fintype.card A - 1) * (Fintype.card T - 1) * (γ2 * σ2 / (γ2 + σ2)))
        / (Fintype.card A * Fintype.card T) := by
    intro c
    have hcc : LBal α2 β2 γ2 c c = α2 + β2 + γ2 := by simp [LBal, levelCov_apply]
    rw [Core.linMse, hcc, blupWeight_KBal hα hβ hγ hσ, mulVec_layer, LBal_eq_layer,
      layer_dotProduct_layer, layer_dotProduct_layer]
    simp only [zRow, zCol, zCell]
    field_simp
    ring
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
    Nat.cast_mul]
  field_simp

/-! #### Equicorrelated noise

The noise of the thesis simulation study, `Σ = σ²((1 - ρ)I + ρ11ᵀ)`, is `σ²(1 - ρ)I` plus a
term common to all cells, which cancels in every contrast. -/

/-- `K` of the balanced table with equicorrelated noise `σ²((1 - ρ)I + ρ11ᵀ)`. -/
noncomputable def KBalρ (α2 β2 γ2 σ2 ρ : ℝ) : Matrix (A × T) (A × T) ℝ :=
  K Prod.fst Prod.snd α2 β2 γ2 (σ2 • ((1 - ρ) • (1 : Matrix (A × T) (A × T) ℝ) + ρ • vecMulVec 1 1))

lemma KBalρ_eq (α2 β2 γ2 σ2 ρ : ℝ) :
    (KBalρ α2 β2 γ2 σ2 ρ : Matrix (A × T) (A × T) ℝ)
      = KBal α2 β2 γ2 (σ2 * (1 - ρ)) + (σ2 * ρ) • vecMulVec 1 1 := by
  ext p q
  simp only [KBalρ, KBal, K, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `K ≻ 0` for `0 ≤ ρ < 1`. -/
theorem KBalρ_posDef {α2 β2 γ2 σ2 ρ : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2)
    (hσ : 0 < σ2) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    (KBalρ α2 β2 γ2 σ2 ρ : Matrix (A × T) (A × T) ℝ).PosDef := by
  rw [KBalρ_eq]
  have h1' : (vecMulVec (1 : A × T → ℝ) 1).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (1 : A × T → ℝ)
  exact (K_posDef _ _ hα hβ hγ (PosDef.one.smul (mul_pos hσ (sub_pos.mpr h1)))).add_posSemidef
    (h1'.smul (mul_nonneg hσ.le h0))

/-- **The crossed formula with equicorrelated noise**: the same weights, with `σ²(1 - ρ)` in place
of `σ²` (`notes/crossed-2x2.md` §5). Positive correlation raises all three factors: common
noise cancels in every contrast. Any `ρ` for which `K ≻ 0`. -/
theorem blupWeight_KBalρ [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 ρ : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2 * (1 - ρ))
    (hK : (KBalρ α2 β2 γ2 σ2 ρ : Matrix (A × T) (A × T) ℝ).PosDef) (c : A × T) :
    Core.blupWeight (KBalρ α2 β2 γ2 σ2 ρ) (LBal α2 β2 γ2) c
      = Core.blupWeight (KBal α2 β2 γ2 (σ2 * (1 - ρ))) (LBal α2 β2 γ2) c := by
  rw [KBalρ_eq] at hK ⊢
  exact Core.blupWeight_add_rankOne (K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)) _ hK _ c

/-- …so `blup_balanced` holds with `σ²(1 - ρ)`. -/
theorem blup_balancedρ [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 ρ : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2 * (1 - ρ))
    (hK : (KBalρ α2 β2 γ2 σ2 ρ : Matrix (A × T) (A × T) ℝ).PosDef) (x : A × T → ℝ) (c : A × T) :
    Core.blupWeight (KBalρ α2 β2 γ2 σ2 ρ) (LBal α2 β2 γ2) c ⬝ᵥ x
      = (∑ p, x p) / (Fintype.card A * Fintype.card T)
        + zRow T α2 γ2 (σ2 * (1 - ρ)) * ((∑ t, x (c.1, t)) / Fintype.card T
            - (∑ p, x p) / (Fintype.card A * Fintype.card T))
        + zCol A β2 γ2 (σ2 * (1 - ρ)) * ((∑ a, x (a, c.2)) / Fintype.card A
            - (∑ p, x p) / (Fintype.card A * Fintype.card T))
        + zCell γ2 (σ2 * (1 - ρ)) * (x c - (∑ t, x (c.1, t)) / Fintype.card T
            - (∑ a, x (a, c.2)) / Fintype.card A
            + (∑ p, x p) / (Fintype.card A * Fintype.card T)) := by
  rw [blupWeight_KBalρ hα hβ hγ hσ hK, blup_balanced hα hβ hγ hσ]

/-- …and the blend's excess is that of `sum_linMse_blend` with `σ²(1 - ρ)`: the common noise
costs every unbiased rule the same. -/
theorem sum_linMse_blendρ [Nonempty A] [Nonempty T] {α2 β2 γ2 σ2 ρ : ℝ} (hα : 0 ≤ α2)
    (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2) (hσ : 0 < σ2 * (1 - ρ))
    (hK : (KBalρ α2 β2 γ2 σ2 ρ : Matrix (A × T) (A × T) ℝ).PosDef) (z : ℝ) :
    ∑ c : A × T, Core.linMse (KBalρ α2 β2 γ2 σ2 ρ) (LBal α2 β2 γ2) c
        (Core.blendWeight (KBalρ α2 β2 γ2 σ2 ρ) c z)
      = ∑ c : A × T, Core.linMse (KBalρ α2 β2 γ2 σ2 ρ) (LBal α2 β2 γ2) c
          (Core.blupWeight (KBalρ α2 β2 γ2 σ2 ρ) (LBal α2 β2 γ2) c)
        + ((Fintype.card A - 1) * (Fintype.card T * α2 + γ2 + σ2 * (1 - ρ))
            * (z - zRow T α2 γ2 (σ2 * (1 - ρ))) ^ 2
          + (Fintype.card T - 1) * (Fintype.card A * β2 + γ2 + σ2 * (1 - ρ))
            * (z - zCol A β2 γ2 (σ2 * (1 - ρ))) ^ 2
          + (Fintype.card A - 1) * (Fintype.card T - 1) * (γ2 + σ2 * (1 - ρ))
            * (z - zCell γ2 (σ2 * (1 - ρ))) ^ 2) := by
  have hK0 : (KBal α2 β2 γ2 (σ2 * (1 - ρ)) : Matrix (A × T) (A × T) ℝ).PosDef :=
    K_posDef _ _ hα hβ hγ (PosDef.one.smul hσ)
  have hK' := hK
  rw [KBalρ_eq] at hK'
  have hb : ∀ c : A × T, Core.blendWeight (KBalρ α2 β2 γ2 σ2 ρ) c z
      = Core.blendWeight (KBal α2 β2 γ2 (σ2 * (1 - ρ))) c z := fun c => by
    rw [Core.blendWeight, Core.blendWeight, KBalρ_eq, Core.glsWeight_add_rankOne hK0 _ hK']
  have hsb : ∀ c : A × T, ∑ i, Core.blendWeight (KBal α2 β2 γ2 (σ2 * (1 - ρ))) c z i = 1 :=
    fun c => by
      have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
      have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
      rw [blendWeight_KBal hα hβ hγ hσ, sum_layer]; field_simp; ring
  simp only [hb, blupWeight_KBalρ hα hβ hγ hσ hK]
  rw [KBalρ_eq]
  simp only [Core.linMse_add_rankOne, hsb, Core.sum_blupWeight hK0, Finset.sum_add_distrib]
  rw [sum_linMse_blend hα hβ hγ hσ]
  ring

end Balanced

/-! ### A cell without data

The level of a cell `(a, t)` with no data of its own still has covariance with the data
through its row and its column: `Cov(Xⱼ, μₐₜ) = α²[row j = a] + β²[col j = t]` (the cell
effect `Cₐₜ` is seen nowhere). The best predictor (`Core.blup`, `X = 1`, `x₀ = 1`) uses it; a
blend has no `Xₐₜ` to blend and can only return the collective mean. -/

/-- The covariance of the data with the level of a cell `(a, t)` that has no data:
`α²·[row j = a] + β²·[col j = t]`. -/
def cellCov (a : A) (t : T) (α2 β2 : ℝ) : n → ℝ := fun j =>
  α2 * (if row j = a then 1 else 0) + β2 * (if col j = t then 1 else 0)

/-- The 2×2 table without its first cell: the observed cells are the one in the same row
(`0`), the one in the same column (`1`) and the opposite one (`2`). -/
def missRow : Fin 3 → Fin 2 := ![0, 1, 1]

/-- …and their columns. -/
def missCol : Fin 3 → Fin 2 := ![1, 0, 1]

/-- **A cell without data, 2×2 table.** Drop cell `(0, 0)` and predict its level from the
other three. With `s = γ² + σ²` and `D = 4α²β² + 4(α² + β²)s + 3s²`, the best linear
unbiased predictor has the weights

  same row `(4α²β² + 4α²s + s²)/D`, same column `(4α²β² + 4β²s + s²)/D`,
  opposite cell `(s² - 4α²β²)/D`:

the additive relativity `same row + same column - opposite`, shrunk. As `s → 0` the weights
tend to `(1, 1, -1)`; the opposite cell gets a negative weight as soon as `4α²β² > s²`. -/
theorem missing_blup {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2)
    (hσ : 0 < σ2) :
    Core.blup (K missRow missCol α2 β2 γ2 (σ2 • 1)) (Unequal.onesCol (Fin 3))
        (cellCov missRow missCol 0 0 α2 β2) 1
      = ![(4 * α2 * β2 + 4 * α2 * (γ2 + σ2) + (γ2 + σ2) ^ 2)
            / (4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2),
          (4 * α2 * β2 + 4 * β2 * (γ2 + σ2) + (γ2 + σ2) ^ 2)
            / (4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2),
          ((γ2 + σ2) ^ 2 - 4 * α2 * β2)
            / (4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2)] := by
  have hK := K_posDef missRow missCol hα hβ hγ (PosDef.one.smul hσ)
  have hs : 0 < γ2 + σ2 := by positivity
  have hD : 0 < 4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2 := by positivity
  symm
  refine Core.eq_blup_of_normal hK Unequal.onesCol_injective _ 1
    (c := fun _ => (γ2 + σ2) * (2 * α2 + γ2 + σ2) * (2 * β2 + γ2 + σ2)
      / (4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2)) ?_ ?_
  · funext i
    fin_cases i <;>
      simp [K, mulVec, dotProduct, Fin.sum_univ_three, levelCov_apply, cellCov, missRow,
        missCol, Unequal.onesCol, Matrix.one_apply] <;>
      field_simp <;> ring
  · funext u
    simp [mulVec, dotProduct, Fin.sum_univ_three, Unequal.onesCol]
    field_simp
    ring

/-- …and its mean squared error is `γ² + s(12α²β² + 4(α² + β²)s + s²)/D`: the cell effect
`γ²`, which no data see, plus the price of predicting row and column effects
(`notes/crossed-2x2.md` §4: `3.575` against `4.814` for the collective mean alone). -/
theorem missing_predMse {α2 β2 γ2 σ2 : ℝ} (hα : 0 ≤ α2) (hβ : 0 ≤ β2) (hγ : 0 ≤ γ2)
    (hσ : 0 < σ2) :
    Core.predMse (K missRow missCol α2 β2 γ2 (σ2 • 1)) (cellCov missRow missCol 0 0 α2 β2)
        (α2 + β2 + γ2)
        (Core.blup (K missRow missCol α2 β2 γ2 (σ2 • 1)) (Unequal.onesCol (Fin 3))
          (cellCov missRow missCol 0 0 α2 β2) 1)
      = γ2 + (γ2 + σ2) * (12 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + (γ2 + σ2) ^ 2)
          / (4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2) := by
  have hD : 0 < 4 * α2 * β2 + 4 * (α2 + β2) * (γ2 + σ2) + 3 * (γ2 + σ2) ^ 2 := by
    have : 0 < γ2 + σ2 := by positivity
    positivity
  rw [missing_blup hα hβ hγ hσ]
  simp [Core.predMse, K, mulVec, dotProduct, Fin.sum_univ_three, levelCov_apply, cellCov,
    missRow, missCol, Matrix.one_apply]
  field_simp
  ring

end Crossed
end Credibility
