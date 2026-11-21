import Credibility.Factor
import Credibility.CoreVector

/-!
# Frequency × severity with a factor table per component (extension, `notes/card-data.md` Step 6)

Each component `p ∈ P` (`P = {F, Y}`: claim frequency and mean severity) has its own Step 3
table `(comp p).obsCov` (`Factor`): frequency cells `Nⱼₜ/wⱼₜ` with volumes `w` = cards,
severity cells `Sⱼₜ/Nⱼₜ` with volumes = claim counts, each with its own loadings, factor `Γ`,
shock, process noise and level variance `τₚ²`. Across components, cells have any covariance:
a level covariance `levelCross p q` (a card's frequency and severity levels) and the rest
`cross p q i k t s` (a common factor with loadings `λ_F`, `λ_Y`, a joint shock, …).

Cohort estimates `μ̂ⱼₚ = Σₜ αₚⱼₜXⱼₚₜ` (`Σₜ αₚⱼₜ = 1`) give the joint `K` over cohorts × `P`
(`K`), and the level vector `μⱼ = (μⱼ_F, μⱼ_Y)` the joint `L` (`L`): the `CoreVector`
setting. So all of `CoreVector` applies; what is new here is only:

* each component's `K` is that of its own table, and is `≻ 0` (`component_K_posDef`);
* with no cross-component covariance the joint `K` is `≻ 0` (`K_posDef_of_separate`, via the
  general `CoreVector.posDef_of_componentBlockDiag`), and **joint = separate**: the vector
  BLUP is the scalar BLUP of each component on its own data (`blupW_eq_separate`, from
  `CoreVector.blupW_eq_sepW_of_componentBlockDiag`);
* the converse fails (Finding 32): with a Kronecker structure `K = K_c ⊗ S`, `L = L_c ⊗ S`
  (the same cohort structure in both components, any cross-component covariance `S`) joint is
  still separate (`CoreVector.blupW_kronecker`, Zellner's seemingly unrelated regressions with
  identical regressors). So "do the residuals cross-correlate?" is sufficient, not necessary.

All second moments are given numbers; distribution-free.
-/

open Finset Matrix

namespace Credibility

/-! ### A general lemma: block diagonal over components -/

namespace CoreVector

variable {J P : Type*} [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P]

omit [DecidableEq J] in
/-- **Block diagonal over components with positive definite blocks is positive definite.** -/
theorem posDef_of_componentBlockDiag {M : Matrix (J × P) (J × P) ℝ}
    (hM : IsComponentBlockDiag M) (hc : ∀ p, (component M p).PosDef) : M.PosDef := by
  have hsplit : ∀ x : J × P → ℝ, star x ⬝ᵥ (M *ᵥ x)
      = ∑ p, star (fun i => x (i, p)) ⬝ᵥ (component M p *ᵥ fun i => x (i, p)) := by
    intro x
    simp only [star_trivial, dotProduct, mulVec, component, Fintype.sum_prod_type]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => sum_congr rfl fun i _ => ?_
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single p (fun q _ hq => by rw [hM i k p q (Ne.symm hq), zero_mul])
      (by simp)]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext ⟨i, p⟩ ⟨k, q⟩
    simp only [conjTranspose_apply, star_trivial]
    by_cases hpq : p = q
    · subst hpq
      have := (hc p).1.apply i k
      simpa [component] using this
    · rw [hM i k p q hpq, hM k i q p (Ne.symm hpq)]
  · rw [hsplit]
    obtain ⟨⟨i, p⟩, hip⟩ : ∃ y, x y ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    refine sum_pos' (fun q _ => ?_) ⟨p, mem_univ _, ?_⟩
    · exact (hc q).posSemidef.dotProduct_mulVec_nonneg _
    · refine (hc p).dotProduct_mulVec_pos fun h => hip ?_
      exact congrFun h i

/-- **Joint = separate does not need block diagonality** (Finding 32). With the same cohort
structure in every component, `K = K_c ⊗ S` and `L = L_c ⊗ S` for any `S`, the vector BLUP
predicts each component by the scalar BLUP `Core.blupWeight K_c L_c` of that component's data
alone, whatever the cross-component covariance `S` (Zellner 1962: seemingly unrelated
regressions with identical regressors are OLS). -/
theorem blupW_kronecker [Nonempty J] {Kc Lc : Matrix J J ℝ} {S : Matrix P P ℝ}
    (hK : (kroneckerMap (· * ·) Kc S).PosDef) (hKc : Kc.PosDef) (hL : Lcᵀ = Lc) (j : J) :
    blupW (kroneckerMap (· * ·) Kc S) (kroneckerMap (· * ·) Lc S) j
      = sepW fun _ => Core.blupWeight Kc Lc j := by
  set c : ℝ := (1 - 1 ⬝ᵥ (Kc⁻¹ *ᵥ Lc j)) * (invTotal Kc)⁻¹
  refine (eq_blupW_of_mul hK _ j (stack_transpose_mul_sepW fun _ =>
    Core.sum_blupWeight hKc _ j) (C := c • S) ?_).symm
  ext ⟨i, p⟩ q
  have h := Core.mulVec_blupWeight hKc Lc j i
  simp only [mulVec, dotProduct] at h
  have e : ∑ x : J × P, Kc i x.1 * S p x.2 * (if x.2 = q then Core.blupWeight Kc Lc j x.1 else 0)
      = S p q * ∑ k, Kc i k * Core.blupWeight Kc Lc j k := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single q (fun r _ hr => by simp [hr]) (by simp)]
    simp; ring
  have h' : ∑ k, Kc i k * Core.blupWeight Kc Lc j k - Lc j i = c :=
    Core.mulVec_blupWeight hKc Lc j i
  have hLs : Lc i j = Lc j i := by rw [← transpose_apply Lc j i, hL]
  simp only [Matrix.sub_apply, Matrix.mul_apply, kroneckerMap_apply, sepW, sel, stack,
    Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul] at e ⊢
  rw [e]
  simp [ite_and, hLs]
  rw [← h']; ring

end CoreVector

/-! ### The frequency × severity model -/

/-- Frequency × severity: a `Factor` table per component and any covariance across
components. -/
structure FreqSev (J T P : Type*) where
  /-- The Step 3 table of each component (volumes: cards for frequency, claims for
  severity). -/
  comp : P → Factor J T
  /-- The level covariance between components `p ≠ q` of the same cohort. -/
  levelCross : P → P → ℝ
  /-- Any further covariance between cells of components `p ≠ q` (a common factor, a joint
  shock, …). -/
  cross : P → P → J → J → T → T → ℝ

namespace FreqSev

variable {J T P : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] [Fintype P]
  [DecidableEq P] (M : FreqSev J T P)

/-- The level covariance `T₍ₚq₎` across components: `τₚ²` on the diagonal. -/
noncomputable def lev (p q : P) : ℝ := if p = q then (M.comp p).τ2 else M.levelCross p q

/-- The joint cell table: `(comp p).obsCov` within a component, `δᵢₖT_pq + cross` across. -/
noncomputable def tab (p q : P) (i k : J) (t s : T) : ℝ :=
  if p = q then (M.comp p).obsCov i k t s
  else M.levelCross p q * (if i = k then 1 else 0) + M.cross p q i k t s

/-- The joint `K = Cov(μ̂)` over cohorts × components of `μ̂ⱼₚ = Σₜ αₚⱼₜXⱼₚₜ`. -/
noncomputable def K (α : P → J → T → ℝ) : Matrix (J × P) (J × P) ℝ :=
  of fun x y => ∑ t, ∑ s, α x.2 x.1 t * α y.2 y.1 s * M.tab x.2 y.2 x.1 y.1 t s

/-- The joint `L = Cov(μ)` of the level vectors: `δᵢₖT_pq`. -/
noncomputable def L : Matrix (J × P) (J × P) ℝ :=
  of fun x y => if x.1 = y.1 then M.lev x.2 y.2 else 0

/-- No covariance between components. -/
def Separate : Prop := (∀ p q, p ≠ q → M.levelCross p q = 0) ∧
  (∀ p q, p ≠ q → ∀ i k t s, M.cross p q i k t s = 0)

/-- The weights of component `p` as a map from its cells to cohorts:
`(i, t) ↦ αₚᵢₜ` on cohort `i`. -/
def wMat (α : P → J → T → ℝ) (p : P) : Matrix (J × T) J ℝ :=
  of fun x k => if x.1 = k then α p k x.2 else 0

omit [Fintype P] in
/-- **Each component's `K` is that of its own table**:
`component K p = Aₚᵀ (comp p).K Aₚ`, the covariance of `μ̂ⱼₚ` under `(comp p).obsCov`. -/
theorem component_K (α : P → J → T → ℝ) (p : P) :
    CoreVector.component (M.K α) p = (wMat α p)ᵀ * (M.comp p).K id * wMat α p := by
  ext i k
  simp only [CoreVector.component, K, tab, of_apply, ite_true, Matrix.mul_apply,
    transpose_apply, wMat, Factor.K, id, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite,
    mul_zero, sum_mul]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  ring

omit [Fintype P] in
/-- **Each component's `K` is `≻ 0`** for weights summing to one per cohort. -/
theorem component_K_posDef {α : P → J → T → ℝ} (hα : ∀ p j, ∑ t, α p j t = 1) (p : P) :
    (CoreVector.component (M.K α) p).PosDef := by
  rw [component_K, ← conjTranspose_eq_transpose_of_trivial]
  refine PosDef.conjTranspose_mul_mul_same ((M.comp p).K_posDef Function.injective_id)
    fun x y hxy => funext fun k => ?_
  have h : ∀ t, α p k t * x k = α p k t * y k := fun t => by
    have := congrFun hxy (k, t)
    simpa [mulVec, dotProduct, wMat] using this
  have hx : x k = ∑ t, α p k t * x k := by rw [← sum_mul, hα, one_mul]
  have hy : y k = ∑ t, α p k t * y k := by rw [← sum_mul, hα, one_mul]
  rw [hx, hy]
  exact sum_congr rfl fun t _ => h t

variable {M}

omit [Fintype J] [Fintype P] in
/-- With no cross-component covariance, `K` has none either. -/
theorem isComponentBlockDiag_K (hs : M.Separate) (α : P → J → T → ℝ) :
    CoreVector.IsComponentBlockDiag (M.K α) := by
  intro i k p q hpq
  simp [K, tab, hpq, hs.1 p q hpq, hs.2 p q hpq]

omit [Fintype J] [Fintype T] [DecidableEq T] [Fintype P] in
/-- With no cross-component covariance, `L` has none either. -/
theorem isComponentBlockDiag_L (hs : M.Separate) : CoreVector.IsComponentBlockDiag M.L := by
  intro i k p q hpq
  simp [L, lev, hpq, hs.1 p q hpq]

omit [Fintype J] [Fintype T] [DecidableEq T] [Fintype P] in
/-- With no cross-component covariance, `L` is symmetric. -/
theorem L_transpose (hs : M.Separate) : M.Lᵀ = M.L := by
  ext x y
  simp only [transpose_apply, L, lev, of_apply, eq_comm (a := y.1), eq_comm (a := y.2)]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, hs.1 _ _ h, hs.1 _ _ (Ne.symm h)]

omit [Fintype J] [Fintype T] [DecidableEq T] [Fintype P] in
/-- Component `p` of `L` is `τₚ²I`: the level variance of its own table. -/
theorem component_L (p : P) : CoreVector.component M.L p = (M.comp p).τ2 • (1 : Matrix J J ℝ) := by
  ext i k
  by_cases h : i = k <;> simp [CoreVector.component, L, lev, h]

/-- **The joint `K` is `≻ 0`** with no cross-component covariance. -/
theorem K_posDef_of_separate (hs : M.Separate) {α : P → J → T → ℝ}
    (hα : ∀ p j, ∑ t, α p j t = 1) : (M.K α).PosDef :=
  CoreVector.posDef_of_componentBlockDiag (isComponentBlockDiag_K hs α) (M.component_K_posDef hα)

/-- **Joint = separate** (Q4): with no covariance between frequency and severity, the best
linear unbiased predictor of the level vector `(μⱼ_F, μⱼ_Y)` predicts each component by the
scalar BLUP of its own table alone (`K` of its cells, `L = τₚ²I`). -/
theorem blupW_eq_separate [Nonempty J] (hs : M.Separate) {α : P → J → T → ℝ}
    (hα : ∀ p j, ∑ t, α p j t = 1) (j : J) :
    CoreVector.blupW (M.K α) M.L j
      = CoreVector.sepW fun p => Core.blupWeight (CoreVector.component (M.K α) p)
          ((M.comp p).τ2 • (1 : Matrix J J ℝ)) j := by
  rw [CoreVector.blupW_eq_sepW_of_componentBlockDiag (K_posDef_of_separate hs hα)
    (isComponentBlockDiag_K hs α) (L_transpose hs) (isComponentBlockDiag_L hs) j]
  simp only [component_L]

end FreqSev
end Credibility
