import Credibility.CrossedPoolWeights
import Credibility.Hierarchical

/-!
# Group levels: the best pool of pair estimators for `φτ²` (moment layer, distribution-free)

PLAN G4, the open half. With group levels (`Hierarchical.lean`, Bridge 5) the pair estimator
`P̂ᵢⱼ` has mean `2(1-φ)τ² + 2φτ²·[g(i) ≠ g(j)]`: the pairs follow a linear model with design
`xₚ = (2, 2·[across])` and parameter `β = ((1-φ)τ², φτ²)`. A pool `Σₚ cₚP̂ₚ` over all pairs is
unbiased for `φτ²` for every `τ²`, `φ` exactly when `Σₚ cₚ = 0` and `Σ_across cₚ = ½`
(`Blup.unbiased_iff`; one direction is `phiTauPooled_unbiasedG`, here `pairPool_unbiasedG`).

Which such pool has the least variance? The pair estimators are quadratic forms in the cells, so
`Var(Σₚ cₚP̂ₚ) = cᵀVc` with `V` their covariance table (`variance_pairPool`, moments up to order
four). Minimising `cᵀVc` under the design constraint `Xᵀc = x₀` is Gauss–Markov, the target-free
case of the best linear unbiased predictor (`Blup.blup_optimal` with `ℓ = 0`, `v = 0`):

* `pairPool_blue_optimal`: for any set of pairs and any design, the pool with the weights
  `V⁻¹X(XᵀV⁻¹X)⁻¹x₀` has the least variance among the pools with `Xᵀc = x₀`. With one class
  (`X = 1`) this is `pairPool_gls_optimal`;
* `phiTauPool_blue_optimal`: the group case. One within-group pair and one across-group pair
  make the design of full rank (`groupDesign_injective`).

The same weights with `x₀ = (1, 0)` or `(1, 1)` give the best pools for `(1-φ)τ²` and `τ²`.
The table `V` depends on the unknown moments, so a fit plugs in estimates (a first pass with
any unbiased weights, e.g. `phiTauPooled_unbiasedG` with volume weights); with weights from the
data the pool is no longer exactly unbiased.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]

/-- The design of a pair pool over `S` as a matrix: row `p` is `Xd p`. -/
def pairDesign {q : Type*} (S : Finset (J × J)) (Xd : J × J → q → ℝ) : Matrix S q ℝ :=
  Matrix.of fun p k => Xd p.1 k

/-- The Gauss–Markov weights on the pair covariance table for the design `Xd` and target
`x₀ᵀβ`, as weights on all pairs (zero outside `S`). -/
noncomputable def pairBLUE {q : Type*} [Fintype q] [DecidableEq q] (w : J → T → ℝ)
    (S : Finset (J × J)) (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ)
    (κ₃ : J × T → J × T → J × T → ℝ) (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (Xd : J × J → q → ℝ) (x₀ : q → ℝ) (p : J × J) : ℝ :=
  if h : p ∈ S then Core.blup (pairCovTable w S C m κ₃ κ₄) (pairDesign S Xd) 0 x₀ ⟨p, h⟩ else 0

omit [Fintype J] [DecidableEq J] in
lemma transpose_pairDesign_mulVec {q : Type*} (S : Finset (J × J)) (Xd : J × J → q → ℝ)
    (b : J × J → ℝ) (k : q) :
    ((pairDesign S Xd)ᵀ *ᵥ fun p : S => b p.1) k = ∑ p ∈ S, b p * Xd p k := by
  simp only [mulVec, dotProduct, transpose_apply, pairDesign, of_apply]
  rw [← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The minimum-variance unbiased pool for a design is Gauss–Markov on the pair covariance
table.** If the pair estimators of `S` have means `Xd p ⬝ β`, the pools unbiased for `x₀ᵀβ` are
those with `Σₚ bₚXd p = x₀`; among them the weights `V⁻¹X(XᵀV⁻¹X)⁻¹x₀` (`pairBLUE`) have the
least variance, for any random cells with these moment tables (distribution-free). -/
theorem pairPool_blue_optimal {q : Type*} [Fintype q] [DecidableEq q] (w : J → T → ℝ)
    (S : Finset (J × J)) (Z : J × T → Ω → ℝ)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hV : (pairCovTable w S C m κ₃ κ₄).PosDef) (Xd : J × J → q → ℝ)
    (hX : Function.Injective (pairDesign S Xd).mulVec) (x₀ : q → ℝ)
    (b : J × J → ℝ) (hb : ∀ k, ∑ p ∈ S, b p * Xd p k = x₀ k) :
    Var[fun ω => pairPool w S (pairBLUE w S C m κ₃ κ₄ Xd x₀) (Z · ω); P]
      ≤ Var[fun ω => pairPool w S b (Z · ω); P] := by
  rw [variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4,
    variance_pairPool w S Z C m κ₃ κ₄ hZ hm hc h3 h4]
  have hg : (fun p : S => pairBLUE w S C m κ₃ κ₄ Xd x₀ p.1)
      = Core.blup (pairCovTable w S C m κ₃ κ₄) (pairDesign S Xd) 0 x₀ := by
    ext p; simp [pairBLUE, p.2]
  have hd : (pairDesign S Xd)ᵀ *ᵥ (fun p : S => b p.1) = x₀ :=
    funext fun k => by rw [transpose_pairDesign_mulVec]; exact hb k
  have h := Core.blup_optimal hV hX 0 0 x₀ hd
  simp only [Core.predMse, dotProduct_zero, mul_zero, sub_zero, add_zero] at h
  rw [hg]
  exact h

/-! ### The group case -/

variable {G : Type*} [DecidableEq G] (grp : J → G)

/-- The design of the pair estimators with group levels: `xₚ = (2, 2·[g(i) ≠ g(j)])`, for the
parameter `((1-φ)τ², φτ²)`. -/
def groupDesign (p : J × J) : Fin 2 → ℝ := ![2, 2 * if grp p.1 = grp p.2 then 0 else 1]

omit [Fintype J] [DecidableEq J] in
/-- With one pair within a group and one across groups (in `S`), the group design has full
column rank. -/
theorem groupDesign_injective {S : Finset (J × J)} {i j k l : J} (hij : (i, j) ∈ S)
    (hg : grp i = grp j) (hkl : (k, l) ∈ S) (hg' : grp k ≠ grp l) :
    Function.Injective (pairDesign S (groupDesign grp)).mulVec := by
  intro β₁ β₂ hβ
  have h : ∀ p : S, (pairDesign S (groupDesign grp) *ᵥ (β₁ - β₂)) p = 0 := fun p => by
    rw [mulVec_sub, hβ, sub_self, Pi.zero_apply]
  have h1 := h ⟨(i, j), hij⟩
  have h2 := h ⟨(k, l), hkl⟩
  simp only [mulVec, dotProduct, pairDesign, groupDesign, of_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, hg, hg', ite_true, ite_false, Pi.sub_apply] at h1 h2
  funext r
  fin_cases r <;> simp <;> linarith

/-- **The best pool of pair estimators for `φτ²`.** Over all ordered pairs `i ≠ j`, the pools
unbiased for `φτ²` are those with `Σₚ bₚ = 0` and `Σ_across bₚ = ½`; with a pair of each kind,
the Gauss–Markov weights on the pair covariance table have the least variance among them, for
any random cells with these moment tables (distribution-free). -/
theorem phiTauPool_blue_optimal (w : J → T → ℝ) (Z : J × T → Ω → ℝ)
    (C : Matrix (J × T) (J × T) ℝ) (m : J × T → ℝ) (κ₃ : J × T → J × T → J × T → ℝ)
    (κ₄ : J × T → J × T → J × T → J × T → ℝ)
    (hZ : ∀ i, MemLp (Z i) 4 P) (hm : ∀ i, ∫ ω, Z i ω ∂P = m i)
    (hc : ∀ i j, covariance (Z i) (Z j) P = C i j)
    (h3 : ∀ i j k, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) ∂P = κ₃ i j k)
    (h4 : ∀ i j k l, ∫ ω, (Z i ω - m i) * (Z j ω - m j) * (Z k ω - m k) * (Z l ω - m l) ∂P
      = κ₄ i j k l + C i j * C k l + C i k * C j l + C i l * C j k)
    (hV : (pairCovTable w univ.offDiag C m κ₃ κ₄).PosDef) {i j k l : J} (hij : i ≠ j)
    (hg : grp i = grp j) (hkl : k ≠ l) (hg' : grp k ≠ grp l) (b : J × J → ℝ)
    (hb0 : ∑ p ∈ univ.offDiag, b p = 0)
    (hb1 : ∑ p ∈ univ.offDiag with grp p.1 ≠ grp p.2, b p = 1 / 2) :
    Var[fun ω => pairPool w univ.offDiag
        (pairBLUE w univ.offDiag C m κ₃ κ₄ (groupDesign grp) ![0, 1]) (Z · ω); P]
      ≤ Var[fun ω => pairPool w univ.offDiag b (Z · ω); P] := by
  refine pairPool_blue_optimal w _ Z C m κ₃ κ₄ hZ hm hc h3 h4 hV _
    (groupDesign_injective grp (by simp [hij]) hg (by simp [hkl]) hg') _ b fun r => ?_
  fin_cases r
  · simp only [groupDesign, Matrix.cons_val_zero, Fin.zero_eta]
    rw [← Finset.sum_mul, hb0, zero_mul]
  · simp only [groupDesign, Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_zero]
    calc ∑ p ∈ univ.offDiag, b p * (2 * if grp p.1 = grp p.2 then 0 else 1)
        = 2 * ∑ p ∈ univ.offDiag with grp p.1 ≠ grp p.2, b p := by
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : grp p.1 = grp p.2
          · simp [h]
          · simp [h]; ring
      _ = 1 := by rw [hb1]; norm_num

end Model
end Credibility
