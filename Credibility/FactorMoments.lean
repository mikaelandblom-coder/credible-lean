import Credibility.BlupMoments
import Credibility.Factor

/-!
# The moment layer for the common factor model (extension, distribution-free)

`Factor.lean` takes the table `cov(Xᵢₜ, Xⱼₛ)` as given numbers. Here the cells are random:
**any** square-integrable `X_{(j,t)}` over all months, past and future, with fixed-effect
means `E X = Dβ` (a design `D` over all cells: one common mean, a season, …) and covariances
given by a table (`Factor.Cells`). For observed cells `c` and the target `Y = Σₜ bₜX_{j₀t}`
they form a `Core.Target` (`Cells.toTarget`): `K`, `ℓ = Cov(x, Y)` and `v = Var Y` are the
actual moments, and the target mean is `x₀ = Σₜ bₜD_{(j₀,t)}` (`targetMean`).

So for the common factor model (`Factor.obsCov`) `Factor.K`, `Factor.ell`, `Factor.var` are
the actual covariances, and `Core.blup` minimises the true mean squared error
(`Cells.blup_mse_optimal`, `Cells.mse_blup`); likewise with per-card dynamics
(`Factor.obsCovG`: `Cells.blupG_mse_optimal`). No distribution is assumed.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Factor

variable {Ω : Type*} [MeasurableSpace Ω] {J T q : Type*} [Fintype q]

/-- Random cells over all months, past and future, under `P`: square integrable, with means
`E X = Dβ` and covariances `cov(Xᵢₜ, Xⱼₛ) = tab i j t s`. Only moments are assumed. -/
structure Cells (tab : J → J → T → T → ℝ) (D : Matrix (J × T) q ℝ) (β : q → ℝ)
    (P : Measure Ω) where
  /-- The cell `X_{(j,t)}`. -/
  X : J × T → Ω → ℝ
  memLp : ∀ p, MemLp (X p) 2 P
  mean : ∀ p, P[X p] = (D *ᵥ β) p
  cov : ∀ p r, cov[X p, X r; P] = tab p.1 r.1 p.2 r.2

/-- The mean of the target `Σₜ bₜX_{j₀t}`: `x₀ = Σₜ bₜD_{(j₀,t)}`. -/
def targetMean [Fintype T] (D : Matrix (J × T) q ℝ) (j₀ : J) (b : T → ℝ) : q → ℝ :=
  fun k => ∑ t, b t * D (j₀, t) k

namespace Cells

variable [Fintype T] {tab : J → J → T → T → ℝ} {D : Matrix (J × T) q ℝ} {β : q → ℝ}
  {P : Measure Ω} (C : Cells tab D β P)

/-- The target `Y = Σₜ bₜX_{j₀t}` (`bₜ = 1` on the next 12 months). -/
noncomputable def target (j₀ : J) (b : T → ℝ) : Ω → ℝ := Core.portLin (fun t => C.X (j₀, t)) b

variable [IsProbabilityMeasure P] {n : Type*} [Fintype n]

/-- **The cells are a `Core.Target`**: observed cells `c` and the target `Σₜ bₜX_{j₀t}` have
`K = (tab)` on the cells, `ℓ_p = Σₜ bₜ tab(c p, (j₀,t))` and `v = Σₜₛ bₜbₛ tab(j₀,j₀,t,s)`. -/
noncomputable def toTarget (c : n → J × T) (j₀ : J) (b : T → ℝ) :
    Core.Target (of fun p r => tab (c p).1 (c r).1 (c p).2 (c r).2)
      (fun p => ∑ t, b t * tab (c p).1 j₀ (c p).2 t) (∑ t, ∑ s, b t * b s * tab j₀ j₀ t s)
      (D.submatrix c id) (targetMean D j₀ b) β P where
  x p := C.X (c p)
  Y := C.target j₀ b
  x_memLp p := C.memLp (c p)
  Y_memLp := memLp_finsetSum _ fun t _ => (C.memLp (j₀, t)).const_mul (b t)
  x_mean p := by rw [C.mean]; rfl
  Y_mean := by
    unfold target Core.portLin
    rw [integral_finsetSum _ fun t _ => ((C.memLp (j₀, t)).const_mul (b t)).integrable
      (by norm_num)]
    simp only [integral_const_mul, C.mean, targetMean, mulVec, dotProduct, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun t _ => by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  cov_x p r := by rw [C.cov]; rfl
  cov_x_Y p := by
    unfold target Core.portLin
    beta_reduce
    rw [covariance_fun_sum_right
      (fun t => (C.memLp (j₀, t)).const_mul (b t)) (C.memLp (c p))]
    simp only [covariance_const_mul_right]
    exact sum_congr rfl fun t _ => by rw [C.cov]
  var_Y := by
    have hY : MemLp (C.target j₀ b) 2 P :=
      memLp_finsetSum _ fun t _ => (C.memLp (j₀, t)).const_mul (b t)
    rw [← covariance_self hY.aestronglyMeasurable.aemeasurable]
    unfold target Core.portLin
    rw [covariance_fun_sum_fun_sum (fun t => (C.memLp (j₀, t)).const_mul (b t))
      (fun s => (C.memLp (j₀, s)).const_mul (b s))]
    simp only [covariance_const_mul_left, covariance_const_mul_right, C.cov]
    exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

end Cells

/-! ### The common factor model: true mean squared error -/

namespace Cells

variable [DecidableEq J] [DecidableEq T] [Fintype J] [Fintype T] [DecidableEq q]
  {D : Matrix (J × T) q ℝ} {β : q → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {n : Type*} [Fintype n] [DecidableEq n] {M : Factor J T}

/-- **The best linear unbiased predictor in true MSE** under the common factor model:
`Core.blup` for `Factor.K`, `Factor.ell` minimises `E(dᵀx - Y)²` among all `d` unbiased for
the design (`(D on the cells)ᵀd = Σₜ bₜD_{(j₀,t)}`), for every distribution with these
moments. -/
theorem blup_mse_optimal (C : Cells M.obsCov D β P) {c : n → J × T} (hc : Function.Injective c)
    (hX : Function.Injective (D.submatrix c id).mulVec) (j₀ : J) (b : T → ℝ) {d : n → ℝ}
    (hd : (D.submatrix c id)ᵀ *ᵥ d = targetMean D j₀ b) :
    P[fun ω => (Core.portLin (fun p => C.X (c p))
        (Core.blup (M.K c) (D.submatrix c id) (M.ell c j₀ b) (targetMean D j₀ b)) ω
          - C.target j₀ b ω) ^ 2]
      ≤ P[fun ω => (Core.portLin (fun p => C.X (c p)) d ω - C.target j₀ b ω) ^ 2] :=
  (C.toTarget c j₀ b).blup_mse_optimal (M.K_posDef hc) hX hd

/-- **Its true error** `v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r` for `Factor.K`, `Factor.ell`,
`Factor.var`. -/
theorem mse_blup (C : Cells M.obsCov D β P) {c : n → J × T} (hc : Function.Injective c)
    (hX : Function.Injective (D.submatrix c id).mulVec) (j₀ : J) (b : T → ℝ) :
    P[fun ω => (Core.portLin (fun p => C.X (c p))
        (Core.blup (M.K c) (D.submatrix c id) (M.ell c j₀ b) (targetMean D j₀ b)) ω
          - C.target j₀ b ω) ^ 2]
      = M.var j₀ b - M.ell c j₀ b ⬝ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b)
        + (targetMean D j₀ b - (D.submatrix c id)ᵀ *ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b))
          ⬝ᵥ (((D.submatrix c id)ᵀ * (M.K c)⁻¹ * D.submatrix c id)⁻¹
            *ᵥ (targetMean D j₀ b - (D.submatrix c id)ᵀ *ᵥ ((M.K c)⁻¹ *ᵥ M.ell c j₀ b))) :=
  (C.toTarget c j₀ b).mse_blup (M.K_posDef hc) hX

/-- **With per-card dynamics** (`Factor.obsCovG`, e.g. per-card AR(1)): `Core.blup` for
`Factor.KG`, `Factor.ellG` minimises the true mean squared error. -/
theorem blupG_mse_optimal {G : J → Matrix T T ℝ} (hG : ∀ j, (G j).PosSemidef)
    (C : Cells (M.obsCovG G) D β P) {c : n → J × T} (hc : Function.Injective c)
    (hX : Function.Injective (D.submatrix c id).mulVec) (j₀ : J) (b : T → ℝ) {d : n → ℝ}
    (hd : (D.submatrix c id)ᵀ *ᵥ d = targetMean D j₀ b) :
    P[fun ω => (Core.portLin (fun p => C.X (c p))
        (Core.blup (M.KG c G) (D.submatrix c id) (M.ellG c G j₀ b) (targetMean D j₀ b)) ω
          - C.target j₀ b ω) ^ 2]
      ≤ P[fun ω => (Core.portLin (fun p => C.X (c p)) d ω - C.target j₀ b ω) ^ 2] :=
  (C.toTarget c j₀ b).blup_mse_optimal (M.KG_posDef hc hG) hX hd

end Cells

end Factor
end Credibility
