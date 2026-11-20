import Credibility.Blup

/-!
# The moment layer for a general target with fixed effects (extension, distribution-free)

`Blup.lean` takes `K = Cov(x)`, `ℓ = Cov(x, Y)` and `v = Var Y` as given numbers. Here they
are actual moments: **any** square-integrable random cells `xᵢ` and target `Y` with means
`E x = Xβ`, `E Y = x₀ᵀβ` and these covariances (`Core.Target`). Then an unbiased linear
predictor `dᵀx` (`Xᵀd = x₀`) has true mean squared error `predMse K ℓ v d`, so `Core.blup`
is the best one for every distribution with these moments, with true error
`v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r`.

Unlike `Core.Estimates`, nothing ties `Cov(x, Y)` to `Var Y`: the noise in the cells may be
correlated with the target (a persistent common factor, `notes/card-data.md` Step 3).
`Core.Estimates` is the case `X = 1`, `Y = μⱼ` (`Core.Estimates.toTarget`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A linear portfolio estimate `Σⱼ dⱼ μ̂ⱼ` of cohort estimates `est`, with
arbitrary weights `d`. -/
noncomputable def portLin {J : Type*} [Fintype J] (est : J → Ω → ℝ) (d : J → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, d j * est j ω

variable {n q : Type*} [Fintype n] [Fintype q]

/-- Data cells `xᵢ` and a target `Y` under `P`: square integrable, with fixed-effect means
`E x = Xβ` and `E Y = x₀ᵀβ`, and second moments `cov(xᵢ, xⱼ) = Kᵢⱼ`, `cov(xᵢ, Y) = ℓᵢ`,
`Var Y = v`. Only moments are assumed, no distribution. -/
structure Target (K : Matrix n n ℝ) (ℓ : n → ℝ) (v : ℝ) (X : Matrix n q ℝ) (x₀ : q → ℝ)
    (β : q → ℝ) (P : Measure Ω) where
  /-- The data cell `xᵢ`. -/
  x : n → Ω → ℝ
  /-- The target `Y`. -/
  Y : Ω → ℝ
  x_memLp : ∀ i, MemLp (x i) 2 P
  Y_memLp : MemLp Y 2 P
  x_mean : ∀ i, P[x i] = (X *ᵥ β) i
  Y_mean : P[Y] = x₀ ⬝ᵥ β
  cov_x : ∀ i j, cov[x i, x j; P] = K i j
  cov_x_Y : ∀ i, cov[x i, Y; P] = ℓ i
  var_Y : Var[Y; P] = v

namespace Target

variable {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  {P : Measure Ω} (T : Target K ℓ v X x₀ β P)

lemma memLp_portLin (d : n → ℝ) : MemLp (portLin T.x d) 2 P :=
  memLp_finsetSum _ fun i _ => (T.x_memLp i).const_mul (d i)

variable [IsProbabilityMeasure P]

/-- `E(dᵀx) = (Xᵀd)ᵀβ`: unbiased for `Y` when `Xᵀd = x₀` (`Core.unbiased_iff`). -/
lemma integral_portLin (d : n → ℝ) : P[portLin T.x d] = (Xᵀ *ᵥ d) ⬝ᵥ β := by
  unfold portLin
  rw [integral_finsetSum _ fun i _ => ((T.x_memLp i).const_mul (d i)).integrable (by norm_num),
    mulVec_transpose, ← dotProduct_mulVec]
  simp [integral_const_mul, T.x_mean, dotProduct]

/-- `Var(dᵀx) = dᵀKd`. -/
lemma variance_portLin (d : n → ℝ) : Var[portLin T.x d; P] = d ⬝ᵥ (K *ᵥ d) := by
  rw [← covariance_self (T.memLp_portLin d).aestronglyMeasurable.aemeasurable]
  unfold portLin
  rw [covariance_fun_sum_fun_sum (fun i => (T.x_memLp i).const_mul (d i))
    (fun j => (T.x_memLp j).const_mul (d j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, T.cov_x,
    dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- `cov(dᵀx, Y) = dᵀℓ`. -/
lemma cov_portLin_Y (d : n → ℝ) : cov[portLin T.x d, T.Y; P] = d ⬝ᵥ ℓ := by
  rw [covariance_comm]
  unfold portLin
  rw [covariance_fun_sum_right (fun i => (T.x_memLp i).const_mul (d i)) T.Y_memLp]
  simp only [covariance_const_mul_right, dotProduct]
  exact sum_congr rfl fun i _ => by rw [covariance_comm, T.cov_x_Y]

/-- **The true mean squared error**: an unbiased linear predictor `dᵀx` (`Xᵀd = x₀`) of `Y`
has `E(dᵀx - Y)² = dᵀKd - 2dᵀℓ + v`, for every distribution with these moments. -/
theorem mse_portLin {d : n → ℝ} (hd : Xᵀ *ᵥ d = x₀) :
    P[fun ω => (portLin T.x d ω - T.Y ω) ^ 2] = predMse K ℓ v d := by
  have hp := T.memLp_portLin d
  have hl := T.Y_memLp
  have hD : MemLp (fun ω => portLin T.x d ω - T.Y ω) 2 P := hp.sub hl
  have hDm : P[fun ω => portLin T.x d ω - T.Y ω] = 0 := by
    rw [integral_sub (hp.integrable (by norm_num)) (hl.integrable (by norm_num)),
      integral_portLin, hd, T.Y_mean, sub_self]
  rw [← variance_of_integral_eq_zero hD.aestronglyMeasurable.aemeasurable hDm,
    variance_fun_sub hp hl, variance_portLin, cov_portLin_Y, T.var_Y, predMse]

variable [DecidableEq n] [DecidableEq q]

/-- **The best linear unbiased predictor in true MSE**: `Core.blup` minimises the actual mean
squared error among all unbiased `dᵀx`. -/
theorem blup_mse_optimal (hK : K.PosDef) (hX : Function.Injective X.mulVec) {d : n → ℝ}
    (hd : Xᵀ *ᵥ d = x₀) :
    P[fun ω => (portLin T.x (blup K X ℓ x₀) ω - T.Y ω) ^ 2]
      ≤ P[fun ω => (portLin T.x d ω - T.Y ω) ^ 2] := by
  rw [T.mse_portLin (transpose_mulVec_blup hK hX ℓ x₀), T.mse_portLin hd]
  exact blup_optimal hK hX ℓ v x₀ hd

/-- **Its true error**: `E(d*ᵀx - Y)² = v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r`, `r = x₀ - XᵀK⁻¹ℓ`. -/
theorem mse_blup (hK : K.PosDef) (hX : Function.Injective X.mulVec) :
    P[fun ω => (portLin T.x (blup K X ℓ x₀) ω - T.Y ω) ^ 2]
      = v - ℓ ⬝ᵥ (K⁻¹ *ᵥ ℓ)
        + (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ)) ⬝ᵥ ((Xᵀ * K⁻¹ * X)⁻¹ *ᵥ (x₀ - Xᵀ *ᵥ (K⁻¹ *ᵥ ℓ))) := by
  rw [T.mse_portLin (transpose_mulVec_blup hK hX ℓ x₀), predMse_blup hK hX]

end Target

end Core
end Credibility
