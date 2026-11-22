import Credibility.PlugIn

/-!
# The plug-in predictor under normal noise (distribution layer)

**Optional distribution layer** (owner, 2026-11-15): this file assumes *normal noise* (the data
and the target jointly Gaussian), so nothing in the core depends on it.

Kackar & Harville (1984): if the estimated weights `d̂(x)` are translation invariant
(`d̂(u + Xb) = d̂(u)`, as for quadratic fits on residuals) and unbiased for every data set
(`Xᵀd̂(u) = x₀`), the plug-in predictor loses against the best predictor `d*` exactly the mean
square of the difference of the two predictions:

`E(d̂ᵀx - Y)² = mse(d*) + E(d̂ᵀx - d*ᵀx)²`  (`plugIn_mse_of_normal`).

So under normal noise estimating `K` and `ℓ` can only cost (`plugIn_mse_ge_of_normal`).

Why: the difference `d̂ᵀx - d*ᵀx` depends on the data only through the residuals `Mx`,
`M = I - X(XᵀX)⁻¹Xᵀ`, and the best predictor's error `d*ᵀx - Y` is uncorrelated with them
(`Cov = M(Kd* - ℓ) = 0`, the first-order condition). Jointly normal and uncorrelated means
independent, so the cross term of `Target.integral_sq_plugIn` is `E[d*ᵀx - Y]·E[…] = 0`.
Without normality uncorrelated is not independent, and the cross term can be negative.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core
namespace Target

variable {Ω : Type*} [MeasurableSpace Ω] {n q : Type*} [Fintype n] [Fintype q]
  [DecidableEq n] [DecidableEq q]
  {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  {P : Measure Ω} (T : Target K ℓ v X x₀ β P)

/-- The residual projection `M = I - X(XᵀX)⁻¹Xᵀ`. -/
noncomputable def resid (X : Matrix n q ℝ) : Matrix n n ℝ := 1 - X * (Xᵀ * X)⁻¹ * Xᵀ

lemma resid_mul (hXi : Function.Injective X.mulVec) : resid X * X = 0 := by
  have hP : (Xᵀ * X).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosDef.one (n := n) (R := ℝ)).conjTranspose_mul_mul_same hXi
  have hu : IsUnit (Xᵀ * X).det := isUnit_iff_ne_zero.2 hP.det_pos.ne'
  rw [resid, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    nonsing_inv_mul _ hu, Matrix.mul_one, sub_self]

lemma eq_resid_add (u : n → ℝ) :
    u = resid X *ᵥ u + X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ u)) := by
  rw [resid, sub_mulVec, one_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  abel

/-- **The plug-in predictor under normal noise** (Kackar & Harville 1984). Let `d̂(u)` be
measurable, unbiased for every data set (`Xᵀd̂(u) = x₀`) and translation invariant
(`d̂(u + Xb) = d̂(u)`), and the data and target jointly normal. If the difference `d̂ᵀx - d*ᵀx`
from the best predictor `d* = Core.blup K X ℓ x₀` is square integrable, then
`E(d̂ᵀx - Y)² = mse(d*) + E(d̂ᵀx - d*ᵀx)²`. -/
theorem plugIn_mse_of_normal [IsProbabilityMeasure P] (hK : K.PosDef)
    (hXi : Function.Injective X.mulVec) (dh : (n → ℝ) → (n → ℝ)) (hdm : Measurable dh)
    (hX : ∀ u, Xᵀ *ᵥ dh u = x₀) (hinv : ∀ u b, dh (u + X *ᵥ b) = dh u)
    (hG : HasGaussianLaw (fun ω => ((fun i => T.x i ω), T.Y ω)) P)
    (hB : MemLp (fun ω => T.plugIn (fun ω => dh fun i => T.x i ω) ω
      - portLin T.x (blup K X ℓ x₀) ω) 2 P) :
    P[fun ω => (T.plugIn (fun ω => dh fun i => T.x i ω) ω - T.Y ω) ^ 2]
      = predMse K ℓ v (blup K X ℓ x₀)
        + P[fun ω => (T.plugIn (fun ω => dh fun i => T.x i ω) ω
            - portLin T.x (blup K X ℓ x₀) ω) ^ 2] := by
  set d := blup K X ℓ x₀ with hd_def
  have hd : Xᵀ *ᵥ d = x₀ := transpose_mulVec_blup hK hXi ℓ x₀
  rw [T.integral_sq_plugIn _ hd hB]
  suffices h0 : P[fun ω => (portLin T.x d ω - T.Y ω)
      * (T.plugIn (fun ω => dh fun i => T.x i ω) ω - portLin T.x d ω)] = 0 by
    rw [h0, mul_zero, add_zero]
  set M := resid X
  let xv : Ω → n → ℝ := fun ω i => T.x i ω
  let A : Ω → ℝ := fun ω => portLin T.x d ω - T.Y ω
  let h : (n → ℝ) → ℝ := fun u => (dh u - d) ⬝ᵥ u
  -- the difference of the predictions depends only on the residuals
  have hBeq : ∀ ω, T.plugIn (fun ω => dh fun i => T.x i ω) ω - portLin T.x d ω
      = h (M *ᵥ xv ω) := by
    intro ω
    set b := (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ xv ω)
    have hx : xv ω = M *ᵥ xv ω + X *ᵥ b := eq_resid_add (xv ω)
    have hdx : dh (xv ω) = dh (M *ᵥ xv ω) := by rw [hx, hinv, ← hx]
    have hXb : (dh (M *ᵥ xv ω) - d) ⬝ᵥ (X *ᵥ b) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, hX, hd, sub_self, zero_dotProduct]
    have : T.plugIn (fun ω => dh fun i => T.x i ω) ω - portLin T.x d ω
        = (dh (xv ω) - d) ⬝ᵥ xv ω := by
      simp only [plugIn, portLin, dotProduct, Pi.sub_apply, sub_mul, sum_sub_distrib, xv]
    have hsplit : (dh (M *ᵥ xv ω) - d) ⬝ᵥ xv ω
        = (dh (M *ᵥ xv ω) - d) ⬝ᵥ (M *ᵥ xv ω) + (dh (M *ᵥ xv ω) - d) ⬝ᵥ (X *ᵥ b) := by
      rw [← dotProduct_add, ← hx]
    rw [this, hdx, hsplit, hXb, add_zero]
  simp_rw [hBeq]
  -- the best predictor's error is uncorrelated with the residuals
  have hrow : ∀ j ω, (M *ᵥ xv ω) j = portLin T.x (fun k => M j k) ω := fun j ω => rfl
  have hcov : ∀ j, cov[A, fun ω => (M *ᵥ xv ω) j; P] = 0 := by
    intro j
    simp_rw [hrow]
    have hMd := T.memLp_portLin (fun k => M j k)
    rw [covariance_fun_sub_left (T.memLp_portLin d) T.Y_memLp hMd, covariance_comm T.Y,
      T.cov_portLin_Y]
    have hpp : cov[portLin T.x d, portLin T.x (fun k => M j k); P]
        = (fun k => M j k) ⬝ᵥ (K *ᵥ d) := by
      unfold portLin
      rw [covariance_fun_sum_fun_sum (fun i => (T.x_memLp i).const_mul (d i))
        (fun k => (T.x_memLp k).const_mul (M j k))]
      simp only [covariance_const_mul_left, covariance_const_mul_right, T.cov_x, dotProduct,
        mulVec, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
      have := hK.1.apply i k
      simp only [star_trivial] at this
      rw [← this]; ring
    rw [hpp, ← dotProduct_sub]
    have hfoc := mulVec_blup hK X ℓ x₀
    rw [← hd_def] at hfoc
    rw [hfoc, dotProduct_mulVec]
    have : (fun k => M j k) ᵥ* X = 0 := by
      funext r
      have := congrFun (congrFun (resid_mul hXi) j) r
      simpa [vecMul, dotProduct, Matrix.mul_apply] using this
    rw [this, zero_dotProduct]
  -- jointly normal and uncorrelated: independent
  let f : (n → ℝ) × ℝ →ₗ[ℝ] (Unit → ℝ) × (n → ℝ) :=
    { toFun := fun z => (fun _ => d ⬝ᵥ z.1 - z.2, M *ᵥ z.1)
      map_add' := fun a b => by
        ext
        · simp [dotProduct_add]; ring
        · simp [mulVec_add]
      map_smul' := fun c a => by
        ext
        · simp [dotProduct_smul]; ring
        · simp [mulVec_smul] }
  have hG' : HasGaussianLaw (fun ω => ((fun _ : Unit => A ω), fun j => (M *ᵥ xv ω) j)) P := by
    have := hG.map_fun (LinearMap.toContinuousLinearMap f)
    convert this using 1
    funext ω
    simp [f, A, xv, portLin, dotProduct]
  have hind := HasGaussianLaw.indepFun_of_covariance_eval hG' (fun _ j => hcov j)
  have hind2 : IndepFun A (fun ω => h (M *ᵥ xv ω)) P := by
    have := hind.comp (measurable_pi_apply ())
      (show Measurable fun u : n → ℝ => h u by
        simp only [h, dotProduct]
        exact Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp (hdm.sub_const d)).mul (measurable_pi_apply i))
    exact this
  have hAm : MemLp A 2 P := (T.memLp_portLin d).sub T.Y_memLp
  have hBm : MemLp (fun ω => h (M *ᵥ xv ω)) 2 P := by
    simpa only [hBeq] using hB
  rw [hind2.integral_fun_mul_eq_mul_integral hAm.aestronglyMeasurable hBm.aestronglyMeasurable]
  have hA0 : P[A] = 0 := by
    simp only [A]
    rw [integral_sub ((T.memLp_portLin d).integrable (by norm_num))
      (T.Y_memLp.integrable (by norm_num)), T.integral_portLin, hd, T.Y_mean, sub_self]
  rw [hA0, zero_mul]

/-- **Under normal noise estimating the moments can only cost**: the plug-in predictor's mean
squared error is at least the best predictor's. -/
theorem plugIn_mse_ge_of_normal [IsProbabilityMeasure P] (hK : K.PosDef)
    (hXi : Function.Injective X.mulVec) (dh : (n → ℝ) → (n → ℝ)) (hdm : Measurable dh)
    (hX : ∀ u, Xᵀ *ᵥ dh u = x₀) (hinv : ∀ u b, dh (u + X *ᵥ b) = dh u)
    (hG : HasGaussianLaw (fun ω => ((fun i => T.x i ω), T.Y ω)) P)
    (hB : MemLp (fun ω => T.plugIn (fun ω => dh fun i => T.x i ω) ω
      - portLin T.x (blup K X ℓ x₀) ω) 2 P) :
    predMse K ℓ v (blup K X ℓ x₀)
      ≤ P[fun ω => (T.plugIn (fun ω => dh fun i => T.x i ω) ω - T.Y ω) ^ 2] := by
  rw [T.plugIn_mse_of_normal hK hXi dh hdm hX hinv hG hB]
  exact le_add_of_nonneg_right (integral_nonneg fun ω => sq_nonneg _)

end Target
end Core
end Credibility
