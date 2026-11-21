import Credibility.OffDiagonal

/-!
# Projecting an estimate onto a convex set that contains the truth

An unbiased moment estimator `θ̂` of a vector of second-moment parameters (a covariance
table, variances) can fall outside the set `S` of valid parameters (for example, a table
that is not positive semidefinite). Replace it by its projection `p` onto `S` in the metric
`‖v‖²_H = vᵀHv` of a positive semidefinite `H` (for MINQUE, the least squares Hessian: the
fit minimizes `θᵀHθ - 2qᵀθ`, so the constrained fit is this projection; Hartung 1981,
Pukelsheim 1981).

If `S` is convex and contains the true `θ`, the projection is never further from the truth
in the `H`-norm, for every draw:
`‖p - θ‖²_H + ‖θ̂ - p‖²_H ≤ ‖θ̂ - θ‖²_H` (`hsq_proj_add_le`), so its `H`-weighted mean squared
error is at most the unbiased estimate's (`integral_hsq_proj_le`). Nothing about the
distribution of `θ̂` is used, nor unbiasedness: the bound holds for any estimate. The price is
bias (`p` is not unbiased in general; LaMotte 1973).

For positive definite `H` and closed nonempty `S` the projection exists and is unique
(`exists_hsq_proj`, `hsq_proj_unique`). The set of parameters whose tables (any linear
images of `θ`) are positive semidefinite is convex (`convex_setOf_posSemidef`), so the app's
`constrainPSD` (`γλλᵀ ⪰ 0`, `C ⪰ 0`, `s² ≥ 0`) is a case.

Not in the thesis.
-/

open Matrix

namespace Credibility.ConeProjection

variable {ι : Type*} [Fintype ι]

/-- The squared `H`-norm `vᵀHv`. -/
def hsq (H : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (H *ᵥ v)

theorem hsq_nonneg {H : Matrix ι ι ℝ} (hH : H.PosSemidef) (v : ι → ℝ) : 0 ≤ hsq H v := by
  simpa [hsq] using hH.dotProduct_mulVec_nonneg v

/-- Expanding `‖d + t e‖²_H` for symmetric `H`. -/
theorem hsq_add_smul {H : Matrix ι ι ℝ} (hH : H.IsSymm) (d e : ι → ℝ) (t : ℝ) :
    hsq H (d + t • e) = hsq H d + 2 * t * (d ⬝ᵥ (H *ᵥ e)) + t ^ 2 * hsq H e := by
  have hc : e ⬝ᵥ (H *ᵥ d) = d ⬝ᵥ (H *ᵥ e) := hH.dotProduct_mulVec_comm
  simp only [hsq, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hc]
  ring

/-- A scalar step: `0 ≤ 2b + tq` for all `t ∈ (0, 1]` with `q ≥ 0` forces `b ≥ 0`. -/
theorem nonneg_of_forall_small {b q : ℝ} (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ 2 * b + t * q) : 0 ≤ b := by
  by_contra hb
  replace hb := not_le.mp hb
  set t := min 1 (-b / (q + 1)) with ht
  have hq1 : 0 < q + 1 := by linarith
  have htpos : 0 < t := lt_min one_pos (div_pos (by linarith) hq1)
  have htle : t ≤ -b / (q + 1) := min_le_right _ _
  have h1 := h t htpos (min_le_left _ _)
  have h2 : t * q ≤ -b / (q + 1) * q := mul_le_mul_of_nonneg_right htle hq
  have h3 : -b / (q + 1) * q < -b := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hq1]
    nlinarith
  linarith

/-- The variational inequality of the projection: if `p ∈ S` minimizes `‖x - θ̂‖_H` over a
convex `S`, then `(p - θ̂)ᵀH(x - p) ≥ 0` for every `x ∈ S`. -/
theorem proj_inner_nonneg {H : Matrix ι ι ℝ} (hH : H.PosSemidef) {S : Set (ι → ℝ)}
    (hS : Convex ℝ S) {θhat p x : ι → ℝ} (hp : p ∈ S) (hx : x ∈ S)
    (hmin : ∀ y ∈ S, hsq H (p - θhat) ≤ hsq H (y - θhat)) :
    0 ≤ (p - θhat) ⬝ᵥ (H *ᵥ (x - p)) := by
  have hsymm : H.IsSymm := hH.isHermitian.isSymm
  refine nonneg_of_forall_small (hsq_nonneg hH (x - p)) fun t ht0 ht1 => ?_
  have hmem : p + t • (x - p) ∈ S := by
    have := hS.add_smul_sub_mem hp hx ⟨ht0.le, ht1⟩
    simpa using this
  have h := hmin _ hmem
  have he : p + t • (x - p) - θhat = (p - θhat) + t • (x - p) := by abel
  rw [he, hsq_add_smul hsymm] at h
  have : 0 ≤ t * (2 * ((p - θhat) ⬝ᵥ (H *ᵥ (x - p))) + t * hsq H (x - p)) := by nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith) ht0

/-- **The projection is closer to the truth.** If `p` is an `H`-projection of the estimate
`θ̂` onto a convex set `S` that contains the true `θ`, then
`‖p - θ‖²_H + ‖θ̂ - p‖²_H ≤ ‖θ̂ - θ‖²_H`, for every value of `θ̂`. -/
theorem hsq_proj_add_le {H : Matrix ι ι ℝ} (hH : H.PosSemidef) {S : Set (ι → ℝ)}
    (hS : Convex ℝ S) {θ θhat p : ι → ℝ} (hθ : θ ∈ S) (hp : p ∈ S)
    (hmin : ∀ y ∈ S, hsq H (p - θhat) ≤ hsq H (y - θhat)) :
    hsq H (p - θ) + hsq H (θhat - p) ≤ hsq H (θhat - θ) := by
  have hi := proj_inner_nonneg hH hS hp hθ hmin
  have hsymm : H.IsSymm := hH.isHermitian.isSymm
  -- `θ̂ - θ = (θ̂ - p) + 1 • (p - θ)`, and the cross term is the variational inequality
  have e1 : θhat - θ = (θhat - p) + (1 : ℝ) • (p - θ) := by rw [one_smul]; abel
  have e2 : (θhat - p) ⬝ᵥ (H *ᵥ (p - θ)) = (p - θhat) ⬝ᵥ (H *ᵥ (θ - p)) := by
    rw [← neg_sub p θhat, ← neg_sub θ p, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [e1, hsq_add_smul hsymm, e2]
  nlinarith

/-- **The projection is closer to the truth** (the `H`-norm error alone). -/
theorem hsq_proj_le {H : Matrix ι ι ℝ} (hH : H.PosSemidef) {S : Set (ι → ℝ)}
    (hS : Convex ℝ S) {θ θhat p : ι → ℝ} (hθ : θ ∈ S) (hp : p ∈ S)
    (hmin : ∀ y ∈ S, hsq H (p - θhat) ≤ hsq H (y - θhat)) :
    hsq H (p - θ) ≤ hsq H (θhat - θ) := by
  have := hsq_proj_add_le hH hS hθ hp hmin
  have := hsq_nonneg hH (θhat - p)
  linarith

/-- **Mean squared error in the `H`-norm.** For a random estimate `θ̂(ω)` and its projection
`p(ω)` onto a convex `S` containing the truth, `E‖p - θ‖²_H ≤ E‖θ̂ - θ‖²_H` (any probability
law; only the right side need be integrable). -/
theorem integral_hsq_proj_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {H : Matrix ι ι ℝ} (hH : H.PosSemidef) {S : Set (ι → ℝ)}
    (hS : Convex ℝ S) {θ : ι → ℝ} (hθ : θ ∈ S) {θhat p : Ω → ι → ℝ} (hp : ∀ ω, p ω ∈ S)
    (hmin : ∀ ω, ∀ y ∈ S, hsq H (p ω - θhat ω) ≤ hsq H (y - θhat ω))
    (hint : MeasureTheory.Integrable (fun ω => hsq H (θhat ω - θ)) μ) :
    ∫ ω, hsq H (p ω - θ) ∂μ ≤ ∫ ω, hsq H (θhat ω - θ) ∂μ :=
  MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hsq_nonneg hH _)
    hint (Filter.Eventually.of_forall fun ω => hsq_proj_le hH hS hθ (hp ω) (hmin ω))

/-- For positive definite `H` the projection onto a convex set is unique. -/
theorem hsq_proj_unique {H : Matrix ι ι ℝ} (hH : H.PosDef) {S : Set (ι → ℝ)}
    (hS : Convex ℝ S) {θhat p p' : ι → ℝ} (hp : p ∈ S) (hp' : p' ∈ S)
    (hmin : ∀ y ∈ S, hsq H (p - θhat) ≤ hsq H (y - θhat))
    (hmin' : ∀ y ∈ S, hsq H (p' - θhat) ≤ hsq H (y - θhat)) : p = p' := by
  have h := hsq_proj_add_le hH.posSemidef hS hp hp' hmin'
  -- with `θ := p`: `‖p' - p‖² + ‖θ̂ - p'‖² ≤ ‖θ̂ - p‖²`, and symmetrically
  have h' := hsq_proj_add_le hH.posSemidef hS hp' hp hmin
  have h0 : hsq H (p' - p) ≤ 0 := by
    linarith [hsq_nonneg hH.posSemidef (θhat - p), hsq_nonneg hH.posSemidef (θhat - p'),
      hsq_nonneg hH.posSemidef (p - p')]
  by_contra hne
  have := hH.dotProduct_mulVec_pos (x := p' - p) (sub_ne_zero.mpr (Ne.symm hne))
  simp only [star_trivial] at this
  exact absurd h0 (not_le.mpr this)

/-- A positive definite `H` bounds `vᵀv`: `c · vᵀv ≤ vᵀHv` for some `c > 0`. -/
theorem exists_mul_dotProduct_le_hsq [DecidableEq ι] {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ι → ℝ, c * (v ⬝ᵥ v) ≤ hsq H v := by
  obtain ⟨c, hc, hpsd⟩ := hH.exists_posSemidef_sub_smul_one
  refine ⟨c, hc, fun v => ?_⟩
  have h := hpsd.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at h
  unfold hsq
  linarith

theorem continuous_hsq (H : Matrix ι ι ℝ) (a : ι → ℝ) :
    Continuous fun x : ι → ℝ => hsq H (x - a) := by
  unfold hsq
  have hc : Continuous fun x : ι → ℝ => x - a := continuous_id.sub continuous_const
  exact hc.dotProduct (continuous_const.matrix_mulVec hc)

/-- **The projection exists** for positive definite `H` and a closed nonempty `S`
(convexity is not needed for existence). -/
theorem exists_hsq_proj {H : Matrix ι ι ℝ} (hH : H.PosDef) {S : Set (ι → ℝ)}
    (hSc : IsClosed S) (hSn : S.Nonempty) (θhat : ι → ℝ) :
    ∃ p ∈ S, ∀ y ∈ S, hsq H (p - θhat) ≤ hsq H (y - θhat) := by
  classical
  obtain ⟨c, hc, hle⟩ := exists_mul_dotProduct_le_hsq hH
  obtain ⟨x₀, hx₀⟩ := hSn
  set R := hsq H (x₀ - θhat)
  set T := S ∩ {x | hsq H (x - θhat) ≤ R}
  have hTc : IsClosed T := hSc.inter (isClosed_le (continuous_hsq H θhat) continuous_const)
  have hR : 0 ≤ R / c := div_nonneg (hsq_nonneg hH.posSemidef _) hc.le
  have hTb : T ⊆ Metric.closedBall θhat (Real.sqrt (R / c)) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (Real.sqrt_nonneg _)]
    intro i
    rw [Real.dist_eq]
    apply Real.abs_le_sqrt
    have hv : (x - θhat) ⬝ᵥ (x - θhat) ≤ R / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact (hle _).trans hx.2
    refine le_trans ?_ hv
    have := Finset.single_le_sum (f := fun j => (x - θhat) j * (x - θhat) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  have hTk : IsCompact T :=
    Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  obtain ⟨p, hpT, hpmin⟩ := hTk.exists_isMinOn ⟨x₀, hx₀, show hsq H (x₀ - θhat) ≤ R from le_rfl⟩
    (continuous_hsq H θhat).continuousOn
  refine ⟨p, hpT.1, fun y hy => ?_⟩
  by_cases hyT : hsq H (y - θhat) ≤ R
  · exact hpmin ⟨hy, hyT⟩
  · exact hpT.2.trans (not_le.mp hyT).le

omit [Fintype ι] in
/-- The parameters whose tables are positive semidefinite form a convex set: for linear maps
`A k` from parameters to square matrices (blocks such as `γλλᵀ`, `C`, or a `1 × 1` block for
`s² ≥ 0`), `{θ | ∀ k, A k θ ⪰ 0}` is convex. -/
theorem convex_setOf_posSemidef {κ : Type*} {m : κ → Type*} [∀ k, Fintype (m k)]
    (A : ∀ k, (ι → ℝ) →ₗ[ℝ] Matrix (m k) (m k) ℝ) :
    Convex ℝ {θ : ι → ℝ | ∀ k, (A k θ).PosSemidef} := by
  intro x hx y hy a b ha hb _ k
  simp only [map_add, map_smul]
  exact ((hx k).smul ha).add ((hy k).smul hb)

omit [Fintype ι] in
/-- The valid parameters form a closed set (finitely many parameters): each
`{θ | A k θ ⪰ 0}` is the preimage of the closed positive semidefinite cone under a
continuous linear map. With `convex_setOf_posSemidef` and `exists_hsq_proj`, the projection
onto valid tables exists and is unique. -/
theorem isClosed_setOf_posSemidef [Finite ι] {κ : Type*} {m : κ → Type*} [∀ k, Fintype (m k)]
    (A : ∀ k, (ι → ℝ) →ₗ[ℝ] Matrix (m k) (m k) ℝ) :
    IsClosed {θ : ι → ℝ | ∀ k, (A k θ).PosSemidef} := by
  have : {θ : ι → ℝ | ∀ k, (A k θ).PosSemidef} = ⋂ k, A k ⁻¹' {M | M.PosSemidef} := by
    ext θ; simp
  rw [this]
  exact isClosed_iInter fun k =>
    (isClosed_setOfPred_posSemidef (n := m k) (R := ℝ)).preimage (A k).continuous_of_finiteDimensional

end Credibility.ConeProjection
