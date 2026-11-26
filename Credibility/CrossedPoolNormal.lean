import Credibility.Cumulants
import Credibility.CrossedEstimation

/-!
# Crossed levels: the pair pool under normal noise (distribution layer)

**Optional distribution layer** (owner, 2026-11-15): this file assumes *normal noise* (jointly
Gaussian cells), so nothing in the core depends on it. General target (2) of the crossed entry of
`studies/PLAN.md`.

* `integral_pow_four_gaussianReal`: `∫ x⁴ dN(0, v) = 3v²`, from the fourth derivative of the
  moment generating function;
* `variance_sq_of_hasGaussianLaw`, `Model.variance_sq_muHat_sub_of_normal`: for a centred normal
  `D`, `Var(D²) = 2(E D²)²`; so with jointly normal cells of a common mean
  `Var((μ̂ᵢ - μ̂ⱼ)²) = 2(E(μ̂ᵢ - μ̂ⱼ)²)²`, and the diagonal of the pair covariance table
  (`CrossedPoolWeights.lean`) is `2(θ + nₚ)²`, `θ` the class value and `nₚ` the noise variance of
  the difference;
* `sqIVWeight`: inverse variance, i.e. GLS on that diagonal, gives weights `∝ (θ + nₚ)⁻²`; their
  ratios `((θ + n_q)/(θ + nₚ))²` (`sqIVWeight_div`), more weight to precise pairs
  (`sqIVWeight_anti`), and the two limits: signal ≫ noise gives equal weights
  (`tendsto_sqIVWeight_atTop`), noise ≫ signal (`θ = 0`) weights `∝ nₚ⁻²`, favouring large cells.

The full GLS also uses the off-diagonal covariances (pairs sharing a cell), so it differs from
inverse variance in general.
-/

open MeasureTheory ProbabilityTheory

namespace Credibility

/-- The fourth derivative of `t ↦ exp(vt²/2)` at `0` is `3v²`. -/
lemma iteratedDeriv_four_exp_sq (v : ℝ) :
    iteratedDeriv 4 (fun t => Real.exp (v * t ^ 2 / 2)) 0 = 3 * v ^ 2 := by
  set g : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2) with hg
  have hd : ∀ t, HasDerivAt g (v * t * g t) t := fun t => by
    have := ((hasDerivAt_pow 2 t).const_mul v |>.div_const 2).exp
    convert this using 1; simp [hg]; ring
  have hpoly : ∀ (p p' : ℝ → ℝ) (t : ℝ), HasDerivAt p (p' t) t →
      HasDerivAt (fun s => p s * g s) ((p' t + p t * (v * t)) * g t) t := fun p p' t hp => by
    convert hp.mul (hd t) using 1; ring
  have h1 : iteratedDeriv 1 g = fun t => v * t * g t := by
    rw [iteratedDeriv_one]; funext t; exact (hd t).deriv
  have h2 : iteratedDeriv 2 g = fun t => (v + v ^ 2 * t ^ 2) * g t := by
    rw [iteratedDeriv_succ, h1]; funext t
    refine (hpoly (fun s => v * s) (fun _ => v) t ?_).deriv.trans (by ring)
    simpa using (hasDerivAt_id t).const_mul v
  have h3 : iteratedDeriv 3 g = fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * g t := by
    rw [iteratedDeriv_succ, h2]; funext t
    refine (hpoly (fun s => v + v ^ 2 * s ^ 2) (fun s => v ^ 2 * (2 * s)) t ?_).deriv.trans
      (by ring)
    simpa using ((hasDerivAt_pow 2 t).const_mul (v ^ 2)).const_add v
  rw [iteratedDeriv_succ, h3]
  refine (hpoly (fun s => 3 * v ^ 2 * s + v ^ 3 * s ^ 3)
    (fun s => 3 * v ^ 2 + v ^ 3 * (3 * s ^ 2)) 0 ?_).deriv.trans (by simp [hg])
  have := ((hasDerivAt_id (0:ℝ)).const_mul (3 * v ^ 2)).fun_add
    ((hasDerivAt_pow 3 (0:ℝ)).const_mul (v ^ 3))
  simpa using this

/-- **The fourth moment of a centred normal:** `∫ x⁴ dN(0, v) = 3v²`. -/
lemma integral_pow_four_gaussianReal (v : NNReal) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v)
    (by simp [integrableExpSet_id_gaussianReal]) 4
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul, zero_add] at h
  rw [iteratedDeriv_four_exp_sq] at h
  rw [h]; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Under normal noise, `Var(D²) = 2(E D²)²`** for a centred normal `D`. -/
theorem variance_sq_of_hasGaussianLaw {D : Ω → ℝ} (hD : HasGaussianLaw D P) (h0 : P[D] = 0) :
    Var[fun ω => D ω ^ 2; P] = 2 * (P[fun ω => D ω ^ 2]) ^ 2 := by
  have := hD.isProbabilityMeasure
  have hm : AEMeasurable D P := hD.aemeasurable
  have h4 : MemLp D 4 P := hD.memLp (by simp)
  have hsq : MemLp (fun ω => D ω ^ 2) 2 P := by
    have := Cumulants.holder442
    exact (h4.mul h4 (p := 4) (q := 4) (r := 2)).congr_norm (by fun_prop)
      (.of_forall fun ω => by simp [sq])
  have hV : P[fun ω => D ω ^ 2] = Var[D; P] := by
    rw [variance_eq_sub hD.memLp_two, h0]; simp [Pi.pow_apply]
  have hE4 : P[fun ω => D ω ^ 4] = 3 * Var[D; P] ^ 2 := by
    have hmap := hD.map_eq_gaussianReal
    rw [h0] at hmap
    have := integral_pow_four_gaussianReal Var[D; P].toNNReal
    rw [← hmap, integral_map hm (by fun_prop)] at this
    rw [this, Real.coe_toNNReal _ (variance_nonneg _ _)]
  rw [variance_eq_sub hsq, hV]
  have : (fun ω => D ω ^ 2) ^ 2 = fun ω => D ω ^ 4 := by funext ω; simp; ring
  rw [this, hE4]; ring

namespace Model

variable {J T : Type*} [Fintype J] [Fintype T]

/-- The difference of two cohort estimates `X ↦ μ̂ᵢ - μ̂ⱼ` as a linear map. -/
noncomputable def muHatDiff (w : J → T → ℝ) (i j : J) : (J × T → ℝ) →ₗ[ℝ] ℝ where
  toFun X := muHat w X i - muHat w X j
  map_add' X Y := by
    simp only [muHat, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c X := by
    simp only [muHat, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

/-- **Under normal noise the squared difference of two cohort estimates has variance twice its
squared mean:** with jointly normal cells of a common mean `μ`,
`Var((μ̂ᵢ - μ̂ⱼ)²) = 2(E(μ̂ᵢ - μ̂ⱼ)²)²`. -/
theorem variance_sq_muHat_sub_of_normal {w : J → T → ℝ} (hw : ∀ j t, 0 < w j t)
    (Z : J × T → Ω → ℝ) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) {μ : ℝ}
    (hm : ∀ q, ∫ ω, Z q ω ∂P = μ) (i j : J) :
    Var[fun ω => (muHat w (Z · ω) i - muHat w (Z · ω) j) ^ 2; P]
      = 2 * (∫ ω, (muHat w (Z · ω) i - muHat w (Z · ω) j) ^ 2 ∂P) ^ 2 := by
  have := hZ.isProbabilityMeasure
  set L := LinearMap.toContinuousLinearMap (muHatDiff w i j)
  have hD : HasGaussianLaw (fun ω => L (Z · ω)) P := hZ.map_fun L
  refine variance_sq_of_hasGaussianLaw (D := fun ω => L (Z · ω)) hD ?_
  by_cases hT : IsEmpty T
  · simp [L, muHatDiff, muHat, Finset.univ_eq_empty]
  rw [not_isEmpty_iff] at hT
  have hint : ∀ q, Integrable (Z q) P := fun q => (hZ.eval q).integrable
  have hmu : ∀ k, ∫ ω, muHat w (Z · ω) k ∂P = μ := fun k => by
    simp only [muHat]
    rw [integral_finsetSum _ fun t _ => (hint (k, t)).const_mul _]
    simp only [integral_const_mul, hm, ← Finset.sum_mul]
    rw [← Finset.sum_div, show ∑ t, w k t = wtot w k from rfl, div_self (wtot_pos hw k).ne',
      one_mul]
  have hintμ : ∀ k, Integrable (fun ω => muHat w (Z · ω) k) P := fun k =>
    integrable_finsetSum _ fun t _ => (hint (k, t)).const_mul _
  change ∫ ω, (muHat w (Z · ω) i - muHat w (Z · ω) j) ∂P = 0
  rw [integral_sub (hintμ i) (hintμ j), hmu, hmu, sub_self]

end Model

section InverseVariance

open Filter Topology

variable {I : Type*} [Fintype I]

/-- The inverse-variance weights of squared differences with means `θ + nₚ` under normal noise,
whose variances are `2(θ + nₚ)²` (`variance_sq_of_hasGaussianLaw`). -/
noncomputable def sqIVWeight (θ : ℝ) (n : I → ℝ) : I → ℝ :=
  invVarWeight fun r => 2 * (θ + n r) ^ 2

/-- The ratio of two weights is `((θ + n_q)/(θ + n_p))²`. -/
theorem sqIVWeight_div (θ : ℝ) (n : I → ℝ) (hn : ∀ r, θ + n r ≠ 0) (p q : I) :
    sqIVWeight θ n p / sqIVWeight θ n q = ((θ + n q) / (θ + n p)) ^ 2 := by
  have : Nonempty I := ⟨p⟩
  have hS : 0 < ∑ r, (2 * (θ + n r) ^ 2)⁻¹ :=
    sum_inv_pos _ fun r => by have := hn r; positivity
  have hp := hn p
  have hq := hn q
  simp only [sqIVWeight, invVarWeight]
  rw [div_div_div_cancel_right₀ hS.ne']
  field_simp

/-- More precise pairs get more weight: `n_p ≤ n_q` and `θ ≥ 0` give `b_q ≤ b_p`. -/
theorem sqIVWeight_anti {θ : ℝ} (hθ : 0 ≤ θ) {n : I → ℝ} (hn : ∀ r, 0 < n r) {p q : I}
    (h : n p ≤ n q) : sqIVWeight θ n q ≤ sqIVWeight θ n p := by
  have : Nonempty I := ⟨p⟩
  have hS : 0 < ∑ r, (2 * (θ + n r) ^ 2)⁻¹ :=
    sum_inv_pos _ fun r => by have := hn r; positivity
  simp only [sqIVWeight, invVarWeight]
  refine div_le_div_of_nonneg_right ?_ hS.le
  have := hn p
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- **Signal ≫ noise: equal weights.** As `θ → ∞` the weights tend to `1/|I|`. -/
theorem tendsto_sqIVWeight_atTop (n : I → ℝ) (p : I) :
    Tendsto (fun θ => sqIVWeight θ n p) atTop (𝓝 (1 / Fintype.card I)) := by
  have hratio : ∀ r, Tendsto (fun θ : ℝ => (θ + n p) / (θ + n r)) atTop (𝓝 1) := fun r => by
    have h1 : Tendsto (fun θ : ℝ => θ + n r) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have h2 := (tendsto_const_nhds (x := n p - n r)).div_atTop h1
    have h3 : Tendsto (fun θ : ℝ => 1 + (n p - n r) / (θ + n r)) atTop (𝓝 1) := by
      simpa using h2.const_add 1
    refine h3.congr' ?_
    filter_upwards [h1.eventually_gt_atTop 0] with θ hθ
    field_simp; ring
  have hsum : Tendsto (fun θ : ℝ => ∑ r, ((θ + n p) / (θ + n r)) ^ 2) atTop
      (𝓝 (Fintype.card I)) := by
    have := tendsto_finsetSum (Finset.univ : Finset I) fun r _ => (hratio r).pow 2
    simpa using this
  have hinv := hsum.inv₀ (by have : Nonempty I := ⟨p⟩; exact_mod_cast Fintype.card_ne_zero)
  rw [one_div]
  refine hinv.congr' ?_
  have hev : ∀ᶠ θ : ℝ in atTop, ∀ r, 0 < θ + n r :=
    eventually_all.2 fun r => (tendsto_atTop_add_const_right _ _ tendsto_id).eventually_gt_atTop 0
  filter_upwards [hev] with θ hθ
  have : Nonempty I := ⟨p⟩
  have hS : 0 < ∑ r, (2 * (θ + n r) ^ 2)⁻¹ :=
    sum_inv_pos _ fun r => by have := hθ r; positivity
  have hp := (hθ p).ne'
  have e : ∑ r, ((θ + n p) / (θ + n r)) ^ 2
      = 2 * (θ + n p) ^ 2 * ∑ r, (2 * (θ + n r) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by have := (hθ r).ne'; field_simp
  simp only [sqIVWeight, invVarWeight, e]
  field_simp

end InverseVariance

end Credibility
