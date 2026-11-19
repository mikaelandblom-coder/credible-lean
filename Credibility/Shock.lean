import Credibility.Core
import Credibility.Expectation

/-!
# Shock plus process noise (extension, Finding 23)

The thesis takes `cov(μᵢₜ, μⱼₜ) = σᵢₜσⱼₜρᵢⱼ` with `ρᵢⱼ` fixed over periods and, in §2.8,
`σⱼₜ² = σⱼ²/wⱼₜ`: the covariance between cohorts then shrinks with volume. A period shock
(travel demand, thesis §2.2) does not. Here each period has a shock with covariance `C ⪰ 0`
across cohorts and, on top of it, process noise `sⱼ²/wⱼₜ` that does shrink with volume:

`cov(μᵢₜ, μⱼₛ) = δₜₛ(Cᵢⱼ + δᵢⱼ sᵢ²/wᵢₜ) + τ²δᵢⱼ`  (`obsCov`).

One shock with loadings `λⱼ` is `C = λλᵀ` (`posSemidef_loadings`).

* For any cohort weights `aⱼₜ` summing to one, `μ̂ⱼ = Σₜ aⱼₜμⱼₜ` has covariance
  `Kᵢⱼ = (Σₜ aᵢₜaⱼₜ)Cᵢⱼ + δᵢⱼ(sᵢ²Σₜ aᵢₜ²/wᵢₜ + τ²)` (`K_apply`), and `K ≻ 0` (`K_posDef`).
  The Core results (GLS weights, `bestZ`) then apply as they stand (`bestZ_eq`).
* Estimation (§2.8): within-cohort residuals `rⱼₜ = μⱼₜ - μ̂ⱼ` remove `τ²` and the mean.
  Same-period cross products give `Cᵢⱼ` for `i ≠ j` (`crossHat_unbiased`). On the diagonal
  `E rⱼₜ² = dⱼⱼₜCⱼⱼ + hⱼₜsⱼ²` mixes the shock and the process noise; two weightings of
  the squared residuals separate them when a 2×2 determinant is nonzero
  (`CdiagHat_unbiased`, `s2Hat_unbiased`). With a constant volume no estimator can
  separate them (`not_unbiased_s2_of_const`): `sⱼ²` is identified only through volume
  variation.
-/

open Finset Matrix

namespace Credibility

/-- Weighted sums of positive semidefinite matrices: if every `Nₜ ⪰ 0`, then
`(Σₜ aᵢₜ aⱼₜ (Nₜ)ᵢⱼ)ᵢⱼ ⪰ 0` for any weights `a` (a sum of `DₜNₜDₜ`, `Dₜ = diag(a·ₜ)`). -/
theorem posSemidef_weightedSum {J T : Type*} [Fintype J] [Fintype T]
    (N : T → Matrix J J ℝ) (hN : ∀ t, (N t).PosSemidef) (a : J → T → ℝ) :
    (of fun i j => ∑ t, a i t * a j t * N t i j).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [conjTranspose_apply, of_apply, star_trivial]
    refine sum_congr rfl fun t _ => ?_
    have := (hN t).1.apply i j
    simp only [star_trivial] at this
    rw [this]; ring
  · have key : star x ⬝ᵥ ((of fun i j => ∑ t, a i t * a j t * N t i j) *ᵥ x)
        = ∑ t, star (fun j => a j t * x j) ⬝ᵥ (N t *ᵥ fun j => a j t * x j) := by
      simp only [dotProduct, mulVec, star_trivial, of_apply, mul_sum, sum_mul]
      symm
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring
    rw [key]
    exact sum_nonneg fun t _ => (hN t).dotProduct_mulVec_nonneg _

/-- One shock with loadings `λⱼ`: `C = λλᵀ ⪰ 0`. -/
theorem posSemidef_loadings {J : Type*} [Fintype J] (l : J → ℝ) :
    (vecMulVec l l).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star l

/-- Shock plus process noise: per period a shock with covariance `C ⪰ 0` across cohorts,
process noise `sⱼ²/wⱼₜ` shrinking with the volume `wⱼₜ`, and cohort levels with
variance `τ²`. Distribution-free: only these second moments are assumed. -/
structure Shock (J T : Type*) where
  /-- Heterogeneity between cohorts. -/
  τ2 : ℝ
  /-- Covariance of the period shock across cohorts. -/
  C : Matrix J J ℝ
  /-- Process noise per unit of volume. -/
  s2 : J → ℝ
  /-- Volume of cohort `j` in period `t`. -/
  w : J → T → ℝ
  τ2_pos : 0 < τ2
  C_posSemidef : C.PosSemidef
  s2_pos : ∀ j, 0 < s2 j
  w_pos : ∀ j t, 0 < w j t

namespace Shock

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Shock J T)

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
lemma C_symm (i j : J) : M.C j i = M.C i j := by
  simpa using M.C_posSemidef.1.apply i j

/-- `cov(μᵢₜ, μⱼₛ) = δₜₛ(Cᵢⱼ + δᵢⱼ sᵢ²/wᵢₜ) + τ²δᵢⱼ`. -/
noncomputable def obsCov (i j : J) (t s : T) : ℝ :=
  (if t = s then M.C i j + (if i = j then M.s2 i / M.w i t else 0) else 0)
    + M.τ2 * (if i = j then 1 else 0)

/-- The covariance table of the data, indexed by cells `p = (j, t)`. -/
noncomputable def cov (p q : J × T) : ℝ := M.obsCov p.1 q.1 p.2 q.2

omit [Fintype J] [Fintype T] in
lemma cov_symm (p q : J × T) : M.cov q p = M.cov p q := by
  simp only [cov, obsCov, M.C_symm q.1 p.1, eq_comm (a := q.2), eq_comm (a := q.1)]
  split_ifs <;> simp_all

/-- The period-`t` noise covariance `C + diag(sⱼ²/wⱼₜ)`: shock plus process noise. -/
noncomputable def noise (t : T) : Matrix J J ℝ := M.C + diagonal fun j => M.s2 j / M.w j t

omit [Fintype J] [Fintype T] [DecidableEq T] in
lemma noise_apply (t : T) (i j : J) :
    M.noise t i j = M.C i j + (if i = j then M.s2 i / M.w i t else 0) := by
  by_cases h : i = j <;> simp [noise, h]

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
lemma noise_posSemidef [DecidableEq J] [Fintype J] (t : T) : (M.noise t).PosSemidef :=
  M.C_posSemidef.add (PosSemidef.diagonal fun j => (div_pos (M.s2_pos j) (M.w_pos j t)).le)

variable (a : J → T → ℝ)

/-- `Kᵢⱼ = cov(μ̂ᵢ, μ̂ⱼ)` for `μ̂ⱼ = Σₜ aⱼₜμⱼₜ`. -/
noncomputable def K : Matrix J J ℝ :=
  of fun i j => ∑ t, ∑ s, a i t * a j s * M.obsCov i j t s

/-- The error covariance `Σᵢⱼ = Σₜ aᵢₜaⱼₜ(Cᵢⱼ + δᵢⱼsᵢ²/wᵢₜ)`: `K` without the level variance. -/
noncomputable def errCov : Matrix J J ℝ := of fun i j => ∑ t, a i t * a j t * M.noise t i j

variable {a}

omit [Fintype J] in
/-- `K = Σ + τ²I` when each cohort's weights sum to one. -/
theorem K_eq_errCov (ha : ∀ j, ∑ t, a j t = 1) : M.K a = M.errCov a + M.τ2 • (1 : Matrix J J ℝ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [K, of_apply, obsCov, errCov, of_apply, noise_apply, mul_add, sum_add_distrib, mul_ite,
    mul_zero, sum_ite_eq, mem_univ, ite_true]
  congr 1
  split_ifs with h
  · subst h
    simp only [mul_one, ← sum_mul, ← mul_sum, ha, one_mul]
  · simp

omit [Fintype J] in
/-- `Kᵢⱼ = (Σₜ aᵢₜaⱼₜ)Cᵢⱼ + δᵢⱼ(sᵢ²Σₜ aᵢₜ²/wᵢₜ + τ²)`. -/
theorem K_apply (ha : ∀ j, ∑ t, a j t = 1) (i j : J) :
    M.K a i j = (∑ t, a i t * a j t) * M.C i j
      + (if i = j then M.s2 i * ∑ t, a i t ^ 2 / M.w i t + M.τ2 else 0) := by
  rw [M.K_eq_errCov ha, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [errCov, noise_apply, of_apply, mul_add, sum_add_distrib, ← sum_mul]
  split_ifs with h
  · subst h
    rw [mul_sum]
    simp only [mul_one]
    rw [add_assoc]
    congr 2
    exact sum_congr rfl fun t _ => by ring
  · simp

omit [DecidableEq T] in
theorem errCov_posSemidef : (M.errCov a).PosSemidef :=
  posSemidef_weightedSum M.noise M.noise_posSemidef a

/-- `K ≻ 0` for any cohort weights summing to one: `K = Σ + τ²I` with `Σ ⪰ 0`. -/
theorem K_posDef (ha : ∀ j, ∑ t, a j t = 1) : (M.K a).PosDef := by
  rw [M.K_eq_errCov ha, add_comm]
  exact (PosDef.one.smul M.τ2_pos).add_posSemidef M.errCov_posSemidef

/-! ### The blend: Core results for this `K` -/

variable (a) in
/-- The moments entering the blend for cohort `j`: those of `Core` for this `K`, `τ²`
and `vⱼ = Σⱼⱼ = (Σₜ aⱼₜ²)Cⱼⱼ + sⱼ²Σₜ aⱼₜ²/wⱼₜ`. -/
noncomputable def moments (j : J) : BlendMoments :=
  Core.moments (M.K a) M.τ2 (fun j => M.errCov a j j) j

/-- Eqs. (26)/(27) under shock plus process noise: the Core formula for this `K`. -/
theorem bestZ_eq (ha : ∀ j, ∑ t, a j t = 1) (j : J) :
    (M.moments a j).bestZ = (1 - glsWeight (M.K a) j) * M.τ2
      / (M.τ2 + M.errCov a j j - (invTotal (M.K a))⁻¹) :=
  Core.bestZ_eq (M.K_posDef ha) j

/-- Inverse-variance cohort weights (eq. (23)) for the per-cell variance
`σⱼₜ² = Cⱼⱼ + sⱼ²/wⱼₜ`. -/
noncomputable def invVarA (j : J) (t : T) : ℝ :=
  invVarWeight (fun s => M.C j j + M.s2 j / M.w j s) t

omit [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] in
lemma sigmaSq_pos (j : J) (t : T) : 0 < M.C j j + M.s2 j / M.w j t :=
  add_pos_of_nonneg_of_pos (M.C_posSemidef.diag_nonneg)
    (div_pos (M.s2_pos j) (M.w_pos j t))

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma sum_invVarA [Nonempty T] (j : J) : ∑ t, M.invVarA j t = 1 :=
  sum_invVarWeight _ (M.sigmaSq_pos j)

/-! ### Estimation (§2.8): residuals within each cohort

`Model.UnbiasedCov` for the table `cov` of this model. The cohort weights `a` are any
fixed weights summing to one (not estimated), e.g. the exposure weights `wⱼₜ/wⱼ*`. -/

variable (a)

/-- The residual `rⱼₜ = μⱼₜ - μ̂ⱼ`, `μ̂ⱼ = Σₛ aⱼₛμⱼₛ`. -/
def res (X : J × T → ℝ) (j : J) (t : T) : ℝ := X (j, t) - ∑ s, a j s * X (j, s)

/-- The shock coefficient `dᵢⱼₜ = 1 - aᵢₜ - aⱼₜ + Σₛ aᵢₛaⱼₛ` of `E[rᵢₜrⱼₜ]`. -/
def d (i j : J) (t : T) : ℝ := 1 - a i t - a j t + ∑ s, a i s * a j s

/-- The process-noise coefficient `hⱼₜ = (1 - 2aⱼₜ)/wⱼₜ + Σₛ aⱼₛ²/wⱼₛ` of `E[rⱼₜ²]`. -/
noncomputable def h (j : J) (t : T) : ℝ := (1 - 2 * a j t) / M.w j t + ∑ s, a j s ^ 2 / M.w j s

variable {a}

/-- Same-period residual products: `E[rᵢₜrⱼₜ] = dᵢⱼₜCᵢⱼ + δᵢⱼ hᵢₜsᵢ²`. The level variance `τ²`
and the mean cancel within each cohort; only the period shock links two cohorts. -/
theorem unbiased_res (ha : ∀ j, ∑ t, a j t = 1) (i j : J) (t : T) :
    Model.UnbiasedCov M.cov (fun X => res a X i t * res a X j t)
      (d a i j t * M.C i j + (if i = j then M.s2 i * M.h a i t else 0)) := by
  -- Coefficients of `rₖₜ`: `cₖ(t') = δₜₜ' - aₖₜ'` on cohort `k`.
  let c : J → T → ℝ := fun k t' => (if t' = t then 1 else 0) - a k t'
  let ℓ : J → J × T → ℝ := fun k p => if p.1 = k then c k p.2 else 0
  have hc0 : ∀ k, ∑ t', c k t' = 0 := fun k => by simp [c, sum_sub_distrib, ha]
  have hlin : ∀ k (X : J × T → ℝ), ∑ p, ℓ k p * X p = res a X k t := fun k X => by
    rw [Fintype.sum_prod_type, sum_eq_single k (fun l _ hl => by simp [ℓ, hl]) (by simp)]
    simp [ℓ, c, res, sub_mul, sum_sub_distrib]
  have hsum : ∑ p, ℓ i p = 0 := by
    have := hlin i (fun _ => 1)
    simp only [mul_one] at this
    rw [this, res]; simp [ha]
  have hpair : ∀ F : J × T → J × T → ℝ,
      ∑ p, ∑ q, ℓ i p * ℓ j q * F p q = ∑ t', ∑ s', c i t' * c j s' * F (i, t') (j, s') := by
    intro F
    rw [Fintype.sum_prod_type, sum_eq_single i (fun k _ hk => by simp [ℓ, hk]) (by simp)]
    refine sum_congr rfl fun t' _ => ?_
    rw [Fintype.sum_prod_type, sum_eq_single j (fun l _ hl => by simp [ℓ, hl]) (by simp)]
    simp [ℓ]
  have hd : ∑ t', c i t' * c j t' = d a i j t := by
    simp only [c, d, sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
      sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
    ring
  have hh : ∑ t', c i t' * c i t' * (M.s2 i / M.w i t') = M.s2 i * M.h a i t := by
    simp only [c, h]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
      sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
    rw [mul_add, mul_sum, show ∑ x, a i x * a i x * (M.s2 i / M.w i x)
      = ∑ x, M.s2 i * (a i x ^ 2 / M.w i x) from sum_congr rfl fun x _ => by ring]
    ring
  refine (Model.unbiasedCov_mul M.cov (ℓ i) (ℓ j) hsum).congr (fun X => by rw [hlin, hlin]) ?_
  rw [hpair]
  simp only [cov, obsCov, mul_add, sum_add_distrib]
  have hτ : ∑ t', ∑ s', c i t' * c j s' * (M.τ2 * (if i = j then 1 else 0)) = 0 := by
    simp only [← sum_mul, ← mul_sum, hc0, mul_zero, zero_mul, sum_const_zero]
  rw [hτ, add_zero]
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, mul_add, sum_add_distrib]
  rw [← sum_mul, hd]
  congr 1
  split_ifs with hij
  · subst hij; exact hh
  · simp

variable (a) in
/-- `Ĉᵢⱼ = Σₜ rᵢₜrⱼₜ / Σₜ dᵢⱼₜ`, the estimator of the shock covariance for `i ≠ j`. -/
noncomputable def crossHat (X : J × T → ℝ) (i j : J) : ℝ :=
  (∑ t, res a X i t * res a X j t) / ∑ t, d a i j t

/-- `Ĉᵢⱼ` is unbiased for `Cᵢⱼ` (`i ≠ j`) whenever `Σₜ dᵢⱼₜ ≠ 0` (`sum_d_pos`). -/
theorem crossHat_unbiased (ha : ∀ j, ∑ t, a j t = 1) {i j : J} (hij : i ≠ j)
    (hd : ∑ t, d a i j t ≠ 0) :
    Model.UnbiasedCov M.cov (fun X => crossHat a X i j) (M.C i j) := by
  refine (Model.UnbiasedCov.const_mul (∑ t, d a i j t)⁻¹
    (Model.UnbiasedCov.sum univ fun t _ => M.unbiased_res ha i j t)).congr
    (fun X => by rw [crossHat, div_eq_inv_mul]) ?_
  simp only [hij, ite_false, add_zero, ← sum_mul]
  rw [inv_mul_cancel_left₀ hd]

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- `Σₜ dᵢⱼₜ = |T| - 2 + |T|Σₜ aᵢₜaⱼₜ > 0` for positive weights and `|T| ≥ 2`. -/
theorem sum_d_pos (ha : ∀ j, ∑ t, a j t = 1) (hpos : ∀ j t, 0 < a j t)
    (hT : 2 ≤ Fintype.card T) (i j : J) : 0 < ∑ t, d a i j t := by
  have hne : (univ : Finset T).Nonempty := univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
  have hg : 0 < ∑ s, a i s * a j s := sum_pos (fun s _ => mul_pos (hpos i s) (hpos j s)) hne
  have h2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have : ∑ t, d a i j t = (Fintype.card T : ℝ) - 2 + Fintype.card T * ∑ s, a i s * a j s := by
    simp only [d, sum_add_distrib, sum_sub_distrib, ha, sum_const, card_univ, nsmul_eq_mul,
      mul_one]
    ring
  rw [this]
  nlinarith

/-! #### The diagonal: shock and process noise separated by two weightings -/

variable (a) (u : J → T → ℝ)

/-- A weighted sum of squared residuals `Σₜ uⱼₜ rⱼₜ²`. -/
noncomputable def sqSum (X : J × T → ℝ) (j : J) : ℝ := ∑ t, u j t * res a X j t ^ 2

/-- Its shock coefficient `Σₜ uⱼₜ dⱼⱼₜ`. -/
def dSum (j : J) : ℝ := ∑ t, u j t * d a j j t

/-- Its process-noise coefficient `Σₜ uⱼₜ hⱼₜ`. -/
noncomputable def hSum (j : J) : ℝ := ∑ t, u j t * M.h a j t

variable {a u}

/-- `E Σₜ uⱼₜ rⱼₜ² = (Σₜ uⱼₜdⱼⱼₜ)Cⱼⱼ + (Σₜ uⱼₜhⱼₜ)sⱼ²`. -/
theorem sqSum_unbiased (ha : ∀ j, ∑ t, a j t = 1) (j : J) :
    Model.UnbiasedCov M.cov (fun X => sqSum a u X j)
      (dSum a u j * M.C j j + M.hSum a u j * M.s2 j) := by
  refine (Model.UnbiasedCov.sum univ fun t _ =>
    (M.unbiased_res ha j j t).const_mul (u j t)).congr
    (fun X => by simp only [sqSum, sq]) ?_
  simp only [ite_true, dSum, hSum, mul_add, sum_add_distrib]
  rw [sum_mul, sum_mul]
  congr 1 <;> exact sum_congr rfl fun t _ => by ring

variable (a u) (v : J → T → ℝ)

/-- The determinant of the 2×2 system for `(Cⱼⱼ, sⱼ²)` from the weightings `u`, `v`. -/
noncomputable def det (j : J) : ℝ := dSum a u j * M.hSum a v j - dSum a v j * M.hSum a u j

/-- `Ĉⱼⱼ`, by Cramer's rule from `Σₜ uⱼₜrⱼₜ²` and `Σₜ vⱼₜrⱼₜ²`. -/
noncomputable def CdiagHat (X : J × T → ℝ) (j : J) : ℝ :=
  (M.hSum a v j * sqSum a u X j - M.hSum a u j * sqSum a v X j) / M.det a u v j

/-- `ŝⱼ²`, by Cramer's rule from `Σₜ uⱼₜrⱼₜ²` and `Σₜ vⱼₜrⱼₜ²`. -/
noncomputable def s2Hat (X : J × T → ℝ) (j : J) : ℝ :=
  (dSum a u j * sqSum a v X j - dSum a v j * sqSum a u X j) / M.det a u v j

variable {a u v}

/-- `Ĉⱼⱼ` is unbiased for `Cⱼⱼ` when the determinant is nonzero. -/
theorem CdiagHat_unbiased (ha : ∀ j, ∑ t, a j t = 1) {j : J} (hdet : M.det a u v j ≠ 0) :
    Model.UnbiasedCov M.cov (fun X => M.CdiagHat a u v X j) (M.C j j) := by
  refine (Model.UnbiasedCov.const_mul (M.det a u v j)⁻¹
    (((M.sqSum_unbiased (u := u) ha j).const_mul (M.hSum a v j)).add
      ((M.sqSum_unbiased (u := v) ha j).const_mul (-M.hSum a u j)))).congr
    (fun X => by rw [CdiagHat, div_eq_inv_mul]; ring) ?_
  rw [inv_mul_eq_iff_eq_mul₀ hdet, det]
  ring

/-- `ŝⱼ²` is unbiased for `sⱼ²` when the determinant is nonzero. -/
theorem s2Hat_unbiased (ha : ∀ j, ∑ t, a j t = 1) {j : J} (hdet : M.det a u v j ≠ 0) :
    Model.UnbiasedCov M.cov (fun X => M.s2Hat a u v X j) (M.s2 j) := by
  refine (Model.UnbiasedCov.const_mul (M.det a u v j)⁻¹
    (((M.sqSum_unbiased (u := v) ha j).const_mul (dSum a u j)).add
      ((M.sqSum_unbiased (u := u) ha j).const_mul (-dSum a v j)))).congr
    (fun X => by rw [s2Hat, div_eq_inv_mul]; ring) ?_
  rw [inv_mul_eq_iff_eq_mul₀ hdet, det]
  ring

variable (a u v) in
/-- The estimated shock covariance: `Ĉⱼⱼ` on the diagonal, `Ĉᵢⱼ` off it. -/
noncomputable def CHat (X : J × T → ℝ) (i j : J) : ℝ :=
  if i = j then M.CdiagHat a u v X i else crossHat a X i j

/-- Every entry of `Ĉ` is unbiased for the shock covariance `C`. -/
theorem CHat_unbiased (ha : ∀ j, ∑ t, a j t = 1)
    (hd : ∀ i j, i ≠ j → ∑ t, d a i j t ≠ 0) (hdet : ∀ j, M.det a u v j ≠ 0) (i j : J) :
    Model.UnbiasedCov M.cov (fun X => M.CHat a u v X i j) (M.C i j) := by
  by_cases hij : i = j
  · subst hij
    simpa [CHat] using M.CdiagHat_unbiased ha (hdet i)
  · simpa [CHat, hij] using M.crossHat_unbiased ha hij (hd i j hij)

/-! #### Identification needs volume variation -/

/-- **No estimator separates shock and process noise at a constant volume.** If cohort `j`
has the same volume in every period, no function of the data is unbiased for `sⱼ²` in
every model with these volumes: the data see only `Cⱼⱼ + sⱼ²/wⱼ`. -/
theorem not_unbiased_s2_of_const [Nonempty T] (j : J) (hw : ∀ t t', M.w j t = M.w j t')
    (f : (J × T → ℝ) → ℝ) :
    ¬ ∀ M' : Shock J T, M'.w = M.w → Model.UnbiasedCov M'.cov f (M'.s2 j) := by
  intro H
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  set e := M.s2 j / 2 with he
  have he0 : 0 < e := half_pos (M.s2_pos j)
  -- Move half of `sⱼ²/wⱼ` from the process noise into the shock variance `Cⱼⱼ`.
  let M' : Shock J T :=
    { M with
      s2 := Function.update M.s2 j e
      C := M.C + diagonal (Pi.single j (e / M.w j t₀))
      C_posSemidef := M.C_posSemidef.add (PosSemidef.diagonal fun k => by
        by_cases hk : k = j
        · subst hk; simp [(div_pos he0 (M.w_pos k t₀)).le]
        · simp [hk])
      s2_pos := fun k => by
        by_cases hk : k = j
        · subst hk; simp [he0]
        · simp [hk, M.s2_pos k] }
  have hcov : M'.cov = M.cov := by
    funext p q
    simp only [cov, obsCov, M']
    by_cases hpq : p.1 = q.1
    · rw [hpq]
      by_cases hq : q.1 = j
      · rw [hq]
        simp only [Matrix.add_apply, diagonal_apply_eq, Pi.single_eq_same, Function.update_self,
          ite_true]
        split_ifs with ht
        · rw [hw p.2 t₀, he]; ring
        · rfl
      · simp [hq, diagonal_apply_eq]
    · simp [hpq]
  have h1 := H M rfl
  have h2 := H M' rfl
  rw [hcov] at h2
  have := Model.UnbiasedCov.unique M.cov_symm h1 h2
  simp only [M', Function.update_self] at this
  linarith

/-! #### Exposure weights: the coefficients in closed form -/

/-- `wⱼ* = Σₜ wⱼₜ`. -/
def wtot (j : J) : ℝ := ∑ t, M.w j t

/-- Exposure weights `wⱼₜ/wⱼ*`. -/
noncomputable def expo (j : J) (t : T) : ℝ := M.w j t / M.wtot j

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma wtot_pos [Nonempty T] (j : J) : 0 < M.wtot j :=
  sum_pos (fun t _ => M.w_pos j t) univ_nonempty

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma sum_expo [Nonempty T] (j : J) : ∑ t, M.expo j t = 1 := by
  simp only [expo, ← sum_div]; exact div_self (M.wtot_pos j).ne'

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Exposure weights, residuals weighted by volume (the Bühlmann–Straub sum):
`E Σₜ wⱼₜrⱼₜ² = (wⱼ* - Σₜ wⱼₜ²/wⱼ*)Cⱼⱼ + (|T| - 1)sⱼ²`; first the shock coefficient… -/
theorem dSum_expo_w [Nonempty T] (j : J) :
    dSum M.expo M.w j = M.wtot j - (∑ t, M.w j t ^ 2) / M.wtot j := by
  have hW := (M.wtot_pos j).ne'
  simp only [dSum, d, expo, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul]
  rw [show ∑ t, M.w j t = M.wtot j from rfl]
  simp only [mul_div_assoc', sum_div]
  simp only [← sum_div, show ∑ t, M.w j t * M.w j t = ∑ t, M.w j t ^ 2 from
    sum_congr rfl fun t _ => (sq _).symm, mul_one]
  rw [show ∑ i, M.w j i / M.wtot j * M.w j i = (∑ t, M.w j t ^ 2) / M.wtot j by
    rw [sum_div]; exact sum_congr rfl fun t _ => by ring]
  field_simp
  ring

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- …and the process-noise coefficient `|T| - 1`. -/
theorem hSum_expo_w [Nonempty T] (j : J) :
    M.hSum M.expo M.w j = (Fintype.card T : ℝ) - 1 := by
  have hW := (M.wtot_pos j).ne'
  have hterm : ∀ t, M.w j t * M.h M.expo j t = 1 - M.w j t / M.wtot j := fun t => by
    have hs : ∑ s, M.expo j s ^ 2 / M.w j s = (M.wtot j)⁻¹ := by
      rw [show (M.wtot j)⁻¹ = ∑ s, M.w j s / M.wtot j ^ 2 by
        rw [← sum_div, show ∑ s, M.w j s = M.wtot j from rfl]; field_simp]
      exact sum_congr rfl fun s _ => by
        have := (M.w_pos j s).ne'; simp only [expo]; field_simp
    have := (M.w_pos j t).ne'
    rw [h, hs]; simp only [expo]; field_simp; ring
  simp only [hSum, hterm, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← sum_div]
  rw [show ∑ t, M.w j t = M.wtot j from rfl, div_self hW]

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Exposure weights, unweighted residuals: shock coefficient `|T| - 2 + |T|Σₜ(wⱼₜ/wⱼ*)²`… -/
theorem dSum_expo_one [Nonempty T] (j : J) :
    dSum M.expo (fun _ _ => 1) j
      = (Fintype.card T : ℝ) - 2 + Fintype.card T * ∑ t, M.expo j t ^ 2 := by
  simp only [dSum, d, one_mul, sum_add_distrib, sum_sub_distrib, M.sum_expo, sum_const,
    card_univ, nsmul_eq_mul, mul_one, sq]
  ring

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- …and process-noise coefficient `Σₜ 1/wⱼₜ - |T|/wⱼ*`. -/
theorem hSum_expo_one [Nonempty T] (j : J) :
    M.hSum M.expo (fun _ _ => 1) j = ∑ t, (M.w j t)⁻¹ - Fintype.card T / M.wtot j := by
  have hW := (M.wtot_pos j).ne'
  have hs : ∑ s, M.expo j s ^ 2 / M.w j s = (M.wtot j)⁻¹ := by
    rw [show (M.wtot j)⁻¹ = ∑ s, M.w j s / M.wtot j ^ 2 by
      rw [← sum_div, show ∑ s, M.w j s = M.wtot j from rfl]; field_simp]
    exact sum_congr rfl fun s _ => by
      have := (M.w_pos j s).ne'; simp only [expo]; field_simp
  have hterm : ∀ t, M.h M.expo j t = (M.w j t)⁻¹ - (M.wtot j)⁻¹ := fun t => by
    have := (M.w_pos j t).ne'
    rw [h, hs]; simp only [expo]; field_simp; ring
  simp only [hSum, one_mul, hterm, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

end Shock

end Credibility
