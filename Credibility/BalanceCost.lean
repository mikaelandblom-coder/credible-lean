import Credibility.CoreMoments

/-!
# The cost of balancing: one common shift (extension, distribution-free)

Balancing moves every rate by the same `D`, so that the exposure-weighted rate hits a chosen
portfolio level `T` (the historical exposure average `Σ uⱼμ̂ⱼ`, or a cross-fitted level, …):
`D = T - Σ uⱼ rⱼ`, with exposure shares `uⱼ` (`Σ uⱼ = 1`). Here:

* `sum_sq_shift` (any numbers) and `integral_sum_sq_shift` (any random rates, levels and target,
  square integrable): the exposure-weighted squared error after the shift is the one before,
  plus `(T - μ̄)²`, minus `(r̄ - μ̄)²`, where `μ̄ = Σ uⱼμⱼ` and `r̄ = Σ uⱼrⱼ`. So balancing replaces
  the fit's own error for the portfolio level with the target's, and changes nothing else: it
  pays exactly when `T` estimates `μ̄` better than `r̄` does.
* `Estimates.portTarget`: the portfolio level `μ̄` as a prediction target, with moments
  `cov(μ̂ᵢ, μ̄) = (uᵀL)ᵢ` and `Var μ̄ = uᵀLu`.
* `Estimates.balance_blup_cost`: for the BLUP (known moments) balanced to the historical exposure
  average, the cost is exactly `(u - c)ᵀK(u - c) ≥ 0`, with `c = Σⱼ uⱼ d*ⱼ`: `r̄ = cᵀμ̂` is the
  best unbiased estimate of `μ̄`, so no target built linearly from the `μ̂ᵢ` beats it.

Nothing about the distribution is assumed.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility

variable {J : Type*} [Fintype J]

/-- **A common shift, pointwise.** For shares `u` (`Σ uⱼ = 1`), rates `r`, levels `m` and a target
`t`, the shift `D = t - Σ uᵢrᵢ` gives
`Σ uⱼ(rⱼ + D - mⱼ)² = Σ uⱼ(rⱼ - mⱼ)² + (t - Σ uᵢmᵢ)² - (Σ uᵢrᵢ - Σ uᵢmᵢ)²`. -/
theorem sum_sq_shift (u r m : J → ℝ) (hu : ∑ j, u j = 1) (t : ℝ) :
    ∑ j, u j * (r j + (t - ∑ i, u i * r i) - m j) ^ 2
      = ∑ j, u j * (r j - m j) ^ 2 + (t - ∑ i, u i * m i) ^ 2
        - (∑ i, u i * r i - ∑ i, u i * m i) ^ 2 := by
  set D := t - ∑ i, u i * r i
  have h : ∀ j, u j * (r j + D - m j) ^ 2
      = u j * (r j - m j) ^ 2 + 2 * D * (u j * r j - u j * m j) + D ^ 2 * u j := fun j => by ring
  simp only [h, sum_add_distrib, ← mul_sum, sum_sub_distrib, hu]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The cost of a common shift.** For any square-integrable random rates `rⱼ`, levels `μⱼ` and
target `T`, shifting by `D = T - Σ uᵢrᵢ` changes the exposure-weighted mean squared error by
`E(T - μ̄)² - E(r̄ - μ̄)²` (`μ̄ = Σ uᵢμᵢ`, `r̄ = Σ uᵢrᵢ`), for every distribution. -/
theorem integral_sum_sq_shift (u : J → ℝ) (hu : ∑ j, u j = 1) (r lev : J → Ω → ℝ)
    (T : Ω → ℝ) (hr : ∀ j, MemLp (r j) 2 P) (hl : ∀ j, MemLp (lev j) 2 P) (hT : MemLp T 2 P) :
    P[fun ω => ∑ j, u j * (r j ω + (T ω - ∑ i, u i * r i ω) - lev j ω) ^ 2]
      = P[fun ω => ∑ j, u j * (r j ω - lev j ω) ^ 2]
        + P[fun ω => (T ω - ∑ i, u i * lev i ω) ^ 2]
        - P[fun ω => (∑ i, u i * r i ω - ∑ i, u i * lev i ω) ^ 2] := by
  have hsum : ∀ (f : J → Ω → ℝ), (∀ j, MemLp (f j) 2 P) →
      MemLp (fun ω => ∑ i, u i * f i ω) 2 P := fun f hf =>
    memLp_finsetSum _ fun i _ => (hf i).const_mul (u i)
  have i1 : Integrable (fun ω => ∑ j, u j * (r j ω - lev j ω) ^ 2) P :=
    integrable_finsetSum _ fun j _ => (((hr j).sub (hl j)).integrable_sq).const_mul (u j)
  have i2 : Integrable (fun ω => (T ω - ∑ i, u i * lev i ω) ^ 2) P :=
    (hT.sub (hsum lev hl)).integrable_sq
  have i3 : Integrable (fun ω => (∑ i, u i * r i ω - ∑ i, u i * lev i ω) ^ 2) P :=
    ((hsum r hr).sub (hsum lev hl)).integrable_sq
  simp_rw [sum_sq_shift u (fun j => r j _) (fun j => lev j _) hu]
  have e := integral_sub (i1.add i2) i3
  simp only [Pi.add_apply] at e
  rw [e, integral_add i1 i2]

namespace Core

variable [DecidableEq J] {K L : Matrix J J ℝ} {μ : ℝ}

namespace Estimates

variable (E : Estimates K L μ P)

/-- **The portfolio level as a target.** With shares `u` (`Σ uⱼ = 1`), `μ̄ = Σ uⱼμⱼ` has mean `μ`,
`cov(μ̂ᵢ, μ̄) = (uᵀL)ᵢ` and `Var μ̄ = uᵀLu`. -/
noncomputable def portTarget [IsProbabilityMeasure P] (u : J → ℝ) (hu : ∑ j, u j = 1) :
    Target K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) (replicateCol Unit (1 : J → ℝ)) 1 (fun _ => μ) P where
  x := E.est
  Y := fun ω => ∑ j, u j * E.level j ω
  x_memLp := E.est_memLp
  Y_memLp := memLp_finsetSum _ fun j _ => (E.level_memLp j).const_mul (u j)
  x_mean i := by simp [mulVec, dotProduct, replicateCol, E.est_mean]
  Y_mean := by
    rw [integral_finsetSum _ fun j _ => ((E.level_memLp j).const_mul (u j)).integrable
      (by norm_num)]
    simp [integral_const_mul, E.level_mean, ← sum_mul, hu]
  cov_x := E.cov_est
  cov_x_Y i := by
    rw [covariance_fun_sum_right (fun j => (E.level_memLp j).const_mul (u j)) (E.est_memLp i)]
    simp only [covariance_const_mul_right, vecMul, dotProduct]
    exact sum_congr rfl fun j _ => by rw [covariance_comm, E.cov_level_est]
  var_Y := by
    rw [← covariance_self (memLp_finsetSum _ fun j _ => (E.level_memLp j).const_mul (u j)
      : MemLp (fun ω => ∑ j, u j * E.level j ω) 2 P).aestronglyMeasurable.aemeasurable,
      covariance_fun_sum_fun_sum (fun i => (E.level_memLp i).const_mul (u i))
        (fun j => (E.level_memLp j).const_mul (u j))]
    simp only [covariance_const_mul_left, covariance_const_mul_right, E.cov_level,
      dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

omit [DecidableEq J] in
/-- `Σⱼ uⱼ (dⱼᵀμ̂) = (Σⱼ uⱼdⱼ)ᵀμ̂`. -/
lemma sum_mul_portLin (u : J → ℝ) (d : J → J → ℝ) (ω : Ω) :
    ∑ j, u j * E.portLin (d j) ω = E.portLin (∑ j, u j • d j) ω := by
  simp only [portLin, Core.portLin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum,
    sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

variable [IsProbabilityMeasure P]

/-- **Balancing the BLUP to the historical exposure average costs `(u - c)ᵀK(u - c)`.** With known
moments, shifting the BLUP's rates `d*ⱼᵀμ̂` so that their exposure average is `Σ uⱼμ̂ⱼ` raises the
exposure-weighted mean squared error by exactly `(u - c)ᵀK(u - c)`, `c = Σⱼ uⱼd*ⱼ`, for every
distribution with these moments. It is never negative and is zero only when `u = c`. -/
theorem balance_blup_cost (hK : K.PosDef) (u : J → ℝ) (hu : ∑ j, u j = 1) :
    P[fun ω => ∑ j, u j * (E.portLin (blupWeight K L j) ω
        + (E.portLin u ω - ∑ i, u i * E.portLin (blupWeight K L i) ω) - E.level j ω) ^ 2]
      = P[fun ω => ∑ j, u j * (E.portLin (blupWeight K L j) ω - E.level j ω) ^ 2]
        + (u - ∑ j, u j • blupWeight K L j)
            ⬝ᵥ (K *ᵥ (u - ∑ j, u j • blupWeight K L j)) := by
  have : Nonempty J := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hu
  set c := ∑ j, u j • blupWeight K L j
  set Tg := E.portTarget u hu
  have hc : ∑ i, c i = 1 := by
    simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    simp [← mul_sum, sum_blupWeight hK, hu]
  have hX : ∀ d : J → ℝ, ∑ i, d i = 1 →
      (replicateCol Unit (1 : J → ℝ))ᵀ *ᵥ d = 1 := fun d hd => by
    rw [replicateCol_one_transpose_mulVec, hd]; rfl
  rw [integral_sum_sq_shift u hu _ E.level _ (fun j => E.memLp_portLin _) E.level_memLp
    (E.memLp_portLin u)]
  simp_rw [E.sum_mul_portLin u (fun j => blupWeight K L j)]
  have h1 := Tg.mse_portLin (hX u hu)
  have h2 := Tg.mse_portLin (hX c hc)
  simp only [Tg, portTarget] at h1 h2
  have hu' : P[fun ω => (E.portLin u ω - ∑ i, u i * E.level i ω) ^ 2]
      = predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) u := h1
  have hc' : P[fun ω => (E.portLin c ω - ∑ i, u i * E.level i ω) ^ 2]
      = predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) c := h2
  rw [hu', hc']
  -- `Kc - uᵀL` is constant: `Kd*ⱼ - Lⱼ` is, for every `j`.
  have he : K *ᵥ c - vecMul u L
      = replicateCol Unit (1 : J → ℝ) *ᵥ fun _ =>
          ∑ j, u j * ((1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹) := by
    funext i
    have hKc : (K *ᵥ c) i = ∑ j, u j * (K *ᵥ blupWeight K L j) i := by
      simp [c, mulVec_sum, mulVec_smul]
    have hvL : vecMul u L i = ∑ j, u j * L j i := rfl
    have hR : (replicateCol Unit (1 : J → ℝ) *ᵥ fun _ =>
        ∑ j, u j * ((1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹)) i
        = ∑ j, u j * ((1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹) := by
      simp [mulVec, dotProduct, replicateCol]
    rw [Pi.sub_apply, hKc, hvL, hR, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by rw [← mulVec_blupWeight hK L j i]; ring
  have hp := predMse_eq_add_of_normal hK.isHermitian (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) _ he
    (d := u) (by rw [hX u hu, hX c hc])
  rw [hp]
  ring

end Estimates
end Core
end Credibility
