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
* `Estimates.balance_cost_portLin`: for fixed rate weights `dⱼ` and target weights `a`, the cost is
  `mse(a) - mse(c)` in closed form at the level of `K`, `c = Σⱼ uⱼdⱼ` (on fitted moments: the
  plug-in rule of study S76).
* `Estimates.balance_blup_cost`: for the BLUP (known moments) balanced to the historical exposure
  average, the cost is exactly `(u - c)ᵀK(u - c) ≥ 0`, with `c = Σⱼ uⱼ d*ⱼ`: `r̄ = cᵀμ̂` is the
  best unbiased estimate of `μ̄`, so no target built linearly from the `μ̂ᵢ` beats it.

* `integral_sq_cellLin_sub`, `balance_cost_cellLin` (any volumes): estimates linear in the yearly
  cells `Xᵢₛ = μᵢ + eᵢₛ` (the cross-fitted level `Σₛ πₛc⁽ˢ⁾ᵀXₛ` is one; it is not a function of the `μ̂ᵢ`
  unless the regions' volumes share one shape) have error `(G − u)ᵀL(G − u) + Σₛ gₛᵀDₛgₛ` for `μ̄`, so
  the cost of balancing to them is closed form for any volumes (S82).

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

omit [DecidableEq J] in
/-- **The cost of balancing fixed weights, at the level of `K`.** Rates `dⱼᵀμ̂` (`Σᵢ dⱼᵢ = 1`) shifted
to a target `aᵀμ̂` (`Σ aᵢ = 1`, e.g. the exposure average `a = u`, or a cross-fitted level with its
mean weights): the exposure-weighted mean squared error changes by exactly
`mse(a) - mse(c)`, `c = Σⱼ uⱼdⱼ`, `mse(e) = eᵀKe - 2eᵀ(uᵀL) + uᵀLu` the true error of `eᵀμ̂` for
`μ̄`, for every distribution with these moments. On fitted moments this is the plug-in rule of
study S76. -/
theorem balance_cost_portLin (u : J → ℝ) (hu : ∑ j, u j = 1) (d : J → J → ℝ)
    (hd : ∀ j, ∑ i, d j i = 1) (a : J → ℝ) (ha : ∑ i, a i = 1) :
    P[fun ω => ∑ j, u j * (E.portLin (d j) ω
        + (E.portLin a ω - ∑ i, u i * E.portLin (d i) ω) - E.level j ω) ^ 2]
      = P[fun ω => ∑ j, u j * (E.portLin (d j) ω - E.level j ω) ^ 2]
        + predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) a
        - predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) (∑ j, u j • d j) := by
  set c := ∑ j, u j • d j
  set Tg := E.portTarget u hu
  have hc : ∑ i, c i = 1 := by
    simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    simp [← mul_sum, hd, hu]
  have hX : ∀ e : J → ℝ, ∑ i, e i = 1 →
      (replicateCol Unit (1 : J → ℝ))ᵀ *ᵥ e = 1 := fun e he => by
    rw [replicateCol_one_transpose_mulVec, he]; rfl
  rw [integral_sum_sq_shift u hu _ E.level _ (fun j => E.memLp_portLin _) E.level_memLp
    (E.memLp_portLin a)]
  simp_rw [E.sum_mul_portLin u d]
  have h1 := Tg.mse_portLin (hX a ha)
  have h2 := Tg.mse_portLin (hX c hc)
  simp only [Tg, portTarget] at h1 h2
  have ha' : P[fun ω => (E.portLin a ω - ∑ i, u i * E.level i ω) ^ 2]
      = predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) a := h1
  have hc' : P[fun ω => (E.portLin c ω - ∑ i, u i * E.level i ω) ^ 2]
      = predMse K (vecMul u L) (u ⬝ᵥ (L *ᵥ u)) c := h2
  rw [ha', hc']

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
  rw [E.balance_cost_portLin u hu (fun j => blupWeight K L j) (fun j => sum_blupWeight hK L j) u hu]
  set c := ∑ j, u j • blupWeight K L j
  have hX : ∀ e : J → ℝ, ∑ i, e i = 1 →
      (replicateCol Unit (1 : J → ℝ))ᵀ *ᵥ e = 1 := fun e he => by
    rw [replicateCol_one_transpose_mulVec, he]; rfl
  have hc : ∑ i, c i = 1 := by
    simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    simp [← mul_sum, sum_blupWeight hK, hu]
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
section YearlyCells

/-! ### Targets built from the yearly cells (any volumes) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The cell-linear estimate `Σₛ Σᵢ gₛᵢ Xᵢₛ` of yearly cells `Xᵢₛ = μᵢ + eᵢₛ`. -/
noncomputable def cellLin (lev : J → Ω → ℝ) (e : J → S → Ω → ℝ) (g : S → J → ℝ) (ω : Ω) : ℝ :=
  ∑ s, ∑ i, g s i * (lev i ω + e i s ω)

/-- **The error of a cell-linear estimate of the portfolio level** (any volumes). Yearly cells
`Xᵢₛ = μᵢ + eᵢₛ`: levels with mean `μ` and covariance `L`, noise centred, uncorrelated with the
levels, with covariance `Dₛ` within year `s` and none across years. For weights `gₛᵢ` summing to
one and shares `u` (`Σ uᵢ = 1`), with `Gᵢ = Σₛ gₛᵢ` (each region's total weight),
`E(Σₛᵢ gₛᵢXᵢₛ − Σᵢ uᵢμᵢ)² = (G − u)ᵀL(G − u) + Σₛ gₛᵀDₛgₛ`, for every distribution with these
moments. The cross-fitted level (`gₛ = πₛc⁽ˢ⁾`) and the fit's own `r̄` (`gₛᵢ = (Σⱼ uⱼdⱼᵢ)aᵢₛ`) are both
of this form. -/
theorem integral_sq_cellLin_sub (lev : J → Ω → ℝ) (e : J → S → Ω → ℝ) (μ : ℝ)
    (L : Matrix J J ℝ) (D : S → Matrix J J ℝ)
    (hl : ∀ i, MemLp (lev i) 2 P) (he : ∀ i s, MemLp (e i s) 2 P)
    (hlm : ∀ i, P[lev i] = μ) (hem : ∀ i s, P[e i s] = 0)
    (hL : ∀ i j, cov[lev i, lev j; P] = L i j) (hLe : ∀ i j s, cov[lev i, e j s; P] = 0)
    (hD : ∀ i j s s', cov[e i s, e j s'; P] = if s = s' then D s i j else 0)
    (g : S → J → ℝ) (u : J → ℝ) (hg : ∑ s, ∑ i, g s i = 1) (hu : ∑ i, u i = 1) :
    P[fun ω => (cellLin lev e g ω - ∑ i, u i * lev i ω) ^ 2]
      = (fun i => ∑ s, g s i - u i) ⬝ᵥ (L *ᵥ fun i => ∑ s, g s i - u i)
        + ∑ s, g s ⬝ᵥ (D s *ᵥ g s) := by
  set a : J → ℝ := fun i => ∑ s, g s i - u i with ha
  -- the error as one linear combination of levels and noise
  let Z : J ⊕ (S × J) → Ω → ℝ := Sum.elim lev fun p => e p.2 p.1
  let k : J ⊕ (S × J) → ℝ := Sum.elim a fun p => g p.1 p.2
  have hZ : ∀ q, MemLp (Z q) 2 P := fun q => by cases q with
    | inl i => exact hl i
    | inr p => exact he p.2 p.1
  have hY : (fun ω => cellLin lev e g ω - ∑ i, u i * lev i ω) = fun ω => ∑ q, k q * Z q ω := by
    funext ω
    simp only [cellLin, Fintype.sum_sum_type, Fintype.sum_prod_type, k, Z, Sum.elim_inl,
      Sum.elim_inr, ha, mul_add, sum_add_distrib, sub_mul]
    rw [sum_comm (f := fun s i => g s i * lev i ω), sum_sub_distrib]
    simp only [← sum_mul]
    ring
  have hkZ : ∀ q, MemLp (fun ω => k q * Z q ω) 2 P := fun q => (hZ q).const_mul _
  have hYm : MemLp (fun ω => ∑ q, k q * Z q ω) 2 P := memLp_finsetSum _ fun q _ => hkZ q
  have hmean : P[fun ω => ∑ q, k q * Z q ω] = 0 := by
    rw [integral_finsetSum _ fun q _ => (hkZ q).integrable (by norm_num)]
    simp only [integral_const_mul, Fintype.sum_sum_type, Fintype.sum_prod_type, k, Z,
      Sum.elim_inl, Sum.elim_inr]
    simp only [hlm, hem, mul_zero, sum_const_zero, add_zero, ← sum_mul, ha, sum_sub_distrib, hu]
    rw [sum_comm, hg]; ring
  have hY' : ∀ ω, cellLin lev e g ω - ∑ i, u i * lev i ω = ∑ q, k q * Z q ω := fun ω =>
    congrFun hY ω
  simp only [hY']
  have hv := variance_eq_sub hYm
  rw [hmean] at hv
  change P[fun ω => (∑ q, k q * Z q ω) ^ 2] = _
  have hsq : P[fun ω => (∑ q, k q * Z q ω) ^ 2] = Var[fun ω => ∑ q, k q * Z q ω; P] := by
    rw [hv]; simp
  rw [hsq, ← covariance_self hYm.aemeasurable, covariance_fun_sum_fun_sum hkZ hkZ]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, k, Z, Sum.elim_inl, Sum.elim_inr, hL,
    hLe, hD, covariance_comm (e _ _) (lev _), mul_zero, sum_const_zero, add_zero, zero_add,
    mul_ite]
  simp only [dotProduct, mulVec, mul_sum]
  congr 1
  · exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  · refine sum_congr rfl fun s _ => ?_
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single s (fun y _ hy => sum_eq_zero fun j _ => by simp [Ne.symm hy])
      (fun h => absurd (mem_univ s) h)]
    exact sum_congr rfl fun j _ => by simp only [↓reduceIte]; ring

omit [IsProbabilityMeasure P] [DecidableEq S] in
lemma memLp_cellLin (lev : J → Ω → ℝ) (e : J → S → Ω → ℝ) (hl : ∀ i, MemLp (lev i) 2 P)
    (he : ∀ i s, MemLp (e i s) 2 P) (g : S → J → ℝ) : MemLp (cellLin lev e g) 2 P :=
  memLp_finsetSum _ fun s _ => memLp_finsetSum _ fun i _ => ((hl i).add (he i s)).const_mul _

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [DecidableEq S] in
/-- `Σⱼ uⱼ (cell-linear rate j) = the cell-linear estimate with weights Σⱼ uⱼdⱼ`. -/
lemma sum_mul_cellLin (lev : J → Ω → ℝ) (e : J → S → Ω → ℝ) (u : J → ℝ)
    (d : J → S → J → ℝ) (ω : Ω) :
    ∑ j, u j * cellLin lev e (d j) ω = cellLin lev e (fun s i => ∑ j, u j * d j s i) ω := by
  simp only [cellLin, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- **The cost of balancing to a target built from the yearly cells** (any volumes). Rates
`rⱼ = Σₛᵢ dⱼₛᵢXᵢₛ` and target `T = Σₛᵢ gₛᵢXᵢₛ`, all with weights summing to one (e.g. `dⱼᵀμ̂` with
`μ̂ᵢ = Σₛ aᵢₛXᵢₛ`, and the cross-fitted level `gₛ = πₛc⁽ˢ⁾` with its weights held fixed). Shifting to
`T` changes the exposure-weighted mean squared error by exactly `m(g) − m(Σⱼ uⱼdⱼ)`, with
`m(g) = (G − u)ᵀL(G − u) + Σₛ gₛᵀDₛgₛ` (`integral_sq_cellLin_sub`), for every distribution with
these moments. No volume shape is needed: the target need not be a function of the `μ̂ᵢ`. -/
theorem balance_cost_cellLin (lev : J → Ω → ℝ) (e : J → S → Ω → ℝ) (μ : ℝ)
    (L : Matrix J J ℝ) (D : S → Matrix J J ℝ)
    (hl : ∀ i, MemLp (lev i) 2 P) (he : ∀ i s, MemLp (e i s) 2 P)
    (hlm : ∀ i, P[lev i] = μ) (hem : ∀ i s, P[e i s] = 0)
    (hL : ∀ i j, cov[lev i, lev j; P] = L i j) (hLe : ∀ i j s, cov[lev i, e j s; P] = 0)
    (hD : ∀ i j s s', cov[e i s, e j s'; P] = if s = s' then D s i j else 0)
    (u : J → ℝ) (hu : ∑ i, u i = 1) (d : J → S → J → ℝ) (hd : ∀ j, ∑ s, ∑ i, d j s i = 1)
    (g : S → J → ℝ) (hg : ∑ s, ∑ i, g s i = 1) :
    P[fun ω => ∑ j, u j * (cellLin lev e (d j) ω
        + (cellLin lev e g ω - ∑ i, u i * cellLin lev e (d i) ω) - lev j ω) ^ 2]
      = P[fun ω => ∑ j, u j * (cellLin lev e (d j) ω - lev j ω) ^ 2]
        + ((fun i => ∑ s, g s i - u i) ⬝ᵥ (L *ᵥ fun i => ∑ s, g s i - u i)
          + ∑ s, g s ⬝ᵥ (D s *ᵥ g s))
        - ((fun i => ∑ s, (∑ j, u j * d j s i) - u i)
            ⬝ᵥ (L *ᵥ fun i => ∑ s, (∑ j, u j * d j s i) - u i)
          + ∑ s, (fun i => ∑ j, u j * d j s i) ⬝ᵥ (D s *ᵥ fun i => ∑ j, u j * d j s i)) := by
  have hc : ∑ s, ∑ i, ∑ j, u j * d j s i = 1 := by
    have h1 : ∀ s, ∑ i, ∑ j, u j * d j s i = ∑ j, u j * ∑ i, d j s i := fun s => by
      rw [sum_comm]; exact sum_congr rfl fun j _ => (mul_sum _ _ _).symm
    rw [sum_congr rfl fun s _ => h1 s, sum_comm]
    rw [sum_congr rfl fun j _ => (mul_sum _ _ _).symm]
    simp [hd, hu]
  rw [integral_sum_sq_shift u hu _ lev _ (fun j => memLp_cellLin lev e hl he (d j)) hl
    (memLp_cellLin lev e hl he g)]
  simp_rw [sum_mul_cellLin lev e u d]
  rw [integral_sq_cellLin_sub lev e μ L D hl he hlm hem hL hLe hD g u hg hu,
    integral_sq_cellLin_sub lev e μ L D hl he hlm hem hL hLe hD _ u hc hu]

end YearlyCells

end Credibility
