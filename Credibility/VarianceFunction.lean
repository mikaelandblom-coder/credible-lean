import Credibility.Cumulants

/-!
# Under a variance function: noise cumulants that depend on the random level

Distribution layer (owner's option (b), `notes/fourth-moments.md`). Under a variance function the
noise of a cell has cumulants that depend on the cell's own mean, which is random. So the noise is
uncorrelated with the level but not independent of it, and `Cumulants.variance_quad_of_sources`
does not apply as it stands. Here the levels are a random point `a ~ μ` (random effects, shocks,
factor: anything), and given the levels the noise has the law `κ a`: independent centred sources
whose variances and third and fourth cumulants are functions of `a`. The joint law is `μ ⊗ₘ κ`.

* `variance_compProd`: the law of total variance for `μ ⊗ₘ κ`;
* `variance_quad_of_conditional_sources`: the unconditional variance of a quadratic estimator is
  the mean over the levels of its conditional variance (`variance_quad_of_sources` at each level)
  plus the variance over the levels of its conditional mean (law of total cumulance);
* `variance_quad_of_powerVariance`: the variance function `V(μ) = μᵖ` with dispersion `φ/w`
  (Tweedie): noise cumulants `φ/w·μᵖ`, `(φ/w)² p μ^(2p−1)`, `(φ/w)³ p(2p−1) μ^(3p−2)`, from
  `κₙ₊₁ = (φ/w) V dκₙ/dμ`. Only `p` is new; `p = 0` is the normal case.

Nothing in the core depends on this file.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Credibility.VarianceFunction

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  [IsProbabilityMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ]

/-- **Law of total variance** for levels `a ~ μ` and, given them, `b ~ κ a`:
`Var f = E[Var(f | a)] + Var(E[f | a])`. -/
theorem variance_compProd {f : α × β → ℝ} (hf : MemLp f 2 (μ ⊗ₘ κ))
    (hsec : ∀ a, MemLp (fun b => f (a, b)) 2 (κ a)) :
    variance f (μ ⊗ₘ κ) = ∫ a, variance (fun b => f (a, b)) (κ a) ∂μ
      + variance (fun a => ∫ b, f (a, b) ∂κ a) μ := by
  set g : α → ℝ := fun a => ∫ b, f (a, b) ∂κ a with hg
  have hf2 : Integrable (fun x => f x ^ 2) (μ ⊗ₘ κ) := hf.integrable_sq
  have hf1 : Integrable f (μ ⊗ₘ κ) := hf.integrable one_le_two
  have hI2 : Integrable (fun a => ∫ b, f (a, b) ^ 2 ∂κ a) μ := hf2.integral_compProd
  have hgm : AEStronglyMeasurable g μ := hf1.1.integral_kernel_compProd
  have hle : ∀ a, g a ^ 2 ≤ ∫ b, f (a, b) ^ 2 ∂κ a := fun a => by
    have := variance_nonneg (fun b => f (a, b)) (κ a)
    rw [variance_eq_sub (hsec a)] at this
    simp only [Pi.pow_apply] at this
    linarith
  have hg2 : Integrable (fun a => g a ^ 2) μ :=
    hI2.mono' (hgm.pow 2) (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle a)
  have hgL : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).2 hg2
  have hvar : ∀ a, variance (fun b => f (a, b)) (κ a) = ∫ b, f (a, b) ^ 2 ∂κ a - g a ^ 2 :=
    fun a => by rw [variance_eq_sub (hsec a)]; rfl
  simp_rw [hvar]
  rw [variance_eq_sub hf, variance_eq_sub hgL, integral_sub hI2 hg2]
  simp only [Pi.pow_apply]
  rw [Measure.integral_compProd hf2, Measure.integral_compProd hf1]
  ring

/-- Hölder for two `L⁴` factors: `1/4 + 1/4 = 1/2`. -/
lemma holder442 : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

variable {ι : Type*} [Fintype ι] {S : Type*} [Fintype S] [DecidableEq S]

omit [IsProbabilityMeasure μ] [IsMarkovKernel κ] [DecidableEq S] in
/-- A quadratic form in `L⁴` cells is in `L²`. -/
lemma memLp_quad {ν : Measure β} (ξ : S → β → ℝ) (hL : ∀ s, MemLp (ξ s) 4 ν)
    (B : Matrix ι S ℝ) (m : ι → ℝ) (A : Matrix ι ι ℝ) [IsFiniteMeasure ν] :
    MemLp (fun b => ∑ i, ∑ j, A i j * (m i + ∑ s, B i s * ξ s b)
      * (m j + ∑ s, B j s * ξ s b)) 2 ν := by
  have hZ : ∀ i, MemLp (fun b => m i + ∑ s, B i s * ξ s b) 4 ν := fun i =>
    (memLp_const _).add (memLp_finsetSum _ fun s _ => (hL s).const_mul _)
  have := holder442
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
  exact ((hZ i).const_mul (A i j)).mul (hZ j) (p := 4) (q := 4) (r := 2)

/-- **Variance of a quadratic estimator when the noise cumulants depend on the levels.** Levels
`a ~ μ` give the cell means `m a`; given them, the cells are `m a + Bξ` for sources `ξₛ` that are
independent and centred under `κ a`, with variances `v a s`, third moments `c₃ a s` and fourth
cumulants `c₄ a s`. With `C a = B diag(v a) Bᵀ`, `M = BᵀAB`:
`Var(Σ Aᵢⱼ ZᵢZⱼ) = E_a[2 tr(A C A C) + 4 (Am)ᵀC(Am) + 4 Σₛ c₃ₛ Mₛₛ (BᵀAm)ₛ + Σₛ c₄ₛ Mₛₛ²]`
`+ Var_a(Σ Aᵢⱼ (mᵢmⱼ + Cᵢⱼ))`: the mean of the conditional variance plus the variance of the
conditional mean. No distribution is assumed for the levels. -/
theorem variance_quad_of_conditional_sources (ξ : S → β → ℝ)
    (hind : ∀ a, iIndepFun ξ (κ a)) (hmeas : ∀ s, Measurable (ξ s))
    (hL : ∀ a s, MemLp (ξ s) 4 (κ a)) (h0 : ∀ a s, ∫ b, ξ s b ∂κ a = 0)
    (v c₃ c₄ : α → S → ℝ) (hv : ∀ a s, ∫ b, ξ s b * ξ s b ∂κ a = v a s)
    (h3 : ∀ a s, ∫ b, ξ s b * ξ s b * ξ s b ∂κ a = c₃ a s)
    (h4 : ∀ a s, ∫ b, ξ s b * ξ s b * ξ s b * ξ s b ∂κ a = c₄ a s + 3 * v a s ^ 2)
    (B : Matrix ι S ℝ) (m : α → ι → ℝ) (A : Matrix ι ι ℝ) (hA : ∀ i j, A j i = A i j)
    (hQ : MemLp (fun p : α × β => ∑ i, ∑ j, A i j * (m p.1 i + ∑ s, B i s * ξ s p.2)
      * (m p.1 j + ∑ s, B j s * ξ s p.2)) 2 (μ ⊗ₘ κ)) :
    variance (fun p : α × β => ∑ i, ∑ j, A i j * (m p.1 i + ∑ s, B i s * ξ s p.2)
      * (m p.1 j + ∑ s, B j s * ξ s p.2)) (μ ⊗ₘ κ)
      = ∫ a, (2 * trace (A * (B * diagonal (v a) * Bᵀ) * A * (B * diagonal (v a) * Bᵀ))
          + 4 * (A *ᵥ m a) ⬝ᵥ ((B * diagonal (v a) * Bᵀ) *ᵥ (A *ᵥ m a))
          + 4 * ∑ s, c₃ a s * (Bᵀ * A * B) s s * (Bᵀ *ᵥ (A *ᵥ m a)) s
          + ∑ s, c₄ a s * (Bᵀ * A * B) s s ^ 2) ∂μ
        + variance (fun a => ∑ i, ∑ j, A i j * (m a i * m a j + (B * diagonal (v a) * Bᵀ) i j))
          μ := by
  rw [variance_compProd hQ fun a => memLp_quad ξ (hL a) B (m a) A]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact Cumulants.variance_quad_of_sources ξ (hind a) hmeas (hL a) (h0 a) (v a) (c₃ a) (c₄ a)
      (hv a) (h3 a) (h4 a) B (m a) A hA
  · congr 1
    funext a
    exact Cumulants.integral_quad_of_sources ξ (hind a) hmeas (hL a) (h0 a) (v a) (hv a) B (m a) A

section PowerVariance

/-- The noise variance `φ/w · μᵖ` of a cell with weight `w` and mean `μ` (variance function `μᵖ`). -/
noncomputable def tweedieVar (φ w p μ : ℝ) : ℝ := φ / w * μ ^ p

/-- The third cumulant `(φ/w)² p μ^(2p−1)` of the noise under the variance function `μᵖ`. -/
noncomputable def tweedieκ₃ (φ w p μ : ℝ) : ℝ := (φ / w) ^ 2 * p * μ ^ (2 * p - 1)

/-- The fourth cumulant `(φ/w)³ p(2p−1) μ^(3p−2)` of the noise under the variance function `μᵖ`. -/
noncomputable def tweedieκ₄ (φ w p μ : ℝ) : ℝ := (φ / w) ^ 3 * p * (2 * p - 1) * μ ^ (3 * p - 2)

variable [DecidableEq ι]

omit [Fintype ι] in
/-- The trace term for a diagonal covariance and a symmetric `A`:
`tr(A D A D) = Σ Aᵢⱼ² dᵢdⱼ`. -/
lemma trace_mul_diagonal_mul_diagonal [Fintype ι] (A : Matrix ι ι ℝ) (hA : ∀ i j, A j i = A i j)
    (d : ι → ℝ) :
    trace (A * diagonal d * A * diagonal d) = ∑ i, ∑ j, A i j ^ 2 * d i * d j := by
  simp only [Matrix.trace, Matrix.diag]
  refine sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_apply, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, hA i j]; ring

/-- **Variance of a quadratic estimator under the variance function `μᵖ`** (Tweedie, dispersion
`φ/wᵢ`). Levels `a ~ μ` give the cell means `m a`; given them, the cell noises `εᵢ` are independent
and centred with the cumulants of the variance function `μᵖ` at `m a i`: variance `Vᵢ = φ/wᵢ·mᵢᵖ`,
third cumulant `(φ/wᵢ)² p mᵢ^(2p−1)`, fourth `(φ/wᵢ)³ p(2p−1) mᵢ^(3p−2)`. Then for a symmetric `A`
`Var(Σ Aᵢⱼ ZᵢZⱼ) = E_a[2 Σ Aᵢⱼ² VᵢVⱼ + 4 Σ Vᵢ (Am)ᵢ² + 4 Σ κ₃ᵢ Aᵢᵢ (Am)ᵢ + Σ κ₄ᵢ Aᵢᵢ²]`
`+ Var_a(mᵀAm + Σ Aᵢᵢ Vᵢ)`. The level-dependent cumulants are averaged over the levels exactly,
not evaluated at the mean level. -/
theorem variance_quad_of_powerVariance (ε : ι → β → ℝ)
    (hind : ∀ a, iIndepFun ε (κ a)) (hmeas : ∀ i, Measurable (ε i))
    (hL : ∀ a i, MemLp (ε i) 4 (κ a)) (h0 : ∀ a i, ∫ b, ε i b ∂κ a = 0)
    (φ p : ℝ) (w : ι → ℝ) (m : α → ι → ℝ)
    (hv : ∀ a i, ∫ b, ε i b * ε i b ∂κ a = tweedieVar φ (w i) p (m a i))
    (h3 : ∀ a i, ∫ b, ε i b * ε i b * ε i b ∂κ a = tweedieκ₃ φ (w i) p (m a i))
    (h4 : ∀ a i, ∫ b, ε i b * ε i b * ε i b * ε i b ∂κ a
      = tweedieκ₄ φ (w i) p (m a i) + 3 * tweedieVar φ (w i) p (m a i) ^ 2)
    (A : Matrix ι ι ℝ) (hA : ∀ i j, A j i = A i j)
    (hQ : MemLp (fun x : α × β => ∑ i, ∑ j, A i j * (m x.1 i + ε i x.2)
      * (m x.1 j + ε j x.2)) 2 (μ ⊗ₘ κ)) :
    variance (fun x : α × β => ∑ i, ∑ j, A i j * (m x.1 i + ε i x.2) * (m x.1 j + ε j x.2))
      (μ ⊗ₘ κ)
      = ∫ a, (2 * ∑ i, ∑ j, A i j ^ 2 * tweedieVar φ (w i) p (m a i)
              * tweedieVar φ (w j) p (m a j)
          + 4 * ∑ i, tweedieVar φ (w i) p (m a i) * (A *ᵥ m a) i ^ 2
          + 4 * ∑ i, tweedieκ₃ φ (w i) p (m a i) * A i i * (A *ᵥ m a) i
          + ∑ i, tweedieκ₄ φ (w i) p (m a i) * A i i ^ 2) ∂μ
        + variance (fun a => ∑ i, ∑ j, A i j * m a i * m a j
          + ∑ i, A i i * tweedieVar φ (w i) p (m a i)) μ := by
  have hcell : ∀ i b, ∑ s, (1 : Matrix ι ι ℝ) i s * ε s b = ε i b := fun i b => by
    simp [Matrix.one_apply]
  have key := variance_quad_of_conditional_sources (μ := μ) ε hind hmeas hL h0
    (fun a i => tweedieVar φ (w i) p (m a i)) (fun a i => tweedieκ₃ φ (w i) p (m a i))
    (fun a i => tweedieκ₄ φ (w i) p (m a i)) hv h3 h4 1 m A hA (by simpa only [hcell] using hQ)
  simp only [hcell, transpose_one, Matrix.one_mul, Matrix.mul_one, one_mulVec] at key
  rw [key]
  simp_rw [trace_mul_diagonal_mul_diagonal A hA]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [dotProduct, mulVec_diagonal]
    congr 2
    exact congrArg _ (congrArg _ (sum_congr rfl fun i _ => by ring))
  · congr 1; funext a
    simp only [diagonal_apply, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq,
      mem_univ, ite_true]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

end PowerVariance

end Credibility.VarianceFunction
