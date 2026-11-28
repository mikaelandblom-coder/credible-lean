import Credibility.Cumulants

/-!
# The app's `Wⱼ`: the estimated variance of `σ̂ⱼ²` (G1a, distribution-free)

The corrBS fit (`Engine.vcEstimate`, formula `F.vcW`) credibility-weights the region variances
`σ̂ⱼ²` with `ζⱼ = β²/(β² + Wⱼ)`, where `Wⱼ` estimates `Var σ̂ⱼ²` from the yearly terms. In one
region, with volumes `wₜ`, `aₜ = wₜ/Σw`, residuals `rₜ = Xₜ − Σ aₛXₛ` and `n` years:

* `uₜ = wₜ rₜ² n/(n − 1)`, whose average is `σ̂² = Σ wₜrₜ²/(n − 1)`;
* `W = Σₜ (uₜ − σ̂²)² / (n(n − 1))`.

Each `uₜ` and `σ̂²` is a quadratic form in the noise, so `E W` is of order four. For cells
`Xₜ = L + ξₜ` with any level `L` and independent centred yearly noise `ξₜ` (variances `vₜ`, fourth
cumulants `κₜ`), all exact:

* `integral_sq_quad_of_sources`: `E[(ξᵀGξ)²] = (Σ Gₛₛvₛ)² + 2 Σ Gₛᵣ²vₛvᵣ + Σ κₛGₛₛ²`;
* `integral_vcW`: `E W` in closed form for any volumes (`G = Aₜ − Ā`, `Aₜ` the form of `uₜ`);
* `integral_sigHat_sq`: `E σ̂⁴` the same way, so `Var σ̂² = E σ̂⁴ − (E σ̂²)²`;
* equal volumes and identically distributed years (`*_equal`): `E W = 2σ⁴(n − 2)/(n − 1)² +
  κ(n − 2)²/(n(n − 1)²)` while `Var σ̂² = 2σ⁴/(n − 1) + κ/n`: `W` is low by a relative `O(1/n)`
  (Finding 47), and `vcWCorr = (n − 1)³/(n(n − 2)(n − 3)) W − 2σ̂⁴/(n(n − 3))` is unbiased for
  `Var σ̂²` (`n ≥ 4`, `integral_vcWCorr_equal`).

Literature: the unbiased estimator of the variance of a sample variance is classical (Fisher's
k-statistics); `studies/literature.md` §10aa.
-/

open MeasureTheory ProbabilityTheory Finset Matrix Credibility.Cumulants

namespace Credibility.VcW

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The mean of a quadratic form in independent centred sources: `E[ξᵀGξ] = Σₛ Gₛₛvₛ`. -/
theorem integral_quadForm_of_sources (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s) (G : Matrix ι ι ℝ) :
    ∫ ω, ∑ i, ∑ j, G i j * ξ i ω * ξ j ω ∂P = ∑ s, G s s * v s := by
  have hform : (fun ω => ∑ i, ∑ j, G i j * ((0 : ι → ℝ) i + ∑ s, (1 : Matrix ι ι ℝ) i s * ξ s ω)
      * ((0 : ι → ℝ) j + ∑ s, (1 : Matrix ι ι ℝ) j s * ξ s ω))
      = fun ω => ∑ i, ∑ j, G i j * ξ i ω * ξ j ω := funext fun ω => by
    simp [Matrix.one_apply]
  have hmean := integral_quad_of_sources ξ hind hmeas hL h0 v hv 1 0 G
  rw [hform] at hmean
  rw [hmean]
  simp only [Matrix.one_mul, transpose_one, Matrix.mul_one, Pi.zero_apply, mul_zero, zero_add,
    diagonal_apply]
  simp

/-- **Second moment of a quadratic form in independent sources.** For independent centred
sources `ξₛ` in `L⁴` with variances `vₛ` and fourth cumulants `κₛ` (fourth moment `κₛ + 3vₛ²`)
and a symmetric `G`, `E[(ξᵀGξ)²] = (Σₛ Gₛₛvₛ)² + 2 Σₛᵣ Gₛᵣ² vₛvᵣ + Σₛ κₛ Gₛₛ²`. No third
moment enters. -/
theorem integral_sq_quad_of_sources (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v κ : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ s + 3 * v s ^ 2)
    (G : Matrix ι ι ℝ) (hG : ∀ i j, G j i = G i j) :
    ∫ ω, (∑ i, ∑ j, G i j * ξ i ω * ξ j ω) ^ 2 ∂P
      = (∑ s, G s s * v s) ^ 2 + 2 * ∑ s, ∑ r, G s r ^ 2 * v s * v r
        + ∑ s, κ s * G s s ^ 2 := by
  have hform : (fun ω => ∑ i, ∑ j, G i j * ((0 : ι → ℝ) i + ∑ s, (1 : Matrix ι ι ℝ) i s * ξ s ω)
      * ((0 : ι → ℝ) j + ∑ s, (1 : Matrix ι ι ℝ) j s * ξ s ω))
      = fun ω => ∑ i, ∑ j, G i j * ξ i ω * ξ j ω := funext fun ω => by
    simp [Matrix.one_apply]
  have hvar := variance_quad_of_sources ξ hind hmeas hL h0 v (fun s => ∫ ω, ξ s ω * ξ s ω * ξ s ω ∂P)
    κ hv (fun _ => rfl) h4 1 0 G hG
  rw [hform] at hvar
  have hmem : MemLp (fun ω => ∑ i, ∑ j, G i j * ξ i ω * ξ j ω) 2 P := memLp_quadForm hL G
  rw [variance_eq_sub hmem] at hvar
  have hsq : P[(fun ω => ∑ i, ∑ j, G i j * ξ i ω * ξ j ω) ^ 2]
      = ∫ ω, (∑ i, ∑ j, G i j * ξ i ω * ξ j ω) ^ 2 ∂P := rfl
  rw [hsq] at hvar
  have hm : ∫ ω, ∑ i, ∑ j, G i j * ξ i ω * ξ j ω ∂P = ∑ s, G s s * v s :=
    integral_quadForm_of_sources ξ hind hmeas hL h0 v hv G
  rw [hm] at hvar
  have htr : trace (G * (1 * diagonal v * 1ᵀ) * G * (1 * diagonal v * 1ᵀ))
      = ∑ s, ∑ r, G s r ^ 2 * v s * v r := by
    simp only [Matrix.one_mul, transpose_one, Matrix.mul_one]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, sum_mul]
    refine sum_congr rfl fun s _ => sum_congr rfl fun r _ => ?_
    simp only [diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq', mem_univ,
      ite_true]
    rw [hG r s]; ring
  rw [htr] at hvar
  simp only [mulVec_zero, zero_dotProduct, mul_zero, Pi.zero_apply, add_zero,
    Matrix.one_mul, transpose_one, Matrix.mul_one, sum_const_zero] at hvar
  linarith

/-- **Variance of a quadratic form in independent sources**:
`Var(ξᵀGξ) = 2 Σₛᵣ Gₛᵣ² vₛvᵣ + Σₛ κₛ Gₛₛ²` (`G` symmetric). -/
theorem variance_quadForm_of_sources (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v κ : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ s + 3 * v s ^ 2)
    (G : Matrix ι ι ℝ) (hG : ∀ i j, G j i = G i j) :
    variance (fun ω => ∑ i, ∑ j, G i j * ξ i ω * ξ j ω) P
      = 2 * ∑ s, ∑ r, G s r ^ 2 * v s * v r + ∑ s, κ s * G s s ^ 2 := by
  rw [variance_eq_sub (memLp_quadForm hL G)]
  change ∫ ω, (∑ i, ∑ j, G i j * ξ i ω * ξ j ω) ^ 2 ∂P - _ = _
  rw [integral_sq_quad_of_sources ξ hind hmeas hL h0 v κ hv h4 G hG,
    integral_quadForm_of_sources ξ hind hmeas hL h0 v hv G]
  ring

/-- `Dₜₛ = δₜₛ − aₛ`, `aₛ = wₛ/Σw`: the residual `rₜ = Σₛ Dₜₛ Xₛ`. -/
noncomputable def resCoef (w : ι → ℝ) (t s : ι) : ℝ := (if t = s then 1 else 0) - w s / ∑ r, w r

/-- The residual `rₜ = Xₜ − Σₛ aₛXₛ`, `aₛ = wₛ/Σw`. -/
noncomputable def resid (w X : ι → ℝ) (t : ι) : ℝ := X t - ∑ s, w s / (∑ r, w r) * X s

/-- `σ̂² = Σₜ wₜrₜ²/(n − 1)` (`n` years; thesis eq. (41) for one region). -/
noncomputable def sigHat (w X : ι → ℝ) : ℝ :=
  (∑ t, w t * resid w X t ^ 2) / ((Fintype.card ι : ℝ) - 1)

/-- The yearly term `uₜ = wₜrₜ² n/(n − 1)` (average `σ̂²`). -/
noncomputable def uTerm (w X : ι → ℝ) (t : ι) : ℝ :=
  w t * resid w X t ^ 2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)

/-- The app's `Wⱼ = Σₜ (uₜ − σ̂²)²/(n(n − 1))` (`F.vcW`). -/
noncomputable def vcW (w X : ι → ℝ) : ℝ :=
  (∑ t, (uTerm w X t - sigHat w X) ^ 2)
    / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))

/-- The form of `uₜ` in the noise: `(Aₜ)ᵢⱼ = wₜDₜᵢDₜⱼ n/(n − 1)`. -/
noncomputable def uForm (w : ι → ℝ) (t i j : ι) : ℝ :=
  w t * resCoef w t i * resCoef w t j * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)

/-- The form of `σ̂²`: `Āᵢⱼ = Σₜ wₜDₜᵢDₜⱼ/(n − 1)`. -/
noncomputable def sigForm (w : ι → ℝ) (i j : ι) : ℝ :=
  (∑ t, w t * resCoef w t i * resCoef w t j) / ((Fintype.card ι : ℝ) - 1)

/-- The form of `uₜ − σ̂²`: `Aₜ − Ā`. -/
noncomputable def devForm (w : ι → ℝ) (t i j : ι) : ℝ := uForm w t i j - sigForm w i j

/-- Residuals do not see the level, and are linear in the noise: `rₜ = Σₛ Dₜₛξₛ`. -/
lemma resid_level (w ξ : ι → ℝ) (Lv : ℝ) (hw : ∑ r, w r ≠ 0) (t : ι) :
    resid w (fun s => Lv + ξ s) t = ∑ s, resCoef w t s * ξ s := by
  have ha : ∑ s, w s / ∑ r, w r = 1 := by rw [← sum_div, div_self hw]
  simp only [resid, resCoef, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq,
    mem_univ, ite_true, mul_add, sum_add_distrib, ← sum_mul, ha]
  ring

omit [DecidableEq ι] in
lemma sq_lin (d ξ : ι → ℝ) : (∑ s, d s * ξ s) ^ 2 = ∑ i, ∑ j, d i * d j * (ξ i * ξ j) := by
  rw [sq, sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma uTerm_eq (w ξ : ι → ℝ) (Lv : ℝ) (hw : ∑ r, w r ≠ 0) (t : ι) :
    uTerm w (fun s => Lv + ξ s) t = ∑ i, ∑ j, uForm w t i j * ξ i * ξ j := by
  simp only [uTerm, resid_level w ξ Lv hw, sq_lin, uForm, mul_sum, sum_mul, sum_div]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma sigHat_eq (w ξ : ι → ℝ) (Lv : ℝ) (hw : ∑ r, w r ≠ 0) :
    sigHat w (fun s => Lv + ξ s) = ∑ i, ∑ j, sigForm w i j * ξ i * ξ j := by
  simp only [sigHat, resid_level w ξ Lv hw, sq_lin, sigForm, mul_sum, sum_mul, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring

lemma dev_eq (w ξ : ι → ℝ) (Lv : ℝ) (hw : ∑ r, w r ≠ 0) (t : ι) :
    uTerm w (fun s => Lv + ξ s) t - sigHat w (fun s => Lv + ξ s)
      = ∑ i, ∑ j, devForm w t i j * ξ i * ξ j := by
  rw [uTerm_eq w ξ Lv hw, sigHat_eq w ξ Lv hw, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by simp only [devForm]; ring

lemma devForm_symm (w : ι → ℝ) (t i j : ι) : devForm w t j i = devForm w t i j := by
  simp only [devForm, uForm, sigForm]
  congr 1
  · ring
  · congr 1; exact sum_congr rfl fun s _ => by ring

lemma sigForm_symm (w : ι → ℝ) (i j : ι) : sigForm w j i = sigForm w i j := by
  simp only [sigForm]; congr 1; exact sum_congr rfl fun s _ => by ring

/-- The second-moment value of a form `G` under variances `v` and fourth cumulants `κ`:
`(Σ Gₛₛvₛ)² + 2 Σ Gₛᵣ²vₛvᵣ + Σ κₛGₛₛ²`. -/
noncomputable def secondMoment (G : ι → ι → ℝ) (v κ : ι → ℝ) : ℝ :=
  (∑ s, G s s * v s) ^ 2 + 2 * ∑ s, ∑ r, G s r ^ 2 * v s * v r + ∑ s, κ s * G s s ^ 2

/-- **`E Wⱼ` exactly** (G1a). In one region, cells `Xₜ = L + ξₜ` with any level `L` (random or
not) and independent centred yearly noise `ξₜ` in `L⁴` with variances `vₜ` and fourth cumulants
`κₜ`; volumes with `Σw ≠ 0`. Then `E W = Σₜ m₂(Aₜ − Ā) / (n(n − 1))`, `m₂` the second moment of
a quadratic form (`secondMoment`), `Aₜ` and `Ā` the forms of `uₜ` and `σ̂²`. -/
theorem integral_vcW (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v κ : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ s + 3 * v s ^ 2)
    (L : Ω → ℝ) (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) :
    ∫ ω, vcW w (fun s => L ω + ξ s ω) ∂P
      = (∑ t, secondMoment (devForm w t) v κ)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
  have hpt : ∀ ω, vcW w (fun s => L ω + ξ s ω)
      = (∑ t, (∑ i, ∑ j, devForm w t i j * ξ i ω * ξ j ω) ^ 2)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := fun ω => by
    simp only [vcW, dev_eq w (fun s => ξ s ω) (L ω) hw]
  simp only [hpt]
  rw [integral_div, integral_finsetSum _ fun t _ =>
    (memLp_quadForm hL (devForm w t : Matrix ι ι ℝ)).integrable_sq]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  exact integral_sq_quad_of_sources ξ hind hmeas hL h0 v κ hv h4 (devForm w t)
    (fun i j => devForm_symm w t i j)

/-- **`E σ̂⁴` exactly**, in the setting of `integral_vcW`: `m₂(Ā)`. With `E σ̂² = Σ Āₛₛvₛ`, this
gives `Var σ̂² = 2 Σ Āₛᵣ²vₛvᵣ + Σ κₛĀₛₛ²`, the target of `W`. -/
theorem integral_sigHat_sq (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v κ : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ s + 3 * v s ^ 2)
    (L : Ω → ℝ) (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) :
    ∫ ω, sigHat w (fun s => L ω + ξ s ω) ^ 2 ∂P = secondMoment (sigForm w) v κ := by
  simp only [sigHat_eq w _ _ hw]
  exact integral_sq_quad_of_sources ξ hind hmeas hL h0 v κ hv h4 (sigForm w)
    (fun i j => sigForm_symm w i j)

/-- `E σ̂² = Σₛ Āₛₛvₛ`, in the setting of `integral_vcW`. -/
theorem integral_sigHat (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (L : Ω → ℝ) (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) :
    ∫ ω, sigHat w (fun s => L ω + ξ s ω) ∂P = ∑ s, sigForm w s s * v s := by
  simp only [sigHat_eq w _ _ hw]
  exact integral_quadForm_of_sources ξ hind hmeas hL h0 v hv (sigForm w)

/-- **`Var σ̂²` exactly**, the target of `W`: `2 Σ Āₛᵣ²vₛvᵣ + Σ κₛĀₛₛ²`. -/
theorem variance_sigHat (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v κ : ι → ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = v s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ s + 3 * v s ^ 2)
    (L : Ω → ℝ) (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) :
    variance (fun ω => sigHat w (fun s => L ω + ξ s ω)) P
      = 2 * ∑ s, ∑ r, sigForm w s r ^ 2 * v s * v r + ∑ s, κ s * sigForm w s s ^ 2 := by
  simp only [sigHat_eq w _ _ hw]
  exact variance_quadForm_of_sources ξ hind hmeas hL h0 v κ hv h4 (sigForm w)
    (fun i j => sigForm_symm w i j)

omit [IsProbabilityMeasure P] in
lemma integrable_vcW (ξ : ι → Ω → ℝ) (hL : ∀ s, MemLp (ξ s) 4 P) (L : Ω → ℝ) (w : ι → ℝ)
    (hw : ∑ r, w r ≠ 0) : Integrable (fun ω => vcW w (fun s => L ω + ξ s ω)) P := by
  have hpt : (fun ω => vcW w (fun s => L ω + ξ s ω)) = fun ω =>
      (∑ t, (∑ i, ∑ j, devForm w t i j * ξ i ω * ξ j ω) ^ 2)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := funext fun ω => by
    simp only [vcW, dev_eq w (fun s => ξ s ω) (L ω) hw]
  rw [hpt]
  exact (integrable_finsetSum _ fun t _ =>
    (memLp_quadForm hL (devForm w t : Matrix ι ι ℝ)).integrable_sq).div_const _

omit [IsProbabilityMeasure P] in
lemma integrable_sigHat_sq (ξ : ι → Ω → ℝ) (hL : ∀ s, MemLp (ξ s) 4 P) (L : Ω → ℝ)
    (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) :
    Integrable (fun ω => sigHat w (fun s => L ω + ξ s ω) ^ 2) P := by
  simp only [sigHat_eq w _ _ hw]
  exact (memLp_quadForm hL (sigForm w : Matrix ι ι ℝ)).integrable_sq

/-- The corrected `W` (Finding 47): `W̃ = (n − 1)³/(n(n − 2)(n − 3)) W − 2σ̂⁴/(n(n − 3))`,
unbiased for `Var σ̂²` with equal volumes and `n ≥ 4` (`integral_vcWCorr_equal`). -/
noncomputable def vcWCorr (w X : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) - 1) ^ 3 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 2)
      * ((Fintype.card ι : ℝ) - 3)) * vcW w X
    - 2 * sigHat w X ^ 2 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 3))

omit [DecidableEq ι] in
/-- `m₂` is a quadratic form in the variances plus a linear one in the cumulants: with
`v = σ²v₁` and `κ = kκ₁`, `m₂(G, v, κ) = σ⁴ m₂(G, v₁, 0) + k m₂(G, 0, κ₁)`. -/
lemma secondMoment_scale (G : ι → ι → ℝ) (v₁ κ₁ : ι → ℝ) (σ2 k : ℝ) :
    secondMoment G (fun s => σ2 * v₁ s) (fun s => k * κ₁ s)
      = σ2 ^ 2 * secondMoment G v₁ 0 + k * secondMoment G 0 κ₁ := by
  simp only [secondMoment, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, add_zero,
    zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have e1 : ∑ s, G s s * (σ2 * v₁ s) = σ2 * ∑ s, G s s * v₁ s := by
    rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  have e2 : ∑ s, ∑ r, G s r ^ 2 * (σ2 * v₁ s) * (σ2 * v₁ r)
      = σ2 ^ 2 * ∑ s, ∑ r, G s r ^ 2 * v₁ s * v₁ r := by
    rw [mul_sum]; refine sum_congr rfl fun s _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun r _ => by ring
  have e3 : ∑ s, k * κ₁ s * G s s ^ 2 = k * ∑ s, κ₁ s * G s s ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  rw [e1, e2, e3]
  ring

/-- **A corrected `W` for any volumes** (Finding 47). Suppose the yearly variances and fourth
cumulants are known up to two scales, `vₜ = σ²v₁ₜ` and `κₜ = kκ₁ₜ` (e.g. noise of a fixed shape
scaled by volume: `v₁ₜ = 1/wₜ`, `κ₁ₜ = 1/wₜ²`). If `λ`, `μ` solve the two linear equations that
match the `σ⁴` and the `k` parts of `E[λW + μσ̂⁴]` and `Var σ̂²` (coefficients from
`integral_vcW`, `integral_sigHat_sq`, `integral_sigHat`, all computable from the volumes), then
`E[λW + μσ̂⁴] = Var σ̂²` for every `σ²` and `k`. -/
theorem integral_vcWCorr (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (v₁ κ₁ : ι → ℝ) (σ2 k : ℝ) (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = σ2 * v₁ s)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = k * κ₁ s + 3 * (σ2 * v₁ s) ^ 2)
    (L : Ω → ℝ) (w : ι → ℝ) (hw : ∑ r, w r ≠ 0) (lam mu : ℝ)
    (hσ : lam * (∑ t, secondMoment (devForm w t) v₁ 0)
          / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))
        + mu * secondMoment (sigForm w) v₁ 0
        = secondMoment (sigForm w) v₁ 0 - (∑ s, sigForm w s s * v₁ s) ^ 2)
    (hk : lam * (∑ t, secondMoment (devForm w t) 0 κ₁)
          / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))
        + mu * secondMoment (sigForm w) 0 κ₁ = secondMoment (sigForm w) 0 κ₁) :
    ∫ ω, lam * vcW w (fun s => L ω + ξ s ω) + mu * sigHat w (fun s => L ω + ξ s ω) ^ 2 ∂P
      = variance (fun ω => sigHat w (fun s => L ω + ξ s ω)) P := by
  have hv' : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = (fun s => σ2 * v₁ s) s := hv
  have h4' : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P
      = (fun s => k * κ₁ s) s + 3 * (fun s => σ2 * v₁ s) s ^ 2 := h4
  rw [integral_add ((integrable_vcW ξ hL L w hw).const_mul _)
      ((integrable_sigHat_sq ξ hL L w hw).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_vcW ξ hind hmeas hL h0 _ _ hv' h4' L w hw,
    integral_sigHat_sq ξ hind hmeas hL h0 _ _ hv' h4' L w hw,
    variance_sigHat ξ hind hmeas hL h0 _ _ hv' h4' L w hw]
  simp only [secondMoment_scale, sum_add_distrib, ← mul_sum]
  have hvar : 2 * ∑ s, ∑ r, sigForm w s r ^ 2 * (σ2 * v₁ s) * (σ2 * v₁ r)
        + ∑ s, k * κ₁ s * sigForm w s s ^ 2
      = σ2 ^ 2 * (secondMoment (sigForm w) v₁ 0 - (∑ s, sigForm w s s * v₁ s) ^ 2)
        + k * secondMoment (sigForm w) 0 κ₁ := by
    have := secondMoment_scale (sigForm w) v₁ κ₁ σ2 k
    simp only [secondMoment] at this ⊢
    have e1 : ∑ s, sigForm w s s * (σ2 * v₁ s) = σ2 * ∑ s, sigForm w s s * v₁ s := by
      rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
    rw [e1] at this
    linear_combination this
  rw [hvar]
  linear_combination σ2 ^ 2 * hσ + k * hk

section Equal

/-! ### Equal volumes: the closed form (Finding 47) -/

omit [DecidableEq ι] in
lemma card_ne (hn : 2 ≤ Fintype.card ι) : (Fintype.card ι : ℝ) ≠ 0 := by
  have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  intro h; rw [h] at this; norm_num at this

/-- With equal volumes the residual coefficients are the centering matrix `δₜₛ − 1/n`. -/
lemma resCoef_const (c : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι) (t s : ι) :
    resCoef (fun _ : ι => c) t s = (if t = s then 1 else 0) - 1 / (Fintype.card ι : ℝ) := by
  have hn' := card_ne hn
  simp only [resCoef, sum_const, card_univ, nsmul_eq_mul]
  congr 1
  field_simp

lemma cent_mul (n : ℝ) (hn : n = Fintype.card ι) (hn0 : n ≠ 0) (t r : ι) :
    ∑ s, ((if t = s then (1 : ℝ) else 0) - 1 / n) * ((if r = s then 1 else 0) - 1 / n)
      = (if t = r then 1 else 0) - 1 / n := by
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul, ← hn]
  field_simp
  ring

lemma cent_sq_diag (n : ℝ) (hn : n = Fintype.card ι) (hn0 : n ≠ 0) (t : ι) :
    ∑ s, ((if t = s then (1 : ℝ) else 0) - 1 / n) ^ 2 = 1 - 1 / n := by
  have := cent_mul n hn hn0 t t
  simp only [ite_true] at this
  rw [← this]
  exact sum_congr rfl fun s _ => sq _

/-- The `κ` sum of one year's form, `Σₛ (n Hₜₛ² − Hₛₛ)² = (n − 1)(n − 2)²/n`. -/
lemma cent_quartic (n : ℝ) (hn : n = Fintype.card ι) (hn0 : n ≠ 0) (t : ι) :
    ∑ s, (n * ((if t = s then (1 : ℝ) else 0) - 1 / n) ^ 2 - (1 - 1 / n)) ^ 2
      = (n - 1) * (n - 2) ^ 2 / n := by
  rw [← Finset.add_sum_erase _ _ (mem_univ t)]
  have hrest : ∀ s ∈ univ.erase t,
      (n * ((if t = s then (1 : ℝ) else 0) - 1 / n) ^ 2 - (1 - 1 / n)) ^ 2
        = (n * (1 / n) ^ 2 - (1 - 1 / n)) ^ 2 := fun s hs => by
    have h : ¬ t = s := Ne.symm (ne_of_mem_erase hs)
    simp only [h, ↓reduceIte]; ring
  rw [sum_congr rfl hrest, sum_const, card_erase_of_mem (mem_univ t), card_univ,
    nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨t⟩), ← hn]
  simp only [↓reduceIte]
  field_simp
  ring

/-- The Gaussian sum of one year's form,
`Σₛᵣ (n HₜₛHₜᵣ − Hₛᵣ)² = (n − 1)(n − 2)`. -/
lemma cent_gauss (n : ℝ) (hn : n = Fintype.card ι) (hn0 : n ≠ 0) (t : ι) :
    ∑ s, ∑ r, (n * (((if t = s then (1 : ℝ) else 0) - 1 / n)
        * ((if t = r then 1 else 0) - 1 / n)) - ((if s = r then 1 else 0) - 1 / n)) ^ 2
      = (n - 1) * (n - 2) := by
  set H : ι → ι → ℝ := fun a b => (if a = b then 1 else 0) - 1 / n with hH
  have hHs : ∀ a b, H b a = H a b := fun a b => by simp only [hH, eq_comm]
  have hm : ∀ a b, ∑ s, H a s * H b s = H a b := cent_mul n hn hn0
  have h5 : ∑ s, H t s ^ 2 = 1 - 1 / n := cent_sq_diag n hn hn0 t
  have hrow : ∀ s, ∑ r, (n * (H t s * H t r) - H s r) ^ 2
      = n ^ 2 * H t s ^ 2 * (1 - 1 / n) - 2 * n * H t s * H t s + (1 - 1 / n) := fun s => by
    have hexp : ∀ r, (n * (H t s * H t r) - H s r) ^ 2
        = n ^ 2 * H t s ^ 2 * H t r ^ 2 - 2 * n * H t s * (H t r * H s r) + H s r * H s r :=
      fun r => by ring
    rw [sum_congr rfl fun r _ => hexp r, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
      h5, hm s s]
    have h2 : ∑ r, H t r * H s r = H t s := hm t s
    rw [h2]
    simp [hH]
  change ∑ s, ∑ r, (n * (H t s * H t r) - H s r) ^ 2 = _
  rw [sum_congr rfl fun s _ => hrow s, sum_add_distrib, sum_sub_distrib]
  have e1 : ∑ s, n ^ 2 * H t s ^ 2 * (1 - 1 / n) = n ^ 2 * (1 - 1 / n) * (1 - 1 / n) := by
    rw [← sum_mul, ← mul_sum, h5]
  have e2 : ∑ s, 2 * n * H t s * H t s = 2 * n * (1 - 1 / n) := by
    rw [sum_congr rfl fun s _ => (by ring : 2 * n * H t s * H t s = 2 * n * H t s ^ 2), ← mul_sum,
      h5]
  rw [e1, e2, sum_const, card_univ, nsmul_eq_mul, ← hn]
  field_simp
  ring

lemma resCoef_symm_const (c : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι) (t s : ι) :
    resCoef (fun _ : ι => c) s t = resCoef (fun _ : ι => c) t s := by
  rw [resCoef_const c hc hn, resCoef_const c hc hn]; simp only [eq_comm]

lemma sigForm_const (c : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι) (i j : ι) :
    sigForm (fun _ : ι => c) i j
      = c / ((Fintype.card ι : ℝ) - 1) * ((if i = j then 1 else 0) - 1 / (Fintype.card ι : ℝ)) := by
  have hm := cent_mul (Fintype.card ι : ℝ) rfl (card_ne hn) i j
  simp only [sigForm]
  have : ∀ t, c * resCoef (fun _ : ι => c) t i * resCoef (fun _ : ι => c) t j
      = c * (resCoef (fun _ : ι => c) i t * resCoef (fun _ : ι => c) j t) := fun t => by
    rw [resCoef_symm_const c hc hn i t, resCoef_symm_const c hc hn j t]; ring
  rw [sum_congr rfl fun t _ => this t, ← mul_sum]
  simp only [resCoef_const c hc hn, hm]
  ring

lemma devForm_const (c : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι) (t i j : ι) :
    devForm (fun _ : ι => c) t i j
      = c / ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ)
        * (((if t = i then 1 else 0) - 1 / (Fintype.card ι : ℝ))
          * ((if t = j then 1 else 0) - 1 / (Fintype.card ι : ℝ)))
        - ((if i = j then 1 else 0) - 1 / (Fintype.card ι : ℝ))) := by
  simp only [devForm, sigForm_const c hc hn, uForm, resCoef_const c hc hn]
  ring

omit [DecidableEq ι] in
lemma card_sub_one_ne (hn : 2 ≤ Fintype.card ι) : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
  have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  linarith

/-- One year's second moment with equal volumes `c`, `vₛ = σ²/c`, `κₛ = κ/c²`:
`2σ⁴(n − 2)/(n − 1) + κ(n − 2)²/(n(n − 1))` (the mean part vanishes). -/
lemma secondMoment_dev_const (c σ2 κ : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι) (t : ι) :
    secondMoment (devForm (fun _ : ι => c) t) (fun _ => σ2 / c) (fun _ => κ / c ^ 2)
      = 2 * σ2 ^ 2 * ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1)
        + κ * ((Fintype.card ι : ℝ) - 2) ^ 2
          / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn0 : n ≠ 0 := card_ne hn
  have hn1 : n - 1 ≠ 0 := card_sub_one_ne hn
  set H : ι → ι → ℝ := fun a b => (if a = b then 1 else 0) - 1 / n with hH
  have hd : ∀ i j, devForm (fun _ : ι => c) t i j = c / (n - 1) * (n * (H t i * H t j) - H i j) :=
    devForm_const c hc hn t
  have hdiag : ∀ s, H s s = 1 - 1 / n := fun s => by simp [hH]
  have hg := cent_gauss n hn_def hn0 t
  have hq := cent_quartic n hn_def hn0 t
  have h5 := cent_sq_diag n hn_def hn0 t
  change ∑ s, ∑ r, (n * (H t s * H t r) - H s r) ^ 2 = _ at hg
  change ∑ s, (n * H t s ^ 2 - (1 - 1 / n)) ^ 2 = _ at hq
  change ∑ s, H t s ^ 2 = _ at h5
  simp only [secondMoment, hd, hdiag]
  have t1 : ∑ s, c / (n - 1) * (n * (H t s * H t s) - (1 - 1 / n)) * (σ2 / c) = 0 := by
    rw [← sum_mul, ← mul_sum, sum_sub_distrib, ← mul_sum,
      sum_congr rfl fun s _ => (by ring : H t s * H t s = H t s ^ 2), h5, sum_const, card_univ,
      nsmul_eq_mul, ← hn_def]
    field_simp; ring
  have t2 : ∑ s, ∑ r, (c / (n - 1) * (n * (H t s * H t r) - H s r)) ^ 2 * (σ2 / c) * (σ2 / c)
      = (c / (n - 1)) ^ 2 * (σ2 / c) ^ 2 * ((n - 1) * (n - 2)) := by
    rw [← hg, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have t3 : ∑ s, κ / c ^ 2 * (c / (n - 1) * (n * (H t s * H t s) - (1 - 1 / n))) ^ 2
      = κ / c ^ 2 * (c / (n - 1)) ^ 2 * ((n - 1) * (n - 2) ^ 2 / n) := by
    rw [← hq, mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [t1, t2, t3]
  field_simp
  ring

/-- **`E Wⱼ` with equal volumes** (Finding 47). Equal volumes `c ≠ 0`, `n ≥ 2` identically
distributed independent years with `Var ξₜ = σ²/c` and fourth cumulant `κ/c²` (so `σ²` and `κ`
are those of one unit of volume), any level `L`:
`E W = 2σ⁴(n − 2)/(n − 1)² + κ(n − 2)²/(n(n − 1)²)`. -/
theorem integral_vcW_equal (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (c σ2 κ : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι)
    (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = σ2 / c)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ / c ^ 2 + 3 * (σ2 / c) ^ 2)
    (L : Ω → ℝ) :
    ∫ ω, vcW (fun _ => c) (fun s => L ω + ξ s ω) ∂P
      = 2 * σ2 ^ 2 * ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) ^ 2
        + κ * ((Fintype.card ι : ℝ) - 2) ^ 2
          / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) ^ 2) := by
  have hsum : ∑ _r : ι, c ≠ 0 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_ne_zero (card_ne hn) hc
  rw [integral_vcW ξ hind hmeas hL h0 (fun _ => σ2 / c) (fun _ => κ / c ^ 2) hv h4 L _ hsum]
  simp only [secondMoment_dev_const c σ2 κ hc hn, sum_const, card_univ, nsmul_eq_mul]
  have hn0 := card_ne hn
  have hn1 := card_sub_one_ne hn
  field_simp

/-- **`Var σ̂²` with equal volumes**, in the setting of `integral_vcW_equal`:
`2σ⁴/(n − 1) + κ/n`. -/
theorem variance_sigHat_equal (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (c σ2 κ : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι)
    (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = σ2 / c)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ / c ^ 2 + 3 * (σ2 / c) ^ 2)
    (L : Ω → ℝ) :
    variance (fun ω => sigHat (fun _ => c) (fun s => L ω + ξ s ω)) P
      = 2 * σ2 ^ 2 / ((Fintype.card ι : ℝ) - 1) + κ / (Fintype.card ι : ℝ) := by
  have hsum : ∑ _r : ι, c ≠ 0 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_ne_zero (card_ne hn) hc
  rw [variance_sigHat ξ hind hmeas hL h0 (fun _ => σ2 / c) (fun _ => κ / c ^ 2) hv h4 L _ hsum]
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn0 : n ≠ 0 := card_ne hn
  have hn1 : n - 1 ≠ 0 := card_sub_one_ne hn
  have hm := cent_mul n hn_def hn0
  simp only [sigForm_const c hc hn, ← hn_def]
  have e1 : ∑ s : ι, ∑ r : ι, (c / (n - 1) * ((if s = r then 1 else 0) - 1 / n)) ^ 2 * (σ2 / c) * (σ2 / c)
      = (c / (n - 1)) ^ 2 * (σ2 / c) ^ 2 * (n * (1 - 1 / n)) := by
    have : ∀ s, ∑ r, ((if s = r then (1 : ℝ) else 0) - 1 / n) ^ 2 = 1 - 1 / n := fun s =>
      cent_sq_diag n hn_def hn0 s
    rw [show n * (1 - 1 / n) = ∑ _s : ι, (1 - 1 / n) by
      rw [sum_const, card_univ, nsmul_eq_mul, ← hn_def], mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [← this s, mul_sum]
    exact sum_congr rfl fun r _ => by ring
  rw [e1]
  simp only [↓reduceIte, sum_const, card_univ, nsmul_eq_mul, ← hn_def]
  field_simp

/-- `E σ̂² = σ²` with equal volumes. -/
theorem integral_sigHat_equal (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (c σ2 : ℝ) (hc : c ≠ 0) (hn : 2 ≤ Fintype.card ι)
    (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = σ2 / c) (L : Ω → ℝ) :
    ∫ ω, sigHat (fun _ => c) (fun s => L ω + ξ s ω) ∂P = σ2 := by
  have hsum : ∑ _r : ι, c ≠ 0 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_ne_zero (card_ne hn) hc
  rw [integral_sigHat ξ hind hmeas hL h0 (fun _ => σ2 / c) hv L _ hsum]
  have hn0 := card_ne hn
  have hn1 := card_sub_one_ne hn
  simp only [sigForm_const c hc hn, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- **The corrected `W` is unbiased** (Finding 47): with equal volumes and `n ≥ 4` independent,
identically distributed years, `E W̃ = Var σ̂²` for every noise distribution with four moments. -/
theorem integral_vcWCorr_equal (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ s, Measurable (ξ s)) (hL : ∀ s, MemLp (ξ s) 4 P) (h0 : ∀ s, ∫ ω, ξ s ω ∂P = 0)
    (c σ2 κ : ℝ) (hc : c ≠ 0) (hn : 4 ≤ Fintype.card ι)
    (hv : ∀ s, ∫ ω, ξ s ω * ξ s ω ∂P = σ2 / c)
    (h4 : ∀ s, ∫ ω, ξ s ω * ξ s ω * ξ s ω * ξ s ω ∂P = κ / c ^ 2 + 3 * (σ2 / c) ^ 2)
    (L : Ω → ℝ) :
    ∫ ω, vcWCorr (fun _ => c) (fun s => L ω + ξ s ω) ∂P
      = variance (fun ω => sigHat (fun _ => c) (fun s => L ω + ξ s ω)) P := by
  have hn2 : 2 ≤ Fintype.card ι := by omega
  have hsum : ∑ _r : ι, c ≠ 0 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_ne_zero (card_ne hn2) hc
  have hvar := variance_sigHat_equal ξ hind hmeas hL h0 c σ2 κ hc hn2 hv h4 L
  have hmem : MemLp (fun ω => sigHat (fun _ => c) (fun s => L ω + ξ s ω)) 2 P := by
    simp only [sigHat_eq _ _ _ hsum]
    exact memLp_quadForm hL _
  have hsq : ∫ ω, sigHat (fun _ => c) (fun s => L ω + ξ s ω) ^ 2 ∂P
      = 2 * σ2 ^ 2 / ((Fintype.card ι : ℝ) - 1) + κ / (Fintype.card ι : ℝ) + σ2 ^ 2 := by
    have := hvar
    rw [variance_eq_sub hmem] at this
    change ∫ ω, sigHat (fun _ => c) (fun s => L ω + ξ s ω) ^ 2 ∂P - _ = _ at this
    rw [integral_sigHat_equal ξ hind hmeas hL h0 c σ2 hc hn2 hv L] at this
    linarith
  rw [hvar]
  simp only [vcWCorr]
  rw [integral_sub ((integrable_vcW ξ hL L _ hsum).const_mul _)
      (((integrable_sigHat_sq ξ hL L _ hsum).const_mul 2).div_const _),
    integral_const_mul, integral_div, integral_const_mul, hsq,
    integral_vcW_equal ξ hind hmeas hL h0 c σ2 κ hc hn2 hv h4 L]
  have h4' : (4 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hn2' : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have hn3 : (Fintype.card ι : ℝ) - 3 ≠ 0 := by linarith
  field_simp
  ring

end Equal

section Between

/-! ### `β̂²`: Bühlmann–Straub's `τ̂²` one level up (G1b) -/

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
/-- `Σⱼ (yⱼ − ȳ)² = Σᵢⱼ Hᵢⱼ yᵢyⱼ`, `Hᵢⱼ = δᵢⱼ − 1/J`. -/
lemma sum_sq_dev [DecidableEq J] (y : J → ℝ) :
    ∑ j, (y j - (∑ i, y i) / (Fintype.card J : ℝ)) ^ 2
      = ∑ i, ∑ j, ((if i = j then 1 else 0) - 1 / (Fintype.card J : ℝ)) * y i * y j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp
  have hn : (Fintype.card J : ℝ) ≠ 0 := by positivity
  simp only [sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ,
    ite_true, sub_sq, sum_add_distrib, ← mul_sum, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
  simp only [sq]
  field_simp
  ring

omit [DecidableEq J] in
/-- **`β̂²` is unbiased** (G1b). Random region statistics `Yⱼ` in `L²` (the `σ̂ⱼ²`) with means
`sⱼ` (the `σⱼ²`) and covariances `Cᵢⱼ`, and estimates `Ŵᵢⱼ` with `E Ŵᵢⱼ = Cᵢⱼ` (e.g. the corrected
`W` of `integral_vcWCorr` on the diagonal). Then
`β̂² = (Σⱼ (Yⱼ − Ȳ)² − Σᵢⱼ HᵢⱼŴᵢⱼ)/(J − 1)`, `Hᵢⱼ = δᵢⱼ − 1/J`, has
`E β̂² = Σⱼ (sⱼ − s̄)²/(J − 1)`: Bühlmann–Straub's `τ̂²` with the `σ̂ⱼ²` as observations. With
uncorrelated regions (`Cᵢⱼ = 0`, `Ŵᵢⱼ = 0` for `i ≠ j`) the correction is `(1/J) Σⱼ Ŵⱼⱼ`, the app's
formula; correlated noise (ρ ≠ 0) correlates the `σ̂ⱼ²` and needs the cross terms. -/
theorem integral_betaHat [DecidableEq J] (Y : J → Ω → ℝ) (hY : ∀ j, MemLp (Y j) 2 P) (s : J → ℝ)
    (hs : ∀ j, ∫ ω, Y j ω ∂P = s j) (C : J → J → ℝ)
    (hC : ∀ i j, covariance (Y i) (Y j) P = C i j) (Wh : J → J → Ω → ℝ)
    (hWi : ∀ i j, Integrable (Wh i j) P) (hW : ∀ i j, ∫ ω, Wh i j ω ∂P = C i j) :
    ∫ ω, (∑ j, (Y j ω - (∑ i, Y i ω) / (Fintype.card J : ℝ)) ^ 2
        - ∑ i, ∑ j, ((if i = j then 1 else 0) - 1 / (Fintype.card J : ℝ)) * Wh i j ω)
          / ((Fintype.card J : ℝ) - 1) ∂P
      = (∑ j, (s j - (∑ i, s i) / (Fintype.card J : ℝ)) ^ 2) / ((Fintype.card J : ℝ) - 1) := by
  set H : J → J → ℝ := fun i j => (if i = j then 1 else 0) - 1 / (Fintype.card J : ℝ)
  have hYY : ∀ i j, Integrable (fun ω => Y i ω * Y j ω) P := fun i j =>
    (hY i).integrable_mul (hY j)
  have hE : ∀ i j, ∫ ω, Y i ω * Y j ω ∂P = C i j + s i * s j := fun i j => by
    have := covariance_eq_sub (hY i) (hY j)
    rw [hC, hs, hs] at this
    change C i j = ∫ ω, Y i ω * Y j ω ∂P - _ at this
    linarith
  simp only [sum_sq_dev]
  rw [integral_div, integral_sub (integrable_finsetSum _ fun i _ => integrable_finsetSum _
      fun j _ => by simpa only [mul_assoc] using (hYY i j).const_mul (H i j))
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hWi i j).const_mul _)]
  congr 1
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      simpa only [mul_assoc] using (hYY i j).const_mul (H i j),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hWi i j).const_mul _,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => by simpa only [mul_assoc] using (hYY i j).const_mul (H i j),
    integral_finsetSum _ fun j _ => (hWi i j).const_mul _, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, integral_const_mul, hE, hW]
  ring

omit [DecidableEq J] in
/-- **`β̂²` with the corrected `W` is unbiased** (G1b, given G1a). Regions `j` with equal volumes
`cⱼ`, `n ≥ 4` independent years each (variances `σⱼ²/cⱼ`, fourth cumulants `κⱼ/cⱼ²`), any levels,
and uncorrelated `σ̂ⱼ²` across regions (e.g. regions independent; not for correlated noise, `ρ ≠ 0`).
With `Ŵⱼⱼ = W̃ⱼ` (`vcWCorr`) and `Ŵᵢⱼ = 0` off the diagonal, `β̂²` of `integral_betaHat` (that is
`Σⱼ(σ̂ⱼ² − σ̄²)²/(J − 1) − (1/J)Σⱼ W̃ⱼ`) has `E β̂² = Σⱼ (σⱼ² − σ̄²)²/(J − 1)`. -/
theorem integral_betaHat_equal [DecidableEq J] (ξ : J → ι → Ω → ℝ) (hind : ∀ j, iIndepFun (ξ j) P)
    (hmeas : ∀ j s, Measurable (ξ j s)) (hL : ∀ j s, MemLp (ξ j s) 4 P)
    (h0 : ∀ j s, ∫ ω, ξ j s ω ∂P = 0) (c σ2 κ : J → ℝ) (hc : ∀ j, c j ≠ 0)
    (hn : 4 ≤ Fintype.card ι) (hv : ∀ j s, ∫ ω, ξ j s ω * ξ j s ω ∂P = σ2 j / c j)
    (h4 : ∀ j s, ∫ ω, ξ j s ω * ξ j s ω * ξ j s ω * ξ j s ω ∂P
      = κ j / c j ^ 2 + 3 * (σ2 j / c j) ^ 2) (L : J → Ω → ℝ)
    (hunc : ∀ i j, i ≠ j → covariance (fun ω => sigHat (fun _ => c i) (fun s => L i ω + ξ i s ω))
      (fun ω => sigHat (fun _ => c j) (fun s => L j ω + ξ j s ω)) P = 0) :
    ∫ ω, (∑ j, (sigHat (fun _ => c j) (fun s => L j ω + ξ j s ω)
          - (∑ i, sigHat (fun _ => c i) (fun s => L i ω + ξ i s ω)) / (Fintype.card J : ℝ)) ^ 2
        - ∑ i, ∑ j, ((if i = j then 1 else 0) - 1 / (Fintype.card J : ℝ))
          * (if i = j then vcWCorr (fun _ => c j) (fun s => L j ω + ξ j s ω) else 0))
          / ((Fintype.card J : ℝ) - 1) ∂P
      = (∑ j, (σ2 j - (∑ i, σ2 i) / (Fintype.card J : ℝ)) ^ 2) / ((Fintype.card J : ℝ) - 1) := by
  have hn2 : 2 ≤ Fintype.card ι := by omega
  set Y : J → Ω → ℝ := fun j ω => sigHat (fun _ => c j) (fun s => L j ω + ξ j s ω) with hYdef
  have hsum : ∀ j, ∑ _r : ι, c j ≠ 0 := fun j => by
    rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_ne_zero (card_ne hn2) (hc j)
  have hY : ∀ j, MemLp (Y j) 2 P := fun j => by
    simp only [hYdef, sigHat_eq _ _ _ (hsum j)]
    exact memLp_quadForm (hL j) _
  have hWi : ∀ i j, Integrable (fun ω => if i = j then
      vcWCorr (fun _ => c j) (fun s => L j ω + ξ j s ω) else 0) P := fun i j => by
    by_cases h : i = j
    · simp only [h, ↓reduceIte]
      simp only [vcWCorr]
      exact ((integrable_vcW (ξ j) (hL j) (L j) _ (hsum j)).const_mul _).sub
        (((integrable_sigHat_sq (ξ j) (hL j) (L j) _ (hsum j)).const_mul 2).div_const _)
    · simp [h]
  refine integral_betaHat Y hY σ2 (fun j => integral_sigHat_equal (ξ j) (hind j) (hmeas j) (hL j)
    (h0 j) (c j) (σ2 j) (hc j) hn2 (hv j) (L j)) (fun i j => covariance (Y i) (Y j) P)
    (fun _ _ => rfl) _ hWi (fun i j => ?_)
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    rw [integral_vcWCorr_equal (ξ i) (hind i) (hmeas i) (hL i) (h0 i) (c i) (σ2 i) (κ i) (hc i) hn
      (hv i) (h4 i) (L i), covariance_self (hY i).aemeasurable]
  · simp only [h, ↓reduceIte, integral_zero]
    exact (hunc i j h).symm

end Between

end Credibility.VcW
