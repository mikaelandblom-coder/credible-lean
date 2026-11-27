import Credibility.Merging
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Merging two cohorts when the gap looks small: the exact winner's curse under normal noise

**Optional distribution layer** (owner, 2026-11-15): this file assumes *normal noise*, so nothing
in the core depends on it.

Two cohorts with fixed levels `μ₁`, `μ₂`, gap `δ = μ₁ - μ₂`, estimates `Xⱼ = μⱼ + eⱼ`, as in
`Merging.lean`: `V = Var(X₁ - X₂)`, and the predictor `X₁ - β(X₁ - X₂)` of `μ₁`. Merging uses
the weight `a = (v₁ - c₁₂)/V` (`Merging.weight` at gap `0`), keeping the cohorts separate the
weight `a·k` (the thesis blend: `k = V/(V + 2τ²)`; the cohort's own estimate: `k = 0`). The
**pre-test rule** merges iff the observed gap looks small, `(X₁ - X₂)² < c`, and so decides with
the same data it then blends (notes/merging-cohorts.md §4, "Winner's curse").

**Reduction** (`integral_sq_pretest`). Write `D = X₁ - X₂` (law `N(δ, V)`) and
`e₁ = u + a(D - δ)` (the regression of `e₁` on `D`; under normal noise `u` is independent of `D`).
Then the error of every such rule is `u + a·G(D)` with `G(x) = -δ` when merged and
`G(x) = (1 - k)x - δ` when kept separate, and

`E(error)² = E u² + a² R`,  `R = E G(D)²` (`gapRisk`):

predicting `μ₁` is estimating the gap `δ`, and the pre-test merge is **hard thresholding** of the
observed gap (with shrinkage `1 - k` above the threshold). The same holds for cohort 2 with
`a₂ = (v₂ - c₁₂)/V`, so the comparison of rules is the comparison of `R`, cohort by cohort.
Always merging has `R = δ²` (`gapRisk_merge`), never merging `R = m²V + (1 - m)²δ²` with
`m = 1 - k` (`gapRisk_never`); they tie at `δ²(2 - m) = mV`.

**Finding 43** (`lt_gapRisk_of_tie`). At that tie, the pre-test rule is strictly worse than both,
for every threshold `c > 0`: no threshold makes "merge iff the gap looks small" never lose to both
fixed rules (Judge & Bock's pre-test estimator; hard thresholding). Numerically
(`studies/runs/pretest-merge.js`): with own estimates (`k = 0`), `c = 2V` it loses by `0.20·a²V`,
a fifth of the separate rule's whole excess; it loses to both on 5–14% of the gaps.

Proof of the Finding: with `p(x) = δ² - (mx - δ)²`, `R - δ² = E[p(D); D² < c]
`= -E[p(D); D² ≥ c]`, since `E p(D) = 0` at the tie. Folding `x ↦ -x` against the density
(`integral_eq_integral_Ioi_add_neg`, `gaussianPDFReal_neg`), the integrand on `x > 0` is a positive
factor times `sinh y/(y cosh y) - mV/(2δ²)`, `y = δx/V` (`fold_eq`), and `sinh y/(y cosh y)` is
strictly decreasing (`sinh_div_strictAntiOn`). So the fold is positive below `√c` or negative
above it, and one of the two integrals has the needed sign (`integral_pos_of_fold`).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal

namespace Credibility
namespace PreTest

/-- The pre-test weight on the other cohort: `a` (merge) when the observed gap looks small,
`x² < c`, and `a·k` (keep separate) otherwise. -/
noncomputable def weight (a k c x : ℝ) : ℝ := if x ^ 2 < c then a else a * k

/-- The pre-test weight switches between the two rules of `Merging.lean`: with
`a = (v - c₁₂)/V` and `k = V/(V + x)` it is `Merging.weight` at gap `0` (merge) when the gap looks
small and at the working gap `x` (separate, `x = 2τ²` for the thesis rule) otherwise. -/
theorem weight_eq_merging {v c₁₂ V x : ℝ} (hV : V ≠ 0) (hVx : V + x ≠ 0) (c D : ℝ) :
    weight ((v - c₁₂) / V) (V / (V + x)) c D
      = if D ^ 2 < c then Merging.weight v c₁₂ V 0 else Merging.weight v c₁₂ V x := by
  rw [Merging.weight_eq (by simpa using hV), Merging.weight_eq hVx, weight, add_zero]
  congr 1
  field_simp

/-- The rule's error in units of `a`, as an estimate of the gap: `G(x) = -δ` when merged and
`G(x) = m x - δ` (`m = 1 - k`) when kept separate. -/
noncomputable def gapErr (m δ c x : ℝ) : ℝ := if x ^ 2 < c then -δ else m * x - δ

/-- The risk `R = E G(D)²` of the gap estimate, `D ~ N(δ, V)`. -/
noncomputable def gapRisk (m δ c : ℝ) (V : ℝ≥0) : ℝ := ∫ x, gapErr m δ c x ^ 2 ∂gaussianReal δ V

lemma measurable_gapErr (m δ c : ℝ) : Measurable (gapErr m δ c) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const (by fun_prop)

lemma memLp_gapErr (m δ c : ℝ) (V : ℝ≥0) : MemLp (gapErr m δ c) 2 (gaussianReal δ V) := by
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal δ V) := memLp_id_gaussianReal 2
  have hg : MemLp (fun x : ℝ => |m * x - δ| + |δ|) 2 (gaussianReal δ V) :=
    ((hid.const_mul m).sub (memLp_const δ)).abs.add (memLp_const _)
  refine hg.of_le (measurable_gapErr m δ c).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  simp only [gapErr, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |m * x - δ| + |δ|)]
  split_ifs
  · rw [abs_neg]; linarith [abs_nonneg (m * x - δ)]
  · linarith [abs_nonneg δ]

/-- The pre-test rule's error is `u + a·G(D)`. -/
lemma err_eq (u a k c δ D : ℝ) :
    u + a * (D - δ) - weight a k c D * D = u + a * gapErr (1 - k) δ c D := by
  simp only [weight, gapErr]
  split_ifs <;> ring

/-- **The reduction**: if `D = X₁ - X₂` has law `N(δ, V)` and the residual `u = e₁ - a(D - δ)`
(mean `0`) is independent of `D` (as under normal noise), the pre-test rule's MSE is

`E(u + a(D - δ) - β̂(D)·D)² = E u² + a²·R(1 - k, δ, c, V)`. -/
theorem integral_sq_pretest {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u D : Ω → ℝ} {δ : ℝ} {V : ℝ≥0} (hu : MemLp u 2 P)
    (hu0 : P[u] = 0) (hD : HasLaw D (gaussianReal δ V) P) (hind : IndepFun u D P) (a k c : ℝ) :
    P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2]
      = P[fun ω => u ω ^ 2] + a ^ 2 * gapRisk (1 - k) δ c V := by
  set G := gapErr (1 - k) δ c
  have hG : MemLp (fun ω => G (D ω)) 2 P := hD.memLp_comp (memLp_gapErr (1 - k) δ c V)
  have hpt : ∀ ω, (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2
      = u ω ^ 2 + 2 * a * (u ω * G (D ω)) + a ^ 2 * G (D ω) ^ 2 := fun ω => by
    rw [err_eq]; ring
  simp_rw [hpt]
  have i1 := hu.integrable_sq
  have i2 := (hu.integrable_mul hG).const_mul (2 * a)
  have i3 := hG.integrable_sq.const_mul (a ^ 2)
  have e1 := integral_add (i1.add i2) i3
  have e2 := integral_add i1 i2
  simp only [Pi.add_apply, Pi.mul_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul]
  have hcross : P[fun ω => u ω * G (D ω)] = 0 := by
    have hi : IndepFun u (fun ω => G (D ω)) P :=
      hind.comp measurable_id (measurable_gapErr (1 - k) δ c)
    have := hi.integral_mul_eq_mul_integral hu.aestronglyMeasurable hG.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hu0, zero_mul]
  have hsq : P[fun ω => G (D ω) ^ 2] = gapRisk (1 - k) δ c V :=
    hD.integral_comp (f := fun x => G x ^ 2)
      ((measurable_gapErr (1 - k) δ c).pow_const 2).aestronglyMeasurable
  rw [hcross, hsq]
  ring

/-- **Always merging** (`m = 0`, i.e. `k = 1`): `R = δ²`. -/
theorem gapRisk_merge (δ c : ℝ) (V : ℝ≥0) : gapRisk 0 δ c V = δ ^ 2 := by
  have : ∀ x, gapErr 0 δ c x ^ 2 = δ ^ 2 := fun x => by
    simp only [gapErr]; split_ifs <;> ring
  simp [gapRisk, this]

/-- **Never merging** (`c ≤ 0`): `R = m²V + (1 - m)²δ²`. -/
theorem gapRisk_never (m δ : ℝ) {c : ℝ} (hc : c ≤ 0) (V : ℝ≥0) :
    gapRisk m δ c V = m ^ 2 * V + (1 - m) ^ 2 * δ ^ 2 := by
  have hpt : ∀ x, gapErr m δ c x ^ 2
      = m ^ 2 * (x - δ) ^ 2 + (2 * m * (m - 1) * δ) * (x - δ) + (m - 1) ^ 2 * δ ^ 2 := fun x => by
    have : ¬ x ^ 2 < c := not_lt.2 (le_trans hc (sq_nonneg x))
    simp only [gapErr, this, ite_false]; ring
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal δ V) := memLp_id_gaussianReal 2
  have hc' : MemLp (fun x : ℝ => x - δ) 2 (gaussianReal δ V) := hid.sub (memLp_const δ)
  have i1 := hc'.integrable_sq.const_mul (m ^ 2)
  have i2 := (hc'.integrable one_le_two).const_mul (2 * m * (m - 1) * δ)
  have hvar : ∫ x, (x - δ) ^ 2 ∂gaussianReal δ V = V := by
    have h := variance_fun_id_gaussianReal (μ := δ) (v := V)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    exact h
  have hmean : ∫ x, (x - δ) ∂gaussianReal δ V = 0 := by
    rw [integral_sub (hid.integrable one_le_two) (integrable_const _), integral_id_gaussianReal]
    simp
  simp only [gapRisk, hpt]
  have e1 := integral_add (i1.add i2) (integrable_const ((m - 1) ^ 2 * δ ^ 2))
  have e2 := integral_add i1 i2
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, hvar, hmean]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-! ### The proof of Finding 43: folding at `x ↦ -x` -/
theorem integral_eq_integral_Ioi_add_neg {g : ℝ → ℝ} (hg : Integrable g) :
    ∫ x, g x = ∫ x in Ioi 0, (g x + g (-x)) := by
  have h1 : ∫ x, g x = (∫ x in Iic 0, g x) + ∫ x in Ioi 0, g x := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hg.integrableOn
      hg.integrableOn, Iic_union_Ioi, Measure.restrict_univ]
  have h2 : ∫ x in Iic 0, g x = ∫ x in Ioi 0, g (-x) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  have hn : Integrable (fun x => g (-x)) := hg.comp_neg
  rw [h1, h2, integral_add hg.integrableOn hn.integrableOn, add_comm]

theorem sinh_div_strictAntiOn : StrictAntiOn (fun y => sinh y / (y * cosh y)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro y hy
    have hD : y * cosh y ≠ 0 := mul_ne_zero (ne_of_gt hy) (cosh_pos y).ne'
    exact (continuous_sinh.continuousAt.div (continuous_id.mul continuous_cosh).continuousAt
      hD).continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hy0 : (0 : ℝ) < y := hy
    have hD : y * cosh y ≠ 0 := mul_ne_zero (ne_of_gt hy0) (cosh_pos y).ne'
    have hd : HasDerivAt (fun y => sinh y / (y * cosh y))
        ((cosh y * (y * cosh y) - sinh y * (1 * cosh y + y * sinh y)) / (y * cosh y) ^ 2) y :=
      (Real.hasDerivAt_sinh y).div ((hasDerivAt_id' y).mul (Real.hasDerivAt_cosh y)) hD
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos
    · have hs : y < sinh y := self_lt_sinh_iff.2 hy0
      have hc : 1 < cosh y := one_lt_cosh.2 hy0.ne'
      have hid : cosh y ^ 2 - sinh y ^ 2 = 1 := cosh_sq_sub_sinh_sq y
      nlinarith [mul_pos (sub_pos.2 hc) (lt_trans hy0 hs)]
    · positivity

lemma gaussianPDFReal_neg {δ : ℝ} {V : ℝ≥0} (hV : (V : ℝ) ≠ 0) (x : ℝ) :
    gaussianPDFReal δ V (-x) = gaussianPDFReal δ V x * exp (-(2 * δ * x / V)) := by
  simp only [gaussianPDFReal, mul_assoc, ← exp_add]
  congr 2
  field_simp
  ring

lemma integrable_pdf_mul {δ : ℝ} {V : ℝ≥0} (hV : V ≠ 0) {F : ℝ → ℝ}
    (hF : Integrable F (gaussianReal δ V)) :
    Integrable (fun x => gaussianPDFReal δ V x * F x) := by
  rw [gaussianReal_of_var_ne_zero _ hV, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hF
  simpa [toReal_gaussianPDF] using hF

/-- The folded integrand of `p(x) = δ² - (mx - δ)²` against the density has the sign of
`sinh y/(y cosh y) - mV/(2δ²)`, `y = δx/V`. -/
lemma fold_eq {m δ : ℝ} {V : ℝ≥0} (hV : (V : ℝ) ≠ 0) (hδ : δ ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    gaussianPDFReal δ V x * (δ ^ 2 - (m * x - δ) ^ 2)
        + gaussianPDFReal δ V (-x) * (δ ^ 2 - (m * -x - δ) ^ 2)
      = (gaussianPDFReal δ V x * exp (-(δ * x / V)) * (4 * m * x * δ * (δ * x / V)
          * cosh (δ * x / V)))
        * (sinh (δ * x / V) / (δ * x / V * cosh (δ * x / V)) - m * V / (2 * δ ^ 2)) := by
  rw [gaussianPDFReal_neg hV]
  set y := δ * x / V with hy
  have hy0 : y ≠ 0 := by rw [hy]; exact div_ne_zero (mul_ne_zero hδ hx) hV
  have hc : cosh y ≠ 0 := (cosh_pos y).ne'
  have h2 : exp (-(2 * δ * x / V)) = exp (-y) * exp (-y) := by
    rw [← exp_add, hy]; congr 1; ring
  rw [h2, sinh_eq, cosh_eq] at *
  have hE : exp y ≠ 0 := (exp_pos y).ne'
  rw [exp_neg]
  have hxy : x = y * V / δ := by rw [hy]; field_simp
  rw [hxy]
  field_simp
  ring

/-- A fold that is nonnegative on `x > 0` and positive on a set of positive length gives a
positive integral under `N(δ, V)`. -/
lemma integral_pos_of_fold {δ : ℝ} {V : ℝ≥0} (hV0 : V ≠ 0) {F : ℝ → ℝ}
    (hF : Integrable F (gaussianReal δ V)) {S : Set ℝ} (hSsub : S ⊆ Ioi 0) (hSvol : 0 < volume S)
    (hnn : ∀ x, 0 < x → 0 ≤ gaussianPDFReal δ V x * F x + gaussianPDFReal δ V (-x) * F (-x))
    (hpos : ∀ x ∈ S, 0 < gaussianPDFReal δ V x * F x + gaussianPDFReal δ V (-x) * F (-x)) :
    0 < ∫ x, F x ∂gaussianReal δ V := by
  rw [integral_gaussianReal_eq_integral_smul hV0]
  simp only [smul_eq_mul]
  have hI := integrable_pdf_mul hV0 hF
  rw [integral_eq_integral_Ioi_add_neg hI, setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le hSvol (measure_mono fun x hx => ⟨(hpos x hx).ne', hSsub hx⟩)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => hnn x hx
  · exact (hI.add hI.comp_neg).integrableOn

/-- **Finding 43: the pre-test merge loses to both fixed rules.** At the gap where always and
never merging tie (`δ²(2 - m) = mV`, `0 < m < 2`), the pre-test rule's risk exceeds their common
risk `δ²` for every threshold `c > 0`, under normal noise. -/
theorem lt_gapRisk_of_tie {m δ c : ℝ} {V : ℝ≥0} (hm : 0 < m) (hm2 : m < 2) (hδ : 0 < δ)
    (htie : δ ^ 2 * (2 - m) = m * V) (hc : 0 < c) : δ ^ 2 < gapRisk m δ c V := by
  have hVpos : (0 : ℝ) < V := by
    have h2 : 0 < 2 - m := by linarith
    have : 0 < m * (V : ℝ) := by rw [← htie]; positivity
    exact pos_of_mul_pos_right this hm.le
  have hV : (V : ℝ) ≠ 0 := hVpos.ne'
  have hV0 : V ≠ 0 := fun h => hV (by simp [h])
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal δ V) := memLp_id_gaussianReal 2
  have hq : MemLp (fun x : ℝ => m * x - δ) 2 (gaussianReal δ V) :=
    (hid.const_mul m).sub (memLp_const δ)
  have hpI : Integrable (fun x : ℝ => δ ^ 2 - (m * x - δ) ^ 2) (gaussianReal δ V) :=
    (integrable_const _).sub hq.integrable_sq
  have htot : ∫ x, (m * x - δ) ^ 2 ∂gaussianReal δ V = δ ^ 2 := by
    have h := gapRisk_never m δ (le_refl (0 : ℝ)) V
    have he : ∀ x, gapErr m δ 0 x = m * x - δ := fun x => by
      simp [gapErr, not_lt.2 (sq_nonneg x)]
    simp only [gapRisk, he] at h
    rw [h]
    linear_combination (-m) * htie
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  set β := m * V / (2 * δ ^ 2) with hβ
  set U : ℝ → ℝ := fun y => sinh y / (y * cosh y) with hU
  -- the fold of `p` has the sign of `U(δx/V) - β`
  have hsign : ∀ x, 0 < x → ∃ A, 0 < A ∧
      gaussianPDFReal δ V x * (δ ^ 2 - (m * x - δ) ^ 2)
        + gaussianPDFReal δ V (-x) * (δ ^ 2 - (m * -x - δ) ^ 2) = A * (U (δ * x / V) - β) := by
    intro x hx
    refine ⟨_, ?_, fold_eq hV hδ.ne' hx.ne'⟩
    have := gaussianPDFReal_pos δ V x hV0
    have hy : 0 < δ * x / V := by positivity
    have := cosh_pos (δ * x / V)
    positivity
  have hmono : ∀ x, 0 < x → (x < √c ↔ U (δ * √c / V) < U (δ * x / V)) := by
    intro x hx
    have hδV : 0 < δ / V := div_pos hδ hVpos
    have e1 : δ * x / V = δ / V * x := by ring
    have e2 : δ * √c / V = δ / V * √c := by ring
    rw [e1, e2]
    constructor
    · intro h
      exact sinh_div_strictAntiOn (by simp; positivity) (by simp; positivity)
        (mul_lt_mul_of_pos_left h hδV)
    · intro h
      by_contra h'
      have : δ / V * √c ≤ δ / V * x := mul_le_mul_of_nonneg_left (not_lt.1 h') hδV.le
      exact absurd h (not_lt.2 (sinh_div_strictAntiOn.antitoneOn (by simp; positivity)
        (by simp; positivity) this))
  have hsq : ∀ x, 0 ≤ x → (x ^ 2 < c ↔ x < √c) := fun x hx => (Real.lt_sqrt hx).symm
  by_cases hcase : β ≤ U (δ * √c / V)
  · -- the part inside the threshold is positive
    set F := Set.indicator {x : ℝ | x ^ 2 < c} (fun x : ℝ => δ ^ 2 - (m * x - δ) ^ 2)
    have hmeas : MeasurableSet {x : ℝ | x ^ 2 < c} := measurableSet_lt (by fun_prop) measurable_const
    have hFI : Integrable F (gaussianReal δ V) := hpI.indicator hmeas
    have hR : gapRisk m δ c V = δ ^ 2 + ∫ x, F x ∂gaussianReal δ V := by
      have hpt : ∀ x, gapErr m δ c x ^ 2 = (m * x - δ) ^ 2 + F x := fun x => by
        simp only [gapErr, F, Set.indicator_apply, Set.mem_ofPred_eq]
        split_ifs <;> ring
      simp only [gapRisk, hpt]
      rw [integral_add hq.integrable_sq hFI, htot]
    have hfold : ∀ x, 0 < x → gaussianPDFReal δ V x * F x + gaussianPDFReal δ V (-x) * F (-x)
        = if x < √c then gaussianPDFReal δ V x * (δ ^ 2 - (m * x - δ) ^ 2)
            + gaussianPDFReal δ V (-x) * (δ ^ 2 - (m * -x - δ) ^ 2) else 0 := by
      intro x hx
      simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, neg_sq, hsq x hx.le]
      split_ifs <;> ring
    have hI := integral_pos_of_fold hV0 hFI (S := Ioo 0 √c) Ioo_subset_Ioi_self (by simp [hs])
      (fun x hx => by
        rw [hfold x hx]
        split_ifs with h
        · obtain ⟨A, hA, he⟩ := hsign x hx
          rw [he]
          have := (hmono x hx).1 h
          exact mul_nonneg hA.le (by linarith)
        · exact le_rfl)
      (fun x hx => by
        rw [hfold x hx.1, ite_eq_left hx.2]
        obtain ⟨A, hA, he⟩ := hsign x hx.1
        rw [he]
        have := (hmono x hx.1).1 hx.2
        exact mul_pos hA (by linarith))
    linarith
  · -- the part beyond the threshold is negative
    push Not at hcase
    set F := Set.indicator {x : ℝ | c ≤ x ^ 2} (fun x : ℝ => (m * x - δ) ^ 2 - δ ^ 2)
    have hmeas : MeasurableSet {x : ℝ | c ≤ x ^ 2} := measurableSet_le measurable_const (by fun_prop)
    have hFI : Integrable F (gaussianReal δ V) := (hpI.neg.congr (ae_of_all _ fun x => by
      simp only [Pi.neg_apply]; ring)).indicator hmeas
    have hR : gapRisk m δ c V = δ ^ 2 + ∫ x, F x ∂gaussianReal δ V := by
      have hpt : ∀ x, gapErr m δ c x ^ 2 = δ ^ 2 + F x := fun x => by
        simp only [gapErr, F, Set.indicator_apply, Set.mem_ofPred_eq]
        split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring
      simp only [gapRisk, hpt]
      rw [integral_add (integrable_const _) hFI]
      simp
    have hfold : ∀ x, 0 < x → gaussianPDFReal δ V x * F x + gaussianPDFReal δ V (-x) * F (-x)
        = if x < √c then 0 else -(gaussianPDFReal δ V x * (δ ^ 2 - (m * x - δ) ^ 2)
            + gaussianPDFReal δ V (-x) * (δ ^ 2 - (m * -x - δ) ^ 2)) := by
      intro x hx
      have : c ≤ x ^ 2 ↔ ¬ x < √c := by rw [← hsq x hx.le, not_lt]
      simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, neg_sq, this]
      split_ifs <;> ring
    have hneg : ∀ x, 0 < x → ¬ x < √c → 0 < -(gaussianPDFReal δ V x * (δ ^ 2 - (m * x - δ) ^ 2)
        + gaussianPDFReal δ V (-x) * (δ ^ 2 - (m * -x - δ) ^ 2)) := by
      intro x hx h
      obtain ⟨A, hA, he⟩ := hsign x hx
      rw [he]
      have : U (δ * x / V) ≤ U (δ * √c / V) := by
        by_contra h'
        exact h ((hmono x hx).2 (lt_of_not_ge h'))
      nlinarith
    have hI := integral_pos_of_fold hV0 hFI (S := Ioi √c) (Ioi_subset_Ioi hs.le) (by simp)
      (fun x hx => by
        rw [hfold x hx]
        split_ifs with h
        · exact le_rfl
        · exact (hneg x hx h).le)
      (fun x hx => by
        have hx' : ¬ x < √c := not_lt.2 (le_of_lt hx)
        rw [hfold x (lt_trans hs hx), ite_eq_right hx']
        exact hneg x (lt_trans hs hx) hx')
    linarith

/-- **Finding 43 for the predictor**: under the hypotheses of `integral_sq_pretest`, with
`a ≠ 0`, `0 < 1 - k < 2` and the gap at the tie, the pre-test rule's MSE exceeds both that of
always merging (`k = 1`) and that of never merging (`c = 0`), for every threshold `c > 0`. -/
theorem pretest_mse_gt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u D : Ω → ℝ} {δ : ℝ} {V : ℝ≥0} (hu : MemLp u 2 P)
    (hu0 : P[u] = 0) (hD : HasLaw D (gaussianReal δ V) P) (hind : IndepFun u D P)
    {a k c : ℝ} (ha : a ≠ 0) (hk : 0 < 1 - k) (hk2 : 1 - k < 2) (hδ : 0 < δ)
    (htie : δ ^ 2 * (2 - (1 - k)) = (1 - k) * V) (hc : 0 < c) :
    P[fun ω => (u ω + a * (D ω - δ) - weight a 1 c (D ω) * D ω) ^ 2]
        < P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2] ∧
      P[fun ω => (u ω + a * (D ω - δ) - weight a k 0 (D ω) * D ω) ^ 2]
        < P[fun ω => (u ω + a * (D ω - δ) - weight a k c (D ω) * D ω) ^ 2] := by
  have hlt := lt_gapRisk_of_tie hk hk2 hδ htie hc
  have ha2 : 0 < a ^ 2 := by positivity
  rw [integral_sq_pretest hu hu0 hD hind, integral_sq_pretest hu hu0 hD hind,
    integral_sq_pretest hu hu0 hD hind, sub_self, gapRisk_merge,
    gapRisk_never _ _ le_rfl]
  have hnev : (1 - k) ^ 2 * (V : ℝ) + (1 - (1 - k)) ^ 2 * δ ^ 2 = δ ^ 2 := by
    have : (1 - k) * (V : ℝ) = δ ^ 2 * (2 - (1 - k)) := htie.symm
    nlinarith [this]
  rw [hnev]
  exact ⟨by nlinarith, by nlinarith⟩

end PreTest
end Credibility
