import Credibility.CoreMoments

/-!
# Clipping an estimated credibility factor that does not see the cohort's data (G3b)

Eq. (34) of the thesis clips `z` to `[0, 1]`. For a fixed `z`, clipping never raises the blend's mean
squared error exactly when the best `z` is in `[0, 1]` (`BlendMoments.errVar_clipZ_le_iff`,
Finding 36). Here `ẑ` is random but independent of the cohort estimate, the portfolio estimate and
the target (a held-out or cross-fitted `ẑ`):

* `BlendMoments.integral_sq_blend_indep`: `E[(ẑX + (1 − ẑ)Y − Z)²] = E[errVar(ẑ)]`, the fixed-`z`
  error averaged over `ẑ`;
* `BlendMoments.integral_sq_blend_clip_le`: if the best `z` is in `[0, 1]`, clipping `ẑ` never raises
  the mean squared error, for every distribution of `ẑ` and of the data with these moments;
* `BlendMoments.integral_sq_blend_clip_le_iff`: and that holds for every independent `ẑ` exactly when
  the best `z` is in `[0, 1]`.

An in-sample `ẑ` is correlated with the cohort's data, and none of this applies (studied in S83).
Nothing about the distribution is assumed beyond second moments and independence of `ẑ`.
-/

open MeasureTheory ProbabilityTheory

namespace Credibility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace BlendMoments

/-- The blend's error for a fixed `z` as a quadratic: with `A = X − Y`, `B = Y − Z`,
`errVar z = z² E A² + 2z E[AB] + E B²`. -/
lemma errVar_eq_quad (m : BlendMoments) {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hZ : MemLp Z 2 P) {μ : ℝ} (hXm : P[X] = μ) (hYm : P[Y] = μ) (hZm : P[Z] = μ)
    (h1 : Var[X; P] = m.varCohort) (h2 : Var[Y; P] = m.varPortfolio)
    (h3 : Var[Z; P] = m.varTarget) (h4 : cov[X, Y; P] = m.covEst)
    (h5 : cov[X, Z; P] = m.covCohortTarget) (h6 : cov[Y, Z; P] = m.covPortfolioTarget) (z : ℝ) :
    m.errVar z = z ^ 2 * P[fun ω => (X ω - Y ω) ^ 2]
      + 2 * z * P[fun ω => (X ω - Y ω) * (Y ω - Z ω)] + P[fun ω => (Y ω - Z ω) ^ 2] := by
  rw [← m.integral_sq_blend_sub hX hY hZ hXm hYm hZm h1 h2 h3 h4 h5 h6 z]
  have hA := hX.sub hY
  have hB := hY.sub hZ
  have iA : Integrable (fun ω => (X ω - Y ω) ^ 2) P := hA.integrable_sq
  have iB : Integrable (fun ω => (Y ω - Z ω) ^ 2) P := hB.integrable_sq
  have iAB : Integrable (fun ω => (X ω - Y ω) * (Y ω - Z ω)) P := hA.integrable_mul hB
  have e : (fun ω => (z * X ω + (1 - z) * Y ω - Z ω) ^ 2)
      = fun ω => z ^ 2 * (X ω - Y ω) ^ 2 + 2 * z * ((X ω - Y ω) * (Y ω - Z ω))
        + (Y ω - Z ω) ^ 2 := funext fun ω => by ring
  rw [e, integral_add ((iA.const_mul _).fun_add (iAB.const_mul _)) iB,
    integral_add (iA.const_mul _) (iAB.const_mul _), integral_const_mul, integral_const_mul]

/-- **The error of the blend with an independent `ẑ`** (G3b). If `ẑ` (in `L²`) is independent of the
cohort estimate `X`, the portfolio estimate `Y` and the target `Z` jointly (e.g. fitted on held-out
data), then `E[(ẑX + (1 − ẑ)Y − Z)²] = E[errVar(ẑ)]`, for every distribution with these moments. -/
theorem integral_sq_blend_indep (m : BlendMoments) {X Y Z zh : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) (hz : MemLp zh 2 P) {μ : ℝ} (hXm : P[X] = μ)
    (hYm : P[Y] = μ) (hZm : P[Z] = μ)
    (h1 : Var[X; P] = m.varCohort) (h2 : Var[Y; P] = m.varPortfolio)
    (h3 : Var[Z; P] = m.varTarget) (h4 : cov[X, Y; P] = m.covEst)
    (h5 : cov[X, Z; P] = m.covCohortTarget) (h6 : cov[Y, Z; P] = m.covPortfolioTarget)
    (hind : IndepFun zh (fun ω => (X ω, Y ω, Z ω)) P) :
    P[fun ω => (zh ω * X ω + (1 - zh ω) * Y ω - Z ω) ^ 2] = P[fun ω => m.errVar (zh ω)] := by
  have hA := hX.sub hY
  have hB := hY.sub hZ
  set a := P[fun ω => (X ω - Y ω) ^ 2]
  set b := P[fun ω => (X ω - Y ω) * (Y ω - Z ω)]
  set c := P[fun ω => (Y ω - Z ω) ^ 2]
  have iA : Integrable (fun ω => (X ω - Y ω) ^ 2) P := hA.integrable_sq
  have iB : Integrable (fun ω => (Y ω - Z ω) ^ 2) P := hB.integrable_sq
  have iAB : Integrable (fun ω => (X ω - Y ω) * (Y ω - Z ω)) P := hA.integrable_mul hB
  have iz2 : Integrable (fun ω => zh ω ^ 2) P := hz.integrable_sq
  have iz : Integrable zh P := hz.integrable (by norm_num)
  -- functions of ẑ are independent of functions of (X, Y, Z)
  have hmA : Measurable fun p : ℝ × ℝ × ℝ => (p.1 - p.2.1) ^ 2 := by fun_prop
  have hmAB : Measurable fun p : ℝ × ℝ × ℝ => (p.1 - p.2.1) * (p.2.1 - p.2.2) := by fun_prop
  have hI1 : IndepFun (fun ω => zh ω ^ 2) (fun ω => (X ω - Y ω) ^ 2) P :=
    hind.comp (φ := fun x : ℝ => x ^ 2) (by fun_prop) hmA
  have hI2 : IndepFun zh (fun ω => (X ω - Y ω) * (Y ω - Z ω)) P :=
    hind.comp (φ := id) measurable_id hmAB
  have j1 : Integrable (fun ω => zh ω ^ 2 * (X ω - Y ω) ^ 2) P := hI1.integrable_mul iz2 iA
  have j2 : Integrable (fun ω => zh ω * ((X ω - Y ω) * (Y ω - Z ω))) P := hI2.integrable_mul iz iAB
  have e1 : P[fun ω => zh ω ^ 2 * (X ω - Y ω) ^ 2] = P[fun ω => zh ω ^ 2] * a :=
    hI1.integral_fun_mul_eq_mul_integral iz2.aestronglyMeasurable iA.aestronglyMeasurable
  have e2 : P[fun ω => zh ω * ((X ω - Y ω) * (Y ω - Z ω))] = P[zh] * b :=
    hI2.integral_fun_mul_eq_mul_integral iz.aestronglyMeasurable iAB.aestronglyMeasurable
  have lhs : (fun ω => (zh ω * X ω + (1 - zh ω) * Y ω - Z ω) ^ 2)
      = fun ω => zh ω ^ 2 * (X ω - Y ω) ^ 2 + 2 * (zh ω * ((X ω - Y ω) * (Y ω - Z ω)))
        + (Y ω - Z ω) ^ 2 := funext fun ω => by ring
  have rhs : (fun ω => m.errVar (zh ω))
      = fun ω => a * zh ω ^ 2 + 2 * b * zh ω + c := funext fun ω => by
    rw [m.errVar_eq_quad hX hY hZ hXm hYm hZm h1 h2 h3 h4 h5 h6]; ring
  rw [lhs, rhs, integral_add (j1.fun_add (j2.const_mul 2)) iB, integral_add j1 (j2.const_mul 2),
    integral_const_mul, e1, e2,
    integral_add ((iz2.const_mul a).fun_add (iz.const_mul (2 * b))) (integrable_const c),
    integral_add (iz2.const_mul a) (iz.const_mul (2 * b)), integral_const_mul,
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Clipping a held-out `ẑ` never hurts when the best `z` is in `[0, 1]`** (G3b). With `ẑ`
independent of the data as in `integral_sq_blend_indep`, `E[(c X + (1 − c)Y − Z)²]
≤ E[(ẑX + (1 − ẑ)Y − Z)²]` for the clipped `c = clipZ ẑ`, whatever the distribution of `ẑ`. -/
theorem integral_sq_blend_clip_le (m : BlendMoments) {X Y Z zh : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) (hz : MemLp zh 2 P) {μ : ℝ} (hXm : P[X] = μ)
    (hYm : P[Y] = μ) (hZm : P[Z] = μ)
    (h1 : Var[X; P] = m.varCohort) (h2 : Var[Y; P] = m.varPortfolio)
    (h3 : Var[Z; P] = m.varTarget) (h4 : cov[X, Y; P] = m.covEst)
    (h5 : cov[X, Z; P] = m.covCohortTarget) (h6 : cov[Y, Z; P] = m.covPortfolioTarget)
    (hind : IndepFun zh (fun ω => (X ω, Y ω, Z ω)) P)
    (hg : 0 < m.gap) (h0 : 0 ≤ m.bestZ) (h1' : m.bestZ ≤ 1) :
    P[fun ω => (clipZ (zh ω) * X ω + (1 - clipZ (zh ω)) * Y ω - Z ω) ^ 2]
      ≤ P[fun ω => (zh ω * X ω + (1 - zh ω) * Y ω - Z ω) ^ 2] := by
  have hmc : Measurable clipZ := by unfold clipZ; fun_prop
  have hzc : MemLp (fun ω => clipZ (zh ω)) 2 P := by
    refine MemLp.of_bound (hmc.comp_aemeasurable hz.aemeasurable).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    have := clipZ_mem (zh ω)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hindc : IndepFun (fun ω => clipZ (zh ω)) (fun ω => (X ω, Y ω, Z ω)) P :=
    hind.comp (φ := clipZ) (ψ := id) hmc measurable_id
  rw [m.integral_sq_blend_indep hX hY hZ hzc hXm hYm hZm h1 h2 h3 h4 h5 h6 hindc,
    m.integral_sq_blend_indep hX hY hZ hz hXm hYm hZm h1 h2 h3 h4 h5 h6 hind]
  have hq : ∀ w : Ω → ℝ, MemLp w 2 P → Integrable (fun ω => m.errVar (w ω)) P := fun w hw => by
    rw [funext fun ω => m.errVar_eq_quad hX hY hZ hXm hYm hZm h1 h2 h3 h4 h5 h6 (w ω)]
    exact ((hw.integrable_sq.mul_const _).fun_add
      (((hw.integrable (by norm_num)).const_mul 2).mul_const _)).fun_add (integrable_const _)
  exact integral_mono (hq _ hzc) (hq _ hz) fun ω => m.errVar_clipZ_le hg h0 h1' (zh ω)

/-- **The condition is sharp**: clipping lowers (or keeps) the error for every `ẑ` independent of the
data exactly when the best `z` is in `[0, 1]`. A constant `ẑ` is independent of everything, so the
fixed-`z` condition (`errVar_clipZ_le_iff`) is necessary. -/
theorem integral_sq_blend_clip_le_iff (m : BlendMoments) {X Y Z : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) {μ : ℝ} (hXm : P[X] = μ)
    (hYm : P[Y] = μ) (hZm : P[Z] = μ)
    (h1 : Var[X; P] = m.varCohort) (h2 : Var[Y; P] = m.varPortfolio)
    (h3 : Var[Z; P] = m.varTarget) (h4 : cov[X, Y; P] = m.covEst)
    (h5 : cov[X, Z; P] = m.covCohortTarget) (h6 : cov[Y, Z; P] = m.covPortfolioTarget)
    (hg : 0 < m.gap) :
    (∀ zh : Ω → ℝ, MemLp zh 2 P → IndepFun zh (fun ω => (X ω, Y ω, Z ω)) P →
      P[fun ω => (clipZ (zh ω) * X ω + (1 - clipZ (zh ω)) * Y ω - Z ω) ^ 2]
        ≤ P[fun ω => (zh ω * X ω + (1 - zh ω) * Y ω - Z ω) ^ 2])
      ↔ 0 ≤ m.bestZ ∧ m.bestZ ≤ 1 := by
  refine ⟨fun h => (m.errVar_clipZ_le_iff hg).mp fun z => ?_, fun hb zh hz hind =>
    m.integral_sq_blend_clip_le hX hY hZ hz hXm hYm hZm h1 h2 h3 h4 h5 h6 hind hg hb.1 hb.2⟩
  have hc := h (fun _ => z) (memLp_const z) (indepFun_const_left z _)
  rwa [m.integral_sq_blend_sub hX hY hZ hXm hYm hZm h1 h2 h3 h4 h5 h6,
    m.integral_sq_blend_sub hX hY hZ hXm hYm hZm h1 h2 h3 h4 h5 h6] at hc

end BlendMoments

end Credibility
