import Credibility.BlupMoments

/-!
# Under normal noise the best linear predictor is the conditional expectation (distribution layer)

**Optional distribution layer** (owner, 2026-11-15): this file assumes *normal noise* (the data
and the target jointly Gaussian), so nothing in the core depends on it.

With the mean **known** (`β` given), the best linear predictor of `Y` from the cells `x` is
`E Y + ℓᵀK⁻¹(x − E x)` (`Target.knownMeanPred`). Its error `R = Y − ℓᵀK⁻¹x + const` is
uncorrelated with every cell: `cov(R, xⱼ) = ℓⱼ − (KK⁻¹ℓ)ⱼ = 0`. Jointly normal and uncorrelated
means independent (`HasGaussianLaw.indepFun_of_covariance_eval`), so under normal noise

* `E[Y | x] = E Y + ℓᵀK⁻¹(x − E x)` (`condExp_eq_knownMeanPred_of_normal`), and
* this predictor has the smallest mean squared error among **all** measurable functions of the
  data, not only the linear ones (`knownMeanPred_mse_le_of_normal`).

Known mean only: with an unknown `β` (universal kriging, `Core.blup`) the BLUP has to estimate
`β` from the same data and is not `E[Y | x]`. Stat-Lean's Gaussian conditioning kernel was
checked and not ported (literature §10n); independence is all that is needed here.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core
namespace Target

variable {Ω : Type*} [MeasurableSpace Ω] {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n]
  {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  {P : Measure Ω} (T : Target K ℓ v X x₀ β P)

/-- The best linear predictor with known mean, `E Y + ℓᵀK⁻¹(x − E x)` (simple kriging). -/
noncomputable def knownMeanPred : Ω → ℝ :=
  fun ω => x₀ ⬝ᵥ β + (K⁻¹ *ᵥ ℓ) ⬝ᵥ ((fun i => T.x i ω) - X *ᵥ β)

/-- The known-mean predictor is `cᵀx` plus a constant, `c = K⁻¹ℓ`. -/
lemma knownMeanPred_eq (ω : Ω) :
    T.knownMeanPred ω
      = portLin T.x (K⁻¹ *ᵥ ℓ) ω + (x₀ ⬝ᵥ β - (K⁻¹ *ᵥ ℓ) ⬝ᵥ (X *ᵥ β)) := by
  rw [knownMeanPred, dotProduct_sub]
  simp only [portLin, dotProduct]
  ring

lemma memLp_knownMeanPred [IsFiniteMeasure P] : MemLp T.knownMeanPred 2 P := by
  have := (T.memLp_portLin (K⁻¹ *ᵥ ℓ)).add
    (memLp_const (x₀ ⬝ᵥ β - (K⁻¹ *ᵥ ℓ) ⬝ᵥ (X *ᵥ β)) : MemLp _ 2 P)
  convert this using 1
  funext ω
  exact T.knownMeanPred_eq ω

lemma measurable_knownMeanPred_fun :
    Measurable fun u : n → ℝ => x₀ ⬝ᵥ β + (K⁻¹ *ᵥ ℓ) ⬝ᵥ (u - X *ᵥ β) := by
  simp only [dotProduct, Pi.sub_apply]
  fun_prop

/-- The known-mean predictor is unbiased: `E[Y − Ŷ] = 0`. -/
lemma integral_sub_knownMeanPred [IsProbabilityMeasure P] :
    P[fun ω => T.Y ω - T.knownMeanPred ω] = 0 := by
  rw [integral_sub (T.Y_memLp.integrable one_le_two)
    (T.memLp_knownMeanPred.integrable one_le_two)]
  simp_rw [T.knownMeanPred_eq]
  rw [integral_add ((T.memLp_portLin _).integrable one_le_two) (integrable_const _),
    T.integral_portLin, integral_const, T.Y_mean, mulVec_transpose, ← dotProduct_mulVec]
  simp

/-- **Under normal noise the error of the known-mean predictor is independent of the data.** -/
theorem indepFun_knownMeanPred_of_normal [IsProbabilityMeasure P] (hK : K.PosDef)
    (hG : HasGaussianLaw (fun ω => ((fun i => T.x i ω), T.Y ω)) P) :
    IndepFun (fun ω => T.Y ω - T.knownMeanPred ω) (fun ω i => T.x i ω) P := by
  set c := K⁻¹ *ᵥ ℓ with hc_def
  have hu : IsUnit K.det := isUnit_iff_ne_zero.2 hK.det_pos.ne'
  have hc : K *ᵥ c = ℓ := by rw [hc_def, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  let R₀ : Ω → ℝ := fun ω => T.Y ω - portLin T.x c ω
  -- the error is uncorrelated with every cell
  have hcov : ∀ j, cov[R₀, T.x j; P] = 0 := by
    intro j
    rw [covariance_fun_sub_left T.Y_memLp (T.memLp_portLin c) (T.x_memLp j),
      covariance_comm T.Y, T.cov_x_Y]
    have hpc : cov[portLin T.x c, T.x j; P] = (K *ᵥ c) j := by
      unfold portLin
      rw [covariance_fun_sum_left (fun i => (T.x_memLp i).const_mul (c i)) (T.x_memLp j)]
      simp only [covariance_const_mul_left, T.cov_x, mulVec, dotProduct]
      refine sum_congr rfl fun i _ => ?_
      have := hK.1.apply i j
      simp only [star_trivial] at this
      rw [← this]; ring
    rw [hpc, hc, sub_self]
  -- jointly normal and uncorrelated: independent
  let f : (n → ℝ) × ℝ →ₗ[ℝ] (Unit → ℝ) × (n → ℝ) :=
    { toFun := fun z => (fun _ => z.2 - c ⬝ᵥ z.1, z.1)
      map_add' := fun a b => by
        ext
        · simp [dotProduct_add]; ring
        · simp
      map_smul' := fun r a => by
        ext
        · simp [dotProduct_smul]; ring
        · simp }
  have hG' : HasGaussianLaw (fun ω => ((fun _ : Unit => R₀ ω), fun j => T.x j ω)) P := by
    have := hG.map_fun (LinearMap.toContinuousLinearMap f)
    convert this using 1
    funext ω
    simp [f, R₀, portLin, dotProduct]
  have hind := HasGaussianLaw.indepFun_of_covariance_eval hG' (fun _ j => hcov j)
  have hφ : Measurable fun r : Unit → ℝ => r () - (x₀ ⬝ᵥ β - c ⬝ᵥ (X *ᵥ β)) :=
    (measurable_pi_apply ()).sub_const _
  have hfun : (fun ω => T.Y ω - T.knownMeanPred ω)
      = (fun r : Unit → ℝ => r () - (x₀ ⬝ᵥ β - c ⬝ᵥ (X *ᵥ β))) ∘ fun ω _ => R₀ ω := by
    funext ω
    simp only [Function.comp_apply, R₀]
    rw [T.knownMeanPred_eq]
    ring
  rw [hfun]
  exact hind.comp hφ measurable_id

/-- **Under normal noise the best linear predictor is the conditional expectation**: with known
mean, `E[Y | x] = E Y + ℓᵀK⁻¹(x − E x)` almost surely. Not so with an unknown mean `β`
(universal kriging), where the BLUP estimates `β` from the data. -/
theorem condExp_eq_knownMeanPred_of_normal [IsProbabilityMeasure P] (hK : K.PosDef)
    (hG : HasGaussianLaw (fun ω => ((fun i => T.x i ω), T.Y ω)) P)
    (hx : ∀ i, Measurable (T.x i)) (hY : Measurable T.Y) :
    P[T.Y | MeasurableSpace.comap (fun ω i => T.x i ω) inferInstance] =ᵐ[P] T.knownMeanPred := by
  have hind := T.indepFun_knownMeanPred_of_normal hK hG
  have hpmeas := measurable_knownMeanPred_fun (x₀ := x₀) (β := β) (K := K) (ℓ := ℓ) (X := X)
  have hxv : Measurable fun ω (i : n) => T.x i ω := measurable_pi_iff.mpr hx
  have hle₂ := hxv.comap_le
  have hpm : StronglyMeasurable[MeasurableSpace.comap (fun ω i => T.x i ω) inferInstance]
      T.knownMeanPred :=
    (hpmeas.comp (comap_measurable _)).stronglyMeasurable
  have hpL := T.memLp_knownMeanPred
  have hRm : Measurable fun ω => T.Y ω - T.knownMeanPred ω :=
    hY.sub (hpmeas.comp hxv)
  have hRL : MemLp (fun ω => T.Y ω - T.knownMeanPred ω) 2 P := T.Y_memLp.sub hpL
  have hRc := condExp_indep_eq hRm.comap_le hle₂ (comap_measurable _).stronglyMeasurable
    ((IndepFun_iff_Indep _ _ _).1 hind)
  have hY_eq : T.Y = T.knownMeanPred + fun ω => T.Y ω - T.knownMeanPred ω := by
    funext ω; simp
  conv_lhs => rw [hY_eq]
  filter_upwards [condExp_add (hpL.integrable one_le_two) (hRL.integrable one_le_two)
    (MeasurableSpace.comap (fun ω i => T.x i ω) inferInstance), hRc] with ω h1 h2
  rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable hle₂ hpm (hpL.integrable one_le_two), h2,
    T.integral_sub_knownMeanPred, add_zero]

/-- **Under normal noise it is the best predictor of all**: no measurable function `g` of the
data has a smaller mean squared error than `E Y + ℓᵀK⁻¹(x − E x)`. Known mean only. -/
theorem knownMeanPred_mse_le_of_normal [IsProbabilityMeasure P] (hK : K.PosDef)
    (hG : HasGaussianLaw (fun ω => ((fun i => T.x i ω), T.Y ω)) P)
    (g : (n → ℝ) → ℝ) (hg : Measurable g) (hgL : MemLp (fun ω => g fun i => T.x i ω) 2 P) :
    P[fun ω => (T.knownMeanPred ω - T.Y ω) ^ 2]
      ≤ P[fun ω => (g (fun i => T.x i ω) - T.Y ω) ^ 2] := by
  have hind := T.indepFun_knownMeanPred_of_normal hK hG
  have hpmeas := measurable_knownMeanPred_fun (x₀ := x₀) (β := β) (K := K) (ℓ := ℓ) (X := X)
  have hpL := T.memLp_knownMeanPred
  set R : Ω → ℝ := fun ω => T.Y ω - T.knownMeanPred ω with hR
  set A : Ω → ℝ := fun ω => g (fun i => T.x i ω) - T.knownMeanPred ω with hA
  have hRL : MemLp R 2 P := T.Y_memLp.sub hpL
  have hAL : MemLp A 2 P := hgL.sub hpL
  -- the cross term factors and vanishes
  have hindA : IndepFun R A P := by
    exact hind.comp measurable_id (hg.sub hpmeas)
  have hRA : P[fun ω => R ω * A ω] = 0 := by
    rw [hindA.integral_fun_mul_eq_mul_integral hRL.aestronglyMeasurable hAL.aestronglyMeasurable,
      T.integral_sub_knownMeanPred, zero_mul]
  have e1 : (fun ω => (T.knownMeanPred ω - T.Y ω) ^ 2) = fun ω => R ω ^ 2 := by
    funext ω; simp only [hR]; ring
  have e2 : (fun ω => (g (fun i => T.x i ω) - T.Y ω) ^ 2)
      = fun ω => A ω ^ 2 + R ω ^ 2 - 2 * (R ω * A ω) := by
    funext ω; simp only [hR, hA]; ring
  have hRAi : Integrable (fun ω => R ω * A ω) P := hRL.integrable_mul hAL
  rw [e1, e2, integral_sub (f := fun ω => A ω ^ 2 + R ω ^ 2) (g := fun ω => 2 * (R ω * A ω))
      (hAL.integrable_sq.add hRL.integrable_sq) (hRAi.const_mul 2),
    integral_add (f := fun ω => A ω ^ 2) (g := fun ω => R ω ^ 2) hAL.integrable_sq
      hRL.integrable_sq, integral_const_mul, hRA, mul_zero, sub_zero]
  linarith [integral_nonneg (μ := P) fun ω => sq_nonneg (A ω)]

end Target
end Core
end Credibility
