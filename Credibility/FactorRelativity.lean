import Credibility.FactorMoments

/-!
# When does the factor cancel from relativities? (extension, `notes/card-data.md` Step 4)

Any linear statistic of the cells, or the error of a linear predictor (statistic minus a
linear target), is `Σₚ aₚXₚ` for coefficients `a` over all cells `J × T`, past and future
(`a = 0` on cells not observed or not in the target). Under the common factor model its
variance is the variance without the factor (`Shock`) plus one exact term:

`Var_Factor(Σ aX) = Var_Shock(Σ aX) + gᵀΓg`, `gₜ = Σⱼ λⱼ aⱼₜ` (`quadTab_eq`).

`g` is the loading-weighted month profile of the statistic (`profile`). So:

* the factor term is `≥ 0`: a fit that ignores the factor understates the error
  (`quadTab_shock_le`), and it vanishes for a factor with `Γ ≻ 0` iff `g = 0`
  (`quadTab_eq_shock_iff`);
* **equal loadings** and a statistic that is a contrast within every month (`Σⱼ aⱼₜ = 0`)
  give `g = 0` (`profile_eq_zero_of_equal`);
* **relativities** `z(μ̂ⱼ - Σᵢ bᵢμ̂ᵢ)` of cohort estimates `μ̂ᵢ = Σₜ αᵢₜXᵢₜ`, `Σ bᵢ = 1`:
  `gₜ = z(λⱼαⱼₜ - Σᵢ bᵢλᵢαᵢₜ)` (`profile_relCoef`). With equal loadings **and the same
  weight profile over months** `αᵢₜ = αₜ` the factor cancels (`relCoef_factor_free`): the
  relativity, its variance and its true MSE are those of the factor-free model
  (`Cells.variance_relCoef`). Exposure weights have the same profile when volumes are
  proportional (`Shock.expo_eq_of_proportional`).

Being observed in the same months is not enough (Finding 31): the weights must have the same
profile. Counterexamples with `Γ` an AR(1), `Γₜₛ = γφ^|t-s|`, two months, equal loadings:
a cohort entering in the second month (`extra_entry`) and two cohorts in the same months with
weights `(3/4, 1/4)` and `(1/4, 3/4)` (`extra_profile`) both leave `γ(1 - φ)/2`; it vanishes
only for `φ = 1`, a factor constant over the window (a pure level shift). Unequal loadings
`λ = (1, 2)` leave `Γₜₜ` in one month (`extra_loadings`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Factor

variable {J T : Type*} [Fintype J] [Fintype T] [DecidableEq J] [DecidableEq T]
variable (M : Factor J T)

/-- The variance `Σₚ Σ_q aₚa_q tab(p, q)` of the statistic `Σₚ aₚXₚ` for a covariance table
`tab` over all cells `J × T`. -/
def quadTab (tab : J → J → T → T → ℝ) (a : J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, a p * a q * tab p.1 q.1 p.2 q.2

/-- The loading-weighted month profile `gₜ = Σⱼ λⱼaⱼₜ` of the statistic `Σₚ aₚXₚ`: how much
of the factor in month `t` it picks up. -/
def profile (a : J × T → ℝ) : T → ℝ := fun t => ∑ j, M.load j * a (j, t)

/-- **The exact factor term.** For any coefficients `a` over all cells,
`Var_Factor(Σ aX) = Var_Shock(Σ aX) + gᵀΓg` with `g` the loading-weighted month profile. -/
theorem quadTab_eq (a : J × T → ℝ) :
    quadTab M.obsCov a = quadTab M.toShock.obsCov a + M.profile a ⬝ᵥ (M.Γ *ᵥ M.profile a) := by
  simp only [quadTab, obsCov, mul_add, sum_add_distrib]
  rw [add_comm]
  congr 1
  simp only [profile, dotProduct, mulVec, Fintype.sum_prod_type, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun s _ => ?_
  ring

/-- **Ignoring the factor understates the error**: the factor term is `≥ 0`. -/
theorem quadTab_shock_le (a : J × T → ℝ) :
    quadTab M.toShock.obsCov a ≤ quadTab M.obsCov a := by
  rw [quadTab_eq]
  have := M.Γ_posSemidef.dotProduct_mulVec_nonneg (M.profile a)
  simp only [star_trivial] at this
  linarith

/-- **The factor cancels iff the profile is zero** (for a factor with `Γ ≻ 0`, e.g. an AR(1)
with `|φ| < 1`, `γ > 0`). -/
theorem quadTab_eq_shock_iff (hΓ : M.Γ.PosDef) (a : J × T → ℝ) :
    quadTab M.obsCov a = quadTab M.toShock.obsCov a ↔ M.profile a = 0 := by
  rw [quadTab_eq, add_eq_left]
  constructor
  · intro h
    by_contra hne
    have := hΓ.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  · intro h; simp [h]

omit [Fintype T] [DecidableEq J] [DecidableEq T] in
/-- **Equal loadings, a contrast within every month**: if `λⱼ = λ` for all cohorts and
`Σⱼ aⱼₜ = 0` for every month, the profile is zero. -/
theorem profile_eq_zero_of_equal {l : ℝ} (hl : ∀ j, M.load j = l) {a : J × T → ℝ}
    (ha : ∀ t, ∑ j, a (j, t) = 0) : M.profile a = 0 := by
  ext t
  simp [profile, hl, ← mul_sum, ha]

omit [Fintype T] [DecidableEq J] [DecidableEq T] in
/-- The profile is linear: a predictor's error `Σ aX - Σ a'X` has profile `g(a) - g(a')`. -/
theorem profile_sub (a a' : J × T → ℝ) : M.profile (a - a') = M.profile a - M.profile a' := by
  ext t
  simp [profile, mul_sub, sum_sub_distrib]

/-! ### Relativities of cohort estimates -/

/-- The coefficients of the relativity `z(μ̂ⱼ - Σᵢ bᵢμ̂ᵢ)` with cohort estimates
`μ̂ᵢ = Σₜ αᵢₜXᵢₜ` (`αᵢₜ = 0` where cohort `i` is not observed) and portfolio weights `b`. -/
def relCoef (α : J → T → ℝ) (b : J → ℝ) (j : J) (z : ℝ) : J × T → ℝ :=
  fun p => z * ((if p.1 = j then 1 else 0) - b p.1) * α p.1 p.2

omit [Fintype T] [DecidableEq T] in
/-- The profile of a relativity: `gₜ = z(λⱼαⱼₜ - Σᵢ bᵢλᵢαᵢₜ)`. -/
theorem profile_relCoef (α : J → T → ℝ) (b : J → ℝ) (j : J) (z : ℝ) (t : T) :
    M.profile (relCoef α b j z) t = z * (M.load j * α j t - ∑ i, b i * M.load i * α i t) := by
  simp only [profile, relCoef, mul_sub, sub_mul, mul_sum, sum_sub_distrib, ite_mul,
    zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  congr 1
  · ring
  · exact sum_congr rfl fun i _ => by ring

/-- **The exact extra error of a relativity**:
`Var_Factor = Var_Shock + z²gᵀΓg`, `gₜ = λⱼαⱼₜ - Σᵢ bᵢλᵢαᵢₜ`. -/
theorem quadTab_relCoef (α : J → T → ℝ) (b : J → ℝ) (j : J) (z : ℝ) :
    quadTab M.obsCov (relCoef α b j z)
      = quadTab M.toShock.obsCov (relCoef α b j z)
        + z ^ 2 * ((fun t => M.load j * α j t - ∑ i, b i * M.load i * α i t)
          ⬝ᵥ (M.Γ *ᵥ fun t => M.load j * α j t - ∑ i, b i * M.load i * α i t)) := by
  rw [quadTab_eq]
  have hg : M.profile (relCoef α b j z)
      = z • fun t => M.load j * α j t - ∑ i, b i * M.load i * α i t := by
    ext t; rw [profile_relCoef]; rfl
  rw [hg, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    sq]

omit [Fintype T] [DecidableEq T] in
/-- **Equal loadings and the same weight profile: the factor cancels from relativities.** If
`λᵢ = λ` and `αᵢₜ = αₜ` for every cohort, and `Σ bᵢ = 1`, the relativity picks up no factor. -/
theorem relCoef_factor_free {l : ℝ} (hl : ∀ i, M.load i = l) {α₀ : T → ℝ} {α : J → T → ℝ}
    (hα : ∀ i t, α i t = α₀ t) {b : J → ℝ} (hb : ∑ i, b i = 1) (j : J) (z : ℝ) :
    M.profile (relCoef α b j z) = 0 := by
  ext t
  rw [profile_relCoef]
  simp only [hl, hα, Pi.zero_apply]
  rw [← sum_mul, ← sum_mul, hb]
  ring

/-- **Relativities need no factor model**: under equal loadings and the same weight profile,
the relativity has the variance of the factor-free model, whatever `Γ`. -/
theorem quadTab_relCoef_eq_shock {l : ℝ} (hl : ∀ i, M.load i = l) {α₀ : T → ℝ}
    {α : J → T → ℝ} (hα : ∀ i t, α i t = α₀ t) {b : J → ℝ} (hb : ∑ i, b i = 1) (j : J)
    (z : ℝ) :
    quadTab M.obsCov (relCoef α b j z) = quadTab M.toShock.obsCov (relCoef α b j z) := by
  rw [quadTab_eq, M.relCoef_factor_free hl hα hb j z]
  simp

/-! ### Counterexamples (Finding 31) -/

section Counterexamples

/-- The relativity of cohort `0` against cohort `1`, `μ̂₀ - μ̂₁`: `b = (0, 1)`, `z = 1`. -/
def diffCoef {T : Type*} (α : Fin 2 → T → ℝ) : Fin 2 × T → ℝ := relCoef α ![0, 1] 0 1

/-- **Unequal loadings**: `λ = (1, 2)`, one month, `μ̂ⱼ = Xⱼ`. The difference keeps the factor
variance `Γ₀₀`. -/
theorem extra_loadings (M : Factor (Fin 2) (Fin 1)) (hl : M.load = ![1, 2]) :
    quadTab M.obsCov (diffCoef fun _ _ => 1)
      = quadTab M.toShock.obsCov (diffCoef fun _ _ => 1) + M.Γ 0 0 := by
  rw [quadTab_eq]
  have : M.profile (diffCoef fun _ _ => 1) = fun _ => -1 := by
    ext t; simp [profile_relCoef, diffCoef, hl, Fin.sum_univ_two]; norm_num
  rw [this]
  simp [dotProduct, mulVec]

/-- The AR(1) extra term of a two-month profile `(1/2, -1/2)`: `γ(1 - φ)/2`. -/
lemma ar1_half_profile (γ φ : ℝ) :
    (fun t : Fin 2 => if t = 0 then (1 / 2 : ℝ) else -(1 / 2))
      ⬝ᵥ (ar1 2 γ φ *ᵥ fun t : Fin 2 => if t = 0 then (1 / 2 : ℝ) else -(1 / 2))
        = γ * (1 - φ) / 2 := by
  simp [dotProduct, mulVec, ar1, Fin.sum_univ_two]
  ring

/-- **A cohort entering mid-window**: equal loadings `1`, AR(1) factor over two months,
cohort `0` observed in both months (weights `(1/2, 1/2)`), cohort `1` only in the second
(weights `(0, 1)`). The relativity `μ̂₀ - μ̂₁` keeps `γ(1 - φ)/2`, positive unless `φ = 1`. -/
theorem extra_entry (M : Factor (Fin 2) (Fin 2)) (hl : ∀ j, M.load j = 1) {γ φ : ℝ}
    (hΓ : M.Γ = ar1 2 γ φ) :
    quadTab M.obsCov (diffCoef ![![1 / 2, 1 / 2], ![0, 1]])
      = quadTab M.toShock.obsCov (diffCoef ![![1 / 2, 1 / 2], ![0, 1]]) + γ * (1 - φ) / 2 := by
  rw [quadTab_eq, hΓ, ← ar1_half_profile γ φ]
  congr 2 <;>
  · ext t; fin_cases t <;> simp [profile_relCoef, diffCoef, hl, Fin.sum_univ_two] <;> norm_num

/-- **Same months, different weight profiles**: equal loadings `1`, AR(1) factor over two
months, both cohorts observed in both months, with weights `(3/4, 1/4)` and `(1/4, 3/4)`
(e.g. exposure weights of a shrinking and a growing card). The relativity keeps
`γ(1 - φ)/2`. -/
theorem extra_profile (M : Factor (Fin 2) (Fin 2)) (hl : ∀ j, M.load j = 1) {γ φ : ℝ}
    (hΓ : M.Γ = ar1 2 γ φ) :
    quadTab M.obsCov (diffCoef ![![3 / 4, 1 / 4], ![1 / 4, 3 / 4]])
      = quadTab M.toShock.obsCov (diffCoef ![![3 / 4, 1 / 4], ![1 / 4, 3 / 4]])
        + γ * (1 - φ) / 2 := by
  rw [quadTab_eq, hΓ, ← ar1_half_profile γ φ]
  congr 2 <;>
  · ext t; fin_cases t <;> simp [profile_relCoef, diffCoef, hl, Fin.sum_univ_two] <;> norm_num

end Counterexamples

/-! ### The moment layer -/

namespace Cells

variable {Ω : Type*} [MeasurableSpace Ω] {q : Type*} [Fintype q] {tab : J → J → T → T → ℝ}
  {D : Matrix (J × T) q ℝ} {β : q → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq J] [DecidableEq T] in
/-- **`quadTab` is the true variance**: for any random cells with covariance table `tab`,
`Var(Σₚ aₚXₚ) = Σₚ Σ_q aₚa_q tab(p, q)`. -/
theorem variance_lin (C : Cells tab D β P) (a : J × T → ℝ) :
    Var[Core.portLin C.X a; P] = quadTab tab a := by
  have hm : MemLp (Core.portLin C.X a) 2 P :=
    memLp_finsetSum _ fun p _ => (C.memLp p).const_mul (a p)
  rw [← covariance_self hm.aestronglyMeasurable.aemeasurable]
  unfold Core.portLin
  rw [covariance_fun_sum_fun_sum (fun p => (C.memLp p).const_mul (a p))
    (fun p => (C.memLp p).const_mul (a p))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, C.cov, quadTab]
  exact sum_congr rfl fun p _ => sum_congr rfl fun r _ => by ring

/-- **The true variance of any statistic under the factor model**: that of the factor-free
model plus `gᵀΓg`, for every distribution with these moments. -/
theorem variance_lin_eq (C : Cells M.obsCov D β P) (a : J × T → ℝ) :
    Var[Core.portLin C.X a; P]
      = quadTab M.toShock.obsCov a + M.profile a ⬝ᵥ (M.Γ *ᵥ M.profile a) := by
  rw [variance_lin, quadTab_eq]

/-- **Relativities in true variance**: with equal loadings and the same weight profile, the
relativity `z(μ̂ⱼ - Σᵢ bᵢμ̂ᵢ)` has the variance of the factor-free model, for every
distribution with these moments and every `Γ`. -/
theorem variance_relCoef (C : Cells M.obsCov D β P) {l : ℝ} (hl : ∀ i, M.load i = l)
    {α₀ : T → ℝ} {α : J → T → ℝ} (hα : ∀ i t, α i t = α₀ t) {b : J → ℝ} (hb : ∑ i, b i = 1)
    (j : J) (z : ℝ) :
    Var[Core.portLin C.X (relCoef α b j z); P] = quadTab M.toShock.obsCov (relCoef α b j z) := by
  rw [variance_lin, M.quadTab_relCoef_eq_shock hl hα hb]

end Cells
end Factor

/-! ### Exposure weights with proportional volumes -/

namespace Shock

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T] (M : Shock J T)

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- **Proportional volumes give the same exposure profile**: if `wᵢₜ = k wⱼₜ` for all months,
`k > 0`, then `wᵢₜ/Σₛwᵢₛ = wⱼₜ/Σₛwⱼₛ`. -/
theorem expo_eq_of_proportional {i j : J} {k : ℝ} (hk : 0 < k) (hw : ∀ t, M.w i t = k * M.w j t)
    (t : T) : M.expo i t = M.expo j t := by
  simp only [expo, wtot, hw, ← mul_sum]
  rw [mul_div_mul_left _ _ hk.ne']

end Shock
end Credibility
