import Credibility.Expectation
import Credibility.FactorMoments

/-!
# Estimating the common factor model, part 1: identification and the shock fit (extension, `notes/card-data.md` Step 5)

What the table `Factor.obsCov` (with per-cohort dynamics `obsCovG`) lets the data identify, and
the first unbiased estimator (`studies/literature.md` §10h). Distribution-free throughout.

* **(I1) Scale** (`obsCov_rescale`, `blup_rescale`): `(λ, Γ) ↦ (aλ, a⁻²Γ)`, `a ≠ 0` (a sign
  flip included), leaves the table, `K`, `ℓ`, `v` and the predictor unchanged. So fixing the
  scale (exposure-weighted mean loading `1`) is a presentation choice.
* **(I2) Lag 0** (`obsCov_eq_of_lag0`, `blup_eq_of_lag0`): with a constant factor variance
  `Γₜₜ = γ`, the table, hence `K`, `ℓ`, `v` and the predictor, depend on `C` and `γλλᵀ` only
  through `C + γλλᵀ` (plus the lagged factor part `λλᵀΓₜₛ`, `t ≠ s`). The split is not needed
  for prediction.
* **(I3) Lag ≥ 1** (`obsCovG_of_ne`, `factor_eq_of_obsCovG_eq`): for two different cohorts in
  two different months the table is `λᵢλⱼΓₜₛ`, free of `C`, `s²`, `τ²` and the per-cohort
  dynamics `G`. So tables that agree there agree on the lagged factor part: a common factor
  and per-cohort dynamics are distinguishable.
* **The year-on-year lagged cross-product** (`yoy_unbiased`, `yoy_unbiased_factor`): with
  means `Dβ` for any design whose rows agree for the same cohort in two months (a cohort-specific
  calendar-month season, `cohortSeason`), `(Xᵢₜ - Xᵢᵤ)(Xⱼₛ - Xⱼᵥ)` with `mon t = mon u` is
  unbiased for every `β` (`Model.UnbiasedMean`); for `i ≠ j` and months distinct across the
  two cohorts its expectation is `λᵢλⱼ(Γₜₛ - Γₜᵥ - Γᵤₛ + Γᵤᵥ)`. With `u = t - 12`,
  `s = t + h`, `v = s - 12` and a stationary `Γ` this is `λᵢλⱼ(2Γ(h) - Γ(h-12) - Γ(h+12))`
  for `h ≥ 1`, `h ≠ 12`. Pooled over months: `yoyPooled_unbiased`; the true expectation for
  random cells (`Cells.integral_yoy`).
* **(I4) Three cohorts** (`load_sq_of_three`): `Σ(i,j)Σ(i,k)/Σ(j,k) = λᵢ²Γₜₛ`; with two cohorts a
  loading trades against per-cohort dynamics (`obsCovG_eq_of_trade`, `two_cohorts_not_identified`).
* **(I5) AR(1)** (`ar1_identified`): `Σ₂ = φΣ₁` across cohorts, so `φ`, `γλᵢλⱼ` and `Cᵢⱼ` are read off
  when `φ ≠ 0`; `φ = 0` is the shock `C + γλλᵀ` (`ar1_zero_eq_shock`).
* **The shock fit under a factor** (Finding 26, `res_unbiased`, `crossHat_factor_unbiased`,
  `crossHat_ar1_two`): within-card residuals keep `λᵢλⱼ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)`; with two months
  and AR(1), `Shock.crossHat` estimates `C + (1 - φ)γλλᵀ`, neither `C` nor `C + γλλᵀ`.
* **The between-cohort spread under a factor** (`between_factor_unbiased`): it gains
  `ΣⱼxⱼvⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢxᵢλᵢaᵢ`, and `Σₖxₖ(1 - xₖ)aₖᵀGₖaₖ`; with equal weights the factor
  term is `Σⱼxⱼ(λⱼ - λ̄)²·αᵀΓα` (`between_factor_equal_weights`), so `Shock.tauHat` reads loading
  dispersion and per-cohort dynamics as heterogeneity.
* **The diagonal and `τ̂²` under a factor** (`CdiagHat_factor_unbiased`, `s2Hat_factor_unbiased`,
  `errCovHat_factor_unbiased`, `tauHat_factor_unbiased`): each weighted sum of squared
  residuals gains `Fⱼ(u) = Σₜuⱼₜ(λⱼ²(eₜ - aⱼ)ᵀΓ(eₜ - aⱼ) + (eₜ - aⱼ)ᵀGⱼ(eₜ - aⱼ))`; Cramer's rule
  passes it on to `Ĉⱼⱼ` and `ŝⱼ²`, and `τ̂²` collects the spread's extra term minus the
  plugged-in biases of `Σ̂`. With independent months `Γ = γI`: `Ĉⱼⱼ` reads `Cⱼⱼ + γλⱼ²` and `ŝⱼ²`
  stays unbiased (`CdiagHat_s2Hat_indep`).
* Henderson III and MINQUE given the shape, and when their systems are nonsingular, are in
  `FactorHenderson`.
-/

open Finset Matrix

namespace Credibility
namespace Factor

variable {J T n : Type*} [DecidableEq J] [DecidableEq T]

/-! ### Equal tables give the same predictor -/

section Congr

variable {M M' : Factor J T} (h : ∀ i j t s, M.obsCov i j t s = M'.obsCov i j t s)
include h

/-- Equal tables give the same `K`. -/
theorem K_congr (c : n → J × T) : M.K c = M'.K c := by
  ext p q; simp [K, h]

/-- Equal tables give the same `ℓ`. -/
theorem ell_congr [Fintype T] (c : n → J × T) (j₀ : J) (b : T → ℝ) :
    M.ell c j₀ b = M'.ell c j₀ b := by
  funext p; simp [ell, h]

/-- Equal tables give the same `v`. -/
theorem var_congr [Fintype T] (j₀ : J) (b : T → ℝ) : M.var j₀ b = M'.var j₀ b := by
  simp [var, h]

/-- **Equal tables give the same predictor and the same error for every weight vector `d`.** -/
theorem blup_congr [Fintype T] [Fintype n] [DecidableEq n] {q : Type*} [Fintype q]
    [DecidableEq q] (c : n → J × T) (X : Matrix n q ℝ) (j₀ : J) (b : T → ℝ) (x₀ : q → ℝ) :
    Core.blup (M.K c) X (M.ell c j₀ b) x₀ = Core.blup (M'.K c) X (M'.ell c j₀ b) x₀ ∧
      ∀ d, Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) d
        = Core.predMse (M'.K c) (M'.ell c j₀ b) (M'.var j₀ b) d := by
  rw [K_congr h, ell_congr h, var_congr h]
  exact ⟨rfl, fun _ => rfl⟩

end Congr

/-! ### (I1) The scale shared by loadings and factor -/

variable (M : Factor J T)

/-- The same model with loadings `aλ` and factor autocovariance `a⁻²Γ`. -/
noncomputable def rescale (a : ℝ) : Factor J T :=
  { M with
    load := fun j => a * M.load j
    Γ := (a ^ 2)⁻¹ • M.Γ
    Γ_posSemidef := M.Γ_posSemidef.smul (by positivity) }

/-- **(I1) Scale invariance**: `(λ, Γ) ↦ (aλ, a⁻²Γ)`, `a ≠ 0`, leaves the table unchanged. -/
theorem obsCov_rescale {a : ℝ} (ha : a ≠ 0) (i j : J) (t s : T) :
    (M.rescale a).obsCov i j t s = M.obsCov i j t s := by
  simp only [obsCov, rescale, toShock, Matrix.smul_apply, smul_eq_mul]
  congr 1
  field_simp

/-- With per-cohort dynamics too. -/
theorem obsCovG_rescale {a : ℝ} (ha : a ≠ 0) (G : J → Matrix T T ℝ) (i j : J) (t s : T) :
    (M.rescale a).obsCovG G i j t s = M.obsCovG G i j t s := by
  simp only [obsCovG, M.obsCov_rescale ha]

/-- **(I1) for the predictor**: rescaling gives the same `K`, `ℓ`, `v`, so the same best linear
unbiased predictor and the same error for every weight vector. -/
theorem blup_rescale [Fintype T] [Fintype n] [DecidableEq n] {q : Type*} [Fintype q]
    [DecidableEq q] {a : ℝ} (ha : a ≠ 0) (c : n → J × T) (X : Matrix n q ℝ) (j₀ : J)
    (b : T → ℝ) (x₀ : q → ℝ) :
    Core.blup ((M.rescale a).K c) X ((M.rescale a).ell c j₀ b) x₀
        = Core.blup (M.K c) X (M.ell c j₀ b) x₀ ∧
      ∀ d, Core.predMse ((M.rescale a).K c) ((M.rescale a).ell c j₀ b) ((M.rescale a).var j₀ b) d
        = Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) d :=
  blup_congr (M.obsCov_rescale ha) c X j₀ b x₀

/-! ### (I2) Lag 0 sees only `C + γλλᵀ` -/

/-- **(I2) Lag-0 sufficiency**: two models with the same `τ²`, `s²`, volumes and lagged factor
part `λᵢλⱼΓₜₛ` (`t ≠ s`), constant factor variances `Γₜₜ = γ`, `Γ'ₜₜ = γ'`, and equal
`C + γλλᵀ = C' + γ'λ'λ'ᵀ` have the same table. -/
theorem obsCov_eq_of_lag0 {M' : Factor J T} {γ γ' : ℝ} (hτ : M'.τ2 = M.τ2) (hs : M'.s2 = M.s2)
    (hw : M'.w = M.w) (hΓ : ∀ t, M.Γ t t = γ) (hΓ' : ∀ t, M'.Γ t t = γ')
    (hsum : ∀ i j, M.C i j + γ * (M.load i * M.load j)
      = M'.C i j + γ' * (M'.load i * M'.load j))
    (hlag : ∀ i j t s, t ≠ s →
      M.load i * M.load j * M.Γ t s = M'.load i * M'.load j * M'.Γ t s)
    (i j : J) (t s : T) : M.obsCov i j t s = M'.obsCov i j t s := by
  simp only [obsCov, Shock.obsCov, toShock, hτ, hs, hw]
  by_cases hts : t = s
  · subst hts
    simp only [hΓ, hΓ', ite_true]
    have := hsum i j
    split_ifs <;> linarith
  · rw [hlag i j t s hts]
    simp [hts]

/-- **(I2) for the predictor**: the same `K`, `ℓ`, `v`, so the same predictor and errors;
trading `C` against `γλλᵀ` at lag 0 does not change the prediction. -/
theorem blup_eq_of_lag0 [Fintype T] [Fintype n] [DecidableEq n] {q : Type*} [Fintype q]
    [DecidableEq q] {M' : Factor J T} {γ γ' : ℝ} (hτ : M'.τ2 = M.τ2) (hs : M'.s2 = M.s2)
    (hw : M'.w = M.w) (hΓ : ∀ t, M.Γ t t = γ) (hΓ' : ∀ t, M'.Γ t t = γ')
    (hsum : ∀ i j, M.C i j + γ * (M.load i * M.load j)
      = M'.C i j + γ' * (M'.load i * M'.load j))
    (hlag : ∀ i j t s, t ≠ s →
      M.load i * M.load j * M.Γ t s = M'.load i * M'.load j * M'.Γ t s)
    (c : n → J × T) (X : Matrix n q ℝ) (j₀ : J) (b : T → ℝ) (x₀ : q → ℝ) :
    Core.blup (M.K c) X (M.ell c j₀ b) x₀ = Core.blup (M'.K c) X (M'.ell c j₀ b) x₀ ∧
      ∀ d, Core.predMse (M.K c) (M.ell c j₀ b) (M.var j₀ b) d
        = Core.predMse (M'.K c) (M'.ell c j₀ b) (M'.var j₀ b) d :=
  blup_congr (M.obsCov_eq_of_lag0 hτ hs hw hΓ hΓ' hsum hlag) c X j₀ b x₀

/-! ### (I3) Lags `≥ 1` across cohorts see only the factor -/

section Lagged

variable (G : J → Matrix T T ℝ)

/-- **(I3) Separation**: two different cohorts in two different months have covariance
`λᵢλⱼΓₜₛ`: no `C`, no `s²/w`, no `τ²`, no per-cohort dynamics `G`. -/
theorem obsCovG_of_ne {i j : J} {t s : T} (hij : i ≠ j) (hts : t ≠ s) :
    M.obsCovG G i j t s = M.load i * M.load j * M.Γ t s := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hij, hts]

/-- The same cohort in two different months: `λᵢ²Γₜₛ + τ² + (Gᵢ)ₜₛ`; here the factor is
confounded with `τ²` and `G`. -/
theorem obsCovG_self_of_ne (i : J) {t s : T} (hts : t ≠ s) :
    M.obsCovG G i i t s = M.load i ^ 2 * M.Γ t s + M.τ2 + G i t s := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hts, sq]

/-- **(I3) Distinguishable**: tables that agree (whatever their `C`, `s²`, `τ²`, `G`) have the
same lagged cross-card factor part. So `λλᵀΓ ≠ λ'λ'ᵀΓ'` there means different tables: a common
factor and per-cohort dynamics only are told apart by the lagged cross-moments. -/
theorem factor_eq_of_obsCovG_eq {M' : Factor J T} {G' : J → Matrix T T ℝ}
    (h : ∀ i j t s, M.obsCovG G i j t s = M'.obsCovG G' i j t s) {i j : J} {t s : T}
    (hij : i ≠ j) (hts : t ≠ s) :
    M.load i * M.load j * M.Γ t s = M'.load i * M'.load j * M'.Γ t s := by
  rw [← M.obsCovG_of_ne G hij hts, ← M'.obsCovG_of_ne G' hij hts, h]

/-! ### The year-on-year lagged cross-product -/

/-- The table `obsCovG` indexed by cells `p = (j, t)`. -/
noncomputable def covG (p q : J × T) : ℝ := M.obsCovG G p.1 q.1 p.2 q.2

/-- A season per cohort and calendar month: `E Xⱼₜ = β_{j, mon t}`. It contains the cohort mean and
a season common to all cohorts (`Model.UnbiasedMean.of_mul`). -/
def cohortSeason {Mo : Type*} [DecidableEq Mo] (mon : T → Mo) : Matrix (J × T) (J × Mo) ℝ :=
  of fun p k => if p.1 = k.1 ∧ mon p.2 = k.2 then 1 else 0

omit [DecidableEq T] in
/-- Months with the same calendar month have the same row in the season design. -/
theorem cohortSeason_row {Mo : Type*} [DecidableEq Mo] {mon : T → Mo} (i : J) {t u : T}
    (h : mon t = mon u) : cohortSeason (J := J) mon (i, t) = cohortSeason mon (i, u) := by
  funext k; simp [cohortSeason, h]

/-- The year-on-year lagged cross-product `(Xᵢₜ - Xᵢᵤ)(Xⱼₛ - Xⱼᵥ)` (`u = t - 12`,
`v = s - 12`). -/
def yoy (i j : J) (t u s v : T) (X : J × T → ℝ) : ℝ := (X (i, t) - X (i, u)) * (X (j, s) - X (j, v))

/-- **The year-on-year cross-product is unbiased for every `β`** under any design whose rows
agree for cohort `i` in months `t`, `u` (e.g. `cohortSeason` with `mon t = mon u`). -/
theorem yoy_unbiased [Fintype J] [Fintype T] {B : Type*} [Fintype B] (D : Matrix (J × T) B ℝ)
    (i j : J) {t u : T} (s v : T) (hD : D (i, t) = D (i, u)) :
    Model.UnbiasedMean (M.covG G) D (yoy i j t u s v)
      (M.obsCovG G i j t s - M.obsCovG G i j t v - M.obsCovG G i j u s + M.obsCovG G i j u v) :=
  Model.unbiasedMean_diff_mul (M.covG G) D hD

/-- **Its expectation across cohorts**: for `i ≠ j` and months distinct across the two cohorts,
`λᵢλⱼ(Γₜₛ - Γₜᵥ - Γᵤₛ + Γᵤᵥ)`: no `C`, `s²`, `τ²` or `G`. With `u = t - 12`, `s = t + h`,
`v = s - 12` and a stationary `Γ`: `λᵢλⱼ(2Γ(h) - Γ(h-12) - Γ(h+12))`, `h ≥ 1`, `h ≠ 12`. -/
theorem yoy_unbiased_factor [Fintype J] [Fintype T] {B : Type*} [Fintype B]
    (D : Matrix (J × T) B ℝ) {i j : J} (hij : i ≠ j) {t u s v : T} (hD : D (i, t) = D (i, u))
    (hts : t ≠ s) (htv : t ≠ v) (hus : u ≠ s) (huv : u ≠ v) :
    Model.UnbiasedMean (M.covG G) D (yoy i j t u s v)
      (M.load i * M.load j * (M.Γ t s - M.Γ t v - M.Γ u s + M.Γ u v)) :=
  (M.yoy_unbiased G D i j s v hD).congr (fun _ => rfl) (by
    rw [M.obsCovG_of_ne G hij hts, M.obsCovG_of_ne G hij htv, M.obsCovG_of_ne G hij hus,
      M.obsCovG_of_ne G hij huv]
    ring)

/-- **Pooled over months**: a weighted sum `Σₖ aₖ(Xᵢₜₖ - Xᵢᵤₖ)(Xⱼₛₖ - Xⱼᵥₖ)` over month
quadruples `k = (tₖ, uₖ, sₖ, vₖ)` (e.g. all pairs at lag `h` in the overlap of the two cohorts'
months) is unbiased for `λᵢλⱼΣₖ aₖ(Γₜₛ - Γₜᵥ - Γᵤₛ + Γᵤᵥ)`. -/
theorem yoyPooled_unbiased [Fintype J] [Fintype T] {B : Type*} [Fintype B]
    (D : Matrix (J × T) B ℝ) {i j : J} (hij : i ≠ j) (S : Finset (T × T × T × T))
    (a : T × T × T × T → ℝ)
    (hS : ∀ k ∈ S, D (i, k.1) = D (i, k.2.1) ∧ k.1 ≠ k.2.2.1 ∧ k.1 ≠ k.2.2.2 ∧
      k.2.1 ≠ k.2.2.1 ∧ k.2.1 ≠ k.2.2.2) :
    Model.UnbiasedMean (M.covG G) D
      (fun X => ∑ k ∈ S, a k * yoy i j k.1 k.2.1 k.2.2.1 k.2.2.2 X)
      (M.load i * M.load j * ∑ k ∈ S, a k *
        (M.Γ k.1 k.2.2.1 - M.Γ k.1 k.2.2.2 - M.Γ k.2.1 k.2.2.1 + M.Γ k.2.1 k.2.2.2)) := by
  refine (Model.UnbiasedMean.sum S (θ := fun k => a k * (M.load i * M.load j *
    (M.Γ k.1 k.2.2.1 - M.Γ k.1 k.2.2.2 - M.Γ k.2.1 k.2.2.1 + M.Γ k.2.1 k.2.2.2)))
    fun k hk => ?_).congr (fun _ => rfl) ?_
  · obtain ⟨hD, h1, h2, h3, h4⟩ := hS k hk
    exact (M.yoy_unbiased_factor G D hij hD h1 h2 h3 h4).const_mul (a k)
  · rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring

end Lagged

/-! ### The true expectation for random cells -/

namespace Cells

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {B : Type*} [Fintype B] {D : Matrix (J × T) B ℝ}
  {β : B → ℝ} {G : J → Matrix T T ℝ}

/-- **For random cells with the factor table**: any square-integrable cells with means `Dβ` and
covariances `obsCovG` (`Factor.Cells`) have
`E[(Xᵢₜ - Xᵢᵤ)(Xⱼₛ - Xⱼᵥ)] = λᵢλⱼ(Γₜₛ - Γₜᵥ - Γᵤₛ + Γᵤᵥ)` for `i ≠ j`, months distinct across
the cohorts and `D` equal in rows `(i, t)`, `(i, u)`. No distribution is assumed. -/
theorem integral_yoy [Fintype J] [Fintype T] (X : Cells (M.obsCovG G) D β P) {i j : J}
    (hij : i ≠ j) {t u s v : T} (hD : D (i, t) = D (i, u)) (hts : t ≠ s) (htv : t ≠ v)
    (hus : u ≠ s) (huv : u ≠ v) :
    ∫ ω, yoy i j t u s v (fun p => X.X p ω) ∂P
      = M.load i * M.load j * (M.Γ t s - M.Γ t v - M.Γ u s + M.Γ u v) :=
  (M.yoy_unbiased_factor G D hij hD hts htv hus huv).integral_eq X.X β X.memLp X.mean
    fun p q => X.cov p q

end Cells

/-! ### (I4) Individual loadings need three cohorts -/

section Loadings

variable (G : J → Matrix T T ℝ)

/-- **(I4) Three cohorts identify a loading**: for distinct cohorts `i, j, k` with `λⱼ, λₖ ≠ 0` and
months `t ≠ s`, `Σ(i,j)Σ(i,k)/Σ(j,k) = λᵢ²Γₜₛ` (Anderson–Rubin), whatever `C`, `s²`, `τ²`, `G`. -/
theorem load_sq_of_three {i j k : J} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : M.load j ≠ 0) (hk : M.load k ≠ 0) {t s : T} (hts : t ≠ s) :
    M.obsCovG G i j t s * M.obsCovG G i k t s / M.obsCovG G j k t s
      = M.load i ^ 2 * M.Γ t s := by
  rw [M.obsCovG_of_ne G hij hts, M.obsCovG_of_ne G hik hts, M.obsCovG_of_ne G hjk hts]
  by_cases hΓ : M.Γ t s = 0
  · simp [hΓ]
  · field_simp

/-- **Trading a loading against per-cohort dynamics**: two models that differ only in their
loadings and per-cohort dynamics have the same table if the cross products `λᵢλⱼ` (`i ≠ j`) agree
and `Gᵢ + λᵢ²Γ` agrees for every cohort. -/
theorem obsCovG_eq_of_trade {M' : Factor J T} {G' : J → Matrix T T ℝ} (hτ : M'.τ2 = M.τ2)
    (hC : M'.C = M.C) (hs : M'.s2 = M.s2) (hw : M'.w = M.w) (hΓ : M'.Γ = M.Γ)
    (hcross : ∀ i j, i ≠ j → M'.load i * M'.load j = M.load i * M.load j)
    (hG : ∀ i t s, G' i t s + M'.load i ^ 2 * M.Γ t s = G i t s + M.load i ^ 2 * M.Γ t s)
    (i j : J) (t s : T) : M'.obsCovG G' i j t s = M.obsCovG G i j t s := by
  simp only [obsCovG, obsCov, Shock.obsCov, toShock, hτ, hC, hs, hw, hΓ]
  by_cases hij : i = j
  · subst hij
    have := hG i t s
    simp only [ite_true]
    nlinarith [this]
  · simp only [hij, ite_false, hcross i j hij]

/-- Two cohorts, two months, `Γ = I`, no shock, unit noise and `τ² = 1`; loadings `l`. -/
noncomputable def exTwo (l : Fin 2 → ℝ) : Factor (Fin 2) (Fin 2) where
  τ2 := 1
  C := 0
  s2 := fun _ => 1
  w := fun _ _ => 1
  load := l
  Γ := 1
  τ2_pos := one_pos
  C_posSemidef := PosSemidef.zero
  s2_pos := fun _ => one_pos
  w_pos := fun _ _ => one_pos
  Γ_posSemidef := PosSemidef.one

/-- **(I4) Two cohorts do not identify the loadings**: loadings `(2, 1/2)` with per-cohort dynamics
`(0, (3/4)I)` and loadings `(1, 1)` with `(3I, 0)` (all `⪰ 0`) give the same table, but
`λ₀² = 4` against `1`. -/
theorem two_cohorts_not_identified :
    (∀ j, (![0, (3 / 4 : ℝ) • 1] : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) j |>.PosSemidef) ∧
    (∀ j, (![(3 : ℝ) • 1, 0] : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) j |>.PosSemidef) ∧
    (∀ i j t s, (exTwo ![1, 1]).obsCovG ![(3 : ℝ) • 1, 0] i j t s
      = (exTwo ![2, 1 / 2]).obsCovG ![0, (3 / 4 : ℝ) • 1] i j t s) ∧
    (exTwo ![2, 1 / 2]).load 0 ^ 2 ≠ (exTwo ![1, 1]).load 0 ^ 2 := by
  refine ⟨fun j => ?_, fun j => ?_, obsCovG_eq_of_trade _ _ rfl rfl rfl rfl rfl ?_ ?_, ?_⟩
  · fin_cases j
    · exact PosSemidef.zero
    · exact PosSemidef.one.smul (by norm_num)
  · fin_cases j
    · exact PosSemidef.one.smul (by norm_num)
    · exact PosSemidef.zero
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [exTwo] at hij ⊢
  · intro i t s
    fin_cases i <;> simp [exTwo, Matrix.one_apply] <;> split_ifs <;> norm_num
  · simp [exTwo]; norm_num

end Loadings

/-! ### (I5) An AR(1) factor from its cross-moments -/

section AR1

variable {N : ℕ} (M : Factor J (Fin N)) (G : J → Matrix (Fin N) (Fin N) ℝ) {γ φ : ℝ}

/-- Under an AR(1) factor, two different cohorts at lag `h = s - t ≥ 1` have covariance
`λᵢλⱼγφʰ`. -/
theorem obsCovG_ar1 (hΓ : M.Γ = ar1 N γ φ) {i j : J} (hij : i ≠ j) {t s : Fin N}
    (hts : t < s) : M.obsCovG G i j t s = M.load i * M.load j * γ * φ ^ ((s : ℕ) - t) := by
  rw [M.obsCovG_of_ne G hij hts.ne, hΓ, ar1, of_apply]
  simp only [show (t : ℕ) ≤ s from Fin.le_def.mp hts.le, ite_true]
  ring

/-- At lag `0`, two different cohorts have covariance `γλᵢλⱼ + Cᵢⱼ`. -/
theorem obsCovG_ar1_lag0 (hΓ : M.Γ = ar1 N γ φ) {i j : J} (hij : i ≠ j) (t : Fin N) :
    M.obsCovG G i j t t = M.load i * M.load j * γ + M.C i j := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hΓ, ar1, hij]

/-- **(I5) `φ`, `γλᵢλⱼ` and `Cᵢⱼ` from the cross-moments**: with `N ≥ 3` months and two
different cohorts, `S₂ = φS₁` (lags `2` and `1` from month `0`); if `φ ≠ 0` and `γλᵢλⱼ ≠ 0`,
then `φ = S₂/S₁`, `γλᵢλⱼ = S₁²/S₂` and `Cᵢⱼ = S₀ - S₁²/S₂`. -/
theorem ar1_identified (hN : 3 ≤ N) (hΓ : M.Γ = ar1 N γ φ) {i j : J} (hij : i ≠ j) :
    let S₀ := M.obsCovG G i j ⟨0, by omega⟩ ⟨0, by omega⟩
    let S₁ := M.obsCovG G i j ⟨0, by omega⟩ ⟨1, by omega⟩
    let S₂ := M.obsCovG G i j ⟨0, by omega⟩ ⟨2, by omega⟩
    S₂ = φ * S₁ ∧ (φ ≠ 0 → M.load i * M.load j * γ ≠ 0 →
      φ = S₂ / S₁ ∧ M.load i * M.load j * γ = S₁ ^ 2 / S₂ ∧ M.C i j = S₀ - S₁ ^ 2 / S₂) := by
  intro S₀ S₁ S₂
  have h1 : S₁ = M.load i * M.load j * γ * φ :=
    (M.obsCovG_ar1 G hΓ hij (by simp [Fin.lt_def])).trans (by simp)
  have h2 : S₂ = M.load i * M.load j * γ * φ ^ 2 :=
    (M.obsCovG_ar1 G hΓ hij (by simp [Fin.lt_def])).trans (by simp)
  have h0 : S₀ = M.load i * M.load j * γ + M.C i j := M.obsCovG_ar1_lag0 G hΓ hij _
  refine ⟨by rw [h1, h2]; ring, fun hφ hk => ?_⟩
  have hk' := hk
  simp only [mul_ne_zero_iff] at hk'
  obtain ⟨⟨hi, hj⟩, hγ⟩ := hk'
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
  ring

omit [DecidableEq J] in
/-- The same model with the factor moved into the shock: `C + γλλᵀ` and no factor. -/
noncomputable def factorToShock [Fintype J] {T : Type*} (M : Factor J T) (γ : ℝ) (hγ : 0 ≤ γ) :
    Factor J T :=
  { M with
    C := M.C + γ • vecMulVec M.load M.load
    Γ := 0
    C_posSemidef := M.C_posSemidef.add ((posSemidef_loadings M.load).smul hγ)
    Γ_posSemidef := PosSemidef.zero }

/-- **(I5) `φ = 0` does not separate**: an AR(1) factor with `φ = 0` is independent months, and
the table is that of the same model with shock `C + γλλᵀ` and no factor (`obsCov_eq_of_lag0`). -/
theorem ar1_zero_eq_shock [Fintype J] (hΓ : M.Γ = ar1 N γ 0) (hγ : 0 ≤ γ) (i j : J)
    (t s : Fin N) : M.obsCov i j t s = (M.factorToShock γ hγ).obsCov i j t s := by
  refine M.obsCov_eq_of_lag0 (M' := M.factorToShock γ hγ) (γ := γ) (γ' := 0) rfl rfl rfl (fun _ => by simp [hΓ, ar1])
    (fun _ => rfl) (fun i' j' => by
      simp only [factorToShock, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
        smul_eq_mul]
      ring) (fun i' j' t' s' hts => ?_) i j t s
  have hv := Fin.val_ne_of_ne hts
  simp only [factorToShock, hΓ, ar1, of_apply, Matrix.zero_apply, mul_zero]
  split_ifs with h
  · rw [zero_pow (by omega), mul_zero, mul_zero]
  · rw [zero_pow (by omega), mul_zero, mul_zero]

end AR1

/-! ### The shock estimators under a factor -/

section ShockBias

variable [Fintype J] [Fintype T] (G : J → Matrix T T ℝ) {a : J → T → ℝ}

variable (a) in
/-- `(eₜ - aᵢ)ᵀA(eₜ - aⱼ)`: what a matrix `A` over months contributes to `E[rᵢₜrⱼₜ]` for the
within-card residuals `rⱼₜ = Xⱼₜ - Σₛaⱼₛ Xⱼₛ`. -/
def resQuad (A : Matrix T T ℝ) (i j : J) (t : T) : ℝ :=
  ∑ t', ∑ s', ((if t' = t then 1 else 0) - a i t') * ((if s' = t then 1 else 0) - a j s') * A t' s'

/-- **Residual products under a factor**: `E[rᵢₜrⱼₜ]` is the `Shock` value
`dᵢⱼₜCᵢⱼ + δᵢⱼhᵢₜsᵢ²` plus `λᵢλⱼ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)` plus, on one cohort, `(eₜ - aᵢ)ᵀGᵢ(eₜ - aᵢ)`:
within-card demeaning removes only the part of the factor that is constant over the months. -/
theorem res_unbiased (ha : ∀ j, ∑ t, a j t = 1) (i j : J) (t : T) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.res a X i t * Shock.res a X j t)
      (Shock.d a i j t * M.C i j + (if i = j then M.s2 i * M.toShock.h a i t else 0)
        + M.load i * M.load j * resQuad a M.Γ i j t
        + (if i = j then resQuad a (G i) i i t else 0)) := by
  let c : J → T → ℝ := fun k t' => (if t' = t then 1 else 0) - a k t'
  let ℓ : J → J × T → ℝ := fun k p => if p.1 = k then c k p.2 else 0
  have hlin : ∀ k (X : J × T → ℝ), ∑ p, ℓ k p * X p = Shock.res a X k t := fun k X => by
    rw [Fintype.sum_prod_type, sum_eq_single k (fun l _ hl => by simp [ℓ, hl]) (by simp)]
    simp [ℓ, c, Shock.res, sub_mul, sum_sub_distrib]
  have hsum : ∑ p, ℓ i p = 0 := by
    have := hlin i (fun _ => 1)
    simp only [mul_one] at this
    rw [this, Shock.res]; simp [ha]
  have hpair : ∀ F : J × T → J × T → ℝ,
      ∑ p, ∑ q, ℓ i p * ℓ j q * F p q = ∑ t', ∑ s', c i t' * c j s' * F (i, t') (j, s') := by
    intro F
    rw [Fintype.sum_prod_type, sum_eq_single i (fun k _ hk => by simp [ℓ, hk]) (by simp)]
    refine sum_congr rfl fun t' _ => ?_
    rw [Fintype.sum_prod_type, sum_eq_single j (fun l _ hl => by simp [ℓ, hl]) (by simp)]
    simp [ℓ]
  -- The shock part is the `Shock` value: one estimator has one expectation.
  have hshock : ∑ p, ∑ q, ℓ i p * ℓ j q * M.toShock.cov p q
      = Shock.d a i j t * M.C i j + (if i = j then M.s2 i * M.toShock.h a i t else 0) :=
    Model.UnbiasedCov.unique M.toShock.cov_symm
      ((Model.unbiasedCov_mul M.toShock.cov (ℓ i) (ℓ j) hsum).congr
        (fun X => by rw [hlin, hlin]) rfl)
      (M.toShock.unbiased_res ha i j t)
  refine (Model.unbiasedCov_mul (M.covG G) (ℓ i) (ℓ j) hsum).congr
    (fun X => by rw [hlin, hlin]) ?_
  have hsplit : ∀ p q, M.covG G p q = M.load p.1 * M.load q.1 * M.Γ p.2 q.2
      + M.toShock.cov p q + (if p.1 = q.1 then G p.1 p.2 q.2 else 0) := fun p q => by
    simp [covG, obsCovG, obsCov, Shock.cov]
  have hfac : ∑ t', ∑ s', c i t' * c j s' * (M.load i * M.load j * M.Γ t' s')
      = M.load i * M.load j * resQuad a M.Γ i j t := by
    simp only [resQuad, c, mul_sum]
    exact sum_congr rfl fun t' _ => sum_congr rfl fun s' _ => by ring
  have hcard : ∑ t', ∑ s', c i t' * c j s' * (if i = j then G i t' s' else 0)
      = if i = j then resQuad a (G i) i i t else 0 := by
    split_ifs with hij
    · subst hij; rfl
    · simp
  simp only [hsplit, mul_add, sum_add_distrib, hshock, hpair]
  rw [hfac, hcard]
  ring

/-- **`Shock.crossHat` under a factor** (`i ≠ j`): unbiased for
`Cᵢⱼ + λᵢλⱼ Σₜ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ) / Σₜdᵢⱼₜ`. With independent months `Γ = γI` the ratio is
`γ` (the factor is a rank-one shock); with a constant factor it is `0`. -/
theorem crossHat_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) {i j : J} (hij : i ≠ j)
    (hd : ∑ t, Shock.d a i j t ≠ 0) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.crossHat a X i j)
      (M.C i j + M.load i * M.load j * (∑ t, resQuad a M.Γ i j t) / ∑ t, Shock.d a i j t) := by
  refine (Model.UnbiasedCov.const_mul (∑ t, Shock.d a i j t)⁻¹
    (Model.UnbiasedCov.sum univ fun t _ => M.res_unbiased G ha i j t)).congr
    (fun X => by rw [Shock.crossHat, div_eq_inv_mul]) ?_
  simp only [hij, ite_false, add_zero, sum_add_distrib, ← sum_mul, ← mul_sum]
  field_simp

/-- **Finding 26: the shock fit absorbs only part of the factor.** Two months, equal weights
`aⱼₜ = 1/2`, an AR(1) factor `γφ^|t-s|`: `Shock.crossHat` is unbiased for
`Cᵢⱼ + (1 - φ)γλᵢλⱼ`, so for `0 < φ < 1` (and `γλᵢλⱼ ≠ 0`) neither for `Cᵢⱼ` nor for the lag-0
covariance `Cᵢⱼ + γλᵢλⱼ`. -/
theorem crossHat_ar1_two (M : Factor J (Fin 2)) (G : J → Matrix (Fin 2) (Fin 2) ℝ) {γ φ : ℝ}
    (hΓ : M.Γ = ar1 2 γ φ) {i j : J} (hij : i ≠ j) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.crossHat (fun _ _ => 1 / 2) X i j)
      (M.C i j + (1 - φ) * γ * (M.load i * M.load j)) := by
  have hd : ∑ t, Shock.d (fun (_ : J) (_ : Fin 2) => (1 / 2 : ℝ)) i j t = 1 := by
    simp [Shock.d]; norm_num
  refine (M.crossHat_factor_unbiased G (fun j => by simp) hij
    (by rw [hd]; norm_num)).congr (fun _ => rfl) ?_
  rw [hd, hΓ]
  simp [resQuad, Fin.sum_univ_two, ar1]
  ring

end ShockBias

/-! ### The between-cohort spread under a factor -/

section Between

omit [DecidableEq J] [DecidableEq T] in
/-- Regrouping a double sum of a bilinear form: `Σₖₗ fₖgₗ(pₖᵀΓqₗ) = (Σₖ fₖpₖ)ᵀΓ(Σₗ gₗqₗ)`. -/
lemma sum_mul_sum_bilin [Fintype J] [Fintype T] (f g : J → ℝ) (p q : J → T → ℝ)
    (Γ : T → T → ℝ) :
    ∑ k, ∑ l, f k * g l * (∑ t, ∑ s, p k t * q l s * Γ t s)
      = ∑ t, ∑ s, (∑ k, f k * p k t) * (∑ l, g l * q l s) * Γ t s := by
  have h : ∀ t s, (∑ k, f k * p k t) * (∑ l, g l * q l s) * Γ t s
      = ∑ k, ∑ l, f k * g l * (p k t * q l s * Γ t s) := fun t s => by
    rw [sum_mul_sum, sum_mul]
    exact sum_congr rfl fun k _ => by rw [sum_mul]; exact sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl fun t _ => sum_congr rfl fun s _ => h t s]
  have h2 : ∀ k l, f k * g l * (∑ t, ∑ s, p k t * q l s * Γ t s)
      = ∑ t, ∑ s, f k * g l * (p k t * q l s * Γ t s) := fun k l => by simp only [mul_sum]
  rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => h2 k l]
  calc _ = ∑ k, ∑ t, ∑ l, ∑ s, f k * g l * (p k t * q l s * Γ t s) :=
        sum_congr rfl fun k _ => sum_comm
    _ = ∑ t, ∑ k, ∑ s, ∑ l, f k * g l * (p k t * q l s * Γ t s) :=
        (sum_comm).trans (sum_congr rfl fun t _ => sum_congr rfl fun k _ => sum_comm)
    _ = _ := sum_congr rfl fun t _ => sum_comm

variable [Fintype J] [Fintype T] (G : J → Matrix T T ℝ) {a : J → T → ℝ}

variable (a) in
/-- `Pᵢⱼ = cov(μ̂ᵢ, μ̂ⱼ)` for the cohort estimates `μ̂ⱼ = Σₜaⱼₜ Xⱼₜ` under the factor table. -/
noncomputable def portCovG (i j : J) : ℝ := ∑ t, ∑ s, a i t * a j s * M.obsCovG G i j t s

omit [Fintype J] in
/-- `P` is the `Shock` matrix `K` plus `λᵢλⱼaᵢᵀΓaⱼ` plus, on the diagonal, `aᵢᵀGᵢaᵢ`. -/
theorem portCovG_eq (i j : J) :
    M.portCovG G a i j = M.toShock.K a i j
      + M.load i * M.load j * (∑ t, ∑ s, a i t * a j s * M.Γ t s)
      + (if i = j then ∑ t, ∑ s, a i t * a i s * G i t s else 0) := by
  simp only [portCovG, Shock.K, of_apply, obsCovG, obsCov, mul_add, sum_add_distrib, mul_sum]
  congr 1
  · rw [add_comm]
    congr 1
    exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring
  · split_ifs with h
    · subst h; rfl
    · simp

/-- Products of contrasts of the cohort estimates under the factor table: if `Σⱼ cⱼ = 0`, then
`E[(Σⱼ cⱼμ̂ⱼ)(Σⱼ c'ⱼμ̂ⱼ)] = Σᵢⱼ cᵢc'ⱼPᵢⱼ`. -/
theorem contrast_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) (c c' : J → ℝ)
    (hc : ∑ j, c j = 0) :
    Model.UnbiasedCov (M.covG G)
      (fun X => (∑ j, c j * Shock.muHat a X j) * (∑ j, c' j * Shock.muHat a X j))
      (∑ i, ∑ j, c i * c' j * M.portCovG G a i j) := by
  have hlin : ∀ (e : J → ℝ) (X : J × T → ℝ),
      ∑ p : J × T, e p.1 * a p.1 p.2 * X p = ∑ j, e j * Shock.muHat a X j := fun e X => by
    simp only [Fintype.sum_prod_type, Shock.muHat, mul_sum, mul_assoc]
  have hsum : ∑ p : J × T, c p.1 * a p.1 p.2 = 0 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, ha, mul_one, hc]
  refine (Model.unbiasedCov_mul (M.covG G) (fun p => c p.1 * a p.1 p.2)
    (fun p => c' p.1 * a p.1 p.2) hsum).congr (fun X => by rw [hlin, hlin]) ?_
  simp only [Fintype.sum_prod_type, portCovG, covG, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

/-- **The between-cohort spread under a factor.** For weights `x` summing to one,
`E Σⱼ xⱼ(μ̂ⱼ - Σᵢ xᵢμ̂ᵢ)²` is the `Shock` value `τ²(1 - Σⱼ xⱼ²) + Σⱼ xⱼΣⱼⱼ - xᵀΣx` plus the
factor term `Σⱼ xⱼ vⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢ xᵢλᵢaᵢ`, plus `Σₖ xₖ(1 - xₖ)aₖᵀGₖaₖ`: per-cohort
dynamics look like extra heterogeneity `τ²`. -/
theorem between_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) {x : J → ℝ} (hx : ∑ j, x j = 1) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.between a x X)
      (M.τ2 * (1 - ∑ j, x j ^ 2) + ∑ j, x j * M.toShock.errCov a j j
        - ∑ i, ∑ j, x i * x j * M.toShock.errCov a i j
        + ∑ j, x j * ∑ t, ∑ s, (M.load j * a j t - ∑ i, x i * M.load i * a i t)
            * (M.load j * a j s - ∑ i, x i * M.load i * a i s) * M.Γ t s
        + ∑ k, x k * (1 - x k) * ∑ t, ∑ s, a k t * a k s * G k t s) := by
  let c : J → J → ℝ := fun j k => (if k = j then 1 else 0) - x k
  have hc : ∀ j, ∑ k, c j k = 0 := fun j => by simp [c, sum_sub_distrib, hx]
  have hlin : ∀ j X, ∑ k, c j k * Shock.muHat a X k
      = Shock.muHat a X j - ∑ i, x i * Shock.muHat a X i :=
    fun j X => by simp [c, sub_mul, sum_sub_distrib]
  have hfun : ∀ X, ∑ j ∈ univ, x j * ((∑ k, c j k * Shock.muHat a X k)
      * (∑ k, c j k * Shock.muHat a X k)) = Shock.between a x X := fun X => by
    simp only [Shock.between, hlin, sq]
  -- The shock part: one estimator, one expectation.
  have hS : ∑ j ∈ univ, x j * ∑ k, ∑ l, c j k * c j l * M.toShock.K a k l
      = M.τ2 * (1 - ∑ j, x j ^ 2) + ∑ j, x j * M.toShock.errCov a j j
        - ∑ i, ∑ j, x i * x j * M.toShock.errCov a i j :=
    Model.UnbiasedCov.unique M.toShock.cov_symm
      ((Model.UnbiasedCov.sum univ fun j _ =>
        (M.toShock.unbiased_contrast ha (c j) (c j) (hc j)).const_mul (x j)).congr hfun rfl)
      (M.toShock.between_unbiased ha hx)
  refine ((Model.UnbiasedCov.sum univ fun j _ =>
    (M.contrast_factor_unbiased G ha (c j) (c j) (hc j)).const_mul (x j)).congr hfun ?_)
  have hsplit : ∑ j ∈ univ, x j * ∑ k, ∑ l, c j k * c j l * M.portCovG G a k l
      = ∑ j ∈ univ, x j * ∑ k, ∑ l, c j k * c j l * M.toShock.K a k l
        + ∑ j, x j * ∑ k, ∑ l, c j k * c j l
            * (M.load k * M.load l * (∑ t, ∑ s, a k t * a l s * M.Γ t s))
        + ∑ j, x j * ∑ k, ∑ l, c j k * c j l
            * (if k = l then ∑ t, ∑ s, a k t * a k s * G k t s else 0) := by
    simp only [portCovG_eq, mul_add, sum_add_distrib]
  have hfac : ∑ j, x j * ∑ k, ∑ l, c j k * c j l
        * (M.load k * M.load l * (∑ t, ∑ s, a k t * a l s * M.Γ t s))
      = ∑ j, x j * ∑ t, ∑ s, (M.load j * a j t - ∑ i, x i * M.load i * a i t)
          * (M.load j * a j s - ∑ i, x i * M.load i * a i s) * M.Γ t s := by
    refine sum_congr rfl fun j _ => ?_
    congr 1
    have hv : ∀ t, ∑ k, c j k * M.load k * a k t
        = M.load j * a j t - ∑ i, x i * M.load i * a i t :=
      fun t => by simp [c, sub_mul, sum_sub_distrib]
    calc _ = ∑ k, ∑ l, (c j k * M.load k) * (c j l * M.load l)
          * (∑ t, ∑ s, a k t * a l s * M.Γ t s) :=
          sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
      _ = _ := sum_mul_sum_bilin _ _ a a M.Γ
      _ = _ := sum_congr rfl fun t _ => sum_congr rfl fun s _ => by rw [hv t, hv s]
  -- The per-cohort part: `Σⱼ xⱼcⱼₖ² = xₖ(1 - xₖ)`.
  have hq : ∀ k, ∑ j, x j * (c j k * c j k) = x k * (1 - x k) := fun k => by
    simp only [c, sub_mul, mul_sub, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      sum_sub_distrib, mem_univ, ite_true, sum_ite_eq]
    rw [← sum_mul, hx]
    ring
  have hcard : ∑ j, x j * ∑ k, ∑ l, c j k * c j l
        * (if k = l then ∑ t, ∑ s, a k t * a k s * G k t s else 0)
      = ∑ k, x k * (1 - x k) * ∑ t, ∑ s, a k t * a k s * G k t s := by
    have h1 : ∀ j, ∑ k, ∑ l, c j k * c j l
          * (if k = l then ∑ t, ∑ s, a k t * a k s * G k t s else 0)
        = ∑ k, c j k * c j k * ∑ t, ∑ s, a k t * a k s * G k t s := fun j =>
      sum_congr rfl fun k _ => by simp [mul_ite]
    have hg : ∀ g : J → ℝ, ∑ j, x j * ∑ k, c j k * c j k * g k = ∑ k, x k * (1 - x k) * g k :=
      fun g => by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← hq k, sum_mul]
        exact sum_congr rfl fun j _ => by ring
    simp only [h1]
    exact hg fun k => ∑ t, ∑ s, a k t * a k s * G k t s
  rw [hsplit, hS, hfac, hcard]

/-- **Equal weights**: with the same weights `aⱼₜ = αₜ` for every cohort, the factor term is
`Σⱼ xⱼ(λⱼ - λ̄)² · αᵀΓα`, `λ̄ = Σᵢ xᵢλᵢ`: zero exactly when the loadings are equal (or
`αᵀΓα = 0`). A shock fit then reads the loading dispersion times the factor variance of the
averaged month as heterogeneity `τ²`. -/
theorem between_factor_equal_weights {α : T → ℝ} (hα : ∑ t, α t = 1) {x : J → ℝ}
    (hx : ∑ j, x j = 1) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.between (fun _ => α) x X)
      (M.τ2 * (1 - ∑ j, x j ^ 2) + ∑ j, x j * M.toShock.errCov (fun _ => α) j j
        - ∑ i, ∑ j, x i * x j * M.toShock.errCov (fun _ => α) i j
        + (∑ j, x j * (M.load j - ∑ i, x i * M.load i) ^ 2)
          * (∑ t, ∑ s, α t * α s * M.Γ t s)
        + ∑ k, x k * (1 - x k) * ∑ t, ∑ s, α t * α s * G k t s) := by
  refine (M.between_factor_unbiased G (fun _ => hα) hx).congr (fun _ => rfl) ?_
  congr 2
  rw [sum_mul]
  refine sum_congr rfl fun j _ => ?_
  have hv : ∀ t, M.load j * α t - ∑ i, x i * M.load i * α t
      = (M.load j - ∑ i, x i * M.load i) * α t := fun t => by rw [← sum_mul]; ring
  simp only [hv, mul_sum]
  exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring

end Between

/-! ### The diagonal shock estimators and `τ̂²` under a factor -/

section ShockDiag

variable [Fintype J] [Fintype T] (G : J → Matrix T T ℝ) (a u v : J → T → ℝ)

/-- What the factor and the per-cohort dynamics add to `E[rⱼₜ²]`:
`λⱼ²(eₜ - aⱼ)ᵀΓ(eₜ - aⱼ) + (eₜ - aⱼ)ᵀGⱼ(eₜ - aⱼ)`. -/
noncomputable def resExtra (j : J) (t : T) : ℝ :=
  M.load j ^ 2 * resQuad a M.Γ j j t + resQuad a (G j) j j t

/-- Its `u`-weighted sum `Fⱼ(u) = Σₜ uⱼₜ · resExtra`. -/
noncomputable def resExtraSum (j : J) : ℝ := ∑ t, u j t * M.resExtra G a j t

/-- The bias of `Ĉⱼⱼ` under a factor, by Cramer's rule: `(hⱼ(v)Fⱼ(u) - hⱼ(u)Fⱼ(v)) / det`. -/
noncomputable def CdiagBias (j : J) : ℝ :=
  (M.toShock.hSum a v j * M.resExtraSum G a u j - M.toShock.hSum a u j * M.resExtraSum G a v j)
    / M.toShock.det a u v j

/-- The bias of `ŝⱼ²` under a factor: `(dⱼ(u)Fⱼ(v) - dⱼ(v)Fⱼ(u)) / det`. -/
noncomputable def s2Bias (j : J) : ℝ :=
  (Shock.dSum a u j * M.resExtraSum G a v j - Shock.dSum a v j * M.resExtraSum G a u j)
    / M.toShock.det a u v j

/-- The bias of `Σ̂ᵢⱼ` under a factor: on the diagonal from `Ĉⱼⱼ` and `ŝⱼ²`, off it from
`Shock.crossHat` (`crossHat_factor_unbiased`). -/
noncomputable def errCovBias (i j : J) : ℝ :=
  if i = j then (∑ t, a i t * a i t) * M.CdiagBias G a u v i
      + M.s2Bias G a u v i * ∑ t, a i t ^ 2 / M.w i t
  else (∑ t, a i t * a j t)
      * (M.load i * M.load j * (∑ t, resQuad a M.Γ i j t) / ∑ t, Shock.d a i j t)

/-- What the factor and the per-cohort dynamics add to the between-cohort spread
(`between_factor_unbiased`). -/
noncomputable def betweenBias (x : J → ℝ) : ℝ :=
  ∑ j, x j * ∑ t, ∑ s, (M.load j * a j t - ∑ i, x i * M.load i * a i t)
      * (M.load j * a j s - ∑ i, x i * M.load i * a i s) * M.Γ t s
    + ∑ k, x k * (1 - x k) * ∑ t, ∑ s, a k t * a k s * G k t s

/-- The bias of `τ̂²` under a factor:
`(betweenBias - Σⱼ xⱼBⱼⱼ + Σᵢⱼ xᵢxⱼBᵢⱼ) / (1 - Σⱼ xⱼ²)`, `B = errCovBias`. -/
noncomputable def tauBias (x : J → ℝ) : ℝ :=
  (M.betweenBias G a x - ∑ j, x j * M.errCovBias G a u v j j
    + ∑ i, ∑ j, x i * x j * M.errCovBias G a u v i j) / (1 - ∑ j, x j ^ 2)

variable {a u v}

/-- `E Σₜ uⱼₜrⱼₜ² = dⱼ(u)Cⱼⱼ + hⱼ(u)sⱼ² + Fⱼ(u)` under a factor. -/
theorem sqSum_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) (j : J) :
    Model.UnbiasedCov (M.covG G) (fun X => Shock.sqSum a u X j)
      (Shock.dSum a u j * M.C j j + M.toShock.hSum a u j * M.s2 j + M.resExtraSum G a u j) := by
  refine (Model.UnbiasedCov.sum univ fun t _ =>
    (M.res_unbiased G ha j j t).const_mul (u j t)).congr
    (fun X => by simp only [Shock.sqSum, sq]) ?_
  simp only [ite_true, Shock.dSum, Shock.hSum, resExtraSum, resExtra, sum_mul,
    ← sum_add_distrib]
  exact sum_congr rfl fun t _ => by ring

/-- **`Ĉⱼⱼ` under a factor** is unbiased for `Cⱼⱼ + CdiagBias`. -/
theorem CdiagHat_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) {j : J}
    (hdet : M.toShock.det a u v j ≠ 0) :
    Model.UnbiasedCov (M.covG G) (fun X => M.toShock.CdiagHat a u v X j)
      (M.C j j + M.CdiagBias G a u v j) := by
  refine (Model.UnbiasedCov.const_mul (M.toShock.det a u v j)⁻¹
    (((M.sqSum_factor_unbiased G (u := u) ha j).const_mul (M.toShock.hSum a v j)).add
      ((M.sqSum_factor_unbiased G (u := v) ha j).const_mul (-M.toShock.hSum a u j)))).congr
    (fun X => by rw [Shock.CdiagHat, div_eq_inv_mul]; ring) ?_
  rw [inv_mul_eq_iff_eq_mul₀ hdet, CdiagBias, mul_add (M.toShock.det a u v j),
    mul_div_cancel₀ _ hdet]
  simp only [Shock.det]
  ring

/-- **`ŝⱼ²` under a factor** is unbiased for `sⱼ² + s2Bias`. -/
theorem s2Hat_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1) {j : J}
    (hdet : M.toShock.det a u v j ≠ 0) :
    Model.UnbiasedCov (M.covG G) (fun X => M.toShock.s2Hat a u v X j)
      (M.s2 j + M.s2Bias G a u v j) := by
  refine (Model.UnbiasedCov.const_mul (M.toShock.det a u v j)⁻¹
    (((M.sqSum_factor_unbiased G (u := v) ha j).const_mul (Shock.dSum a u j)).add
      ((M.sqSum_factor_unbiased G (u := u) ha j).const_mul (-Shock.dSum a v j)))).congr
    (fun X => by rw [Shock.s2Hat, div_eq_inv_mul]; ring) ?_
  rw [inv_mul_eq_iff_eq_mul₀ hdet, s2Bias, mul_add (M.toShock.det a u v j),
    mul_div_cancel₀ _ hdet]
  simp only [Shock.det]
  ring

/-- **`Σ̂` under a factor**: every entry is unbiased for `Σᵢⱼ + errCovBias`. -/
theorem errCovHat_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1)
    (hd : ∀ i j, i ≠ j → ∑ t, Shock.d a i j t ≠ 0) (hdet : ∀ j, M.toShock.det a u v j ≠ 0)
    (i j : J) :
    Model.UnbiasedCov (M.covG G) (fun X => M.toShock.errCovHat a u v X i j)
      (M.toShock.errCov a i j + M.errCovBias G a u v i j) := by
  rw [M.toShock.errCov_apply]
  by_cases hij : i = j
  · subst hij
    refine (((M.CdiagHat_factor_unbiased G ha (hdet i)).const_mul (∑ t, a i t * a i t)).add
      ((M.s2Hat_factor_unbiased G ha (hdet i)).const_mul (∑ t, a i t ^ 2 / M.w i t))).congr
      (fun X => by simp only [Shock.errCovHat, Shock.CHat, ite_true]; simp only [toShock]; ring) ?_
    simp only [errCovBias, ite_true]
    simp only [toShock]
    ring
  · refine ((M.crossHat_factor_unbiased G ha hij (hd i j hij)).const_mul
      (∑ t, a i t * a j t)).congr
      (fun X => by simp [Shock.errCovHat, Shock.CHat, hij]) ?_
    simp only [errCovBias, hij, ite_false, add_zero]
    simp only [toShock]
    ring

/-- **`τ̂²` under a factor** is unbiased for `τ² + tauBias`: the factor and the per-cohort
dynamics enter both through the spread and through the plugged-in `Σ̂`. -/
theorem tauHat_factor_unbiased (ha : ∀ j, ∑ t, a j t = 1)
    (hd : ∀ i j, i ≠ j → ∑ t, Shock.d a i j t ≠ 0) (hdet : ∀ j, M.toShock.det a u v j ≠ 0)
    {x : J → ℝ} (hx : ∑ j, x j = 1) (hx2 : ∑ j, x j ^ 2 ≠ 1) :
    Model.UnbiasedCov (M.covG G) (fun X => M.toShock.tauHat a u v x X)
      (M.τ2 + M.tauBias G a u v x) := by
  have hne : 1 - ∑ j, x j ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx2)
  refine (Model.UnbiasedCov.const_mul (1 - ∑ j, x j ^ 2)⁻¹
    (((M.between_factor_unbiased G ha hx).add ((Model.UnbiasedCov.sum univ fun j _ =>
      (M.errCovHat_factor_unbiased G ha hd hdet j j).const_mul (x j)).const_mul (-1))).add
      (Model.UnbiasedCov.sum univ fun i _ => Model.UnbiasedCov.sum univ fun j _ =>
        (M.errCovHat_factor_unbiased G ha hd hdet i j).const_mul (x i * x j)))).congr
    (fun X => by rw [Shock.tauHat, div_eq_inv_mul]; ring) ?_
  rw [inv_mul_eq_iff_eq_mul₀ hne, tauBias, betweenBias, mul_add (1 - ∑ j, x j ^ 2),
    mul_div_cancel₀ _ hne]
  simp only [mul_add, sum_add_distrib]
  ring

omit [DecidableEq J] [Fintype J] in
/-- With independent months `Γ = γI` the factor part of a residual product is `γ dᵢⱼₜ`: the
same coefficient as the shock. -/
theorem resQuad_smul_one (γ : ℝ) (i j : J) (t : T) :
    resQuad a (γ • (1 : Matrix T T ℝ)) i j t = γ * Shock.d a i j t := by
  have h : ∀ t', ∑ s', ((if t' = t then (1 : ℝ) else 0) - a i t')
      * ((if s' = t then 1 else 0) - a j s') * (γ • (1 : Matrix T T ℝ)) t' s'
      = γ * (((if t' = t then 1 else 0) - a i t') * ((if t' = t then 1 else 0) - a j t')) :=
    fun t' => by
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        sum_ite_eq, mem_univ, ite_true]
      ring
  simp only [resQuad, h, ← mul_sum, Shock.d]
  congr 1
  simp only [sub_mul, mul_sub, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
  ring

/-- **Independent months: the factor is a rank-one shock.** With `Γ = γI` and no per-cohort
dynamics, `Ĉⱼⱼ` is unbiased for `Cⱼⱼ + γλⱼ²` and `ŝⱼ²` stays unbiased for `sⱼ²`, as the
off-diagonal `Shock.crossHat` reads `Cᵢⱼ + γλᵢλⱼ` (`crossHat_factor_unbiased`). -/
theorem CdiagHat_s2Hat_indep (ha : ∀ j, ∑ t, a j t = 1) {γ : ℝ}
    (hΓ : M.Γ = γ • (1 : Matrix T T ℝ)) {j : J} (hdet : M.toShock.det a u v j ≠ 0) :
    Model.UnbiasedCov (M.covG 0) (fun X => M.toShock.CdiagHat a u v X j)
        (M.C j j + γ * M.load j ^ 2)
      ∧ Model.UnbiasedCov (M.covG 0) (fun X => M.toShock.s2Hat a u v X j) (M.s2 j) := by
  have hF : ∀ u' : J → T → ℝ, M.resExtraSum 0 a u' j = M.load j ^ 2 * γ * Shock.dSum a u' j :=
    fun u' => by
      simp only [resExtraSum, resExtra, hΓ, resQuad_smul_one, Pi.zero_apply, Shock.dSum,
        mul_sum]
      refine sum_congr rfl fun t _ => ?_
      simp only [resQuad, Matrix.zero_apply, mul_zero, sum_const_zero, add_zero]
      ring
  constructor
  · refine (M.CdiagHat_factor_unbiased 0 ha hdet).congr (fun _ => rfl) ?_
    rw [CdiagBias, hF, hF]
    congr 1
    rw [div_eq_iff hdet, Shock.det]
    ring
  · refine (M.s2Hat_factor_unbiased 0 ha hdet).congr (fun _ => rfl) ?_
    rw [s2Bias, hF, hF]
    ring_nf

end ShockDiag

end Factor

end Credibility
