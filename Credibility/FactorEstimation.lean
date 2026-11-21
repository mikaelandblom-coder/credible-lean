import Credibility.Expectation
import Credibility.FactorMoments

/-!
# Estimating the common factor model, part 1 (extension, `notes/card-data.md` Step 5)

What the table `Factor.obsCov` (with per-card dynamics `obsCovG`) lets the data identify, and
the first unbiased estimator (`studies/literature.md` §10h). Distribution-free throughout.

* **(I1) Scale** (`obsCov_rescale`, `blup_rescale`): `(λ, Γ) ↦ (aλ, a⁻²Γ)`, `a ≠ 0` (a sign
  flip included), leaves the table, `K`, `ℓ`, `v` and the predictor unchanged. So fixing the
  scale (exposure-weighted mean loading `1`) is a presentation choice.
* **(I2) Lag 0** (`obsCov_eq_of_lag0`, `blup_eq_of_lag0`): with a constant factor variance
  `Γₜₜ = γ`, the table, hence `K`, `ℓ`, `v` and the predictor, depend on `C` and `γλλᵀ` only
  through `C + γλλᵀ` (plus the lagged factor part `λλᵀΓₜₛ`, `t ≠ s`). The split is not needed
  for prediction.
* **(I3) Lag ≥ 1** (`obsCovG_of_ne`, `factor_eq_of_obsCovG_eq`): for two different cards in
  two different months the table is `λᵢλⱼΓₜₛ`, free of `C`, `s²`, `τ²` and the per-card
  dynamics `G`. So tables that agree there agree on the lagged factor part: a common factor
  and per-card dynamics are distinguishable.
* **The year-on-year lagged cross-product** (`yoy_unbiased`, `yoy_unbiased_factor`): with
  means `Dβ` for any design whose rows agree for the same card in two months (a card-specific
  calendar-month season, `cardSeason`), `(Xᵢₜ - Xᵢᵤ)(Xⱼₛ - Xⱼᵥ)` with `mon t = mon u` is
  unbiased for every `β` (`Model.UnbiasedMean`); for `i ≠ j` and months distinct across the
  two cards its expectation is `λᵢλⱼ(Γₜₛ - Γₜᵥ - Γᵤₛ + Γᵤᵥ)`. With `u = t - 12`,
  `s = t + h`, `v = s - 12` and a stationary `Γ` this is `λᵢλⱼ(2Γ(h) - Γ(h-12) - Γ(h+12))`
  for `h ≥ 1`, `h ≠ 12`. Pooled over months: `yoyPooled_unbiased`; the true expectation for
  random cells (`Cells.integral_yoy`).
* **(I4) Three cards** (`load_sq_of_three`): `Σ(i,j)Σ(i,k)/Σ(j,k) = λᵢ²Γₜₛ`; with two cards a
  loading trades against per-card dynamics (`obsCovG_eq_of_trade`, `two_cards_not_identified`).
* **(I5) AR(1)** (`ar1_identified`): `Σ₂ = φΣ₁` across cards, so `φ`, `γλᵢλⱼ` and `Cᵢⱼ` are read off
  when `φ ≠ 0`; `φ = 0` is the shock `C + γλλᵀ` (`ar1_zero_eq_shock`).
* **The shock fit under a factor** (Finding 26, `res_unbiased`, `crossHat_factor_unbiased`,
  `crossHat_ar1_two`): within-card residuals keep `λᵢλⱼ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)`; with two months
  and AR(1), `Shock.crossHat` estimates `C + (1 - φ)γλλᵀ`, neither `C` nor `C + γλλᵀ`.
* **The between-cohort spread under a factor** (`between_factor_unbiased`): it gains
  `ΣⱼxⱼvⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢxᵢλᵢaᵢ`, and `Σₖxₖ(1 - xₖ)aₖᵀGₖaₖ`; with equal weights the factor
  term is `Σⱼxⱼ(λⱼ - λ̄)²·αᵀΓα` (`between_factor_equal_weights`), so `Shock.tauHat` reads loading
  dispersion and per-card dynamics as heterogeneity.
* **The diagonal and `τ̂²` under a factor** (`CdiagHat_factor_unbiased`, `s2Hat_factor_unbiased`,
  `errCovHat_factor_unbiased`, `tauHat_factor_unbiased`): each weighted sum of squared
  residuals gains `Fⱼ(u) = Σₜuⱼₜ(λⱼ²(eₜ - aⱼ)ᵀΓ(eₜ - aⱼ) + (eₜ - aⱼ)ᵀGⱼ(eₜ - aⱼ))`; Cramer's rule
  passes it on to `Ĉⱼⱼ` and `ŝⱼ²`, and `τ̂²` collects the spread's extra term minus the
  plugged-in biases of `Σ̂`. With independent months `Γ = γI`: `Ĉⱼⱼ` reads `Cⱼⱼ + γλⱼ²` and `ŝⱼ²`
  stays unbiased (`CdiagHat_s2Hat_indep`).
* **Henderson III / MINQUE given the shape** (`Model.henderson_unbiased`,
  `Model.minque_unbiased`, `henderson_factor_unbiased`): for a table `ΣₗθₗVₗ`, invariant forms
  (`QₖD = 0`) and a nonsingular system `Hₖₗ = Σ QₖVₗ`, `θ̂ = H⁻¹(quad Qₖ X)ₖ` is unbiased for every
  `θ` and `β`; MINQUE's `RVₖR` are such forms. Given `Γ = γΓ₀` the factor table is linear in a
  symmetric `A = γλλᵀ`, `C`, `s²`, `τ²` (`covG_zero_eq_shapeTable`). The shock fit's closed forms
  `Shock.CdiagHat`, `Shock.s2Hat` are Henderson III with particular forms (`A = 0`); they are not
  yet derived from `Model.henderson_unbiased` (owner, 2026-11-21: at a third instance).
* **When the system is nonsingular** (`Model.exists_hendersonMat_det_ne_zero_iff`): some forms
  give `det H ≠ 0` iff the basis tables are linearly independent; a dependent basis is singular
  for every choice of forms (`Model.hendersonMat_det_eq_zero`). So: a card with constant volume
  makes the shock part singular, `sⱼ²` against `Cⱼⱼ` (`hendersonMat_shock_det_eq_zero`, cf.
  `Shock.not_unbiased_s2_of_const`); independent months `Γ₀ = I` make `A` and `C` one table
  (`hendersonMat_shape_one_det_eq_zero`), and no estimator separates them
  (`not_unbiased_shape_one`, `not_unbiased_factor_of_indep`; cf. `CdiagHat_s2Hat_indep`).
* **Per-card dynamics of known shape** `Gⱼ = gⱼG₀` (`covG_eq_shapeTableG`,
  `henderson_factorG_unbiased`): one more basis table `Eⱼⱼ ⊗ G₀` per card; Henderson III is
  unbiased for `gⱼ` too. White noise `G₀ = I` is the shock variance again
  (`hendersonMat_shapeG_one_det_eq_zero`).
* **When MINQUE is nonsingular** (`Model.minque_det_ne_zero_iff`): for `W ≻ 0` and symmetric
  tables, iff the projected tables `RVₖR` are independent. An independent basis and a
  full-rank design are not enough (`exists_independent_singular`): a table `DNDᵀ` in the span
  of the design is invisible to every invariant form (`Model.hendersonMat_det_eq_zero_of_design`).
  So with a card season the card level `τ²` cannot be estimated (Finding 27,
  `hendersonMat_cardSeason_det_eq_zero`).
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

/-- With per-card dynamics too. -/
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

/-! ### (I3) Lags `≥ 1` across cards see only the factor -/

section Lagged

variable (G : J → Matrix T T ℝ)

/-- **(I3) Separation**: two different cards in two different months have covariance
`λᵢλⱼΓₜₛ`: no `C`, no `s²/w`, no `τ²`, no per-card dynamics `G`. -/
theorem obsCovG_of_ne {i j : J} {t s : T} (hij : i ≠ j) (hts : t ≠ s) :
    M.obsCovG G i j t s = M.load i * M.load j * M.Γ t s := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hij, hts]

/-- The same card in two different months: `λᵢ²Γₜₛ + τ² + (Gᵢ)ₜₛ`; here the factor is
confounded with `τ²` and `G`. -/
theorem obsCovG_self_of_ne (i : J) {t s : T} (hts : t ≠ s) :
    M.obsCovG G i i t s = M.load i ^ 2 * M.Γ t s + M.τ2 + G i t s := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hts, sq]

/-- **(I3) Distinguishable**: tables that agree (whatever their `C`, `s²`, `τ²`, `G`) have the
same lagged cross-card factor part. So `λλᵀΓ ≠ λ'λ'ᵀΓ'` there means different tables: a common
factor and per-card dynamics only are told apart by the lagged cross-moments. -/
theorem factor_eq_of_obsCovG_eq {M' : Factor J T} {G' : J → Matrix T T ℝ}
    (h : ∀ i j t s, M.obsCovG G i j t s = M'.obsCovG G' i j t s) {i j : J} {t s : T}
    (hij : i ≠ j) (hts : t ≠ s) :
    M.load i * M.load j * M.Γ t s = M'.load i * M'.load j * M'.Γ t s := by
  rw [← M.obsCovG_of_ne G hij hts, ← M'.obsCovG_of_ne G' hij hts, h]

/-! ### The year-on-year lagged cross-product -/

/-- The table `obsCovG` indexed by cells `p = (j, t)`. -/
noncomputable def covG (p q : J × T) : ℝ := M.obsCovG G p.1 q.1 p.2 q.2

/-- A season per card and calendar month: `E Xⱼₜ = β_{j, mon t}`. It contains the card mean and
a season common to all cards (`Model.UnbiasedMean.of_mul`). -/
def cardSeason {Mo : Type*} [DecidableEq Mo] (mon : T → Mo) : Matrix (J × T) (J × Mo) ℝ :=
  of fun p k => if p.1 = k.1 ∧ mon p.2 = k.2 then 1 else 0

omit [DecidableEq T] in
/-- Months with the same calendar month have the same row in the season design. -/
theorem cardSeason_row {Mo : Type*} [DecidableEq Mo] {mon : T → Mo} (i : J) {t u : T}
    (h : mon t = mon u) : cardSeason (J := J) mon (i, t) = cardSeason mon (i, u) := by
  funext k; simp [cardSeason, h]

/-- The year-on-year lagged cross-product `(Xᵢₜ - Xᵢᵤ)(Xⱼₛ - Xⱼᵥ)` (`u = t - 12`,
`v = s - 12`). -/
def yoy (i j : J) (t u s v : T) (X : J × T → ℝ) : ℝ := (X (i, t) - X (i, u)) * (X (j, s) - X (j, v))

/-- **The year-on-year cross-product is unbiased for every `β`** under any design whose rows
agree for card `i` in months `t`, `u` (e.g. `cardSeason` with `mon t = mon u`). -/
theorem yoy_unbiased [Fintype J] [Fintype T] {B : Type*} [Fintype B] (D : Matrix (J × T) B ℝ)
    (i j : J) {t u : T} (s v : T) (hD : D (i, t) = D (i, u)) :
    Model.UnbiasedMean (M.covG G) D (yoy i j t u s v)
      (M.obsCovG G i j t s - M.obsCovG G i j t v - M.obsCovG G i j u s + M.obsCovG G i j u v) :=
  Model.unbiasedMean_diff_mul (M.covG G) D hD

/-- **Its expectation across cards**: for `i ≠ j` and months distinct across the two cards,
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
quadruples `k = (tₖ, uₖ, sₖ, vₖ)` (e.g. all pairs at lag `h` in the overlap of the two cards'
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
the cards and `D` equal in rows `(i, t)`, `(i, u)`. No distribution is assumed. -/
theorem integral_yoy [Fintype J] [Fintype T] (X : Cells (M.obsCovG G) D β P) {i j : J}
    (hij : i ≠ j) {t u s v : T} (hD : D (i, t) = D (i, u)) (hts : t ≠ s) (htv : t ≠ v)
    (hus : u ≠ s) (huv : u ≠ v) :
    ∫ ω, yoy i j t u s v (fun p => X.X p ω) ∂P
      = M.load i * M.load j * (M.Γ t s - M.Γ t v - M.Γ u s + M.Γ u v) :=
  (M.yoy_unbiased_factor G D hij hD hts htv hus huv).integral_eq X.X β X.memLp X.mean
    fun p q => X.cov p q

end Cells

/-! ### (I4) Individual loadings need three cards -/

section Loadings

variable (G : J → Matrix T T ℝ)

/-- **(I4) Three cards identify a loading**: for distinct cards `i, j, k` with `λⱼ, λₖ ≠ 0` and
months `t ≠ s`, `Σ(i,j)Σ(i,k)/Σ(j,k) = λᵢ²Γₜₛ` (Anderson–Rubin), whatever `C`, `s²`, `τ²`, `G`. -/
theorem load_sq_of_three {i j k : J} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : M.load j ≠ 0) (hk : M.load k ≠ 0) {t s : T} (hts : t ≠ s) :
    M.obsCovG G i j t s * M.obsCovG G i k t s / M.obsCovG G j k t s
      = M.load i ^ 2 * M.Γ t s := by
  rw [M.obsCovG_of_ne G hij hts, M.obsCovG_of_ne G hik hts, M.obsCovG_of_ne G hjk hts]
  by_cases hΓ : M.Γ t s = 0
  · simp [hΓ]
  · field_simp

/-- **Trading a loading against per-card dynamics**: two models that differ only in their
loadings and per-card dynamics have the same table if the cross products `λᵢλⱼ` (`i ≠ j`) agree
and `Gᵢ + λᵢ²Γ` agrees for every card. -/
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

/-- Two cards, two months, `Γ = I`, no shock, unit noise and `τ² = 1`; loadings `l`. -/
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

/-- **(I4) Two cards do not identify the loadings**: loadings `(2, 1/2)` with per-card dynamics
`(0, (3/4)I)` and loadings `(1, 1)` with `(3I, 0)` (all `⪰ 0`) give the same table, but
`λ₀² = 4` against `1`. -/
theorem two_cards_not_identified :
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

/-- Under an AR(1) factor, two different cards at lag `h = s - t ≥ 1` have covariance
`λᵢλⱼγφʰ`. -/
theorem obsCovG_ar1 (hΓ : M.Γ = ar1 N γ φ) {i j : J} (hij : i ≠ j) {t s : Fin N}
    (hts : t < s) : M.obsCovG G i j t s = M.load i * M.load j * γ * φ ^ ((s : ℕ) - t) := by
  rw [M.obsCovG_of_ne G hij hts.ne, hΓ, ar1, of_apply]
  simp only [show (t : ℕ) ≤ s from Fin.le_def.mp hts.le, ite_true]
  ring

/-- At lag `0`, two different cards have covariance `γλᵢλⱼ + Cᵢⱼ`. -/
theorem obsCovG_ar1_lag0 (hΓ : M.Γ = ar1 N γ φ) {i j : J} (hij : i ≠ j) (t : Fin N) :
    M.obsCovG G i j t t = M.load i * M.load j * γ + M.C i j := by
  simp [obsCovG, obsCov, Shock.obsCov, toShock, hΓ, ar1, hij]

/-- **(I5) `φ`, `γλᵢλⱼ` and `Cᵢⱼ` from the cross-moments**: with `N ≥ 3` months and two
different cards, `S₂ = φS₁` (lags `2` and `1` from month `0`); if `φ ≠ 0` and `γλᵢλⱼ ≠ 0`,
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
`dᵢⱼₜCᵢⱼ + δᵢⱼhᵢₜsᵢ²` plus `λᵢλⱼ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)` plus, on one card, `(eₜ - aᵢ)ᵀGᵢ(eₜ - aᵢ)`:
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
factor term `Σⱼ xⱼ vⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢ xᵢλᵢaᵢ`, plus `Σₖ xₖ(1 - xₖ)aₖᵀGₖaₖ`: per-card
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
  -- The per-card part: `Σⱼ xⱼcⱼₖ² = xₖ(1 - xₖ)`.
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

/-- What the factor and the per-card dynamics add to `E[rⱼₜ²]`:
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

/-- What the factor and the per-card dynamics add to the between-cohort spread
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

/-- **`τ̂²` under a factor** is unbiased for `τ² + tauBias`: the factor and the per-card
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

/-- **Independent months: the factor is a rank-one shock.** With `Γ = γI` and no per-card
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

/-! ### Henderson III and MINQUE for a table linear in its parameters -/

namespace Model

section Henderson

variable {J T L B : Type*} [Fintype J] [Fintype T] [Fintype L] [DecidableEq L] [Fintype B]

/-- A covariance table linear in parameters `θ`: `Σₗ θₗVₗ`. -/
def linTable (V : L → Matrix (J × T) (J × T) ℝ) (θ : L → ℝ) : J × T → J × T → ℝ :=
  fun p q => ∑ l, θ l * V l p q

/-- The Henderson III system for forms `Qₖ`: `Hₖₗ = Σₚq (Qₖ)ₚq(Vₗ)ₚq`, so that
`E quad Qₖ = (Hθ)ₖ` when the forms annihilate the design. -/
def hendersonMat (Q V : L → Matrix (J × T) (J × T) ℝ) : Matrix L L ℝ :=
  of fun k l => ∑ p, ∑ q, Q k p q * V l p q

/-- **Henderson III**: equate the forms to their expectations and solve,
`θ̂ = H⁻¹(quad Qₖ X)ₖ`. -/
noncomputable def henderson (Q V : L → Matrix (J × T) (J × T) ℝ) (X : J × T → ℝ) : L → ℝ :=
  (hendersonMat Q V)⁻¹ *ᵥ fun k => quad (Q k) X

omit [DecidableEq L] in
/-- A form is linear in its matrix: `quad (Σₖ cₖQₖ) = Σₖ cₖ quad Qₖ`. -/
lemma quad_sum (c : L → ℝ) (Q : L → Matrix (J × T) (J × T) ℝ) (X : J × T → ℝ) :
    quad (fun p q => ∑ k, c k * Q k p q) X = ∑ k, c k * quad (Q k) X := by
  simp only [quad, sum_mul, mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun q _ => sum_congr rfl fun k _ => by ring

omit [DecidableEq L] in
/-- Regrouping `Σₚq (Σₖ cₖFₖ)ₚq (Σₘ bₘGₘ)ₚq` as `Σₖₘ cₖbₘ Σₚq (Fₖ)ₚq(Gₘ)ₚq`. -/
lemma sum_lin_mul_lin (c b : L → ℝ) (F V : L → Matrix (J × T) (J × T) ℝ) :
    ∑ p, ∑ q, (∑ k, c k * F k p q) * (∑ m, b m * V m p q)
      = ∑ k, ∑ m, c k * b m * ∑ p, ∑ q, F k p q * V m p q := by
  calc _ = ∑ p, ∑ q, ∑ k, ∑ m, c k * b m * (F k p q * V m p q) :=
        sum_congr rfl fun p _ => sum_congr rfl fun q _ => by
          rw [sum_mul_sum]
          exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    _ = ∑ k, ∑ p, ∑ q, ∑ m, c k * b m * (F k p q * V m p q) :=
        (sum_congr rfl fun p _ => sum_comm).trans sum_comm
    _ = ∑ k, ∑ m, ∑ p, ∑ q, c k * b m * (F k p q * V m p q) :=
        sum_congr rfl fun k _ =>
          (sum_congr rfl fun p _ => sum_comm).trans sum_comm
    _ = _ := by simp only [mul_sum]

/-- `quad Q x = xᵀQx`. -/
lemma quad_eq_dotProduct (Q : Matrix (J × T) (J × T) ℝ) (x : J × T → ℝ) :
    quad Q x = x ⬝ᵥ (Q *ᵥ x) := by
  simp only [quad, dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

/-- **Invariance**: a form with `QD = 0` vanishes at every mean `Dβ`. -/
lemma quad_design_eq_zero {D : Matrix (J × T) B ℝ} {Q : Matrix (J × T) (J × T) ℝ}
    (hQ : Q * D = 0) (β : B → ℝ) : quad Q (D *ᵥ β) = 0 := by
  rw [quad_eq_dotProduct, mulVec_mulVec, hQ, zero_mulVec, dotProduct_zero]

/-- **Henderson III is unbiased** (Henderson 1953; Searle, Casella & McCulloch 1992, ch. 5):
for a table linear in its parameters, invariant forms (`QₖD = 0`) and a nonsingular system
`H`, every `θ̂ₗ` is unbiased for `θₗ`, for every `θ` and every fixed effect `β`. The
estimator is a quadratic form, distribution-free; it need not be nonnegative. -/
theorem henderson_unbiased {Q V : L → Matrix (J × T) (J × T) ℝ} {D : Matrix (J × T) B ℝ}
    (hQ : ∀ k, Q k * D = 0) (hH : IsUnit (hendersonMat Q V).det) (θ : L → ℝ) (l : L) :
    UnbiasedMean (linTable V θ) D (fun X => henderson Q V X l) (θ l) := by
  set Hi := (hendersonMat Q V)⁻¹ with hHi
  refine ⟨fun p q => ∑ k, Hi l k * Q k p q, fun X => ?_, fun β => ?_⟩
  · rw [quad_sum]
    simp only [henderson, mulVec, dotProduct, ← hHi]
  · rw [EcovMean_eq, quad_sum]
    simp only [quad_design_eq_zero (hQ _), mul_zero, sum_const_zero, add_zero, linTable]
    rw [sum_lin_mul_lin]
    have h : ∑ k, ∑ m, Hi l k * θ m * ∑ p, ∑ q, Q k p q * V m p q
        = (Hi *ᵥ (hendersonMat Q V *ᵥ θ)) l := by
      simp only [mulVec, dotProduct, hendersonMat, of_apply]
      exact sum_congr rfl fun k _ => by
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by ring
    rw [h, mulVec_mulVec, hHi, nonsing_inv_mul _ hH, one_mulVec]


/-! #### When is the system nonsingular? -/

omit [DecidableEq L] in
/-- `H` applied to a parameter vector `c` pairs each form with the table `Σₗ cₗVₗ`. -/
lemma hendersonMat_mulVec (Q V : L → Matrix (J × T) (J × T) ℝ) (c : L → ℝ) :
    hendersonMat Q V *ᵥ c = fun k => ∑ p, ∑ q, Q k p q * linTable V c p q := by
  funext k
  simp only [mulVec, dotProduct, hendersonMat, of_apply, linTable, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun q _ => sum_congr rfl fun l _ => by ring

/-- **A dependent basis makes the system singular, whatever the forms**: if `Σₗ cₗVₗ = 0` for
some `c ≠ 0`, two parameter vectors `θ` and `θ + c` give the same table, and `Hc = 0`. -/
theorem hendersonMat_det_eq_zero {Q V : L → Matrix (J × T) (J × T) ℝ} {c : L → ℝ} (hc : c ≠ 0)
    (h : linTable V c = 0) : (hendersonMat Q V).det = 0 :=
  exists_mulVec_eq_zero_iff.mp ⟨c, hc, by
    rw [hendersonMat_mulVec, h]; funext k; simp⟩

/-- **Two proportional basis tables make the system singular**: `V l' = a • V l`, `l ≠ l'`. -/
theorem hendersonMat_det_eq_zero_of_smul {Q V : L → Matrix (J × T) (J × T) ℝ} {l l' : L}
    (hl : l ≠ l') (a : ℝ) (h : V l' = a • V l) : (hendersonMat Q V).det = 0 := by
  refine hendersonMat_det_eq_zero (c := Pi.single l' 1 - Pi.single l a) ?_ ?_
  · intro h0
    have := congrFun h0 l'
    simp [hl.symm] at this
  · funext p q
    simp only [linTable, Pi.sub_apply, sub_mul, sum_sub_distrib, Pi.single_apply, ite_mul,
      one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, h, Matrix.smul_apply, smul_eq_mul]
    simp

omit [DecidableEq L] in
/-- `cᵀ H c = Σₚq (Σₖ cₖQₖ)ₚq (Σₗ cₗVₗ)ₚq`. -/
lemma dotProduct_hendersonMat (Q V : L → Matrix (J × T) (J × T) ℝ) (c : L → ℝ) :
    c ⬝ᵥ (hendersonMat Q V *ᵥ c) = ∑ p, ∑ q, linTable Q c p q * linTable V c p q := by
  rw [hendersonMat_mulVec]
  simp only [dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  simp only [linTable, sum_mul]
  exact sum_congr rfl fun l _ => by ring

omit [DecidableEq L] in
/-- `cᵀ H(V, V) c = Σₚq (Σₗ cₗVₗ)ₚq²`: with the basis tables themselves as forms, `H` is the
Gram matrix of the tables. -/
lemma dotProduct_hendersonMat_self (V : L → Matrix (J × T) (J × T) ℝ) (c : L → ℝ) :
    c ⬝ᵥ (hendersonMat V V *ᵥ c) = ∑ p, ∑ q, linTable V c p q ^ 2 := by
  simp only [dotProduct_hendersonMat, sq]

/-- **Independent basis tables give a nonsingular system** with the tables as forms (`Qₖ = Vₖ`,
the Gram matrix). -/
theorem hendersonMat_self_det_ne_zero {V : L → Matrix (J × T) (J × T) ℝ}
    (hV : ∀ c, linTable V c = 0 → c = 0) : (hendersonMat V V).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc, h0⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  apply hc (hV c _)
  have hsq := dotProduct_hendersonMat_self V c
  rw [h0, dotProduct_zero] at hsq
  have hp := (sum_eq_zero_iff_of_nonneg fun p _ =>
    sum_nonneg fun q _ => sq_nonneg (linTable V c p q)).mp hsq.symm
  funext p q
  have := (sum_eq_zero_iff_of_nonneg fun q _ => sq_nonneg (linTable V c p q)).mp
    (hp p (mem_univ _)) q (mem_univ _)
  simpa using this

/-- **When some system is nonsingular**: there are forms with `det H ≠ 0` iff the basis tables
are linearly independent (no `c ≠ 0` with `Σₗ cₗVₗ = 0`), i.e. iff the table determines `θ`.
Invariance (`QₖD = 0`) can only lose rank on top of this. -/
theorem exists_hendersonMat_det_ne_zero_iff {V : L → Matrix (J × T) (J × T) ℝ} :
    (∃ Q, (hendersonMat Q V).det ≠ 0) ↔ ∀ c, linTable V c = 0 → c = 0 := by
  refine ⟨fun ⟨Q, hQ⟩ c hc => ?_, fun hV => ⟨V, hendersonMat_self_det_ne_zero hV⟩⟩
  by_contra hne
  exact hQ (hendersonMat_det_eq_zero hne hc)

/-- `Σₚq QₚqYₚq = tr(QᵀY)`. -/
lemma sum_mul_eq_trace (Q Y : Matrix (J × T) (J × T) ℝ) :
    ∑ p, ∑ q, Q p q * Y p q = trace (Qᵀ * Y) := by
  simp only [trace, Matrix.diag_apply]
  exact sum_comm

/-- **A basis table in the span of the design is lost to invariant forms**: if
`V l = DNDᵀ`, then `Σₚq (Qₖ)ₚq(V l)ₚq = tr(QₖᵀDNDᵀ) = 0` whenever `QₖD = 0`, so the column `l`
of `H` vanishes and the system is singular, however independent the basis. Such a component
is confounded with the fixed effects (e.g. the card level `τ²` under card-specific means). -/
theorem hendersonMat_det_eq_zero_of_design {Q V : L → Matrix (J × T) (J × T) ℝ}
    {D : Matrix (J × T) B ℝ} (hQ : ∀ k, Q k * D = 0) {l : L} (N : Matrix B B ℝ)
    (hV : V l = D * N * Dᵀ) : (hendersonMat Q V).det = 0 := by
  refine det_eq_zero_of_column_eq_zero l fun k => ?_
  have h0 : Dᵀ * (Q k)ᵀ = 0 := by rw [← transpose_mul, hQ k, transpose_zero]
  simp only [hendersonMat, of_apply]
  rw [sum_mul_eq_trace, hV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, trace_zero]

variable [DecidableEq J] [DecidableEq T] [DecidableEq B]

/-- The MINQUE projection for a prior table `W` (Rao 1971):
`R = W⁻¹ - W⁻¹D(DᵀW⁻¹D)⁻¹DᵀW⁻¹`. -/
noncomputable def minqueR (W : Matrix (J × T) (J × T) ℝ) (D : Matrix (J × T) B ℝ) :
    Matrix (J × T) (J × T) ℝ :=
  W⁻¹ - W⁻¹ * D * (Dᵀ * W⁻¹ * D)⁻¹ * Dᵀ * W⁻¹

/-- `RD = 0` when `DᵀW⁻¹D` is nonsingular. -/
lemma minqueR_mul (W : Matrix (J × T) (J × T) ℝ) {D : Matrix (J × T) B ℝ}
    (hD : IsUnit (Dᵀ * W⁻¹ * D).det) : minqueR W D * D = 0 := by
  have h : (Dᵀ * W⁻¹ * D)⁻¹ * (Dᵀ * W⁻¹ * D) = 1 := nonsing_inv_mul _ hD
  rw [minqueR, Matrix.sub_mul, sub_eq_zero]
  calc W⁻¹ * D = W⁻¹ * D * ((Dᵀ * W⁻¹ * D)⁻¹ * (Dᵀ * W⁻¹ * D)) := by rw [h, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The MINQUE forms `Qₖ = RVₖR`. -/
noncomputable def minqueForms (W : Matrix (J × T) (J × T) ℝ) (D : Matrix (J × T) B ℝ)
    (V : L → Matrix (J × T) (J × T) ℝ) (k : L) : Matrix (J × T) (J × T) ℝ :=
  minqueR W D * V k * minqueR W D

/-- **MINQUE is a Henderson III estimator**, so unbiased: with the forms `RVₖR` for any prior
table `W` (`DᵀW⁻¹D` and the system nonsingular), `θ̂ₗ` is unbiased for `θₗ`. Iterating the
prior is REML; the minimum-norm property is not used here. -/
theorem minque_unbiased (W : Matrix (J × T) (J × T) ℝ) {D : Matrix (J × T) B ℝ}
    {V : L → Matrix (J × T) (J × T) ℝ} (hD : IsUnit (Dᵀ * W⁻¹ * D).det)
    (hH : IsUnit (hendersonMat (minqueForms W D V) V).det) (θ : L → ℝ) (l : L) :
    UnbiasedMean (linTable V θ) D (fun X => henderson (minqueForms W D V) V X l) (θ l) :=
  henderson_unbiased (fun k => by rw [minqueForms, Matrix.mul_assoc, minqueR_mul W hD,
    Matrix.mul_zero]) hH θ l

/-! #### When is the MINQUE system nonsingular? -/

omit [Fintype L] [DecidableEq L] [DecidableEq J] [DecidableEq T] in
/-- A positive semidefinite real matrix is `BᵀB` (from the spectral theorem). -/
lemma PosSemidef.exists_eq_transpose_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {W : Matrix n n ℝ} (hW : W.PosSemidef) : ∃ B : Matrix n n ℝ, W = Bᵀ * B := by
  set U : Matrix n n ℝ := (hW.1.eigenvectorUnitary : Matrix n n ℝ)
  refine ⟨diagonal (fun i => Real.sqrt (hW.1.eigenvalues i)) * Uᵀ, ?_⟩
  have h := hW.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
  have he : (fun i => Real.sqrt (hW.1.eigenvalues i) * Real.sqrt (hW.1.eigenvalues i))
      = RCLike.ofReal ∘ hW.1.eigenvalues := by
    funext i; simp [Real.mul_self_sqrt (hW.eigenvalues_nonneg i)]
  rw [he, ← Matrix.mul_assoc]
  convert h using 2
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

omit [Fintype L] [DecidableEq L] in
/-- `DᵀR = 0` when `DᵀW⁻¹D` is nonsingular. -/
lemma transpose_mul_minqueR (W : Matrix (J × T) (J × T) ℝ) {D : Matrix (J × T) B ℝ}
    (hD : IsUnit (Dᵀ * W⁻¹ * D).det) : Dᵀ * minqueR W D = 0 := by
  have h : (Dᵀ * W⁻¹ * D) * (Dᵀ * W⁻¹ * D)⁻¹ = 1 := mul_nonsing_inv _ hD
  rw [minqueR, Matrix.mul_sub, sub_eq_zero]
  calc Dᵀ * W⁻¹ = (Dᵀ * W⁻¹ * D) * (Dᵀ * W⁻¹ * D)⁻¹ * (Dᵀ * W⁻¹) := by rw [h, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [Fintype L] [DecidableEq L] in
/-- `RWR = R`. -/
lemma minqueR_mul_mul {W : Matrix (J × T) (J × T) ℝ} (hW : IsUnit W.det) {D : Matrix (J × T) B ℝ}
    (hD : IsUnit (Dᵀ * W⁻¹ * D).det) : minqueR W D * W * minqueR W D = minqueR W D := by
  have hWW : W⁻¹ * W = 1 := nonsing_inv_mul _ hW
  have h0 := transpose_mul_minqueR W hD
  calc minqueR W D * W * minqueR W D
        = W⁻¹ * W * minqueR W D - W⁻¹ * D * (Dᵀ * W⁻¹ * D)⁻¹ * (Dᵀ * (W⁻¹ * W) * minqueR W D) := by
          conv_lhs => arg 1; arg 1; rw [minqueR]
          simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = minqueR W D := by rw [hWW, Matrix.mul_one, h0, Matrix.one_mul, Matrix.mul_zero, sub_zero]

omit [Fintype L] [DecidableEq L] in
/-- `R` is symmetric for a symmetric prior `W`. -/
lemma minqueR_transpose {W : Matrix (J × T) (J × T) ℝ} (hW : Wᵀ = W) (D : Matrix (J × T) B ℝ) :
    (minqueR W D)ᵀ = minqueR W D := by
  have hWi : (W⁻¹)ᵀ = W⁻¹ := by rw [transpose_nonsing_inv, hW]
  have hG : ((Dᵀ * W⁻¹ * D)⁻¹)ᵀ = (Dᵀ * W⁻¹ * D)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_mul, transpose_transpose, hWi,
      Matrix.mul_assoc]
  rw [minqueR, transpose_sub, hWi, transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    hWi, hG, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- **When the MINQUE system is nonsingular** (Rao 1971): for a positive definite prior `W`,
`DᵀW⁻¹D` nonsingular and symmetric basis tables, `det H ≠ 0` iff the projected tables `RVₖR`
are linearly independent. `H` is the Gram matrix of the `RVₖR` in the `W`-weighted trace
inner product. An independent basis is not enough (`hendersonMat_det_eq_zero_of_design`): a
table in the span of the design projects to `0`. -/
theorem minque_det_ne_zero_iff {W : Matrix (J × T) (J × T) ℝ} (hW : W.PosDef)
    {D : Matrix (J × T) B ℝ} (hD : IsUnit (Dᵀ * W⁻¹ * D).det)
    {V : L → Matrix (J × T) (J × T) ℝ} (hV : ∀ k, (V k)ᵀ = V k) :
    (hendersonMat (minqueForms W D V) V).det ≠ 0
      ↔ ∀ c : L → ℝ, minqueR W D * (∑ k, c k • V k) * minqueR W D = 0 → c = 0 := by
  set R := minqueR W D with hR
  have hWt : Wᵀ = W := by
    have := hW.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hWu : IsUnit W.det := isUnit_iff_ne_zero.mpr hW.det_pos.ne'
  have hRt : Rᵀ = R := minqueR_transpose hWt D
  have hRWR : R * W * R = R := minqueR_mul_mul hWu hD
  have hlin : ∀ c : L → ℝ, linTable V c = ∑ k, c k • V k := fun c => by
    funext p q; simp [linTable, Matrix.sum_apply]
  have hlinQ : ∀ c : L → ℝ, linTable (minqueForms W D V) c = R * (∑ k, c k • V k) * R :=
    fun c => by
      funext p q
      simp only [linTable, minqueForms, ← hR]
      rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
      exact sum_congr rfl fun k _ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  -- `(Hc)ₖ = tr(RVₖR S)`, `S = Σ cₗVₗ`.
  have hHc : ∀ c : L → ℝ, hendersonMat (minqueForms W D V) V *ᵥ c
      = fun k => trace (V k * (R * (∑ l, c l • V l) * R)) := fun c => by
    rw [hendersonMat_mulVec, hlin]
    funext k
    rw [sum_mul_eq_trace, minqueForms, ← hR, transpose_mul, transpose_mul, hRt, hV,
      Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  constructor
  · intro hdet c hc
    by_contra hne
    refine hdet (exists_mulVec_eq_zero_iff.mp ⟨c, hne, ?_⟩)
    rw [hHc, hc]
    funext k
    simp
  · intro hind hdet
    obtain ⟨c, hc, h0⟩ := exists_mulVec_eq_zero_iff.mpr hdet
    apply hc (hind c _)
    set S := ∑ l, c l • V l with hS
    have hSt : Sᵀ = S := by
      rw [hS, transpose_sum]
      exact sum_congr rfl fun l _ => by rw [transpose_smul, hV]
    set N := R * S * R with hN
    have hNt : Nᵀ = N := by
      rw [hN, transpose_mul, transpose_mul, hRt, hSt, Matrix.mul_assoc]
    -- `0 = cᵀHc = tr(NS) = tr(WNWN)`.
    have htr : trace (W * N * W * N) = 0 := by
      have h1 := dotProduct_hendersonMat (minqueForms W D V) V c
      rw [h0, dotProduct_zero, hlinQ, hlin, sum_mul_eq_trace, ← hS, ← hN, hNt] at h1
      rw [h1]
      have e1 : W * N * W * N = (W * R * S * R * W * R * S) * R := by
        simp only [hN, Matrix.mul_assoc]
      have e2 : R * (W * R * S * R * W * R * S) = (R * W * R) * S * (R * W * R) * S := by
        simp only [Matrix.mul_assoc]
      rw [e1, trace_mul_comm, e2, hRWR, hN]
    obtain ⟨B', hB'⟩ := PosSemidef.exists_eq_transpose_mul_self hW.posSemidef
    set Y := B' * N * B'ᵀ with hY
    have hYt : Yᵀ = Y := by
      rw [hY, transpose_mul, transpose_mul, transpose_transpose, hNt]
      simp only [hN, Matrix.mul_assoc]
    have hY0 : Y = 0 := by
      refine trace_conjTranspose_mul_self_eq_zero_iff.mp ?_
      rw [conjTranspose_eq_transpose_of_trivial, hYt, ← htr, hY, hB',
        show B'ᵀ * B' * N * (B'ᵀ * B') * N = B'ᵀ * (B' * N * B'ᵀ * B' * N) by
          simp only [Matrix.mul_assoc], trace_mul_comm B'ᵀ]
      simp only [Matrix.mul_assoc]
    have hWNW : W * N * W = 0 := by
      rw [hB']
      calc B'ᵀ * B' * N * (B'ᵀ * B') = B'ᵀ * Y * B' := by rw [hY]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hY0, Matrix.mul_zero, Matrix.zero_mul]
    have hWi : W⁻¹ * W = 1 := nonsing_inv_mul _ hWu
    have hWi' : W * W⁻¹ = 1 := mul_nonsing_inv _ hWu
    calc N = W⁻¹ * (W * N * W) * W⁻¹ := by
          simp only [← Matrix.mul_assoc, hWi, Matrix.one_mul]
          rw [Matrix.mul_assoc, hWi', Matrix.mul_one]
      _ = 0 := by rw [hWNW, Matrix.mul_zero, Matrix.zero_mul]

end Henderson

end Model

/-! ### The factor table given its shape is linear -/

namespace Factor

section GivenShape

variable {J T B : Type*} [DecidableEq J] [DecidableEq T] (M : Factor J T) [Fintype J] [Fintype T]

/-- The parameters of the factor table given the factor's shape `Γ₀`: a symmetric `A`
(`γλλᵀ`), a symmetric `C` (both indexed by unordered pairs), `s²` per card, and `τ²`. -/
abbrev Par (J : Type*) := Sym2 J ⊕ Sym2 J ⊕ J ⊕ Unit

/-- The table given the shape `Γ₀` and volumes `w`:
`Aᵢⱼ(Γ₀)ₜₛ + δₜₛ(Cᵢⱼ + δᵢⱼsᵢ²/wᵢₜ) + τ²δᵢⱼ`, linear in `(A, C, s², τ²)`. -/
noncomputable def shapeTable (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) : J × T → J × T → ℝ := fun p q =>
  A s(p.1, q.1) * Γ₀ p.2 q.2
    + (if p.2 = q.2 then C s(p.1, q.1) + (if p.1 = q.1 then s2 p.1 / w p.1 p.2 else 0) else 0)
    + (if p.1 = q.1 then τ2 else 0)

/-- The basis tables `Vₗ`: `Eᵢⱼ ⊗ Γ₀`, `Eᵢⱼ ⊗ I`, `Eⱼⱼ ⊗ diag(1/wⱼ)`, `I ⊗ 11ᵀ`. -/
noncomputable def shapeBasis (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ) :
    Par J → Matrix (J × T) (J × T) ℝ
  | .inl z => fun p q => if s(p.1, q.1) = z then Γ₀ p.2 q.2 else 0
  | .inr (.inl z) => fun p q => if s(p.1, q.1) = z then (if p.2 = q.2 then 1 else 0) else 0
  | .inr (.inr (.inl j)) => fun p q =>
      if p.1 = j then (if q.1 = j then (if p.2 = q.2 then 1 / w j p.2 else 0) else 0) else 0
  | .inr (.inr (.inr _)) => fun p q => if p.1 = q.1 then 1 else 0

/-- The parameter vector `(A, C, s², τ²)`. -/
def shapePar (A C : Sym2 J → ℝ) (s2 : J → ℝ) (τ2 : ℝ) : Par J → ℝ :=
  Sum.elim A (Sum.elim C (Sum.elim s2 fun _ => τ2))

omit [Fintype T] in
/-- **The table given the shape is linear in its parameters**: `Σₗ θₗVₗ`. -/
theorem shapeTable_eq_linTable (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) :
    shapeTable Γ₀ w A C s2 τ2 = Model.linTable (shapeBasis Γ₀ w) (shapePar A C s2 τ2) := by
  funext p q
  simp only [Model.linTable, Fintype.sum_sum_type, shapePar, Sum.elim_inl, Sum.elim_inr,
    shapeBasis, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, Fintype.sum_unique,
    shapeTable]
  by_cases ht : p.2 = q.2 <;> by_cases hj : p.1 = q.1 <;> simp [ht, hj, div_eq_mul_inv]
  all_goals first | exact fun h => absurd h.symm hj | ring

variable [Fintype B]

/-- **Henderson III / MINQUE given the factor's shape** (literature §10h, plan item 2): for any
invariant forms (`QₖD = 0`, e.g. `minqueForms`) with a nonsingular system, `θ̂` is unbiased,
whatever the fixed effects `β`, for every parameter of the table: `Aᵢⱼ`, `Cᵢⱼ`, `sⱼ²`, `τ²`. -/
theorem henderson_shape_unbiased (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ) {D : Matrix (J × T) B ℝ}
    {Q : Par J → Matrix (J × T) (J × T) ℝ} (hQ : ∀ k, Q k * D = 0)
    (hH : IsUnit (Model.hendersonMat Q (shapeBasis Γ₀ w)).det) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) (l : Par J) :
    Model.UnbiasedMean (shapeTable Γ₀ w A C s2 τ2) D
      (fun X => Model.henderson Q (shapeBasis Γ₀ w) X l) (shapePar A C s2 τ2 l) := by
  rw [shapeTable_eq_linTable]
  exact Model.henderson_unbiased hQ hH _ l

omit [Fintype J] [Fintype T] in
/-- **The factor model given its shape** `Γ = γΓ₀` (e.g. `ar1 N 1 φ` for a known `φ`), without
per-card dynamics: its table is `shapeTable` with `A = γλλᵀ`. So Henderson III / MINQUE
(`henderson_shape_unbiased`) is unbiased for `γλᵢλⱼ`, `Cᵢⱼ`, `sⱼ²` and `τ²`. -/
theorem covG_zero_eq_shapeTable {Γ₀ : Matrix T T ℝ} {γ : ℝ} (hΓ : M.Γ = γ • Γ₀) :
    M.covG 0 = shapeTable Γ₀ M.w
      (Sym2.lift ⟨fun i j => γ * (M.load i * M.load j), fun i j => by ring⟩)
      (Sym2.lift ⟨fun i j => M.C i j, fun i j => by
        simpa using (M.C_posSemidef.1.apply i j).symm⟩) M.s2 M.τ2 := by
  funext p q
  simp only [covG, obsCovG, obsCov, Shock.obsCov, toShock, shapeTable, Sym2.lift_mk, hΓ,
    Matrix.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.zero_apply]
  by_cases ht : p.2 = q.2 <;> by_cases hj : p.1 = q.1 <;> simp [ht, hj] <;> ring

/-- **Henderson III / MINQUE for the factor model given its shape** `Γ = γΓ₀`: unbiased for
`γλᵢλⱼ` (on `s(i, j)`), `Cᵢⱼ`, `sⱼ²` and `τ²`, whatever the fixed effects. -/
theorem henderson_factor_unbiased {Γ₀ : Matrix T T ℝ} {γ : ℝ} (hΓ : M.Γ = γ • Γ₀)
    {D : Matrix (J × T) B ℝ} {Q : Par J → Matrix (J × T) (J × T) ℝ} (hQ : ∀ k, Q k * D = 0)
    (hH : IsUnit (Model.hendersonMat Q (shapeBasis Γ₀ M.w)).det) :
    (∀ i j, Model.UnbiasedMean (M.covG 0) D
        (fun X => Model.henderson Q (shapeBasis Γ₀ M.w) X (.inl s(i, j))) (γ * (M.load i * M.load j)))
      ∧ (∀ i j, Model.UnbiasedMean (M.covG 0) D
        (fun X => Model.henderson Q (shapeBasis Γ₀ M.w) X (.inr (.inl s(i, j)))) (M.C i j))
      ∧ (∀ j, Model.UnbiasedMean (M.covG 0) D
        (fun X => Model.henderson Q (shapeBasis Γ₀ M.w) X (.inr (.inr (.inl j)))) (M.s2 j))
      ∧ Model.UnbiasedMean (M.covG 0) D
        (fun X => Model.henderson Q (shapeBasis Γ₀ M.w) X (.inr (.inr (.inr ())))) M.τ2 := by
  rw [M.covG_zero_eq_shapeTable hΓ]
  refine ⟨fun i j => ?_, fun i j => ?_, fun j => ?_, ?_⟩ <;>
    exact (henderson_shape_unbiased Γ₀ M.w hQ hH _ _ _ _ _).congr (fun _ => rfl)
      (by simp [shapePar])

end GivenShape

/-! ### When is the shape system nonsingular? -/

section Singular

variable {J T B : Type*} [DecidableEq J] [DecidableEq T] [Fintype J] [Fintype T]

/-- The parameters of the shock part (`A = 0`): `C`, `s²`, `τ²`. -/
abbrev ShockPar (J : Type*) := Sym2 J ⊕ J ⊕ Unit

/-- The basis tables of the shock part: `Eᵢⱼ ⊗ I`, `Eⱼⱼ ⊗ diag(1/wⱼ)`, `I ⊗ 11ᵀ` (the shape basis
without the factor). -/
noncomputable def shockBasis (w : J → T → ℝ) : ShockPar J → Matrix (J × T) (J × T) ℝ :=
  fun l => shapeBasis 0 w (.inr l)

omit [Fintype J] [Fintype T] in
/-- At a constant volume `wⱼ`, the process-noise table of card `j` is `1/wⱼ` times its shock
variance table: `Eⱼⱼ ⊗ diag(1/wⱼ) = (1/wⱼ)(Eⱼⱼ ⊗ I)`. -/
theorem shapeBasis_s2_eq_smul (Γ₀ : Matrix T T ℝ) {w : J → T → ℝ} {j : J} {c : ℝ}
    (hw : ∀ t, w j t = c) :
    shapeBasis Γ₀ w (.inr (.inr (.inl j))) = (1 / c) • shapeBasis Γ₀ w (.inr (.inl s(j, j))) := by
  funext p q
  rw [Matrix.smul_apply]
  simp only [shapeBasis, smul_eq_mul, Sym2.eq_iff]
  by_cases hp : p.1 = j <;> by_cases hq : q.1 = j <;> by_cases ht : p.2 = q.2 <;>
    simp [hp, hq, ht, hw]

/-- **The shock part needs volume variation** (cf. `Shock.not_unbiased_s2_of_const`): if card
`j` has the same volume in every month, the Henderson III system of the shock part (`A = 0`)
is singular for every choice of forms, since `sⱼ²` and `Cⱼⱼ` enter the table only through
`Cⱼⱼ + sⱼ²/wⱼ`. -/
theorem hendersonMat_shock_det_eq_zero [Nonempty T] (w : J → T → ℝ) {j : J}
    (hw : ∀ t t', w j t = w j t') (Q : ShockPar J → Matrix (J × T) (J × T) ℝ) :
    (Model.hendersonMat Q (shockBasis w)).det = 0 := by
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  exact Model.hendersonMat_det_eq_zero_of_smul (l := .inl s(j, j)) (l' := .inr (.inl j))
    (by simp) _ (shapeBasis_s2_eq_smul 0 fun t => hw t t₀)

/-- With the factor too: a constant volume of one card makes the full shape system singular,
whatever `Γ₀` and the forms. -/
theorem hendersonMat_shape_det_eq_zero_of_const [Nonempty T] (Γ₀ : Matrix T T ℝ)
    (w : J → T → ℝ) {j : J} (hw : ∀ t t', w j t = w j t') (Q : Par J → Matrix (J × T) (J × T) ℝ) :
    (Model.hendersonMat Q (shapeBasis Γ₀ w)).det = 0 := by
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  exact Model.hendersonMat_det_eq_zero_of_smul (l := .inr (.inl s(j, j)))
    (l' := .inr (.inr (.inl j))) (by simp) _ (shapeBasis_s2_eq_smul Γ₀ fun t => hw t t₀)

omit [Fintype J] [Fintype T] in
/-- With independent months `Γ₀ = I` the factor table of a pair is its shock table:
`Eᵢⱼ ⊗ I` twice. -/
theorem shapeBasis_one_inl (w : J → T → ℝ) (z : Sym2 J) :
    shapeBasis (1 : Matrix T T ℝ) w (.inl z) = shapeBasis 1 w (.inr (.inl z)) := by
  funext p q
  simp [shapeBasis, Matrix.one_apply]

/-- **Independent months: `A` and `C` are not separable by Henderson III** (the rank-one shock,
cf. `CdiagHat_s2Hat_indep`): with `Γ₀ = I` the system is singular for every choice of forms. -/
theorem hendersonMat_shape_one_det_eq_zero [Nonempty J] (w : J → T → ℝ)
    (Q : Par J → Matrix (J × T) (J × T) ℝ) :
    (Model.hendersonMat Q (shapeBasis (1 : Matrix T T ℝ) w)).det = 0 := by
  obtain ⟨j⟩ := (inferInstance : Nonempty J)
  exact Model.hendersonMat_det_eq_zero_of_smul (l := .inr (.inl s(j, j))) (l' := .inl s(j, j))
    (by simp) 1 (by rw [one_smul, shapeBasis_one_inl])

omit [Fintype J] [Fintype T] in
/-- With `Γ₀ = I` the table depends on `A` and `C` only through `A + C`. -/
theorem shapeTable_one_eq (w : J → T → ℝ) (A C : Sym2 J → ℝ) (s2 : J → ℝ) (τ2 : ℝ) :
    shapeTable (1 : Matrix T T ℝ) w A C s2 τ2 = shapeTable 1 w 0 (A + C) s2 τ2 := by
  funext p q
  simp only [shapeTable, Matrix.one_apply, Pi.zero_apply, Pi.add_apply]
  split_ifs <;> ring

omit [Fintype J] [Fintype T] in
/-- The shape table is symmetric when `Γ₀` is. -/
theorem shapeTable_symm {Γ₀ : Matrix T T ℝ} (hΓ₀ : ∀ t s, Γ₀ s t = Γ₀ t s) (w : J → T → ℝ)
    (A C : Sym2 J → ℝ) (s2 : J → ℝ) (τ2 : ℝ) (p q : J × T) :
    shapeTable Γ₀ w A C s2 τ2 q p = shapeTable Γ₀ w A C s2 τ2 p q := by
  simp only [shapeTable, Sym2.eq_swap (a := q.1), hΓ₀]
  by_cases ht : p.2 = q.2 <;> by_cases hj : p.1 = q.1
  · simp [ht, hj]
  · simp [ht, hj, Ne.symm hj]
  · simp [ht, hj, Ne.symm ht]
  · simp [ht, hj, Ne.symm ht, Ne.symm hj]

variable [Fintype B]

/-- **Independent months: no estimator separates `A` from `C`.** With `Γ₀ = I`, no function of
the data is unbiased for `A_z` for every parameter set (whatever the design): `(A, C)` and
`(A + 1, C - 1)` give the same table. -/
theorem not_unbiased_shape_one (w : J → T → ℝ) (D : Matrix (J × T) B ℝ) (z : Sym2 J)
    (f : (J × T → ℝ) → ℝ) :
    ¬ ∀ (A C : Sym2 J → ℝ) (s2 : J → ℝ) (τ2 : ℝ),
      Model.UnbiasedMean (shapeTable (1 : Matrix T T ℝ) w A C s2 τ2) D f (A z) := by
  intro H
  have h0 := H 0 0 1 1
  have h1 := H 1 (-1) 1 1
  rw [shapeTable_one_eq] at h0 h1
  simp only [add_neg_cancel, add_zero] at h0 h1
  have := Model.UnbiasedMean.unique (shapeTable_symm (fun t s => by
    simp [Matrix.one_apply, eq_comm]) w _ _ _ _) h0 h1
  simp at this

/-- **Independent months: the factor is not identified from the shock** (the factor-model form
of `not_unbiased_shape_one`): if `M` has `Γ = γI` and `γλᵢλⱼ ≠ 0`, no function of the data is
unbiased for `γ'λ'ᵢλ'ⱼ` in every model `M'` with `Γ' = γ'I`, whatever the design: moving the
factor into the shock (`factorToShock`) keeps the table and gives `0`. -/
theorem not_unbiased_factor_of_indep (M : Factor J T) [Nonempty T] {γ : ℝ}
    (hΓ : M.Γ = γ • (1 : Matrix T T ℝ)) {i j : J} (hne : γ * (M.load i * M.load j) ≠ 0)
    (D : Matrix (J × T) B ℝ) (f : (J × T → ℝ) → ℝ) :
    ¬ ∀ (M' : Factor J T) (γ' : ℝ), M'.Γ = γ' • (1 : Matrix T T ℝ) →
      Model.UnbiasedMean (M'.covG 0) D f (γ' * (M'.load i * M'.load j)) := by
  intro H
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  have hγ : 0 ≤ γ := by simpa [hΓ] using M.Γ_posSemidef.diag_nonneg (i := t₀)
  set M₀ := M.factorToShock γ hγ
  have h1 := H M γ hΓ
  have h0 := H M₀ 0 (by simp [M₀, factorToShock])
  rw [M.covG_zero_eq_shapeTable hΓ, shapeTable_one_eq] at h1
  rw [M₀.covG_zero_eq_shapeTable (Γ₀ := 1) (γ := 0) (by simp [M₀, factorToShock]),
    shapeTable_one_eq] at h0
  have hT : shapeTable (1 : Matrix T T ℝ) M₀.w 0
      ((Sym2.lift ⟨fun i j => 0 * (M₀.load i * M₀.load j), fun i j => by ring⟩) +
        Sym2.lift ⟨fun i j => M₀.C i j, fun i j => by
          simpa using (M₀.C_posSemidef.1.apply i j).symm⟩) M₀.s2 M₀.τ2
      = shapeTable 1 M.w 0
      ((Sym2.lift ⟨fun i j => γ * (M.load i * M.load j), fun i j => by ring⟩) +
        Sym2.lift ⟨fun i j => M.C i j, fun i j => by
          simpa using (M.C_posSemidef.1.apply i j).symm⟩) M.s2 M.τ2 := by
    congr 1
    funext z
    induction z using Sym2.ind with
    | _ a b =>
      simp only [Pi.add_apply, Sym2.lift_mk, M₀, factorToShock, Matrix.add_apply,
        Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      ring
  rw [hT] at h0
  have := Model.UnbiasedMean.unique (shapeTable_symm (fun t s => by
    simp [Matrix.one_apply, eq_comm]) _ _ _ _ _) h1 h0
  simp only [zero_mul] at this
  exact hne this

omit [Fintype T] in
/-- The card-level table `I ⊗ 11ᵀ` is `DEDᵀ` for the card season `D = cardSeason mon`, with
`E_{(j,m),(j',m')} = δⱼⱼ'`: the card level lies in the span of card-specific means. -/
theorem shapeBasis_tau_eq_cardSeason {Mo : Type*} [Fintype Mo] [DecidableEq Mo] (Γ₀ : Matrix T T ℝ)
    (w : J → T → ℝ) (mon : T → Mo) :
    shapeBasis Γ₀ w (.inr (.inr (.inr ()))) = cardSeason (J := J) mon
      * (of fun k k' : J × Mo => if k.1 = k'.1 then (1 : ℝ) else 0) * (cardSeason (J := J) mon)ᵀ := by
  have hD : ∀ (p : J × T) (k : J × Mo),
      (cardSeason mon : Matrix (J × T) (J × Mo) ℝ) p k = if (p.1, mon p.2) = k then 1 else 0 :=
    fun p k => by simp [cardSeason, Prod.ext_iff]
  funext p q
  simp [shapeBasis, Matrix.mul_apply, hD]
  rw [Fintype.sum_eq_single (p.1, mon p.2) (fun x hx => by simp [Ne.symm hx])]
  simp


/-- **Card-specific means hide the card level** (Finding 27): with the card season as fixed
effects (it contains the card means), every invariant system of the shape is singular, so
Henderson III / MINQUE never applies as stated; drop `τ²` from the parameters (`τ²` is the
spread of what the design already fits). -/
theorem hendersonMat_cardSeason_det_eq_zero {Mo : Type*} [Fintype Mo] [DecidableEq Mo]
    (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ) (mon : T → Mo) {Q : Par J → Matrix (J × T) (J × T) ℝ}
    (hQ : ∀ k, Q k * cardSeason (J := J) mon = 0) :
    (Model.hendersonMat Q (shapeBasis Γ₀ w)).det = 0 :=
  Model.hendersonMat_det_eq_zero_of_design hQ _ (shapeBasis_tau_eq_cardSeason Γ₀ w mon)

/-- **An independent basis and a full-rank design are not enough** for MINQUE (or any
invariant forms): one card, two months, a common mean (`D = 1`), and the tables `I` (shock)
and `11ᵀ` (card level). The tables are independent and `DᵀD = 2`, but `11ᵀ = DDᵀ`, so every
invariant system is singular (`Model.hendersonMat_det_eq_zero_of_design`). -/
theorem exists_independent_singular :
    ∃ (V : Bool → Matrix (Unit × Fin 2) (Unit × Fin 2) ℝ) (D : Matrix (Unit × Fin 2) Unit ℝ),
      (∀ c, Model.linTable V c = 0 → c = 0) ∧ IsUnit (Dᵀ * D).det ∧
      ∀ Q : Bool → Matrix (Unit × Fin 2) (Unit × Fin 2) ℝ, (∀ k, Q k * D = 0) →
        (Model.hendersonMat Q V).det = 0 := by
  refine ⟨fun b => if b then 1 else of fun _ _ => 1, of fun _ _ => 1, fun c hc => ?_, ?_,
    fun Q hQ => Model.hendersonMat_det_eq_zero_of_design (l := false) hQ 1 ?_⟩
  · have h0 := congrFun (congrFun hc ((), 0)) ((), 1)
    have h1 := congrFun (congrFun hc ((), 0)) ((), 0)
    simp [Model.linTable] at h0 h1
    funext b
    cases b
    · simpa using h0
    · simp only [Pi.zero_apply]; linarith
  · simp [Matrix.mul_apply]
  · funext p q
    simp [Matrix.mul_apply]

end Singular

/-! ### Per-card dynamics of known shape -/

section GivenShapeG

variable {J T B : Type*} [DecidableEq J] [DecidableEq T] (M : Factor J T) [Fintype J] [Fintype T]

/-- The parameters given the shapes `Γ₀` of the factor and `G₀` of the per-card dynamics
(`Gⱼ = gⱼG₀`): those of `Par` and one scale `gⱼ` per card. -/
abbrev ParG (J : Type*) := Par J ⊕ J

/-- The table given both shapes: `shapeTable` plus `δᵢⱼgᵢ(G₀)ₜₛ`. -/
noncomputable def shapeTableG (Γ₀ G₀ : Matrix T T ℝ) (w : J → T → ℝ) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) (g : J → ℝ) : J × T → J × T → ℝ := fun p q =>
  shapeTable Γ₀ w A C s2 τ2 p q + if p.1 = q.1 then g p.1 * G₀ p.2 q.2 else 0

/-- The basis tables: those of `shapeBasis` and `Eⱼⱼ ⊗ G₀` per card. -/
noncomputable def shapeBasisG (Γ₀ G₀ : Matrix T T ℝ) (w : J → T → ℝ) :
    ParG J → Matrix (J × T) (J × T) ℝ :=
  Sum.elim (shapeBasis Γ₀ w) fun j p q => if p.1 = j ∧ q.1 = j then G₀ p.2 q.2 else 0

/-- The parameter vector `(A, C, s², τ², g)`. -/
def shapeParG (A C : Sym2 J → ℝ) (s2 : J → ℝ) (τ2 : ℝ) (g : J → ℝ) : ParG J → ℝ :=
  Sum.elim (shapePar A C s2 τ2) g

omit [Fintype T] in
/-- **The table given both shapes is linear in its parameters**. -/
theorem shapeTableG_eq_linTable (Γ₀ G₀ : Matrix T T ℝ) (w : J → T → ℝ) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) (g : J → ℝ) :
    shapeTableG Γ₀ G₀ w A C s2 τ2 g
      = Model.linTable (shapeBasisG Γ₀ G₀ w) (shapeParG A C s2 τ2 g) := by
  funext p q
  rw [shapeTableG, shapeTable_eq_linTable]
  simp only [Model.linTable]
  conv_rhs => rw [Fintype.sum_sum_type]
  simp only [shapeBasisG, shapeParG, Sum.elim_inl, Sum.elim_inr]
  congr 1
  change _ = ∑ k, g k * (if p.1 = k ∧ q.1 = k then G₀ p.2 q.2 else 0)
  by_cases hj : p.1 = q.1
  · simp [hj]
  · simp only [hj, ite_false]
    refine (sum_eq_zero fun k _ => ?_).symm
    by_cases hk : p.1 = k
    · subst hk; simp [Ne.symm hj]
    · simp [hk]

variable [Fintype B]

/-- **Henderson III / MINQUE given both shapes**: for invariant forms with a nonsingular system,
`θ̂` is unbiased for every `Aᵢⱼ`, `Cᵢⱼ`, `sⱼ²`, `τ²` and per-card scale `gⱼ`, whatever `β`. -/
theorem henderson_shapeG_unbiased (Γ₀ G₀ : Matrix T T ℝ) (w : J → T → ℝ)
    {D : Matrix (J × T) B ℝ} {Q : ParG J → Matrix (J × T) (J × T) ℝ} (hQ : ∀ k, Q k * D = 0)
    (hH : IsUnit (Model.hendersonMat Q (shapeBasisG Γ₀ G₀ w)).det) (A C : Sym2 J → ℝ)
    (s2 : J → ℝ) (τ2 : ℝ) (g : J → ℝ) (l : ParG J) :
    Model.UnbiasedMean (shapeTableG Γ₀ G₀ w A C s2 τ2 g) D
      (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ w) X l) (shapeParG A C s2 τ2 g l) := by
  rw [shapeTableG_eq_linTable]
  exact Model.henderson_unbiased hQ hH _ l

omit [Fintype J] [Fintype T] in
/-- **The factor model with per-card dynamics of known shape** `Gⱼ = gⱼG₀` and `Γ = γΓ₀` is
`shapeTableG` with `A = γλλᵀ`. -/
theorem covG_eq_shapeTableG {Γ₀ G₀ : Matrix T T ℝ} {γ : ℝ} (hΓ : M.Γ = γ • Γ₀)
    {G : J → Matrix T T ℝ} {g : J → ℝ} (hG : ∀ j, G j = g j • G₀) :
    M.covG G = shapeTableG Γ₀ G₀ M.w
      (Sym2.lift ⟨fun i j => γ * (M.load i * M.load j), fun i j => by ring⟩)
      (Sym2.lift ⟨fun i j => M.C i j, fun i j => by
        simpa using (M.C_posSemidef.1.apply i j).symm⟩) M.s2 M.τ2 g := by
  funext p q
  rw [shapeTableG, ← M.covG_zero_eq_shapeTable hΓ]
  simp only [covG, obsCovG, hG, Pi.zero_apply, Matrix.zero_apply, Matrix.smul_apply,
    smul_eq_mul, ite_self, add_zero]

/-- **Henderson III / MINQUE for the factor model with per-card dynamics** of known shapes
`Γ = γΓ₀`, `Gⱼ = gⱼG₀`: unbiased for `γλᵢλⱼ`, `Cᵢⱼ`, `sⱼ²`, `τ²` and `gⱼ`, whatever the fixed
effects. The system is singular, for instance, when `G₀ = I` (`hendersonMat_shapeG_one_det_eq_zero`:
`gⱼ` against `Cⱼⱼ`). -/
theorem henderson_factorG_unbiased {Γ₀ G₀ : Matrix T T ℝ} {γ : ℝ} (hΓ : M.Γ = γ • Γ₀)
    {G : J → Matrix T T ℝ} {g : J → ℝ} (hG : ∀ j, G j = g j • G₀)
    {D : Matrix (J × T) B ℝ} {Q : ParG J → Matrix (J × T) (J × T) ℝ} (hQ : ∀ k, Q k * D = 0)
    (hH : IsUnit (Model.hendersonMat Q (shapeBasisG Γ₀ G₀ M.w)).det) :
    (∀ i j, Model.UnbiasedMean (M.covG G) D
        (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ M.w) X (.inl (.inl s(i, j))))
        (γ * (M.load i * M.load j)))
      ∧ (∀ i j, Model.UnbiasedMean (M.covG G) D
        (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ M.w) X (.inl (.inr (.inl s(i, j)))))
        (M.C i j))
      ∧ (∀ j, Model.UnbiasedMean (M.covG G) D
        (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ M.w) X (.inl (.inr (.inr (.inl j)))))
        (M.s2 j))
      ∧ Model.UnbiasedMean (M.covG G) D
        (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ M.w) X (.inl (.inr (.inr (.inr ())))))
        M.τ2
      ∧ (∀ j, Model.UnbiasedMean (M.covG G) D
        (fun X => Model.henderson Q (shapeBasisG Γ₀ G₀ M.w) X (.inr j)) (g j)) := by
  rw [M.covG_eq_shapeTableG hΓ hG]
  refine ⟨fun i j => ?_, fun i j => ?_, fun j => ?_, ?_, fun j => ?_⟩ <;>
    exact (henderson_shapeG_unbiased Γ₀ G₀ M.w hQ hH _ _ _ _ _ _).congr (fun _ => rfl)
      (by simp [shapeParG, shapePar])

/-- **White-noise per-card dynamics are not separable from the shock**: with `G₀ = I` the
per-card table `Eⱼⱼ ⊗ I` is the shock variance table of card `j`, so the system is singular
for every choice of forms. -/
theorem hendersonMat_shapeG_one_det_eq_zero [Nonempty J] (Γ₀ : Matrix T T ℝ) (w : J → T → ℝ)
    (Q : ParG J → Matrix (J × T) (J × T) ℝ) :
    (Model.hendersonMat Q (shapeBasisG Γ₀ 1 w)).det = 0 := by
  obtain ⟨j⟩ := (inferInstance : Nonempty J)
  refine Model.hendersonMat_det_eq_zero_of_smul (l := .inl (.inr (.inl s(j, j)))) (l' := .inr j)
    (by simp) 1 ?_
  rw [one_smul]
  funext p q
  change (if p.1 = j ∧ q.1 = j then (1 : Matrix T T ℝ) p.2 q.2 else 0)
    = shapeBasis Γ₀ w (.inr (.inl s(j, j))) p q
  simp only [shapeBasis, Matrix.one_apply, Sym2.eq_iff]
  by_cases hp : p.1 = j <;> by_cases hq : q.1 = j <;> simp [hp, hq]

end GivenShapeG

end Factor

end Credibility
