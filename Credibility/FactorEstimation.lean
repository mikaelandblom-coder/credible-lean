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

end Factor
end Credibility
