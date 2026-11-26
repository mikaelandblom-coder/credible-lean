import Credibility.PlugIn
import Credibility.Core

/-!
# Mixing two predictors: the path from the plug-in blend to the plug-in BLUP (distribution-free)

`Core.linMse_add_smul_blupWeight_sub` moves fixed unbiased weights `w` the fraction `θ` towards
the best predictor `d*`; with known moments the full step `θ = 1` is best. With fitted moments
both ends are random: the plug-in blend `ŵᵀx` and the plug-in best predictor `d̂ᵀx`. With
errors `e₀`, `e₁`, their mean squares `M₀`, `M₁` and the spread `S = E(e₁ - e₀)²` (the mean
square of the difference of the two predictions, which needs no truth), pointwise
`((1 - θ)a + θb)² = (1 - θ)a² + θb² - θ(1 - θ)(b - a)²` gives, for every distribution,

`MSE(θ) = (1 - θ)M₀ + θM₁ - θ(1 - θ)S`  (`integral_sq_mix`, `Target.integral_sq_plugIn_mix`):

the straight line between the two errors minus the spread (Krogh & Vedelsby's ambiguity
decomposition; the optimal weight is Bates & Granger's for combining forecasts and that of a
composite small-area estimator). So the best `θ` is `½ + (M₀ - M₁)/(2S)` (`bestMix`): `1` exactly
when the gain `M₀ - M₁` equals the spread, as with known moments (Pythagoras), `½` when both
predictors are equally good, and within `[0, 1]` iff `|M₀ - M₁| ≤ S`.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Credibility

/-! ### The loss along the path -/

section Real

variable (M₀ M₁ S : ℝ)

/-- The mean squared error `(1 - θ)M₀ + θM₁ - θ(1 - θ)S` of `(1 - θ)·first + θ·second`, from the
two mean squared errors `M₀`, `M₁` and the spread `S = E(e₁ - e₀)²`. -/
def mixLoss (θ : ℝ) : ℝ := (1 - θ) * M₀ + θ * M₁ - θ * (1 - θ) * S

/-- The best fraction `θ* = ½ + (M₀ - M₁)/(2S)`. -/
noncomputable def bestMix : ℝ := 1 / 2 + (M₀ - M₁) / (2 * S)

theorem mixLoss_zero : mixLoss M₀ M₁ S 0 = M₀ := by simp [mixLoss]

theorem mixLoss_one : mixLoss M₀ M₁ S 1 = M₁ := by simp [mixLoss]

/-- `MSE(θ) = MSE(θ*) + S(θ - θ*)²`. -/
theorem mixLoss_eq (hS : S ≠ 0) (θ : ℝ) :
    mixLoss M₀ M₁ S θ = mixLoss M₀ M₁ S (bestMix M₀ M₁ S) + S * (θ - bestMix M₀ M₁ S) ^ 2 := by
  simp only [mixLoss, bestMix]
  field_simp
  ring

/-- **The best fraction**: for a positive spread, `θ*` minimises the loss along the path. -/
theorem bestMix_optimal (hS : 0 < S) (θ : ℝ) :
    mixLoss M₀ M₁ S (bestMix M₀ M₁ S) ≤ mixLoss M₀ M₁ S θ := by
  rw [mixLoss_eq M₀ M₁ S hS.ne' θ]
  have := mul_nonneg hS.le (sq_nonneg (θ - bestMix M₀ M₁ S))
  linarith

/-- The best loss: `(M₀ + M₁)/2 - S/4 - (M₀ - M₁)²/(4S)`. -/
theorem mixLoss_bestMix (hS : S ≠ 0) :
    mixLoss M₀ M₁ S (bestMix M₀ M₁ S) = (M₀ + M₁) / 2 - S / 4 - (M₀ - M₁) ^ 2 / (4 * S) := by
  simp only [mixLoss, bestMix]
  field_simp
  ring

/-- The full step is best exactly when the gain equals the spread: `θ* = 1 ↔ M₀ - M₁ = S`. -/
theorem bestMix_eq_one_iff (hS : S ≠ 0) : bestMix M₀ M₁ S = 1 ↔ M₀ - M₁ = S := by
  simp only [bestMix]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- `θ*` lies in `[0, 1]` exactly when `|M₀ - M₁| ≤ S`. -/
theorem bestMix_mem_Icc_iff (hS : 0 < S) :
    bestMix M₀ M₁ S ∈ Set.Icc 0 1 ↔ |M₀ - M₁| ≤ S := by
  have h2 : (0 : ℝ) < 2 * S := by linarith
  simp only [Set.mem_Icc, bestMix, abs_le]
  constructor
  · rintro ⟨h0, h1⟩
    have e : (M₀ - M₁) / (2 * S) * (2 * S) = M₀ - M₁ := div_mul_cancel₀ _ h2.ne'
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩
    constructor
    · have : -1 / 2 ≤ (M₀ - M₁) / (2 * S) := by
        rw [le_div_iff₀ h2]; linarith
      linarith
    · have : (M₀ - M₁) / (2 * S) ≤ 1 / 2 := by
        rw [div_le_iff₀ h2]; linarith
      linarith

/-- **When a step towards the second predictor is safe**: for `θ > 0`, the mix is no worse than
the first predictor iff the second loses at most `(1 - θ)S` against it. -/
theorem mixLoss_le_zero_iff {θ : ℝ} (hθ : 0 < θ) :
    mixLoss M₀ M₁ S θ ≤ M₀ ↔ M₁ - M₀ ≤ (1 - θ) * S := by
  have h : mixLoss M₀ M₁ S θ - M₀ = θ * ((M₁ - M₀) - (1 - θ) * S) := by
    simp only [mixLoss]; ring
  constructor
  · intro hle
    have : θ * ((M₁ - M₀) - (1 - θ) * S) ≤ 0 := by linarith
    have := nonpos_of_mul_nonpos_right this hθ
    linarith
  · intro hle
    have : θ * ((M₁ - M₀) - (1 - θ) * S) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ.le (by linarith)
    linarith

/-- Halfway: `MSE(½) = (M₀ + M₁)/2 - S/4`. -/
theorem mixLoss_half : mixLoss M₀ M₁ S (1 / 2) = (M₀ + M₁) / 2 - S / 4 := by
  simp only [mixLoss]; ring

end Real

namespace Core

/-- **With known moments the full step is best**: for fixed unbiased weights `w ≠ d*`, the gain
`mse(w) - mse(d*)` equals the spread `(w - d*)ᵀK(w - d*)` (Pythagoras), so `θ* = 1`. -/
theorem bestMix_blupWeight {J : Type*} [Fintype J] [DecidableEq J] {K : Matrix J J ℝ}
    (hK : K.PosDef) (L : Matrix J J ℝ) (j : J) {w : J → ℝ} (hw : ∑ i, w i = 1)
    (hne : w ≠ blupWeight K L j) :
    bestMix (linMse K L j w) (linMse K L j (blupWeight K L j))
      ((w - blupWeight K L j) ⬝ᵥ (K *ᵥ (w - blupWeight K L j))) = 1 := by
  have : Nonempty J := ⟨j⟩
  have hS := hK.dotProduct_mulVec_pos (x := w - blupWeight K L j) (sub_ne_zero.mpr hne)
  simp only [star_trivial] at hS
  refine (bestMix_eq_one_iff _ _ _ hS.ne').mpr ?_
  rw [linMse_eq_blupWeight_add hK L j w hw]
  ring

end Core

/-! ### For random errors (distribution-free) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The loss along the path, for any random errors**: if `e₀`, `e₁` are square integrable,
`E((1 - θ)e₀ + θe₁)² = (1 - θ)Ee₀² + θEe₁² - θ(1 - θ)E(e₁ - e₀)²`. -/
theorem integral_sq_mix {e₀ e₁ : Ω → ℝ} (h₀ : MemLp e₀ 2 P) (h₁ : MemLp e₁ 2 P) (θ : ℝ) :
    P[fun ω => ((1 - θ) * e₀ ω + θ * e₁ ω) ^ 2]
      = mixLoss (P[fun ω => e₀ ω ^ 2]) (P[fun ω => e₁ ω ^ 2])
          (P[fun ω => (e₁ ω - e₀ ω) ^ 2]) θ := by
  have hpt : ∀ ω, ((1 - θ) * e₀ ω + θ * e₁ ω) ^ 2
      = (1 - θ) * e₀ ω ^ 2 + θ * e₁ ω ^ 2 - θ * (1 - θ) * (e₁ ω - e₀ ω) ^ 2 := fun ω => by ring
  simp_rw [hpt]
  have i0 := h₀.integrable_sq
  have i1 := h₁.integrable_sq
  have i2 := (h₁.sub h₀).integrable_sq
  have e1 := integral_sub ((i0.const_mul (1 - θ)).add (i1.const_mul θ))
    (i2.const_mul (θ * (1 - θ)))
  have e2 := integral_add (i0.const_mul (1 - θ)) (i1.const_mul θ)
  simp only [Pi.add_apply, Pi.sub_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

namespace Core
namespace Target

variable {n q : Type*} [Fintype n] [Fintype q]
  {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  (T : Target K ℓ v X x₀ β P)

/-- Mixing the weights mixes the predictions: `(ŵ + θ(d̂ - ŵ))ᵀx = (1 - θ)ŵᵀx + θd̂ᵀx`. -/
theorem plugIn_mix (wh dh : Ω → n → ℝ) (θ : ℝ) (ω : Ω) :
    T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω
      = (1 - θ) * T.plugIn wh ω + θ * T.plugIn dh ω := by
  simp only [plugIn, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The plug-in path from the blend to the best predictor.** For random weights `ŵ` (e.g. the
fitted blend) and `d̂` (e.g. the fitted best predictor) with square-integrable errors, moving
the fraction `θ` from `ŵ` to `d̂` has mean squared error `(1 - θ)M₀ + θM₁ - θ(1 - θ)S`, with
`S = E(d̂ᵀx - ŵᵀx)²`, for every distribution with the moments of `Target`. -/
theorem integral_sq_plugIn_mix (wh dh : Ω → n → ℝ)
    (h₀ : MemLp (fun ω => T.plugIn wh ω - T.Y ω) 2 P)
    (h₁ : MemLp (fun ω => T.plugIn dh ω - T.Y ω) 2 P) (θ : ℝ) :
    P[fun ω => (T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - T.Y ω) ^ 2]
      = mixLoss (P[fun ω => (T.plugIn wh ω - T.Y ω) ^ 2])
          (P[fun ω => (T.plugIn dh ω - T.Y ω) ^ 2])
          (P[fun ω => (T.plugIn dh ω - T.plugIn wh ω) ^ 2]) θ := by
  have hpt : ∀ ω, T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - T.Y ω
      = (1 - θ) * (T.plugIn wh ω - T.Y ω) + θ * (T.plugIn dh ω - T.Y ω) := fun ω => by
    rw [plugIn_mix]; ring
  have hS : ∀ ω, T.plugIn dh ω - T.plugIn wh ω
      = (T.plugIn dh ω - T.Y ω) - (T.plugIn wh ω - T.Y ω) := fun ω => by ring
  simp_rw [hpt, hS]
  exact integral_sq_mix h₀ h₁ θ

end Target
end Core
end Credibility
