import Credibility.PlugIn
import Credibility.Core
import Credibility.Expectation

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

/-- **Clipping to `[0, 1]` never hurts** when the best fraction lies there (`|M₀ - M₁| ≤ S`):
any `θ`, e.g. an estimate, moved into `[0, 1]` has no larger loss. -/
theorem mixLoss_clip_le (hS : 0 < S) (hmem : bestMix M₀ M₁ S ∈ Set.Icc 0 1) (θ : ℝ) :
    mixLoss M₀ M₁ S (max 0 (min θ 1)) ≤ mixLoss M₀ M₁ S θ := by
  rw [mixLoss_eq M₀ M₁ S hS.ne' θ, mixLoss_eq M₀ M₁ S hS.ne' (max 0 (min θ 1))]
  obtain ⟨h0, h1⟩ := hmem
  have hsq : (max 0 (min θ 1) - bestMix M₀ M₁ S) ^ 2 ≤ (θ - bestMix M₀ M₁ S) ^ 2 := by
    rcases le_total θ 0 with hθ | hθ
    · rw [min_eq_left (by linarith), max_eq_left hθ]; nlinarith
    · rcases le_total θ 1 with hθ1 | hθ1
      · rw [min_eq_left hθ1, max_eq_right hθ]
      · rw [min_eq_right hθ1, max_eq_right zero_le_one]; nlinarith
  nlinarith

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

/-! ### Choosing `θ` against a held-out proxy

The target `Y` is unobserved; a proxy `Y' = Y + ε` (next year's experience, a held-out year) is.
With the blend's error `e₀` and the disagreement `Δ` of the two predictions, the proxy's loss
curve is the true one plus a constant, minus `2θE[Δε]`. So the regression of the blend's
proxy error on the disagreement (Granger & Ramanathan's combination, stacking) finds the best
`θ` exactly when `E[Δε] = 0`, and is off by `E[Δε]/EΔ²` otherwise. -/

/-- **The proxy's loss curve**: `E(e₀ + θΔ - ε)² = E(e₀ + θΔ)² + (Eε² - 2E[e₀ε]) - 2θE[Δε]`. -/
theorem integral_sq_mix_proxy {e₀ Δ ε : Ω → ℝ} (h₀ : MemLp e₀ 2 P) (hΔ : MemLp Δ 2 P)
    (hε : MemLp ε 2 P) (θ : ℝ) :
    P[fun ω => (e₀ ω + θ * Δ ω - ε ω) ^ 2]
      = P[fun ω => (e₀ ω + θ * Δ ω) ^ 2]
        + (P[fun ω => ε ω ^ 2] - 2 * P[fun ω => e₀ ω * ε ω]) - 2 * θ * P[fun ω => Δ ω * ε ω] := by
  have hpt : ∀ ω, (e₀ ω + θ * Δ ω - ε ω) ^ 2
      = (e₀ ω + θ * Δ ω) ^ 2 + (ε ω ^ 2 - 2 * (e₀ ω * ε ω)) - 2 * θ * (Δ ω * ε ω) := fun ω => by
    ring
  simp_rw [hpt]
  have iA := (h₀.add (hΔ.const_mul θ)).integrable_sq
  have iε := hε.integrable_sq
  have i0 := h₀.integrable_mul hε
  have iΔ := hΔ.integrable_mul hε
  have e1 := integral_sub (iA.add (iε.sub (i0.const_mul 2))) (iΔ.const_mul (2 * θ))
  have e2 := integral_add iA (iε.sub (i0.const_mul 2))
  have e3 := integral_sub iε (i0.const_mul 2)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at e1 e2 e3
  rw [e1, e2, e3, integral_const_mul, integral_const_mul]

/-- **The best fraction as a regression**: with `e₁ = e₀ + Δ`, `θ* = -E[e₀Δ]/EΔ²`. -/
theorem bestMix_eq_neg_div {e₀ Δ : Ω → ℝ} (h₀ : MemLp e₀ 2 P) (hΔ : MemLp Δ 2 P)
    (hS : P[fun ω => Δ ω ^ 2] ≠ 0) :
    bestMix (P[fun ω => e₀ ω ^ 2]) (P[fun ω => (e₀ ω + Δ ω) ^ 2]) (P[fun ω => Δ ω ^ 2])
      = -P[fun ω => e₀ ω * Δ ω] / P[fun ω => Δ ω ^ 2] := by
  have hpt : ∀ ω, (e₀ ω + Δ ω) ^ 2 = e₀ ω ^ 2 + 2 * (e₀ ω * Δ ω) + Δ ω ^ 2 := fun ω => by ring
  simp_rw [hpt]
  have i0 := h₀.integrable_sq
  have iΔ := hΔ.integrable_sq
  have i1 := h₀.integrable_mul hΔ
  have e1 := integral_add (i0.add (i1.const_mul 2)) iΔ
  have e2 := integral_add i0 (i1.const_mul 2)
  simp only [Pi.add_apply, Pi.mul_apply] at e1 e2
  rw [e1, e2, integral_const_mul]
  simp only [bestMix]
  field_simp
  ring

/-- **The proxy's best fraction**: regressing the blend's proxy error `e₀ - ε` on `Δ` gives
`θ* + E[Δε]/EΔ²`; it is the best fraction for the target exactly when `E[Δε] = 0`. -/
theorem proxy_neg_div_eq {e₀ Δ ε : Ω → ℝ} (h₀ : MemLp e₀ 2 P) (hΔ : MemLp Δ 2 P)
    (hε : MemLp ε 2 P) (hS : P[fun ω => Δ ω ^ 2] ≠ 0) :
    -P[fun ω => (e₀ ω - ε ω) * Δ ω] / P[fun ω => Δ ω ^ 2]
      = bestMix (P[fun ω => e₀ ω ^ 2]) (P[fun ω => (e₀ ω + Δ ω) ^ 2]) (P[fun ω => Δ ω ^ 2])
        + P[fun ω => Δ ω * ε ω] / P[fun ω => Δ ω ^ 2] := by
  rw [bestMix_eq_neg_div h₀ hΔ hS]
  have hpt : ∀ ω, (e₀ ω - ε ω) * Δ ω = e₀ ω * Δ ω - Δ ω * ε ω := fun ω => by ring
  simp_rw [hpt]
  have e := integral_sub (h₀.integrable_mul hΔ) (hΔ.integrable_mul hε)
  simp only [Pi.mul_apply] at e
  rw [e]
  field_simp
  ring

/-- **The proxy's gain**: `E(e₀ - ε)² - E(e₀ + Δ - ε)² = (Ee₀² - E(e₀ + Δ)²) + 2E[Δε]`. -/
theorem proxy_gain_eq {e₀ Δ ε : Ω → ℝ} (h₀ : MemLp e₀ 2 P) (hΔ : MemLp Δ 2 P)
    (hε : MemLp ε 2 P) :
    P[fun ω => (e₀ ω - ε ω) ^ 2] - P[fun ω => (e₀ ω + Δ ω - ε ω) ^ 2]
      = (P[fun ω => e₀ ω ^ 2] - P[fun ω => (e₀ ω + Δ ω) ^ 2])
        + 2 * P[fun ω => Δ ω * ε ω] := by
  have h0 := integral_sq_mix_proxy h₀ hΔ hε 0
  have h1 := integral_sq_mix_proxy h₀ hΔ hε 1
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  rw [h0, h1]
  ring

/-- A proxy whose noise is independent of the disagreement and has mean zero has `E[Δε] = 0`. -/
theorem integral_mul_eq_zero_of_indepFun {Δ ε : Ω → ℝ} (hind : Δ ⟂ᵢ[P] ε)
    (hΔ : AEStronglyMeasurable Δ P) (hε : AEStronglyMeasurable ε P) (h0 : P[ε] = 0) :
    P[fun ω => Δ ω * ε ω] = 0 := by
  have := hind.integral_mul_eq_mul_integral hΔ hε
  simp only [Pi.mul_apply] at this
  rw [this, h0, mul_zero]

/-! ### The price of one held-out year (S64, target 1)

Given the fit, the blend's errors `e₀` on the cohorts and the disagreement `Δ` of the two fitted
predictions are fixed vectors; the held-out year adds its noise `ε` (mean 0, covariance table
`C`, any distribution). With weights `W = diag(w)` and `D = ΔᵀWΔ > 0`, the weighted loss
`(e₀ + θΔ)ᵀW(e₀ + θΔ)` is a parabola with minimum at the draw's own best fraction
`θ̃ = -ΔᵀWe₀/D`, and the held-out regression `θ̂ = -ΔᵀW(e₀ - ε)/D = θ̃ + ΔᵀWε/D` is unbiased for
it. Its mean loss exceeds the best by the price `ΔᵀWCWΔ/D`, a Rayleigh quotient of
`W^½CW^½`, so at least its smallest eigenvalue, whatever the fits. -/

section HeldOut

variable {J : Type*} [Fintype J]

/-- The weighted product `xᵀWy = Σⱼ wⱼxⱼyⱼ`. -/
def wDot (w x y : J → ℝ) : ℝ := ∑ j, w j * x j * y j

/-- The weighted loss `(e₀ + θΔ)ᵀW(e₀ + θΔ)` of the fraction `θ` on the cohorts. -/
def wLoss (w e₀ Δ : J → ℝ) (θ : ℝ) : ℝ := wDot w (e₀ + θ • Δ) (e₀ + θ • Δ)

/-- The draw's own best fraction `θ̃ = -ΔᵀWe₀/ΔᵀWΔ`. -/
noncomputable def drawTheta (w e₀ Δ : J → ℝ) : ℝ := -wDot w Δ e₀ / wDot w Δ Δ

/-- The held-out regression `θ̂ = -ΔᵀW(e₀ - ε)/ΔᵀWΔ`. -/
noncomputable def heldOutTheta (w e₀ Δ ε : J → ℝ) : ℝ := -wDot w Δ (e₀ - ε) / wDot w Δ Δ

/-- `ΔᵀWCWΔ`. -/
def heldOutNum (w Δ : J → ℝ) (C : Matrix J J ℝ) : ℝ :=
  ∑ i, ∑ j, w i * Δ i * C i j * (w j * Δ j)

/-- The price `ΔᵀWCWΔ/ΔᵀWΔ` of choosing `θ` on one held-out year. -/
noncomputable def heldOutPrice (w Δ : J → ℝ) (C : Matrix J J ℝ) : ℝ :=
  heldOutNum w Δ C / wDot w Δ Δ

/-- `(e₀ + θΔ)ᵀW(e₀ + θΔ) = e₀ᵀWe₀ + 2θΔᵀWe₀ + θ²ΔᵀWΔ`. -/
theorem wLoss_expand (w e₀ Δ : J → ℝ) (θ : ℝ) :
    wLoss w e₀ Δ θ = wDot w e₀ e₀ + 2 * θ * wDot w Δ e₀ + θ ^ 2 * wDot w Δ Δ := by
  simp only [wLoss, wDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The weighted loss is a parabola around the draw's best fraction:
`L(θ) = L(θ̃) + ΔᵀWΔ (θ - θ̃)²`. -/
theorem wLoss_eq (w e₀ Δ : J → ℝ) (hD : wDot w Δ Δ ≠ 0) (θ : ℝ) :
    wLoss w e₀ Δ θ
      = wLoss w e₀ Δ (drawTheta w e₀ Δ) + wDot w Δ Δ * (θ - drawTheta w e₀ Δ) ^ 2 := by
  rw [wLoss_expand, wLoss_expand, drawTheta]
  field_simp
  ring

/-- `θ̂ = θ̃ + ΔᵀWε/ΔᵀWΔ`. -/
theorem heldOutTheta_eq (w e₀ Δ ε : J → ℝ) (hD : wDot w Δ Δ ≠ 0) :
    heldOutTheta w e₀ Δ ε = drawTheta w e₀ Δ + (∑ j, w j * Δ j * ε j) / wDot w Δ Δ := by
  have h : wDot w Δ (e₀ - ε) = wDot w Δ e₀ - ∑ j, w j * Δ j * ε j := by
    simp only [wDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heldOutTheta, drawTheta, h]
  field_simp
  ring

/-- For a fixed `θ₀`: `L(θ₀) - L(θ̃) = ΔᵀWΔ (θ₀ - θ̃)²` is the room a held-out choice can gain. -/
theorem wLoss_sub_drawTheta (w e₀ Δ : J → ℝ) (hD : wDot w Δ Δ ≠ 0) (θ₀ : ℝ) :
    wLoss w e₀ Δ θ₀ - wLoss w e₀ Δ (drawTheta w e₀ Δ)
      = wDot w Δ Δ * (θ₀ - drawTheta w e₀ Δ) ^ 2 := by
  rw [wLoss_eq w e₀ Δ hD θ₀]; ring

/-- **The price is at least the smallest eigenvalue of `W^½CW^½`**: if every eigenvalue of
`M = (√wᵢ Cᵢⱼ √wⱼ)` is at least `m`, then `m ≤ ΔᵀWCWΔ/ΔᵀWΔ`, whatever `Δ`. -/
theorem le_heldOutPrice [DecidableEq J] (w Δ : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hD : 0 < wDot w Δ Δ) (C : Matrix J J ℝ)
    (hM : (Matrix.of fun i j => Real.sqrt (w i) * C i j * Real.sqrt (w j)).IsHermitian)
    {m : ℝ} (hm : ∀ i, m ≤ hM.eigenvalues i) : m ≤ heldOutPrice w Δ C := by
  set y : J → ℝ := fun j => Real.sqrt (w j) * Δ j
  have hs : ∀ j, Real.sqrt (w j) * Real.sqrt (w j) = w j := fun j => Real.mul_self_sqrt (hw j)
  have hyy : y ⬝ᵥ y = wDot w Δ Δ := by
    simp only [y, dotProduct, wDot]
    exact Finset.sum_congr rfl fun j _ => by linear_combination (Δ j * Δ j) * hs j
  have hyM : y ⬝ᵥ ((Matrix.of fun i j => Real.sqrt (w i) * C i j * Real.sqrt (w j)) *ᵥ y)
      = heldOutNum w Δ C := by
    simp only [y, dotProduct, mulVec, Matrix.of_apply, heldOutNum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : Real.sqrt (w i) * Real.sqrt (w i) * (Real.sqrt (w j) * Real.sqrt (w j))
        = w i * w j := by rw [hs i, hs j]
    linear_combination (Δ i * C i j * Δ j) * hij
  have := hM.mul_dotProduct_le_dotProduct_mulVec hm y
  rw [hyy, hyM] at this
  rw [heldOutPrice, le_div_iff₀ hD]
  exact this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma memLp_wsum (a : J → ℝ) {ε : J → Ω → ℝ} (hε : ∀ j, MemLp (ε j) 2 P) :
    MemLp (fun ω => ∑ j, a j * ε j ω) 2 P := by
  exact memLp_finsetSum (μ := P) (p := 2) Finset.univ
    (f := fun j ω => a j * ε j ω) fun j _ => (hε j).const_mul (a j)

/-- `E(aᵀε)² = aᵀCa` for noise with mean 0 and covariance table `C` (any distribution),
from `Model.integral_quad_of_cov`. -/
theorem integral_sq_wsum (a : J → ℝ) (ε : J → Ω → ℝ) (C : Matrix J J ℝ)
    (hε : ∀ j, MemLp (ε j) 2 P) (hm : ∀ j, P[ε j] = 0)
    (hc : ∀ i j, covariance (ε i) (ε j) P = C i j) :
    P[fun ω => (∑ j, a j * ε j ω) ^ 2] = ∑ i, ∑ j, a i * C i j * a j := by
  have h := Model.integral_quad_of_cov (J := J) (T := Unit) (P := P) (fun p => ε p.1)
    (fun p q => C p.1 q.1) 0 (fun p q => a p.1 * a q.1) (fun _ => True)
    (fun _ _ _ => ⟨trivial, trivial⟩) (fun p _ => hε p.1) (fun p _ => hm p.1)
    (fun p q _ _ => hc p.1 q.1)
  simp only [Model.quad, Model.Ecov, Fintype.sum_prod_type, Finset.univ_unique,
    Finset.sum_singleton, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h
  rw [← Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    (show a i * a j * C i j = a i * C i j * a j by ring), ← h]
  congr 1
  funext ω
  show (∑ j, a j * ε j ω) ^ 2 = _
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable (w e₀ Δ : J → ℝ) {ε : J → Ω → ℝ} {C : Matrix J J ℝ}

/-- **The held-out fraction is unbiased for the draw's best one**: `E θ̂ = θ̃`. -/
theorem integral_heldOutTheta (hD : wDot w Δ Δ ≠ 0) (hε : ∀ j, MemLp (ε j) 2 P)
    (hm : ∀ j, P[ε j] = 0) :
    P[fun ω => heldOutTheta w e₀ Δ (fun j => ε j ω)] = drawTheta w e₀ Δ := by
  simp_rw [heldOutTheta_eq w e₀ Δ _ hD]
  have hi := (memLp_wsum (fun j => w j * Δ j) hε).integrable one_le_two
  rw [integral_add (integrable_const _) (hi.div_const _), integral_const, integral_div,
    integral_finsetSum _ fun j _ => ((hε j).integrable one_le_two).const_mul _]
  simp [integral_const_mul, hm]

/-- **The spread of the held-out fraction**: `E(θ̂ - θ̃)² = ΔᵀWCWΔ/(ΔᵀWΔ)²`, its variance. -/
theorem integral_sq_heldOutTheta_sub (hD : wDot w Δ Δ ≠ 0) (hε : ∀ j, MemLp (ε j) 2 P)
    (hm : ∀ j, P[ε j] = 0) (hc : ∀ i j, covariance (ε i) (ε j) P = C i j) :
    P[fun ω => (heldOutTheta w e₀ Δ (fun j => ε j ω) - drawTheta w e₀ Δ) ^ 2]
      = heldOutNum w Δ C / wDot w Δ Δ ^ 2 := by
  simp_rw [heldOutTheta_eq w e₀ Δ _ hD, add_sub_cancel_left, div_pow]
  rw [integral_div, integral_sq_wsum _ ε C hε hm hc, heldOutNum]

/-- **The price of one held-out year**: `E[(e₀ + θ̂Δ)ᵀW(e₀ + θ̂Δ)] = L(θ̃) + ΔᵀWCWΔ/ΔᵀWΔ`,
for every distribution of the held-out noise with mean 0 and covariance table `C`. -/
theorem integral_wLoss_heldOutTheta (hD : wDot w Δ Δ ≠ 0) (hε : ∀ j, MemLp (ε j) 2 P)
    (hm : ∀ j, P[ε j] = 0) (hc : ∀ i j, covariance (ε i) (ε j) P = C i j) :
    P[fun ω => wLoss w e₀ Δ (heldOutTheta w e₀ Δ (fun j => ε j ω))]
      = wLoss w e₀ Δ (drawTheta w e₀ Δ) + heldOutPrice w Δ C := by
  simp_rw [wLoss_eq w e₀ Δ hD (heldOutTheta w e₀ Δ _)]
  have hi := ((memLp_wsum (fun j => w j * Δ j) hε).sub (memLp_const (drawTheta w e₀ Δ))
    |>.add (memLp_const (drawTheta w e₀ Δ))).integrable_sq
  have hsq : Integrable (fun ω => (heldOutTheta w e₀ Δ (fun j => ε j ω)
      - drawTheta w e₀ Δ) ^ 2) P := by
    simp_rw [heldOutTheta_eq w e₀ Δ _ hD, add_sub_cancel_left, div_pow]
    exact ((memLp_wsum (fun j => w j * Δ j) hε).integrable_sq).div_const _
  rw [integral_add (integrable_const _) (hsq.const_mul _), integral_const, integral_const_mul,
    integral_sq_heldOutTheta_sub w e₀ Δ hD hε hm hc, heldOutPrice]
  simp only [probReal_univ, one_smul]
  field_simp

/-- **When the held-out choice beats a fixed fraction**: in mean, `θ̂` beats a fixed `θ₀`
iff the room `ΔᵀWΔ(θ₀ - θ̃)²` exceeds the price `ΔᵀWCWΔ/ΔᵀWΔ`. -/
theorem integral_wLoss_heldOutTheta_lt_iff (hD : wDot w Δ Δ ≠ 0) (hε : ∀ j, MemLp (ε j) 2 P)
    (hm : ∀ j, P[ε j] = 0) (hc : ∀ i j, covariance (ε i) (ε j) P = C i j) (θ₀ : ℝ) :
    P[fun ω => wLoss w e₀ Δ (heldOutTheta w e₀ Δ (fun j => ε j ω))] < wLoss w e₀ Δ θ₀
      ↔ heldOutPrice w Δ C < wDot w Δ Δ * (θ₀ - drawTheta w e₀ Δ) ^ 2 := by
  rw [integral_wLoss_heldOutTheta w e₀ Δ hD hε hm hc, wLoss_eq w e₀ Δ hD θ₀]
  constructor <;> intro h <;> linarith

end HeldOut

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

/-- **Choosing `θ` on a held-out proxy.** Let `Y'` be a proxy for the target (next year's
experience) whose noise `Y' - Y` is uncorrelated with the disagreement `d̂ᵀx - ŵᵀx` of the two
fitted predictions. Then for every `θ` the proxy's mean squared error is the target's plus a
constant, so both are minimised by the same `θ`, for every distribution. -/
theorem integral_sq_plugIn_mix_proxy (wh dh : Ω → n → ℝ) (Y' : Ω → ℝ)
    (h₀ : MemLp (fun ω => T.plugIn wh ω - T.Y ω) 2 P)
    (h₁ : MemLp (fun ω => T.plugIn dh ω - T.Y ω) 2 P)
    (hε : MemLp (fun ω => Y' ω - T.Y ω) 2 P)
    (horth : P[fun ω => (T.plugIn dh ω - T.plugIn wh ω) * (Y' ω - T.Y ω)] = 0) (θ : ℝ) :
    P[fun ω => (T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - Y' ω) ^ 2]
      = P[fun ω => (T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - T.Y ω) ^ 2]
        + (P[fun ω => (T.plugIn wh ω - Y' ω) ^ 2] - P[fun ω => (T.plugIn wh ω - T.Y ω) ^ 2]) := by
  have hΔ : MemLp (fun ω => T.plugIn dh ω - T.plugIn wh ω) 2 P := by
    have := h₁.sub h₀
    refine this.congr_norm ?_ ?_
    · exact (h₁.sub h₀).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.sub_apply]; ring)
    · exact Filter.Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring_nf
  have key := integral_sq_mix_proxy h₀ hΔ hε θ
  have key0 := integral_sq_mix_proxy h₀ hΔ hε 0
  rw [horth] at key key0
  simp only [zero_mul, add_zero, mul_zero, sub_zero] at key0 key
  have p1 : ∀ ω, T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - Y' ω
      = (T.plugIn wh ω - T.Y ω) + θ * (T.plugIn dh ω - T.plugIn wh ω) - (Y' ω - T.Y ω) :=
    fun ω => by rw [plugIn_mix]; ring
  have p2 : ∀ ω, T.plugIn (fun ω => wh ω + θ • (dh ω - wh ω)) ω - T.Y ω
      = (T.plugIn wh ω - T.Y ω) + θ * (T.plugIn dh ω - T.plugIn wh ω) :=
    fun ω => by rw [plugIn_mix]; ring
  have p3 : ∀ ω, T.plugIn wh ω - Y' ω = (T.plugIn wh ω - T.Y ω) - (Y' ω - T.Y ω) :=
    fun ω => by ring
  simp_rw [p1, p2, p3, key, key0]
  ring

end Target
end Core
end Credibility
