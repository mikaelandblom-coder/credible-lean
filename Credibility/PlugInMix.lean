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
  simp only [Pi.sub_apply, Pi.mul_apply] at e
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
