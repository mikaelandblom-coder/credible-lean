import Credibility.BlupMoments

/-!
# The plug-in predictor is unbiased under symmetric noise (distribution layer)

**Optional distribution layer** (owner, 2026-11-15): this file assumes *symmetric noise*, so
nothing in the core depends on it.

In practice `K` and `ℓ` are estimated from the same data `x` and plugged into the best
linear unbiased predictor (`Core.blup`): the weights `d̂(x)` are random, and `d̂(x)ᵀx` is no
longer linear in `x`. Kackar & Harville (1981) showed it is still unbiased when the estimator
is **even** (`d̂(-u) = d̂(u)`) and **translation invariant** (`d̂(u + Xb) = d̂(u)`) and the noise
is symmetric. Quadratic moment fits built from residuals (Henderson III, MINQUE, the forms of
`Expectation.UnbiasedMean`, which annihilate the design) have both properties, and so does any
function of them (e.g. the projection onto valid tables, `ConeProjection`).

* `plugIn_unbiased_of_symmetric`: for any measurable weights `d̂` with `Xᵀd̂(u) = x₀` for all
  `u`, even and translation invariant, if the centred data and target `(x - Xβ, Y - x₀ᵀβ)` have
  the same law as their negatives, then `E[d̂(x)ᵀx - Y] = 0`.
* `blup_plugIn_unbiased_of_symmetric`: the plug-in BLUP `Core.blup (K̂ x) X (ℓ̂ x) x₀` with
  `K̂(u) ≻ 0` for every `u` and `X` of full column rank.

Symmetry (e.g. normal noise) is the assumption; the distribution-free core only knows means
and covariances, and the plug-in predictor need not be unbiased without it.
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core
namespace Target

variable {Ω : Type*} [MeasurableSpace Ω] {n q : Type*} [Fintype n] [Fintype q]
  {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  {P : Measure Ω} (T : Target K ℓ v X x₀ β P)

/-- The centred data and target `(x - Xβ, Y - x₀ᵀβ)`. -/
def centred (ω : Ω) : (n → ℝ) × ℝ := (fun i => T.x i ω - (X *ᵥ β) i, T.Y ω - x₀ ⬝ᵥ β)

/-- **The plug-in predictor is unbiased under symmetric noise** (Kackar & Harville 1981). Let
the weights `d̂(u)` be a measurable function of the data, unbiased for every data set
(`Xᵀd̂(u) = x₀`), translation invariant (`d̂(u + Xb) = d̂(u)`) and even (`d̂(-u) = d̂(u)`). If the
centred data and target have the same law as their negatives, then `E[d̂(x)ᵀx - Y] = 0`. -/
theorem plugIn_unbiased_of_symmetric [IsProbabilityMeasure P]
    (dh : (n → ℝ) → (n → ℝ)) (hdm : Measurable dh) (hX : ∀ u, Xᵀ *ᵥ dh u = x₀)
    (hinv : ∀ u b, dh (u + X *ᵥ b) = dh u) (heven : ∀ u, dh (-u) = dh u)
    (hsym : P.map T.centred = P.map (fun ω => -T.centred ω)) :
    P[fun ω => dh (fun i => T.x i ω) ⬝ᵥ (fun i => T.x i ω) - T.Y ω] = 0 := by
  let g : (n → ℝ) × ℝ → ℝ := fun z => dh z.1 ⬝ᵥ z.1 - z.2
  have hg : Measurable g := by
    simp only [g, dotProduct]
    refine Measurable.sub (Finset.measurable_sum _ fun i _ => ?_) measurable_snd
    exact ((measurable_pi_apply i).comp (hdm.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp measurable_fst)
  have hpt : ∀ ω, dh (fun i => T.x i ω) ⬝ᵥ (fun i => T.x i ω) - T.Y ω = g (T.centred ω) := by
    intro ω
    have hx : (fun i => T.x i ω) = (T.centred ω).1 + X *ᵥ β := by
      funext i; simp [centred]
    have hdx : dh (fun i => T.x i ω) = dh (T.centred ω).1 := by rw [hx, hinv]
    have hβ : dh (T.centred ω).1 ⬝ᵥ (X *ᵥ β) = x₀ ⬝ᵥ β := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hX]
    simp only [g]
    rw [hdx, hx, dotProduct_add, hβ]
    simp only [centred]
    ring
  have hneg : ∀ z, g (-z) = -g z := fun z => by
    simp only [g, Prod.fst_neg, Prod.snd_neg, heven, dotProduct_neg]
    ring
  have hZ : AEMeasurable T.centred P := by
    refine AEMeasurable.prodMk (AEMeasurable.of_eval fun i => ?_) ?_
    · exact ((T.x_memLp i).aestronglyMeasurable.aemeasurable).sub_const _
    · exact (T.Y_memLp.aestronglyMeasurable.aemeasurable).sub_const _
  have hZn : AEMeasurable (fun ω => -T.centred ω) P := hZ.neg
  have h1 : P[fun ω => g (T.centred ω)] = ∫ z, g z ∂(P.map T.centred) :=
    (integral_map hZ hg.aestronglyMeasurable).symm
  have h2 : ∫ z, g z ∂(P.map (fun ω => -T.centred ω)) = P[fun ω => g (-T.centred ω)] :=
    integral_map hZn hg.aestronglyMeasurable
  simp_rw [hpt]
  have : P[fun ω => g (T.centred ω)] = -P[fun ω => g (T.centred ω)] := by
    conv_lhs => rw [h1, hsym, h2]
    simp only [hneg, integral_neg]
  linarith

variable [DecidableEq n] [DecidableEq q]

/-- **The plug-in BLUP is unbiased under symmetric noise.** Plug estimates `K̂(x) ≻ 0` and
`ℓ̂(x)`, both even and translation invariant (as quadratic fits on residuals are), into the best
linear unbiased predictor (`Core.blup`). If the centred data and target are symmetric in law,
the plug-in predictor is unbiased for `Y`. -/
theorem blup_plugIn_unbiased_of_symmetric [IsProbabilityMeasure P]
    (Kh : (n → ℝ) → Matrix n n ℝ) (ℓh : (n → ℝ) → n → ℝ) (hK : ∀ u, (Kh u).PosDef)
    (hXi : Function.Injective X.mulVec)
    (hm : Measurable fun u => Core.blup (Kh u) X (ℓh u) x₀)
    (hKinv : ∀ u b, Kh (u + X *ᵥ b) = Kh u) (hℓinv : ∀ u b, ℓh (u + X *ᵥ b) = ℓh u)
    (hKeven : ∀ u, Kh (-u) = Kh u) (hℓeven : ∀ u, ℓh (-u) = ℓh u)
    (hsym : P.map T.centred = P.map (fun ω => -T.centred ω)) :
    P[fun ω => Core.blup (Kh fun i => T.x i ω) X (ℓh fun i => T.x i ω) x₀
        ⬝ᵥ (fun i => T.x i ω) - T.Y ω] = 0 :=
  T.plugIn_unbiased_of_symmetric (fun u => Core.blup (Kh u) X (ℓh u) x₀) hm
    (fun u => transpose_mulVec_blup (hK u) hXi _ _)
    (fun u b => by simp only [hKinv, hℓinv]) (fun u => by simp only [hKeven, hℓeven]) hsym

end Target
end Core
end Credibility
