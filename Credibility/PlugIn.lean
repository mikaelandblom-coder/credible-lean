import Credibility.BlupMoments

/-!
# The plug-in predictor: the exact MSE identity (extension, distribution-free)

With `K` and `ℓ` estimated from the data, the predictor uses random weights `d̂`, so it is no
longer linear in the data. Compare it with fixed unbiased weights `d` (e.g. the best predictor
`Core.blup` with the true moments). Write the error of `d̂` as the error of `d` plus the
difference of the two predictions, `A + B` with `A = dᵀx - Y` and `B = d̂ᵀx - dᵀx`. Then

`E(d̂ᵀx - Y)² = mse(d) + E B² + 2 E[AB]`  (`Target.integral_sq_plugIn`),

for every distribution with the moments of `Core.Target`, as soon as `B` is square integrable.
This is Kackar & Harville's (1984) identity without normality: the cross term `2E[AB]` is the
part that needs a distributional assumption. Under normal noise and a translation-invariant fit it
vanishes (`PlugInNormal.lean`); under heavy tails it can be negative (`studies/literature.md` §4).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Credibility
namespace Core
namespace Target

variable {Ω : Type*} [MeasurableSpace Ω] {n q : Type*} [Fintype n] [Fintype q]
  {K : Matrix n n ℝ} {ℓ : n → ℝ} {v : ℝ} {X : Matrix n q ℝ} {x₀ : q → ℝ} {β : q → ℝ}
  {P : Measure Ω} (T : Target K ℓ v X x₀ β P)

/-- The plug-in prediction `d̂ᵀx` with random weights `d̂ : Ω → n → ℝ`. -/
def plugIn (dh : Ω → n → ℝ) (ω : Ω) : ℝ := ∑ i, dh ω i * T.x i ω

variable [IsProbabilityMeasure P]

/-- **The exact MSE of a plug-in predictor.** For random weights `d̂` and fixed unbiased weights
`d` (`Xᵀd = x₀`), with `A = dᵀx - Y` and `B = d̂ᵀx - dᵀx` square integrable,
`E(d̂ᵀx - Y)² = mse(d) + E B² + 2E[AB]`, for every distribution with these moments. -/
theorem integral_sq_plugIn (dh : Ω → n → ℝ) {d : n → ℝ} (hd : Xᵀ *ᵥ d = x₀)
    (hB : MemLp (fun ω => T.plugIn dh ω - portLin T.x d ω) 2 P) :
    P[fun ω => (T.plugIn dh ω - T.Y ω) ^ 2]
      = predMse K ℓ v d + P[fun ω => (T.plugIn dh ω - portLin T.x d ω) ^ 2]
        + 2 * P[fun ω => (portLin T.x d ω - T.Y ω) * (T.plugIn dh ω - portLin T.x d ω)] := by
  have hA : MemLp (fun ω => portLin T.x d ω - T.Y ω) 2 P := (T.memLp_portLin d).sub T.Y_memLp
  have hpt : ∀ ω, (T.plugIn dh ω - T.Y ω) ^ 2
      = (portLin T.x d ω - T.Y ω) ^ 2 + (T.plugIn dh ω - portLin T.x d ω) ^ 2
        + 2 * ((portLin T.x d ω - T.Y ω) * (T.plugIn dh ω - portLin T.x d ω)) := fun ω => by
    ring
  simp_rw [hpt]
  have iAB : Integrable (fun ω => (portLin T.x d ω - T.Y ω) * (T.plugIn dh ω - portLin T.x d ω))
      P := hA.integrable_mul hB
  have e1 := integral_add (hA.integrable_sq.add hB.integrable_sq) (iAB.const_mul 2)
  have e2 := integral_add hA.integrable_sq hB.integrable_sq
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, T.mse_portLin hd]

end Target
end Core
end Credibility
