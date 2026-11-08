import Credibility.Blend
import Credibility.Weights

/-!
# The correlated data model (thesis §2.3, eqs. (15)–(16))

`μⱼ = μ + τ ηⱼ` (cohort effect), `μⱼₜ = μⱼ + σⱼₜ εⱼₜ` (sampling noise),
`cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ`. The thesis writes the cohort effect `εⱼ`; it is
renamed `ηⱼ` here to keep it apart from the noise. Distribution-free: only
first and second moments are assumed.

Only the parameters and eq. (16) live here, so that both `Unequal` (cohort `j`
observed in `Tⱼ`) and `Model` (`Tⱼ = T`, the thesis) can build on them;
`Model` results are corollaries of the `Unequal` ones.
-/

namespace Credibility

structure Model (J T : Type*) where
  /-- Heterogeneity between cohorts. -/
  τ2 : ℝ
  /-- Observation noise (standard deviation) of cohort `j` in period `t`. -/
  σ : J → T → ℝ
  /-- Contemporaneous correlation between cohorts. -/
  ρ : J → J → ℝ
  τ2_pos : 0 < τ2
  σ_pos : ∀ j t, 0 < σ j t
  ρ_self : ∀ j, ρ j j = 1
  ρ_symm : ∀ i j, ρ i j = ρ j i

namespace Model

variable {J T : Type*} [DecidableEq J] [DecidableEq T]
variable (M : Model J T)

/-- `cov(μᵢₜ, μⱼₛ)` (the thesis's `K̄ᵢⱼᵗˢ`), eq. (16). -/
def obsCov (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0)
    + M.τ2 * (if i = j then 1 else 0)

end Model
end Credibility
