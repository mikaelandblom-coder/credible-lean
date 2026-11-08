import Credibility.Estimation

/-!
# Cohort-dependent series lengths (extension, not in the thesis)

Cohort `j` is observed only in the periods `Tⱼ ⊆ T` (`obs j`). Correlations act
only on periods two cohorts share, `Tᵢⱼ = Tᵢ ∩ Tⱼ` (`overlap i j`). The model
itself is `Model` (eqs. (15)–(16)); only the weights `aⱼₜ`, hence `σ²ᵢⱼ` and
`K`, change. See `notes/unequal-lengths.md`.

The estimators reuse `Model.Unbiased`, which gives every cell `(j, t)` a
(latent) value; `Observed f` says that `f` reads only cells with `t ∈ Tⱼ`.
-/

open Finset Matrix

namespace Credibility

/-- The correlated model with cohort `j` observed in `Tⱼ = obs j ≠ ∅`. -/
structure Unequal (J T : Type*) extends Model J T where
  /-- The periods `Tⱼ` in which cohort `j` is observed. -/
  obs : J → Finset T
  obs_nonempty : ∀ j, (obs j).Nonempty

namespace Unequal

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Unequal J T)

/-- The shared periods `Tᵢⱼ = Tᵢ ∩ Tⱼ`. -/
def overlap (i j : J) : Finset T := M.obs i ∩ M.obs j

/-- Cohort weights: inverse-variance on `Tⱼ`, zero elsewhere (eq. (23) on `Tⱼ`). -/
noncomputable def a (j : J) (t : T) : ℝ :=
  if t ∈ M.obs j then (M.σ j t ^ 2)⁻¹ / ∑ s ∈ M.obs j, (M.σ j s ^ 2)⁻¹ else 0

/-- `σ²ᵢⱼ = Σ_{t∈Tᵢⱼ} aᵢₜ aⱼₜ σᵢₜ σⱼₜ`, eq. (18) over the shared periods. -/
noncomputable def σ2 (i j : J) : ℝ :=
  ∑ t ∈ M.overlap i j, M.a i t * M.a j t * M.σ i t * M.σ j t

/-- `Kᵢⱼ = cov(μ̂ᵢ, μ̂ⱼ) = Σ_{t∈Tᵢ} Σ_{s∈Tⱼ} aᵢₜ aⱼₛ K̄ᵢⱼᵗˢ`, eq. (21) on the observed cells. -/
noncomputable def K : Matrix J J ℝ :=
  fun i j => ∑ t ∈ M.obs i, ∑ s ∈ M.obs j, M.a i t * M.a j s * M.toModel.obsCov i j t s

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- The cohort weights sum to one over `Tⱼ`. -/
theorem sum_a (j : J) : ∑ t ∈ M.obs j, M.a j t = 1 := by
  sorry

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (23) on `Tⱼ` minimises `Σ_{t∈Tⱼ} aₜ² σⱼₜ²` among weights on `Tⱼ` summing to one. -/
theorem a_optimal (j : J) (c : T → ℝ) (hc : ∑ t ∈ M.obs j, c t = 1) :
    ∑ t ∈ M.obs j, M.a j t ^ 2 * M.σ j t ^ 2 ≤ ∑ t ∈ M.obs j, c t ^ 2 * M.σ j t ^ 2 := by
  sorry

omit [Fintype J] in
/-- `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ`, as in eq. (27); no `T ≥ 1` needed since `Tⱼ ≠ ∅`. -/
theorem K_apply (i j : J) :
    M.K i j = M.σ2 i j * M.ρ i j + M.τ2 * (if i = j then 1 else 0) := by
  sorry

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Cohorts with no shared period have `σ²ᵢⱼ = 0`. -/
theorem σ2_eq_zero_of_disjoint {i j : J} (h : Disjoint (M.obs i) (M.obs j)) :
    M.σ2 i j = 0 := by
  sorry

omit [Fintype J] in
theorem K_symm : M.Kᵀ = M.K := by
  sorry

/-- `K` stays positive definite for any overlap pattern. It suffices that for
every period `t` the correlations of the cohorts observed at `t` form a
positive-semidefinite matrix: pairs that never overlap do not matter. -/
theorem K_posDef
    (hρ : ∀ t, ((Matrix.of M.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      Subtype.val).PosSemidef) :
    M.K.PosDef := by
  sorry

/-- …in particular under the hypothesis of `Model.K_posDef`. -/
theorem K_posDef_of_posSemidef (hρ : (Matrix.of M.ρ).PosSemidef) : M.K.PosDef := by
  sorry

omit [Fintype J] [DecidableEq J] in
/-- With full series (`Tⱼ = T`) the weights are those of the thesis. -/
theorem a_eq_of_full (h : ∀ j, M.obs j = univ) : M.a = M.toModel.a := by
  sorry

omit [Fintype J] [DecidableEq J] in
/-- With full series, `σ²ᵢⱼ` is that of the thesis, eq. (18). -/
theorem σ2_eq_of_full (h : ∀ j, M.obs j = univ) : M.σ2 = M.toModel.σ2 := by
  sorry

omit [Fintype J] in
/-- With full series, `K` is that of the thesis, eq. (21). -/
theorem K_eq_of_full (h : ∀ j, M.obs j = univ) : M.K = M.toModel.K := by
  sorry

/-! ### Weights and the credibility factor (eqs. (24)–(26)): only `K` changes -/

/-- Portfolio weights `bⱼ`, eq. (25) with the new `K`. -/
noncomputable def b : J → ℝ := glsWeight M.K

/-- Portfolio error variance `s²`, eq. (24) with the new `K`. -/
noncomputable def s2 : ℝ := (invTotal M.K)⁻¹

/-- The moments entering the blend for cohort `j` (§2.4). -/
noncomputable def moments (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := M.s2
  varTarget := M.τ2
  covEst := (M.K *ᵥ M.b) j
  covCohortTarget := M.τ2
  covPortfolioTarget := M.b j * M.τ2

/-- Eqs. (26)/(27) with unequal lengths: the same formula, with the new `σ²ⱼⱼ`, `b`, `s²`. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) := by
  sorry

/-! ### Parameter estimation (§2.8) with unequal lengths -/

/-- `f` reads only observed cells `(j, t)`, `t ∈ Tⱼ`. -/
def Observed (f : (J × T → ℝ) → ℝ) : Prop :=
  ∀ X Y : J × T → ℝ, (∀ j, ∀ t ∈ M.obs j, X (j, t) = Y (j, t)) → f X = f Y

/-- The display before (37), for a shared period `t ∈ Tᵢⱼ`:
`E[(μᵢₜ - μ̂ᵢ)(μⱼₜ - μ̂ⱼ)] = (1 - aᵢₜ - aⱼₜ)σᵢₜσⱼₜρᵢⱼ + σ²ᵢⱼρᵢⱼ`. -/
theorem unbiased_dev (i j : J) {t : T} (ht : t ∈ M.overlap i j) :
    M.toModel.Unbiased
      (fun X => (X (i, t) - ∑ s ∈ M.obs i, M.a i s * X (i, s))
        * (X (j, t) - ∑ s ∈ M.obs j, M.a j s * X (j, s)))
      ((1 - M.a i t - M.a j t) * M.σ i t * M.σ j t * M.ρ i j + M.σ2 i j * M.ρ i j) := by
  sorry

variable (w : J → T → ℝ)

/-- `wⱼ* = Σ_{t∈Tⱼ} wⱼₜ`. -/
def wtot (j : J) : ℝ := ∑ t ∈ M.obs j, w j t

/-- `w** = Σⱼ wⱼ*`. -/
def wall : ℝ := ∑ j, M.wtot w j

/-- `Sᵢⱼ = Σ_{t∈Tᵢⱼ} √(wᵢₜwⱼₜ)`. -/
noncomputable def sqrtSum (i j : J) : ℝ := ∑ t ∈ M.overlap i j, √(w i t * w j t)

/-- The per-pair count `nᵢⱼ = |Tᵢⱼ| - Σ_{Tᵢⱼ} wᵢₜ/wᵢ* - Σ_{Tᵢⱼ} wⱼₜ/wⱼ*`,
replacing `T - 2` in eq. (39). -/
noncomputable def count (i j : J) : ℝ :=
  (#(M.overlap i j) : ℝ) - (∑ t ∈ M.overlap i j, w i t) / M.wtot w i
    - (∑ t ∈ M.overlap i j, w j t) / M.wtot w j

/-- The denominator `Sᵢⱼ + nᵢⱼ wᵢ*wⱼ*/Sᵢⱼ` of the `σ²ᵢⱼρᵢⱼ` estimator. -/
noncomputable def den (i j : J) : ℝ :=
  M.sqrtSum w i j + M.count w i j * M.wtot w i * M.wtot w j / M.sqrtSum w i j

/-- `μ̂ⱼ = Σ_{t∈Tⱼ} (wⱼₜ/wⱼ*) μⱼₜ`. -/
noncomputable def muHat (X : J × T → ℝ) (j : J) : ℝ :=
  ∑ t ∈ M.obs j, w j t / M.wtot w j * X (j, t)

/-- The estimator of `σ²ᵢⱼρᵢⱼ`, first line of eq. (39) with the per-pair count. -/
noncomputable def sigRhoHat (X : J × T → ℝ) (i j : J) : ℝ :=
  (∑ t ∈ M.overlap i j, √(w i t * w j t) * (X (i, t) - M.muHat w X i) * (X (j, t) - M.muHat w X j))
    / M.den w i j

/-- `ĉⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ^`, eq. (39). -/
noncomputable def cHat (X : J × T → ℝ) (j : J) : ℝ :=
  ∑ i, ((if i = j then 1 else 0) - M.wtot w i / M.wall w) * M.sigRhoHat w X i j

/-- The estimator of `τ²`, eq. (39). -/
noncomputable def tauHat (X : J × T → ℝ) : ℝ :=
  (∑ j, M.wtot w j * ((M.muHat w X j - ∑ i, M.wtot w i / M.wall w * M.muHat w X i) ^ 2
      - M.cHat w X j))
    / (M.wall w - ∑ i, M.wtot w i ^ 2 / M.wall w)

/-- `K̂ᵢⱼ = σ²ᵢⱼρᵢⱼ^ + τ̂²δᵢⱼ`, last line of eq. (39). -/
noncomputable def KHat (X : J × T → ℝ) (i j : J) : ℝ :=
  M.sigRhoHat w X i j + M.tauHat w X * (if i = j then 1 else 0)

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- On the diagonal the count is `|Tⱼ| - 2`. -/
theorem count_self (hw : ∀ j t, 0 < w j t) (j : J) :
    M.count w j j = (#(M.obs j) : ℝ) - 2 := by
  sorry

omit [Fintype J] [DecidableEq J] in
/-- With full series the count is the thesis's `T - 2`. -/
theorem count_of_full (hw : ∀ j t, 0 < w j t) (h : ∀ j, M.obs j = univ) (i j : J) :
    M.count w i j = (Fintype.card T : ℝ) - 2 := by
  sorry

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Two or more shared periods make the denominator positive. -/
theorem den_pos_of_two_le (hw : ∀ j t, 0 < w j t) {i j : J} (h : 2 ≤ #(M.overlap i j)) :
    0 < M.den w i j := by
  sorry

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- One shared period `t`: `den · Sᵢⱼ/(wᵢ*wⱼ*) = (1 - wᵢₜ/wᵢ*)(1 - wⱼₜ/wⱼ*)`, so the
denominator is positive iff both cohorts are also observed outside `t`. -/
theorem den_of_overlap_singleton (hw : ∀ j t, 0 < w j t) {i j : J} {t : T}
    (h : M.overlap i j = {t}) :
    M.den w i j * M.sqrtSum w i j / (M.wtot w i * M.wtot w j)
      = (1 - w i t / M.wtot w i) * (1 - w j t / M.wtot w j) := by
  sorry

variable {w} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t) (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- From eq. (29): on `Tⱼ` the special case still gives `aⱼₜ = wⱼₜ/wⱼ*`. -/
theorem a_special (j : J) {t : T} (ht : t ∈ M.obs j) : M.a j t = w j t / M.wtot w j := by
  sorry

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (37) over the shared periods: `σ²ᵢⱼρᵢⱼ = (Sᵢⱼ/(wᵢ*wⱼ*)) σᵢσⱼρᵢⱼ`. -/
theorem σ2ρ_special (i j : J) :
    M.σ2 i j * M.ρ i j
      = M.sqrtSum w i j / (M.wtot w i * M.wtot w j) * (sig i * sig j * M.ρ i j) := by
  sorry

/-- Eq. (39), first line, with the per-pair count: `σ²ᵢⱼρᵢⱼ^` is unbiased whenever
the denominator is positive (or there is no shared period, when both sides are `0`). -/
theorem sigRhoHat_unbiased (i j : J) (hden : (M.overlap i j).Nonempty → 0 < M.den w i j) :
    M.toModel.Unbiased (fun X => M.sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  sorry

/-- Eq. (39): `τ̂²` is unbiased. Needs `J ≥ 2` and a positive denominator for every
overlapping pair (e.g. `|Tᵢⱼ| ≠ 1` for all `i, j`, `den_pos_of_two_le`). -/
theorem tauHat_unbiased (hJ : 2 ≤ Fintype.card J)
    (hden : ∀ i j, (M.overlap i j).Nonempty → 0 < M.den w i j) :
    M.toModel.Unbiased (M.tauHat w) M.τ2 := by
  sorry

/-- Eq. (39), last line: `K̂ᵢⱼ` is unbiased for `Kᵢⱼ`. -/
theorem KHat_unbiased (hJ : 2 ≤ Fintype.card J)
    (hden : ∀ i j, (M.overlap i j).Nonempty → 0 < M.den w i j) (i j : J) :
    M.toModel.Unbiased (fun X => M.KHat w X i j) (M.K i j) := by
  sorry

omit hσ hw in
/-- `K̂ᵢⱼ` reads only observed cells. -/
theorem KHat_observed (i j : J) : M.Observed (fun X => M.KHat w X i j) := by
  sorry

omit hσ [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (41) with unequal lengths: on the diagonal the estimator is Bühlmann–Straub
with the cohort's own length, `σ̂ⱼ²/wⱼ*`, `σ̂ⱼ² = Σ_{t∈Tⱼ} wⱼₜ(μⱼₜ - μ̂ⱼ)²/(|Tⱼ| - 1)`. -/
theorem sigRhoHat_self (X : J × T → ℝ) (j : J) :
    M.sigRhoHat w X j j
      = (∑ t ∈ M.obs j, w j t * (X (j, t) - M.muHat w X j) ^ 2 / ((#(M.obs j) : ℝ) - 1))
        / M.wtot w j := by
  sorry

end Unequal
end Credibility
