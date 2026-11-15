import Credibility.UnequalEstimation

/-!
# Parameter estimation (thesis §2.8, eqs. (37)–(41))

Special case `σⱼₜ = σⱼ/√wⱼₜ` with known volumes `wⱼₜ > 0`: Bühlmann–Straub, but
with a cohort-dependent base variance `σⱼ²` and correlations `ρᵢⱼ`.

Expectation and unbiasedness of quadratic estimators are in `Expectation.lean`.
The thesis observes every cohort in every period: this is `Unequal` with `Tⱼ = T`
(`toUnequal`), so the results below are corollaries of their twins in
`UnequalEstimation.lean`.

Data are indexed by `p = (j, t) : J × T`.
-/

open Finset

namespace Credibility.Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- The display before (37): `E[(μᵢₜ - μ̂ᵢ)(μⱼₜ - μ̂ⱼ)] = (1 - aᵢₜ - aⱼₜ)σᵢₜσⱼₜρᵢⱼ + σ²ᵢⱼρᵢⱼ`,
for any `σⱼₜ`. -/
theorem unbiased_dev (i j : J) (t : T) :
    M.Unbiased (fun X => (X (i, t) - ∑ s, M.a i s * X (i, s)) * (X (j, t) - ∑ s, M.a j s * X (j, s)))
      ((1 - M.a i t - M.a j t) * M.σ i t * M.σ j t * M.ρ i j + M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := ⟨t⟩
  refine (M.toUnequal.unbiased_dev i j (t := t) (by simp [Unequal.overlap, toUnequal])).congr
    (fun X => by rw [toUnequal_a]; rfl) (by rw [toUnequal_a, toUnequal_σ2]; rfl)

/-! ### The special case `σⱼₜ = σⱼ/√wⱼₜ` -/

variable (w : J → T → ℝ)

/-- `wⱼ* = Σₜ wⱼₜ`. -/
def wtot (j : J) : ℝ := ∑ t, w j t

/-- `w** = Σⱼ wⱼ*`. -/
def wall : ℝ := ∑ j, wtot w j

variable {w} in
omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma wtot_pos [Nonempty T] (hw : ∀ j t, 0 < w j t) (j : J) : 0 < wtot w j :=
  sum_pos (fun t _ => hw j t) univ_nonempty

/-- `Sᵢⱼ = Σₜ √(wᵢₜwⱼₜ)`. -/
noncomputable def sqrtSum (i j : J) : ℝ := ∑ t, √(w i t * w j t)

/-- `μ̂ⱼ = Σₜ (wⱼₜ/wⱼ*) μⱼₜ`. -/
noncomputable def muHat (X : J × T → ℝ) (j : J) : ℝ := ∑ t, w j t / wtot w j * X (j, t)

/-- The estimator of `σ²ᵢⱼρᵢⱼ`, first line of eq. (39). -/
noncomputable def sigRhoHat (X : J × T → ℝ) (i j : J) : ℝ :=
  (∑ t, √(w i t * w j t) * (X (i, t) - muHat w X i) * (X (j, t) - muHat w X j))
    / (sqrtSum w i j + ((Fintype.card T : ℝ) - 2) * wtot w i * wtot w j / sqrtSum w i j)

/-- `ĉⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ^`, eq. (39). -/
noncomputable def cHat (X : J × T → ℝ) (j : J) : ℝ :=
  ∑ i, ((if i = j then 1 else 0) - wtot w i / wall w) * sigRhoHat w X i j

/-- The estimator of `τ²`, eq. (39). -/
noncomputable def tauHat (X : J × T → ℝ) : ℝ :=
  (∑ j, wtot w j * ((muHat w X j - ∑ i, wtot w i / wall w * muHat w X i) ^ 2 - cHat w X j))
    / (wall w - ∑ i, wtot w i ^ 2 / wall w)

/-- `K̂ᵢⱼ = σ²ᵢⱼρᵢⱼ^ + τ̂²δᵢⱼ`, last line of eq. (39). -/
noncomputable def KHat (X : J × T → ℝ) (i j : J) : ℝ :=
  sigRhoHat w X i j + tauHat w X * (if i = j then 1 else 0)

/-- The classical Bühlmann–Straub variance estimate, eq. (13):
`σ̂² = (1/J) Σⱼ σ̂ⱼ²` with `σ̂ⱼ² = Σₜ wⱼₜ(μⱼₜ - μ̂ⱼ)²/(T - 1)`. The thesis writes `1/T`, a typo
(Finding 7): there are `J` terms. -/
noncomputable def sigHatBS (X : J × T → ℝ) : ℝ :=
  (∑ j, ∑ t, w j t * (X (j, t) - muHat w X j) ^ 2 / ((Fintype.card T : ℝ) - 1))
    / (Fintype.card J : ℝ)

/-- The classical Bühlmann–Straub estimator of `τ²`, eq. (13):
`τ̂² = (Σⱼ wⱼ*(μ̂ⱼ - Σᵢ (wᵢ*/w**) μ̂ᵢ)² - (J - 1)σ̂²)/(w** - Σⱼ wⱼ*²/w**)`. -/
noncomputable def tauHatBS (X : J × T → ℝ) : ℝ :=
  (∑ j, wtot w j * (muHat w X j - ∑ i, wtot w i / wall w * muHat w X i) ^ 2
      - ((Fintype.card J : ℝ) - 1) * sigHatBS w X)
    / (wall w - ∑ i, wtot w i ^ 2 / wall w)

/-! ### Back to the thesis: the estimators of `Unequal` with `Tⱼ = T` -/

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma toUnequal_wtot [Nonempty T] : M.toUnequal.wtot w = wtot w := rfl

omit [DecidableEq J] [DecidableEq T] in
lemma toUnequal_wall [Nonempty T] : M.toUnequal.wall w = wall w := rfl

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
lemma toUnequal_muHat [Nonempty T] (X : J × T → ℝ) : M.toUnequal.muHat w X = muHat w X := rfl

omit [Fintype J] [DecidableEq J] in
lemma toUnequal_sqrtSum [Nonempty T] : M.toUnequal.sqrtSum w = sqrtSum w := by
  funext i j; simp [Unequal.sqrtSum, sqrtSum, Unequal.overlap, toUnequal]

variable {w} in
omit [Fintype J] [DecidableEq J] in
/-- With `Tⱼ = T` the per-pair count is `T - 2`, so the estimators agree. -/
lemma toUnequal_sigRhoHat [Nonempty T] (hw : ∀ j t, 0 < w j t) (X : J × T → ℝ) :
    M.toUnequal.sigRhoHat w X = sigRhoHat w X := by
  funext i j
  rw [Unequal.sigRhoHat, Unequal.den, M.toUnequal.count_of_full w hw (fun _ => rfl),
    toUnequal_sqrtSum]
  simp [sigRhoHat, Unequal.overlap, toUnequal]
  rfl

variable {w} in
lemma toUnequal_tauHat [Nonempty T] (hw : ∀ j t, 0 < w j t) (X : J × T → ℝ) :
    M.toUnequal.tauHat w X = tauHat w X := by
  simp only [Unequal.tauHat, Unequal.cHat, M.toUnequal_sigRhoHat hw]; rfl

variable {w} in
lemma toUnequal_KHat [Nonempty T] (hw : ∀ j t, 0 < w j t) (X : J × T → ℝ) :
    M.toUnequal.KHat w X = KHat w X := by
  funext i j
  simp only [Unequal.KHat, M.toUnequal_sigRhoHat hw, M.toUnequal_tauHat hw]; rfl

variable {w} in
omit [Fintype J] [DecidableEq J] in
/-- With `T ≥ 2` every denominator `Sᵢⱼ + (T - 2)wᵢ*wⱼ*/Sᵢⱼ` is positive. -/
lemma toUnequal_den_pos [Nonempty T] (hw : ∀ j t, 0 < w j t) (hT : 2 ≤ Fintype.card T)
    (i j : J) : (M.toUnequal.overlap i j).Nonempty → 0 < M.toUnequal.den w i j := fun _ =>
  M.toUnequal.den_pos_of_two_le w hw (by simpa [Unequal.overlap, toUnequal] using hT)

variable {w} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t) (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- §2.8, from eq. (29): the special case still gives `aⱼₜ = wⱼₜ/wⱼ*`. -/
theorem a_special (j : J) (t : T) : M.a j t = w j t / wtot w j := by
  have : Nonempty T := ⟨t⟩
  classical
  rw [← M.toUnequal_a]
  exact M.toUnequal.a_special sig hw hσ j (mem_univ t)

omit [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Eq. (37): `σ²ᵢⱼρᵢⱼ = (Sᵢⱼ/(wᵢ*wⱼ*)) σᵢσⱼρᵢⱼ`. -/
theorem σ2ρ_special (i j : J) :
    M.σ2 i j * M.ρ i j = sqrtSum w i j / (wtot w i * wtot w j) * (sig i * sig j * M.ρ i j) := by
  rcases isEmpty_or_nonempty T with hT | hT
  · simp [σ2, sqrtSum]
  classical
  rw [← M.toUnequal_σ2, ← M.toUnequal_sqrtSum]
  exact M.toUnequal.σ2ρ_special sig hw hσ i j

/-- Eq. (39), first line: `σ²ᵢⱼρᵢⱼ^` is unbiased. Needs `T ≥ 2`: with one
period the denominator is `0`. -/
theorem sigRhoHat_unbiased (hT : 2 ≤ Fintype.card T) (i j : J) :
    M.Unbiased (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  refine (M.toUnequal.sigRhoHat_unbiased sig hw hσ i j (M.toUnequal_den_pos hw hT i j)).congr
    (fun X => by rw [M.toUnequal_sigRhoHat hw]) (by rw [toUnequal_σ2]; rfl)

/-- `ĉⱼ` is unbiased for `cⱼ = Σᵢ (δᵢⱼ - wᵢ*/w**) σ²ᵢⱼρᵢⱼ`. -/
theorem cHat_unbiased (hT : 2 ≤ Fintype.card T) (j : J) :
    M.Unbiased (fun X => cHat w X j)
      (∑ i, ((if i = j then 1 else 0) - wtot w i / wall w) * (M.σ2 i j * M.ρ i j)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact (M.toUnequal.cHat_unbiased sig hw hσ (M.toUnequal_den_pos hw hT) j).congr
    (fun X => by simp only [Unequal.cHat, M.toUnequal_sigRhoHat hw]; rfl)
    (by rw [toUnequal_σ2]; rfl)

/-- Eq. (39): `τ̂²` is unbiased. Needs `T ≥ 2` and `J ≥ 2`: with one cohort
the denominator `w** - Σᵢ wᵢ*²/w**` is `0`. -/
theorem tauHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) :
    M.Unbiased (tauHat w) M.τ2 := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact (M.toUnequal.tauHat_unbiased sig hw hσ hJ (M.toUnequal_den_pos hw hT)).congr
    (fun X => by rw [M.toUnequal_tauHat hw]) rfl

/-- Eq. (39), last line: `K̂ᵢⱼ` is unbiased for `Kᵢⱼ`. -/
theorem KHat_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (i j : J) :
    M.Unbiased (fun X => KHat w X i j) (M.K i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact (M.toUnequal.KHat_unbiased sig hw hσ hJ (M.toUnequal_den_pos hw hT) i j).congr
    (fun X => by rw [M.toUnequal_KHat hw]) (by rw [toUnequal_K])

omit hσ [Fintype J] [DecidableEq J] [DecidableEq T] in
/-- Eq. (41): on the diagonal the estimator is the Bühlmann–Straub one,
`σ²ⱼⱼ^ = σ̂ⱼ²/wⱼ*` with `σ̂ⱼ² = Σₜ wⱼₜ(μⱼₜ - μ̂ⱼ)²/(T - 1)` from eq. (13). -/
theorem sigRhoHat_self (X : J × T → ℝ) (j : J) :
    sigRhoHat w X j j
      = (∑ t, w j t * (X (j, t) - muHat w X j) ^ 2 / ((Fintype.card T : ℝ) - 1)) / wtot w j := by
  rcases isEmpty_or_nonempty T with hT | hT
  · simp [sigRhoHat]
  classical
  -- The estimator does not involve the model; any one will do.
  let M₀ : Model J T := ⟨1, fun _ _ => 1, fun _ _ => 1, one_pos, fun _ _ => one_pos,
    fun _ => rfl, fun _ _ => rfl⟩
  rw [← M₀.toUnequal_sigRhoHat hw, M₀.toUnequal.sigRhoHat_self hw X j]
  simp [toUnequal]
  rfl

/-- PLAN G0, eq. (13): with uncorrelated cohorts (`ρᵢⱼ = 0` for `i ≠ j`) and a common
base variance `σⱼ = s` (the Bühlmann–Straub model), the classical `τ̂²` is unbiased.
Proof: it differs from the thesis estimator (39) by `(Σⱼ wⱼ*ĉⱼ - (J - 1)σ̂²)/D`, and
both `Σⱼ wⱼ*ĉⱼ` and `(J - 1)σ̂²` estimate `(J - 1)s²` without bias. -/
theorem tauHatBS_unbiased (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J)
    (hρ : ∀ i j, i ≠ j → M.ρ i j = 0) (s : ℝ) (hs : ∀ j, sig j = s) :
    M.Unbiased (tauHatBS w) M.τ2 := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hW : ∀ k, 0 < wtot w k := wtot_pos hw
  have hWall : 0 < wall w := sum_pos (fun k _ => hW k) univ_nonempty
  have hJ0 : (Fintype.card J : ℝ) ≠ 0 := by positivity
  set D := wall w - ∑ i, wtot w i ^ 2 / wall w
  -- `wⱼ* σ²ⱼⱼ^` is the cohort's `σ̂ⱼ²`, eq. (41).
  have hself : ∀ X j, wtot w j * sigRhoHat w X j j
      = ∑ t, w j t * (X (j, t) - muHat w X j) ^ 2 / ((Fintype.card T : ℝ) - 1) := fun X j => by
    rw [sigRhoHat_self hw X j]; field_simp [(hW j).ne']
  have key : ∀ X, tauHat w X + 1 / D * ((∑ j, wtot w j * cHat w X j)
      + -(((Fintype.card J : ℝ) - 1) / Fintype.card J) * ∑ j, wtot w j * sigRhoHat w X j j)
        = tauHatBS w X := fun X => by
    simp only [tauHatBS, tauHat, sigHatBS, hself, mul_sub, sum_sub_distrib]
    field_simp
    ring
  -- Under the Bühlmann–Straub model `σ²ᵢⱼρᵢⱼ = δᵢⱼ s²/wⱼ*`.
  have hS : ∀ j, sqrtSum w j j = wtot w j := fun j =>
    sum_congr rfl fun t _ => Real.sqrt_mul_self (hw j t).le
  have hσρ : ∀ i j, M.σ2 i j * M.ρ i j = if i = j then s ^ 2 / wtot w j else 0 := fun i j => by
    split_ifs with h
    · subst h
      rw [M.σ2ρ_special sig hw hσ, hS, hs, M.ρ_self]
      field_simp [(hW i).ne']
    · rw [hρ i j h, mul_zero]
  have hx : ∑ j, wtot w j / wall w = 1 := by rw [← sum_div]; exact div_self hWall.ne'
  have hc : ∑ j, wtot w j * ∑ i, ((if i = j then 1 else 0) - wtot w i / wall w)
      * (M.σ2 i j * M.ρ i j) = ((Fintype.card J : ℝ) - 1) * s ^ 2 := by
    simp only [hσρ, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [← sub_eq_zero]
    have : ∀ j, wtot w j * ((1 - wtot w j / wall w) * (s ^ 2 / wtot w j))
        = s ^ 2 - s ^ 2 * (wtot w j / wall w) := fun j => by field_simp [(hW j).ne']
    simp only [this, sum_sub_distrib, ← mul_sum, hx, sum_const, card_univ, nsmul_eq_mul]
    ring
  have hd : ∑ j, wtot w j * (M.σ2 j j * M.ρ j j) = (Fintype.card J : ℝ) * s ^ 2 := by
    simp only [hσρ, ite_true]
    rw [sum_congr rfl fun j _ => by rw [mul_div_cancel₀ _ (hW j).ne']]
    simp
  refine ((M.tauHat_unbiased sig hw hσ hT hJ).add
    (((UnbiasedCov.sum univ fun j _ => (M.cHat_unbiased sig hw hσ hT j).const_mul (wtot w j)).add
      ((UnbiasedCov.sum univ fun j _ =>
        (M.sigRhoHat_unbiased sig hw hσ hT j j).const_mul (wtot w j)).const_mul
          (-(((Fintype.card J : ℝ) - 1) / Fintype.card J)))).const_mul (1 / D))).congr key ?_
  rw [hc, hd]
  field_simp
  ring

end Credibility.Model
