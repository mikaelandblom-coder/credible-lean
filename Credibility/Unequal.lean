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
  have hpos : 0 < ∑ s ∈ M.obs j, (M.σ j s ^ 2)⁻¹ :=
    sum_pos (fun s _ => inv_pos.mpr (pow_pos (M.σ_pos j s) 2)) (M.obs_nonempty j)
  simp only [a]
  rw [sum_ite_of_true (fun t ht => ht), ← sum_div, div_self hpos.ne']

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (23) on `Tⱼ` minimises `Σ_{t∈Tⱼ} aₜ² σⱼₜ²` among weights on `Tⱼ` summing to one. -/
theorem a_optimal (j : J) (c : T → ℝ) (hc : ∑ t ∈ M.obs j, c t = 1) :
    ∑ t ∈ M.obs j, M.a j t ^ 2 * M.σ j t ^ 2 ≤ ∑ t ∈ M.obs j, c t ^ 2 * M.σ j t ^ 2 := by
  set S := ∑ s ∈ M.obs j, (M.σ j s ^ 2)⁻¹
  have hS : S ≠ 0 :=
    (sum_pos (fun s _ => inv_pos.mpr (pow_pos (M.σ_pos j s) 2)) (M.obs_nonempty j)).ne'
  have hσ : ∀ t, M.σ j t ^ 2 ≠ 0 := fun t => pow_ne_zero 2 (M.σ_pos j t).ne'
  have ha : ∀ t ∈ M.obs j, M.a j t = (M.σ j t ^ 2)⁻¹ / S := fun t ht => by
    simp only [a, ht, ↓reduceIte, S]
  -- `Σ a²σ² = Σ c a σ² = 1/S`, and `Σ (c - a)²σ² ≥ 0`.
  have h1 : ∑ t ∈ M.obs j, M.a j t ^ 2 * M.σ j t ^ 2 = S⁻¹ := by
    rw [sum_congr rfl fun t ht => by rw [ha t ht]]
    have : ∀ t, ((M.σ j t ^ 2)⁻¹ / S) ^ 2 * M.σ j t ^ 2 = (M.σ j t ^ 2)⁻¹ / S ^ 2 := fun t => by
      field_simp [hσ t]
    simp only [this, ← sum_div]
    change S / S ^ 2 = S⁻¹
    field_simp
  have h2 : ∑ t ∈ M.obs j, c t * M.a j t * M.σ j t ^ 2 = S⁻¹ := by
    rw [sum_congr rfl fun t ht => by rw [ha t ht]]
    have : ∀ t, c t * ((M.σ j t ^ 2)⁻¹ / S) * M.σ j t ^ 2 = c t / S := fun t => by
      field_simp [hσ t, (M.σ_pos j t).ne']
    simp only [this, ← sum_div, hc, one_div]
  have hnn : 0 ≤ ∑ t ∈ M.obs j, (c t - M.a j t) ^ 2 * M.σ j t ^ 2 :=
    sum_nonneg fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hexp : ∑ t ∈ M.obs j, (c t - M.a j t) ^ 2 * M.σ j t ^ 2
      = ∑ t ∈ M.obs j, c t ^ 2 * M.σ j t ^ 2 - 2 * ∑ t ∈ M.obs j, c t * M.a j t * M.σ j t ^ 2
        + ∑ t ∈ M.obs j, M.a j t ^ 2 * M.σ j t ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  rw [hexp, h1, h2] at hnn
  rw [h1]
  linarith

omit [Fintype J] [Fintype T] in
/-- `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ`, as in eq. (27); no `T ≥ 1` needed since `Tⱼ ≠ ∅`. -/
theorem K_apply (i j : J) :
    M.K i j = M.σ2 i j * M.ρ i j + M.τ2 * (if i = j then 1 else 0) := by
  simp only [K, Model.obsCov, mul_add, sum_add_distrib]
  congr 1
  · simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, ← sum_filter, filter_mem_eq_inter]
    rw [σ2, overlap, sum_mul]
    exact sum_congr rfl fun t _ => by ring
  · split_ifs with h
    · subst h
      calc ∑ x ∈ M.obs i, ∑ y ∈ M.obs i, M.a i x * M.a i y * (M.τ2 * 1)
          = (∑ x ∈ M.obs i, M.a i x) * (∑ y ∈ M.obs i, M.a i y) * M.τ2 := by
            rw [sum_mul_sum, sum_mul]; simp_rw [sum_mul, mul_one]
        _ = M.τ2 * 1 := by rw [M.sum_a]; ring
    · simp

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Cohorts with no shared period have `σ²ᵢⱼ = 0`. -/
theorem σ2_eq_zero_of_disjoint {i j : J} (h : Disjoint (M.obs i) (M.obs j)) :
    M.σ2 i j = 0 := by
  simp [σ2, overlap, disjoint_iff_inter_eq_empty.mp h]

omit [Fintype J] [Fintype T] in
theorem K_symm : M.Kᵀ = M.K := by
  ext i j
  simp only [transpose_apply, K, Model.obsCov]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  rw [M.ρ_symm j i]
  simp only [eq_comm (a := s), eq_comm (a := j)]
  ring

/-- `K` stays positive definite for any overlap pattern. It suffices that for
every period `t` the correlations of the cohorts observed at `t` form a
positive-semidefinite matrix: pairs that never overlap do not matter. -/
theorem K_posDef
    (hρ : ∀ t, ((Matrix.of M.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      Subtype.val).PosSemidef) :
    M.K.PosDef := by
  have ha0 : ∀ j t, t ∉ M.obs j → M.a j t = 0 := fun j t ht => by simp [a, ht]
  -- `σ²ᵢⱼ` as a sum over all periods, since `aⱼₜ = 0` off `Tⱼ`.
  have hσ2 : ∀ i j, M.σ2 i j = ∑ t, M.a i t * M.a j t * M.σ i t * M.σ j t := fun i j => by
    refine sum_subset (subset_univ _) fun t _ ht => ?_
    rcases not_and_or.mp (mt mem_inter.mpr ht) with h | h <;> simp [ha0 _ _ h]
  -- Sums over `J` of terms vanishing off `Jₜ` are sums over `Jₜ`.
  have hS : ∀ t (f : J → ℝ), (∀ j, t ∉ M.obs j → f j = 0) →
      ∑ j, f j = ∑ j : {j // t ∈ M.obs j}, f j := fun t f hf => by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => t ∈ M.obs j) f,
      Fintype.sum_eq_zero (fun j : {j // ¬t ∈ M.obs j} => f j) fun j => hf j j.2, add_zero]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, M.K_symm]
  -- `xᵀKx = Σₜ yₜᵀ R yₜ + τ²‖x‖²` with `(yₜ)ⱼ = aⱼₜ σⱼₜ xⱼ`, supported on `Jₜ`.
  set y : T → J → ℝ := fun t j => M.a j t * M.σ j t * x j
  have hy : ∀ t j, t ∉ M.obs j → y t j = 0 := fun t j h => by simp [y, ha0 _ _ h]
  have key : star x ⬝ᵥ (M.K *ᵥ x)
      = ∑ t, star (y t) ⬝ᵥ (Matrix.of M.ρ *ᵥ y t) + M.τ2 * ∑ i, x i ^ 2 := by
    simp only [dotProduct, mulVec, M.K_apply, hσ2, star_trivial, of_apply, y, add_mul,
      mul_add, sum_add_distrib, ite_mul, mul_ite, mul_one, mul_zero, zero_mul, sum_ite_eq,
      mem_univ, ite_true, mul_sum, sum_mul]
    congr 1
    · symm
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring
    · exact sum_congr rfl fun i _ => by ring
  rw [key]
  have h1 : 0 ≤ ∑ t, star (y t) ⬝ᵥ (Matrix.of M.ρ *ᵥ y t) := by
    refine sum_nonneg fun t _ => ?_
    have := (hρ t).dotProduct_mulVec_nonneg (fun j => y t j.1)
    convert this using 1
    simp only [dotProduct, mulVec, star_trivial, submatrix_apply, of_apply]
    rw [hS t _ fun j h => by simp [hy t j h]]
    refine sum_congr rfl fun i _ => ?_
    rw [hS t _ fun j h => by simp [hy t j h]]
  have h2 : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩
  nlinarith [M.τ2_pos]

/-- …in particular under the hypothesis of `Model.K_posDef`. -/
theorem K_posDef_of_posSemidef (hρ : (Matrix.of M.ρ).PosSemidef) : M.K.PosDef :=
  M.K_posDef fun _ => hρ.submatrix _

omit [Fintype J] [DecidableEq J] in
/-- With full series (`Tⱼ = T`) the weights are those of the thesis. -/
theorem a_eq_of_full (h : ∀ j, M.obs j = univ) : M.a = M.toModel.a := by
  funext j t
  simp [a, Model.a, invVarWeight, h]

omit [Fintype J] [DecidableEq J] in
/-- With full series, `σ²ᵢⱼ` is that of the thesis, eq. (18). -/
theorem σ2_eq_of_full (h : ∀ j, M.obs j = univ) : M.σ2 = M.toModel.σ2 := by
  funext i j
  simp [σ2, Model.σ2, overlap, h, M.a_eq_of_full h]

omit [Fintype J] in
/-- With full series, `K` is that of the thesis, eq. (21). -/
theorem K_eq_of_full (h : ∀ j, M.obs j = univ) : M.K = M.toModel.K := by
  funext i j
  simp [K, Model.K, h, M.a_eq_of_full h]

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

omit [Fintype T] in
/-- Eqs. (26)/(27) with unequal lengths: the same formula, with the new `σ²ⱼⱼ`, `b`, `s²`. -/
theorem bestZ_eq (hK : M.K.PosDef) (j : J) :
    (M.moments j).bestZ = (1 - M.b j) * M.τ2 / (M.τ2 + M.σ2 j j - M.s2) := by
  -- `v = K b = s² u` (`mulVec_glsWeight`), substituted into eq. (22).
  have hv : (M.K *ᵥ M.b) j = M.s2 := by
    rw [b, mulVec_glsWeight hK, s2]
  rw [BlendMoments.bestZ, show (M.moments j).gap = M.τ2 + M.σ2 j j - M.s2 by
    simp only [BlendMoments.gap, moments, hv]; ring]
  simp only [moments, hv]
  ring

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
