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

omit [Fintype J] [DecidableEq J] in
/-- `aⱼₜ = 0` off `Tⱼ`, so sums over `Tⱼ` are sums over all of `T`. -/
lemma sum_a_mul (j : J) (F : T → ℝ) : ∑ t ∈ M.obs j, M.a j t * F t = ∑ t, M.a j t * F t :=
  sum_subset (subset_univ _) fun t _ ht => by simp [a, ht]

omit [Fintype J] [DecidableEq J] in
/-- `σ²ᵢⱼ` as a sum over all periods. -/
lemma σ2_eq_sum (i j : J) : M.σ2 i j = ∑ t, M.a i t * M.a j t * M.σ i t * M.σ j t := by
  refine sum_subset (subset_univ _) fun t _ ht => ?_
  rcases not_and_or.mp (mt mem_inter.mpr ht) with h | h <;> simp [a, h]

omit [Fintype J] in
/-- `K` as a double sum over all periods. -/
lemma K_eq_sum (i j : J) :
    M.K i j = ∑ t, ∑ s, M.a i t * M.a j s * M.toModel.obsCov i j t s := by
  simp only [K]
  rw [sum_subset (subset_univ (M.obs i)) fun t _ ht => by simp [a, ht]]
  exact sum_congr rfl fun t _ => sum_subset (subset_univ _) fun s _ hs => by simp [a, hs]

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
`E[(μᵢₜ - μ̂ᵢ)(μⱼₜ - μ̂ⱼ)] = (1 - aᵢₜ - aⱼₜ)σᵢₜσⱼₜρᵢⱼ + σ²ᵢⱼρᵢⱼ`. The algebra holds
for any `t`; `t ∈ Tᵢⱼ` is what makes both factors observed. -/
theorem unbiased_dev (i j : J) {t : T} (_ht : t ∈ M.overlap i j) :
    M.toModel.Unbiased
      (fun X => (X (i, t) - ∑ s ∈ M.obs i, M.a i s * X (i, s))
        * (X (j, t) - ∑ s ∈ M.obs j, M.a j s * X (j, s)))
      ((1 - M.a i t - M.a j t) * M.σ i t * M.σ j t * M.ρ i j + M.σ2 i j * M.ρ i j) := by
  have ha : ∀ k, ∑ s, M.a k s = 1 := fun k => by
    have := M.sum_a_mul k (fun _ => 1)
    simp only [mul_one] at this
    rw [← this, M.sum_a]
  refine (?_ : M.toModel.Unbiased (fun X => (X (i, t) - ∑ s, M.a i s * X (i, s))
    * (X (j, t) - ∑ s, M.a j s * X (j, s))) _).congr
    (fun X => by rw [M.sum_a_mul i (fun s => X (i, s)), M.sum_a_mul j (fun s => X (j, s))]) rfl
  -- Coefficients of `μₖₜ - μ̂ₖ`.
  let ℓ : J → J × T → ℝ := fun k p =>
    if p.1 = k then (if p.2 = t then 1 else 0) - M.a k p.2 else 0
  have hlin : ∀ (k : J) (F : J × T → ℝ),
      ∑ p, ℓ k p * F p = F (k, t) - ∑ s, M.a k s * F (k, s) := by
    intro k F
    rw [Fintype.sum_prod_type, Finset.sum_eq_single k (fun b _ hb => by simp [ℓ, hb]) (by simp)]
    simp [ℓ, sub_mul, sum_sub_distrib, ite_mul]
  have hsum : ∑ p, ℓ i p = 0 := by
    have := hlin i (fun _ => 1)
    simp only [mul_one, ha] at this
    rw [this]; ring
  refine (M.toModel.unbiased_mul (ℓ i) (ℓ j) hsum).congr (fun X => by rw [hlin, hlin]) ?_
  simp_rw [mul_assoc, ← mul_sum, hlin]
  simp only [Model.obsCov, mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, ite_true]
  rw [M.σ2_eq_sum, sum_mul]
  split_ifs <;>
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite, mul_zero, add_zero,
    sum_ite_eq', mem_univ, ite_true, ← sum_mul, ha, sum_const_zero] <;>
  ring_nf <;> rw [mul_sum] <;> ring_nf

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
  have hW : M.wtot w j ≠ 0 := (sum_pos (fun s _ => hw j s) (M.obs_nonempty j)).ne'
  simp only [count, overlap, inter_self]
  rw [show ∑ t ∈ M.obs j, w j t = M.wtot w j from rfl, div_self hW]
  ring

omit [Fintype J] [DecidableEq J] in
/-- With full series the count is the thesis's `T - 2`. -/
theorem count_of_full (hw : ∀ j t, 0 < w j t) (h : ∀ j, M.obs j = univ) (i j : J) :
    M.count w i j = (Fintype.card T : ℝ) - 2 := by
  have hW : ∀ k, M.wtot w k ≠ 0 := fun k =>
    (sum_pos (fun s _ => hw k s) (M.obs_nonempty k)).ne'
  have hO : M.overlap i j = univ := by simp [overlap, h]
  have hw' : ∀ k, ∑ t ∈ M.overlap i j, w k t = M.wtot w k := fun k => by rw [hO, wtot, h]
  rw [count, hw', hw', div_self (hW i), div_self (hW j), hO, card_univ]
  ring

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Two or more shared periods make the denominator positive. -/
theorem den_pos_of_two_le (hw : ∀ j t, 0 < w j t) {i j : J} (h : 2 ≤ #(M.overlap i j)) :
    0 < M.den w i j := by
  have hO : (M.overlap i j).Nonempty := card_pos.mp (by omega)
  have hS : 0 < M.sqrtSum w i j :=
    sum_pos (fun t _ => Real.sqrt_pos.mpr (mul_pos (hw i t) (hw j t))) hO
  have hW : ∀ k, 0 < M.wtot w k := fun k => sum_pos (fun s _ => hw k s) (M.obs_nonempty k)
  -- Each cohort has at most all of its volume in the overlap, so `nᵢⱼ ≥ 2 - 1 - 1`.
  have hle : ∀ k, M.overlap i j ⊆ M.obs k →
      (∑ t ∈ M.overlap i j, w k t) / M.wtot w k ≤ 1 := fun k hk => by
    rw [div_le_one (hW k)]
    exact sum_le_sum_of_subset_of_nonneg hk fun t _ _ => (hw k t).le
  have hc : 0 ≤ M.count w i j := by
    have h2 : (2 : ℝ) ≤ #(M.overlap i j) := by exact_mod_cast h
    have := hle i inter_subset_left
    have := hle j inter_subset_right
    simp only [count]; linarith
  have := mul_nonneg (mul_nonneg hc (hW i).le) (hW j).le
  exact add_pos_of_pos_of_nonneg hS (div_nonneg this hS.le)

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- One shared period `t`: `den · Sᵢⱼ/(wᵢ*wⱼ*) = (1 - wᵢₜ/wᵢ*)(1 - wⱼₜ/wⱼ*)`, so the
denominator is positive iff both cohorts are also observed outside `t`. -/
theorem den_of_overlap_singleton (hw : ∀ j t, 0 < w j t) {i j : J} {t : T}
    (h : M.overlap i j = {t}) :
    M.den w i j * M.sqrtSum w i j / (M.wtot w i * M.wtot w j)
      = (1 - w i t / M.wtot w i) * (1 - w j t / M.wtot w j) := by
  have hWi : M.wtot w i ≠ 0 := (sum_pos (fun s _ => hw i s) (M.obs_nonempty i)).ne'
  have hWj : M.wtot w j ≠ 0 := (sum_pos (fun s _ => hw j s) (M.obs_nonempty j)).ne'
  have hS0 : 0 < √(w i t * w j t) := Real.sqrt_pos.mpr (mul_pos (hw i t) (hw j t))
  have hsq : √(w i t * w j t) ^ 2 = w i t * w j t :=
    Real.sq_sqrt (mul_pos (hw i t) (hw j t)).le
  simp only [den, count, sqrtSum, h, sum_singleton, card_singleton, Nat.cast_one]
  field_simp
  rw [hsq]
  ring

variable {w} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t) (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- From eq. (29): on `Tⱼ` the special case still gives `aⱼₜ = wⱼₜ/wⱼ*`. -/
theorem a_special (j : J) {t : T} (ht : t ∈ M.obs j) : M.a j t = w j t / M.wtot w j := by
  have hs : sig j ≠ 0 := by
    intro h; have := M.σ_pos j t; rw [hσ, h, zero_div] at this; exact lt_irrefl _ this
  have hsq : ∀ s, M.σ j s ^ 2 = sig j ^ 2 / w j s := fun s => by
    rw [hσ, div_pow, Real.sq_sqrt (hw j s).le]
  simp only [a, ht, ↓reduceIte, hsq, inv_div]
  rw [← sum_div, div_div_div_cancel_right₀ (pow_ne_zero 2 hs), wtot]

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (37) over the shared periods: `σ²ᵢⱼρᵢⱼ = (Sᵢⱼ/(wᵢ*wⱼ*)) σᵢσⱼρᵢⱼ`. -/
theorem σ2ρ_special (i j : J) :
    M.σ2 i j * M.ρ i j
      = M.sqrtSum w i j / (M.wtot w i * M.wtot w j) * (sig i * sig j * M.ρ i j) := by
  -- `aᵢₜσᵢₜ = σᵢ√wᵢₜ/wᵢ*` on `Tᵢ`.
  have key : ∀ k t, t ∈ M.obs k → M.a k t * M.σ k t = sig k * √(w k t) / M.wtot w k :=
    fun k t ht => by
      rw [M.a_special sig hw hσ k ht, hσ]
      have := Real.sqrt_pos.mpr (hw k t)
      rw [← Real.sq_sqrt (hw k t).le]
      field_simp
      rw [Real.sqrt_sq (Real.sqrt_nonneg _)]; ring
  simp only [σ2, sqrtSum, sum_mul, div_mul_eq_mul_div, sum_div]
  refine sum_congr rfl fun t ht => ?_
  rw [Real.sqrt_mul (hw i t).le,
    show M.a i t * M.a j t * M.σ i t * M.σ j t = (M.a i t * M.σ i t) * (M.a j t * M.σ j t) by ring,
    key i t (mem_inter.mp ht).1, key j t (mem_inter.mp ht).2]
  ring

/-- Eq. (39), first line, with the per-pair count: `σ²ᵢⱼρᵢⱼ^` is unbiased whenever
the denominator is positive (or there is no shared period, when both sides are `0`). -/
theorem sigRhoHat_unbiased (i j : J) (hden : (M.overlap i j).Nonempty → 0 < M.den w i j) :
    M.toModel.Unbiased (fun X => M.sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  rcases (M.overlap i j).eq_empty_or_nonempty with hO | hO
  · refine ⟨0, fun X => ?_, fun μ => ?_⟩
    · simp [Model.quad, sigRhoHat, hO]
    · simp [Model.E, σ2, hO]
  have hden' := hden hO
  have hW : ∀ k, 0 < M.wtot w k := fun k => sum_pos (fun s _ => hw k s) (M.obs_nonempty k)
  have hS : 0 < M.sqrtSum w i j :=
    sum_pos (fun t _ => Real.sqrt_pos.mpr (mul_pos (hw i t) (hw j t))) hO
  have hmu : ∀ X k, M.muHat w X k = ∑ s ∈ M.obs k, M.a k s * X (k, s) := fun X k =>
    sum_congr rfl fun s hs => by rw [M.a_special sig hw hσ k hs]
  -- The estimator is a combination of the residual products of `unbiased_dev`.
  refine (Model.Unbiased.const_mul (M.den w i j)⁻¹ (Model.Unbiased.sum (M.overlap i j) fun t ht =>
    (M.unbiased_dev i j ht).const_mul √(w i t * w j t))).congr (fun X => ?_) ?_
  · simp only [sigRhoHat, hmu, div_eq_mul_inv, sum_mul, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  · -- `√(wᵢₜwⱼₜ) σᵢₜσⱼₜ = σᵢσⱼ`, and `Σ_{Tᵢⱼ} (1 - aᵢₜ - aⱼₜ) = nᵢⱼ`.
    have hterm : ∀ t ∈ M.overlap i j, √(w i t * w j t) * ((1 - M.a i t - M.a j t) * M.σ i t
          * M.σ j t * M.ρ i j + M.σ2 i j * M.ρ i j)
        = (1 - w i t / M.wtot w i - w j t / M.wtot w j) * (sig i * sig j * M.ρ i j)
          + √(w i t * w j t) * (M.σ2 i j * M.ρ i j) := fun t ht => by
      rw [M.a_special sig hw hσ i (mem_inter.mp ht).1, M.a_special sig hw hσ j (mem_inter.mp ht).2,
        hσ, hσ, Real.sqrt_mul (hw i t).le]
      have := Real.sqrt_pos.mpr (hw i t)
      have := Real.sqrt_pos.mpr (hw j t)
      field_simp
    have hcount : ∑ t ∈ M.overlap i j, (1 - w i t / M.wtot w i - w j t / M.wtot w j)
        = M.count w i j := by
      simp only [count, sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
    rw [sum_congr rfl hterm]
    simp only [sum_add_distrib, ← sum_mul, hcount]
    rw [show ∑ t ∈ M.overlap i j, √(w i t * w j t) = M.sqrtSum w i j from rfl,
      M.σ2ρ_special sig hw hσ, inv_mul_eq_iff_eq_mul₀ hden'.ne']
    simp only [den]
    have := (hW i).ne'; have := (hW j).ne'; have := hS.ne'
    field_simp
    ring

/-- Eq. (39): `τ̂²` is unbiased. Needs `J ≥ 2` and a positive denominator for every
overlapping pair (e.g. `|Tᵢⱼ| ≠ 1` for all `i, j`, `den_pos_of_two_le`). -/
theorem tauHat_unbiased (hJ : 2 ≤ Fintype.card J)
    (hden : ∀ i j, (M.overlap i j).Nonempty → 0 < M.den w i j) :
    M.toModel.Unbiased (M.tauHat w) M.τ2 := by
  have hW : ∀ k, 0 < M.wtot w k := fun k => sum_pos (fun s _ => hw k s) (M.obs_nonempty k)
  have : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have pull1 : ∀ (j : J) (g : J → T → ℝ),
      ∑ k, ∑ s, (if k = j then g k s else 0) = ∑ s, g j s := fun j g => by
    rw [sum_comm]; simp [sum_ite_eq']
  have hWall : 0 < M.wall w := sum_pos (fun k _ => hW k) univ_nonempty
  -- Cohort shares `xₖ = wₖ*/w**`, summing to one.
  set x : J → ℝ := fun k => M.wtot w k / M.wall w with hx_def
  have hx : ∑ k, x k = 1 := by rw [hx_def, ← sum_div]; exact div_self hWall.ne'
  have hxpos : ∀ k, 0 < x k := fun k => div_pos (hW k) hWall
  -- `J ≥ 2` gives `Σ xₖ² < 1`, so the denominator `w**(1 - Σ xₖ²)` is positive.
  have hx1 : ∀ k, x k < 1 := fun k => by
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) k
    rw [← hx, ← add_sum_erase _ _ (mem_univ k)]
    have : 0 < ∑ m ∈ univ.erase k, x m :=
      sum_pos (fun m _ => hxpos m) ⟨l, mem_erase.mpr ⟨hl, mem_univ _⟩⟩
    linarith
  have hQ : ∑ k, x k ^ 2 < 1 := by
    rw [← hx]
    exact sum_lt_sum_of_nonempty univ_nonempty fun k _ => by
      nlinarith [hxpos k, hx1 k]
  have hdenom : M.wall w - ∑ i, M.wtot w i ^ 2 / M.wall w = M.wall w * (1 - ∑ k, x k ^ 2) := by
    simp only [hx_def, div_pow, ← sum_div, mul_sub, mul_one]
    field_simp
  have hden_pos : 0 < M.wall w * (1 - ∑ k, x k ^ 2) := mul_pos hWall (by linarith)
  have hmu : ∀ X k, M.muHat w X k = ∑ s, M.a k s * X (k, s) := fun X k => by
    rw [← M.sum_a_mul k (fun s => X (k, s))]
    exact sum_congr rfl fun s hs => by rw [M.a_special sig hw hσ k hs]
  -- Coefficients of `μ̂ⱼ - Σᵢ xᵢμ̂ᵢ`.
  let ℓ : J → J × T → ℝ := fun j p => ((if p.1 = j then 1 else 0) - x p.1) * M.a p.1 p.2
  have ha : ∀ k, ∑ s, M.a k s = 1 := fun k => by
    have := M.sum_a_mul k (fun _ => 1)
    simp only [mul_one] at this
    rw [← this, M.sum_a]
  have hlin : ∀ j (X : J × T → ℝ), ∑ p, ℓ j p * X p
      = M.muHat w X j - ∑ i, M.wtot w i / M.wall w * M.muHat w X i := fun j X => by
    simp only [ℓ, hmu, Fintype.sum_prod_type, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib,
      mul_assoc, ← mul_sum, hx_def, pull1]
  have hsum : ∀ j, ∑ p, ℓ j p = 0 := fun j => by
    have h1 : ∀ k, ∑ s, ((if k = j then 1 else 0) - x k) * M.a k s
        = (if k = j then 1 else 0) - x k := fun k => by rw [← mul_sum, ha, mul_one]
    rw [Fintype.sum_prod_type]
    simp only [ℓ, h1]
    simp [sum_sub_distrib, hx]
  have hcov : ∀ j, ∑ p, ∑ q, ℓ j p * ℓ j q * M.obsCov p.1 q.1 p.2 q.2
      = ∑ k, ∑ l, ((if k = j then 1 else 0) - x k) * ((if l = j then 1 else 0) - x l) * M.K k l :=
    fun j => by
      simp only [ℓ, Fintype.sum_prod_type, K_eq_sum, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ => sum_congr rfl fun s _ => sum_congr rfl fun r _ => by ring
  have hsq : ∀ j, M.toModel.Unbiased (fun X => (M.muHat w X j - ∑ i, M.wtot w i / M.wall w * M.muHat w X i) ^ 2)
      (∑ k, ∑ l, ((if k = j then 1 else 0) - x k) * ((if l = j then 1 else 0) - x l) * M.K k l) :=
    fun j => (M.toModel.unbiased_mul (ℓ j) (ℓ j) (hsum j)).congr (fun X => by rw [hlin, sq]) (hcov j)
  have hc : ∀ j, M.toModel.Unbiased (fun X => M.cHat w X j)
      (∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j)) :=
    fun j => Model.Unbiased.sum univ fun i _ =>
      (M.sigRhoHat_unbiased sig hw hσ i j (hden i j)).const_mul _
  refine (Model.Unbiased.const_mul (M.wall w * (1 - ∑ k, x k ^ 2))⁻¹ (Model.Unbiased.sum univ fun j _ =>
    ((hsq j).const_mul (M.wtot w j)).add ((hc j).const_mul (-M.wtot w j)))).congr
    (fun X => ?_) ?_
  · rw [tauHat, hdenom, div_eq_inv_mul]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  · -- The algebra: `Σⱼ xⱼ (E[dⱼ²] - cⱼ) = τ²(1 - Σ xₖ²)`.
    have key : ∑ j, x j * ((∑ k, ∑ l, ((if k = j then 1 else 0) - x k)
          * ((if l = j then 1 else 0) - x l) * M.K k l)
          - ∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j))
        = M.τ2 * (1 - ∑ k, x k ^ 2) := by
      have pull : ∀ (j : J) (g : J → J → ℝ),
          ∑ k, ∑ l, (if k = j then g k l else 0) = ∑ l, g j l := fun j g => by
        rw [sum_comm]; simp [sum_ite_eq']
      simp only [M.K_apply]
      simp only [mul_add, sum_add_distrib]
      simp only [sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
        mul_zero, sum_ite_eq', sum_ite_eq, mem_univ, ite_true, sum_add_distrib, mul_add, pull]
      simp only [← sum_mul, hx, mul_sum]
      have h3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * M.σ2 b c * M.ρ b c
          = ∑ b, ∑ c, x b * x c * M.σ2 b c * M.ρ b c := by
        calc _ = ∑ a, x a * ∑ b, ∑ c, x b * x c * M.σ2 b c * M.ρ b c := by
                simp only [mul_sum, mul_assoc]
          _ = _ := by rw [← sum_mul, hx, one_mul]
      ring_nf
      rw [h3, mul_sum]
      ring
    have hWj : ∀ j, M.wtot w j = M.wall w * x j := fun j => by
      simp only [hx_def]; field_simp
    rw [inv_mul_eq_iff_eq_mul₀ hden_pos.ne']
    calc _ = M.wall w * ∑ j, x j * ((∑ k, ∑ l, ((if k = j then 1 else 0) - x k)
          * ((if l = j then 1 else 0) - x l) * M.K k l)
          - ∑ i, ((if i = j then 1 else 0) - x i) * (M.σ2 i j * M.ρ i j)) := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [hWj]; ring
      _ = _ := by rw [key]; ring

/-- Eq. (39), last line: `K̂ᵢⱼ` is unbiased for `Kᵢⱼ`. -/
theorem KHat_unbiased (hJ : 2 ≤ Fintype.card J)
    (hden : ∀ i j, (M.overlap i j).Nonempty → 0 < M.den w i j) (i j : J) :
    M.toModel.Unbiased (fun X => M.KHat w X i j) (M.K i j) := by
  refine ((M.sigRhoHat_unbiased sig hw hσ i j (hden i j)).add
    ((M.tauHat_unbiased sig hw hσ hJ hden).const_mul (if i = j then 1 else 0))).congr
    (fun X => by simp only [KHat]; ring) ?_
  rw [M.K_apply]; ring

omit hσ hw [Fintype T] in
/-- `K̂ᵢⱼ` reads only observed cells. -/
theorem KHat_observed (i j : J) : M.Observed (fun X => M.KHat w X i j) := by
  intro X Y hXY
  have hmu : ∀ k, M.muHat w X k = M.muHat w Y k := fun k =>
    sum_congr rfl fun t ht => by rw [hXY k t ht]
  have hsig : ∀ k l, M.sigRhoHat w X k l = M.sigRhoHat w Y k l := fun k l => by
    simp only [sigRhoHat, hmu]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    rw [hXY k t (mem_inter.mp ht).1, hXY l t (mem_inter.mp ht).2]
  simp only [KHat, tauHat, cHat, hmu, hsig]

omit hσ [Fintype J] [DecidableEq J] [Fintype T] in
/-- Eq. (41) with unequal lengths: on the diagonal the estimator is Bühlmann–Straub
with the cohort's own length, `σ̂ⱼ²/wⱼ*`, `σ̂ⱼ² = Σ_{t∈Tⱼ} wⱼₜ(μⱼₜ - μ̂ⱼ)²/(|Tⱼ| - 1)`. -/
theorem sigRhoHat_self (X : J × T → ℝ) (j : J) :
    M.sigRhoHat w X j j
      = (∑ t ∈ M.obs j, w j t * (X (j, t) - M.muHat w X j) ^ 2 / ((#(M.obs j) : ℝ) - 1))
        / M.wtot w j := by
  have hW : 0 < M.wtot w j := sum_pos (fun s _ => hw j s) (M.obs_nonempty j)
  have hS : M.sqrtSum w j j = M.wtot w j := by
    simp only [sqrtSum, overlap, inter_self]
    exact sum_congr rfl fun t _ => Real.sqrt_mul_self (hw j t).le
  rw [sigRhoHat, den, hS, M.count_self w hw j, ← sum_div, div_div,
    show M.wtot w j + ((#(M.obs j) : ℝ) - 2) * M.wtot w j * M.wtot w j / M.wtot w j
      = ((#(M.obs j) : ℝ) - 1) * M.wtot w j by field_simp; ring]
  congr 1
  simp only [overlap, inter_self]
  refine sum_congr rfl fun t _ => ?_
  rw [Real.sqrt_mul_self (hw j t).le]; ring

end Unequal
end Credibility
