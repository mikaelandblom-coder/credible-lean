import Credibility.Data

/-!
# Cohort-dependent series lengths (extension, not in the thesis)

Cohort `j` is observed only in the periods `Tⱼ ⊆ T` (`obs j`). Correlations act
only on periods two cohorts share, `Tᵢⱼ = Tᵢ ∩ Tⱼ` (`overlap i j`). The model
itself is `Model` (eqs. (15)–(16)); only the weights `aⱼₜ`, hence `σ²ᵢⱼ` and
`K`, change. See `notes/unequal-lengths.md`.

The thesis model is the case `Tⱼ = T` (`Model.toUnequal`): its `K`, positive
definiteness and credibility factor are corollaries of the results here.
Estimation and balance are in `UnequalEstimation.lean`.
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


/-! ### Diagonal `K`: equal covariances (Finding 5) and Bühlmann–Straub -/

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- `σ²ⱼⱼ = Σ_{t∈Tⱼ} (aⱼₜσⱼₜ)² ≥ 0`. -/
lemma σ2_self_nonneg (j : J) : 0 ≤ M.σ2 j j :=
  sum_nonneg fun t _ => by
    rw [show M.a j t * M.a j t * M.σ j t * M.σ j t = (M.a j t * M.σ j t) ^ 2 by ring]
    exact sq_nonneg _

omit [Fintype J] [Fintype T] in
/-- If distinct cohorts never covary, `K = diag(τ² + σ²ⱼⱼ)`. -/
theorem K_eq_diagonal (h0 : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = 0) :
    M.K = diagonal fun j => M.τ2 + M.σ2 j j := by
  ext i j
  rw [M.K_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp [M.ρ_self, add_comm]
  · simp [h0 i j h, h]

omit [Fintype T] in
/-- For diagonal `K`, `K⁻¹u = (τ² + σ²ⱼⱼ)⁻¹`. -/
theorem Kinv_one_of_diag (h0 : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = 0) :
    M.K⁻¹ *ᵥ 1 = fun j => (M.τ2 + M.σ2 j j)⁻¹ := by
  have hd : ∀ j, M.τ2 + M.σ2 j j ≠ 0 := fun j =>
    (add_pos_of_pos_of_nonneg M.τ2_pos (M.σ2_self_nonneg j)).ne'
  have hinv : (diagonal fun j => M.τ2 + M.σ2 j j)⁻¹ = diagonal fun j => (M.τ2 + M.σ2 j j)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hd _), diagonal_one]
  rw [M.K_eq_diagonal h0, hinv]
  ext j
  simp [mulVec_diagonal]

omit [Fintype T] in
/-- For diagonal `K`, `bⱼ = (τ² + σ²ⱼⱼ)⁻¹ / Σᵢ (τ² + σ²ᵢᵢ)⁻¹`. -/
theorem b_of_diag (h0 : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = 0) (j : J) :
    M.b j = (M.τ2 + M.σ2 j j)⁻¹ / ∑ i, (M.τ2 + M.σ2 i i)⁻¹ := by
  rw [b, glsWeight, invTotal, M.Kinv_one_of_diag h0, one_dotProduct]

omit [Fintype T] in
/-- For diagonal `K` and `J ≥ 2`, `zⱼ = τ²/(τ² + σ²ⱼⱼ)`. -/
theorem bestZ_of_diag (h0 : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = 0)
    (hJ : 1 < Fintype.card J) (j : J) :
    (M.moments j).bestZ = M.τ2 / (M.τ2 + M.σ2 j j) := by
  have hd : ∀ j, 0 < M.τ2 + M.σ2 j j := fun j =>
    add_pos_of_pos_of_nonneg M.τ2_pos (M.σ2_self_nonneg j)
  have hpd : M.K.PosDef := by rw [M.K_eq_diagonal h0, posDef_diagonal_iff]; exact hd
  set V := ∑ i, (M.τ2 + M.σ2 i i)⁻¹
  have hs2 : M.s2 = V⁻¹ := by rw [s2, invTotal, M.Kinv_one_of_diag h0, one_dotProduct]
  -- `J ≥ 2`: `V > (τ² + σ²ⱼⱼ)⁻¹`, so there is no `0/0`.
  have hV : (M.τ2 + M.σ2 j j)⁻¹ < V := by
    obtain ⟨i, hij⟩ := Fintype.exists_ne_of_one_lt_card hJ j
    change _ < ∑ i, _
    rw [← add_sum_erase _ _ (mem_univ j)]
    exact lt_add_of_pos_right _
      (sum_pos (fun k _ => inv_pos.mpr (hd k)) ⟨i, mem_erase.mpr ⟨hij, mem_univ i⟩⟩)
  rw [M.bestZ_eq hpd, M.b_of_diag h0, hs2, show ∑ x, (M.τ2 + M.σ2 x x)⁻¹ = V from rfl]
  have hdj := (hd j).ne'
  have hV0 : 0 < V := (inv_pos.mpr (hd j)).trans hV
  have hne : V - (M.τ2 + M.σ2 j j)⁻¹ ≠ 0 := (sub_pos.mpr hV).ne'
  have hne' : M.τ2 + M.σ2 j j - V⁻¹ ≠ 0 := by
    rw [show M.τ2 + M.σ2 j j - V⁻¹ = (M.τ2 + M.σ2 j j) * (V - (M.τ2 + M.σ2 j j)⁻¹) / V by
      field_simp]
    exact div_ne_zero (mul_ne_zero hdj hne) hV0.ne'
  rw [div_eq_div_iff hne' hdj]
  field_simp

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Finding 5 with unequal lengths: if all distinct pairs have the same covariance
`σ²ᵢⱼρᵢⱼ = c` and some two cohorts share no period, then `c = 0`. -/
theorem equalCov_eq_zero (c : ℝ) (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) {i k : J}
    (hik : i ≠ k) (hdisj : Disjoint (M.obs i) (M.obs k)) : c = 0 := by
  rw [← hc i k hik, M.σ2_eq_zero_of_disjoint hdisj, zero_mul]

omit [Fintype T] in
/-- …so the equal-covariance weights are `bⱼ ∝ (τ² + σ²ⱼⱼ - c)⁻¹` with `c = 0`. -/
theorem b_of_equalCov (c : ℝ) (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) {i k : J}
    (hik : i ≠ k) (hdisj : Disjoint (M.obs i) (M.obs k)) (j : J) :
    M.b j = (M.τ2 + M.σ2 j j - c)⁻¹ / ∑ i, (M.τ2 + M.σ2 i i - c)⁻¹ := by
  obtain rfl := M.equalCov_eq_zero c hc hik hdisj
  simp only [sub_zero]
  exact M.b_of_diag hc j

omit [Fintype T] in
/-- …and `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, eq. (32) with `σ₁σ₂ρ` replaced by `c = 0`. The
disjoint pair already gives `J ≥ 2`. -/
theorem bestZ_of_equalCov (c : ℝ) (hc : ∀ i j, i ≠ j → M.σ2 i j * M.ρ i j = c) {i k : J}
    (hik : i ≠ k) (hdisj : Disjoint (M.obs i) (M.obs k)) (j : J) :
    (M.moments j).bestZ = M.τ2 / (M.τ2 + M.σ2 j j - c) := by
  obtain rfl := M.equalCov_eq_zero c hc hik hdisj
  rw [sub_zero]
  exact M.bestZ_of_diag hc (Fintype.one_lt_card_iff.mpr ⟨i, k, hik⟩) j

/-! ### A partial correlation table: `ρᵢⱼ` only on overlapping pairs

Correlations act only on shared periods, so `ρᵢⱼ` should not be needed for
pairs with `Tᵢ ∩ Tⱼ = ∅`. `AgreeOnOverlaps` says two models differ at most in
those values; then `K`, `b`, `s²` and `z` agree. `PartialCorr` is the model with
`ρ` given only on overlapping pairs; `extend` fills the rest arbitrarily. -/

/-- `M` and `M'` differ at most in `ρᵢⱼ` for pairs with no shared period. -/
structure AgreeOnOverlaps (M M' : Unequal J T) : Prop where
  τ2_eq : M.τ2 = M'.τ2
  σ_eq : M.σ = M'.σ
  obs_eq : M.obs = M'.obs
  ρ_eq : ∀ i j, (M.overlap i j).Nonempty → M.ρ i j = M'.ρ i j

variable {M} {M' : Unequal J T}

omit [Fintype J] [DecidableEq J] [Fintype T] in
theorem AgreeOnOverlaps.σ2_eq (h : M.AgreeOnOverlaps M') : M.σ2 = M'.σ2 := by
  funext i j
  simp only [σ2, overlap, a, h.σ_eq, h.obs_eq]

omit [Fintype T] in
/-- `K` does not see `ρᵢⱼ` on disjoint pairs: there `σ²ᵢⱼ = 0`. -/
theorem AgreeOnOverlaps.K_eq (h : M.AgreeOnOverlaps M') : M.K = M'.K := by
  ext i j
  rw [M.K_apply, M'.K_apply, h.τ2_eq, ← h.σ2_eq]
  rcases (M.overlap i j).eq_empty_or_nonempty with h0 | h0
  · simp [σ2, h0]
  · rw [h.ρ_eq i j h0]

omit [Fintype T] in
theorem AgreeOnOverlaps.b_eq (h : M.AgreeOnOverlaps M') : M.b = M'.b := by
  simp only [b, h.K_eq]

omit [Fintype T] in
theorem AgreeOnOverlaps.s2_eq (h : M.AgreeOnOverlaps M') : M.s2 = M'.s2 := by
  simp only [s2, h.K_eq]

omit [Fintype T] in
/-- All moments of the blend, hence `zⱼ`, agree. -/
theorem AgreeOnOverlaps.moments_eq (h : M.AgreeOnOverlaps M') : M.moments = M'.moments := by
  funext j
  simp only [moments, h.τ2_eq, h.σ2_eq, h.K_eq, h.b_eq, h.s2_eq]

omit [Fintype T] in
theorem AgreeOnOverlaps.bestZ_eq (h : M.AgreeOnOverlaps M') (j : J) :
    (M.moments j).bestZ = (M'.moments j).bestZ := by
  rw [h.moments_eq]

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- The block hypothesis of `K_posDef` only reads `ρᵢⱼ` with `t ∈ Tᵢ ∩ Tⱼ`. -/
theorem AgreeOnOverlaps.blocks_iff (h : M.AgreeOnOverlaps M') (t : T) :
    ((Matrix.of M.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      (Subtype.val : {j // t ∈ M.obs j} → J)).PosSemidef ↔
    ((Matrix.of M'.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      Subtype.val).PosSemidef := by
  have : (Matrix.of M.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      (Subtype.val : {j // t ∈ M.obs j} → J)
      = (Matrix.of M'.ρ).submatrix (Subtype.val : {j // t ∈ M.obs j} → J)
      (Subtype.val : {j // t ∈ M.obs j} → J) := by
    ext i j
    exact h.ρ_eq i j ⟨t, mem_inter.mpr ⟨i.2, j.2⟩⟩
  rw [this]

end Unequal

/-- The unequal-lengths model with a *partial* correlation table: `ρᵢⱼ` is
given only for pairs that share a period, `Tᵢ ∩ Tⱼ ≠ ∅`. -/
structure PartialCorr (J T : Type*) [DecidableEq T] where
  τ2 : ℝ
  σ : J → T → ℝ
  obs : J → Finset T
  /-- `ρᵢⱼ`, defined only when `Tᵢ ∩ Tⱼ ≠ ∅`. -/
  ρ : (i j : J) → (obs i ∩ obs j).Nonempty → ℝ
  τ2_pos : 0 < τ2
  σ_pos : ∀ j t, 0 < σ j t
  obs_nonempty : ∀ j, (obs j).Nonempty
  ρ_self : ∀ j h, ρ j j h = 1
  ρ_symm : ∀ i j h h', ρ i j h = ρ j i h'

namespace PartialCorr

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (P : PartialCorr J T)

/-- Complete the table with any symmetric values `fᵢⱼ` on disjoint pairs. -/
noncomputable def extend (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) : Unequal J T where
  τ2 := P.τ2
  σ := P.σ
  ρ i j := if h : (P.obs i ∩ P.obs j).Nonempty then P.ρ i j h else f i j
  τ2_pos := P.τ2_pos
  σ_pos := P.σ_pos
  ρ_self j := by
    have h : (P.obs j ∩ P.obs j).Nonempty := by rw [inter_self]; exact P.obs_nonempty j
    simp only [h, ↓reduceDIte, P.ρ_self]
  ρ_symm i j := by
    by_cases h : (P.obs i ∩ P.obs j).Nonempty
    · have h' : (P.obs j ∩ P.obs i).Nonempty := by rwa [inter_comm]
      simp only [h, h', ↓reduceDIte, P.ρ_symm i j h h']
    · have h' : ¬(P.obs j ∩ P.obs i).Nonempty := by rwa [inter_comm]
      simp only [h, h', ↓reduceDIte, hf i j]
  obs := P.obs
  obs_nonempty := P.obs_nonempty

/-- The canonical completion, with `ρᵢⱼ = 0` on disjoint pairs. -/
noncomputable def toUnequal : Unequal J T := P.extend (fun _ _ => 0) fun _ _ => rfl

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- Any two completions differ only on disjoint pairs. -/
theorem extend_agree (f g : J → J → ℝ) (hf : ∀ i j, f i j = f j i)
    (hg : ∀ i j, g i j = g j i) : (P.extend f hf).AgreeOnOverlaps (P.extend g hg) where
  τ2_eq := rfl
  σ_eq := rfl
  obs_eq := rfl
  ρ_eq i j h := by
    have h' : (P.obs i ∩ P.obs j).Nonempty := h
    change (if h : _ then _ else _) = (if h : _ then _ else _)
    simp only [h', ↓reduceDIte]

omit [Fintype T] in
/-- `K`, `b`, `s²` and `zⱼ` do not depend on how the table is completed. -/
theorem K_extend (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) :
    (P.extend f hf).K = P.toUnequal.K :=
  (P.extend_agree _ _ hf _).K_eq

omit [Fintype T] in
theorem b_extend (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) :
    (P.extend f hf).b = P.toUnequal.b :=
  (P.extend_agree _ _ hf _).b_eq

omit [Fintype T] in
theorem s2_extend (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) :
    (P.extend f hf).s2 = P.toUnequal.s2 :=
  (P.extend_agree _ _ hf _).s2_eq

omit [Fintype T] in
theorem bestZ_extend (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) (j : J) :
    ((P.extend f hf).moments j).bestZ = (P.toUnequal.moments j).bestZ :=
  (P.extend_agree _ _ hf _).bestZ_eq j

omit [Fintype J] [DecidableEq J] [Fintype T] in
/-- The block of the partial table at period `t`: cohorts in `Jₜ` pairwise share `t`. -/
lemma mem_inter_of_block {t : T} (i j : {j : J // t ∈ P.obs j}) :
    (P.obs i.1 ∩ P.obs j.1).Nonempty :=
  ⟨t, mem_inter.mpr ⟨i.2, j.2⟩⟩

/-- `K_posDef` with the block hypothesis stated on the partial table alone:
if every block `(ρᵢⱼ)_{i,j∈Jₜ}` is positive semidefinite, every completion has
`K ≻ 0` (and they all have the same `K`). -/
theorem K_posDef
    (hρ : ∀ t, (Matrix.of fun i j : {j : J // t ∈ P.obs j} =>
      P.ρ i j (P.mem_inter_of_block i j)).PosSemidef)
    (f : J → J → ℝ) (hf : ∀ i j, f i j = f j i) :
    (P.extend f hf).K.PosDef := by
  refine Unequal.K_posDef _ fun t => ?_
  have : ((Matrix.of (P.extend f hf).ρ).submatrix
      (Subtype.val : {j // t ∈ P.obs j} → J) (Subtype.val : {j // t ∈ P.obs j} → J))
      = Matrix.of fun i j : {j : J // t ∈ P.obs j} => P.ρ i j (P.mem_inter_of_block i j) := by
    ext i j
    change (if h : _ then _ else _) = _
    simp only [P.mem_inter_of_block i j, ↓reduceDIte, of_apply]
  exact this ▸ hρ t

end PartialCorr

variable {J T : Type*} [DecidableEq T] in
/-- Every full model is a completion of its own partial table. -/
theorem Unequal.eq_extend (M : Unequal J T) :
    M = (PartialCorr.mk M.τ2 M.σ M.obs (fun i j _ => M.ρ i j) M.τ2_pos M.σ_pos
      M.obs_nonempty (fun j _ => M.ρ_self j) (fun i j _ _ => M.ρ_symm i j)).extend M.ρ
      M.ρ_symm := by
  obtain ⟨⟨τ2, σ, ρ, _, _, _, _⟩, obs, _⟩ := M
  simp only [PartialCorr.extend, Unequal.mk.injEq, Model.mk.injEq, true_and, and_true]
  funext i j
  split_ifs <;> rfl

end Credibility
