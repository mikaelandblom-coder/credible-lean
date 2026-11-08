import Credibility.Model
import Credibility.OffDiagonal

/-!
# Bridge to hierarchical credibility: a shared group level

Not in the thesis; first step towards two-level credibility (FINDINGS item 6,
`notes/merging-cohorts.md`). In the thesis the cohort levels `μⱼ` are
uncorrelated with variance `τ²`. Here they share a fraction `φ` of that
variance: `cov(μᵢ, μⱼ) = τ²` if `i = j` and `φτ²` otherwise, i.e. the level
covariance is `τ²·(11ᵀ)^φ` with `(·)^φ` the damping of `OffDiagonal.lean`.
The cohort estimates then have covariance `K_φ = τ²·(11ᵀ)^φ + Σ`, where
`Σᵢⱼ = σ²ᵢⱼρᵢⱼ` is the error covariance.

* `φ = 0` is the thesis: `K_0 = K` (`Kφ_zero`);
* `φ ∈ [0,1)` keeps `K_φ` positive definite (`Kφ_posDef`);
* `φ = 1` (one common level) gives `Σ + τ²·11ᵀ`: the error covariance plus
  a rank-one term along `1`, the structure behind Finding 5 (`Kφ_one`).

Bridge 2: `K_φ` is the thesis `K` with `τ²` replaced by `(1-φ)τ²` (the model
`M.withLevel φ`), plus `φτ²·11ᵀ` (`Kφ_eq`). A rank-one term along `1` does not
move the GLS weights and adds its size to `s²` (`glsWeight_add_rankOne`,
`invTotal_inv_add_rankOne`). The shared level then adds `φτ²` to all six
moments of the blend, which changes neither its error variance nor `bestZ`
(`BlendMoments.shift`): credibility only sees the non-shared part `(1-φ)τ²`.
-/

open Matrix

namespace Credibility

/-! ### A rank-one term along `1` (Core level) -/

section RankOne

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- If `K` and `K + c·11ᵀ` are positive definite, then
`(K + c·11ᵀ)⁻¹1 = K⁻¹1 / (1 + c·1ᵀK⁻¹1)`, with `1 + c·1ᵀK⁻¹1 > 0`:
`(K + c·11ᵀ) K⁻¹1 = (1 + c·1ᵀK⁻¹1)·1`. -/
theorem Kinv_one_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    0 < 1 + c * invTotal K ∧
      (K + c • vecMulVec 1 1)⁻¹ *ᵥ 1 = (1 + c * invTotal K)⁻¹ • (K⁻¹ *ᵥ 1) := by
  set w := K⁻¹ *ᵥ 1
  set S := invTotal K
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).mp hK'.isUnit
  have hKw : (K + c • vecMulVec 1 1) *ᵥ w = (1 + c * S) • (1 : J → ℝ) := by
    rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, mulVec_mulVec, mul_nonsing_inv K hdet,
      one_mulVec]
    ext i; simp [S, invTotal, w]
  have hw : w = (1 + c * S) • ((K + c • vecMulVec 1 1)⁻¹ *ᵥ 1) := by
    rw [← mulVec_smul, ← hKw, mulVec_mulVec, nonsing_inv_mul _ hdet', one_mulVec]
  -- `wᵀ(K + c·11ᵀ)w = (1 + cS)·S > 0` with `S > 0`.
  have hpos : 0 < 1 + c * S := by
    rcases isEmpty_or_nonempty J with hJ | hJ
    · simp [S, invTotal]
    have hS : 0 < S := invTotal_pos hK
    have hw0 : w ≠ 0 := by
      intro h0
      have : S = 0 := by
        simp only [S, invTotal]; rw [show K⁻¹ *ᵥ 1 = w from rfl, h0, dotProduct_zero]
      linarith
    have := hK'.dotProduct_mulVec_pos hw0
    rw [star_trivial, hKw, dotProduct_smul, dotProduct_one, smul_eq_mul] at this
    have hS' : ∑ i, w i = S := by simp [S, invTotal, w, one_dotProduct]
    rw [hS'] at this
    exact pos_of_mul_pos_left this hS.le
  refine ⟨hpos, ?_⟩
  rw [eq_inv_smul_iff₀ hpos.ne']; exact hw.symm

/-- A rank-one term along `1` does not change the GLS weights:
`b(K + c·11ᵀ) = b(K)`, since `(K + c·11ᵀ)⁻¹1 ∝ K⁻¹1`. -/
theorem glsWeight_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    glsWeight (K + c • vecMulVec 1 1) = glsWeight K := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  ext j
  rw [glsWeight, glsWeight, invTotal, hinv, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_div_mul_left _ _ (inv_ne_zero hpos.ne'), invTotal]

/-- …and it adds `c` to the portfolio variance: `s²(K + c·11ᵀ) = s²(K) + c`. -/
theorem invTotal_inv_add_rankOne [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    (invTotal (K + c • vecMulVec 1 1))⁻¹ = (invTotal K)⁻¹ + c := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  have hS := (invTotal_pos hK).ne'
  rw [invTotal, hinv, dotProduct_smul, smul_eq_mul, ← invTotal]
  field_simp

end RankOne

/-! ### Shifting all moments of the blend by a constant -/

namespace BlendMoments

/-- Add `c` to all six second moments of the blend: what a common component of
variance `c` in the cohort estimates, the portfolio estimate and the target does. -/
def shift (m : BlendMoments) (c : ℝ) : BlendMoments where
  varCohort := m.varCohort + c
  varPortfolio := m.varPortfolio + c
  varTarget := m.varTarget + c
  covEst := m.covEst + c
  covCohortTarget := m.covCohortTarget + c
  covPortfolioTarget := m.covPortfolioTarget + c

/-- A common component cancels in the error of the blend:
`z + (1 - z) - 1 = 0`, so the error variance is unchanged. -/
theorem errVar_shift (m : BlendMoments) (c z : ℝ) : (m.shift c).errVar z = m.errVar z := by
  simp only [errVar, shift]; ring

/-- …and so is `Var(μ̂ⱼ - μ̂)`. -/
theorem gap_shift (m : BlendMoments) (c : ℝ) : (m.shift c).gap = m.gap := by
  simp only [gap, shift]; ring

/-- …and so is the best credibility factor. -/
theorem bestZ_shift (m : BlendMoments) (c : ℝ) : (m.shift c).bestZ = m.bestZ := by
  rw [bestZ, gap_shift, bestZ]; simp only [shift]; ring_nf

end BlendMoments

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- Covariance of the cohort levels when they share a fraction `φ` of the
level variance: `τ²` on the diagonal, `φτ²` off it. -/
noncomputable def levelCov (τ2 φ : ℝ) : Matrix J J ℝ :=
  τ2 • shrinkOffDiag φ (of fun _ _ => (1 : ℝ))

/-- The error covariance `Σᵢⱼ = σ²ᵢⱼρᵢⱼ` of the cohort estimates. -/
noncomputable def errCov : Matrix J J ℝ := of fun i j => M.σ2 i j * M.ρ i j

/-- `K_φ = τ²·(11ᵀ)^φ + Σ`, the covariance of the cohort estimates when the
levels share a fraction `φ` of their variance. -/
noncomputable def Kφ (φ : ℝ) : Matrix J J ℝ := levelCov M.τ2 φ + M.errCov

omit [Fintype J] [Fintype T] [DecidableEq T] in
lemma levelCov_apply (τ2 φ : ℝ) (i j : J) :
    levelCov τ2 φ i j = if i = j then τ2 else φ * τ2 := by
  by_cases h : i = j <;> simp [levelCov, shrinkOffDiag, h, mul_comm]

omit [Fintype J] in
/-- `φ = 0` is the thesis model: `K_0 = K`. -/
theorem Kφ_zero [Nonempty T] : M.Kφ 0 = M.K := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h, add_comm]

omit [Fintype J] [DecidableEq T] in
/-- `φ = 1` (one common level): `K_1 = Σ + τ²·11ᵀ`, the error covariance plus
a rank-one term along `1`. -/
theorem Kφ_one : M.Kφ 1 = M.errCov + M.τ2 • vecMulVec 1 1 := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, add_comm]
  by_cases h : i = j <;> simp [h]

omit [Fintype J] in
/-- The error covariance is `K - τ²·I`, so `K_1 = K - τ²·I + τ²·11ᵀ`. -/
theorem errCov_eq [Nonempty T] : M.errCov = M.K - M.τ2 • (1 : Matrix J J ℝ) := by
  ext i j
  rw [Matrix.sub_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h]

/-- The error covariance is positive semidefinite when `ρ` is: for every
`ε > 0`, `Σ + εI` is the `K` of the model with `τ² = ε`, positive definite by
`K_posDef`. -/
theorem errCov_posSemidef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) :
    M.errCov.PosSemidef := by
  -- The model with `τ² = ε`.
  let Mε : (ε : ℝ) → 0 < ε → Model J T := fun ε hε => { M with τ2 := ε, τ2_pos := hε }
  have hK : ∀ ε (hε : 0 < ε), (Mε ε hε).K = M.errCov + ε • (1 : Matrix J J ℝ) := by
    intro ε hε
    ext i j
    rw [Matrix.add_apply, (Mε ε hε).K_apply]
    by_cases h : i = j <;> simp [Mε, errCov, h, σ2, a]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have hE : M.errCov = (Mε 1 one_pos).K - 1 := by rw [hK, one_smul, add_sub_cancel_right]
    rw [hE]
    exact ((Mε 1 one_pos).K_posDef hρ).isHermitian.sub isHermitian_one
  · -- `xᵀΣx + ε‖x‖² ≥ 0` for every `ε > 0`.
    have h : ∀ ε, 0 < ε → 0 ≤ star x ⬝ᵥ (M.errCov *ᵥ x) + ε * (star x ⬝ᵥ x) := by
      intro ε hε
      have := ((hK ε hε) ▸ (Mε ε hε).K_posDef hρ).posSemidef.dotProduct_mulVec_nonneg x
      simpa [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul] using this
    by_contra hneg
    rw [not_le] at hneg
    have hxx : 0 ≤ star x ⬝ᵥ x := by
      simp only [dotProduct, star_trivial]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    set q := star x ⬝ᵥ (M.errCov *ᵥ x)
    set n := star x ⬝ᵥ x
    have := h (-q / (2 * (n + 1))) (div_pos (by linarith) (by linarith))
    have hn1 : 0 < n + 1 := by linarith
    have : -q / (2 * (n + 1)) * n ≤ -q / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith

/-- For `φ ∈ [0,1)`, `K_φ` is positive definite: `τ²·(11ᵀ)^φ ≻ 0` by
`posDef_shrinkOffDiag` (`11ᵀ ⪰ 0` with unit diagonal), and `Σ ⪰ 0`. -/
theorem Kφ_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (M.Kφ φ).PosDef := by
  have h11 : (of fun _ _ => (1 : ℝ) : Matrix J J ℝ).PosSemidef := by
    simpa [vecMulVec] using posSemidef_vecMulVec_self_star (1 : J → ℝ)
  exact PosDef.add_posSemidef
    ((posDef_shrinkOffDiag h11 h0 h1 fun _ => one_pos).smul M.τ2_pos)
    (M.errCov_posSemidef hρ)

/-! ### Bridge 2: `K_φ` is a thesis `K` plus a rank-one term -/

/-- The thesis model with the non-shared level variance `(1-φ)τ²`. -/
def withLevel (φ : ℝ) (h1 : φ < 1) : Model J T :=
  { M with τ2 := (1 - φ) * M.τ2, τ2_pos := mul_pos (sub_pos.mpr h1) M.τ2_pos }

omit [Fintype J] [Fintype T] [DecidableEq T] in
/-- `τ²(11ᵀ)^φ = (1-φ)τ²·I + φτ²·11ᵀ`. -/
lemma levelCov_eq (τ2 φ : ℝ) :
    levelCov τ2 φ = ((1 - φ) * τ2) • (1 : Matrix J J ℝ) + (φ * τ2) • vecMulVec 1 1 := by
  ext i j
  rw [levelCov_apply]
  by_cases h : i = j <;> simp [h]; ring

omit [Fintype J] in
/-- `K_φ` is the thesis `K` with `τ²` replaced by `(1-φ)τ²`, plus `φτ²·11ᵀ`. -/
theorem Kφ_eq [Nonempty T] {φ : ℝ} (h1 : φ < 1) :
    M.Kφ φ = (M.withLevel φ h1).K + (φ * M.τ2) • vecMulVec 1 1 := by
  have he : M.errCov = (M.withLevel φ h1).errCov := rfl
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  rw [Kφ, levelCov_eq, he, errCov_eq, hτ]
  abel

/-- For `φ ∈ [0,1)`, the GLS weights of `K_φ` are the thesis weights with
`τ²` replaced by `(1-φ)τ²`. -/
theorem glsWeight_Kφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : glsWeight (M.Kφ φ) = (M.withLevel φ h1).b := by
  have hK' := M.Kφ_posDef hρ h0 h1
  rw [M.Kφ_eq h1] at hK' ⊢
  exact glsWeight_add_rankOne ((M.withLevel φ h1).K_posDef hρ) _ hK'

/-- …and the portfolio variance is that model's `s²` plus the shared `φτ²`. -/
theorem s2_Kφ [Nonempty T] [Nonempty J] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (invTotal (M.Kφ φ))⁻¹ = (M.withLevel φ h1).s2 + φ * M.τ2 := by
  have hK' := M.Kφ_posDef hρ h0 h1
  rw [M.Kφ_eq h1] at hK' ⊢
  exact invTotal_inv_add_rankOne ((M.withLevel φ h1).K_posDef hρ) _ hK'

/-! ### The blend with a shared level -/

/-- The moments entering the blend for cohort `j` when the levels share `φτ²`
(§2.4 with `cov(μᵢ, μⱼ) = φτ²`): the GLS weights `b` of `K_φ`, and
`cov(μ̂, μⱼ) = Σᵢ bᵢ cov(μᵢ, μⱼ)`. -/
noncomputable def momentsφ (φ : ℝ) (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := (invTotal (M.Kφ φ))⁻¹
  varTarget := M.τ2
  covEst := (M.Kφ φ *ᵥ glsWeight (M.Kφ φ)) j
  covCohortTarget := M.τ2
  covPortfolioTarget := (levelCov M.τ2 φ *ᵥ glsWeight (M.Kφ φ)) j

/-- The shared level adds `φτ²` to every moment of the thesis blend with
non-shared level variance `(1-φ)τ²`. -/
theorem momentsφ_eq [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    M.momentsφ φ j = ((M.withLevel φ h1).moments j).shift (φ * M.τ2) := by
  have : Nonempty J := ⟨j⟩
  set M' := M.withLevel φ h1
  have hb := M.glsWeight_Kφ hρ h0 h1
  have hs := M.s2_Kφ hρ h0 h1
  have hcov : (M.Kφ φ *ᵥ glsWeight (M.Kφ φ)) j = (invTotal (M.Kφ φ))⁻¹ := by
    rw [mulVec_glsWeight (M.Kφ_posDef hρ h0 h1)]
  have hcov' : (M'.K *ᵥ M'.b) j = M'.s2 := by
    rw [Model.b, mulVec_glsWeight (M'.K_posDef hρ)]; rfl
  -- `cov(μ̂, μⱼ) = φτ² + (1-φ)τ² bⱼ`, using `Σ b = 1`.
  have hlev : (levelCov M.τ2 φ *ᵥ glsWeight (M.Kφ φ)) j
      = φ * M.τ2 + (1 - φ) * M.τ2 * M'.b j := by
    rw [levelCov_eq, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hb]
    have hsum : 1 ⬝ᵥ M'.b = 1 := by rw [one_dotProduct, Model.b, sum_glsWeight (M'.K_posDef hρ)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    erw [hsum]; simp; ring
  have hτ : M'.τ2 = (1 - φ) * M.τ2 := rfl
  have hσ : M'.σ2 = M.σ2 := rfl
  simp only [momentsφ, Model.moments, BlendMoments.shift, hcov, hcov', hlev, hs, hτ, hσ,
    BlendMoments.mk.injEq]
  exact ⟨by ring, rfl, by ring, rfl, by ring, by ring⟩

/-- The error variance of the blend with a shared level is that of the thesis
model with `τ²` replaced by `(1-φ)τ²`, for every `z`. -/
theorem errVar_momentsφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) (z : ℝ) :
    (M.momentsφ φ j).errVar z = ((M.withLevel φ h1).moments j).errVar z := by
  rw [M.momentsφ_eq hρ h0 h1, BlendMoments.errVar_shift]

/-- …so the best credibility factor is too. -/
theorem bestZ_momentsφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    (M.momentsφ φ j).bestZ = ((M.withLevel φ h1).moments j).bestZ := by
  rw [M.momentsφ_eq hρ h0 h1, BlendMoments.bestZ_shift]

/-- Eq. (26) with a shared level: `zⱼ = (1 - bⱼ)(1-φ)τ² / ((1-φ)τ² + vⱼ - (s² - φτ²))`,
with `b` and `s²` the GLS weights and portfolio variance of `K_φ`. -/
theorem bestZ_φ_eq [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    (M.momentsφ φ j).bestZ = (1 - glsWeight (M.Kφ φ) j) * ((1 - φ) * M.τ2)
      / ((1 - φ) * M.τ2 + M.σ2 j j - ((invTotal (M.Kφ φ))⁻¹ - φ * M.τ2)) := by
  have : Nonempty J := ⟨j⟩
  rw [M.bestZ_momentsφ hρ h0 h1, Model.bestZ_eq _ ((M.withLevel φ h1).K_posDef hρ) j,
    M.glsWeight_Kφ hρ h0 h1, M.s2_Kφ hρ h0 h1, add_sub_cancel_right]
  rfl

end Model
end Credibility
