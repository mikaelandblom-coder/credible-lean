import Credibility.Estimation
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

Bridge 3: the §2.8 estimators see the same part. With observation covariance
`σᵢₜσⱼₛρᵢⱼδₜₛ + τ²(11ᵀ)^φᵢⱼ`, `τ̂²` has expectation `(1-φ)τ²` and `K̂` estimates
`K_φ - φτ²·11ᵀ` (`tauHat_unbiasedφ`, `KHat_unbiasedφ`), for every `φ`: no
inverse is involved, so `φ = 1` needs no separate case. The shared level acts
like the unknown mean `μ`, which the estimators are built to ignore.
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

/-! ### Bridge 3: the §2.8 estimators with a shared level -/

/-- `cov(μᵢₜ, μⱼₛ)` when the levels share `φτ²`: eq. (16) with the level
covariance `τ²(11ᵀ)^φ` in place of `τ²δᵢⱼ`. -/
noncomputable def obsCovφ (φ : ℝ) (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0) + levelCov M.τ2 φ i j

/-- Expectation of the quadratic form `quad Q` when the levels share `φτ²`
(as `Model.E`, with `obsCovφ` in place of `obsCov`). -/
noncomputable def Eφ (φ μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (M.obsCovφ φ p.1 q.1 p.2 q.2 + μ ^ 2)

/-- `f` is unbiased for `θ` when the levels share `φτ²`: a quadratic form in the
data with expectation `θ` for every mean `μ`. -/
def Unbiasedφ (φ : ℝ) (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ μ, M.Eφ φ μ Q = θ

/-- The part of an expectation coming from the sampling noise. -/
noncomputable def errPart (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (M.σ p.1 p.2 * M.σ q.1 q.2 * M.ρ p.1 q.1 * if p.2 = q.2 then 1 else 0)

/-- Splitting an expectation: noise, level variance on same-cohort pairs, and
the mean on all pairs. -/
lemma E_split (μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.E μ Q = M.errPart Q
      + M.τ2 * ∑ p, ∑ q, Q p q * (if p.1 = q.1 then 1 else 0) + μ ^ 2 * ∑ p, ∑ q, Q p q := by
  simp only [E, mom2, obsCov, errPart, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- …and with a shared level: the level adds `(1-φ)τ²` on same-cohort pairs
and `φτ²` on all pairs, like the mean. -/
lemma Eφ_split (φ μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.Eφ φ μ Q = M.errPart Q
      + (1 - φ) * M.τ2 * ∑ p, ∑ q, Q p q * (if p.1 = q.1 then 1 else 0)
      + (φ * M.τ2 + μ ^ 2) * ∑ p, ∑ q, Q p q := by
  simp only [Eφ, obsCovφ, errPart, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [levelCov_apply]
  split_ifs <;> ring

/-- An estimator unbiased in the thesis model is unbiased with a shared level,
for the value obtained by affine extrapolation in `φ`: if `f` is unbiased for
`θ` in `M` and for `θ'` in `M_ψ` (`ψ ≠ 0`), then under `K_φ` it is unbiased for
`θ + (φ/ψ)(θ' - θ)`, for every `φ`. -/
theorem unbiasedφ_of {f : (J × T → ℝ) → ℝ} {θ θ' ψ : ℝ} (hf : M.Unbiased f θ) (h1 : ψ < 1)
    (hψ : ψ ≠ 0) (hf' : (M.withLevel ψ h1).Unbiased f θ') (φ : ℝ) :
    M.Unbiasedφ φ f (θ + φ / ψ * (θ' - θ)) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hf'
  refine ⟨Q, hQ, fun μ => ?_⟩
  have h0 := hE 0
  have h1' := hE 1
  -- In `M_ψ` the expectation of `f` is `θ'`, whatever matrix represents it.
  have hW : (M.withLevel ψ h1).E 0 Q = θ' :=
    ((M.withLevel ψ h1).E_congr 0 fun X => (hQ X).trans (hQ' X).symm).trans (hE' 0)
  rw [E_split] at h0 h1' hW
  rw [Eφ_split]
  have hA : (M.withLevel ψ h1).errPart Q = M.errPart Q := rfl
  have hτ : (M.withLevel ψ h1).τ2 = (1 - ψ) * M.τ2 := rfl
  rw [hA, hτ] at hW
  set A := M.errPart Q
  set D := ∑ p, ∑ q, Q p q * (if p.1 = q.1 then (1 : ℝ) else 0)
  set S := ∑ p, ∑ q, Q p q
  norm_num at h0 h1' hW
  -- The thesis estimator does not see the mean: `S = 0`.
  have hS : S = 0 := by linarith
  have key : M.τ2 * D = (θ - θ') / ψ := by
    field_simp
    linear_combination h0 - hW
  rw [hS, show φ / ψ * (θ' - θ) = -φ * ((θ - θ') / ψ) by ring, ← key]
  linear_combination h0

variable {w : J → T → ℝ} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t)
  (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

/-- With a shared level, `σ²ᵢⱼρᵢⱼ^` is still unbiased for `σ²ᵢⱼρᵢⱼ`: it uses
only deviations within a cohort, where the level cancels. -/
theorem sigRhoHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (φ : ℝ) (i j : J) :
    M.Unbiasedφ φ (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have h := M.unbiasedφ_of (M.sigRhoHat_unbiased sig hw hσ hT i j)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).sigRhoHat_unbiased sig hw hσ hT i j) φ
  have hσ2 : (M.withLevel (1 / 2) (by norm_num)).σ2 = M.σ2 := rfl
  have hρ : (M.withLevel (1 / 2) (by norm_num)).ρ = M.ρ := rfl
  rw [hσ2, hρ] at h
  simpa using h

/-- Bridge 3: with a shared level, `τ̂²` (eq. (39)) is unbiased for the non-shared
part `(1-φ)τ²`, for every `φ`. At `φ = 1` its expectation is `0`: a common
level is invisible to the data, like the mean `μ`. -/
theorem tauHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ) :
    M.Unbiasedφ φ (tauHat w) ((1 - φ) * M.τ2) := by
  have h := M.unbiasedφ_of (M.tauHat_unbiased sig hw hσ hT hJ)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).tauHat_unbiased sig hw hσ hT hJ) φ
  have hτ : (M.withLevel (1 / 2) (by norm_num)).τ2 = (1 - 1 / 2) * M.τ2 := rfl
  rw [hτ] at h
  convert h using 1
  ring

/-- With a shared level, `K̂ᵢⱼ` is unbiased for `(K_φ - φτ²·11ᵀ)ᵢⱼ`, the thesis
`K` with `τ²` replaced by `(1-φ)τ²`: by Bridge 2, all that credibility needs. -/
theorem KHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ)
    (i j : J) : M.Unbiasedφ φ (fun X => KHat w X i j) (M.Kφ φ i j - φ * M.τ2) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedφ_of (M.KHat_unbiased sig hw hσ hT hJ i j)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).KHat_unbiased sig hw hσ hT hJ i j) φ
  have hτ : (M.withLevel (1 / 2) (by norm_num)).τ2 = (1 - 1 / 2) * M.τ2 := rfl
  have hσ2 : (M.withLevel (1 / 2) (by norm_num)).σ2 = M.σ2 := rfl
  have hρ : (M.withLevel (1 / 2) (by norm_num)).ρ = M.ρ := rfl
  rw [K_apply, K_apply, hτ, hσ2, hρ] at h
  convert h using 1
  rw [Kφ, Matrix.add_apply, levelCov_apply]
  by_cases hij : i = j <;> simp [hij, errCov]; ring

end Model
end Credibility
