# Related work for G1/G2 (common correlation, damping θ)

Collected 2026-11-14 from abstracts and summaries (full texts not read yet). Links in the chat log
of that day; search the titles.

## 1. Our `b` is the global minimum-variance portfolio (GMV)
`b = K⁻¹1 / 1ᵀK⁻¹1` is the GMV portfolio with covariance `K`. Estimating it from a sample
covariance is a large literature, and its central lesson matches study findings S11–S13: **shrink for
the loss you care about.**
- Ledoit & Wolf (2017), *Nonlinear shrinkage of the covariance matrix for portfolio selection:
  Markowitz meets Goldilocks*, RFS 30(12). Shrinkage derived for the portfolio's out-of-sample
  variance, not a generic matrix loss; formulas must be redone per loss function.
- Bodnar, Parolya & Schmid (2018), *Estimation of the global minimum variance portfolio in high
  dimensions*, EJOR 266 (arXiv 1406.0437). Shrinks the *weights* `b` (towards a target such as
  equal weights) with an intensity optimal for out-of-sample variance; **distribution-free, only
  fourth moments assumed**; asymptotic in J, T → ∞.
- Frahm & Memmel (2010), *Dominating estimators for minimum-variance portfolios*, J. Econometrics:
  finite-sample shrinkage of GMV weights that dominates the plug-in (normal returns).
- Schäfer & Strimmer (2005), *A shrinkage approach to large-scale covariance matrix estimation*,
  SAGMB 4(1): the zero-target ("target D") intensity `Σ Var(ŝᵢⱼ)/Σ ŝᵢⱼ²` form. Used 2026-11-22 for
  G2: `Damping.bestTheta = Σs²/(Σs² + ΣV)` is the exact finite-sample version with given moments.
- Ledoit & Wolf (2004), *Honey, I shrunk the sample covariance matrix*, JPM 30(4): the
  **constant-correlation target** (average sample correlation × sample variances), from Elton &
  Gruber's constant-correlation model. This is our H1 model; linear shrinkage intensity there is
  Frobenius-optimal (our stand-in loss, which finding S12 shows is the wrong one for rates).

Difference to note: their target is *out-of-sample* variance (new data); our error compares the
rates with the levels of the *same* history, so the in-sample effect of finding S13 is ours.
G6 (forecasting next year) would move us to their setting.

## 2. Plug-in parameters in BLUP (small-area estimation)
Credibility is a BLUP; with estimated variances it is an EBLUP.
- Kackar & Harville (1984): MSE of the EBLUP = MSE of the BLUP + a term from estimating the
  variance parameters. Prasad & Rao (1990): second-order approximation (the `g₃` term, from
  the covariance of the variance estimates); Das, Jiang & Rao (2004), Ann. Stat. (arXiv
  math/0406455), general version. That is "the price of estimation" (fit − floor) in formulas.
- Fay–Herriot with correlated sampling errors (Statistics Canada LFS work, Verret & Walker 2025):
  estimated covariances are smoothed / restricted to a working structure before use.
- Feasible GLS: with few observations per covariance parameter it can be worse than OLS;
  restrict Σ to few parameters (our BS-vs-full result at ρ = 0, finding S6).

## 3. Credibility with common effects (our correlation model)
- Yeo & Valdez (2006), *Claim dependence with common effects in credibility models*, IME 38(3);
  Wen, Wu & Zhou (2009), IME 44(1) (thesis ref `wen2`): a common effect across risks.
- Ebrahimzadeh, Ibrahim, Jemain & Kilicman (2012), *Unbiased estimation of structural parameters
  in credibility models with dependence induced by common effects*, Bull. Malays. Math. Sci. Soc.
  35(4): unbiased estimators incl. Bühlmann–Straub weights. Compare with item 2 of the
  CommonCorrelation plan (unbiased `ρσ²`); likely the closest prior art.
- Yang & Wang (2024), Comm. Stat. 53(8): REML and linear-Bayes estimators of structural
  parameters in the Bühlmann model with correlated risks.
- Factors outside `[0, 1]` (searched 2026-11-16 for Finding 17): Pinquet (2020), as cited by
  Ahn, Jeong & Lu (arXiv 2109.07956), notes that credibility coefficients of dynamic (serially
  correlated) models need not be non-negative; nothing found on reparametrizing them. Small-area
  estimation (Fay–Herriot EBLUP) reports the weight on the direct estimate, which is our own-data
  weight `cⱼ = bⱼ + zⱼ(1 − bⱼ)` when the synthetic part is the GLS mean. Used: report `cⱼ` next to `z`.

- The blend against the BLUP (searched 2026-11-16 for Finding 18): Goldberger (1962), *Best
  linear unbiased prediction in the generalized linear regression model*, JASA 57: the predictor
  `K⁻¹ℓ` plus the GLS mean of the remainder, which with an unknown common mean is the homogeneous
  credibility estimator. Wen, Wu & Zhou (2009), *The credibility estimator with general dependence
  structure over risks*, and Zhang & Chen (2018), *Credibility estimators with dependence structure over risks and time
  under balanced loss function*, Statistica Neerlandica 72(2), 157–173 (equal dependence over
  risks and time; checked 2026-11-17):
  homogeneous and inhomogeneous estimators under dependence by orthogonal projection. Used: the
  BLUP as the benchmark for the thesis's blend (`Core.blupWeight_optimal`); new here is the exact
  price of the blend and the condition for it to be zero (Finding 18).

- Hierarchical credibility (cited in paper §11, 2026-11-16; details checked by web search
  2026-11-17, contents from abstracts only): Jewell (1975), *The use of collateral data in
  credibility theory: a hierarchical model*, IIASA Research Memorandum RM-75-24 (the Giornale
  dell'Istituto Italiano degli Attuari 38 version is not confirmed); Bühlmann–Straub as the
  limit of a diffuse hyperprior; Taylor (1979), *Credibility analysis
  of a general hierarchical model*, Scand. Actuar. J. 1979(1), 1–12 (reduces it to a sequence of
  standard credibility analyses); Bühlmann & Gisler (2005), *A Course in
  Credibility Theory*, ch. 6. Nested levels with independent noise; the group variance estimated
  from the spread of group means. Small-area analogue: two-fold nested error models (Stukel &
  Rao 1999, *On small-area estimation under two-fold nested error regression models*, JSPI 78,
  131–147). Used: the two-stage weights as the target shape (`glsWeight_blockDiag`).
  New here: correlated noise, and `φτ²` from within- and across-group pairs (Finding 13).

- Ignoring correlation (searched 2026-11-16 for Finding 19): Bloomfield & Watson (1975),
  *The inefficiency of least squares*, Biometrika 62: the Kantorovich bound on OLS against
  GLS, via Wielandt's inequality; Styan (1983) surveys it. Misspecified covariance in
  prediction: Henderson (1975), *Best linear unbiased estimation and prediction under a selection model*,
  Biometrics 31, 423–447, and Cantet (1997) for BLUP in animal breeding, Stein (1999),
  *Interpolation of spatial data: some theory for kriging*, Springer, §3.5 "Prediction with the
  wrong spectral density" and ch. 6, for kriging (asymptotic; not checked for a finite
  Kantorovich bound). Nothing found for credibility. Used: the Kantorovich factor
  `(a + A)²/(4aA)` for any working model (`Core.linMse_blupWeight_working_le`); new here is
  the credibility form `1/(1 − δ²)`, free of `τ²` and the noise variances.

## 4. Error of the plug-in fit (MSEP with estimated parameters)
- Kackar & Harville (1981, 1984): MSE(EBLUP) = MSE(BLUP) + E[(EBLUP − BLUP)²] for even,
  translation-invariant variance estimators, **under normality**. Without normality the cross term
  `2E[(BLUP − target)(EBLUP − BLUP)]` need not vanish; it can be negative, which explains why our
  fit beats the fixed-weight floor under heavy tails (damping-theta.md, finding S9).
- Kackar & Harville (1981), *Unbiasedness of two-stage estimation and prediction procedures for
  mixed linear models*, Comm. Stat. A 10: the plug-in predictor is unbiased when the variance
  estimator is even and translation invariant and the noise symmetric (from memory). Used
  (2026-11-21): `Core.Target.plugIn_unbiased_of_symmetric`, `blup_plugIn_unbiased_of_symmetric`
  (distribution layer, `Credibility/PlugInSymmetric.lean`).
- Kackar & Harville (1984), JASA 79: the MSE identity MSE(EBLUP) = MSE(BLUP) + E(EBLUP − BLUP)²
  under normality for translation-invariant estimators (from memory). Used (2026-11-22): the
  distribution-free identity with the cross term (`Core.Target.integral_sq_plugIn`) and the normal
  case (`plugIn_mse_of_normal`, `plugIn_mse_ge_of_normal`, `Credibility/PlugInNormal.lean`).
  Evenness is not needed for the MSE identity, only for unbiasedness.
- Prasad & Rao (1990), Das, Jiang & Rao (2004): MSEP ≈ g₁ + g₂ + g₃ with g₃ from the covariance of
  the variance-parameter estimates; second-order unbiased MSEP estimator g₁(θ̂) + g₂(θ̂) + 2g₃(θ̂).
  Used 2026-11-24 (`studies/price-formula.js`, S53–S55): g₃ as the first-order price of a fitted
  model against its oracle; reliable from about T = 10, overshooting with short histories.
- Mack (1993), *Distribution-free calculation of the standard error of chain ladder reserve
  estimates*, ASTIN 23(2): MSEP = process variance + estimation error, distribution-free, with an
  approximation for the estimation-error term. Gisler & Wüthrich (2008), credibility chain ladder:
  conditional MSEP of a credibility estimator (formula 4.10). Happ, Maier & Merz (2011),
  multivariate Bühlmann–Straub for correlated triangles: conditional MSEP estimator.
- Benchmarking in small-area estimation (forcing the estimates to add up to a direct total, our
  exposure balance): Pfeffermann & Barnard (1991), Wang, Fuller & Qu (2008, Survey Methodology 34):
  the best linear benchmarked predictor adds a share of the discrepancy to each estimate (a common
  shift for our loss weights); benchmarking costs efficiency. Used in `studies/vc-balance.js`.
  Their optimum ranges over *all* linear predictors; within the credibility class (`b` fixed,
  only `z` free) the best balanced blend is `Core.bestBalanced_optimal` (G7), much worse in our
  worlds (Finding 15), so the WFQ shift is the one to use. Bell, Datta & Ghosh (2013) extend
  WFQ to several benchmark constraints. Their "add a share of the discrepancy" optimum
  needs the base predictor's error uncorrelated with the discrepancy (true for a BLUP).
  Within "blend + `cⱼD`" this is `Core.bestCorrection_optimal` (G7b). The shift is optimal
  for independent cohorts, and under correlation only within about 2% (Finding 16).
- Jiang, Lahiri & Wan (2002), *A unified jackknife theory for empirical best prediction with
  M-estimation*, Ann. Stat. 30: jackknife MSEP of an EBLUP, no normality needed, deletes
  independent units (we delete years). Used in `studies/msep.js`.

## 5. If a distribution is allowed (owner's question, 2026-11-15; not yet decided)
- Stein (1981), *Estimation of the mean of a multivariate normal distribution*, Ann. Stat.: Stein's
  lemma gives SURE, an *exact* unbiased estimate of the MSE of any (weakly differentiable)
  data-dependent shrinkage under normal noise.
- Hudson (1978), *A natural identity for exponential families with applications in multiparameter
  estimation*, Ann. Stat.: the same for exponential families (e.g. Poisson, gamma).
- Xie, Kou & Brown (2012), *SURE estimates for a heteroscedastic hierarchical model*, JASA:
  shrinkage chosen by SURE with unequal variances (our unequal volumes); robust to a wrong prior.
- Jewell (1974): in exponential dispersion families with conjugate priors, linear credibility *is*
  the Bayes (best) predictor; then the plug-in MSEP behaves like Jiang–Lahiri–Wan's case.
- Robust credibility for heavy tails: Künsch (1992), Gisler & Reinhard (1993); Bühlmann & Gisler
  (2005), *A Course in Credibility Theory*.
- Cross-validation and unbiased risk estimates are asymptotically equivalent (Stone 1977); both
  are ways to choose a shrinkage, as are SURE and Mallows' Cp.

- Checked by web search 2026-11-17 (paper §12, §14): Fisher (1958), *On grouping for maximum
  homogeneity*, JASA 53, 789–798; Dannenburg, Kaas & Goovaerts (1996), *Practical actuarial
  credibility models*, IAE Amsterdam (ch. 6: the two-way cross classification model).

- Clustering credibility estimates (checked 2026-11-17, full text read; cited in paper §12, §14,
  Finding 6, `notes/roadmap.md` §5): van Rijn, Weber & Merz (2026), *Credibility Clustering for
  Experience Rating: An Automated Approach to Risk Group Allocation in Group Life Insurance*,
  arXiv:2611.07110. Multidimensional Bühlmann–Straub per economic sector, then unweighted
  Euclidean k-means (100 random starts) on the credibility estimates, then credibility again on
  the groups. They reject exposure-weighted k-means on raw rates (it "cancels" the
  observed-to-expected ratios). Their `ρ` is a shrinkage of the correlation between risk measures
  (frequency, severity), not between risks: noise is independent across sectors. No interval
  result, no dynamic programming, no winner's curse. Used: the problem (risk groups from
  experience). New here: pooled MSE is exactly exposure-weighted k-means on the raw rates, so
  optimal groups are intervals found exactly by DP (Finding 14); distance by gap noise with
  correlated cohorts (Finding 6, §12).

## 6. Covariance tapering (2026-11-17, for `OffDiagonal.lean`)
- Furrer, Genton & Nychka (2006), *Covariance tapering for interpolation of large spatial
  datasets*, J. Comput. Graph. Stat. 15(3), 502–523 (checked by web search): kriging (the
  BLUP) with the covariance multiplied entrywise by a compactly supported correlation function,
  to make it sparse; tapered matrix stays positive definite by the Schur product theorem.
  Kaufman, Schervish & Nychka (2008, JASA) extend it to likelihood estimation. Used: the idea
  that any correlation matrix is a valid taper; our damping `θ` is the taper
  `θ11ᵀ + (1-θ)I`, and `ρ^|tᵢ-tⱼ|` the exponential taper on ordered cohorts.
- Schur (1911): the Hadamard product of PSD matrices is PSD (Mathlib
  `Matrix.PosSemidef.hadamard`). Oppenheim (1930): `A ≻ 0`, `B ⪰ 0` with positive diagonal
  give `A ⊙ B ≻ 0` (proved here as `posDef_hadamard_of_diag_pos`, via `A - cI ⪰ 0`).
- Kac, Murdock & Szegő (1953), *On the eigenvalues of certain Hermitian forms*, J. Rational
  Mech. Anal. 2: the matrix `ρ^|i-j|` (AR(1) correlation). Its positivity is not needed in KMS
  form: a Hadamard product of two-block matrices, one per gap, gives it for any ℕ positions.
- Choosing the taper width: Bickel & Levina (2008), *Regularized estimation of large covariance
  matrices*, Ann. Stat. 36(1), choose the band by random splits of the sample; Cai, Zhang & Zhou
  (2010), Ann. Stat. 38(4), give the optimal tapering rate (from memory, not checked here). Not
  used: splitting is cross-validation, which S14 found too noisy and too cautious for us; the app's
  taper `ρ̂` uses the plug-in loss of S3 per distance instead (study S33–S35: no gain over damping
  for the blend).
- Covariance shrinkage towards a target (Ledoit & Wolf, §1) is additive; tapering is
  multiplicative. Both keep `K̂ ⪰ 0`; damping is both at once (`shrinkOffDiag_eq`).

## 7. Time trends and frequency × severity (2026-11-19, for `notes/time-trends.md`)
- Hachemeister (1975), *Credibility for regression models with application to trend*, in Kahn
  (ed.), *Credibility: Theory and Applications* (checked by web search, CAS abstract): random
  level and slope per state, matrix credibility. Used: the model of trend step 3.
- Bühlmann & Gisler (1997), *Credibility in the regression case revisited*, ASTIN Bull. 27(1),
  83–98 (checked): centre time at each risk's mean so level and slope decouple into scalar
  credibilities. Used: the parametrisation for correlated Hachemeister.
- Jewell (1975), regression credibility with parameters inflated by unknown amounts (cited via
  the search; not read).
- Goulet, Forgues & Lu (2006), *Credibility for severity revisited*, NAAJ 10(1), 49–62
  (checked): four ways to bring frequency and severity into credibility stem from one
  minimisation problem. Starting point for the frequency–severity comparison; to read in full.
- Hewitt (1971), credibility for severity (CAS Proceedings; cited via Goulet et al.).
- Not yet checked: Gerber & Jones (1975) evolving levels; Werner & Modlin, *Basic Ratemaking*
  (separate frequency and severity trends).

### 7a. Vector levels, for `Credibility/CoreVector.lean` (2026-11-19)
Read in full from casact.org (allowlisted in **lean** on 2026-11-19), except where marked.
- Hachemeister (1975), *Credibility for regression models with application to trend*, in Kahn
  (ed.), *Credibility: Theory and Applications*, 129–163; CAS Forum Spring 1992 reprint, 307ff
  (read). States' severity trends (BI, 5 states). The "super" covariance of all observations
  is block diagonal: "observations from one state are independent of those from another
  state". Country-wide line = pooled GLS `β̂ = (YᵀC⁻¹Y)⁻¹YᵀC⁻¹X` with the *noise* covariance
  `C`. Estimator `a₀ + XᵀA` (inhomogeneous), best by unbiasedness + minimum variance; structural
  parameters estimated unbiasedly (trace argument, as our §2.8). Quinn's discussion flags
  autocorrelation and heteroscedasticity. Used: the model of the Hachemeister corollary.
- Bühlmann & Gisler (1997), *Credibility in the regression case revisited*, ASTIN Bull. 27(1),
  83–98 (read). General case: `β̂ᵣ = (I - Zᵣ)b + Zᵣ bᵣˣ`, `Zᵣ = A(A + Wᵣ⁻¹)⁻¹`, `Wᵣ = YᵣᵀΦᵣ⁻¹Yᵣ`,
  `bᵣˣ = Wᵣ⁻¹YᵣᵀΦᵣ⁻¹Xᵣ` (individual GLS), `A = Cov(β(Θ))`. Risks iid. Uncentred time gives
  `Z` with weights outside [0, 1] and lines "out of range" (their examples 1–3); intercept at the
  volume-weighted barycentre makes `W` diagonal, so with `A` diagonal `Z` splits into two scalar
  credibilities (volumes `V` and `V·Var(k)`). General case: weighted Gram–Schmidt on the design.
  Caveat (§7): orthogonality holds for one sampling distribution only, so per risk it is only
  "nearly" separated. Used: in our notation the risk-`r` estimate has `Kᵣᵣ = A + Wᵣ⁻¹`, `L = A`,
  and their known-mean `Zᵣ = Lᵣᵣ Kᵣᵣ⁻¹`; our `moments_bestZ` is the homogeneous version, and
  with correlated cohorts `K` is not block diagonal.
- Bühlmann (1974), *A comparison of three credibility formulae using multidimensional
  techniques*, ASTIN Bull. 7(3), 203–207 (read; poor scan). Inspired by Jewell (1973), which was
  never published in ASTIN ("in agreement with the author"). Target: the pure premium
  `E_k(η)·E_y(θ)` (frequency × severity) with η, θ *independent*; predict linearly from the
  claim count `k` and the total `T = Σ yᵢ`. Three cases: both statistics (multidimensional),
  only `k`, only `T` (one-dimensional). Case I is always best; II and III are **not ordered**
  (either can win). Used: the precedent for our target "vector blend ≤ separate and single-`B`
  blends", and a warning that separate vs single `B` has no general order.
- Jewell (1973), *Multi-dimensional credibility*, ORC 73-7, UC Berkeley (not found online; known
  through Bühlmann 1974 and Englund et al. 2008).
- Englund, Guillén, Gustafsson, Nielsen & Nielsen (2008), *Multivariate latent risk: a
  credibility approach*, ASTIN Bull. 38(1), 137–146 (read). One latent risk *per line*, `Θᵢ ∈ ℝᴾ`
  with covariance `T` (B–G 2005's multidimensional model has one common Θ: correlation 1).
  Estimator `E θ + Cov(θ, Ȳ)Var(Ȳ)⁻¹(Ȳ - EȲ)` (eq. 2), customers independent. Danish data:
  correlation 0.62 between water and theft; with time dependence also cross-lagged. Used:
  `L` with non-trivial off-diagonal blocks is what data show; our `L` allows it.
- Taylor (2007), *Credibility, hypothesis testing and regression software*, ASTIN Bull. 37(2),
  517ff (abstract and intro read): matrix credibility via F-statistics; for the estimation step.
- Bühlmann & Gisler (2005), *A Course in Credibility Theory*, ch. 7 (§7.3 multidimensional
  Bühlmann–Straub, p. 177) and ch. 8 (§8.3.2 Hachemeister, p. 205): not read (book). Our
  `moments_bestZ_buhlmannGisler`/`weight_buhlmannGisler` reproduce the 1997 paper's
  `Zᵣ = A(A + Wᵣ⁻¹)⁻¹` and the `Z`-weighted collective `(ΣZᵢ)⁻¹ΣZᵢbᵢ` (the form quoted for
  §7.3). Page check, pp. 177–179 read (2026-11-19, owner's photos): Model Assumptions 7.7
  match ours. A1: given `Θᵢ`, years independent with mean `μ(Θᵢ)`; A2: risks independent,
  `Θᵢ` i.i.d. (our block-diagonal `K`, `L` with `Lⱼⱼ = Λ`). Conditional covariance either
  diagonal `σₖ²(Θ)/wᵢⱼ⁽ᵏ⁾` (7.30, "standard") or `Σ(Θ)/wᵢⱼ` with one weight (7.31,
  "alternative"); under the general (7.32) the book says its results fail. Ours takes the
  cohort estimates as given with any `Sⱼ`, so it covers (7.32) for predictors linear in those
  estimates. `vecBalanced_buhlmannGisler` is the (7.31) case `Sⱼ = S₀/wⱼ`. Pp. 180–181:
  compression `Bᵢ = Wᵢ•⁻¹ΣⱼWᵢⱼXᵢⱼ` (diagonal weight matrices), `Cov(Bᵢ|Θᵢ) =
  Wᵢ•^(-1/2)Σ(Θᵢ)Wᵢ•^(-1/2)` (7.35, fails under 7.32), and Theorem 7.8 (inhomogeneous, `μ`
  known): `Aᵢ = T(T + Wᵢ•^(-1/2)SWᵢ•^(-1/2))⁻¹`, `T = Cov(μ(Θ))`, `S = E[Σ(Θ)]`. This is our
  `Zⱼ = Λ(Λ + Sⱼ)⁻¹` with `Λ = T`, `Sⱼ = Wⱼ•^(-1/2)SWⱼ•^(-1/2)`; ours is the homogeneous case
  (GLS `μ̂`), where `moments_bestZ_of_blockDiag` shows the same `Z`. Pp. 183–184: Theorem 7.9
  (homogeneous) `Aᵢ Bᵢ + (I − Aᵢ)(ΣAᵢ)⁻¹ΣAᵢBᵢ` is our `weight_buhlmannGisler` (needs `T`
  invertible; our GLS form `(ΣKᵢᵢ⁻¹)⁻¹Kⱼⱼ⁻¹` does not). Theorem 7.10 (componentwise balance
  for the volumes under (7.30) or (7.31)) is our `vecBalanced_buhlmannGisler_diag` and
  `vecBalanced_buhlmannGisler`, both from `vecBalanced_of_mul_noise` (`UⱼSⱼ` constant).
  Check of §7.3 against the book done (2026-11-19). Bühlmann,
  Gisler & Kollöffel (2003), multidimensional credibility: cited by Englund et al., not read.
- Frequency–severity with dependent risk profiles, Bayesian: Cheung, Ni, Oh & Woo (2021), IME
  100, 274–295; Q-credibility (ARCH 2025 abstract, Tang): factors chosen to minimise the MSE of
  the *pure premium*, as Bühlmann (1974). Not read.
- New here: in all of the above, risks/cohorts are independent (`K` block diagonal) and the
  collective mean is either known or a GLS under that independence. We allow a full `K` over
  cohorts × components (year shocks correlate cohorts) and the matrix GLS
  `μ̂ = (UᵀK⁻¹U)⁻¹UᵀK⁻¹x`; the best `Zⱼ` is `(Lⱼⱼ - EⱼᵀLW)(Kⱼⱼ - (UᵀK⁻¹U)⁻¹)⁻¹`.

## 8. Correlated noise across cohorts: prior art and foundation (2026-11-19)
Owner's question: the thesis (§2.2.3) found no reference for correlated *observation noise*
across cohorts in the same period. Re-searched by web; publisher pages were not reachable from
the session, so contents below are from abstracts and listings only.

**Verdict.** The thesis is right about the two papers it cites, and right that the classical
credibility texts assume independence across risks. "No references" is too strong, though:
- Wen & Wu (2011), *The credibility estimator with general dependence structure over risks*,
  Comm. Stat. Theory Methods 40(10), 1893–1910. **Read §2–3.1 (pp. 1895–1897, owner's photos,
  2026-11-19).** Assumption 3.1: given `Θᵢ` the claims of risk `i` are conditionally
  independent with `Var(Xᵢⱼ | Θᵢ) = σ²(Θᵢ)`. Assumption 3.2: `Cov(μ(Θᵢ), μ(Θⱼ)) = τᵢⱼ`, and
  "the dependence structure can be specified by" `R = (τᵢⱼ)`. So the dependence is on the
  **levels** (a general-matrix version of Nurrohmah), permanent over time; the noise stays
  uncorrelated across risks. **Not the thesis model.** In our terms it is Core with level
  covariance `L = R` and `K = R + diag(σᵢ²/nᵢ)`. Their Lemma 2.1 (from Wen, Wu & Zhou 2009) is
  the general tool: for any covariance `Σ_XX`, the homogeneous projection (2.5) is
  `(Σ_YX + (μ_Y − Σ_YXΣ_XX⁻¹μ_X)μ_X′ / μ_X′Σ_XX⁻¹μ_X) Σ_XX⁻¹ X`, i.e. Goldberger's predictor
  (with `μ_X = μ1`: GLS mean plus correction). It holds for the thesis's `Σ_XX` with correlated
  noise too, so it is the same foundation as `Core.blupWeight_optimal`, in projection form.
  With equal `τᵢⱼ` off the diagonal (a permanent common effect) the homogeneous estimator is
  unchanged, consistent with `wen2`.
- Wen & Deng (2011), J. Syst. Sci. Complex. 24(3), 532–539 (thesis ref `wen`, in the
  bibliography but not cited in the text): equal correlation between risks, homogeneous and
  inhomogeneous estimators by projection. The common-effect paper the thesis discusses is
  `wen2` = Wen, Wu & Zhou (2009), IME 44 (§3).
- Zhang, Cui & Chen (2017), *Multidimensional credibility estimators with random common
  effects and time effects*, J. Syst. Sci. Complex. 30, 1107–1120. **Read §2 and Lemma 2.1
  (pp. 1108–1110, owner's photos, 2026-11-19).** One permanent common effect `Λ`; `Θᵢ`
  independent given `Λ`; vector claims `Xᵢⱼ ∈ ℝᵖ`. The "time effect" is a uniform correlation
  *within a risk over time*: `Cov(Xᵢⱼ, Xᵢₜ | Θᵢ, Λ) = ρ(Θᵢ, Λ)`, `j ≠ t`. Across risks,
  `Cov(Xᵢⱼ, Xₛₜ) = W = Var μ(Λ)` for every pair of periods, so eq. (7),
  `Σ_XX = I_K ⊗ (I_n ⊗ (Σ − ρ) + 1ₙ1ₙᵀ ⊗ (V + ρ)) + 1_{nK}1_{nK}ᵀ ⊗ W`, has no term that
  links two risks in the *same* period only. **Not the thesis model.** Note that `ρ` only moves
  variance from the noise `Σ` to the level `V` (`Σ − ρ` and `V + ρ`), so for prediction it acts
  like a larger level variance.
- Huang & Wu (2015), *Credibility models with dependence structure over risks and time
  horizon*, J. Ind. Manag. Optim. 11(2), 365–380. **Read in full (owner's PDF, 2026-11-19).**
  Assumption 1/3: `Cov(Xᵢ | Θ) = σ²(Θᵢ)/wᵢⱼ I + ρ(Θᵢ) 11ᵀ` within risk `i` (exchangeable over
  time), `Cov(μ(Θᵢ), μ(Θⱼ)) = τᵢⱼ` across risks; Lemma 3.1/4.1:
  `Σ_XX = diag(1ₙᵢ) R diag(1ₙᵢᵀ) + diag(Gᵢ)`, block diagonal noise. So across risks only the
  levels correlate, as in Wen & Wu (2011). **Not the thesis model.** Their introduction surveys
  the field as two strands, "dependence over risks" (common effects, correlated levels) and
  "conditional dependence over time" (within a risk), with no work combining them; noise
  correlated across risks within a period is in neither. Their conclusion: under dependence the
  premium is no longer `(1 − z)·mean + z·own mean` in general, only a linear function of all
  claims. That is the BLUP-vs-blend gap that Finding 18 makes exact (price of the blend, and
  when it is zero).
- Dannenburg (1995), *Crossed classification credibility models*, TI 95-64 (DARE has the
  record only, no PDF); Dannenburg, Kaas & Goovaerts (1996), ch. 6; Goulet (2001).
  `y_ijt = β + α_i⁽¹⁾ + α_j⁽²⁾ + α_ij + ε_ijt`: both factors are *risk* classifications, so
  cells sharing a row correlate permanently, not per year. Taking the second factor to be the
  year would give equicorrelated noise within a year (ρ ≥ 0 only), but that is our reading,
  not their use.
- Fung & Xu (2009), *Estimation and robustness of linear mixed models in credibility context*,
  Variance 2(1), 66–80 (read in full, casact.org). ML/REML for Hachemeister and Dannenburg
  under normality. Their correlated errors (MA(1), AR(1), exchangeable) are **within one risk
  over time**; risks stay independent ("yᵢ and yⱼ are statistically independent for i ≠ j").
  They survey the actuarial correlated-error work the same way: Cossette & Luong (2003,
  weighted least squares) and Lo, Fung & Zhu (2006, 2007, GEE), all within-panel; Frees et
  al. (1999) and Antonio & Beirlant (2006) "only independent error structure". So the
  actuarial mixed-model line supports the thesis's finding: correlation *across* risks in the
  same period is not treated there.
- Remark on the thesis's reading of `wen2`: a common effect that is *permanent* (one `Λ` for all
  years) only enters the inhomogeneous estimator. A common effect *per year* is noise
  correlated within the period and does change the homogeneous estimator; that is the thesis's
  case, so the two statements do not conflict.

**Foundation (agreed).** The data model of §2.3 is a linear mixed model specified by first and
second moments only. The best linear unbiased estimator of the mean under an arbitrary positive
definite covariance is Aitken's GLS (Aitken 1935, Proc. R. Soc. Edinb. 55, 42–48); the best
linear unbiased predictor of a random effect under arbitrary covariances of effects *and* errors
is Goldberger (1962, JASA 57) and Henderson / Harville (1976, *Extension of the Gauss–Markov
theorem to include the estimation of random effects*, Ann. Stat. 4(2), 384–395). Frees, Young &
Luo (1999), *A longitudinal data analysis interpretation of credibility models*, IME 24,
229–247, show the additive credibility models are special cases of this longitudinal model.
So correlated noise is standard in mixed models and BLUP theory; the thesis's contribution lies
in bringing it into the Bühlmann–Straub form: the blend with GLS weights, eq. (26), its
singularities and factors outside [0, 1], the §2.8 estimators of `K` from same-period cross
products, and balance. Proofs here use only that foundation (no distribution).

**Status (2026-11-19, second pass).** Allowlisted `dare.uva.nl`, `casact.org`,
`www.casact.org`, `sysmath.cjoe.ac.cn` in the Default environment. Fung & Xu read; Dannenburg
has no open PDF; `sysmath.cjoe.ac.cn` refuses the session (HTTP 403 from the site). The three
candidates that might contain within-period dependence across risks were paywalled. Wen & Wu
(2011) and Zhang, Cui & Chen (2017) are read from photos, Huang & Wu (2015) in full from the
owner's PDF; none of them is it (correlated levels, permanent common effects, within-risk
time correlation). No open candidates; a reviewer may still search further: owner to supply PDFs or photos of the model
assumptions, the homogeneous estimator and any parameter estimation.

**For a reviewer.** (1) Search for any credibility or small-area paper with noise correlated
across units within a period (Wen & Wu 2011, Huang & Wu 2015, Zhang, Cui & Chen 2017, Fung &
Xu 2009 checked: none has it); if so, cite and move the "new here" in paper §15.
(2) Check that `Core.blupWeight_optimal` matches Goldberger's/Harville's predictor.
(3) Check Bühlmann & Gisler (2005) for any within-period dependence across risks.

## 9. Contemporaneous correlation in econometrics (2026-11-19)
Why the thesis assumption is new to credibility but not to statistics. Citations from memory,
not re-checked online.
- Zellner (1962), *An efficient method of estimating seemingly unrelated regressions and tests
  for aggregation bias*, JASA 57, 348–368 (SUR): equations whose errors are correlated in the
  same period and independent across periods, `Cov(εᵢₜ, εⱼₛ) = σᵢⱼ δₜₛ`. That is exactly the
  thesis's `ρᵢⱼ δₜₛ`. Feasible SUR estimates `σᵢⱼ` from same-period cross products of
  residuals, as §2.8 does for `K`.
- Parks (1967), JASA 62, 500–509: FGLS with errors both contemporaneously and serially (AR(1))
  correlated; the roadmap's "serial correlation" step.
- Beck & Katz (1995), *What to do (and not to do) with time-series cross-section data*, APSR
  89, 634–647: Parks FGLS with the full `Σ̂` is badly overconfident unless T is much larger
  than the number of units; they recommend OLS with panel-corrected standard errors. Same
  lesson as the thesis's over-parametrization worry and our studies S6, S11–S13 (restrict or
  damp `K̂`).
- Driscoll & Kraay (1998), Rev. Econ. Stat. 80, 549–560; Pesaran (2006), *common correlated
  effects*, Econometrica 74, 967–1012; Bai (2009), interactive fixed effects, Econometrica
  77, 1229–1279: cross-sectional dependence as common factors with unit-specific loadings, the
  rank-one / low-rank `K` of Core (`notes/roadmap.md`, "period shocks are already in").
- Separating a common component from sampling noise of known relative size `1/wⱼₜ` is the
  method-of-moments step of variance-component estimation (Henderson's method III; in small-area
  estimation the Fay–Herriot model takes the sampling variances as known). From memory.
  `Credibility/Shock.lean` uses it on the diagonal: the volumes must vary for `Cⱼⱼ` and `sⱼ²`
  to be identified.
Used: the interpretation (thesis model = SUR error structure inside a credibility model) and
the warning on full `K̂`. New here: the combination with random levels and the blend.

## 10. Monthly card data: Step 0 of `notes/card-data.md` (2026-11-20)
Web search (abstracts and listings) unless marked "read". Two papers read in full from
casact.org: Ledolter, Klugman & Lee (1991) and Zehnwirth (1985).

**Answer to the note's question.** A *seasonal* credibility model exists (Ledolter, Klugman &
Lee 1991, below), but with seasons estimated per group on a log scale, groups independent, and
shrinkage added heuristically at the last period. Credibility with a *common* AR(1) factor
across risks was not found: the dynamic actuarial models (Gerber & Jones, Sundt, Pinquet) make
each risk's own level evolve and keep risks independent; the common-effect models (Yeo & Valdez
2006, Wen, Wu & Zhou 2009, §8) have one permanent common effect, not one per period that
evolves. Ledolter et al. name the common-trend model as future work (Lee 1991, an Iowa thesis;
not found online). The pieces exist separately in small-area estimation (Rao & Yu 1994) and
econometrics (dynamic factor models); their combination with the blend, GLS weights and
same-period cross-product estimators is new here, as in §8.

### 10a. BLUP with fixed effects and a general target (Step 1)
- Goldberger (1962), *Best linear unbiased prediction in the generalized linear regression
  model*, JASA 57, 369–375. Predict `Y` from `x` with `E x = Xβ`, `E Y = x₀ᵀβ`, `Cov x = K`,
  `Cov(x, Y) = ℓ`: `Ŷ = x₀ᵀβ̂ + ℓᵀK⁻¹(x − Xβ̂)`, `β̂` the GLS estimate. Expanded, its weights are
  Step 1's `d*`. Cressie (1990, *The origins of kriging*, Math. Geol. 22) credits Goldberger
  with this and notes he did not apply it spatially. Used: Step 1's main theorem is
  Goldberger's predictor plus the MSE decomposition `MSE(d) = MSE(d*) + (d − d*)ᵀK(d − d*)`.
- Harville (1976), Ann. Stat. 4(2), 384–395 (§8): target `λ₁ᵀα + λ₂ᵀb`, a fixed plus a random
  part, among linear predictors unbiased for every `α`. Exactly Step 1's general target with
  `x₀ = λ₁` and `ℓ = Cov(x, λ₂ᵀb)`. Henderson's mixed-model equations compute the same.
- Universal kriging (Matheron 1969) and kriging with external drift: the same predictor,
  derived with Lagrange multipliers for `Xᵀd = x₀`. External drift = a known covariate column in
  `X` (Step 3b's `Dₜ`). Software notes warn that external drifts can make the system
  ill-conditioned; relevant when `Dₜ` is nearly collinear with the season columns.
- Wen & Wu (2011), Lemma 2.1 (§8): the one-column case `X = μ_X`.
- Kruskal (1968), *When are Gauss–Markov and least squares estimators identical?*, Ann. Math.
  Stat. 39, 70–75 (from memory): OLS = GLS iff the column space of `X` is `K`-invariant. The
  same kind of condition decides when a richer design leaves the BLUP unchanged (Step 2).

### 10b. Seasonality (Steps 1–2)
- **Ledolter, Klugman & Lee (1991)**, *Credibility models with time-varying trend components*,
  ASTIN Bull. 21(1), 73–91 (**read**). US bodily-injury loss/exposure by state, quarterly,
  31 states, 22 quarters. Model per state on the *log* scale: structural time series
  (Harvey) with level, slope and three additive quarterly seasonal factors, noise `σ²/Pₜ`
  (checked on the data: residual variance linear in 1/exposure). Kalman filter per state, then
  the end-of-sample states are shrunk towards a common value with Bühlmann–Straub-type
  `Z = B(B + V)⁻¹` (De Vylder's iterative estimates). States independent; they say a
  cross-correlation structure is possible in theory but "quite difficult to identify ... for
  short time series", and call their shrinkage step heuristic. Seasonal indices were estimated
  per state and averaged per quarter (fourth quarter highest). Also cited: Meyers & Schenker
  (1983), workers' comp loss ratios "vary independently from year to year around a common
  mean", i.e. a common year effect. Used: precedent for estimated seasons in credibility; their
  log/multiplicative choice is the alternative Step 2 must settle; the missing cross-sectional
  correlation is what Step 3 adds.
- *Notiz zu einem saisonalen Kredibilitätsmodell*, Blätter DGVFM (Springer, doi
  10.1007/BF02809439; author and year not shown in the listing): a credibility model with
  seasonal effects in the net premium. Not read; owner could check the DGVFM archive.
- Nothing found on seasonality in ratemaking credibility beyond these; Werner & Modlin
  (*Basic Ratemaking*) treat seasonality by annual aggregation and trend factors (from memory).

### 10c. Evolutionary and state-space credibility (Step 3, time dimension)
- Gerber & Jones (1975), *Credibility formulas of the updating type*, TSA 27 (also in Kahn,
  ed., *Credibility*): recursive (exponential-smoothing) credibility holds iff the covariances
  have a specific form. Sundt (1981, Scand. Act. J.; 1983) generalizes; Jewell (1975) names the
  class "evolutionary"; Kremer (1982) links to exponential smoothing.
- Zehnwirth (1985), *Linear filtering and recursive credibility estimation*, ASTIN Bull.
  15(1), 19–36 (**read**, intro): projection/innovation proof, Kalman-type filters valid
  without normality (linear least squares only). De Jong & Zehnwirth (1983): credibility as a
  Kalman filter. Used: a common AR(1) factor has a state-space form, so the app can compute the
  Step 3 predictor by a Kalman filter instead of inverting `K` over all cells; the Lean
  statement stays the closed form.
- Bühlmann & Gisler (2005): evolutionary models are **chapter 9** ("Evolutionary credibility
  models and recursive calculation", §9.5 Kalman filter), not chapter 10 (table of contents).
- Pinquet, Guillén & Bolancé (2001), ASTIN Bull. 31(2), 337–348; Bolancé, Guillén & Pinquet
  (2003), IME; Pinquet (2020), *Poisson models with dynamic random effects and nonnegative
  credibilities per period*, ASTIN Bull. 50(2), 585–618; Ahn et al. (arXiv 2109.07956). Per-risk
  stationary random effects; the weight on old claims falls with their age. Pinquet (2020): an
  AR(p) autocovariance can give *negative* weights per period unless constrained (nonnegative
  partial autocorrelations suffice; ARFIMA(0,d,0) is safe). Used: expect negative per-month
  weights with an AR(1) common factor too; a likely finding for Step 3, and a display issue for
  the app.
- Chen, Cheung, Choi & Yam (2020), *Evolutionary credibility risk premium*, IME 93, 216–229:
  Bühlmann's evolutionary model with general (e.g. ARMA) dependence, recursive computation.
  Evolutionary hierarchical credibility (ASTIN Bull., 2017). Not read.
- Englund, Gustafsson, Nielsen & Thuring (2009), *Multidimensional credibility with time
  effects*, J. Risk Insur. 76(2), 443–453: age-dependent weights in multivariate credibility,
  Danish commercial lines. Not read.

### 10d. Common factors (Step 3, cross-section)
- Stock & Watson (2002), JASA 97, 1167–1179 and JBES 20, 147–162: approximate dynamic factor
  model `Xᵢₜ = λᵢ(L)fₜ + uᵢₜ`, factors by principal components, consistent for many series.
  Asymptotics need many series and periods; our card count is small, so PCA estimates of `λ`
  are noisy. Used: the model form of Step 3 (`λᵢλⱼΓₜₛ`); §9's Pesaran (2006) and Bai (2009)
  are the panel-econometrics versions.
- Rao & Yu (1994), *Small area estimation by combining time series and cross-sectional data*,
  Can. J. Stat. 22, 511–528: area level `vᵢ` plus area-by-time AR(1) `uᵢₜ`, sampling errors with
  known covariance; EBLUP (R package `sae2`, also a "dynamic" variant without stationarity).
  The AR(1) is *per area*, areas independent. Datta, Lahiri, Maiti & Lu (1999), JASA 94,
  1074–1082: random-walk area effects (hierarchical Bayes). Pfeffermann & Burck (1990), Survey
  Methodology 16; Pfeffermann & Tiller (2006), JASA: state-space SAE with benchmarking. A Census
  working paper (2024, RRS2024-08) finds AR(1), random-walk and Rao–Yu models often beaten in
  short series. Used: Rao–Yu's per-unit AR(1) is the Pinquet-type alternative to a common
  factor (a `diag` block in time per card); worth a switch value "per-card AR(1)" if the
  student finds the common factor too strong.

### 10e. Regression credibility and random coefficients (Step 3b)
- Hachemeister (1975), Bühlmann & Gisler (1997): §7, §7a. In the repo,
  `CoreVector.hachemeister_bestZ` takes any design `Yⱼ` (`T × P`) and any noise `Φ ≻ 0` over
  cohorts × periods. With `Yⱼ = [1, Dₜ]` the random line `(μⱼ, λⱼ)` with covariance `L` is
  Step 3b's random effects, and `CoreVector.blupW_optimal_dotProduct` with `a = (1, D_{T+1})`
  gives the best predictor of `μⱼ + λⱼD_{T+1}`. So Step 3b's "known signal, unknown
  sensitivities" with correlated cards is already proved, for a `Φ` that contains the shock
  terms. What it does not cover: (i) a persistent latent factor in `Φ` that also enters the
  target (needs Step 1's general `ℓ`), (ii) season columns common to all cards.
- Swamy (1970), *Efficient inference in a random coefficient regression model*,
  Econometrica 38(2), 311–323: the same model in econometrics, GLS for the mean coefficient,
  unbiased moment estimator of `Cov(βᵢ)` (may be non-PSD, as Ledolter et al. note for `B̂`).
  Used: the estimation step of Step 5 for `cov(λᵢ, λⱼ)`.
- Public demand signal (Sweden): Trafikanalys, *Luftfart* (official, annual; monthly series
  on trafa.se/luftfart), Transportstyrelsen monthly flight statistics (not official
  statistics), Swedavia monthly passengers per airport, Eurostat `avia_pa` (monthly, about four
  months' lag). Note the lag: `Dₜ` for recent months arrives late, like reporting delay.

### 10f. Panels with entry and exit (Q5)
- Frees, Young & Luo (1999), IME 24, 229–247; Frees, Young & Luo (2001), NAAJ 5(4), 24–42
  (case studies); Frees (2004), *Longitudinal and Panel Data*, CUP: unbalanced panels are
  handled by the mixed model directly (each unit its own `Tᵢ`), as our `Unequal` (`obs j`).
  Exited units stay in the data: their past cells inform the collective mean, the season,
  the estimates of `K` (same-month cross products) and, through `K`, the other units'
  predictors; they just get no target. Under a likelihood, exit that depends only on the
  observed past (missing at random) is ignorable; Frees ch. 7 and Raknerud (2002, Statistics
  Norway DP 330) treat non-ignorable exit. Our layer is distribution-free and treats `obs j`
  as fixed, so its guarantees (unbiasedness, MSE) need exit independent of the claims. If a
  card is withdrawn *because* it ran badly, its data are still used, but the exit time acts
  like an optional stopping time and the cell means can be biased; the guarantees are then
  approximate. State it as an assumption, not a theorem. Left to the student, with a test in
  the app world (exit driven by results).

### 10g. Edits to `notes/card-data.md` (applied 2026-11-20)
1. Step 0: Bühlmann & Gisler ch. 9 (not 10) for evolutionary credibility.
2. Step 1: name the main theorem as Goldberger's/Harville's predictor (target
   `x₀ᵀβ + random part`); the formula for `d*` is theirs, the MSE identity and the corollaries
   are ours to prove.
3. Step 2, "Expected: the season drops out": the BLUP never depends on `β`, but the *weights*
   with a seasonal design differ from those with one mean unless the one-mean `d*` already
   satisfies the month-wise constraints `Σ_{cells in month m} dᵢ = 1`. Restate the expected
   result as a Kruskal-type condition: the two predictors coincide iff `Xᵀd*₁ = x₀`; sufficient
   if all cards are observed in whole years and `K` and `ℓ` are invariant under shifting the
   calendar. That is rare: the noise `sᵢ²/wᵢₜ` changes with seasonal volume, and an AR(1)
   factor favours recent months. So expect the season to change the weights in general, and
   the counterexample to be easy. Also: Ledolter et al. use a multiplicative
   season on the log scale; the additive-on-rate form is the linear one, so say Lean takes the
   additive form and the log scale is an app option.
4. Step 3: add "expected finding: per-month weights can be negative with an AR(1) `Γ`" (Pinquet
   2020), and that the predictor has a Kalman-filter form for the app (Zehnwirth 1985). Consider
   a per-card AR(1) (Rao–Yu, Pinquet) as a further value of the "latent factor over time"
   switch: it is `Γ` per card instead of `λλᵀ ⊗ Γ`.
5. Step 3b: replace "First check whether that already covers it" by: covered by
   `CoreVector.hachemeister_bestZ` + `blupW_optimal_dotProduct` with `Yⱼ = [1, Dₜ]` and
   `a = (1, D_{T+1})`, for any noise `Φ`; new are only the common season columns and a latent
   factor that also enters the target (both via Step 1). Swamy (1970) for the estimator of
   `cov(λᵢ, λⱼ)`.
6. Step 5 / Q5: exited cards keep all their past cells in the fit (they inform the mean,
   season, `K̂` and, through `K`, the other cards). The exact guarantees assume the exit time
   is independent of the claims; results-driven exit makes them approximate (Frees 2004).
   App world: an option for exit driven by results, to measure the effect.
7. Literature status line: "credibility with a common AR(1) factor: not found; seasonal
   credibility: Ledolter, Klugman & Lee (1991), independent groups, heuristic shrinkage".

### 10h. Estimating the factor model (card-data Steps 4–5, 2026-11-20)
For the table of `Credibility/Factor.lean`,
`cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼΓₜₛ + δₜₛCᵢⱼ + δₜₛδᵢⱼsᵢ²/wᵢₜ + τ²δᵢⱼ` (+ `δᵢⱼGᵢ,ₜₛ` per-card dynamics),
`Γ` AR(1) `γφ^|t−s|` or a block per regime, cards entering and leaving, monthly rates, and no
hand-set hyperparameters (`studies/PLAN.md` §1). Web search (abstracts, listings, package
manuals) on 2026-11-20; nothing read in full. "From memory" marks what was not re-checked.
(Numbering: the request said "Step 4"; in `notes/card-data.md` estimation is Step 5, and
Step 4 is "when does the factor cancel"; the normalisation result below serves both.)

**Dynamic factor models (econometrics).**
- Stock & Watson (2002, JASA 97; JBES 20): principal components on a balanced panel; for missing
  cells an EM that alternates PCA and filling in. Consistency needs many series *and* many
  periods. Normalisation `ΛᵀΛ/N = I` (from memory). Used: only as a cross-check; with a
  handful of cards the factor path is not consistently estimable (fixed `J`), but its
  *covariance parameters* are as `T` grows, and that is all the predictor needs.
- Bai & Ng (2002), *Determining the number of factors in approximate factor models*,
  Econometrica 70(1), 191–221: information criteria for the number of factors, large `N` and
  `T`; reported to overestimate in small samples. Bai (2003), Econometrica 71 (from memory):
  inferential theory for PCA factors. Used: the student's "one factor or several" question;
  with few cards prefer the lag-moment checks below.
- Forni, Hallin, Lippi & Reichlin (2000, REStat) generalized dynamic factor model and Doz,
  Giannone & Reichlin (2011, J. Econometrics; 2012, REStat): PCA first, then a Kalman
  smoother; Gaussian quasi-ML is consistent under misspecification and non-normality for
  large `N` (from memory; not found in this search). Used: the two-step idea (moments, then
  filter) for the app.
- Bańbura & Modugno (2014), *Maximum likelihood estimation of factor models on datasets with
  arbitrary pattern of missing data*, J. Appl. Econometrics 29(1), 133–160 (ECB WP 1189,
  2010): Watson & Engle's (1983) EM with a Kalman smoother in the E-step and two regressions in
  the M-step, any missing pattern, serially correlated idiosyncratic parts (= our per-card
  `Gᵢ`). R package `dfms` ("BM" option). Used: the app's likelihood-based fit for an
  unbalanced card panel (cards entering and leaving = missing cells).
- Lam, Yao & Bathia (2011, Biometrika per the arXiv listing, arXiv 1004.2138) and Lam & Yao
  (2012), Ann. Stat. 40(2): the loading space from the **lagged** autocovariance matrices
  `Σ_h, h ≥ 1` only, because idiosyncratic noise that is white in time does not enter them;
  the number of factors from ratios of their singular values. A 2026 preprint
  (arXiv 2610.00766) adds the lag-0 covariance back. Used: the same idea answers our lag-0
  confounding (below): lagged cross-moments contain no `C`, no `s²/w`, and for `i ≠ j` no
  `τ²` and no `Gᵢ`.
- Identification and normalisation. Bai & Wang (2015, JBES; Columbia discussion paper):
  identification of dynamic factor models with lower-triangular loadings (positive diagonal)
  or unit factor-innovation variance; treating a dynamic model as static needs more
  restrictions than necessary. A scalar normalisation (arXiv 2412.01367) identifies loadings
  and factor up to one common constant. Classical factor analysis (Anderson & Rubin 1956,
  from memory): one factor is identified from the off-diagonal covariances when at least three
  loadings are non-zero; fixes `Var f = 1`. Used: normalisation choice below.
- Short panels: Fortin, Gagliardini & Scaillet (arXiv 2306.14004), large `N`, fixed `T`,
  pseudo-ML without Gaussianity. Opposite of our case (few cards, many months).
- Fasen-Hartmann & Mayer (arXiv 2002.09426): the Whittle estimator is consistent and
  asymptotically normal for stationary state-space models with finite second moments; its
  limit covariance differs from the Gaussian one. Used: Gaussian likelihood / Whittle is a
  distribution-free *estimating equation* (consistent), not an assumption on the data; the
  standard errors must not be the Gaussian ones.

**Variance components with time correlation.**
- Henderson (1953) method III: equate quadratic forms (sums of squares) to their expectations
  and solve the linear system; unbiased, no optimality for unbalanced data (Searle). Rao
  (1970, JASA; 1971, J. Multivar. Anal. 1, 257–275; 1972) MINQUE: for `Cov = Σₖ θₖVₖ` the
  minimum-norm unbiased invariant quadratic estimators; one MINQUE iteration from a prior
  guess, iterated it is REML (Patterson & Thompson 1971, from memory). LaMotte (1973, from
  memory): unbiased and non-negative are generally incompatible. Used: given `φ` (or a block
  shape) our table is **linear** in the remaining parameters, so this is exactly the route to
  unbiased estimators; the repo's `Expectation.UnbiasedCov` is the Henderson-III criterion and
  `Shock.CHat`, `s2Hat`, `tauHat` are instances.
- Swamy (1970), Econometrica 38, 311–323: unbiased estimator of the coefficient covariance;
  may be non-PSD in finite samples, Swamy sets it to zero then (Poi, Stata J.; Monash WP).
  Used: the same fix-up for `γλλᵀ`, `C` (or damping, `OffDiagonal.lean`), which breaks
  unbiasedness: report the raw estimate as the unbiased one, the truncated one as the fit.
- Rao & Yu (1994), Can. J. Stat. 22: area effect + AR(1) per area + known sampling variance;
  they give a method-of-moments estimator for the variances and `ρ` (Rao 2003, *Small Area
  Estimation*, §10.9, not read); `sae2` uses ML/REML with `ρ` estimated (default start
  `0.9`). Datta, Lahiri, Maiti & Lu (1999), JASA 94, 1074–1082: hierarchical Bayes (Gibbs) for
  state unemployment rates, random-walk version. Used: Rao–Yu's MoM is the per-card (`Gᵢ`)
  half of our problem; their experience (Census RRS2024-08) that `ρ` is poorly determined in
  short series carries over.
- Pinquet, Guillén & Bolancé (2001), ASTIN Bull. 31(2): Poisson regression by ML, then the
  autocovariances of the stationary random effects **per lag** by second-order moments; the
  estimated autocorrelations decrease with the lag. Pinquet (2020): nonnegative credibilities
  need constraints on the autocovariance (§10c). Used: the two-stage recipe "unstructured lag
  moments, then fit a decaying shape" is what we propose, and it is actuarial precedent.

**Credibility with common or evolving effects.**
- Gerber & Jones (1975), Sundt (1981, 1983), Jewell (1975): recursive formulas with the
  structural parameters taken as known; no estimation found. Kremer (1983), *A remark on
  parameter-estimation of autoregressive credibility-models*, Blätter DGVFM: the only
  estimation paper found in this line; not read.
- Bühlmann & Gisler (2005): ch. 9 evolutionary models and the Kalman filter, ch. 10
  multidimensional evolutionary models (from memory); structural parameters treated as known
  there as far as recalled; not checked.
- Wen, Wu & Zhou (2009), IME 44: common effect across risks, structural parameters by
  moment estimators (from memory; not checked). Permanent effect, so no lag structure.
- Mehra (1975, *Credibility theory and the Kalman filter*), De Jong & Zehnwirth (1983),
  Zehnwirth (1985): the Kalman filter is the best *linear* predictor without normality.
  Shumway & Stoffer (1982), *An approach to time series smoothing and forecasting using the
  EM algorithm*, J. Time Ser. Anal. 3(4), 253–264: EM with Kalman smoothing, missing
  observations. Used: with Gaussian working likelihood these give Gaussian quasi-ML: a
  consistent, hyperparameter-free fit (for the app), not a moment-unbiased one. MARSS (R)
  documents the EM.

**Identification (our model; worked out here from the table, no source has this exact model).**
Write `Σ_h(i, j)` for the covariance of cards `i, j` at months `t, t + h`.
1. *Lag ≥ 1, `i ≠ j`:* `Σ_h(i, j) = λᵢλⱼΓ_{t,t+h}`. No `C`, no `s²/w`, no `τ²`, no `Gᵢ`.
2. *Lag ≥ 1, `i = j`:* `λᵢ²Γ_{t,t+h} + τ² + Gᵢ(h)`.
3. *Lag 0:* `λᵢλⱼΓₜₜ + Cᵢⱼ + δᵢⱼ(sᵢ²/wᵢₜ + τ² + Gᵢ(0))`.
- **Q: do lagged covariances identify `λ` and `Γ` once `C` is month-independent?** Yes, up to
  the scale below, under conditions: (a) AR(1): `Σ₂/Σ₁ = φ` for any pair with `λᵢλⱼ ≠ 0`,
  then `γλᵢλⱼ = Σ₁(i, j)/φ` (needs `φ ≠ 0`), then `Cᵢⱼ = Σ₀(i, j) − γλᵢλⱼ`. (b) Individual
  loadings need **three** cards with non-zero loadings (`λᵢ² = Σ(i,j)Σ(i,k)/Σ(j,k)`,
  Anderson–Rubin); with two cards only `λ₁λ₂` is identified from cross-moments and `λᵢ²` must
  come from (2), which `τ²` and `Gᵢ` confound. (c) With a stationary `Γ` (`Γₜₜ = γ`), `C` and
  `γλλᵀ` are confounded at lag 0 *only*; a block `Γ` with different regime variances
  separates them at lag 0 as well.
- **But the predictor does not need the split.** `K` uses lag 0 only through
  `C + γλλᵀ` (plus the diagonal noise), and `ℓ`, `v` use only lags `≥ 1` (past × future
  months). So with a stationary `Γ` the BLUP depends on `(C + γλλᵀ, (λλᵀΓ(h))_{h ≥ 1}, s², τ²)`;
  the confounding is harmless. The factor structure matters for *extrapolation*: the
  12-month target needs `Γ(h)` at lags longer than any pair of months observed together, so a
  parametric `Γ` (AR(1), block) is required there, and the rank-one form `λλᵀ` reduces noise.
- **Scale shared between `λ` and `γ`:** `(cλ, Γ/c²)` gives the same table, and `λ ↦ −λ` too.
  Sources fix `Var f = 1` (factor analysis), `ΛᵀΛ/N = I` (PCA), or one loading `= 1` /
  lower-triangular (Bai & Wang). Recommendation: **exposure-weighted mean loading `= 1`**
  (`Σᵢ wᵢλᵢ = Σᵢ wᵢ`), so `γ` is the portfolio's factor variance, equal loadings is
  `λ = 1`, and `λᵢ` reads as "card `i` moves `λᵢ` times the portfolio". Statement to prove:
  `Factor.obsCov`, `K`, `ell`, `var` and hence `Core.blup` are invariant under
  `(λ, Γ) ↦ (cλ, c⁻²Γ)`, `c ≠ 0` (trivial; it makes the normalisation a presentation choice).
- **`φ` against a per-card AR(1):** separable. Cross-card lagged moments (1) contain the common
  factor only; a per-card `Gᵢ` shows up only on the diagonal (2). So "common factor or only
  per-card dynamics" is the question "are the lagged cross-moments zero?", testable with two
  cards. Both together: `Gᵢ(h) = Σ_h(i, i) − τ² − λᵢ²Γ(h)`, with `λᵢ²Γ(h)` from three cards;
  with `Gᵢ` AR(1) at `ψᵢ`, `τ²` is the long-lag limit of (2) (needs `φ, ψᵢ < 1` and many
  lags; weak in practice). `τ²` itself is `Γ` with `φ = 1` restricted to the diagonal.
- **How many months and cards:** cards: `J ≥ 2` for the common/per-card test, `J ≥ 3` for
  individual loadings; more cards do not make the factor path consistent (fixed `J`), only
  the parameters sharper. Months: AR(1) by lag ratios has the usual small-sample bias
  `E φ̂ − φ ≈ −(1 + 3φ)/T` (Kendall/Marriott–Pope, from memory, for a demeaned series), so
  `T = 60`, `φ = 0.9`: about `−0.06`, and sd about `√((1 − φ²)/T) ≈ 0.06`; with an estimated
  monthly season (12 means) a 5-year window is the practical minimum, and a pandemic break
  (block `Γ`) spends one regime's months on its own variance. This is the student's
  simulation question; the app world can answer it.

**Estimating φ in short series (app, 2026-11-21).** Web search (abstracts); nothing read in full.
- Andrews (1993), *Exactly median-unbiased estimation of first order autoregressive/unit root
  models*, Econometrica 61(1), 139–165: median-unbiased AR(1) by inverting the median of the LS
  estimator, by simulation, under i.i.d. normal errors. Sørbye, Nicolau & Rue (2022), Stat.
  Inference Stoch. Process. (arXiv 2010.05870): model-based bias correction for AR(1)/AR(2)
  with 10–50 points. Krone, Albers & Timmerman (2017, PMC5227053): short-series AR(1) estimators
  compared; exact ML usually best. Not used yet: both corrections need a distribution (optional
  layer) and simulation in every fit.
- Used: Gaussian quasi-likelihood (Kalman filter) for an AR(1) observed with noise, as an
  estimating equation (consistent for second-moment parameters under any distribution): the
  app's φ̂ from an external index (`phiIndex`), better than lag-ratio moments when the index is
  noisy (the noise dilutes the low-lag autocorrelations).
- Nonnegative MINQUE: Hartung (1981), *Nonnegative minimum biased invariant estimation in
  variance component models*, Ann. Statist. 9(2), 278–292 (minimum over a cone of PSD forms;
  minimum-norm among minimum-bias); Pukelsheim (1981, Math. Operationsforsch. Statist.): the
  minimum-bias requirement is a projection in parameter space; LaMotte (1973) and Pukelsheim
  (1981, Ann. Statist.): unbiased nonnegative estimators do not exist in general. Used: the
  app's `constrainPSD`, the projection of the unbiased MINQUE onto {γλλᵀ ⪰ 0, C ⪰ 0, s² ≥ 0} in
  the MINQUE metric (matrix cones instead of one sign per component). Its error bound is the
  standard obtuse-angle property of the projection onto a closed convex set (Mathlib's
  `norm_eq_iInf_iff_real_inner_le_zero` in an inner product space); `ConeProjection.lean` states
  it in the matrix metric `vᵀHv` with `H ⪰ 0` and proves it directly.

**Public travel demand signals (Step 3b)**, adding to §10e: Tillväxtverket/SCB accommodation
statistics (`NV1701`, PxWeb), monthly guest nights since 1978 by type and guest residence,
preliminary figures revised until the annual release, "read with caution" from March 2020.
It measures travel *into and within* Sweden, so for outbound travel insurance Swedavia's
international passengers (§10e) remain the closer signal. Eurostat `tour_occ_nim` and card
spending abroad (Riksbank/SCB) not verified.

**Recommended estimation plan (Step 5 of `notes/card-data.md`).**
*Unbiased (Lean, via `Expectation.UnbiasedCov` and `integral_quad_of_cov`):*
1. **Lagged cross-moments of year-on-year differences.** For `i ≠ j`, `h ≥ 1`, cells in the
   overlap `obs i ∩ (obs j − h)`: `Δᵢₜ = Xᵢₜ − Xᵢ,ₜ₋₁₂` removes the card mean and any
   calendar-month season exactly; `E[ΔᵢₜΔⱼ,ₜ₊ₕ] = λᵢλⱼ(2Γ(h) − Γ(h−12) − Γ(h+12))` plus `C`
   terms only at `h = 12` (months coincide); no `τ²`, `s²/w` or `Gᵢ`. Unbiased for that combination for *every* `β`. Needs the
   generalisation of `Ecov` from one mean `μ` to means `Dβ` (an estimator is unbiased for all
   `β` iff its quadratic form annihilates `D`): a small `Expectation` lemma, then each
   estimator is one `UnbiasedCov` proof.
2. **Given `φ` (or a block shape), Henderson III / MINQUE in the linear parameters**
   `A = γλλᵀ` (relaxed to any symmetric `A`), `C`, `s²`, `τ²`: the table is
   `Σ Aᵢⱼ(Eᵢⱼ ⊗ R_φ) + Σ Cᵢⱼ(Eᵢⱼ ⊗ I) + diag(s²/w) + τ²(I ⊗ 11ᵀ)`. Generalizes
   `Shock.CHat`/`s2Hat`/`tauHat` (the case `A = 0`).
3. **Shock estimators under the factor model** (statements to prove, expected findings):
   `E Shock.crossHat = Cᵢⱼ + λᵢλⱼ·Σₜ dₜ-weighted Γ terms` (within-card demeaning removes only
   part of a persistent factor), so `Shock.CHat` is biased for `C` *and* for `C + γλλᵀ`
   whenever `φ > 0`; and `Shock.tauHat` picks up `(λᵢ − λ̄)²`-weighted factor variance unless
   loadings are equal. Exact bias terms = "what the shock fit costs when a factor is present".
*Only consistent (app):*
4. `φ̂` (ratio of pooled lag-2 and lag-1 cross-moments, or profile over `φ` of the MoM fit of
   2), then `λ̂` from the leading eigenvector of `Â`, normalised to mean loading `1`;
   truncation of non-PSD `Â`, `Ĉ` (Swamy) or damping (`OffDiagonal`).
5. Gaussian quasi-ML by Kalman filter + EM (Shumway & Stoffer; Bańbura & Modugno for missing
   cells), started from 4: consistent without normality, no hyperparameters; sandwich, not
   Gaussian, standard errors. Also gives the Kalman form of the predictor (§10c).
6. Feasible GLS for the season `β̂` with `K̂` (Step 1), as before.
*Identification statements (prove or refute in Lean):*
- (I1) Scale invariance: `(λ, Γ) ↦ (cλ, c⁻²Γ)` leaves `obsCov` and `Core.blup` unchanged.
- (I2) Lag-0 sufficiency: with `Γₜₜ` constant, `K`, `ell`, `var` depend on `C` and `γλλᵀ`
  only through `C + γλλᵀ`: two parameter sets with equal sums give the same BLUP and MSE.
- (I3) Separation at lag ≥ 1: for `i ≠ j`, `t ≠ s`, `obsCovG` does not depend on `C`, `s²`,
  `τ²`, `G`; so the common factor and per-card dynamics are distinguishable (two models with
  `λλᵀΓ ≠ λ'λ'ᵀΓ'` off the diagonal give different tables).
- (I4) Rank one from three cards: if `λⱼ, λₖ ≠ 0` then `λᵢ²Γ(h) = Σ_h(i,j)Σ_h(i,k)/Σ_h(j,k)`;
  counterexample for two cards: two parameter sets (trading `λ₁²` against `G₁` or `τ²`) with
  the same table.
- (I5) AR(1) given its cross-moments: `φ ≠ 0` and `λᵢλⱼγ ≠ 0` determine `φ`, `γλᵢλⱼ` and then
  `Cᵢⱼ`; `φ = 0` refutes separability (factor = shock with `C + γλλᵀ`, `obsCov_eq_shock`
  pattern).
- *Status (2026-11-21):* I1–I5 and plan item 1 proved in `Credibility/FactorEstimation.lean`
  (`Model.UnbiasedMean` in `Expectation.lean`); item 3 for `Shock.crossHat` (Finding 26:
  `C + (1 - φ)γλλᵀ` with two months) and the between-cohort spread
  (`Factor.between_factor_unbiased`: `+Σⱼxⱼ(λⱼ - λ̄)²αᵀΓα` with equal weights); item 3 in full
  (2026-11-21: `Factor.CdiagHat_factor_unbiased`, `s2Hat_factor_unbiased`,
  `tauHat_factor_unbiased`); item 2 (2026-11-21: `Model.henderson_unbiased`,
  `Model.minque_unbiased`, `Factor.henderson_factor_unbiased`: unbiased whenever the forms
  annihilate the design and the system is nonsingular; which forms is left to the app; `H` can
  be nonsingular iff the basis tables are independent, `Model.exists_hendersonMat_det_ne_zero_iff`,
  with constant volumes and `Γ₀ = I` as the singular cases, and per-card `Gⱼ = gⱼG₀` as one
  more basis table, `Factor.henderson_factorG_unbiased`; MINQUE: nonsingular iff the `RVₖR` are
  independent, `Model.minque_det_ne_zero_iff` (Rao 1971; Searle, Casella & McCulloch 1992,
  ch. 11, from memory); under card-specific means `τ²` drops out, Finding 27).

### 10h2. Relativities and joint frequency × severity (card-data Steps 4, 6; 2026-11-21)
From memory, not re-checked online.
- Kruskal (1968), *When are Gauss–Markov and least squares estimators identical?*, Ann. Math.
  Stat. 39: GLS = OLS iff the column space of the design is invariant under the covariance.
  Zellner (1962) (§9): SUR with identical regressors is equation-by-equation OLS whatever the
  cross-equation covariance. Used for Finding 32 (`CoreVector.blupW_kronecker`): the Kronecker
  case is the credibility analogue.
- Common factors cancel from within-period contrasts: the interactive-effects literature
  (Pesaran 2006, Bai 2009, §9) removes them by cross-sectional averages only when loadings are
  homogeneous; the difference-in-differences logic. Used for Step 4: the exact remainder `gᵀΓg`
  is the new piece (`Factor.quadTab_eq`).

### 10i. Comparing fits on data (card-data Step 7b, 2026-11-21)
Web search (abstracts and listings); nothing read in full.
- Tashman (2000), *Out-of-sample tests of forecasting accuracy: an analysis and review*,
  IJF 16(4), 437–450: rolling-origin evaluation with recalibration at each origin and several
  test periods is more reliable than one fixed origin. Used: the protocol of Step 7b.
- Diebold & Mariano (1995, JBES; from memory) and Harvey, Leybourne & Newbold (1997, IJF):
  test equal accuracy from the loss differential; for `h`-step forecasts the differentials
  are serially correlated, so a HAC variance with lag `h − 1`, the HLN finite-sample factor
  and `t(T−1)` critical values (statsmodels `diebold_mariano_test`). Harvey, Leybourne &
  Whitehouse (2017, IJF 33(4)): the long-run variance can be negative in small samples at
  multi-step horizons; Coroneo & Iacone's weighted-periodogram version sizes best. Used: paired
  comparison with lag 11 for 12-month targets at monthly origins. Seen in the app (2026-11-21, `dmSize`):
  on loss differentials with the 11-month overlap and mean 0, DM–HLN at 5% rejects in 25% at 25
  origins, 17% at 49, 10% at 97; the weighted periodogram (`m = ⌊n^(1/3)⌋`, `t(2m)`) is no
  better at these sizes. With 12-month targets the effective sample is about `n/12` years, so
  both are shown with their false-alarm rate next to the power (Coroneo & Iacone 2020, JAE,
  from memory: `√n·d̄/σ̂_WPE` against `t(2m)`).
- Bergmeir, Hyndman & Koo (2018), *A note on the validity of cross-validation for evaluating
  autoregressive time series prediction*, CSDA 120, 70–83: K-fold CV is valid for purely
  autoregressive models with uncorrelated errors, fails when errors are correlated
  (misspecification). Used: why not K-fold here (a common factor correlates held-out and
  training months).
- Gneiting (2011), *Making and evaluating point forecasts*, JASA 106 (from memory): squared
  error is consistent for the mean. Used: the score.
- In this repo: leave-one-year-out CV for tuning (`studies/damping-theta.md` S14, too noisy);
  jackknife MSEP of one fit (Jiang, Lahiri & Wan 2002; S19–S23).

### 10j. Bias of weights estimated from the same data (Finding 35, 2026-11-22)
- Hamman et al. (2018), *Bias in meta-analyses using Hedges' d* (abstract only, ECU ScholarShip
  10342/8371; journal not checked): inverse-variance weighting is biased because the
  estimated effect and its weight are correlated; sample-size weights are nearly unbiased.
  Used: the mechanism of Finding 35; exposure weights (BS) play the role of sample-size weights.
- Doncaster et al. (2017), Methods in Ecology and Evolution (Southampton eprint 416153; title not
  checked): weight by an adjusted (pooled)
  variance. Used: the pooled-`σ̂²` remedy, which removes the bias in the app (Finding 35).
- Wang & Fuller (2003), *The MSE of small area predictors constructed with estimated area
  variances*, JASA 98, 716–723 (abstract): EBLUP with each area's own direct variance; MSE term
  for the variance error. Not yet used: their setting has a bias channel only under skew; check
  whether they treat it.
- Benchmarking (§ above: Pfeffermann & Barnard 1991; Wang, Fuller & Qu 2008): balance fixes the
  portfolio level exactly (Finding 35 (b)), not region-level bias.


### 10k. Noise shape from moments (PLAN "Noise shape" step 1, 2026-11-22)
From memory, standard results; not re-read for this step.
- Fisher's k-statistics (Fisher 1929, Proc. LMS 30): unbiased estimators of cumulants from
  products of residuals. Used: `noiseDiagnostics`'s `κ̂ⱼ` is the weighted third-order analogue
  for `X = μ + noise` with variances `σ²/w` and third cumulants `κ/w^q` (exact correction
  `Σₜ cₜ Σₛ (δₜₛ − aₛ)³ wₛ^(−q)`).
- Taylor's power law (Taylor 1961, Nature 189) and the Tweedie variance function `V(μ) = μᵖ`
  (Jørgensen 1997; estimated by profile likelihood in Dunn & Smyth's `tweedie`): log variance
  linear in log mean. Used: the power `p`, but by regression of moments only, no family.
- Sample splitting / cross-fitting (as in Chernozhukov et al. 2018, Econometrics J. 21, double
  ML): estimate the two sides of a product from independent parts of the data. Used: `σ̂²` from
  even years against `μ̂` from odd ones, which removes the same-years bias (the Finding 35 channel,
  §10j) of the naive slope (≈ 2 instead of 0 in the app's skewed world).

### 10l. Recent credibility papers, and higher moments from a variance function (2026-11-22)
Checked to exist; read from abstracts and listings only, not the full texts.
- Morris (2026), *Logistic Credibility with Temporal Decay: Extending Bühlmann–Straub for
  Commercial Lines*, arXiv 2606.08692 (preprint; code at github.com/jakem87/logistic-credibility,
  CAS Schedule P data). The credibility weight is a logistic function of account characteristics
  in place of one `K`, and older years are discounted by an EWMA weight λ. All of it is fitted
  jointly by likelihood, and it nests Bühlmann–Straub. Reports a λ that depends on account size.
  Used 2026-11-24 (`studies/ewma-decay.js`, S43–S45): EWMA of own years is a restricted predictor
  (aggregated data, exact excess `Blup.predMse_aggregate_eq_blup_add`), and the best λ falls with
  `s²/wⱼ` against the AR(1) factor (`Factor.lean`), so a size-dependent λ comes out of the
  second-moment model; the BLUP beats EWMA by pooling the common factor across cohorts.
  A likelihood fit belongs in the distribution layer.
- Wen & Liu (2026), *A new credibility estimation of process variance with applications*,
  ASTIN Bull. 56(3), 1036–1065, doi 10.1017/asb.2026.10094. Gives each risk a credibility
  estimate of its own process variance `σ²(θ)`, with and without a known hypothetical mean, by
  constrained linear projection, for premium principles that use the variance. Not yet used.
  Our §2.8 `ŝ²` and the `Shock.lean` estimators estimate one variance for the whole portfolio;
  shrinking each region's `σ̂ⱼ²` (the Finding 35 remedy between own and pooled `σ̂²`) is their
  setting. It needs fourth moments (see the variance-function item below).
- Zhao & Poudyal (2026), *Robust quadratic credibility*, Ann. Actuar. Sci. 20(2), 302–332 (online
  2025-12-16, doi 10.1017/S1748499525100201, open access). Adds second-order polynomial terms of
  winsorized losses to the credibility premium, extending semi-linear credibility, for heavy
  tails. Not yet used. It needs moments up to order four of the transformed data, so it lies
  outside the second-moment core. Robustness background next to Künsch (1992) and Gisler &
  Reinhard (1993) in §5.
- Higher moments from two parameters (owner's question, 2026-11-22; from memory, standard).
  In a natural exponential family, or an exponential dispersion model with dispersion `φ` and
  weight `w`, the variance function `V(μ)` fixes every cumulant through the recursion
  `κₙ₊₁ = (φ/w) V(μ) dκₙ/dμ` (Jørgensen 1997, *The Theory of Dispersion Models*). Morris (1982),
  *Natural exponential families with quadratic variance functions*, Ann. Stat. 10, finds exactly
  six families with `V = v₀ + v₁μ + v₂μ²`: normal, Poisson, gamma, binomial, negative binomial
  and generalized hyperbolic secant. Their cumulants are polynomials in `μ`, and Morris (1983,
  Ann. Stat. 11) builds the moment theory from them. Tweedie `V = μᵖ` gives `κ₃ = (φ/w)² p μ^(2p−1)`,
  skewness `p √(φ/w) μ^(p/2−1)` (gamma: `2·CV`; Poisson: `1/√μ`), and `κₙ ∝ w^−(n−1)`, the
  `q = 2` scaling of §10k. Conjugate priors make linear credibility exact in these families
  (Jewell 1974; Diaconis & Ylvisaker 1979), and the Poisson–gamma mixture stays in the six
  (negative binomial). The zero-parameter closure is Gaussian (Isserlis): third and fourth
  moments follow from the covariance. Not yet used. Candidate for a cumulant layer (PLAN Pending).
- Variance of a quadratic form beyond normality (2026-11-22, from memory, standard): with cumulant
  tensors `κ₃`, `κ₄` of the centred cells, `Var(xᵀAx) = 2tr(AΣAΣ) + 4μᵀAΣAμ + 4Σ(Aμ)ᵢAⱼₖκ₃ᵢⱼₖ +
  ΣAᵢⱼAₖₗκ₄ᵢⱼₖₗ`. Independent components: Atiqullah (1962, JRSS B 24); Seber & Lee (2003), Thm 1.6.
  Covariance of two quadratic forms (used in `FitStatistics.lean`, 2026-11-24): polarization of the
  variance, `2 tr(ACBC) + 4 (Am)ᵀC(Bm) + κ₃ terms + ΣAᵢⱼBₖₗκ₄ᵢⱼₖₗ`; the normal case is Searle (1971),
  *Linear Models*, ch. 2; no new derivation.
  Gaussian case: Searle (1971) §2.5; Searle, Casella & McCulloch (1992), App. S. MINQUE variance
  with kurtosis: Rao & Kleffe (1988), ch. 5. Products of forms via cumulants: Bao & Ullah
  (https://eml.berkeley.edu/~webfac/bgraham/secnf/Ullah.pdf). Proposed use: `notes/fourth-moments.md`
  (one lemma for G1, G2, G4 and the `κ̂ⱼ` third-moment pieces), awaiting the owner.
- Heavy tails (owner's question, 2026-11-22; from memory, standard). No variance function gives
  them. A natural exponential family has a moment generating function near 0 for every `θ`
  inside its natural range, so its tails are at most exponential and all its moments are finite.
  Lognormal and Pareto are not in the class, and power tails appear only at the boundary (stable
  laws, infinite mean). A steep `V` (Tweedie `p > 2`, inverse Gaussian `p = 3`; exponential
  variance functions, Bar-Lev & Enis 1986) only makes skewness grow fast in `μ`. The actuarial
  route is a compound Poisson cell `S = Σᵢ₌₁ᴺ Yᵢ`, `N ~ Poisson(λw)`. Then `κₙ(S) = λw E[Yⁿ]`
  (collective risk model; Klugman, Panjer & Willmot, *Loss Models*), so the cell mean keeps the
  `κₙ ∝ w^−(n−1)` scaling. A gamma severity gives back Tweedie with `1 < p < 2`. Two-parameter
  heavy-tailed severities with a moment recursion:
  - Lomax (Pareto II): `E[Yⁿ⁺¹]/E[Yⁿ] = θ(n+1)/(α−n−1)`, finite only for `n < α`;
  - lognormal: `E[Yⁿ⁺¹]/E[Yⁿ] = exp(m + (2n+1)σ²/2)`, all moments finite, subexponential.
  The fourth-moment tools need `α > 4`. For `α ≤ 4` the variance of `ŝ²` is truly infinite, which
  is why winsorizing (Zhao & Poudyal 2026) exists. The tail index is normally estimated from
  individual claims (Hill 1975, Ann. Stat. 3). Out of scope for now (owner, 2026-11-22): only cell
  totals are fitted. Not yet used.

### 10m. Does normality hold asymptotically? (owner's question, 2026-11-24)
- **Noise: yes, with volume.** A cell is a sum of claims, and cumulants of independent pieces add.
  So with `n ∝ w` claims the cell's skewness is `E Y³/(√n (E Y²)^(3/2))` (falls like `1/√n`)
  and its excess kurtosis is `E Y⁴/(n (E Y²)²)` (falls like `1/n`), given finite third and
  fourth claim moments. This is the cumulant form of the central limit theorem; Edgeworth
  expansions refine it (Hall 1992, *The Bootstrap and Edgeworth Expansion*; collective risk model:
  Klugman, Panjer & Willmot, *Loss Models*, as in §10l). Exceptions: claim tails with an infinite
  fourth moment (Lomax `α ≤ 4`); skewness converges only like `1/√claims`; a shared year shock is one
  draw per year, not a sum, and keeps its shape.
- **Levels: no.** The levels' excess kurtosis `γL = κL/τ⁴` belongs to the population of regions.
  Neither volume nor years move it. In law (a) (`Cumulants.bsPrice_of_balanced_cumulants`) its term
  `γL z²/J` has the same order `1/J` as the normal part `2/(J − 1)`, so it never becomes negligible
  relative to it. The noise term `γN z²/(JT)` is smaller by `1/T` even at fixed `γN`.
- Lahiri & Rao (1995), "Robust estimation of mean squared error of small area estimators",
  *JASA* 90(430), 758–766 (doi 10.1080/01621459.1995.10476570): the Prasad–Rao MSE estimator of
  the EBLUP (Fay–Herriot model) is robust to non-normal area (random) effects; the sampling errors
  are kept normal. Checked from abstracts only (the exact moment conditions, finite eighth moments
  as recalled, are not verified). The same split as here: normality is safe for the noise,
  not for the levels. Its MSE estimator is second-order; law (a) is first order but exact in
  `γL`, so the level kurtosis shows up there where Lahiri–Rao's robustness says it cancels at their
  order. Worth a closer read before claiming more.
- Used: the app's world switch "Noise shape shrinks with volume" (`params.shrink`, gamma shape
  `k·w/500`); `Engine.noiseShape` recovers the fall (J = 8, T = 10, 600 draws: skew 1.16, 0.42,
  0.14 and `γ̂N` 4.0, 0.40, 0.08 at volume 500, 5 000, 50 000).
