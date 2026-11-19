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
- Prasad & Rao (1990), Das, Jiang & Rao (2004): MSEP ≈ g₁ + g₂ + g₃ with g₃ from the covariance of
  the variance-parameter estimates; second-order unbiased MSEP estimator g₁(θ̂) + g₂(θ̂) + 2g₃(θ̂).
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
  (GLS `μ̂`), where `moments_bestZ_of_blockDiag` shows the same `Z`. Still to read: the
  homogeneous estimator (collective `(ΣAᵢ)⁻¹ΣAᵢBᵢ`, presumably Theorem 7.9). Bühlmann,
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
Used: the interpretation (thesis model = SUR error structure inside a credibility model) and
the warning on full `K̂`. New here: the combination with random levels and the blend.
