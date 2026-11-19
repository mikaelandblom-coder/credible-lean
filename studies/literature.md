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
Searched by web; casact.org is not reachable from the **lean** environment, so only abstracts
and tables of contents were read. Standard results below are from memory and marked so.
- Jewell (1973), *Multi-dimensional credibility*, ORC 73-7, UC Berkeley (10th ASTIN Colloquium;
  full text not found). Matrix credibility factor; the number of structural parameters grows
  with the dimension. Bühlmann (1974), *A comparison of three credibility formulae using
  multidimensional techniques*, ASTIN Bull. 7(3), 203–207: Jewell's framework applied to total
  losses and claim counts (frequency × severity). Used: the vector blend itself.
- Bühlmann & Gisler (2005), *A Course in Credibility Theory and its Applications*, Springer:
  ch. 7 multidimensional credibility (§7.3 multidimensional Bühlmann–Straub, p. 177), ch. 8
  regression (§8.3.2 Hachemeister's general case, p. 205). From memory: the credibility
  estimator is `Zⱼ X̄ⱼ + (I - Zⱼ) μ̂` with `Zⱼ = T (T + Sⱼ)⁻¹` and the homogeneous `μ̂` the
  `Zⱼ`-weighted mean; cohorts are *independent*, so `K` is block diagonal. Used: the target
  `CoreVector` must reproduce this when `K` is block diagonal (next step).
- Hachemeister (1975) and Bühlmann & Gisler (1997), see §7: the regression case is the
  `P = 2` vector blend with design-dependent `K`.
- Frequency–severity with dependent risk profiles: Cheung, Ni, Oh & Woo (2021), IME 100,
  274–295 (bivariate prior; Bayesian); Englund et al. (2008; authors from memory),
  ASTIN Bull. 38(1), multivariate latent risk, a multivariate Bühlmann–Straub; Q-credibility
  (ARCH 2025 abstract, Tang): factors for frequency and severity chosen to minimise the MSE of
  the *pure premium*. Used: the target `aᵀμⱼ` (theorem `bestZ_optimal_dotProduct`) covers the
  first-order premium; the Q-credibility idea (optimise for the product) is the next question.
- New here: the cohorts are correlated, `K` is a full matrix over cohorts × components, and
  the portfolio estimate is the matrix GLS `μ̂ = (UᵀK⁻¹U)⁻¹UᵀK⁻¹x`; the best `Zⱼ` is
  `(Lⱼⱼ - EⱼᵀLW)(Kⱼⱼ - (UᵀK⁻¹U)⁻¹)⁻¹`, the matrix form of eq. (26).
- New here (if it holds): correlated cohorts in both; component-specific `ρ` (winters move
  frequency, not severity); relativities are free of a common trend.
