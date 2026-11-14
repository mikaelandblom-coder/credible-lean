# Related work for G1/G2 (common correlation, damping θ)

Collected 2026-11-14 from abstracts and summaries (full texts not read yet). Links in the chat log
of that day; search the titles.

## 1. Our `b` is the global minimum-variance portfolio (GMV)
`b = K⁻¹1 / 1ᵀK⁻¹1` is the GMV portfolio with covariance `K`. Estimating it from a sample
covariance is a large literature, and its central lesson matches findings 11–13: **shrink for
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
  Frobenius-optimal (our stand-in loss, which finding 12 shows is the wrong one for rates).

Difference to note: their target is *out-of-sample* variance (new data); our error compares the
rates with the levels of the *same* history, so the in-sample effect of finding 13 is ours.
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
  restrict Σ to few parameters (our BS-vs-full result at ρ = 0, finding 6).

## 3. Credibility with common effects (our correlation model)
- Yeo & Valdez (2006), *Claim dependence with common effects in credibility models*, IME 38(3);
  Wen, Wu & Zhou (2009), IME 44(1) (thesis ref `wen2`): a common effect across risks.
- Ebrahimzadeh, Ibrahim, Jemain & Kilicman (2012), *Unbiased estimation of structural parameters
  in credibility models with dependence induced by common effects*, Bull. Malays. Math. Sci. Soc.
  35(4): unbiased estimators incl. Bühlmann–Straub weights. Compare with item 2 of the
  CommonCorrelation plan (unbiased `ρσ²`); likely the closest prior art.
- Yang & Wang (2024), Comm. Stat. 53(8): REML and linear-Bayes estimators of structural
  parameters in the Bühlmann model with correlated risks.
