# Paper changelog

What changed in the paper (*Credibility from second moments: a guide*), newest
first. The title page of every PDF says "version of <date>, commit <hash>": if
your copy is older than the top entry here, the
[latest PDF](https://mikaelandblom-coder.github.io/credible-lean/paper.pdf)
has the changes listed above your date. Exact differences:
`git log -p -- paper/paper.tex`.

One line per change a reader would notice (a new or rewritten paragraph, a
corrected claim, a new section); renumbered handbook citations and typo fixes
are not listed.

## 2026-11-28
- §1.1, §5, §6: what is proved is stated exactly: "every result the paper calls proved"; for the app's fit,
  `K̂ ≻ 0`, the blend and the pooled `ρ̂` (true `σⱼ`) are proved, the credibility-weighted variances are not; the
  moment layer's unbiasedness covers the thesis's estimators, not ratios of them (second external review).
- §5 new paragraph "On real data" (S85, S86): Hachemeister's states and Klugman's workers' compensation classes;
  `ρ̂` is a common time effect (≈ 0 once removed), the gain over BS comes from per-cohort variances, and a
  loss-free cohort is priced at 0 without a guard.
- §5 Estimating the parameters: corrBS's `ρ̂` is biased up by the low level of the credibility-weighted variances, which
  leaves `K̂`'s covariances alone (Finding 48); the unbiased `Wⱼ` exists but worsens the rates (Finding 47).
- §5 Estimating the parameters: the cross-fitted balance level works for any volumes, also volumes varying by year (S82);
  the study worlds now vary volumes by year (S84).
- §3.2 The credibility factor: an estimated `ẑ` from other data is safe to clip iff the best `z` is in `[0, 1]`, but that is
  unknown and the costs are lopsided, so don't clip by default; a held-out clip-or-keep choice is open (§11, S83).
- §3 What ignoring correlation costs: with equal noise covariances the fitted Bühlmann–Straub costs at most
  `vⱼ/(vⱼ − c)` and under-weights own experience, for any number of cohorts (Finding 50).
- §3 What ignoring correlation costs: a fitted Bühlmann–Straub also lowers `τ²` (Finding 49); for two
  cohorts the cost stays within `1/(1 − ρ²)`, from three cohorts it can exceed the true-`τ²` worst case
  (63.5% against 56% at `r = 0.5`).
- §8 Trend lines: correlated cohorts in regression credibility are credited to Poon (2013,
  ch. 5), who gives the predictor with the collective line known; new here is only the
  estimated collective line and the matrix blend.
- §9 Small-area estimation: the common shift is best for any BLUP (Wang, Fuller and Qu) and
  any posterior mean (Datta et al. 2011); the claim for the blend is now "best when it is the
  BLUP" (Finding 18's condition), not "only for independent cohorts".

## 2026-11-27
- Figures for the main study results (from the external review): Figure 1 in §3.4,
  the fitted BLUP against the fitted blend with and without the balance shift (S72,
  S74); Figure 2 in §4, the cost of balancing by noise-variance spread (S75); Figure 3
  in §5, REML and the thesis fit against the pools on crossed tables (S71). Drawn
  from the study outputs by `scripts/paper_figures.py`.
- §8.2 Groups: the held-out choice of groups or none in simulation (S77: least regret,
  at most 4 points, though its picks barely follow the shared share); the open item
  "groups or not" removed from §10.
- §5 choice table: crossed groupings now start with REML on the cell means (S70, S71);
  a new row for groups sharing a level (one GLS pass; groups or none on held-out years).
- §10 Open directions: the group fit marked done, its open part now "groups or not, by
  held-out score"; small crossed tables rewritten around REML as the app's default and
  Finding 44's 2×2 warning.
- §3.4 Beyond the blend: the fitted BLUP beats the fitted blend broadly when rates are
  not shifted afterwards (S72, S74); its larger weight price (Finding 45) is mostly
  offset by the cross term; its balanced losses are the balance step's. Choice table:
  "ρ̂ ≳ 0.6 → BLUP" replaced by "rates not shifted afterwards → BLUP".
- §4 Balance: balancing as a choice of portfolio level, with its exact cost
  (Finding 46); the app's switch now balances only when that cost is negative (S76).
  Conclusion updated to match.
- Title page: version line (date and commit) and a link to this changelog.
- §1 "Four documents": the paper described as the main document that grew out of
  the 2023 thesis (not "the up-to-date thesis").
- §8.2 Groups and shared levels: fitting φτ² by one GLS pass on the pair table;
  the app's "BLUP groups" fit.
- §8.3 Choosing the cohorts: the winner's curse of merging cohorts that look
  close, exact under normal noise (Finding 43); choose on a held-out year.
- §10 Open directions: crossed levels, the default fit and trend lines marked
  done; winner's curse first; small crossed tables and the mix's gain added as
  open fits.
- Catch-up: forecasting and fitting the trend lines, what the blend leaves out
  and the held-out mix (part way from blend to BLUP), crossed pool weights and
  the default fit.

## 2026-11-26
- §3.4: the BLUP as GLS mean plus predicted residuals; the blend as one row.
- §8: crossed levels, best pool of pair estimators (GLS on the pair table).

## 2026-11-25
- Review: new §3.4 "Beyond the blend" (BLUP of any target, restricted
  predictors, recency weighting), new §7 "Beyond second moments", §9 rewritten,
  new §11 Conclusion; Appendix A covers Findings 6–42.

## 2026-11-22 (release v3.0.0)
- Plug-in error and unbiasedness, Finding 35 and balance, tapering; the general
  target, season, factor model and its estimation, valid tables, choosing
  between fits on data; known trend and serial correlation.

## 2026-11-20
- Regrouped into ten sections with run-in paragraphs; the matrix blend added.

## 2026-11-17
- First complete draft (all sections and appendices).

## 2026-11-16
- First draft of §1–6 and Appendices A and C.
