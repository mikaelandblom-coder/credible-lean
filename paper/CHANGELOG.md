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

## 2026-11-27
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
