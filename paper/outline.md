# The paper: outline (draft, 2026-11-16)

Working title: *Credibility from second moments: a guide* (owner to confirm;
see the end).

The paper is the up-to-date version of the thesis and the first complete
source for a reader who wants to understand or cite the work. It explains
the concepts; it does not carry the formulas or the proofs.

## Who holds what

| Content | Home | The paper does |
|---|---|---|
| Statement and proof | Lean + blueprint | gives the Lean name |
| Formula | handbook | cites the handbook number |
| Explanation, intuition, when to use, what can go wrong | **paper** | — |
| Demonstration | app | names the step or switch to try |
| Dated log of gaps and new results | `FINDINGS.md` | explains the finding where it belongs |

Rules that keep this cheap to maintain:
- A formula is displayed in the paper only when the explanation cannot be
  read without it (the model, the blend, the credibility factor). Otherwise:
  "Handbook (n)".
- Sections are concepts, not results. A new result is normally a subsection
  in an existing section.
- No proofs. A proof idea in one or two sentences is welcome when it is the
  explanation.
- Every section ends with a **See** line: handbook numbers, Lean names, app
  step, and the working note it came from.
- Numbers from simulations cite the study script in `studies/` that
  produced them.

## Section template

1. **In one sentence.** What the concept is.
2. **The idea**, in numbered subsections, one per topic (a short
   unheaded intro before the first is fine). Plain words, a small example
   where it helps. A new result is normally a new subsection.
3. **What to watch out for** (a subsection): when it applies, what can go wrong.
4. **See.** Handbook (n) · `Lean.name` · app: step · note.

## Sections

Status: `—` not started, `src` source material exists to absorb, `draft`,
`done`. (2026-11-16: `paper/paper.tex` has every section as a heading with a
"not yet written" note; §1–6 drafted. Later the same day: §0, A and C
drafted, then §7–9, then §10–11. 2026-11-17: §12–14 and B drafted, and
paragraphs for Findings 18–20 in §5–6: the first draft is complete.)

| # | Section | Covers | Source material | Status |
|---|---|---|---|---|
| 0 | How to read this | the four documents and what each is for; machine-checked means what | this file, README "How it was made" | draft |
| 1 | What credibility is | blending own experience with the portfolio; what `z` means; best blend | thesis §2.1, handbook 1 | draft |
| 2 | The model | error terms instead of risk parameters; correlation across cohorts within a period; distribution-free; translation to Bühlmann–Straub notation | thesis §2.3, handbook 0 | draft |
| 3 | From data to `K` | the recipe: build `K`, check it is positive definite, read off everything; why positive definite and not semidefinite; why two cohorts | Findings 1, 2 | draft |
| 4 | The weights | inverse-variance within a cohort; GLS across cohorts; the link to the minimum-variance portfolio | thesis §2.5, `studies/literature.md` §1 | draft |
| 5 | The credibility factor | the proposed `z`; how correlation moves it; `z > 1` and the sign flip; the blend against the BLUP | thesis §2.5, §2.7, Findings 3, 17, 18 | draft |
| 6 | Special cases | Bühlmann–Straub; two cohorts; equal covariances; weights from credibility factors; what ignoring or damping correlation costs | Findings 4, 5, 19, 20 | draft |
| 7 | Balance | what it is and why practitioners want it; when it holds for free; the cost of forcing it; how to balance if you must | Findings 10, 15, 16, study findings S27–S29 | draft |
| 8 | Estimating the parameters | the unbiased estimators and what they need; plug-in `K̂` and damping; a fit with no tuning; the error of a fitted model | thesis §2.8, Finding 7, `studies/damping-theta.md`, `studies/literature.md` §2, §4 | draft |
| 9 | Why the moments are real | given numbers versus actual covariances; true MSE; the assumptions are consistent exactly when `ρ ⪰ 0` | Findings 11, 12 | draft |
| 10 | Cohorts observed over different periods | unequal lengths; the per-pair count | `notes/unequal-lengths.md`, Findings 8–10, 12 | draft |
| 11 | Groups and shared levels | a shared level drops out; several groups; what the estimators see; towards hierarchical credibility | Finding 13, handbook §6, `studies/literature.md` §3 | draft |
| 12 | Choosing the cohorts | when merging pays off; equal credibility is not grouping; optimal cohorts are intervals; when they are not | `notes/merging-cohorts.md`, `notes/kmeans-bridge.md`, Findings 6, 14 | draft |
| 13 | Open directions | crossed levels; time trends; the optional distribution layer | `notes/crossed-2x2.md`, `notes/roadmap.md`, `studies/literature.md` §5 | draft |
| 14 | Related work | credibility with common effects, small-area estimation, covariance shrinkage: what is used from where | `studies/literature.md` | draft |
| A | Changes from the thesis | corrections and sharpenings, by thesis section; concordance thesis equation ↔ handbook number ↔ Lean name | `FINDINGS.md` | draft |
| B | Concept index | alphabetical: term → one-line meaning → section | — | draft |
| C | Notation | symbols, with the Bühlmann–Straub translation | handbook 0 | draft |

## Absorbing the notes

When a section is drafted from a working note (`notes/*.md`,
`studies/damping-theta.md`), the note gets a first line "Absorbed into
paper §n on <date>; kept as the working record" and is not updated again.
`FINDINGS.md` stays the dated log.

## Pending
(Results, findings or changed statements since the last paper update that
may need a paragraph.)
- Finding 23 (2026-11-19, modelling remark): a common period shock does not shrink with
  volume; eq. (16) with fixed `ρ` makes it shrink. One sentence in the model section and in
  §13 (Time) next to "period shocks are already in".
- Matrix blend (2026-11-19, `CoreVector.lean`): vector levels, credibility matrix, matrix GLS
  with correlated cohorts (Jewell 1973; Bühlmann–Gisler ch. 7 has independent cohorts, and is
  recovered: `Credibility.CoreVector.moments_bestZ_buhlmannGisler`). Hachemeister with correlated
  cohorts proved (`Credibility.CoreVector.hachemeister_bestZ`): one paragraph in §13 now
  possible (trend lines per cohort; a year shock correlates the cohorts' lines).
  Frequency × severity (Finding 22): vector credibility beats separate credibility as a best
  predictor (`Credibility.CoreVector.trace_linMse_blupW_le_separate`), not as a blend; one
  paragraph with the counterexample's moral (restricted predictors are not ordered).
  With independent cohorts the matrix blend *is* the best predictor
  (`Credibility.CoreVector.blendW_eq_blupW_of_blockDiag`), and without cross-component
  covariance the vector best predictor is the separate ones
  (`Credibility.CoreVector.blupW_eq_sepW_of_componentBlockDiag`): one sentence each, they
  bracket Finding 22. Balance of the matrix blend (`Credibility.CoreVector.vecBalanced_iff`;
  Bühlmann–Gisler balanced for the volumes, `vecBalanced_buhlmannGisler`): one sentence in
  the balance section.
- Known common trend (2026-11-19, `Trend.lean`, Finding 21): "trend first, then blend; the
  weights do not move"; relativities trend-free only for the true `g`. One paragraph in §13
  (time trends), citing handbook `res:trend`.
- Plug-in `K̂` repair (2026-11-17): damping is now a corollary of tapering by any
  correlation matrix (Schur product theorem; `Credibility.posDef_hadamard_of_corr`,
  `Credibility.distTaper_posSemidef`). One sentence where the paper explains damping,
  citing Furrer–Genton–Nychka (2006) for tapering.
- Appendix C: Bühlmann–Gisler notation checked against pp. 89–90 (Theorem 4.4)
  and 145–147 (owner's photos, 2026-11-17): all symbols match, after fixing the
  collective premium `μ_0` (was `m`; also in §3 and the handbook), `τ²` (was `a`),
  and the double hats of the homogeneous estimators. Only `κ` is unseen (the
  book writes `σ²/τ²` inside `α_i`); low priority.
- §11, §14: Bühlmann–Gisler ch. 6 is hierarchical credibility (checked,
  §6.2 p. 145: levels Ψ_g, Φ_h, Θ_i, X_ij; Bühlmann–Straub its two-level case;
  estimator bottom-up then top-down). The other references were checked
  by web search (2026-11-17, details in `studies/literature.md`): bibliographic
  details and abstracts only, not full texts.
- §10–11: when the app gets its "Unequal lengths" and "Group levels"
  switches (`studies/PLAN.md` step 4), replace "(soon)" in the See lines
  with the step, and add study numbers if a fit is simulated.
- §14: the "new here" claims stand until a precedent turns up.
- §12: when the app gets a step for choosing cohorts (`studies/PLAN.md`, G5),
  add it to the See line. (The BLUP fit is in: §5 and §13 cite it, 2026-11-17.)
- B: regenerate when sections change; the list is written by hand.
- Appendix A: the concordance lists the Lean names at drafting time
  (2026-11-16); add new thesis-facing theorems there as they come.

## Order of work

1. Sections 1–6 (the thesis core), then A and C: this already replaces the
   thesis as the first thing to read.
2. Sections 7–9 (balance, estimation, moments): the parts practitioners ask
   about.
3. Sections 10–14 from the notes; B last, regenerated as sections land.
4. CI: build the paper as a searchable web page and a PDF next to the
   handbook; a `paper_check.py` like `handbook_check.py` (every Lean name
   and handbook number cited must exist and be proved). *Done 2026-11-16:*
   `/paper/` (one page, search box, `paper/search.js`) and `/paper.pdf`;
   cite with `\lean{Name}`, `\hb{res:label}{n}`, `\hbsec{sec:label}{n}`,
   `\finding{n}`, `\file{path}`, `\app{step}`. The handbook number is
   written next to its label; `paper_check.py --fix` rewrites stale numbers
   after the handbook is reordered.
5. A coverage report: proved results cited by none of handbook, paper, app,
   with an explicit "not needed" list.
6. When sections 1–9 are done: point README and `CITATION.cff` at the paper
   as the primary reference, and use it as the arXiv preprint ("Publication plan" below).

## Publication plan (moved from the README, 2026-11-17)

1. **Citable repo** (done, v2.0.0): `CITATION.cff`; Zenodo archives each
   tagged release (concept DOI 10.5281/zenodo.24054631); GitHub topics
   `credibility-theory`, `actuarial-science`, `lean4`, `formalization`.
2. **Preprint on arXiv**: this paper (q-fin.RM, cross-list stat.AP or
   math.ST), stating that every result is machine-checked and linking the
   repo. arXiv is indexed by Google Scholar; GitHub is not.
3. **Two audiences.** The credibility results to an actuarial journal
   (Scandinavian Actuarial Journal, ASTIN Bulletin, European Actuarial
   Journal, Variance). The formalization itself to CPP/ITP or *Annals of
   Formalized Mathematics*.
4. **General lemmas** stay in the repo: Mathlib asks for hand-written code
   and comments in contributors' own words (see `CLAUDE.md`).

## Decided (owner, 2026-11-16)

- **Source format.** LaTeX in `paper/paper.tex`, built by CI into a web page
  with search (plasTeX) and a PDF, next to the handbook.
- **Voice.** Looser than the thesis: plain words, "you", short sentences,
  examples before generality.
- **Title.** General enough to survive new theory (not tied to correlated
  cohorts or to the thesis).

## Open choices for the owner

- **Title**, among for example:
  - *Credibility from second moments: a guide*: names what stays fixed
    however the theory grows (only means and covariances are assumed).
  - *Credibility theory, machine-checked: a guide*: leads with the Lean
    proofs.
  - *A unified credibility framework: concepts and practice*: matches the
    handbook's "one unified framework".
