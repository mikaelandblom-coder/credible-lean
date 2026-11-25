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
- Sections are concepts, not results. A new result is normally a
  paragraph in an existing subsection.
- No proofs. A proof idea in one or two sentences is welcome when it is the
  explanation.
- Every topic ends with a **See** line: handbook numbers, Lean names, app
  step, and the working note it came from.
- Numbers from simulations cite the study script in `studies/` that
  produced them.

## Structure (owner, 2026-11-20)

Laid out like a paper: nine sections, a few subsections each, and the topics
inside as run-in paragraphs (`\paragraph{…}`), not headings of their own. A new
result is normally a new paragraph in an existing subsection; a new extension
is a subsection of §7. Each topic (a subsection, or a section without
subsections) follows the template:

1. An opening sentence: what the concept is (`\oneline`, no heading).
2. **The idea**, in run-in paragraphs, one per topic. Plain words, a small
   example where it helps.
3. **What to watch out for** (`\watch`, a run-in paragraph): when it
   applies, what can go wrong.
4. **See.** Handbook (n) · `Lean.name` · app: step · note.

## Sections

Status: `—` not started, `src` source material exists to absorb, `draft`,
`done`. (2026-11-16: `paper/paper.tex` has every section as a heading with a
"not yet written" note; §1–6 drafted. Later the same day: §0, A and C
drafted, then §7–9, then §10–11. 2026-11-17: §12–14 and B drafted, and
paragraphs for Findings 18–20 in §5–6: the first draft is complete.
2026-11-20: the 15 sections (old §0–14) and ~90 subsections regrouped into 9 sections
with run-in paragraphs; the matrix blend added
as §7.4.)

| # | Section (subsections) | Covers | Was (before 2026-11-20) | Status |
|---|---|---|---|---|
| 1 | Introduction (How to read this paper) | what credibility is, the best factor, what is new; the four documents, machine-checked means what | §1, §0 | draft |
| 2 | The model (Cohorts, periods and error terms; From data to `K`) | error terms, correlation within a period, distribution-free, Bühlmann–Straub notation; the recipe, PD not PSD, two cohorts | §2, §3 | draft |
| 3 | The best blend (The weights; The credibility factor; Special cases) | inverse-variance and GLS weights; the proposed `z`, `z > 1`, the sign flip, blend against BLUP; Bühlmann–Straub, two cohorts, equal covariances, ignoring or damping correlation | §4, §5, §6 | draft |
| 4 | Balance | when it holds for free, the cost of forcing it, how to balance | §7 | draft |
| 5 | Estimating the parameters | unbiased estimators, plug-in `K̂`, damping, a fit with no tuning, error of a fitted model | §8 | draft |
| 6 | Why the moments are real | true covariances and MSE; consistent iff `ρ ⪰ 0` | §9 | draft |
| 7 | Extensions (Cohorts observed over different periods; Groups and shared levels; Choosing the cohorts; Monthly data with a common factor; Several quantities per cohort) | unequal lengths; shared levels and groups; merging and intervals; relativities under a factor (Finding 31); the matrix blend, Hachemeister, Finding 22, frequency × severity and the pure-premium bias (Findings 32–33) | §10, §11, §12, new | draft |
| 8 | Related work | what is used from where | §14 | draft |
| 9 | Open directions | crossed levels, time, better fits, the distribution layer | §13 | draft |
| A | Changes from the thesis | corrections, beyond the thesis, concordance | A | draft |
| B | Concept index | term → meaning → section | B | draft |
| C | Notation | symbols, Bühlmann–Straub translation | C | draft |

Old section numbers in dated notes ("Absorbed into paper §n") use the old
numbering; the "Was" column translates them.

## Absorbing the notes

When a section is drafted from a working note (`notes/*.md`,
`studies/damping-theta.md`), the note gets a first line "Absorbed into
paper §n on <date>; kept as the working record" and is not updated again.
`FINDINGS.md` stays the dated log.

## Pending
(Results, findings or changed statements since the last paper update that
may need a paragraph.)
- *Done 2026-11-25 (later):* "Groups with their own collective mean" (§ Choosing the cohorts,
  Finding 41, contrast with Finding 14); "Given the levels" (error given the level, SURE, the OBP
  collective mean `∝ u(1 − z)²`, next to "What 'best' means"); normal noise with known mean
  makes the best linear predictor `E[Y | x]` ("What 'normal' means here").
- *Done 2026-11-25:* "Is a richer fit worth its price?" (§ Estimating the parameters: gain against
  price, laws (a) and (b), the cross term with Findings 37–40); one sentence on the cross term in
  "What 'normal' means here"; a watch-out in "What 'best' means" (MSE averaged over the collective,
  not per cohort; literature §10p); "The group effects, as mixed-model software computes them"
  (Henderson's equations, § Groups and shared levels).
- *Done 2026-11-24:* "What 'normal' means here" (§ Why the moments are real): normal theory as zero third
  and fourth cumulants, noise vs levels, estimate the cumulants instead of testing normality.
- The fourth-moment layer (2026-11-22, `Cumulants.lean`, `notes/fourth-moments.md`): why
  variances need cumulants, and the assumptions that cut their number (independent sources, a
  variance function). Write once the source corollary is proved. The source corollary and the
  variance-function version (law of total cumulance, `VarianceFunction.lean`, 2026-11-23) are in.
- Finding 35 (2026-11-23, `studies/skew-bias.js`): the plug-in bias predicted from one data set
  to first order (skew channel), within 20–35% of the simulated bias without correlation. A sentence
  where Finding 35 is explained.
- §8 damping (2026-11-23, studies S38–S42): the exact variance of `Σ̂ᵢⱼ` in the damping rule
  makes it worse for the rates; why the correlation-scale rule works, and why its normal-theory
  variance is enough (S41) and safer under heavy tails (S42). One paragraph.
- §12 serial correlation (2026-11-24, studies S43–S45): recency weighting of years (EWMA, Morris
  2026) is a restricted predictor (aggregated data, `Blup.predMse_aggregate_eq_blup_add`); its best
  λ shortens with volume, and the BLUP beats it by reading the common factor from all cohorts. One
  paragraph.
- §8 tapering (2026-11-24, studies S46–S48): when to taper is decided from the data
  (`Engine.taperSignal`, safe but conservative), and every gap between fits is about three times
  smaller at the credibility level of the thesis's own study. One sentence each.
- (Cleared 2026-11-22 for v3.0.0: plug-in MSE and unbiasedness, Finding 35 and balance, tapering
  in §8; the general target, season, factor model, its estimation, valid tables and choosing
  between fits on data in §10.4; known trend and serial correlation in §12. The items below are
  standing notes.)
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
