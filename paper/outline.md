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
- Sections are concepts, not results. A new result is normally a paragraph
  in an existing section.
- No proofs. A proof idea in one or two sentences is welcome when it is the
  explanation.
- Every section ends with a **See** line: handbook numbers, Lean names, app
  step, and the working note it came from.
- Numbers from simulations cite the study script in `studies/` that
  produced them.

## Section template

1. **In one sentence.** What the concept is.
2. **The idea.** Plain words, a small example where it helps.
3. **When it applies, and what to watch out for.**
4. **See.** Handbook (n) · `Lean.name` · app: step · note.

## Sections

Status: `—` not started, `src` source material exists to absorb, `draft`,
`done`.

| # | Section | Covers | Source material | Status |
|---|---|---|---|---|
| 0 | How to read this | the four documents and what each is for; machine-checked means what | this file, README "How it was made" | — |
| 1 | What credibility is | blending own experience with the portfolio; what `z` means; best blend | thesis §2.1, handbook 1 | src |
| 2 | The model | error terms instead of risk parameters; correlation across cohorts within a period; distribution-free; translation to Bühlmann–Straub notation | thesis §2.3, handbook 0 | src |
| 3 | From data to `K` | the recipe: build `K`, check it is positive definite, read off everything; why positive definite and not semidefinite; why two cohorts | Findings 1, 2 | src |
| 4 | The weights | inverse-variance within a cohort; GLS across cohorts; the link to the minimum-variance portfolio | thesis §2.5, `studies/literature.md` §1 | src |
| 5 | The credibility factor | the proposed `z`; how correlation moves it; `z > 1` and the sign flip | thesis §2.5, §2.7, Finding 3 | src |
| 6 | Special cases | Bühlmann–Straub; two cohorts; equal covariances; weights from credibility factors | Findings 4, 5 | src |
| 7 | Balance | what it is and why practitioners want it; when it holds for free; the cost of forcing it; how to balance if you must | Findings 10, 15, 16, study findings S27–S29 | src |
| 8 | Estimating the parameters | the unbiased estimators and what they need; plug-in `K̂` and damping; a fit with no tuning; the error of a fitted model | thesis §2.8, Finding 7, `studies/damping-theta.md`, `studies/literature.md` §2, §4 | src |
| 9 | Why the moments are real | given numbers versus actual covariances; true MSE; the assumptions are consistent exactly when `ρ ⪰ 0` | Findings 11, 12 | src |
| 10 | Cohorts observed over different periods | unequal lengths; the per-pair count | `notes/unequal-lengths.md`, Findings 8–10, 12 | src |
| 11 | Groups and shared levels | a shared level drops out; several groups; what the estimators see; towards hierarchical credibility | Finding 13 | src |
| 12 | Choosing the cohorts | when merging pays off; equal credibility is not grouping; optimal cohorts are intervals; when they are not | `notes/merging-cohorts.md`, `notes/kmeans-bridge.md`, Findings 6, 14 | src |
| 13 | Open directions | crossed levels; time trends; the optional distribution layer | `notes/crossed-2x2.md`, `notes/roadmap.md`, `studies/literature.md` §5 | src |
| 14 | Related work | credibility with common effects, small-area estimation, covariance shrinkage: what is used from where | `studies/literature.md` | src |
| A | Changes from the thesis | corrections and sharpenings, by thesis section; concordance thesis equation ↔ handbook number ↔ Lean name | `FINDINGS.md` | src |
| B | Concept index | alphabetical: term → one-line meaning → section | — | — |
| C | Notation | symbols, with the Bühlmann–Straub translation | handbook 0 | src |

## Absorbing the notes

When a section is drafted from a working note (`notes/*.md`,
`studies/damping-theta.md`), the note gets a first line "Absorbed into
paper §n on <date>; kept as the working record" and is not updated again.
`FINDINGS.md` stays the dated log.

## Pending
(Results, findings or changed statements since the last paper update that
may need a paragraph.)
(none)

## Order of work

1. Sections 1–6 (the thesis core), then A and C: this already replaces the
   thesis as the first thing to read.
2. Sections 7–9 (balance, estimation, moments): the parts practitioners ask
   about.
3. Sections 10–14 from the notes; B last, regenerated as sections land.
4. CI: build the paper as a searchable web page and a PDF next to the
   handbook; a `paper_check.py` like `handbook_check.py` (every Lean name
   and handbook number cited must exist and be proved).
5. A coverage report: proved results cited by none of handbook, paper, app,
   with an explicit "not needed" list.
6. When sections 1–9 are done: point README and `CITATION.cff` at the paper
   as the primary reference, and use it as the arXiv preprint (README
   "Sharing results" item 3).

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
