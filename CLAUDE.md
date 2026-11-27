# Correlated credibility in Lean

A hobby project: formalizing the master thesis *Generalized Bühlmann–Straub
credibility theory for correlated data* (Stockholm University, 2023:2), then
extending it. The owner wrote the thesis and steers from a phone; you grind
tactics.

## Start of every chat
- Check the cloud environment (`get_environment`). Lean work happens only in
  **lean**, where everything is prepared. In any other environment (usually
  **Default**) do only docs, data, discussion or app work (`app/`, its Node
  tests, the CI step that publishes it): don't run `lake` or `lean`, fetch
  Mathlib, edit `.lean` files, or switch environments yourself. If the request
  needs Lean, say so and suggest a new chat in **lean**. The SessionStart hook
  prints "skipping Lean setup" when the Lean hosts are blocked.
- Work on `main`; don't create branches. The SessionStart hook
  (`scripts/session_branch.sh`) moves a generated branch (`ccr-…`, `claude/…`)
  onto `main` tracking `origin/main`; if you still end up on one, don't push it,
  push `HEAD:main`. This overrides session defaults that say to push to that
  branch. Push fast-forward only; never force-push `main`.
- Several chats may run in parallel, each on its own `.lean` file. Before every
  push, run `git pull --rebase origin main`. On a conflict: regenerate
  `PROGRESS.md` with `scripts/progress.py` rather than merging it; keep both
  sides in blueprint chapters, `FINDINGS.md` and `Credibility.lean`; renumber your
  own finding if its number is taken; then rerun `lake build` (not needed if
  the chat touched no `.lean` file) and `scripts/blueprint_check.py`.

## Talking to the owner
- Replies are read on a phone: keep them short and give the math idea in words
  before any Lean.
- Questions are about this project. A general question ("how do we model
  frequency and severity?") means: how the repo does it. Answer from the repo
  (Lean files, `FINDINGS.md`, notes, handbook, paper), point to where it lives,
  and flag gaps; bring in outside literature only as a comparison or when the
  repo has nothing on it.
- At a natural break (a file done, a finding logged, context getting long), say
  so and end with a short, ready-to-paste prompt for the next chat: the file or
  `sorry`s to tackle and any state the next chat can't get from the repo (open
  questions, dead ends tried). After the prompt, ask "Do you want to continue
  here?" so the owner can reply "Yes" to go on in the same chat.
- Direction (owner, 2026-11-27): no fixed goal, but move towards results
  useful to a pricing actuary with real portfolio data, under assumptions such
  data typically meet. Exploring is welcome when it is labelled as such. So
  every next-chat prompt answers in one line each:
  - **Who uses it?** The practitioner question it answers; if none yet,
    label the prompt *exploration*.
  - **How common is the assumption?** Typical data (unequal volumes, short
    histories, skewed claims) or a corner of parameter space?
  - **Does it generalize?** A statement for every world, or a ranking in the
    worlds a study visits?
- Edge cases get logged, not chased: a result that matters only under an
  obscure assumption gets its line in `FINDINGS.md` (or "Parked" in
  `studies/PLAN.md`) with its counterexample, and the thread moves on.
- Depth check: after about three chats on one thread (e.g. S65 → S66 → S67),
  the prompt says what the thread has gained for practice and asks:
  "Continue, or park it and return to <the main thread>?"

## Rules
- Theorem statements are the spec. Never weaken or change one to make it
  provable. If a statement is false or needs an extra hypothesis, stop, explain
  why with a counterexample, and log it in `FINDINGS.md`. Such gaps in the
  thesis are the interesting part.
- General results first (owner, 2026-11-26): a statement for every world beats a
  ranking in the worlds a simulation visits. Simulations illustrate and build
  hypotheses; turn a study's outcome into a general target (Lean, or a Finding)
  rather than reporting it as settled.
- The core is distribution-free (only first and second moments): never add a
  distributional assumption to it. Second moments are given numbers, except in
  the moment layer (`*Moments.lean`, `Cumulants`, `CrossedPoolWeights`), which
  proves they are the actual covariances of *any* random variables with those
  moments. An optional distribution layer is allowed (owner, 2026-11-15):
  results assuming a noise family live in their own files (`*Normal.lean`,
  `PlugInSymmetric`, `VarianceFunction`), say so in their name and docstring
  ("under normal noise"), and nothing in the core depends on them.
- Before deriving or proposing something new, search the literature
  (credibility, small-area estimation / EBLUP, portfolio and covariance
  shrinkage) and note what is used in `studies/literature.md`: combine the best
  existing pieces in this framework rather than reinvent them.
- Fitted models never need hand-set hyperparameters (`studies/PLAN.md` §1).

## Architecture (avoiding proof bloat)
Agreed 2026-11-08. Prove each fact once, at the most general level that still
reads like the thesis; special cases are corollaries.
- Three layers: **Core** (results that only need a positive definite `K` and
  τ²: optimal weights, `bestZ`, GLS, MSE of the blend, balance); **models**
  (`Model`, `Unequal`, extensions: build `K`, prove `K.PosDef`, take the Core
  results as one-line corollaries); **moments** (one generic covariance lemma
  for linear combinations; each model supplies only its weight vectors).
- `Model` is `Unequal` with `obs j = univ`: `Model` results with an `Unequal`
  twin are proved from it.
- Thesis-facing theorems keep their exact statements and docstrings; only the
  proof becomes `simpa using <general result>`, and its blueprint `\uses{}`
  points at the general result.
- Rule of three: generalize when a third instance of a pattern appears, not
  before. Don't go more abstract than the `K` level (e.g. L² projections): the
  blueprint must stay readable as actuarial math.
- New extension: first ask which existing general result it instantiates. Prove
  only what is genuinely new: its `K`, its positive definiteness, its moments.
- `PROGRESS.md` ends with the refactoring backlog (theorem names in several
  namespaces; `progress.py --dupes` prints the open ones; accepted
  non-duplicates go in its `EXEMPT` with a reason). Refactors are done in a
  dedicated chat, one file at a time, with `lake build` passing after each.

## Layout (`Credibility/`)
A map by topic; each file's module docstring has the details and Lean names.
- Thesis §2: `Blend` (§2.1.1, eq. 7), `Data` (§2.3, eq. 16), `Model` (§2.3–2.5,
  `K`, eqs. 21, 22, 26), `Weights` (§2.5, eqs. 23–25), `Core` (§2.5 at the `K`
  level, eq. 26; balance §2.9), `BuhlmannStraub` (§2.6, eqs. 28–30),
  `TwoCohorts` (§2.7, eq. 32), `Expectation` (§2.8, expectation of quadratic
  estimators), `Estimation` (§2.8, eqs. 37–41), `Balance` (§2.9).
- Unequal lengths `Tⱼ`: `Unequal`, `UnequalEstimation`, `UnequalMoments`.
- Moment layer: `CoreMoments`, `Moments`, `RandomWeights`, `Cumulants`
  (variance of quadratic estimators, order four).
- BLUP of a general target: `Blup`, `BlupMoments`, `BlupNormal`, `Henderson`
  (mixed-model equations), `ObservedBest` (collective mean given the levels).
- Plug-in BLUP (estimated moments): `PlugInSymmetric`, `PlugIn` (exact MSE),
  `PlugInNormal`, `PlugInMix` (part way from blend to BLUP), `BlupPrice` (first-order
  price of the BLUP's weights against the blend's on the same `K̂`).
- Hierarchical (groups): `Hierarchical`, `GroupWeights`, `HierarchicalMoments`, `GroupPoolWeights`
  (best pool of pair estimators for `φτ²`).
- Crossed levels: `Crossed`, `CrossedEstimation`, `CrossedMoments`,
  `CrossedPoolWeights`, `CrossedPoolNormal`.
- Card data (`notes/card-data.md`): `Season`, `Factor`, `FactorMoments`,
  `FactorRelativity`, `FactorEstimation`, `FactorHenderson` (Henderson III / MINQUE), `Shock`, `ShockMoments`, `FreqSev`
  (frequency × severity), `Trend` (known common trend).
- Vector levels: `CoreVector`, `CoreVectorMoments`.
- Fitting: `FitStatistics`, `FitCrossTerm` (first-order cross term of the plug-in), `LineResiduals`, `LineResidualsMoments` (per-cohort line fits, corrected `Λ̂`), `VarianceFunction`, `ConeProjection` (valid PSD
  estimates), `OffDiagonal`, `Damping`.
- Cohorts and grouping: `Merging`, `KMeans`, `KMeansBridge`, `CrossFit` (held-out score of a
  chosen rule), `PreTestNormal` (merge iff the gap looks small, under normal noise).

## Lean workflow
- One chat per file or batch of `sorry`s; one `sorry` at a time, `lake build`
  after each step. `lake` is in `~/.elan/bin` (add it to `PATH`).
- Lean, Mathlib and a project build come from the environment's saved snapshot
  (setup script `scripts/fetch_mathlib.sh --build`, not rerun per chat). The
  SessionStart hook starts `lake build` in the background (log:
  `.lake/session-build.log`); the first `lake build` waits for it and only
  compiles what changed.
- Prefer existing Mathlib lemmas: `exact?`, `apply?`, or grep in
  `.lake/packages/mathlib`.
- Versions: Lean v4.36.0-rc2, Mathlib e293c420 (pinned 2026-11-06).

## When you close a `sorry` or log a finding
Commit each closed `sorry` separately, with a short message, after:
1. `python3 scripts/progress.py` (keeps `PROGRESS.md` current).
2. Blueprint: `\leanok` on that proof in its chapter; new theorems need an
   entry; update `\uses{}` when a proof changes (`scripts/CheckUses.lean`
   checks each edge is a direct reference). `scripts/blueprint_check.py` must
   pass.
3. A finding: entry in `FINDINGS.md`, a `remark` in the blueprint next to the
   result it concerns, and a line in the handbook's appendix "Findings"
   (statement or counterexample, Lean links), all in the same commit.
4. Ask for each of app, handbook, paper and thesis proposal: does it need
   this? Update it in the same commit, or add a line under "Pending" in
   `studies/PLAN.md`, `handbook/outline.md`, `paper/outline.md` or
   `studies/thesis-topics/outline.md`. A paper change a reader would notice
   also gets a line in `paper/CHANGELOG.md` (newest first); the title page's
   version line (date, commit) is written by CI.
5. After pushing a `.tex` change, check the Blueprint run on `main` (GitHub MCP
   `actions_list`; TeX isn't installed in sessions) and fix it if it fails. Its
   jobs `lean` and `docs` take about 2 minutes; don't wait for `deploy`.

CI also runs `scripts/CheckAxioms.lean`: open `sorry`s are fine, but a theorem
counted as proved must not depend on one (even through a lemma), and no axioms
beyond `propext`, `Classical.choice`, `Quot.sound`.

## Four documents, one home per kind of content (owner, 2026-11-16)
Words (owner, 2026-11-27): **thesis** means only the original 2023 thesis
(`thesis/original/`); **thesis proposal** is the draft for upcoming thesis work
(`studies/thesis-topics/proposal.tex`); **paper** is the main repo document
below. The paper grew out of the thesis but is not "the thesis", and the
proposal is not "the thesis" either.
A formula lives in the handbook, an explanation in the paper, a proof in Lean
and the blueprint; the others point to it. Don't restate across them.
- **App** (`app/`, plan in `studies/PLAN.md`): an interactive app for
  practitioners showing the ideas at work, world model against fitted model
  (the fit never sees the true parameters). `engine.js`, Node tests
  `engine.test.js`, page `index.html`, published at `/app/`.
- **Handbook** (`handbook/handbook.tex`, outline `handbook/outline.md`): every
  formula useful for credibility, own numbering, at most two lines of "use it" /
  "watch out" (some "why"), no proofs, each linked with `\lean{}`, each section
  citing the paper for context. `scripts/handbook_check.py` (CI) fails if a link
  is not a proved declaration: renaming or moving a linked theorem means
  updating the link. Built to `handbook.pdf`.
- **Paper** (`paper/paper.tex`, outline `paper/outline.md`): the main
  document of the project: concepts and key formulas, from the 2023 thesis
  on, and the first complete source for a reader. Explains concepts,
  organized for lookup; shows the ~10 formulas that carry the story and cites
  handbook numbers for the rest; no proofs, and Lean names only in the
  concordance (Appendix A). `scripts/paper_check.py` (CI) checks citations; run
  it with `--fix` after renumbering the handbook. Study figures (pgfplots) live in
  `paper/figures/`, written by `scripts/paper_figures.py` from the `.out.txt`
  files; CI fails if they drift (`--check`). Built to `/paper/`.
- **Blueprint** (`leanblueprint`): the proof ledger (statements, proofs,
  dependency graph, findings as remarks), a condensed §2 of the thesis. One
  file per chapter in `blueprint/src/chapters/` (`NN-topic.tex`, in reading
  order), listed in `content.tex`; a new chapter is a new file plus its
  `\input` line. Reached by link, not read front to back. `\lean{}` links go to
  the source line via `find/` (no doc-gen4). Deployed to GitHub Pages from
  `main`.

## Keeping the documents current
- "Pending" is a queue, not a parking place. The SessionStart hook runs
  `scripts/pending_status.py`: per document, its open Pending items, the oldest
  one's age, and the Lean commits since it last changed.
- When a document has more than 10 open items or one older than a week, it
  prints "catch-up due": the next-chat prompt then proposes a catch-up chat for
  that document instead of new work (the owner may still decline). For a
  document with few items but many Lean commits since it changed, look for
  stale claims (e.g. a direction called open that is now done).
- A catch-up chat takes one section or theme, ticks items off as it goes, and
  deletes the "*Done*" notes it leaves (the commit log keeps them).

## Studies
Simulation scripts `studies/runs/*.js`, outputs `studies/runs/*.out.txt`. Numbered observations
S1, S2, … are logged in `studies/LOG.md` (index at its top; add a row
for each new one). `studies/PLAN.md` is the app plan and its open Pending list;
finished items move to `studies/PLAN-done.md`.

## Literature and upstream
- Fetch open-access copies only (preprints, theses, repositories; never
  library or publisher PDFs): `bash scripts/fetch_paper.sh <url> [name]`
  (saves to `.papers/`, gitignored, with a `.txt`). If its host is blocked,
  propose adding it to the environment.
- No upstream contributions or posts: don't draft Zulip posts, GitHub
  comments or Mathlib PRs (Mathlib bans LLM-written contributions, and the
  owner's account was suspended over one). Reading public Mathlib to reuse its
  progress is fine. General lemmas stay in this repo, named and stated as if
  they were in Mathlib.

## Thesis source
`thesis/original/` (never edit it), with the R code and defence slides.
`main.tex` is the final version: the published PDF (link in
`thesis/README.md`) plus one later addition, `b₁ = z₁/(z₁+z₂)` in §2.7.1. No
need to look for other versions. Equation numbers in docstrings must match it.
