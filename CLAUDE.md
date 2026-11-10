# Correlated credibility in Lean

A hobby project: formalizing the master thesis *Generalized Bühlmann–Straub
credibility theory for correlated data* (Stockholm University, 2023:2), then
extending it. The owner wrote the thesis and steers from a phone; you grind
tactics.

## Layout (thesis section → file)
- §2.1.1 best credibility factor, eq. (7) → `Credibility/Blend.lean` (also `BlendMoments.shift`)
- §2.5 inverse-variance and GLS weights, eqs. (23)–(25) → `Credibility/Weights.lean`
- §2.3 parameters and eq. (16) → `Credibility/Data.lean`
- §2.5 K-level Core: moments for a level covariance `L`, eq. (26), `K⁻¹1` from `Kw = c·1`, diagonal,
  equal-covariance, rank-one and block-diagonal `K` → `Credibility/Core.lean`
- §2.3–2.5 data model, `K`, eqs. (21), (22), (26) → `Credibility/Model.lean` (corollaries of `Unequal` via `Model.toUnequal`)
- §2.6 Bühlmann–Straub special case, eqs. (28)–(30) → `Credibility/BuhlmannStraub.lean` (corollaries of `UnequalEstimation`);
  §2.9 balance → `Credibility/Balance.lean`
- §2.7 two cohorts, eq. (32) → `Credibility/TwoCohorts.lean`
- §2.8 expectation of quadratic estimators → `Credibility/Expectation.lean` (proved once for a
  symmetric covariance table `C`: `Ecov`, `UnbiasedCov`; the thesis `E`, `Unbiased` are `C = obsCov`)
- §2.8 parameter estimation, eqs. (37)–(41) → `Credibility/Estimation.lean` (corollaries of `UnequalEstimation` via `Model.toUnequal`)
- extension: merging two cohorts (Result A of `notes/merging-cohorts.md`) → `Credibility/Merging.lean`
- extension: cohort-dependent lengths `Tⱼ` (`notes/unequal-lengths.md`) → `Credibility/Unequal.lean`;
  its estimation (§2.8) and balance (§2.9) → `Credibility/UnequalEstimation.lean`
- extension: moment layer at Core level (any random `μ̂ⱼ`, `μⱼ` with covariances `K`, `L`:
  `Core.Estimates`, true MSE of the blend) → `Credibility/CoreMoments.lean`
- extension: moment layer for unequal lengths → `Credibility/UnequalMoments.lean` (cell level;
  portfolio and blend results are corollaries of `CoreMoments` via `Noise.toEstimates`)
- extension: moment layer (distribution-free random variables) → `Credibility/Moments.lean` (corollaries of `UnequalMoments` via `Noise.toUnequal`)
- extension: a shared level within groups, towards hierarchical credibility (Bridges 2–5: `K_φ`,
  `K_G`, the §2.8 estimators under `Unbiasedφ`/`UnbiasedG`, Bridge 3 as the one-group case of
  Bridge 5) → `Credibility/Hierarchical.lean`; group weights `B_g` and the same-group share `π`
  → `Credibility/GroupWeights.lean`
- extension: damping off-diagonal entries keeps PSD/PD (README small lemma (b)) → `Credibility/OffDiagonal.lean`
- extension: optimal 1-D weighted k-means groups are intervals (README small lemma (a)) → `Credibility/KMeans.lean`

Second moments are taken as given numbers, except in `Moments.lean` and `UnequalMoments.lean`, which
proves they are the actual covariances of *any* random variables with
those moments. The model is distribution-free (only first and second
moments are assumed). Never add a distributional assumption.

## Rules
- Theorem statements are the spec. Never weaken or change one to make it
  provable. If a statement is false or needs an extra hypothesis, stop,
  explain why with a counterexample, and log it in `FINDINGS.md`. Such
  gaps in the thesis are the interesting part.
- Work on one `sorry` at a time and run `lake build` after each step.
- Prefer existing Mathlib lemmas; search with `exact?`, `apply?`, or grep in
  `.lake/packages/mathlib`.
- Commit each closed `sorry` separately with a short message, and run
  `python3 scripts/progress.py` first so `PROGRESS.md` stays current.
- Replies are read on a phone: keep them short and give the math idea in
  words before any Lean.

## Workflow
- Check the cloud environment first (`get_environment`). Do Lean work only
  in **lean**, where everything is prepared. In any other environment
  (usually **Default**) the owner wants only docs, data or discussion: don't
  run `lake` or `lean`, fetch Mathlib, edit `.lean` files, or switch
  environments yourself. If the request needs Lean, say so and suggest a
  new chat in **lean**. The SessionStart hook prints "skipping Lean setup"
  when the Lean hosts are blocked.
- One chat per file or batch of `sorry`s. Lean, Mathlib and a build of the
  project come from the environment's saved snapshot (its setup script,
  `scripts/fetch_mathlib.sh --build`, is not rerun for each chat). The
  SessionStart hook starts `lake build` in the background (log:
  `.lake/session-build.log`), so the first `lake build` in a chat waits for
  that one and only compiles what changed since the snapshot. `lake` is in
  `~/.elan/bin` (add it to `PATH`).
- Push finished work to `main` (fast-forward; never force-push `main`).
  Don't create branches: commit on top of `main` and push to `main`. The
  SessionStart hook (`scripts/session_branch.sh`) moves a fresh generated
  branch (`ccr-…`, `claude/…`) onto `main` tracking `origin/main`; if you
  still end up on one, don't push it; push `HEAD:main` instead. The owner's instruction here overrides
  session defaults that say to push to that branch.
- Several chats may run in parallel, each on its own `.lean` file. Before
  every push, run `git pull --rebase origin main`. On a conflict: regenerate
  `PROGRESS.md` with `scripts/progress.py` rather than merging it; keep both
  sides in `content.tex`, `FINDINGS.md` and `Credibility.lean`; renumber
  your own finding if its number is taken. Then rerun `lake build` and
  `scripts/blueprint_check.py` before pushing again.
- TeX is not installed in the sessions, so LaTeX errors only show in CI. After
  pushing a `content.tex` change, check that the Blueprint run on `main`
  passes (GitHub MCP `actions_list`), and fix it if not. Its jobs `lean` and
  `docs` run in parallel (about 2 minutes); the `deploy` job after them only
  publishes the site and need not be waited for.
- At a natural break (a file done, a finding logged, context getting long),
  say so and end the reply with a short, ready-to-paste prompt for the next
  chat: the file or `sorry`s to tackle and any state the next chat can't
  get from the repo (open questions, dead ends tried).
- No upstream contributions or posts. Mathlib's policy (2026-11-09) bans
  LLM-written comments on its Zulip and GitHub and expects code written by
  hand, and the owner works only through AI; their account was suspended for
  an AI-drafted Zulip post. So don't draft Zulip posts, GitHub comments, or
  Mathlib PRs. Reading public Mathlib (source, PRs, issues) to reuse its
  progress is fine. General lemmas stay in this repo, named and stated as
  if they were in Mathlib.

## Architecture (avoiding proof bloat)
Agreed 2026-11-08. Prove each fact once, at the most general level that
still reads like the thesis; special cases are corollaries.
- Three layers: **Core** (results that only need a positive definite `K` and
  τ²: optimal weights, `bestZ`, GLS, MSE of the blend, balance); **models**
  (`Model`, `Unequal`, future extensions: build `K`, prove `K.PosDef`, take
  the Core results as one-line corollaries); **moments** (one generic
  covariance lemma for linear combinations; each model supplies only its
  weight vectors).
- `Model` is `Unequal` with `obs j = univ`: `Model` results with an `Unequal`
  twin are proved from it.
- Thesis-facing theorems keep their exact statements and docstrings. Only the
  proof becomes `simpa using <general result>`. In `content.tex`, `\uses{}`
  points special cases at the general result.
- Rule of three: generalize when a third instance of a pattern appears, not
  before. Don't go more abstract than the `K` level (e.g. L² projections):
  the blueprint must stay readable as actuarial math.
- New extension: first ask which existing general result it instantiates.
  Prove only what is genuinely new: its `K`, its positive definiteness, and
  its moments.
- Tooling: `PROGRESS.md` ends with the refactoring backlog (theorem names in
  several namespaces; `progress.py --dupes` prints the open ones), and
  `scripts/CheckUses.lean` (CI) checks that every blueprint proof `\uses`
  edge is a direct reference in the Lean proof. So when a proof changes,
  update its `\uses{}` too.
- Refactors are done in a dedicated chat, one file at a time, with
  `lake build` passing after each file.

## Blueprint
`blueprint/src/content.tex` is a condensed §2 of `thesis/original/main.tex`
(`leanblueprint`; `\lean{}`/`\uses{}`, dependency graph, `FINDINGS.md` items
as remarks). The owner wants it to become the up-to-date, shorter version of
the thesis. CI builds it and deploys to GitHub Pages from `main`.
- When you close a `sorry`, add `\leanok` to that proof in `content.tex`;
  new theorems need a blueprint entry. `python3 scripts/blueprint_check.py`
  must pass before committing (it compares with the same test as
  `PROGRESS.md`).
- CI also runs `scripts/CheckAxioms.lean`: open `sorry`s are fine, but a
  theorem counted as proved must not depend on one (even through a lemma),
  and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
- A new finding gets a `remark` next to the result it concerns.
- `\lean{}` links go to the source line via `find/` (no doc-gen4 build;
  it would document all of Mathlib).

## Handbook
`handbook/handbook.tex` is the short practitioner's version: key results,
own numbering, comments in a practical voice ("use it", "watch out") with
some intuition ("why"), no proofs, each result linked with `\lean{}`.
Outline and status: `handbook/outline.md`. CI builds it to `handbook.pdf`
on the site.
- `scripts/handbook_check.py` (CI) fails if a handbook link is not a proved
  declaration. Renaming or moving a linked theorem means updating the link.
- When a result is proved, a finding logged, or a statement changed, ask:
  does the handbook need it? If so, add or update its entry (and the
  outline) in the same commit, or note it in `handbook/outline.md` under
  "Pending". Only results useful for credibility go in.

The thesis source is in `thesis/original/` (never edit it). Equation numbers
in docstrings must match it. Collecting the original files is done
(2026-11-06): `main.tex` is the final version: the published PDF (link in
`thesis/README.md`) plus one later addition, `b₁ = z₁/(z₁+z₂)` in §2.7.1. The R code and the defence slides are there too.
No need to look for other versions.

## First session only (done 2026-11-06: Lean v4.36.0-rc2, Mathlib e293c420)
1. If `.lake/packages/mathlib` is missing, run `bash scripts/fetch_mathlib.sh`.
2. Run `lake update`, copy `.lake/packages/mathlib/lean-toolchain` to
   `./lean-toolchain`, pin `rev` in `lakefile.toml` to the Mathlib commit in
   `lake-manifest.json`, run `lake exe cache get`, then `lake build`.
3. Fix any statement that fails to elaborate (syntax, coercions, renamed
   Mathlib names) without changing its meaning, and log what changed.
4. Commit the pinned toolchain, lakefile and manifest.
5. Report whether `lake exe cache get` reached its server; if it was blocked,
   name the host so it can be added to the environment's allowlist.
