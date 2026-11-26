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
  equal-covariance, rank-one and block-diagonal `K`, balance of any blend (§2.9) and the best
  balanced blend (PLAN G7) → `Credibility/Core.lean`
- extension: best linear unbiased predictor of a general target `Y` (`ℓ = Cov(x, Y)`,
  `v = Var Y`) with fixed effects `Xᵀd = x₀` (universal kriging, `notes/card-data.md` Step 1;
  `Core.blupWeight_optimal` is `X = 1`, `CoreVector.blupW_optimal` is `X = U`; nested designs
  and aggregated data as restricted predictors) → `Credibility/Blup.lean`; its moment layer
  (`Core.Target`: any random cells and target, `cov(x, Y)` free; `Core.Estimates` via `toTarget`)
  → `Credibility/BlupMoments.lean`
- extension: the season and the 12-month target (`notes/card-data.md` Step 2): season design,
  when it drops out (`Season.blup_eq_iff`, interchangeable months), it does not in general
  (Finding 24), the bias of ignoring it, a known index via `Unequal` → `Credibility/Season.lean`
- distribution layer: the plug-in BLUP (estimated `K̂`, `ℓ̂`, even and translation invariant) is
  unbiased under symmetric noise (Kackar–Harville) → `Credibility/PlugInSymmetric.lean`; its exact
  MSE `mse(d*) + E B² + 2E[AB]` (distribution-free) → `Credibility/PlugIn.lean`; the cross term
  vanishes under normal noise → `Credibility/PlugInNormal.lean`; part way from the fitted blend to the
  fitted BLUP: `MSE(θ) = (1−θ)M₀ + θM₁ − θ(1−θ)S`, best `θ = ½ + (M₀−M₁)/(2S)`, `θ* = 1` with known
  moments, `θ` chosen on a held-out proxy (exact iff `E[Δε] = 0`, bias `E[Δε]/EΔ²`), clipping to
  `[0, 1]` (distribution-free) → `Credibility/PlugInMix.lean`; with known mean the best linear predictor is `E[Y | x]` and best among all measurable
  predictors under normal noise → `Credibility/BlupNormal.lean`
- §2.3–2.5 data model, `K`, eqs. (21), (22), (26) → `Credibility/Model.lean` (corollaries of `Unequal` via `Model.toUnequal`)
- §2.6 Bühlmann–Straub special case, eqs. (28)–(30) → `Credibility/BuhlmannStraub.lean` (corollaries of `UnequalEstimation`);
  §2.9 balance → `Credibility/Balance.lean`
- §2.7 two cohorts, eq. (32) → `Credibility/TwoCohorts.lean`
- §2.8 expectation of quadratic estimators → `Credibility/Expectation.lean` (proved once for a
  symmetric covariance table `C`: `Ecov`, `UnbiasedCov`; the thesis `E`, `Unbiased` are `C = obsCov`;
  `integral_quad_of_cov`: `Ecov` is the true expectation for any random variables with table `C`;
  means from a design `Dβ`: `EcovMean`, `UnbiasedMean`, `integral_quad_of_mean`)
- §2.8 parameter estimation, eqs. (37)–(41) → `Credibility/Estimation.lean` (corollaries of `UnequalEstimation` via `Model.toUnequal`)
- extension: merging two cohorts (Result A of `notes/merging-cohorts.md`) → `Credibility/Merging.lean`
- extension: cohort-dependent lengths `Tⱼ` (`notes/unequal-lengths.md`) → `Credibility/Unequal.lean`;
  its estimation (§2.8) and balance (§2.9) → `Credibility/UnequalEstimation.lean`
- extension: moment layer at Core level (any random `μ̂ⱼ`, `μⱼ` with covariances `K`, `L`:
  `Core.Estimates`, true MSE of the blend; a common component of orthonormal effects `Core.common`,
  used by group and crossed effects) → `Credibility/CoreMoments.lean`; random weights
  (Finding 35: bias `Σᵢ cov(d̂ᵢ, μ̂ᵢ)`, exposure balance keeps the portfolio unbiased)
  → `Credibility/RandomWeights.lean`
- extension: the collective mean given the levels (literature §10p): the blend's error given
  the level, its unbiased estimate (SURE), and the observed best predictor's collective mean,
  weights `∝ uⱼ(1 − zⱼ)²` (`Core.obpMean`) → `Credibility/ObservedBest.lean`
- extension: moment layer for unequal lengths → `Credibility/UnequalMoments.lean` (cell level;
  portfolio and blend results are corollaries of `CoreMoments` via `Noise.toEstimates`)
- extension: moment layer (distribution-free random variables) → `Credibility/Moments.lean` (corollaries of `UnequalMoments` via `Noise.toUnequal`)
- extension: a shared level within groups, towards hierarchical credibility (Bridges 2–5: `K_φ`,
  `K_G`, the §2.8 estimators under `Unbiasedφ`/`UnbiasedG`, Bridge 3 as the one-group case of
  Bridge 5) → `Credibility/Hierarchical.lean`; group weights `B_g` and the same-group share `π`
  → `Credibility/GroupWeights.lean`; its moment layer (group effects `γ_g`, `K_G` and `L_G` as actual
  covariances, true MSE: `Unequal.NoiseG`, a common component on top of `UnequalMoments` via
  `Core.Estimates.addCommon`; `Model.NoiseG` results are corollaries via `NoiseG.toUnequal`; likewise
  `Model.KG`/`momentsG`/`bestZ_G_eq` in `Hierarchical.lean` via `Unequal.KG` and `KG_eq_toUnequal`;
  the group effects `b_g` as a `Core.Target`: Henderson's equations predict them best in true MSE,
  `NoiseG.mme_groupEffect_mse_optimal`) → `Credibility/HierarchicalMoments.lean`
- extension: a known common trend `g` (`notes/time-trends.md` §1 steps 1–2): `Unequal.scale`/`detrend`,
  `K̃ = (1+g)^(2n)K`, weights and `z` unchanged, trend-free relativities (Finding 21)
  → `Credibility/Trend.lean`
- extension: the common factor model (`notes/card-data.md` Step 3, Finding 25): a factor
  `λᵢλⱼΓₜₛ` over all months on top of `Shock` (`Γ = 0`), `K ≻ 0` for any observed cells, AR(1)
  and block `Γ`, per-cohort dynamics `δᵢⱼGᵢ` (`KG`), `ℓ`, `v` for the 12-month target, Step 1/2 as
  corollaries; fitted tables `tableK` (any `A ⪰ 0`, no `τ²`: `≻ 0` when every `ŝⱼ² > 0`, not with `ŝ² ≥ 0` alone: Finding 30; with some `ŝⱼ² = 0` iff `(Â + Ĉ)_ZZ ≻ 0` given `Φ ≻ 0` and a common month: Finding 34)
  → `Credibility/Factor.lean`; its moment layer (`Factor.Cells`: random cells over
  all months with any covariance table, `Cells.toTarget` into `Core.Target`, true MSE)
  → `Credibility/FactorMoments.lean`
- extension: when the factor cancels from relativities (`notes/card-data.md` Step 4, Finding 31):
  exact extra variance `gᵀΓg` of any linear statistic, relativities with equal loadings and month
  weights, counterexamples, true variance → `Credibility/FactorRelativity.lean`
- extension: frequency × severity with a `Factor` table per component (Step 6, Finding 32): joint
  `K`, `L`, joint = separate, Kronecker case, exact product bias (Finding 33) → `Credibility/FreqSev.lean`
- extension: estimating the factor model, part 1 (`notes/card-data.md` Step 5, literature §10h):
  `Expectation.UnbiasedMean` (means `Dβ`: unbiased for all `β` iff the form annihilates `D`), (I1)
  scale `(λ, Γ) ↦ (aλ, a⁻²Γ)`, (I2) lag 0 only through `C + γλλᵀ`, (I3) lag ≥ 1 cross-card
  entries are `λᵢλⱼΓₜₛ`, the year-on-year lagged cross-product, (I4) loadings need three cohorts,
  (I5) AR(1) from cross-moments, the shock estimators' bias under a factor (Finding 26: `Ĉ`, the
  between-cohort spread)
  → `Credibility/FactorEstimation.lean`
- extension: shock plus process noise (Finding 23): `cov = δₜₛ(Cᵢⱼ + δᵢⱼsᵢ²/wᵢₜ) + τ²δᵢⱼ`, its `K`
  for any cohort weights, `K ≻ 0`, unbiased `Ĉ`, `ŝ²` (identified only through volume variation)
  → `Credibility/Shock.lean`; its moment layer (`Shock.Cells`, random cells with the table `obsCov`,
  `Cells.toEstimates` into `Core.Estimates`, true MSE, `E K̂ = K`) → `Credibility/ShockMoments.lean`
- extension: the matrix Blend (vector levels `μⱼ ∈ ℝᴾ`, credibility matrix `Z`, joint `K` over
  cohorts × components, matrix GLS, matrix eq. (26); `notes/time-trends.md` §3 item 4)
  → `Credibility/CoreVector.lean`; its moment layer (`CoreVector.VecEstimates`, centred to a
  `Core.Estimates` over `J × P`) → `Credibility/CoreVectorMoments.lean`
- extension: valid estimates by projection: the `H`-projection of an estimate onto a convex set
  containing the truth (PSD tables) has `H`-norm error ≤ the estimate's, in every draw and in mean;
  exists and is unique for `H ≻ 0` (`studies/PLAN.md`, `constrainPSD`) → `Credibility/ConeProjection.lean`
- moment layer, order four: the variance of any quadratic estimator from the mean, covariance and
  third and fourth cumulant tables (`varQuad`, `variance_quad_of_cumulants`; distribution-free,
  `notes/fourth-moments.md`) → `Credibility/Cumulants.lean`; noise cumulants that depend on the random
  level (option (b): levels `μ`, noise kernel `κ`, law of total variance on `μ ⊗ₘ κ`), the variance
  function `μᵖ` (Tweedie) as its corollary (distribution layer) → `Credibility/VarianceFunction.lean`; the covariance of two quadratic
  forms and the statistics `P`, `Qn`, `B` of the pooled fits (S53: exact Var/Cov, `cov(B, P) = 0`
  conditions, Finding 37), the balanced identity `ẑ = 1 − v̂/S²` and law (a) of S56 (first-order price of
  fitting BS), the gap between two blends as a quadratic in `z` → `Credibility/FitStatistics.lean`
- extension: crossed levels (`notes/crossed-2x2.md`): `L = α²[same row] + β²[same column] + γ²I`
  for any cell set, `K ≻ 0`, `K = ZGZᵀ + R` (Henderson gives row and column effects), `β² = 0` is
  Bridge 4; balanced table: three factors `z_r, z_c, z_i`, the blend's excess per layer; a cell
  without data (2×2) → `Credibility/Crossed.lean`; its estimation (pair estimators from the
  same row / column / neither, unbiased for any noise correlations, `Model.crossed_unbiasedX`; the
  ANOVA identity `sum_mul_sq_sub_eq_pairs`; Dannenburg's/Goulet's two-way ANOVA equations exactly
  as pair pools, `anovaStat_row/grand_unbiasedX`, biased under correlated noise: Finding 42)
  → `Credibility/CrossedEstimation.lean`; its moment
  layer (`Model.NoiseX`: row and column effects as a common component on the thesis noise, true
  covariances and expectations, true MSE, consistent iff `ρ ⪰ 0`) → `Credibility/CrossedMoments.lean`;
  the best pool within a class (moment layer: Var of a pair pool = `aᵀVa` from `covQuad`, GLS on `V`
  is the minimum-variance unbiased pool, balanced table: equal weights exact by symmetry)
  → `Credibility/CrossedPoolWeights.lean`; under normal noise `Var((μ̂ᵢ − μ̂ⱼ)²) = 2(E(μ̂ᵢ − μ̂ⱼ)²)²`
  and the limits of inverse-variance pair weights (distribution layer) → `Credibility/CrossedPoolNormal.lean`
- general matrix lemmas for `V = ZGZᵀ + R` (ported from Stat-Lean, Apache 2.0): push-through,
  binomial inverse (small form of `V⁻¹`), Henderson's mixed-model equations, their solution is `Core.blup`
  (`hendersonMME_eq_blup`) → `Credibility/Henderson.lean`; group effects by MME: `Unequal.groupEffect_eq_blup`
- extension: damping off-diagonal entries keeps PSD/PD (README small lemma (b)) → `Credibility/OffDiagonal.lean`
- extension: damping as shrinkage (PLAN G2): the table-optimal `θ* = Σs²/(Σs² + ΣV)` for given
  means and variances, and the safe range of `θ` → `Credibility/Damping.lean`
- extension: optimal 1-D weighted k-means groups are intervals (README small lemma (a)) → `Credibility/KMeans.lean`
- extension: exposure-weighted pooling is weighted k-means, so optimal pooled cohorts are
  intervals; with a common variance the blend's optimal cohorts too (`notes/kmeans-bridge.md`,
  Finding 14); group means with one common `τ²` (`group_optimal_contiguous`, Finding 41) → `Credibility/KMeansBridge.lean`

Plan for turning the results into practice: `studies/PLAN.md` (the app in
`app/`: `engine.js` with Node tests `engine.test.js`, page `index.html`,
published at `/app/`; an interactive app for practitioners, world model against fitted model; the fit never sees
the true parameters). When a result is proved or an extension added, ask:
does the app need a switch or a step for it? Note it in the plan if so.

Before deriving or proposing something new, search the literature (credibility, small-area
estimation / EBLUP, portfolio and covariance shrinkage) for work to build on, and note what is
used in `studies/literature.md`: combine the best existing pieces in this framework rather than
reinvent them. Fitted models never need hand-set hyperparameters (`studies/PLAN.md` §1).

Second moments are taken as given numbers, except in the moment layer (`BlupMoments.lean`, `CoreMoments.lean`, `Cumulants.lean`, `FactorMoments.lean`, `CoreVectorMoments.lean`, `ShockMoments.lean`,
`Moments.lean`, `UnequalMoments.lean`, `HierarchicalMoments.lean`, `CrossedMoments.lean`,
`CrossedPoolWeights.lean`), which
proves they are the actual covariances of *any* random variables with
those moments. The core model is distribution-free (only first and second
moments are assumed): never add a distributional assumption to it. An
optional distribution layer is allowed (owner, 2026-11-15): results that
assume a noise family (e.g. normal, gamma) live in their own files and
sections, say so in their name and docstring (e.g. "under normal noise"),
and nothing in the core depends on them.

## Rules
- Theorem statements are the spec. Never weaken or change one to make it
  provable. If a statement is false or needs an extra hypothesis, stop,
  explain why with a counterexample, and log it in `FINDINGS.md`. Such
  gaps in the thesis are the interesting part.
- General results first (owner, 2026-11-26): a statement for every world beats a ranking in the
  worlds a simulation visits. Simulations illustrate and build hypotheses; turn a study's outcome
  into a general target (Lean, or a Finding) rather than reporting it as settled.
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
  (usually **Default**) the owner wants only docs, data, discussion or app
  work: don't run `lake` or `lean`, fetch Mathlib, edit `.lean` files, or
  switch environments yourself. App work (`app/`, its Node tests, the CI
  step that publishes it) is fine in Default; only Lean work needs
  **lean**. An app chat in Default never touches `.lean` files, so a
  rebase conflict there needs no `lake build`. If the request needs Lean,
  say so and suggest a new chat in **lean**. The SessionStart hook prints
  "skipping Lean setup" when the Lean hosts are blocked.
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
- Literature: fetch open-access copies (preprints, theses, repositories; never
  library or publisher PDFs) with `bash scripts/fetch_paper.sh <url> [name]`
  (saves to `.papers/`, gitignored, with a `.txt`). If its host is blocked,
  propose adding that host to the environment.
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
  several namespaces; `progress.py --dupes` prints the open ones; accepted non-duplicates go in its
  `EXEMPT` with a reason), and
  `scripts/CheckUses.lean` (CI) checks that every blueprint proof `\uses`
  edge is a direct reference in the Lean proof. So when a proof changes,
  update its `\uses{}` too.
- Refactors are done in a dedicated chat, one file at a time, with
  `lake build` passing after each file.

## Four documents, one home per kind of content (owner, 2026-11-16)
- **App** (`app/`): shows the ideas and tools at work. Focus: application.
- **Handbook** (`handbook/`): every formula, each with at most two lines of
  "use it" / "watch out"; no explanations (each section cites the paper's for context).
- **Paper** (`paper/`, outline and status in `paper/outline.md`): the
  up-to-date version of the thesis and the first complete source for a
  reader. Explains concepts, organized for lookup; displays the ~10 formulas that
  carry the story and cites handbook numbers for the rest; no proofs and no Lean names
  (the handbook entry links them; only the concordance in Appendix A lists Lean names,
  and `paper_check.py` enforces it).
- **Blueprint**: the proof ledger (statements, proofs, dependency graph).
  Reached by link, not read front to back.
The paper is `paper/paper.tex` (built by CI to `/paper/` and `paper.pdf`);
`scripts/paper_check.py` (CI) checks its citations (Lean names proved,
handbook numbers current: run it with `--fix` after renumbering the handbook).
Don't restate across them: a formula lives in the handbook, an explanation
in the paper, a proof in Lean and the blueprint; the others point to it.
When a result is proved, a finding logged, or a statement changed, ask for
each of app, handbook and paper: does it need this? Update it in the same
commit, or add a line under "Pending" in `studies/PLAN.md`,
`handbook/outline.md` or `paper/outline.md`.

## Blueprint
`blueprint/src/content.tex` is a condensed §2 of `thesis/original/main.tex`
(`leanblueprint`; `\lean{}`/`\uses{}`, dependency graph, `FINDINGS.md` items
as remarks). It is the proof ledger; explanation beyond what a statement
needs belongs in the paper. CI builds it and deploys to GitHub Pages from `main`.
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
- Every finding gets a line in the handbook's appendix "Findings" (statement or
  counterexample, Lean links), in the same commit as its `FINDINGS.md` entry, so
  no result lives only in Lean code.
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
