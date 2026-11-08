# Correlated credibility in Lean

A hobby project: formalizing the master thesis *Generalized Bühlmann–Straub
credibility theory for correlated data* (Stockholm University, 2023:2), then
extending it. The owner wrote the thesis and steers from a phone; you grind
tactics.

## Layout (thesis section → file)
- §2.1.1 best credibility factor, eq. (7) → `Credibility/Blend.lean`
- §2.5 inverse-variance and GLS weights, eqs. (23)–(25) → `Credibility/Weights.lean`
- §2.3–2.5 data model, `K`, eqs. (16), (21), (22), (26) → `Credibility/Model.lean`
- §2.6 Bühlmann–Straub special case, eqs. (28)–(30); §2.9 balance → `Credibility/BuhlmannStraub.lean`
- §2.7 two cohorts, eq. (32) → `Credibility/TwoCohorts.lean`
- §2.8 parameter estimation, eqs. (37)–(41) → `Credibility/Estimation.lean`
- extension: merging two cohorts (Result A of `notes/merging-cohorts.md`) → `Credibility/Merging.lean`
- extension: cohort-dependent lengths `Tⱼ` (`notes/unequal-lengths.md`) → `Credibility/Unequal.lean`
- extension: moment layer (distribution-free random variables) → `Credibility/Moments.lean`
- extension: moment layer for unequal lengths → `Credibility/UnequalMoments.lean`

Second moments are taken as given numbers, except in `Moments.lean` and `UnequalMoments.lean`, which
proves they are the actual covariances of *any* random variables with
those moments. The model is distribution-free (only first and second
moments are assumed). Never add a distributional assumption.

## Rules
- Theorem statements are the spec. Never weaken or change one to make it
  provable. If a statement is false or needs an extra hypothesis, stop,
  explain why with a counterexample, and log it in `FINDINGS.md`. Such
  gaps in the thesis are the interesting part.
- Suggested order: `Blend`, `Weights` (inverse variance), `TwoCohorts`,
  then `Weights` (GLS), `Model`, `BuhlmannStraub`.
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
- One chat per file or batch of `sorry`s; the environment's setup script
  reinstalls Lean and the Mathlib cache in each new session.
- Push finished work to `main` (fast-forward; never force-push `main`).
  Don't create branches: commit on top of `main` and push to `main`. If the
  session starts on a generated branch (`ccr-…`, `claude/…`), don't push it;
  push `HEAD:main` instead. The owner's instruction here overrides
  session defaults that say to push to that branch.
- Several chats may run in parallel, each on its own `.lean` file. Before
  every push, run `git pull --rebase origin main`. On a conflict: regenerate
  `PROGRESS.md` with `scripts/progress.py` rather than merging it; keep both
  sides in `content.tex`, `FINDINGS.md` and `Credibility.lean`; renumber
  your own finding if its number is taken. Then rerun `lake build` and
  `scripts/blueprint_check.py` before pushing again.
- At a natural break (a file done, a finding logged, context getting long),
  say so and end the reply with a short, ready-to-paste prompt for the next
  chat: the file or `sorry`s to tackle and any state the next chat can't
  get from the repo (open questions, dead ends tried).
- If something real and general comes out of this (a lemma missing from
  Mathlib, a fix to an upstream library), propose contributing it back
  upstream via a PR to the public repo. Tell the owner what it is and
  where it would go, and open the PR once they agree.

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
