# Correlated credibility in Lean

A hobby project: formalizing the master thesis *Generalized Bühlmann–Straub
credibility theory for correlated data* (Stockholm University, 2023:2), then
extending it. The owner wrote the thesis and steers from a phone; you grind
tactics.

## Layout (thesis section → file)
- §2.1.1 best credibility factor, eq. (7) → `Credibility/Blend.lean`
- §2.5 inverse-variance and GLS weights, eqs. (23)–(25) → `Credibility/Weights.lean`
- §2.3–2.5 data model, `K`, eqs. (21), (22), (26) → `Credibility/Model.lean`
- §2.6 Bühlmann–Straub special case, §2.9 balance → `Credibility/BuhlmannStraub.lean`
- §2.7 two cohorts, eq. (32) → `Credibility/TwoCohorts.lean`

Second moments are taken as given numbers; a probabilistic layer proving
they are actual covariances of random variables is a later goal.

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
- One chat per file or batch of `sorry`s; the environment's setup script
  reinstalls Lean and the Mathlib cache in each new session.
- Push finished work to `main` (fast-forward; never force-push `main`).
- At a natural break (a file done, a finding logged, context getting long),
  say so and end the reply with a short, ready-to-paste prompt for the next
  chat: the file or `sorry`s to tackle and any state the next chat can't
  get from the repo (open questions, dead ends tried).
- If something real and general comes out of this (a lemma missing from
  Mathlib, a fix to an upstream library), propose contributing it back
  upstream via a PR to the public repo. Tell the owner what it is and
  where it would go, and open the PR once they agree.

## Blueprint (planned)
Once `Weights` and `TwoCohorts` are proved, propose a full `leanblueprint`
(`blueprint/` LaTeX with `\lean{}`/`\uses{}`, dependency graph, CI to
GitHub Pages), seeded from `PROGRESS.md`, with `FINDINGS.md` as remarks.

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
