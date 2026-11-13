# From theorems to practice: implementation plan

Written 2026-11-13. Status: proposal, nothing built yet. Tick items off as
they are done.

**Aim.** Show, on one simulated portfolio, what each proved result buys a
pricing actuary compared with standard Bühlmann–Straub (BS). Short studies,
one message each. Where a result turns out not to give anything usable, that
is logged as a gap and becomes the next thing to prove.

## 1. Design in one page

**One world, one showcase dataset, many replications.** A single dataset is
the right anchor: every study talks about the same portfolio, and the reader
learns it once. But a mean squared error is an average, and one draw cannot
show it. So:

- the **world** (the true parameters) is fixed once and used by all studies;
- the **showcase dataset** is one draw from it (fixed seed, saved as CSV),
  printed in tables so every number can be followed by hand;
- the **replications** are `N` further draws from the same world. All MSE
  numbers come from these.

**Two regimes, always side by side.**

- *Oracle*: true parameters known. Here the theorems apply exactly, so the
  simulated MSE must match the proved formula. This is a test of the code
  and an illustration of the theorem.
- *Plug-in*: parameters estimated from the data. This is what a
  practitioner gets. The theorems are silent here. The share of the oracle
  gain that survives estimation is the practical value of the result.

**The headline: one table, a ladder of methods.** Every method is run on
the same data, each adding one idea:

| | Method | What it adds | Lean |
|---|---|---|---|
| M0 | own mean (`z = 1`), collective (`z = 0`) | the two extremes | |
| M1 | Bühlmann–Straub | the standard | `bs_z` |
| M2 | thesis model on the common window | correlation (data outside the window is thrown away) | `Model.bestZ_eq` |
| M3 | unequal lengths | correlation, all data | `Unequal.bestZ_eq` |
| M4 | group levels | a shared level within groups | `bestZ_G_eq` |
| M5 | chosen cohorts | cohorts picked by dynamic programming | `pool_optimal_contiguous` |

Columns: total MSE in theory (oracle), simulated (oracle), simulated
(plug-in), and the same as a percentage of BS. Each study below zooms in on
one step of the ladder and turns one dial.

**Measures** (the same everywhere): exposure-weighted total MSE of the
blended rates `Σⱼ wⱼ* (μ̂ⱼᵇ − μⱼ)²`; error of the collective `μ̂`; off-balance
`Σⱼ wⱼ*(μ̂ⱼᵇ − μ̂ⱼ) / Σⱼ wⱼ* μ̂ⱼ`.

## 2. The world

Small enough to print, rich enough that every extension has something to
do. Suggested (to be tuned so that the effects are visible but realistic):

- **12 cohorts in 3 groups of 4** (say 3 lines of business × 4 regions),
  **10 years**.
- **Levels**: `μ = 1`; cohort levels share a part `φτ²` within a group
  (`φ = 0.5`). Skewed (gamma), not normal.
- **Noise**: `σⱼₜ = σⱼ/√wⱼₜ` with different `σⱼ`, and volumes differing by
  a factor of about 10 between cohorts (the thesis study has nearly equal
  volumes, which is BS's best case).
- **Correlation within a year**: from a common yearly shock plus a group
  shock, e.g. `ρ = 0.6` within a group and `0.2` across. Skewed noise, to
  underline that the results are distribution-free.
- **Unequal lengths**: four cohorts launched late (3 to 5 years of data),
  one discontinued.

Each feature has a switch (`ρ = 0`, full lengths, `φ = 0`), so a study can
turn its own dial and leave the rest fixed.

## 3. The studies

Each study is one script and one page: the question, the methods compared,
one table, one figure, a one-sentence takeaway, the theorems it rests on.
Nothing else.

**S0. The portfolio and the yardstick.** The showcase dataset, BS applied to
it, and the ladder table. *Check:* simulated oracle MSE equals the proved
MSE (`mse_blend`) for every method within Monte Carlo error.

**S1. Correlation** (thesis §2.5–2.7; Findings 1, 3, 5, 11).
Dial: `ρ` from 0 to 0.9. BS against the proposed `z` with GLS weights.
- Oracle: gain over BS as a function of `ρ`; zero at `ρ = 0`.
- Plug-in, three ways of estimating the correlations: full `K̂` (eq. (39));
  `K̂` damped (`dampedK_posDef`); one common covariance `c` (Finding 5,
  closed form `zⱼ = τ²/(τ² + σ²ⱼⱼ − c)`).
- Side panel: how often `ẑⱼ > 1` or `b̂ⱼ < 0`, and what clipping
  (thesis eq. (34)) costs.

  Expected message: correlation matters from some `ρ` on; the full `K̂`
  has too many parameters for 10 years, and a structured one keeps most of
  the gain. This answers the open question in `thesis/README.md`.

**S2. Unequal lengths** (Findings 8–10, 12).
Dial: how late the late cohorts start. Thesis model on the common window
(M2) against all data (M3), and BS on all data.
- Bias of the naive `|Tᵢⱼ| − 2` against the proved count `nᵢⱼ` (Finding 9).
- Balance in the BS case holds to machine precision (`Unequal.balance_total`).

**S3. Groups** (Finding 13).
Dial: `φ` from 0 to 0.9.
- `E τ̂² = τ² − φτ²π`: simulated against proved (`tauHat_unbiasedG`), and
  the pair estimators that repair it (`phiTauHat_unbiasedG`).
- M3 against M4, and against Jewell's hierarchical model as the standard
  method for this situation.

**S4. Choosing cohorts** (Findings 6, 14).
Start from finer units (say 40) with similar levels in clusters.
- Every unit alone, all pooled, k-means on the estimates, and intervals by
  dynamic programming (`pool_optimal_contiguous`,
  `blend_optimal_contiguous`).
- The merge rule `1/d > 1/V + 1/τ²` (`merge_iff`) with `d` known and with
  `d` estimated.
- Measure the winner's curse: MSE promised by the chosen partition against
  MSE delivered on fresh data. This is an open question in the README.

**S5. Balance.** How far off balance the correlated blend is in the world,
and what rescaling to restore it costs in MSE. One small table; may end up
as a panel in S1.

## 4. From theorem to practice: where we stand

The triage that decides what to prove next. To be revised after each study.

| Result | Usable today? | Missing |
|---|---|---|
| BS special case, balance | yes | |
| `z` and GLS weights from `K` (eq. (26)) | with known `K` | plug-in behaviour (S1) |
| Unbiased estimators (39), `nᵢⱼ` | yes, but noisy: `J(J+1)/2` covariances | a structured estimator (G1) |
| Damped `K̂ ≻ 0` | yes | how to choose the damping `θ` (S1, G2) |
| `z > 1`, negative `b` | diagnosis only | what to do then (G3) |
| Equal covariances: closed form | yes once `c` is estimated | G1 |
| Unequal lengths | yes | |
| Group levels, `τ̂²` bias, pairs | identifies `φτ²` from one pair of each kind | how to combine all pairs (G4) |
| Merge rule | needs the unknown `d` | a rule from data (G5) |
| Optimal cohorts are intervals | of the *true* levels | sorting by estimates (G5) |
| Consistency iff `ρ ⪰ 0` | as an input check in the code | |
| True MSE of the blend | for the level `μⱼ` | next year's outcome (G6) |
| Balance under correlation | no | G7 |

**Gaps: candidate theorems.** Small ones first. A study may show that a gap
does not matter in practice, in which case it is dropped.

- **G1. One common covariance.** The average of the pairwise estimators
  (39) is unbiased for a common `c` (immediate from `KHat_unbiased`); which
  weights minimise its variance is a real question. Likely the most useful
  single addition: one extra parameter on top of BS.
- **G2. Damping as shrinkage.** MSE of the blend when `K̂` is damped
  towards its diagonal: is there a best `θ`, or at least a safe one?
- **G3. Clipping.** Does clipping `z` to `[0, 1]` ever raise the MSE
  when the true `z` is in `[0, 1]`? (No if `ẑ` is treated as a fixed
  number, since the MSE is a parabola in `z`; open when `ẑ` depends on the
  same data.)
- **G4. Pooled pair estimator of `φτ²`.** Unbiased for any weights on the
  pairs; state it, then choose weights.
- **G5. Decisions from data.** The merge rule with `d` replaced by its
  unbiased estimate: probability of a wrong merge, or expected MSE cost.
  Hardest; S4 decides whether it is worth it.
- **G6. Forecasting.** Noise is independent between years, so the MSE of
  predicting next year's `μⱼ,T+1` is the MSE for `μⱼ` plus `σ²ⱼ,T+1`, and
  the same `z` is optimal. Short, and it is what a premium actually is.
- **G7. Balance.** The best balanced blend under correlation (minimise MSE
  subject to the balance constraint), and its cost.

## 5. Code

- `studies/credibility.py`: the reference implementation (data → estimators
  → damped `K̂` → `b`, `z` → rates), numpy only, readable next to the
  handbook: one function per handbook result, named after it.
- `studies/world.py`: the generator. `studies/data/portfolio.csv`: the
  showcase dataset. `studies/sN_*.py`: one script per study, writing
  `studies/results/sN.md` with its table and figure.
- **Tests are the proved identities**, checked to machine precision: BS at
  `ρ = 0`; balance; `b₁ = z₁/(z₁+z₂)`; the equal-covariance closed form;
  eq. (26) equals the minimiser of the MSE; `K̂ ≻ 0` after damping. Run in
  CI, so the code cannot drift from the Lean statements.
- Python, because the cloud sessions and CI can run it today (R is not
  installed there). An R port for actuaries can follow once the results
  are stable.

## 6. Order of work

One chat per step. These need no Lean, except the gap theorems.

- [ ] 1. `credibility.py` with the identity tests (oracle formulas only).
- [ ] 2. `world.py`, the showcase dataset, S0 with the oracle columns of
  the ladder.
- [ ] 3. Estimators and plug-in; S1. Decide G1–G3 from what it shows.
- [ ] 4. S2 and S3.
- [ ] 5. S4 (and S5 if not folded into S1).
- [ ] 6. Prove the gaps the studies point at (Lean chats).
- [ ] 7. Write-up: the ladder table and one figure per study as the worked
  example in the handbook; a "Studies" page on the site; later the preprint.

## 7. Open choices for the owner

1. Python first (default above), or R from the start?
2. The story of the world: lines of business × regions, or something
   closer to the thesis's travel-insurance example?
3. Is Jewell's hierarchical model the right standard to compare with in
   S3, or is plain BS per group enough?
4. Should the showcase dataset stay purely simulated, or should a public
   dataset be added later as a second illustration?
