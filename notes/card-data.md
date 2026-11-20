# Monthly card data: a toolbox of models, then a thesis

Planning note, 2026-11-20 (owner). Not in the thesis. Aim: build in the repo
the theory for **every** reasonable alternative below, so that a master
student can test them on the owner's monthly travel-insurance card data and
choose what works. The repo proves "if model X, then these weights, this MSE,
these unbiased estimators"; the student decides from the data which X holds,
and checks our statements by hand (the human review; the repo is guidance,
not to be trusted blindly). After the theory: one focused thesis proposal
that cites Lean names (`studies/thesis-topics/` holds the earlier
three-topic draft, to be replaced).

## The data and the questions

Monthly aggregates per card product `j` and month `t`: cards in force `wⱼₜ`,
claim counts `Nⱼₜ`, paid amounts `Sⱼₜ`, claim type, reporting dates. Cards
start and stop within the window. Travel demand varies strongly from year to
year, with the pandemic as the extreme case.

- **Q1. Form of the correlation.** It may shrink with volume (thesis eq. (16)), or come from a
  common shock that does not (Finding 23).
- **Q2. Trends.** A persistent common demand factor.
- **Q3. Seasonality.** Aggregate to years, or model the months, with the season *estimated*?
- **Q4. Frequency and severity.** Model them separately, combined, or jointly?
- **Q5. New and decommissioned cards.**

**Target (owner):** the next underwriting year, i.e. card `j`'s total over the
next 12 months.

## The toolbox: every alternative is a switch

| Switch | Alternatives | Theory step |
|---|---|---|
| Correlation form | thesis `σσρ`, shock + process noise, common factor | 3 (thesis: `Unequal`; shock: `Shock`) |
| Demand | latent factor; known signal `Dₜ` with card-specific sensitivity `λⱼ`; both; known signal with equal sensitivity (an exposure adjustment) | 3b (signal), 3 (latent) |
| Latent factor over time | independent months, AR(1) (mean-reverting: no long-term trend), random walk, break at known dates, level + season, general `Γ ⪰ 0` | 3 (general `Γ`, others are instances) |
| Loadings | equal, card-specific `λⱼ` | 3, 4 |
| Season | none, known index, estimated fixed effects | 1 |
| Aggregation | monthly, annual totals | 1 (annual = restricted weights) |
| Frequency × severity | combined burning cost, separate, joint (vector) | 6 |
| Card set | balanced, entry and exit (`obs j ⊆ T`) | 3 (built in) |
| Predictor form | thesis blend `zμ̂ⱼ + (1-z)μ̂`, full best linear unbiased predictor | 2 |

Theory gives each switch its `K`, its predictor and its unbiased estimators.
The app (Step 7) offers each as a fit option. The student chooses by
out-of-sample prediction on the real data.

## Already in the repo (reuse, don't redo)

| Need | Result | Gap for this data |
|---|---|---|
| Shock that does not shrink with volume | `Shock.lean`: `K_apply`, `K_posDef`, `crossHat_unbiased`, `s2Hat_unbiased`, `tauHat_unbiased` | Shocks independent between months (`δₜₛ`); every card in every month (`w > 0`) |
| Cards observed in different months | `Unequal` (`obs j ⊆ T`) | Not combined with the shock |
| Known common trend | `Trend.lean` (`scale`, `detrend`, `bestZ_detrend`) | One factor `(1+g)^t`, not one per month |
| Estimated trend moves relativities | Finding 21 | Counterexample only |
| Best linear unbiased predictor | `Core.blupWeight_optimal`, `Core.linMse` | Target is row `j` of `L` (a level), and one common mean (`Σ dᵢ = 1`) |
| Several fixed means | `CoreVector`: unbiasedness `(stack J P)ᵀ A = 1`, `blupW_optimal` | Design is "one mean per component", not a general design |
| Frequency × severity | `CoreVector.lean`, `CoreVectorMoments.lean`, Finding 22 | No shock model per component |
| Moment layer | `Core.Estimates` | Requires `cov(level, est) = cov(level, level)`: the noise uncorrelated with the target. A persistent factor breaks this |

## Steps

Prove each fact once at the most general level that still reads as
actuarial math (CLAUDE.md, Architecture). Statements are the spec. A
false expectation below is a finding, not something to weaken.

### Step 0. Literature (Default, docs, before any Lean)
Record the results in `studies/literature.md` (new section). Search:
- **BLUP with fixed effects and a general target:** Goldberger 1962, Henderson,
  Harville 1976; universal kriging.
- **Dynamic factor models:** Stock & Watson; common factor with loadings, §9 of the literature file.
- **Evolutionary and state-space credibility:** Gerber & Jones 1975, Sundt 1981,
  Bühlmann & Gisler ch. 9.
- **Seasonality in credibility and ratemaking.**
- **Regression credibility with a covariate, and random-coefficient models:**
  Hachemeister 1975, Swamy 1970. Also look for public travel demand indices.
- **Panels with entry and exit:** Frees.

Question: is credibility with a common AR(1) factor, or with estimated seasonal
effects, already done?

**Done (2026-11-20), `studies/literature.md` §10.** Credibility with a common AR(1)
factor: not found (dynamic models evolve each risk's own level; common-effect models have one
permanent effect). Seasonal credibility: Ledolter, Klugman & Lee (1991), independent groups,
log scale, heuristic shrinkage. Step 1 is Goldberger (1962) / Harville (1976) / universal
kriging. Step 3b is mostly in the repo already (see there).

### Step 1. Core: general target and fixed effects (Lean, Core level)
**Status (2026-11-20):** done in `Credibility/Blup.lean`: `Core.unbiased_iff`,
`Core.blup_optimal` (with `predMse_eq_blup_add`, `blup_unique`), `Core.predMse_blup`;
`Core.blupWeight_optimal` and `CoreVector.blupW_optimal` are now corollaries
(`blupWeight_eq_blup`, `blupW_mulVec_eq_blup`). Restricted predictors: aggregated data
(`predMse_blup_le_aggregate`, exact loss `predMse_aggregate_eq_blup_add`), nested designs
(`blup_eq_blup_iff_of_nested`: the Kruskal-type iff for Step 2; `predMse_blup_nested`: the
price of a finer design when the coarse one is right); the thesis blend was already
`Core.errVar_eq_blupWeight_add`. Moment layer: `Credibility/BlupMoments.lean`
(`Core.Target`, `Target.mse_portLin`, `blup_mse_optimal`, `mse_blup`); `Core.Estimates` is its
case `X = 1` (`Estimates.toTarget`). **Step 1 done.**
A generalization of `Core.linMse` and `Core.blupWeight`, with the data
indexed by observed cells.
- **General target:** predict a random `Y`, given `K = Cov(x)`, `ℓ = Cov(x, Y)`
  and `v = Var Y`. Then `MSE(d) = dᵀKd − 2dᵀℓ + v`.
- **Fixed effects:** `E x = Xβ` and `E Y = x₀ᵀβ` for unknown `β` (season: one
  `β` per calendar month; a design matrix `X`). Unbiased for every `β` iff
  `Xᵀd = x₀`.
- **Optimal weights:** `d* = K⁻¹ℓ + K⁻¹X(XᵀK⁻¹X)⁻¹(x₀ − XᵀK⁻¹ℓ)`, the
  universal-kriging / Goldberger weights. `MSE(d) = MSE(d*) + (d − d*)ᵀK(d − d*)`.
  The error from estimating `β` is included. The main theorem is Goldberger's (1962) and
  Harville's (1976) predictor of `x₀ᵀβ + random part`; the formula for `d*` is theirs, the
  MSE identity in this form and the corollaries are ours to prove.
- **Corollaries:** `X = 1`, `x₀ = 1`, `ℓ = Lⱼ`, `v = Lⱼⱼ` gives
  `Core.blupWeight_optimal`. `CoreVector.blupW_optimal` should be the case
  `X = stack`. Rule of three: scalar, vector and seasonal designs.
- **Restricted predictors:**
  - **Annual aggregation:** weights constant within a card-year. Corollary:
    never better than `d*` with known covariances (Q3, known parameters).
  - **Thesis blend:** a restricted form; keep it as the readable predictor.
- **Moment layer:** a generalization of `Core.Estimates` that drops
  `cov(level, est) = cov(level, level)`. True MSE for any random variables
  with these moments.

### Step 2. The season and the 12-month target (Lean)
Mean `E Xⱼₜ = β_{m(t)}`, or multiplicative on exposure, with the effective
volume `wⱼₜ` times the season. Settle the form in the chat: additive on the
rate is linear; multiplicative needs a plug-in or a log scale, so say which.
- **Expected:** the predictor never depends on the value of `β`, but the season design can
  change the *weights*. With one column per calendar month, unbiasedness asks each month's
  weights to sum to 1. The seasonal and one-mean predictors coincide iff the one-mean `d*`
  already satisfies these month-wise constraints (a Kruskal-type condition). Sufficient: cards
  observed in whole years with `K` and `ℓ` invariant under shifting the calendar. That is rare:
  the noise `sᵢ²/wᵢₜ` changes with seasonal volume, and an AR(1) factor favours recent months.
  So prove the iff, and expect an easy counterexample to "the season drops out". The iff
  in general form is `Core.blup_eq_blup_iff_of_nested` (`X₁ = X₂M`, here `M` = column of
  ones over months); Step 2 only instantiates it and gives the counterexample.
- **Form:** Lean takes the season additive on the rate (linear). Ledolter, Klugman & Lee
  (1991) use a multiplicative season on the log scale; that is an app option.
- **Known index `cₜ`:** a corollary of `Unequal` (divide by `cₜ`). This is the
  oracle fit for the app. Under Poisson-type variance the weight is expected
  claims `cₜwⱼₜ`, not cards in force.

### Step 3. The common factor model (Lean, main step; maybe two chats)
One table that generalizes `Shock` and covers the factor-over-time switch:

`cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼ Γₜₛ + δₜₛ Cᵢⱼ + δₜₛ δᵢⱼ sᵢ²/wᵢₜ + τ²δᵢⱼ`,

for observed cells only (`t ∈ obs i`, `s ∈ obs j`). Here `Γ ⪰ 0` is the
factor's autocovariance over all months, past and future. Instances:
- `Γ = 0`: `Shock`;
- `C = 0`, `Γ = I`: `Shock` with rank-one `C = λλᵀ`;
- AR(1): `Γₜₛ = γφ^|t−s|`;
- a break at known dates: a block `Γ`.

To prove:
- **`K ≻ 0`:** from `Γ ⪰ 0`, `C ⪰ 0`, `s² > 0`, `τ² > 0`, with the
  `posSemidef_weightedSum` pattern of `Shock`.
- **`ℓ` and `v` for the 12-month target:** they involve `Γ` between past and
  future months. That is the reason for Step 1's general target.
- **Step 1 applied:** the predictor and its MSE as one-line corollaries.
- **Expected finding:** per-month weights can be negative with an AR(1) `Γ` (Pinquet 2020 for
  per-risk AR effects: nonnegative partial autocorrelations suffice to avoid it).
- **For the app:** the predictor has a Kalman-filter form (Zehnwirth 1985, valid without
  normality), so the app need not invert `K` over all cells. The Lean statement stays the
  closed form.
- **Per-card AR(1)** (Rao & Yu 1994; Pinquet): each card's own deviation evolves, cards
  independent in it. A further value of the "latent factor over time" switch: a `Γ` block per
  card instead of `λλᵀ ⊗ Γ`; the same `K ⪰ 0` pattern covers it.

Cell-level data `xⱼₜ` are rates `Nⱼₜ/wⱼₜ` (or `Sⱼₜ/wⱼₜ`).

### Step 3b. A known demand signal with unknown sensitivities (Lean)
The actuary observes overall travel demand `Dₜ`, for example passenger
volumes by year from official statistics. Model:

`E[Xⱼₜ | card] = μⱼ + λⱼ Dₜ`, with `λⱼ = λ̄ + (λⱼ − λ̄)`.

- **Fixed effects:** the portfolio sensitivity `λ̄` and the mean are in
  Step 1's design (`X` gets a `Dₜ` column next to the season).
- **Random effects:** the card's deviations `(μⱼ − μ, λⱼ − λ̄)` have a 2 × 2
  covariance. They give `K` the term `Dₜ Dₛ cov(λᵢ, λⱼ)` and the cross terms.
  This is Hachemeister's regression credibility with `Dₜ` as the covariate
  instead of `t`. **Already covered** for any noise `Φ ≻ 0` over cards × months:
  `CoreVector.hachemeister_bestZ` with design `Yⱼ = [1, Dₜ]`, and
  `CoreVector.blupW_optimal_dotProduct` with `a = (1, D_{T+1})` for the target
  `μⱼ + λⱼD_{T+1}`. New are only the common season columns and a latent factor that also
  enters the target (both via Step 1). Estimator of `cov(λᵢ, λⱼ)`: Swamy (1970), as in Step 5.
- **Combination:** the signal and a latent factor (Step 3) can be combined. A
  signal never captures the whole shock. Either part can be switched off.
- **Expected finding:** conditional on `Dₜ`, the remaining cross-card
  correlation may be small. That is the data question for the student.
- **Forecast:** the 12-month target needs `D_{T+1}`, so `x₀` contains `D_{T+1}`.
  Price as a function of the demand assumption (scenarios), or plug in a
  forecast and add its variance, which is common to all cards. State which.
- **Equal sensitivity** (`λⱼ = λ̄`, known): `Dₜ` is an exposure adjustment, as
  in the known season index of Step 2.
- **Time resolution:** with annual `Dₜ` and monthly data, `Dₜ` is constant
  within a year, so the season carries the within-year shape.

### Step 4. When does the factor cancel? (Lean; Q2, loadings)
Expected: with **equal loadings** and cards observed in the same months, the
factor drops out of card relativities, so ranking cards needs no trend model.
Otherwise there is an exact extra error term.
- **To find:** the exact term, and counterexamples with unequal loadings and
  with a card entering mid-window.
- **Payoff:** the theorem behind "credibility for relativities, a separate
  forecast for the portfolio level".

### Step 5. Estimators (Lean)
Distribution-free, unbiased where possible, via `Expectation.UnbiasedCov` for
the table of Step 3.
- **Lagged cross-products:** for `i ≠ j` they estimate `λᵢλⱼΓ(h)`, which
  generalizes `Shock.crossHat_unbiased`.
- **`s²`:** needs volume variation (`Shock.not_unbiased_s2_of_const`).
- **`τ̂²`:** as `Shock.tauHat`.
- **Identification:** what can be estimated from what. With equal loadings
  only `Γ` matters; `λ` and the scale of `Γ` are confounded. Expect findings.
- **Season `β̂`:** comes from Step 1's GLS (feasible GLS with plug-in `K̂`).
  Its extra cost is for the app.
- **Exited cards (Q5):** keep all their past cells in the fit; they inform the mean, the
  season, `K̂` and, through `K`, the other cards, and only lack a target. The exact
  guarantees treat `obs j` as fixed, so they assume the exit date is independent of the
  claims. Exit driven by results (an optional stopping time) makes them approximate (Frees
  2004). State it as an assumption.

### Step 6. Frequency × severity (Lean, corollary of `CoreVector`)
- **Two tables:** the Step 3 table per component, frequency weighted by
  cards and severity by claim counts, with loadings `λ_F`, `λ_Y` on a common
  or separate factor.
- **Joint `K`:** over cards × {F, Y}.
- **Q4 in theory:** separate equals joint iff no cross-component covariance
  (`CoreVector.blupW_eq_sepW_of_componentBlockDiag`), so the data question is
  "do the residuals cross-correlate?". The combined burning cost is the third
  switch.
- **Optional:** the bias of the product `φ̂ψ̂` as a covariance term (delta
  method), labelled as an approximation.

### Step 7. App: a world like the card data (Default, app)
The world uses the optional distribution layer: Poisson counts, gamma
amounts. It has:
- a monthly season,
- an AR(1) demand factor with an optional break, and an observed demand index `Dₜ` (a noisy
  view of the factor) with card-specific sensitivities,
- equal or unequal loadings,
- cards entering and leaving, with an option for exit driven by results.

The fits are every switch in the toolbox table. They are fitted from
simulated data only, never true parameters; the oracle uses the true ones.
Studies:
- monthly against annual with estimated parameters (Q3);
- the price of estimating the season and the factor;
- separate against joint frequency and severity (Q4);
- what the equal-loadings fit costs when loadings differ.

### Step 8. Documents, then the proposal
Each proved step gets its handbook entry and paper paragraph, or a "Pending"
line, as usual. Then rewrite `studies/thesis-topics/` as one topic,
"Correlation structure of claims across card products":
- research questions Q1–Q5;
- the toolbox as the student's starting point, with Lean names;
- check our statements by hand;
- choose among the switches by out-of-sample prediction.

## Left to the student
- **Number of factors.** One factor or several.
- **Loadings.** Whether they are equal.
- **The pandemic.** As a break, an exclusion, or a large draw.
- **Reporting delay.** For recent months, the easiest scope is developed months only.
- **New cardholders.** Whether they behave differently.
- **Data access.** Public text, with aggregated or anonymized company data by
  agreement.

## Decisions (owner, 2026-11-20)
1. **Target:** the next underwriting year (12 months).
2. **Loadings:** card-specific in the theory; equal loadings as the special case.
3. **The pandemic:** general `Γ`, covering a stationary factor and a break at
   known dates; the data decide.
4. **Seasonality:** estimated, not given.
5. **Tools for all alternatives:** the student explores which works best.
6. **Demand:** a known demand signal with unknown card sensitivities is a
   switch next to the latent factor (Step 3b). AR(1) is kept as the
   mean-reverting latent option.

## Order of chats
- Step 0 (Default).
- Then, in **lean**, one chat per step: 1, 2, 3 (maybe two chats), 3b, 4, 5, 6.
- Step 7 (Default) can start after Step 3.
- Step 8 comes last.
