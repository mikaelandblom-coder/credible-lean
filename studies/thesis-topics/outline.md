# Thesis proposal: status

`proposal.tex` is a master thesis proposal: extensions of the 2023 thesis, tested on card data
(`notes/card-data.md`, Step 8), for a student who knows neither the thesis nor this repository. It
cites handbook results (`\hb{}`), so it goes stale when a direction it calls open is done here, or
when a result changes what a student should derive or check.

## Pending
(Results since the last proposal update that may change a topic, its references or its size.)
- [ ] Crossed levels done (2026-11-26, handbook `res:crossed`, `res:crossed_est`, `res:crossed_pool`; Finding 42):
  the country-tiers topic calls "a crossed tier effect" new ground. Point to the crossed results and
  reword it as applying them to cards (which tiers are comparable across countries), not deriving them.
- [ ] Choosing θ on held-out data (2026-11-27, handbook `res:plugIn_mix`, `res:plugIn_proxy`, `res:heldOut_price`,
  `res:heldOut_bias`; S64): one held-out year is too noisy to beat θ = 1, and a common shock biases it.
  Relevant to "Comparing models on data": a line that the rolling-origin comparison has the same
  power problem, with the exact price as the reason.
- [ ] Vector levels with year shocks (2026-11-27, handbook `res:vecSpread`, `res:lineResid`; S65–S67): the
  frequency × severity topic can start from the corrected moment `Λ̂` (unbiased for any distribution)
  and the damped joint BLUP, rather than derive the fit.
