# Thesis source

**Published version:** M. Andblom, *Generalized Bühlmann–Straub credibility
theory for correlated data*, Master Thesis in Actuarial Mathematics 2023:2,
Stockholm University, February 2023. Permanent link (DiVA):
<https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872>

`original/` holds the final LaTeX source, kept unchanged as the reference for
the Lean statements:

- `main.tex`: the full thesis (single file, inline bibliography). Its text
  matches the published PDF word for word. The only difference is the cover,
  which the department adds.
- `*.pdf`: figures (§2.7 numerical example, §3 simulation study)
- `code/`: the R scripts behind the figures. `two_cohorts_example.R` covers
  §2.7 and `simulation_study.R` covers §3. They are renamed from
  `2d example v2.R` and `sim study 2 less heavy.R`, with unchanged content.

`presentation/` holds the Beamer slides from the thesis defence
(`main.tex`, `mystyle.sty`, logos; `Figures` links to `original/`). They are a
compact summary of §2. They also state the two-cohort results in their
simplest form: `z₁ = 1/(1 + κ₁ − √(κ₁κ₂)ρ)` and `b₁ = z₁/(z₁ + z₂)`.

Equation numbers in the Lean files and `PROGRESS.md` follow `main.tex` as
compiled. Only the 46 labelled equations are numbered, the same as in the
published PDF. Unnumbered displays are cited by their position, for example
"just before (24)".

An earlier draft (until commit `a3f65b2`) numbered every display and used the
opposite notation: `K̄` for `cov(μ̂ᵢ, μ̂ⱼ)` and primes on the noise terms `ε`.
The final version, and the Lean code, use `K` for `cov(μ̂ᵢ, μ̂ⱼ)` and `K̄ᵢⱼᵗˢ`
for `cov(μᵢₜ, μⱼₛ)`.

## Notes for the blueprint

The condensed version will be the blueprint (`blueprint/`, planned): §2 cut
down, with `\lean{}` tags and the `FINDINGS.md` results as remarks. Some open
points from the original review still apply to that rewrite. The rest were
applied in the final version or concern §3:

- Open §2.2.1 with "Classical setting: Bühlmann–Straub", and say clearly that
  the aim is to extend it to correlated data.
- Define "cohort" (the index `j`) once and use it consistently. The
  literature also says group, subportfolio or risk.
- §2.7: replace the long display before (32) with the short forms from the
  slides.
- §2.8: name the four covariance terms (for example `T₁ … T₄`) instead of
  using circled numbers.
- Typo in §2.2.1: `w_{j∗} = Σⱼ wᵢⱼ` should sum over `i`.
- Open question: would a single correlation parameter (equicorrelation, as in
  the §3 simulation) be better in practice?
