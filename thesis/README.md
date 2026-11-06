# Thesis source

**Published version:** M. Andblom, *Generalized Bühlmann–Straub credibility
theory for correlated data*, Master Thesis in Actuarial Mathematics 2023:2,
Stockholm University, February 2023. Permanent link (DiVA):
<https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872>

`original/` holds the LaTeX source of the thesis, kept unchanged as the
reference for the Lean statements:

- `main.tex` — the full thesis (single file, inline bibliography)
- `*.pdf` — figures (§2.7 numerical example, §3 simulation study)

Equation numbers in the Lean files and `PROGRESS.md` follow `main.tex` as
compiled (article class, every display numbered consecutively).

## `main.tex` vs. the published PDF

`main.tex` is a late draft; the published PDF is slightly newer. Checked
2026-11-06 (text only, not figures): the mathematics and the prose of every
section are the same. The differences are editorial:

- **Equation numbers.** The published PDF numbers only the 46 labelled
  equations, so its numbers differ from ours. Mapping for the ones the Lean
  files cite (— = unnumbered in the PDF):

  | `main.tex` | 7 | 10 | 23 | 26 | 32 | 36 | 37 | 44 | 51 | 58–59 | 60 | 61 | 62 | 63 | 64 | 73 | 78 | 81 | 85 | 87 | 115–120 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | published | 6 | 7 | 15 | 16 | 18 | 20 | 21 | 22 | 23 | — | 24 | 25 | 26 | 27 | 28 | — | 31 | 32 | 33 | 34 | — |

- **References.** The PDF has 7 consolidated references with page numbers in
  the citation ("[2] page 81"); `main.tex` has one `\bibitem` per cited page.
- **Wording.** §2.4: "second covariance tensor `K̄`" → "covariance matrix"
  (the published wording is the correct one). §2.2: "an introduction to the
  classical results" → "to classical results"; the sentence "We will use
  similar notation in the proposed model." (end of §2.2.2) is dropped.
- **Front matter.** The PDF uses the department's series cover, dated
  February 2023, and lists only the supervisor (Filip Lindskog); `main.tex`
  has its own title page with the external supervisor (Jakub Repiar).

## Notes for the blueprint

The condensed version will be the blueprint (`blueprint/`, planned): §2 cut
down, with `\lean{}` tags and the `FINDINGS.md` results as remarks. Open
points from the original review that still apply to that rewrite (the rest
were applied in the published version or concern §3):

- Open §2.2.1 with "Classical setting: Bühlmann–Straub" and say clearly that
  the aim is to extend it to correlated data.
- Define "cohort" (the index `j`) once and stick to it; the literature also
  says group, subportfolio or risk.
- §2.7: rewrite the two-cohort credibility factor (`main.tex` eq. (79)) in a
  readable form.
- §2.8: name the four covariance terms (e.g. `T₁ … T₄`) instead of circled
  numbers.
- Open question: would a single correlation parameter (equicorrelation, as in
  the §3 simulation) be better in practice?
