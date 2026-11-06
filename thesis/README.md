# Thesis source

`original/` holds the thesis as submitted (Stockholm University, 2023:2), kept
unchanged as the reference for the Lean statements:

- `main.tex` — the full thesis (single file, inline bibliography)
- `*.pdf` — figures (§2.7 numerical example, §3 simulation study)
- `review-comments.txt` — reviewer/supervisor notes, not yet applied

Equation numbers in the Lean files and `PROGRESS.md` follow `main.tex` as
compiled (article class, numbered consecutively).

The condensed version will be the blueprint (`blueprint/`, planned): §2 cut
down, with `\lean{}` tags and the `FINDINGS.md` results as remarks. It can also
pick up the relevant items from `review-comments.txt`.
