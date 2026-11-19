#!/usr/bin/env python3
"""Regenerate PROGRESS.md from the Lean sources.

One row per theorem/lemma: thesis equations (from its docstring), Lean name,
and whether its proof still contains `sorry`. A last section lists theorem
names that occur in several namespaces: the refactoring backlog of CLAUDE.md
(Architecture), where a special case should be a corollary of its general
version. A section "What the count means" gives three counts that do not grow
with special cases: main results (blueprint theorems with a proof of their
own), substantial Lean proofs, and findings backed by Lean.

    python3 scripts/progress.py          # rewrite PROGRESS.md
    python3 scripts/progress.py --check  # exit 1 if PROGRESS.md is stale
    python3 scripts/progress.py --proved # print the names counted as proved
    python3 scripts/progress.py --dupes  # print the open backlog groups
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Credibility"
OUT = ROOT / "PROGRESS.md"

# Suggested order from CLAUDE.md.
ORDER = ["Blend", "Weights", "TwoCohorts", "Model", "BuhlmannStraub"]

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|structure|instance|example)\s+([^\s:({\[]+)",
    re.M,
)
BOUNDARY = re.compile(r"^(?:/--|end\b|section\b|namespace\b|variable\b|open\b)", re.M)
NS = re.compile(r"^(namespace|section|end)\b[ \t]*(\S*)", re.M)


def namespaces(text: str):
    """(position, current namespace) after each namespace/section/end line."""
    stack, out = [], []
    for m in NS.finditer(text):
        kind, name = m.group(1), m.group(2)
        if kind == "end":
            if stack:
                stack.pop()
        else:
            stack.append(name if kind == "namespace" else None)
        out.append((m.start(), ".".join(n for n in stack if n)))
    return out


def eq_refs(doc: str) -> str:
    """Pull equation numbers like (7), (24)–(25) out of a docstring."""
    nums = re.findall(r"\((\d+)\)", doc)
    seen = []
    for n in nums:
        if n not in seen:
            seen.append(n)
    return ", ".join(f"({n})" for n in seen)


def short(doc: str) -> str:
    text = " ".join(doc.split())
    text = re.split(r"\.\s+(?=[A-Z])", text)[0].rstrip(".")
    return text.replace("|", "\\|")


def scan(path: Path):
    text = path.read_text()
    title = re.search(r"^# (.+)$", text, re.M)
    scopes = namespaces(text)
    rows = []
    matches = list(DECL.finditer(text))
    for m in matches:
        kind, name = m.group(1), m.group(2)
        if kind not in ("theorem", "lemma"):
            continue
        # proof body: up to the next declaration or boundary
        rest = text[m.end():]
        stops = [x.start() for x in (DECL.search(rest), BOUNDARY.search(rest)) if x]
        body = rest[: min(stops)] if stops else rest
        before = text[: m.start()].rstrip()
        doc = ""
        if before.endswith("-/"):
            start = before.rfind("/--")
            if start != -1:
                doc = before[start + 3 : -2]
        ns = ""
        for pos, cur in scopes:
            if pos > m.start():
                break
            ns = cur
        prefix = ns + "." if ns else ""
        rows.append(
            dict(
                name=prefix + name if not name.startswith(prefix) else name,
                done=not re.search(r"\bsorry\b", body),
                eqs=eq_refs(doc),
                note=short(doc),
                body=body,
            )
        )
    return (title.group(1) if title else path.stem), rows


def refers_to_namesake(row) -> bool:
    """Does the proof mention its own short name qualified (`Core.x`,
    `M.toUnequal.x`)? A theorem cannot use itself, so this is a namesake."""
    leaf = row["name"].rsplit(".", 1)[-1]
    return bool(re.search(r"\." + re.escape(leaf) + r"(?![\w'!?₀-₉])", row["body"]))


# Groups that share a name but are not duplicates to merge: neither copy can be
# a corollary of the other without changing a statement. Reviewed 2026-11-11.
EXEMPT = {
    "blup_mse_optimal": "the scalar `Core.Estimates` result (common mean, index `J`) and the matrix `CoreVector.VecEstimates` one (component means, index `J × P`, Loewner order) are about different random variables; deriving the scalar one through `P = Unit` would need reindexing `J ≃ J × Unit` and only lengthen it",
    "mse_blend_eq_blup_add": "the scalar `Core.Estimates` result (common mean, index `J`) and the matrix `CoreVector.VecEstimates` one (component means, index `J × P`, Loewner order) are about different random variables; deriving the scalar one through `P = Unit` would need reindexing `J ≃ J × Unit` and only lengthen it",
    "bestZ_optimal": "the scalar `BlendMoments` result is thesis eq. (6)/(7) with a short direct proof; the `VecBlendMoments` (matrix) one needs symmetry hypotheses and contains it via `BlendMoments.toVec`, so deriving the scalar one from it would only lengthen it",
    "bestZ_unique": "the scalar `BlendMoments` result is thesis eq. (6)/(7) with a short direct proof; the `VecBlendMoments` (matrix) one needs symmetry hypotheses and contains it via `BlendMoments.toVec`, so deriving the scalar one from it would only lengthen it",
    "errVar_eq": "the scalar `BlendMoments` result is thesis eq. (6)/(7) with a short direct proof; the `VecBlendMoments` (matrix) one needs symmetry hypotheses and contains it via `BlendMoments.toVec`, so deriving the scalar one from it would only lengthen it",
    "wtot_pos": "`Model.wtot_pos` has no model in its statement, so it cannot call "
    "the `Unequal` one (that needs a whole `Unequal` model); both are one-line `Finset.sum_pos`",
    "memLp_trueMean": "deleting `Model.Noise.memLp_trueMean` for the `Unequal` one "
    "(via `toUnequal`) would add `[Fintype T]` to `memLp_obs` and `cov_γ_obs`",
    "cov_obs": "`Model.Noise.cov_obs` and `Model.NoiseG.cov_obs` are about different random variables (without and with group effects); each is the case `Tⱼ = T` of its own `Unequal` twin (`cov_obsVal`)",
    "memLp_obs": "`Model.Noise.memLp_obs` and `Model.NoiseG.memLp_obs` are about different random variables (without and with group effects); each is the case `Tⱼ = T` of its own `Unequal` twin (`memLp_obsVal`)",
    "obs_mean": "`Model.Noise.obs_mean` and `Model.NoiseG.obs_mean` are about different random variables (without and with group effects); each is the case `Tⱼ = T` of its own `Unequal` twin (`obsVal_mean`)",
    "toUnequal_blend": "the bridges `Model.Noise.toUnequal_blend` and `Model.NoiseG.toUnequal_blend` to `Tⱼ = T` are for different random variables (without and with group effects)",
    "toUnequal_cohortEst": "the bridges `Model.Noise.toUnequal_cohortEst` and `Model.NoiseG.toUnequal_cohortEst` to `Tⱼ = T` are for different random variables (without and with group effects)",
    "toUnequal_obsVal": "the bridges `Model.Noise.toUnequal_obsVal` and `Model.NoiseG.toUnequal_obsVal` to `Tⱼ = T` are for different random variables (without and with group effects)",
    "toUnequal_portEst": "the bridges `Model.Noise.toUnequal_portEst` and `Model.NoiseG.toUnequal_portEst` to `Tⱼ = T` are for different random variables (without and with group effects)",
    "K_eq_errCov": "`Unequal.K_eq_errCov` and `Shock.K_eq_errCov` split two different models' `K` (period-fixed correlations against shock plus process noise); neither table is a case of the other",
    "cov_symm": "`Model.cov_symm` and `Shock.cov_symm` are the symmetry of two different covariance tables (eq. (16) against shock plus process noise); neither is a case of the other",
    "toUnequal_trueMean": "the bridges `Model.Noise.toUnequal_trueMean` and `Model.NoiseG.toUnequal_trueMean` to `Tⱼ = T` are for different random variables (without and with group effects)",
}


def duplicates(files):
    """Groups of theorems sharing a short name, as (leaf, rows, open)."""
    groups = {}
    for f in files:
        for r in scan(f)[1]:
            groups.setdefault(r["name"].rsplit(".", 1)[-1], []).append(dict(r, file=f.stem))
    out = []
    for leaf in sorted(groups):
        rows = groups[leaf]
        if len(rows) > 1:
            is_open = leaf not in EXEMPT and not any(refers_to_namesake(r) for r in rows)
            out.append((leaf, rows, is_open))
    return out


def backlog(files) -> str:
    dups = duplicates(files)
    n_open = sum(o for *_, o in dups)
    lines = [
        "## Refactoring backlog",
        "",
        "Theorem names that occur in several namespaces (CLAUDE.md, Architecture).",
        "↳ marks a copy whose proof refers to a namesake (a corollary, probably",
        "done); a group with no ↳ is open. `scripts/CheckUses.lean` checks the",
        "blueprint `\\uses` edges exactly; this list is a textual hint.",
        "",
        f"**{n_open} open / {len(dups)} groups.**",
        "",
        "| | Name | Copies |",
        "|---|---|---|",
    ]
    for leaf, rows, is_open in dups:
        copies = ", ".join(
            f"{'↳ ' if refers_to_namesake(r) else ''}`{r['name']}` ({r['file']})" for r in rows
        )
        mark = "➖" if leaf in EXEMPT else "⬜" if is_open else "✅"
        lines.append(f"| {mark} | `{leaf}` | {copies} |")
    exempt = [leaf for leaf, *_ in dups if leaf in EXEMPT]
    if exempt:
        lines += ["", "➖ accepted, not a duplicate to merge (`EXEMPT` in `scripts/progress.py`):", ""]
        lines += [f"- `{leaf}`: {EXEMPT[leaf]}." for leaf in exempt]
    return "\n".join(lines)


SKIP_LINE = re.compile(r"^\s*(?:--|omit\b|@\[|set_option\b|attribute\b)")
LONG = 10  # a proof of at least this many lines counts as substantial
SHORT = 4  # a blueprint theorem whose Lean proofs are all shorter is flagged


def proof_lines(row) -> int:
    """Lines of the proof: what follows the first `:=`, without blank lines,
    comments and the `omit … in` / attribute lines of the next declaration."""
    body = row["body"]
    i = body.find(":=")
    proof = body[i + 2 :] if i != -1 else body
    proof = re.sub(r"/-.*?-/", "", proof, flags=re.S)
    proof = re.sub(r"^\s*by\b", "", proof)
    return sum(1 for l in proof.split("\n") if l.strip() and not SKIP_LINE.match(l))


def blueprint_statements():
    """(kind, label, title, \\lean names, proof \\uses, proved) per blueprint environment."""
    from blueprint_check import CONTENT, ENV, PROOF  # lazy: blueprint_check imports this file

    text = re.sub(r"(?<!\\)%.*", "", CONTENT.read_text())
    out = []
    for m in ENV.finditer(text):
        kind, body = m.group(1), m.group(2)
        label = (re.search(r"\\label\{([^}]*)\}", body) or [None, "?"])[1]
        title = (re.match(r"\s*\[([^\]]*)\]", body) or [None, ""])[1]
        names = [n.strip() for g in re.findall(r"\\lean\{([^}]*)\}", body) for n in g.split(",")]
        p = PROOF.match(text, m.end()) if kind != "definition" else None
        proved = bool(p and re.search(r"\\leanok\b", p.group(1)))
        out.append((kind, label, title, [n for n in names if n], proved))
    return out, text


def findings_backed(text, proved_labels):
    """Finding numbers whose blueprint remark \\uses a proved statement."""
    backed = set()
    for m in re.finditer(r"\\begin\{remark\}\[Findings? ([^\]]*)\](.*?)\\end\{remark\}", text, re.S):
        nums = re.match(r"(\d+)(?:--(\d+))?", m.group(1))
        if not nums:
            continue
        used = [u.strip() for g in re.findall(r"\\uses\{([^}]*)\}", m.group(2)) for u in g.split(",")]
        if any(u in proved_labels for u in used):
            lo = int(nums.group(1))
            backed.update(range(lo, int(nums.group(2) or lo) + 1))
    return backed


def weight(files):
    """The three counts of 'what is really proved' and the short-proof flags."""
    rows = {r["name"]: r for f in files for r in scan(f)[1]}
    lines = {n: proof_lines(r) for n, r in rows.items() if r["done"]}
    long_ = sum(1 for k in lines.values() if k >= LONG)
    stmts, text = blueprint_statements()
    thms = [(lab, title, ns) for kind, lab, title, ns, ok in stmts if kind == "theorem" and ok]
    flagged = [
        (lab, title, max(lines.get(n, 0) for n in ns))
        for lab, title, ns in thms
        if ns and max(lines.get(n, 0) for n in ns) < SHORT
    ]
    proved_labels = {lab for kind, lab, _, _, ok in stmts if ok}
    numbers = {int(n) for n in re.findall(r"^(\d+)\. \*\*", (ROOT / "FINDINGS.md").read_text(), re.M)}
    backed = findings_backed(text, proved_labels) & numbers
    return dict(thms=len(thms), own=len(thms) - len(flagged), long=long_, decls=len(lines),
                backed=backed, findings=len(numbers), flagged=flagged)


def weight_section(w) -> list:
    out = [
        "## What the count means",
        "",
        "Every special case is its own Lean declaration, so the count above",
        "grows with corollaries. Three numbers that do not:",
        "",
        "| | Count | How it is measured |",
        "|---|---|---|",
        f"| Main results | {w['own']} | proved blueprint statements labelled *theorem*, one per statement (special cases are corollaries or lemmas there), with a Lean proof of at least {SHORT} lines; {w['thms']} counting thesis-facing restatements of a general result (listed below) |",
        f"| Substantial proofs | {w['long']} | Lean proofs of at least {LONG} lines (of {w['decls']} proved) |",
        f"| Findings backed by Lean | {len(w['backed'])} / {w['findings']} | entries of `FINDINGS.md` whose blueprint remark `\\uses` a proved statement: what is new against the thesis (missing: {', '.join(str(n) for n in sorted(set(range(1, w['findings'] + 1)) - w['backed'])) or 'none'}) |",
        "",
    ]
    if w["flagged"]:
        out += [
            f"Blueprint theorems whose Lean proofs are all under {SHORT} lines, not counted as",
            "main results: mostly thesis-facing statements proved from a general result",
            "(CLAUDE.md, Architecture); relabel as corollary where the statement is not the point.",
            "",
            *[f"- `{lab}` ({k} lines): {title}" for lab, title, k in w["flagged"]],
            "",
        ]
    return out


def render() -> str:
    files = sorted(SRC.glob("*.lean"), key=lambda p: (ORDER.index(p.stem) if p.stem in ORDER else 99, p.stem))
    sections, total, done = [], 0, 0
    summary = ["| File | Proved | Total |", "|---|---|---|"]
    for f in files:
        title, rows = scan(f)
        n, k = len(rows), sum(r["done"] for r in rows)
        total, done = total + n, done + k
        mark = " ✅" if n and k == n else ""
        summary.append(f"| `{f.stem}` | {k} | {n}{mark} |")
        lines = [f"## `{f.stem}` — {title}", "", "| | Lean name | Eq. | Note |", "|---|---|---|---|"]
        for r in rows:
            lines.append(f"| {'✅' if r['done'] else '⬜'} | `{r['name']}` | {r['eqs']} | {r['note']} |")
        sections.append("\n".join(lines))
    head = [
        "# Progress",
        "",
        "Generated by `python3 scripts/progress.py` — do not edit by hand.",
        "✅ proved, ⬜ still `sorry`. Equation numbers refer to the thesis.",
        "",
        f"**{done} / {total} theorems proved.**",
        "",
        *summary,
        "",
        *weight_section(weight(files)),
    ]
    sections.append(backlog(files))
    return "\n".join(head) + "\n\n" + "\n\n".join(sections) + "\n"


def proved():
    """Fully qualified names of the theorems counted as proved."""
    return [r["name"] for f in sorted(SRC.glob("*.lean")) for r in scan(f)[1] if r["done"]]


if __name__ == "__main__":
    if "--dupes" in sys.argv:
        for leaf, rows, is_open in duplicates(sorted(SRC.glob("*.lean"))):
            if is_open:
                print(leaf + ": " + ", ".join(r["name"] for r in rows))
        sys.exit(0)
    if "--proved" in sys.argv:
        print("\n".join(proved()))
        sys.exit(0)
    new = render()
    if "--check" in sys.argv:
        if not OUT.exists() or OUT.read_text() != new:
            print("PROGRESS.md is stale; run python3 scripts/progress.py")
            sys.exit(1)
        print("PROGRESS.md is up to date")
    else:
        OUT.write_text(new)
        print(f"wrote {OUT.relative_to(ROOT)}")
