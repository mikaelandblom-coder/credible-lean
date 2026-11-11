#!/usr/bin/env python3
"""Regenerate PROGRESS.md from the Lean sources.

One row per theorem/lemma: thesis equations (from its docstring), Lean name,
and whether its proof still contains `sorry`. A last section lists theorem
names that occur in several namespaces: the refactoring backlog of CLAUDE.md
(Architecture), where a special case should be a corollary of its general
version.

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
    "wtot_pos": "`Model.wtot_pos` has no model in its statement, so it cannot call "
    "the `Unequal` one (that needs a whole `Unequal` model); both are one-line `Finset.sum_pos`",
    "memLp_trueMean": "deleting `Model.Noise.memLp_trueMean` for the `Unequal` one "
    "(via `toUnequal`) would add `[Fintype T]` to `memLp_obs` and `cov_γ_obs`",
    "cov_trueMean": "different statements (τ²I vs `L_G`); the `NoiseG` one is one line "
    "from the Core layer, which gets it from the `Unequal` one",
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
