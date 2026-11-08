#!/usr/bin/env python3
"""Check that the blueprint agrees with the Lean sources.

* every Lean theorem/lemma appears in a blueprint \\lean{...};
* its proof is marked \\leanok exactly when the Lean proof has no `sorry`
  (the same test as scripts/progress.py, so it matches PROGRESS.md);
* every statement with \\lean{...} is marked \\leanok (it is stated in Lean).

Whether the \\lean names really exist is checked by scripts/CheckDecls.lean.

    python3 scripts/blueprint_check.py
    python3 scripts/blueprint_check.py --uses  # input for scripts/CheckUses.lean

`--uses` prints one line per proved blueprint statement whose proof \\uses
other results: `thm₁|thm₂ label=name₁|name₂ …` (its \\lean names, then each
used label with that label's \\lean names). scripts/CheckUses.lean checks
that the Lean proof really refers to each used result, so a special case
marked as a corollary of a general result is one in Lean too.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from progress import SRC, scan  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
CONTENT = ROOT / "blueprint" / "src" / "content.tex"
THM = "theorem|lemma|proposition|corollary"
ENV = re.compile(r"\\begin\{(" + THM + r"|definition)\}(.*?)\\end\{\1\}", re.S)
PROOF = re.compile(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", re.S)


def blueprint():
    """Map each \\lean name to (label, proof ok)."""
    text = re.sub(r"(?<!\\)%.*", "", CONTENT.read_text())
    out, errors = {}, []
    for m in ENV.finditer(text):
        kind, body = m.group(1), m.group(2)
        label = (re.search(r"\\label\{([^}]*)\}", body) or [None, "?"])[1]
        names = [n.strip() for g in re.findall(r"\\lean\{([^}]*)\}", body) for n in g.split(",")]
        stated = bool(re.search(r"\\leanok\b", body))
        if names and not stated:
            errors.append(f"{label}: has \\lean but no \\leanok on the statement")
        if kind == "definition":
            continue
        p = PROOF.match(text, m.end())
        proved = bool(p and re.search(r"\\leanok\b", p.group(1)))
        for n in names:
            out[n] = (label, proved)
    return out, errors


def uses_edges():
    """(proved \\lean names, [(used label, its \\lean names)]) per proved statement."""
    text = re.sub(r"(?<!\\)%.*", "", CONTENT.read_text())
    done = {r["name"] for f in SRC.glob("*.lean") for r in scan(f)[1] if r["done"]}
    labels, entries = {}, []
    for m in ENV.finditer(text):
        body = m.group(2)
        label = (re.search(r"\\label\{([^}]*)\}", body) or [None, "?"])[1]
        names = [n.strip() for g in re.findall(r"\\lean\{([^}]*)\}", body) for n in g.split(",")]
        labels[label] = names
        p = PROOF.match(text, m.end()) if m.group(1) != "definition" else None
        used = [u.strip() for g in re.findall(r"\\uses\{([^}]*)\}", p.group(1)) for u in g.split(",")] if p else []
        entries.append((names, used))
    out = []
    for names, used in entries:
        thms = [n for n in names if n in done]
        reqs = [(u, labels[u]) for u in used if labels.get(u) and not set(labels[u]) & set(names)]
        if thms and reqs:
            out.append((thms, reqs))
    return out


def main() -> int:
    if "--uses" in sys.argv:
        for thms, reqs in uses_edges():
            print("|".join(thms), " ".join(f"{u}={'|'.join(ns)}" for u, ns in reqs))
        return 0
    bp, errors = blueprint()
    for f in sorted(SRC.glob("*.lean")):
        for r in scan(f)[1]:
            if r["name"] not in bp:
                errors.append(f"{r['name']}: not in the blueprint")
                continue
            label, proved = bp[r["name"]]
            if proved != r["done"]:
                want = "add" if r["done"] else "remove"
                errors.append(f"{label}: {want} \\leanok in the proof ({r['name']})")
    for e in errors:
        print(e)
    print("blueprint matches the Lean sources" if not errors else f"{len(errors)} problem(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
