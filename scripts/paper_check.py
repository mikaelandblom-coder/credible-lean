#!/usr/bin/env python3
"""Check every citation in paper/paper.tex, so the paper never points at a
renamed, unfinished or renumbered result.

- \\lean{Name}: a proved declaration (no sorry), as in handbook_check.py.
- \\hb{label}{n}: `label` is a result in handbook/handbook.tex and is
  currently Result n; \\hbsec{label}{n}: a handbook section, currently n.
- \\finding{n}: item n exists in FINDINGS.md.
- \\file{path}: the file exists in the repository.

The handbook number is written in the paper (so it reads in the source and
needs no cross-document lookup in TeX or plasTeX) next to the label (so a
renumbering is caught). After reordering the handbook, rewrite the numbers:

    python3 scripts/paper_check.py          # check
    python3 scripts/paper_check.py --fix    # rewrite stale handbook numbers
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper" / "paper.tex"


def strip_comments(tex):
    return re.sub(r"(?<!\\)%.*", "", tex)


def handbook_numbers():
    """label -> number, for results ('res:…') and sections ('sec:…'), in the
    handbook's own numbering (one Result counter, unstarred sections)."""
    tex = strip_comments((ROOT / "handbook" / "handbook.tex").read_text())
    tex = tex.split(r"\begin{document}", 1)[1]
    nums, res, sec = {}, 0, 0
    pending = None
    for m in re.finditer(
            r"\\begin\{result\}|\\section\{|\\label\{([^}]+)\}", tex):
        tok = m.group(0)
        if tok == r"\begin{result}":
            res += 1
            pending = res
        elif tok == r"\section{":
            sec += 1
            pending = sec
        elif pending is not None:
            nums[m.group(1)] = pending
            pending = None
    return nums


def main():
    fix = "--fix" in sys.argv[1:]
    raw = PAPER.read_text()
    tex = strip_comments(raw)
    # Citations live in the document body, not in the macro definitions.
    body = tex.split(r"\begin{document}", 1)[1]
    bad = []

    proved = set(subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "progress.py"), "--proved"],
        capture_output=True, text=True, check=True).stdout.split())
    names = re.findall(r"\\lean\{([^}]+)\}", body)
    bad += [f"\\lean{{{n}}} is not a proved declaration"
            for n in names if n not in proved]
    # Lean names only in the concordance (Appendix A); elsewhere cite the
    # handbook entry, which links the proof.
    conc = re.search(r"\\subsection\*\{Concordance\}(.*?)\\section\{", body, re.S)
    outside = re.sub(r"\\subsection\*\{Concordance\}.*?(?=\\section\{)", "", body,
                     flags=re.S)
    bad += [f"\\lean{{{n}}} outside the concordance: cite its handbook entry"
            for n in re.findall(r"\\lean\{([^}]+)\}", outside)]
    if conc is None:
        bad.append("no Concordance subsection found")

    nums = handbook_numbers()
    stale = {}
    cites = re.findall(r"\\(hb|hbsec)\{([^}]+)\}\{([^}]+)\}", body)
    for kind, label, n in cites:
        want = "res:" if kind == "hb" else "sec:"
        if not label.startswith(want) or label not in nums:
            bad.append(f"\\{kind}{{{label}}}: no such handbook "
                       f"{'result' if kind == 'hb' else 'section'}")
        elif str(nums[label]) != n:
            stale[(kind, label, n)] = str(nums[label])
    if fix and stale:
        for (kind, label, n), new in stale.items():
            raw = raw.replace(f"\\{kind}{{{label}}}{{{n}}}",
                              f"\\{kind}{{{label}}}{{{new}}}")
        PAPER.write_text(raw)
        print(f"paper: rewrote {len(stale)} stale handbook numbers")
    else:
        bad += [f"\\{k}{{{l}}}{{{n}}}: the handbook now numbers it {new} "
                "(run with --fix)" for (k, l, n), new in stale.items()]

    findings = set(re.findall(r"^(\d+)\. \*\*",
                              (ROOT / "FINDINGS.md").read_text(), re.M))
    for n in re.findall(r"\\finding\{([^}]+)\}", body):
        if n not in findings:
            bad.append(f"\\finding{{{n}}}: no such item in FINDINGS.md")

    for p in re.findall(r"\\file\{([^}]+)\}", body):
        if not (ROOT / p).exists():
            bad.append(f"\\file{{{p}}}: no such file")

    for b in bad:
        print("paper:", b)
    print(f"paper: {len(names)} Lean names, {len(cites)} handbook citations; "
          f"{len(bad)} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
