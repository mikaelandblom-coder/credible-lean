#!/usr/bin/env python3
"""Check that every \\lean{Name} in handbook/handbook.tex is a proved
declaration (no sorry), so the handbook never links to a renamed, deleted or
unfinished result.

    python3 scripts/handbook_check.py
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
tex = (ROOT / "handbook" / "handbook.tex").read_text()
names = re.findall(r"^\s*\\lean\{([^}]+)\}", tex, re.M)
proved = set(subprocess.run(
    [sys.executable, str(ROOT / "scripts" / "progress.py"), "--proved"],
    capture_output=True, text=True, check=True).stdout.split())
bad = [n for n in names if n not in proved]
for n in bad:
    print(f"handbook links to {n}, which is not a proved declaration")
print(f"handbook: {len(names) - len(bad)}/{len(names)} links ok")


def norm(t):
    """A heading as plain text: \\texorpdfstring{A}{B} -> A, no trailing period."""
    t = re.sub(r"\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{[^{}]*\}", r"\1", t)
    return " ".join(t.split()).rstrip(".")


# \paper{Title}: a section, subsection or paragraph of paper/paper.tex.
paper = (ROOT / "paper" / "paper.tex").read_text()
titles = {norm(m.group(1)) for m in re.finditer(
    r"\\(?:sub)*(?:section|paragraph)\*?\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", paper)}
cited = re.findall(r"\\paper\{((?:[^{}]|\{[^{}]*\})*)\}",
                   re.sub(r"(?<!\\)%.*", "", tex))
missing = sorted({t for t in cited if norm(t) not in titles})
for t in missing:
    print(f"handbook cites the paper's '{t}', which is not a heading there")
print(f"handbook: {len(cited) - len(missing)}/{len(cited)} paper citations ok")
sys.exit(1 if bad or missing else 0)
