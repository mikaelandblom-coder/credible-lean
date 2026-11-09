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
sys.exit(1 if bad else 0)
