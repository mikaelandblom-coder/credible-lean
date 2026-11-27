#!/usr/bin/env python3
"""Print how far each document lags behind the Lean results (CLAUDE.md, "Keeping
the documents current"). Run by the SessionStart hook, so every chat sees it.

For each document: the open items (`- [ ]`) under its "## Pending" heading, the
date of the oldest one, and how many commits changed `Credibility/` since the
document itself last changed. A document is flagged "catch-up due" when it has
more than MAX_OPEN open items or its oldest is older than MAX_DAYS.
"""
import datetime as dt
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAX_OPEN, MAX_DAYS = 10, 7
# (name, Pending list, the document's own source)
DOCS = [
    ("paper", "paper/outline.md", "paper/paper.tex"),
    ("handbook", "handbook/outline.md", "handbook/handbook.tex"),
    ("app", "studies/PLAN.md", "app"),
    ("thesis proposal", "studies/thesis-topics/outline.md", "studies/thesis-topics/proposal.tex"),
]
DATE = re.compile(r"20\d\d-\d\d-\d\d")


def git(*args):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


def pending(path):
    """(open items, done notes, oldest open date) of the "## Pending" section."""
    p = ROOT / path
    if not p.exists():
        return 0, 0, None
    section, on = [], False
    for line in p.read_text().splitlines():
        if line.startswith("## "):
            on = line.strip() == "## Pending"
            continue
        if on:
            section.append(line)
    opened = [l for l in section if l.startswith("- [ ]")]
    done = [l for l in section if l.startswith("- [x]") or l.startswith("- *Done")]
    dates = [dt.date.fromisoformat(m.group()) for l in opened if (m := DATE.search(l))]
    return len(opened), len(done), min(dates) if dates else None


def lag(source):
    """Commits that changed Credibility/ since `source` last changed."""
    last = git("log", "-1", "--format=%H", "--", source)
    return int(git("rev-list", "--count", f"{last}..HEAD", "--", "Credibility") or 0) if last else 0


def main():
    today = dt.date.today()
    lines, due = [], []
    for name, plist, source in DOCS:
        n, done, oldest = pending(plist)
        age = (today - oldest).days if oldest else 0
        text = f"{name}: {n} open"
        if oldest:
            text += f" (oldest {age} days)"
        if done:
            text += f", {done} done notes to clear"
        text += f"; {lag(source)} Lean commits since it last changed"
        if n > MAX_OPEN or age > MAX_DAYS:
            text += "  <- catch-up due"
            due.append(name)
        lines.append(text)
    print("Pending: " + " | ".join(lines))
    if due:
        print("Catch-up due for: " + ", ".join(due)
              + " (propose a catch-up chat in the next-chat prompt; CLAUDE.md).")


if __name__ == "__main__":
    main()
