#!/usr/bin/env python3
"""Write blueprint/web/find/index.html: a redirect from a declaration name
to its line in the Lean source on GitHub.

leanblueprint links each \\lean{Name} to `<dochome>/find/#doc/Name`. Building
doc-gen4 docs would mean documenting all of Mathlib, so the blueprint's
\\dochome points at the site itself and this page sends `#doc/Name` to the
source instead.

    python3 scripts/blueprint_find.py   # after `leanblueprint web`
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPO = "https://github.com/mikaelandblom-coder/credible-lean/blob/main"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|instance)\s+([^\s:({\[]+)"
)


def declarations():
    """Fully qualified name -> 'path#Lline', tracking `namespace`/`end`."""
    out = {}
    for f in sorted((ROOT / "Credibility").glob("*.lean")):
        ns = []
        for i, line in enumerate(f.read_text().splitlines(), 1):
            if m := re.match(r"namespace\s+(\S+)", line):
                ns.append(m.group(1))
            elif m := re.match(r"end\s+(\S+)", line):
                if ns and ns[-1] == m.group(1):
                    ns.pop()
            elif m := DECL.match(line):
                name = ".".join(ns + [m.group(1)])
                out[name] = f"{REPO}/{f.relative_to(ROOT)}#L{i}"
    return out


PAGE = """<!doctype html>
<meta charset="utf-8">
<title>Find declaration</title>
<p id="msg">Redirecting…</p>
<script>
const decls = %s;
const name = decodeURIComponent(location.hash.replace(/^#doc\\//, ""));
if (decls[name]) location.replace(decls[name]);
else document.getElementById("msg").textContent = "Unknown declaration: " + name;
</script>
"""

if __name__ == "__main__":
    decls = declarations()
    wanted = (ROOT / "blueprint" / "lean_decls").read_text().split()
    missing = [n for n in wanted if n not in decls]
    if missing:
        raise SystemExit("no source line for: " + ", ".join(missing))
    out = ROOT / "blueprint" / "web" / "find" / "index.html"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(PAGE % json.dumps(decls, ensure_ascii=False, indent=1))
    print(f"wrote {out.relative_to(ROOT)} ({len(decls)} declarations)")
