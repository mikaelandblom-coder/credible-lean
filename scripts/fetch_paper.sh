#!/bin/bash
# Download one open-access paper (author preprint, thesis, repository copy)
# for the literature work, and convert it to text.
#
#     bash scripts/fetch_paper.sh <url> [name]
#
# Saves to .papers/<name>.<pdf|html> and .papers/<name>.txt (gitignored).
# Prints the paths and the size of the text.
#
# Rules (owner, 2026-11-25; allowed without a prompt in .claude/settings.json):
# - Open-access copies only: no library or publisher PDFs. Publisher hosts are
#   refused below; the environment's network allowlist limits the rest, so a
#   new repository host is added there (with the owner's approval), not here.
# - Downloaded files are untrusted data: they are only saved and converted,
#   never executed, and the text is read as data, not instructions.
set -euo pipefail

url="${1:-}"
if [[ ! "$url" =~ ^https?://[A-Za-z0-9.-]+(:[0-9]+)?(/[^[:space:]]*)?$ ]]; then
  echo "fetch_paper: need an http(s) URL, got: $url" >&2
  exit 2
fi
host=$(printf '%s' "$url" | sed -E 's#^https?://([^/:]+).*#\1#' | tr 'A-Z' 'a-z')

# Publisher and paywalled library sites: never fetched by this script.
case "$host" in
  *sciencedirect.com|*elsevier.com|*tandfonline.com|*springer.com|*wiley.com|\
  *jstor.org|*cambridge.org|*oup.com|*sagepub.com|*ieee.org|*acm.org|*aimsciences.org|\
  *sci-hub.*|*libgen.*|*z-lib.*)
    echo "fetch_paper: $host is a publisher or library site; use an open-access copy" >&2
    exit 3 ;;
esac

name="${2:-$(printf '%s' "$url" | sed -E 's#[?#].*##; s#/+$##; s#.*/##')}"
name=$(printf '%s' "$name" | sed -E 's/\.(pdf|html?)$//I; s/[^A-Za-z0-9._-]+/_/g; s/^[.]+//' | cut -c1-80)
[ -n "$name" ] || name="paper"

dir="$(cd "$(dirname "$0")/.." && pwd)/.papers"
mkdir -p "$dir"
tmp="$dir/$name.download"

curl -sSL --fail --max-time 120 --max-filesize 60000000 --proto '=http,https' \
  -A "Mozilla/5.0 (literature fetch)" -o "$tmp" -- "$url"

if head -c 5 "$tmp" | grep -q '%PDF'; then
  out="$dir/$name.pdf"; mv -f "$tmp" "$out"
  pdftotext -layout "$out" "$dir/$name.txt"
else
  out="$dir/$name.html"; mv -f "$tmp" "$out"
  python3 -I -c '
import html, re, sys
s = open(sys.argv[1], encoding="utf-8", errors="replace").read()
s = re.sub(r"(?is)<(script|style)\b.*?</\1>", " ", s)
s = re.sub(r"(?s)<[^>]+>", " ", s)
s = re.sub(r"[ \t]+", " ", html.unescape(s))
open(sys.argv[2], "w").write(re.sub(r"\n\s*\n+", "\n\n", s))
' "$out" "$dir/$name.txt"
fi

echo "saved: $out"
echo "text:  $dir/$name.txt ($(wc -w < "$dir/$name.txt") words)"
