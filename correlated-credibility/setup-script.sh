#!/bin/bash
# Paste this into the cloud environment's "Setup script" field (not run from the repo).
# It installs elan and pre-fetches Mathlib so the environment snapshot has it on disk.
# Must finish in ~5 min to be cached; it never fails the session.
export PATH="$HOME/.elan/bin:$PATH"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none || true

REPO=$(find / -maxdepth 5 -name lakefile.toml -path '*correlated-credibility*' 2>/dev/null | head -1)
if [ -n "$REPO" ]; then
  cd "$(dirname "$REPO")" && timeout 270 lake exe cache get || true
fi
exit 0
