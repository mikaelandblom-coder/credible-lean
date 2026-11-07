#!/bin/bash
# Idempotent: installs elan/Lean if missing and fetches the prebuilt Mathlib cache.
# Used by both the cloud environment's setup script and the SessionStart hook.
set -u
export PATH="$HOME/.elan/bin:$PATH"

# Only the "lean" cloud environment allows the Mathlib cache host. Elsewhere
# (e.g. Default, meant for docs and discussion) skip Lean setup quietly.
if [ "${CLAUDE_CODE_REMOTE:-}" = "true" ] \
   && ! curl -sS -o /dev/null --max-time 10 https://cache.mathlib.org/ 2>/dev/null; then
  echo "fetch_mathlib: Lean hosts blocked (not the lean environment); skipping Lean setup. Docs and discussion only."
  exit 0
fi

if ! command -v lake >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none || exit 0
fi

cd "${CLAUDE_PROJECT_DIR:-$(dirname "$0")/..}" || exit 0

# Toolchain named in lean-toolchain is installed on first `lake` call.
# `cache get` is fast when the cache is already on disk.
lake exe cache get || echo "fetch_mathlib: cache get failed — check network allowlist"
exit 0
