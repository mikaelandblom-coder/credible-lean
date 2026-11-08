#!/bin/bash
# SessionStart: move a fresh generated session branch (ccr-…, claude/…) onto a
# local `main` tracking origin/main. Work is pushed to main (CLAUDE.md), and the
# cloud stop hook compares the current branch with origin/<branch>, so on `main`
# it only warns about commits really missing from origin/main.
# Does nothing if the branch has its own commits or the tree is dirty.
set -u
cd "${CLAUDE_PROJECT_DIR:-$(dirname "$0")/..}" || exit 0
branch=$(git branch --show-current 2>/dev/null) || exit 0
case "$branch" in ccr-*|claude/*) ;; *) exit 0 ;; esac
git fetch -q origin main 2>/dev/null || exit 0
git diff --quiet && git diff --cached --quiet || exit 0
git merge-base --is-ancestor HEAD origin/main || exit 0
# A local `main` that is not on origin/main (e.g. stale history in the image)
# is kept as a backup rather than overwritten.
if git rev-parse -q --verify main >/dev/null &&
   ! git merge-base --is-ancestor main origin/main; then
  git rev-parse -q --verify main-stale >/dev/null || git branch -m main main-stale
fi
git checkout -q -B main origin/main && git branch -q -u origin/main main &&
  echo "session_branch: switched from $branch to main (tracking origin/main)"
exit 0
