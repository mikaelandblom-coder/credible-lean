#!/bin/bash
# Run a command, retrying on failure with growing waits (30s, 60s, 120s, 240s).
# CI downloads (elan, Lean, Mathlib cache, apt, pip) fail now and then with
# 503/504; a retry nearly always gets through.
#
#     bash scripts/retry.sh <command> [args...]
n=1
until "$@"; do
  if [ "$n" -ge 5 ]; then
    echo "retry: giving up after $n attempts: $*" >&2
    exit 1
  fi
  wait=$((30 * 2 ** (n - 1)))
  echo "retry: attempt $n failed; waiting ${wait}s: $*" >&2
  sleep "$wait"
  n=$((n + 1))
done
