#!/bin/bash
# Copy of the "lean" cloud environment's setup script (kept here for reference;
# the environment runs its own stored copy, from the directory holding the checkout).
# Installs elan/Lean, fetches the Mathlib cache and builds the project, so the
# environment snapshot has all of it on disk. A new chat then rebuilds only the
# files changed since the snapshot.
if [ -d credible-lean ]; then bash credible-lean/scripts/fetch_mathlib.sh --build; fi
