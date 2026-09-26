#!/usr/bin/env bash
# Print the axioms used by the given declarations.
# Usage: scripts/check_axioms.sh Decl.one Decl.two ...
# Acceptable output: only propext, Classical.choice, Quot.sound.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d)/AxiomCheck.lean"
{
  echo "import LieLean"
  for d in "$@"; do echo "#print axioms $d"; done
} > "$tmp"
lake env lean "$tmp"
