#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# Disclosed proof debt is currently ZERO (2026-09-01): the Rhin-lite measure `rhinLiteLIMeasure`
# (FrontA/RhinLiteApprox.lean) is proved, and the sink `sep_two_three` (FrontA/RhinLiteSep.lean)
# is proved from its explicit-constant form with no literature axiom.  Should the Rhin-lite path
# be decomposed further, any new disclosed sorry must stay in RhinLiteApprox.lean; the gate pins
# the LOCATION (no debt may leak elsewhere, in particular not into PowSeparation.lean or
# RhinLiteSep.lean).
expected_files='^CollatzMoonshot/FrontA/RhinLiteApprox\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"

if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected: all disclosed sorries in RhinLiteApprox.lean only (PowSeparation.lean sorry-free).' >&2
  exit 1
fi

printf 'Proof-debt gate: %s disclosed sorries (RhinLiteApprox only; sep_two_three proved axiom-free)\n%s\n' "$count" "$hits"
