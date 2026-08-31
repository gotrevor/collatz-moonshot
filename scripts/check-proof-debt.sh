#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# Disclosed proof debt is now confined to a single file on the Rhin-lite separation path:
#   * FrontA/RhinLiteApprox.lean  — the coarse Rhin linear-independence measure and its named
#     sub-obligations (the crux `rhinLiteLIMeasure` and its decomposition), from which
#     `log23_effective_measure` is derived.  The sink `sep_two_three` (FrontA/PowSeparation.lean)
#     is now PROVED sorry-free from the cited `Assumed.rhin_1987_log_two_three_measure` axiom, so
#     PowSeparation.lean must carry NO anonymous proof debt.
# The gate pins the LOCATIONS (no debt may leak elsewhere, in particular not into
# PowSeparation.lean); the count within RhinLiteApprox.lean may grow as the crux is decomposed.
expected_files='^CollatzMoonshot/FrontA/RhinLiteApprox\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"

if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected: all disclosed sorries in RhinLiteApprox.lean only (PowSeparation.lean sorry-free).' >&2
  exit 1
fi

printf 'Proof-debt gate: %s disclosed sorries (RhinLiteApprox only; sep_two_three proved)\n%s\n' "$count" "$hits"
