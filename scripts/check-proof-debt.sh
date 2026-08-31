#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# Disclosed proof debt is confined to the two files on the Rhin-lite separation path:
#   * FrontA/PowSeparation.lean   — `sep_two_three` (the sink node's β = 1/3 form).
#   * FrontA/RhinLiteApprox.lean  — the coarse Rhin linear-independence measure and its named
#     sub-obligations (the crux `rhinLiteLIMeasure` and its decomposition), from which
#     `log23_effective_measure` is derived, the concrete route to discharging `sep_two_three`.
# The gate pins the LOCATIONS (no debt may leak elsewhere) and requires the sink `sep_two_three`
# to still be present; the count within RhinLiteApprox.lean may grow as the crux is decomposed.
expected_files='^CollatzMoonshot/FrontA/PowSeparation\.lean:|^CollatzMoonshot/FrontA/RhinLiteApprox\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"
pow_hits="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -c '^CollatzMoonshot/FrontA/PowSeparation\.lean:' || true)"

if [[ -n "$unexpected" ]] || [[ "$pow_hits" != "1" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected: exactly one sorry in PowSeparation.lean and all others in RhinLiteApprox.lean.' >&2
  exit 1
fi

printf 'Proof-debt gate: %s disclosed sorries (PowSeparation + RhinLiteApprox only)\n%s\n' "$count" "$hits"
