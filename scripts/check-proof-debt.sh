#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# The two disclosed obligations on the Rhin-lite separation path:
#   1. FrontA/PowSeparation.lean   — `sep_two_three` (the sink node's β = 1/3 form).
#   2. FrontA/RhinLiteApprox.lean  — `rhinLiteLIMeasure` (the coarse Rhin linear-independence
#      measure of {1, log(3/2), log(4/3)}, from which `log23_effective_measure` is proved and
#      which is the concrete route to discharging `sep_two_three`).
expected_files='^CollatzMoonshot/FrontA/PowSeparation\.lean:|^CollatzMoonshot/FrontA/RhinLiteApprox\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"

if [[ "$count" != "2" ]] || [[ -n "$unexpected" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected exactly two disclosed sorries: PowSeparation.lean, RhinLiteApprox.lean.' >&2
  exit 1
fi

printf 'Proof-debt gate: exactly two disclosed sorries\n%s\n' "$hits"
