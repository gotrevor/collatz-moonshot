#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

if [[ "$count" != "1" ]] || ! printf '%s\n' "$hits" \
    | grep -q '^CollatzMoonshot/FrontA/PowSeparation\.lean:'; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected exactly one sorry in FrontA/PowSeparation.lean.' >&2
  exit 1
fi

printf 'Proof-debt gate: exactly one disclosed sorry\n%s\n' "$hits"
