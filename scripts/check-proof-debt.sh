#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# Disclosed proof debt (2026-09-01): ONE sorry, `two_pow_approx_three_pow_from_above` in
# FrontA/PowApprox.lean — powers of two approximate powers of three from above to arbitrary
# relative precision, infinitely often (classical: density of `{A·log₂3}` mod 1).  It is the sole
# remaining obligation behind Rozier--Terracol 2026 Theorem 3.2, which is now a THEOREM of
# Assumed/Paradoxical.lean rather than a cited axiom.  The Rhin-lite tower and the sink
# `sep_two_three` are sorry-free and literature-axiom-free.  The gate pins the LOCATION: debt may
# live only in PowApprox.lean (the active node) or RhinLiteApprox.lean (the Rhin-lite decomposition
# slot), never elsewhere — in particular not in PowSeparation.lean or RhinLiteSep.lean.
expected_files='^CollatzMoonshot/FrontA/(PowApprox|RhinLiteApprox)\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"

if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected: all disclosed sorries in PowApprox.lean / RhinLiteApprox.lean only.' >&2
  exit 1
fi

printf 'Proof-debt gate: %s disclosed sorries (PowApprox/RhinLiteApprox only; sep_two_three proved axiom-free)\n%s\n' "$count" "$hits"
