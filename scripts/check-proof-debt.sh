#!/usr/bin/env bash
set -euo pipefail

# Keep the public proof-debt statement in README.md mechanically honest. This scan is
# deliberately narrow: named axioms are audited separately, while every anonymous proof
# hole must remain isolated at the documented declaration.
hits="$(grep -REn --include='*.lean' \
  '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*by[[:space:]]+sorry([[:space:]]|$)' \
  CollatzMoonshot CollatzMoonshot.lean || true)"
count="$(printf '%s\n' "$hits" | sed '/^$/d' | wc -l | tr -d ' ')"

# Disclosed proof debt (2026-09-01, later): ZERO sorries.  The last one,
# `two_pow_approx_three_pow_from_above` (FrontA/PowApprox.lean), is proved by a multiplicative
# pigeonhole; Rozier--Terracol 2026 Theorem 3.2 and `finite_acyclicParadoxical_imp_noDivergent`
# are trust-base clean.  The Rhin-lite tower and the sink `sep_two_three` are sorry-free and
# literature-axiom-free.  The gate still pins the LOCATION of any future debt: it may live only in
# PowApprox.lean or RhinLiteApprox.lean (the two historical decomposition slots), never elsewhere —
# in particular not in PowSeparation.lean or RhinLiteSep.lean.
expected_files='^CollatzMoonshot/FrontA/(PowApprox|RhinLiteApprox)\.lean:'
unexpected="$(printf '%s\n' "$hits" | sed '/^$/d' | grep -Ev "$expected_files" || true)"

if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'Unexpected anonymous proof debt:' >&2
  printf '%s\n' "$hits" >&2
  printf '%s\n' 'Expected: all disclosed sorries in PowApprox.lean / RhinLiteApprox.lean only.' >&2
  exit 1
fi

printf 'Proof-debt gate: %s disclosed sorries (PowApprox/RhinLiteApprox only; sep_two_three proved axiom-free)\n%s\n' "$count" "$hits"
