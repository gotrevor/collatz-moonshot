# HANDOFF 2026-10-10 — component domination proved

Executed item 1 of `ARC-BAND-CERTIFICATE-DIRECTION.md`.

## Advance

`ArcDelayGame.finiteMemoryRelaxedValue_of_componentK` is proved without `sorry`.  Given a live
`KRelaxedStrategy`, its component set consists of windows containing an absolute translate
`[m+a,m+a+l]`.  The proof sends the relaxed move into the component indexed by `m+j`, and proves that
every adversarial shift has the required child witness.  Local helper lemmas establish:

- the decomposition of a residue modulo `2q` into its low residue plus one top bit;
- compatibility of `(3m-m%2)/2` with reducing `m` modulo `2q`;
- the floor and fractional-part identities for `3(m+u)/2`;
- recovery of the parity bit from a residue modulo `2^k`.

## Verification

- `lake env lean CollatzMoonshot/Benchmark/ArcDelayGame.lean` — PASS.
- `lake env lean /tmp/ArcDelayAxiom.lean` (`#print axioms ...finiteMemoryRelaxedValue_of_componentK`)
  — exactly `propext`, `Classical.choice`, `Quot.sound`.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot --target
  CollatzMoonshot.Benchmark.ArcDelayGame` — `FORMALIZE-TIER GREEN` (8707 jobs).
- `git diff --check` — PASS.

## Current blocker / next attack

Item 1 has no blocker.  The scoped host target remains open because
`ArcBandCertificate.relaxedAboveUpperEdge` is still the item-2 proof hole.  Next implement the affine
interval descent checker in `ArcBandCertificate.lean`, starting with evaluation of affine forms and
the pointwise soundness lemma for one symbolic descent step, then connect the generated trees through
the vertex-sign oracle and boundary shift.
