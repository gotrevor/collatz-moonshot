# HANDOFF 2026-10-16: rcwa-engine-gen done

Branch `wip/rcwa-engine-gen`, HEAD `a642ef6` (plus this doc).

## Done
* `CollatzMoonshot/RcwaEngineGen.lean` has no `sorry`.  All twelve ratified Lemma P statements
  for `r = 5^j` are proved: `le_orderOf_three`, `phase_lt`, `one_le_C1_iff`, `one_le_C2_iff`,
  `scale_spec`, `inEngine_scale`, `phase_scale`, `C1_scale`, `C2_scale`, `junk_scale`,
  `eq_of_decode_eq`, `exists_decode`.
* Axioms are `propext, Classical.choice, Quot.sound` only.  No `native_decide`.
* Ratified statements are unchanged: the diff removes only the `sorry` lines and the `**Open.**`
  prefixes.  Full `lake build` is green.
* The route is in `HANDOFF-rcwa-engine-gen.md`.

## Next steps
* Host: push `wip/rcwa-engine-gen` and merge.
* `box done` was acknowledged: the scoped target `sorry-free:CollatzMoonshot/RcwaEngineGen.lean`
  is clean.
* Next research node, which needs a ratified statement first: wire Lemma P (general `j`) into the
  Theorem C reduction.  That reduction runs from counter-machine halting to orbit counting for
  RCWA permutations whose slopes lie in `2^ℤ 3^ℤ`.  With `le_orderOf_three`, a machine with any
  number of states fits at `j` = (number of states).
