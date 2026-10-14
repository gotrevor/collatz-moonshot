# HANDOFF amusical-reglue

## Done: all five targets in `CollatzMoonshot/AmusicalReglue.lean` proved
`#print axioms`: `propext, Classical.choice, Quot.sound` for each of `exists_reglue_sparseFS` (Π),
`exists_reglue_sparseFS_amusical` (Π′), `bwd_iter_affine`, `lt_bwd_iter_iff`, `chernoff_duality`.
Ratified statements and defs unchanged (diff vs `5a89467` only removes `sorry` lines).

## Route
Both Π and Π′ come from `exists_reglue_of_gluable` (`AmusicalReglue/General.lean`), a
general reglue over a set `S` of allowed change points (Π: `S = univ`; Π′: `S = odd`).
- `GlueWith.lean`: `IsCutSet.glueWith hC φ` = `IsCutSet.glue` with the segment successor `φ`
  given by the caller.
- `Segments.lean`: segments are disjoint and cover the chains; `segMin`; a survivor is at most
  `segMin` of every later segment.
- `Cuts.lean`: GL-style indexed cuts (the change point and the cut both `≥ B q`) plus a
  strictly increasing spine `y_b` with `y_b, σ y_b` both cuts (singleton pieces).
- `Blocks.lean`: block = spine interval of `segMin`; the key is the lex pair (block position in
  `⋯B₃B₁|B₀B₂⋯`, `−segMin`); `WordOrder.lean` turns it into `C ≃ ℤ`
  (`orderIsoIntOfLinearSuccPredArch`).  `survivor_mem`: survivors ⊆ block 0 ∪ spine.

## Correction to the kickoff's Π′ paper proof
The kickoff's E-run spine bound `Σ_{s_b<X}(log₂ X + 1) ≤ G X` fails when `G = o(log X)`.  The
mechanism is `permFwdSurvivor_two_mul`: a survivor `3k` makes `2k` a survivor, so the whole
E-run survives.  The fix: spine points at non-periodic `y ≡ 1 (mod 6)`; `y` and `U⁻¹ y` are
both odd, so the pieces are singletons with odd cuts.

## Open
Nothing in scope.
