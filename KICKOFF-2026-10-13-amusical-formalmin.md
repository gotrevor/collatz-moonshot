# KICKOFF 2026-10-13: formal minima and the resolution gate (amusical)

Repo `collatz-moonshot-amusical-formalmin`: close every `sorry` in `CollatzMoonshot/AmusicalFormalMin.lean`.

## Ratified, do not change

All statements and definitions in that file (`kFwd`, `kBwd`, `FormalMin`).  Everything else in the
repo is read-only; other treadmills own other `Amusical*.lean` files.  Helpers go in
`CollatzMoonshot/AmusicalFormalMin/*.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive check on 2026-10-13 held 16 GB for 2 h and starved every other box.

## Suggested order

1. **Iterate bookkeeping lemma.**  `kBwd (amusical^[j] x) j = kFwd x j`.  This needs
   `amusicalInv^[i+1] (amusical^[j] x) = amusical^[j-1-i] x` for `i < j`.
2. **`not_formalMin_of_periodic`, `formalMin_unique`.**  Both follow from step 1, by the docstring
   proofs.  For `formalMin_unique`, split `j` into `j > 0` (apply step 1 to `x`) and `j < 0` (apply it
   to `y`, with `x = U^{−j} y`).  `(amusicalPerm ^ (n : ℕ)) x = amusical^[n] x`.
3. **`formalMin_neg`.**  `amusical_neg`, plus parity of `-n` equals parity of `n`, and the same for
   `amusicalInv`.
4. **`infinitelyManyOrbits_of_formalMin_infinite`.**  Each orbit contains at most one formal minimum,
   so the map `n ↦ amusicalOrbit n` is injective on formal minima.
5. **`coarse_quasiInvariant_bounded`** (hardest; Proposition G1, paper proof in `emptyint.md` §4,
   staged under the docstring).  Lemma E in `AmusicalEscape.lean` gives unboundedness of an infinite
   orbit.  You may use `amusical_no_periodic_cone` (owned by the antikohl treadmill) as the
   transitivity input.  If the two-visit lemma does not close, leave a clean HANDOFF that names the
   exact missing sub-lemma.

Notes for the next lap go in `HANDOFF-amusical-formalmin.md`.
