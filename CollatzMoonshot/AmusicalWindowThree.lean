/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

/-!
# No bijective reversor reads a window of three symbols

`AmusicalNoContinuousReversor` asks for a bijective reversor `ι` whose step symbol
`stepSym (ι n)` is determined by a residue of `n`.  This file kills the smallest nontrivial
case exactly: `stepSym (ι n)` a function of the three symbols `stepSym (U⁻¹ n)`,
`stepSym n`, `stepSym (U n)` (`no_window3_bijective_reversor`).  Any other offset reduces to this
one by composing `ι` with a power of `U`.

The proof uses only finite information:

* **Cycles.**  A bijective reversor maps integer cycles onto integer cycles of the same length.
  The integer cycles of length at most `12` are the nine known ones (`0`, `±1`, `±{2, 3}`,
  `±{4, 6, 9, 7, 5}`, `±` the `12`-cycle through `44`), by `amusical_periodic_mem`.  Matching
  them forces `f` on `25` of its `27` blocks, in one of `24` ways.
* **Orphans.**  Each of the `24 · 9 = 216` completions has an orphan word of length at most `5`:
  a word that never occurs in the forward itinerary of any `ι n`.  Every finite word occurs in
  the forward itinerary of some integer (`exists_forward_itinerary`), so `ι` is not onto.

Paper proof: agent report `q1.md` §4 (2026-10-13), re-derived independently by
`scripts/amusical/w3check.py`; certificates in `scripts/amusical/w3certs.txt`.  Treadmill target
(`KICKOFF-2026-10-13-amusical-w3.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  Every integer of period at most `12` lies on a known cycle.  Paper proof: on the
cylinder of its itinerary word `w`, a period-`p` point is `x_w = N_w / (2^e − 3^p)`, and
`|x_w| ≤ 483` for every word with `p ≤ 12` (`scripts/amusical/perbound.py`); then check
`|y| ≤ 483` by `decide +kernel`. -/
theorem amusical_periodic_mem (y : ℤ) (p : ℕ) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (h : amusical^[p] y = y) : |y| ∈ knownCycleMembers := by
  sorry

/-- **Target.**  Every finite word is the start of the forward itinerary of some integer (the
set of such integers is a class mod `2^e`, nonempty by the Chinese remainder theorem). -/
theorem exists_forward_itinerary (u : List (Fin 3)) :
    ∃ m : ℤ, ∀ j (hj : j < u.length), stepSym (amusical^[j] m) = u[j] := by
  sorry

/-- **Target (Theorem W3).**  No bijective reversor of `U` has `stepSym (ι n)` determined by
`stepSym (U⁻¹ n)`, `stepSym n`, `stepSym (U n)`.  Paper proof: module docstring and
`KICKOFF-2026-10-13-amusical-w3.md`. -/
theorem no_window3_bijective_reversor (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hbij : Function.Bijective ι)
    (hloc : ∀ n, stepSym (ι n) =
      f (stepSym (amusicalInv n)) (stepSym n) (stepSym (amusical n))) : False := by
  sorry

end CollatzMoonshot.Amusical
