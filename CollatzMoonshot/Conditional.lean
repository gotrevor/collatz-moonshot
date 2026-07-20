/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Conjecture
import CollatzMoonshot.Assumed

/-!
# First conditional results

Demonstrations of the investigatory pattern: combine the axiom-free wiring layer
(`Conjecture.lean`) with the assumed layer, and let `#print axioms` report exactly
what each result is conditional on.  E.g.

```
#print axioms CollatzMoonshot.two_pow_68_lt_of_onCycle_nontrivial
-- the classical trio + Assumed.collatz_verified_up_to_two_pow_68, nothing else
```
-/

namespace CollatzMoonshot

/-- Every member of a nontrivial cycle exceeds `2⁶⁸`.  Conditional on exactly one
assumption: the computational verification frontier (`#print axioms` names it).
The proof is the trivial-cycle analysis from `Conjecture.lean` plus the assumed
frontier - a first taste of the two layers composing. -/
theorem two_pow_68_lt_of_onCycle_nontrivial {n : ℕ} (hn : 1 ≤ n) (hc : OnCycle n)
    (hnt : ¬(n = 1 ∨ n = 2 ∨ n = 4)) : 2 ^ 68 < n := by
  by_contra hle
  push Not at hle
  exact hnt (eq_trivial_of_onCycle_of_reachesOne hc
    (Assumed.collatz_verified_up_to_two_pow_68 n hn hle))

end CollatzMoonshot
