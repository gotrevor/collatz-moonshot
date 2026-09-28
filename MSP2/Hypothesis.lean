/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MSP2.Defs

/-!
# MSP²: the open step, as a named hypothesis

The article is explicit that one step remains open (§16.2 "Statut de cette version",
§16.7.4, §20 "État de la démonstration"): the structural recurrence guaranteeing the
*raccord* (junction with an already-covered part of the Generator Table) at every
coefficient `3ⁿ`.  §16.2 states the target it is meant to deliver:

> pour tout n fini, N ≤ 2ⁿ − 1 ⇒ il existe j fini tel que Tʲ(N) < N.

We record that target as `Raccord`.  **This is our reading of §16/§20, pending the
authors' own statement** of the remaining step at every level `3ⁿ` (requested
2026-09-27).  When they supply it, the finer statement goes here beside `Raccord`, with a
theorem showing it implies `Raccord`.
-/

namespace MSP2

open CollatzMoonshot

/-- The §16.2 target at level `n`: every start `2 ≤ N ≤ 2ⁿ − 1` is covered. -/
def RaccordLevel (n : ℕ) : Prop := ∀ N, 2 ≤ N → N ≤ 2 ^ n - 1 → Covered N

/-- **The open step** (our reading of §16/§20, pending the authors' own statement):
the Generator Table's raccord holds at every level. -/
def Raccord : Prop := ∀ n, RaccordLevel n

end MSP2
