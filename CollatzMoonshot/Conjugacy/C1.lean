/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.SliceFourier
import CollatzMoonshot.Conjugacy.SliceSeven
import TaoCollatz.Sec7P.Statement

/-!
# C1: `BiasDecays`, unconditionally (via `PascalDampingDecay` from tao-collatz Sec7P)

The 3-adic route to C1 (`BiasDecays`, `Ladder.lean`) composes two proved edges:
`sliceCharDecay_of_pascalDampingDecay` (`SliceSeven.lean`, research note §13: slice law to gaps,
Tao's pairing, binomial-mode conditioning) and `biasDecays_of_sliceCharDecay`
(`SliceFourier.lean`, personal-c5: the Fourier expansion of least-residue parity has weight
`O(a)`).  So C1 rests on the single node `PascalDampingDecay`, Tao 2019's (7.5) damping bound at
`Pascal(p)`, uniform on `p ∈ [1/5, 3/5]`.  That node is proved in tao-collatz by the Sec7P campaign
(`TaoCollatz.Sec7P.pascal_damping_decay`, whose definitions are copied verbatim from
`SliceSeven.lean`).  So `biasDecays : BiasDecays` below is unconditional.
-/

namespace CollatzMoonshot.Conjugacy

/-- **C1 from the Sec7P node.**  `BiasDecays` follows from `PascalDampingDecay` alone. -/
theorem biasDecays_of_pascalDampingDecay (h : PascalDampingDecay) : BiasDecays :=
  biasDecays_of_sliceCharDecay (sliceCharDecay_of_pascalDampingDecay h)

/-- **`PascalDampingDecay` holds.**  It is `TaoCollatz.Sec7P.pascal_damping_decay` (tao-collatz, branch
`ren/sec7p-pascal`, required at a SHA in `lakefile.toml`): the Sec7P campaign proves Tao 2019's
(7.5) damping bound at `Pascal(p)` uniformly on `p ∈ [1/5, 3/5]`.  Its five definitions are copied
verbatim from `SliceSeven.lean`, so the two statements agree by definitional unfolding. -/
theorem pascalDampingDecay : PascalDampingDecay :=
  TaoCollatz.Sec7P.pascal_damping_decay

/-- **C1 (`BiasDecays`), unconditionally.**  `E_j / 2^j → 0`: over all `j`-bit inputs, the parity of
the `j`-th Terras iterate is asymptotically balanced. -/
theorem biasDecays : BiasDecays :=
  biasDecays_of_pascalDampingDecay pascalDampingDecay

end CollatzMoonshot.Conjugacy
