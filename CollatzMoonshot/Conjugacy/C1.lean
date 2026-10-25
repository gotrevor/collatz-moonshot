/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.SliceFourier
import CollatzMoonshot.Conjugacy.SliceSeven

/-!
# C1 from one node: `PascalDampingDecay ⇒ BiasDecays`

The 3-adic route to C1 (`BiasDecays`, `Ladder.lean`) composes two proved edges:
`sliceCharDecay_of_pascalDampingDecay` (`SliceSeven.lean`, research note §13: slice law to gaps,
Tao's pairing, binomial-mode conditioning) and `biasDecays_of_sliceCharDecay`
(`SliceFourier.lean`, personal-c5: the Fourier expansion of least-residue parity has weight
`O(a)`).  So C1 rests on the single open node `PascalDampingDecay`, Tao 2019's (7.5) damping bound
at `Pascal(p)`, uniform on `p ∈ [1/5, 3/5]`.  That node is the tao-collatz Sec7P campaign
(`TaoCollatz/Sec7P/Statement.lean`, `pascal_damping_decay`, whose definitions are copied verbatim
from `SliceSeven.lean`).
-/

namespace CollatzMoonshot.Conjugacy

/-- **C1 from the Sec7P node.**  `BiasDecays` follows from `PascalDampingDecay` alone. -/
theorem biasDecays_of_pascalDampingDecay (h : PascalDampingDecay) : BiasDecays :=
  biasDecays_of_sliceCharDecay (sliceCharDecay_of_pascalDampingDecay h)

end CollatzMoonshot.Conjugacy
