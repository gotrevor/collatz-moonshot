/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcDelayGame
import CollatzMoonshot.Benchmark.ArcBandCertificateData

/-!
# The memoryless relaxed game above its upper edge

A Lean twin of `experiments/arc_band.py`: the memoryless relaxed descent with interval endpoints affine in
`(β, l)`, run on the triangles of a decision tree of split lines, with signs read off the triangle vertices.
The plan, the data format and the soundness obligations are in `ARC-BAND-CERTIFICATE-DIRECTION.md`.
-/

namespace CollatzMoonshot.Benchmark.ArcBandCertificate

open ArcTrap ArcDelayGame

/-- **No memoryless relaxed strategy above the upper edge** (`ArcDelayGame.RelaxedAboveUpperEdge`).
Route: soundness of the symbolic descent at one real point, a vertex sign test on open triangles (barycentric
coordinates), a decision tree whose split lines all have a nonzero `β` coefficient, and, for points on a split
line, a small leftward shift in `β` plus `RelaxedStrategy.mono`.  The certificate is checked by `native_decide`. -/
theorem relaxedAboveUpperEdge : RelaxedAboveUpperEdge := by
  sorry

end CollatzMoonshot.Benchmark.ArcBandCertificate
