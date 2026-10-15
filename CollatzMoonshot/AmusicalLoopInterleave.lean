/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSwap

/-!
# Two block swaps of `U` with the wrong loop correlation (research §49)

Round-3 ideation (2026-10-14, Codex "astra") tested a stochastic route to Klamkin (a): weight a
finite cube of block swaps by `q ^ (number of closed loops)` with `q > 1`, and compare `U` with
random members by FKG.  The first lemma needed is log-supermodularity,
`w(0,0) w(1,1) ≥ w(1,0) w(0,1)`.

**L1.**  If two switches act on four points of one orbit met in the interleaved order `a, c, b, d`
(switch the successors of `a, b`, or of `c, d`), each switch alone cuts one cycle out of the
segment and both together cut none, so the loop counts on that orbit are `C, C+1, C+1, C` and the
mixed difference is `−2`.  This file records that the interleaving happens for two actual blocks of
`U` (`ampSwap` with no swaps): on the orbit of `37`, block 9's sources `37, 39` sit at times `0, 7`
and block 8's sources `35, 33` at times `5, 10`.

* `interleave_path`: the eleven-step `U`-segment `37 → ⋯ → 25`.
* `swap_nine_cycle`, `swap_eight_cycle`: swapping either block alone closes a 7-cycle or a 5-cycle
  inside the segment.
* `swap_both_path`: swapping both rethreads the same twelve points into one segment with the same
  entrance `37` and exit `25`.

So increasing spatial block order does not give the temporal non-interleaving FKG would need.

**Pivots.**  A finite-horizon monotone coupling ("a swap never lowers survival") fails both ways
on `U`: swapping block 42 lifts `100` from a drop at time 5 to 64 steps above `100`
(`pivot_raises`), and swapping block 49 drops `104` (64 steps above `104` under `U`) to `85` at
time 20 (`pivot_lowers`).
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  `U`'s orbit of `37` meets block 9 at times 0, 7 and block 8 at times 5, 10. -/
theorem interleave_path :
    (List.range 12).map (fun k => (ampSwap (fun _ => false))^[k] 37) =
      [37, 28, 42, 63, 47, 35, 26, 39, 29, 22, 33, 25] := by
  decide

/-- **Target.**  Swapping block 9 alone closes the 7-cycle `28 → ⋯ → 39 → 28`. -/
theorem swap_nine_cycle :
    (List.range 8).map (fun k => (ampSwap (· == 9))^[k] 28) =
      [28, 42, 63, 47, 35, 26, 39, 28] := by
  decide

/-- **Target.**  Swapping block 8 alone closes the 5-cycle `26 → 39 → 29 → 22 → 33 → 26`. -/
theorem swap_eight_cycle :
    (List.range 6).map (fun k => (ampSwap (· == 8))^[k] 26) = [26, 39, 29, 22, 33, 26] := by
  decide

/-- **Target.**  Swapping both blocks leaves one segment on the same twelve points, `37` to `25`. -/
theorem swap_both_path :
    (List.range 12).map (fun k => (ampSwap (fun b => b == 8 || b == 9))^[k] 37) =
      [37, 29, 22, 33, 26, 39, 28, 42, 63, 47, 35, 25] := by
  decide

/-- **Target.**  Swapping block 42 raises the start `100`: `U` drops below it at time 5, the swapped
map stays above it for 64 steps. -/
theorem pivot_raises :
    (ampSwap (fun _ => false))^[5] 100 = 95 ∧
      ((List.range' 1 64).all fun t => decide (100 < (ampSwap (· == 42))^[t] 100)) = true := by
  decide

/-- **Target.**  Swapping block 49 lowers the start `104`: `U` stays above it for 64 steps, the
swapped map reaches `85` at time 20. -/
theorem pivot_lowers :
    ((List.range' 1 64).all fun t => decide (104 < (ampSwap (fun _ => false))^[t] 104)) = true ∧
      (ampSwap (· == 49))^[20] 104 = 85 := by
  decide

end CollatzMoonshot.Amusical
