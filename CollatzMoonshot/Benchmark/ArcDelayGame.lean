/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcTrap

/-!
# The arc game as a pure delay game (lookahead without carries)

In `ArcTrap.KRelaxedStrategy` the residue `m mod 2^k` does two jobs.  It is lookahead (given the
constructor's floors, it is the next `k` parities), and it is control: the floor `J = ⌊3u/2 + d⌋` is
added to `⌊3m/2⌋`, so for `k ≥ 2` the constructor's own move changes the next parity.  This file
separates the first job.  In `KDelayStrategy` the index is the parity word itself, shifted out one
letter per move, and the adversary appends the letter `k` moves ahead.  The constructor sees the next
`k` parities and controls none of them.  That is a delay game in the sense of Klein and Zimmermann
(*How much lookahead is needed to win infinite games?*, LMCS 12(3), 2016), on the fractional arena.

Neither game dominates the other: the `k`-memory constructor has parity control, but its knowledge is
conditional on its own future floors.
-/

namespace CollatzMoonshot.Benchmark.ArcDelayGame

/-- **`k`-lookahead delay strategy** (`arc_sweep` with `ARC_NOCARRY=1`).  `P w` holds the window left
ends allowed when the next `k` parities are the bits of `w` (bit `0` is the current one).  After a move,
the word shifts down one letter and the adversary sets the new top letter `b`.  It is
`ArcTrap.KRelaxedStrategy` with the child index `(3w - w mod 2)/2 + J` replaced by `w / 2`.
Measurements (2026-10-10, exact rational Rust solver, `N = 2^20` / `2^15` grids):
* Off-centre sibling: same as the `k`-memory game.  On the arc `[2/5, 2/5 + 87/100]` at width
  `87/100 · 86/400`, `k = 1, 2` lose and `k = 3, 4, 5` win (all residues live); the `k`-memory game has
  `k = 2` losing and `k = 3` winning there (`MemoryHelpsOffCentre`).  So on that arc the benefit of
  memory is lookahead alone; carries are not needed.
* Positive control below `7/57` (`β = 7/57 - 10⁻⁵`, `N = 2^15`, widths `0.1225, 0.1231, 0.1234`):
  identical live sets in both games for `k = 1, …, 4` (winners only at `0.1225`, `k ≥ 2`).
* Above `7/57`: `ARC_NOCARRY=1 arc_sweep sweep 1 8 7057/57000 1/1000 1/2500 17` is empty at all 2825
  widths for every `k = 1, …, 8`, as the `k`-memory game is (`ArcSolverComputable.no_kRelaxedStrategy_7_57_plus`).
  So the two games share the threshold `7/57` as far as measured, although neither dominates.
* They are different games: over 60 random arcs (`k = 2, 3, 4`, `N = 2^14`) they disagree once, at
  `k = 4`, arc `[1/20, 1/20 + 79/100]`, width `1501/8000`, where the delay game wins (all 16 words live)
  and the `k`-memory game loses (`test_delay_game_controls`).
* Kill depth (descent steps from `[0, 1]` everywhere until empty, `arc_sweep solve`, `N = 2^16`; the
  relaxed fixed-width game).  At `β = 0.13`, widths `1/8, 3/20, 1/5`, the two games take IDENTICAL step
  counts for `k = 1, …, 5` (e.g. `5, 7, 8, 10, 12` at width `1/8`), then the delay game resists longer
  (`k = 8`: 18 vs 16; width `1/5`: 20 vs 16).  The `k`-memory game, `k = 5, …, 12`: `12, 14, 15, 16, 17,
  20, 21, 23` (`0.13`, width `1/8`) and `15, 17, 18, 21, 22, 25, 28, 31` (`1/8`, width `1/8`).
  Dead: "the adversary pays only the free ride" (depth `k + C`).  It looked true at `k = 5, …, 8`
  (`+1` per bit), but the plateau breaks at `k = 9, 10`, and the long-run rate is 1.5 to 2.3 moves per bit,
  as in the component game (`ArcDelay`). -/
def KDelayStrategy (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ) : Prop :=
  0 < l ∧ (∀ w, P w ⊆ Set.Ico 0 1) ∧
  ∀ w < 2 ^ k, ∀ a ∈ P w, ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b < 2, Int.fract (3 * u / 2 + ((w % 2 : ℕ) : ℝ) / 2) ∈ P (w / 2 + b * 2 ^ (k - 1))

/-- **Conjecture: finite lookahead does not pass `7/57` on the symmetric arc.**  The delay-game
analogue of `ArcTrap.FiniteMemoryRelaxedValue`.  Confidence 75% (as the `k`-memory conjecture,
discounted because the two games are not comparable).  Exploratory extension (2026-10-10, no widening,
`β = 7057/57000`, widths `i/1000`, `N = 2^16`): empty at every width for `k = 10` and `k = 12`, although at
`β = 0.10` the delay game's lookahead opens a second band of wide windows (`KRelaxedUpperEdgeMemoryless`).
Why it is worth stating separately: after the `k`-independent rounding of `ArcSolverInclusion` (grid
`e0 N ≥ 96`, no `k` in it) the delay game is a safety game on a finite arena with lookahead `k`.  For
such games Klein and Zimmermann show that if any finite lookahead wins, a lookahead exponential in the
arena already wins.  So here, unlike in the `k`-memory game (whose carries make the arena grow with
`k`), "every `k`" reduces in principle to one `K(e0)` per `β`.  The bound is far too large to compute;
what the route needs is a problem-specific version, a small monoid of parity-word profiles on the
symmetric arc (`DelayLookaheadCollapses`). -/
def DelayGameValue : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ (l : ℝ) (P : ℕ → Set ℝ),
    (∃ w < 2 ^ k, (P w).Nonempty) → ¬ KDelayStrategy β (1 - 2 * β) l k P

/-- **Open: lookahead collapses at a cost in the arc.**  For every `e0 > 0` some `K` serves every
lookahead: a `k`-lookahead winner at `β` gives a `K`-lookahead winner at `β - e0`.  The Klein-Zimmermann
pumping argument on the rounded arena should give it with `K` exponential in `1/e0` (confidence 60%:
the rounded game's cell transitions have to be checked to be a finite arena in their sense).  Unlike
`ArcTrap.KRelaxedStrategy.lift` (more lookahead never hurts), it bounds how much lookahead can help. -/
def DelayLookaheadCollapses : Prop :=
  ∀ e0 : ℝ, 0 < e0 → ∃ K : ℕ, ∀ (β l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → e0 ≤ β → β ≤ 1 / 2 →
    (∃ w < 2 ^ k, (P w).Nonempty) → KDelayStrategy β (1 - 2 * β) l k P →
      ∃ (l' : ℝ) (Q : ℕ → Set ℝ), (∃ w < 2 ^ K, (Q w).Nonempty) ∧
        KDelayStrategy (β - e0) (1 - 2 * (β - e0)) l' K Q

open ArcTrap in
/-- **Conjecture: on the symmetric arc, memory never widens the window.**  A live `k`-memory strategy at
width `l` gives a live `(k - 1)`-memory strategy at some width `l' ≥ l`.  So the upper edge of the
winning widths does not depend on `k`, and only the lower edge moves.  Confidence 70%.
Evidence (2026-10-10, `arc_sweep sweep 1 6 β 0 STEP LOGN 0 2/5`, the set of winning widths per `k`):
* `β = 7/57 - 1/100` (`N = 2^16`, step `1/2000`): upper edge `0.197` for every `k = 1, …, 6`; lower edge
  `0.123, 0.082, 0.055, 0.0365, 0.0245, 0.0165`, a factor `2/3` per bit (one move of growth per bit of
  lookahead); every band is a full interval.
* `β = 7/57 - 1/1000` (`N = 2^18`, step `1/5000`): upper edge `0.138` for every `k`; lower edges the same
  as at `1/100` (`0.123 · (2/3)^(k-1)`).
* `β = 7/57 - 1/10000` (`N = 2^20`, step `1/20000`): upper edge `0.1322` for every `k = 1, …, 6`, lower
  edges `0.12285, 0.0819, 0.0546, 0.0364, 0.0243, 0.0162`.
* Upper edges only (`k = 1, …, 8`, widths `≥ 1/10`, `N = 2^16`): `0.2620, 0.2135, 0.1495, 0.1365` at
  `β = 0.10, 0.11, 0.12, 0.122`, each the same for all eight `k`; at `β = 0.12` also `k = 10, 12`
  (`0.1495`, widths `[0.148, 0.152]`).
* Independent probes (Astra, 2026-10-10, `k = 1, …, 4`, step `1/1000`, `N = 2^15`, widths from `0.125`): largest
  winning width the same for all four `k` at `β = 0.02` (`0.674`), `0.05` (`0.562`), `0.06` (`0.524`), `0.07`
  (`0.408`), `0.10` (`0.262`); just above the `β ≈ 0.0668` wide-band transition, `k = 4, …, 8` win at none of 17
  widths in `[0.43, 0.51]`.  Coordinates for a proof: `ArcCentered.lifted_iff_centered` (Astra; centre
  `y = x + l/2`, move centre `z`, `|z - y| ≤ l/6`, band radius `R = (1 - 2β)/2 - l/3`, `R + 2 · l/6 = (1 - 2β)/2`).
* Slightly asymmetric arc `[0.115, 0.89]` (margins `0.115` and `0.11`): upper edge `0.190` for every
  `k = 1, …, 6` (`0.2125` on the symmetric `[0.11, 0.89]`, same scan).
* The memoryless lower edge is `7/57` itself at every `β` measured: `(0.122810, 0.122815]` at
  `β = 0.10` and `0.11` (`N = 2^20`, step `10⁻⁵/2`), against `7/57 = 0.1228070…`.  The `k`-memory lower edge
  is `(2/3)^(k-1) · 7/57` (compare `ArcTrap.not_kRelaxedStrategy_1229_small_width`, the proved
  `(1/9)(2/3)^k`).
* So the winning region is `(2/3)^(k-1) · 7/57 ≤ l ≤ u(β)` with `u` independent of `k`, and `u(β)` stays
  near `0.132` as `β → 7/57`: no band pinches.  Every band, at every `k`, dies at once at `7/57` with
  positive span, a width-independent transition like the memoryless barrier's (funnel and runaway).
* Known-false sibling, the off-centre arc `[2/5, 2/5 + 87/100]` (`MemoryHelpsOffCentre`, widths
  `t · j/400`): `k = 1, 2` never win; the upper edge is `0.252` at `k = 3` and `0.548` at `k = 4, 5, 6`, so
  there memory widens the window, and the statement is false off-centre.  The lower edge still moves by
  about `2/3` per bit (`0.1305, 0.0870, 0.0609`).
* Shifted gap, fixed gap width `0.22` (arc `[0.11 + ε, 0.89 + ε]`, `N = 2^15`, widths `i/200`): `ε = 0.01`
  upper edge `0.190` for every `k = 1, …, 6`; `ε = 0.08` (margins `0.19` and `0.03`) upper edge `0.275` for
  every `k`, lower edges `0.25, 0.17, 0.115, 0.075, 0.05, 0.035`; `ε = 0.03, 0.05`: no winner at any `k ≤ 6`.
So exact symmetry is NOT what the statement needs (it is stated for the symmetric arc only because that is
where `FiniteMemoryRelaxedValue` lives).  What the off-centre counterexample lacks is a gap around the
integers: its gap is `[0.27, 0.40]`.  A proof must use that.
* **The carries are essential.**  In the pure delay game (`KDelayStrategy`, `ARC_NOCARRY=1`, same scans) the
  property FAILS on the symmetric arc: at `β = 0.10` the upper edge is `0.262` for `k = 1, 2, 4` but `0.3495`
  for `k = 6, 8`, a second band `[0.3005, 0.3495]` disjoint from `[0.1, 0.262]` (`test_upper_edge_memoryless`
  pins width `0.31`: delay `k = 6` wins, delay `k = 4` and memory `k = 1, 6` lose) (at `β = 0.12` it stays `0.1495` for `k ≤ 8`, and `k = 10` has no winner above `0.15`).
  The `k`-memory game keeps `0.262` through `k = 12` (`k = 9, …, 12`: widths `[0.26, 0.36]`, step `1/1000`).  So knowing the next parities outright (delay game) is worth more than knowing the residue
  (parities conditional on one's own future floors), and a proof must use the 2-adic carry structure.
By induction it gives a memoryless winner, which
`ArcTrap.relaxed_barrier` excludes above `7/57` at every width
(`finiteMemoryRelaxedValue_of_upperEdge`).  It is a one-bit induction step, unlike
`ArcDelay.DelayCostBounded`, which needs a bounded price at every position. -/
def KRelaxedUpperEdgeMemoryless : Prop :=
  ∀ (β l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 0 < β → β < 1 / 2 → 2 ≤ k →
    (∃ r < 2 ^ k, (P r).Nonempty) → KRelaxedStrategy β (1 - 2 * β) l k P →
      ∃ (l' : ℝ) (Q : ℕ → Set ℝ), l ≤ l' ∧ (∃ r < 2 ^ (k - 1), (Q r).Nonempty) ∧
        KRelaxedStrategy β (1 - 2 * β) l' (k - 1) Q

open ArcTrap in
/-- The upper-edge conjecture implies `FiniteMemoryRelaxedValue`: step memory down to `1`, then the
memoryless barrier. -/
theorem finiteMemoryRelaxedValue_of_upperEdge (h : KRelaxedUpperEdgeMemoryless) :
    FiniteMemoryRelaxedValue := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact finiteMemoryRelaxedValue_one
  | succ k hk ih =>
    intro β hβ hβ' l P hne hS
    obtain ⟨l', Q, -, hQne, hQ⟩ := h β l (k + 1) P (by linarith [show (0 : ℝ) < 7 / 57 by norm_num])
      hβ' (by omega) hne hS
    exact ih β hβ hβ' l' Q (by simpa using hQne) (by simpa using hQ)

open ArcTrap in
/-- **Conjecture: the memoryless relaxed game needs width `7/57`, whatever the arc.**  For `β ≥ 1/10` no
memoryless relaxed strategy holds `[β, 1 - β]` at a width `l < 7/57`.  Confidence 75%.
Evidence (2026-10-10, `arc_sweep sweep 1 1 β 0 1/200000 20 0.1226 0.1230`): the `k = 1` winning widths
start in `(0.122810, 0.122815]` at both `β = 0.10` and `β = 0.11` (`N = 2^20` rounds inward, so a
lattice lower edge sits just above the true one), and at `0.1230` (the first grid width above `7/57`) for
`β = 7/57 - 1/100, 7/57 - 1/1000, 0.12, 0.122` on coarser grids.  The same number as the `β`-threshold
(`relaxed_barrier`) but a different statement: here `β` is well below `7/57`.  Monotone in `β`
(`RelaxedStrategy.mono`), so `β = 1/10` is the whole claim.  A finite refutation in the style of
`barrier_core` (node lemmas with endpoints affine in `l`) is the expected proof shape. -/
def RelaxedLowerEdge : Prop :=
  ∀ (β l : ℝ) (P : Set ℝ), 1 / 10 ≤ β → β < 1 / 2 → l < 7 / 57 → ¬ RelaxedStrategy β (1 - 2 * β) l P

open ArcTrap in
/-- **Conjecture: each bit of memory buys a factor `2/3` in width.**  For `β ≥ 1/10` no live `k`-memory
relaxed strategy at width `l < (2/3)^(k-1) · 7/57`.  Confidence 65%.  Lower edges measured
(`KRelaxedUpperEdgeMemoryless` evidence): `0.123, 0.082, 0.055, 0.0365, 0.0245, 0.0165` for
`k = 1, …, 6` at `β = 7/57 - 1/100`, the same at `7/57 - 1/1000` and `7/57 - 1/10000` (`0.12285,
0.0819, 0.0546, 0.0364, 0.0243, 0.0162`), each the previous times `2/3` up to the grid step.  The proved
`ArcTrap.not_kRelaxedStrategy_1229_small_width` is this shape with the constant `(1/9)(2/3)` in place of
`7/57`, at `β ≥ 0.1229`.  Off-centre the lower edge also moves by `2/3` per bit, so unlike the upper edge
this one need not use symmetry: one move of growth (`3/2`) per bit of lookahead. -/
def KRelaxedLowerEdge : Prop :=
  ∀ (β l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → 1 / 10 ≤ β → β < 1 / 2 →
    l < (2 / 3) ^ (k - 1) * (7 / 57) → (∃ r < 2 ^ k, (P r).Nonempty) →
      ¬ KRelaxedStrategy β (1 - 2 * β) l k P

open ArcTrap in
/-- **Conjecture: above width `7/57`, memory changes the kill depth but not the winner.**  On the symmetric
arc with `β ≥ 1/10` and `l ≥ 7/57`, a live `k`-memory strategy gives a memoryless one at the SAME `(β, l)`.
The same-width form of `KRelaxedUpperEdgeMemoryless`; with `RelaxedLowerEdge` and `KRelaxedLowerEdge` it
says memory helps only windows narrower than `7/57`.  Confidence 60%.
Evidence (2026-10-10): for `l ≥ 0.123` the winning widths of `k = 1, …, 8` coincide cell for cell at
`β = 0.10, 0.11, 0.12, 0.122` (e.g. at `0.10`: `[0.1230, 0.2620]`, 279 grid widths, for every `k`), and for
`k ≤ 6` at `7/57 - 10⁻², 10⁻³, 10⁻⁴`.
Dead mechanism: "too wide to survive any parity word".  Just above the upper edge the kill depth GROWS with
`k`: `7, 9, 11, 14, 16, 25` (`k = 1, 2, 3, 4, 6, 8`; `β = 0.1`, `l = 0.263`, `N = 2^16` descent steps) and
`7, 10, 11, 13, 17, 21` (`β = 0.12`, `l = 0.15`).  So the adversary adapts with delay and pays about two
moves per bit, as below `7/57` in `β`; it never needs to stop winning.  Off-centre this fails outright
(`[2/5, 2/5 + 87/100]`: no memoryless winner at any width, `k = 4` wins on `[0.13, 0.548]`).
Not a set-level reduction: memory does enlarge the strategy (`solve_vw`, `N = 2^16`).  At `β = 0.11`,
`l = 0.15` the greatest `k = 2` fixed point has 4 different residue sets, each strictly larger than the
memoryless one (residue `0` fills the memoryless gap `[0.1286, 0.1658]`), and `k = 3` has 8.  At
`β = 0.11`, `l = 0.2`, `k = 3` is exactly the lift of `k = 2` (memory saturates).  Dead route, "once one
more bit stops helping, no further bit helps": false in general, since off-centre `k = 1, 2` are both empty
(saturated) and `k = 3` wins.  On the symmetric arc that propagation is this conjecture again. -/
def KRelaxedMemorylessAboveLowerEdge : Prop :=
  ∀ (β l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → 1 / 10 ≤ β → β < 1 / 2 → 7 / 57 ≤ l →
    (∃ r < 2 ^ k, (P r).Nonempty) → KRelaxedStrategy β (1 - 2 * β) l k P →
      ∃ Q : Set ℝ, RelaxedStrategy β (1 - 2 * β) l Q

end CollatzMoonshot.Benchmark.ArcDelayGame
