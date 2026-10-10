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
* Independent probes (Astra, 2026-10-10, `k = 1, …, 4`, step `1/1000`, `N = 2^15`, widths from `0.125`, except
  `β = 0.05` from `0.56`): largest winning width the same for all four `k` at `β = 0.02` (`0.674`), `0.05`
  (`0.562`), `0.06` (`0.524`), `0.07` (`0.408`), `0.10` (`0.262`); at `β = 2003/30000`, `k = 4, …, 8` win at none
  of the 17 widths `0.43, 0.435, …, 0.51` (`N = 2^16`).  Coordinates for a proof: `ArcCentered.lifted_iff_centered` (Astra; centre
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
(`RelaxedStrategy.mono`), so `β = 1/10` is the whole claim.
Exact (2026-10-10, `experiments/arc_band.py point`, no lattice): at `β = 1/10`, `l = 7/57` is live after 80
steps (`[5/57, 7/57]` survives), and below it the kill depth GROWS: `7, 11, 19, 25, 30, 36` steps at
`l = 0.11, 0.12, 0.1227, 0.1228, 0.122806, 0.1228069`.  That is about `log_{3/2}(1/ε)`, so unlike the upper edge
(`RelaxedAboveUpperEdge`, depth `≤ 8`) there is no finite cover.  The proof shape is `relaxed_barrier`'s: an
AND-OR funnel with endpoints affine in `l`, plus a runaway lemma.
The runaway, located (symbolic descent near `(1/10, 7/57 - 10⁻⁷)`): the slow death is a small interval
`[L, R]` around `11/57` (with partners near `20/57`, `10/19 = 30/57`, `39/57`).  From step 3 on, every 3 descent
steps map it EXACTLY to `[(8/27) L + 2/9 - 19 l/27, (8/27) R + 11/81]`, with no `β` term.  Fixed points:
`L* = 6/19 - l` and `R* = 11/57`, so the interval survives iff `6/19 - l ≤ 11/57`, i.e. `l ≥ 7/57`.  For a
strategy `P` this is a self-improving bound: `inf` and `sup` of `P` near `11/57` satisfy `a ≥ 6/19 - l` and
`b ≤ 11/57`, so `l < 7/57` empties it.  The descent then dies one step later.  The same `10/19` as the
`β`-barrier's runaway, and `57 = 3 · 19` in both thresholds. -/
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

open ArcTrap in
/-- **Conjecture: the memoryless winning widths are exactly `[7/57, u(β)]` on `1/10 ≤ β ≤ 7/57`,** with
`u(β) = min (3/4 - 39β/8) (15/16 - 105β/16)`.  The two pieces cross at `β = 1/9`, and `u(7/57) = 5/38`, so at the
threshold the band is `[7/57, 5/38]`, of positive length: the transition at `7/57` is not a pinch.
Confidence 80% for the formula (the existence direction holds whenever the solver's inward-rounded descent is
nonempty there; the exclusion direction is the open half).
Evidence (2026-10-10, `arc_sweep solve 1`, `N = 2^20`, bisection to `10⁻⁵`): `u = 0.262494 … 0.262500` at
`β = 0.10` (formula `0.2625`), `0.238120 …` at `0.105` (`0.238125`), `0.213747 …` at `0.11` (`0.21375`),
`0.182809 …` at `0.115` (`0.1828125`), `0.149997 …` at `0.12` (`0.15`), `0.136869 …` at `0.122` (`0.136875`),
`0.132227 …` at `7/57 - 10⁻⁴` (`0.13224`).  Astra's independent `β = 0.07` probe (`0.408`, `N = 2^15`) fits the
first piece (`0.40875`), so it extends below `1/10`; at `β = 0.06, 0.05, 0.02` (`0.524, 0.562, 0.674`) a
different wide band has taken over.  By `KRelaxedUpperEdgeMemoryless` the same `u` is the upper edge for
every memory `k` (measured for `k ≤ 12`).
Why it matters: rational affine edges are what a finite node-lemma refutation produces (`barrier_core`
has endpoints affine in `β`), so the exclusion `l > u(β)` is a treadmill-shaped target, and the two
coefficient pairs `(39/8, 3/4)` and `(105/16, 15/16)` name the parity words of the critical kills.  Both slopes are
`(3/2)^n + 3/2` (`39/8 = 27/8 + 3/2`, `105/16 = 81/16 + 3/2`, `n = 3, 4`), and the constants have denominator `2^n`:
the edge reads as a squeeze between the gap met after one move and the gap met after `n` moves.
Descent anatomy (2026-10-10, `ARC_TRACE=1 arc_sweep solve`, `β = 0.12`, `N = 2^16`).  At the edge (`l = 0.1495`) the
memoryless fixed point at residue `0` is `[0.0702, 0.1246] [0.1704, 0.3468] [0.3926, 0.5202] [0.6636, 0.7803]`; its
outer ends are `β - l/3` and the band edge `1 - β - 2l/3`, so `u(β)` is decided by the three internal gaps.  Just
above (`l = 0.155`) the set erodes over 6 steps.  The `k = 2` descent (dead at step 10) uses exactly the same
endpoint rationals (`0.12296, 0.16650, 0.34517, 0.38872, 0.49908, 0.67926, 0.74863, …`), shared out among the
residues, and through step 5 the memoryless set equals the intersection of the two parity-`0` residue sets of the
`k = 2` descent, cut for cut (step 6 differs).  So memory redistributes and delays the same cuts rather than
creating new ones.  Not by itself the mechanism: the delay game has the same preimage maps and still widens.
Measured more widely (`k = 2, 3, 4` at `(β, l) = (0.12, 0.155), (0.10, 0.263), (0.11, 0.22)`): the memoryless
survivor set after `n` steps equals the intersection, over residues of the same parity, of the `k`-memory survivor
sets after `n` steps, for every `n ≤ n₁ - 2`, where `n₁` (7, 7, 6) is the memoryless death step, independent of
`k`.  It fails at the last two steps, after which memory keeps sets alive for about two more moves per bit
(deaths at `10, 11, 13`; `9, 11, 14`; `7, 9, 11`).
**The edge is a bounded-depth kill.**  The memoryless descent empties in 7 steps at `l = u(β) + ε` for
`ε = 10⁻³, 10⁻⁴, 10⁻⁵` (`β = 0.12` and `0.105`, `N = 2^22`; 8 steps at `ε = 10⁻²`).  The exclusion above the
edge is now certified symbolically (`RelaxedAboveUpperEdge`), so the open parts of this band are the lower
exclusion (`RelaxedLowerEdge`, a runaway, not a finite cover) and the existence direction.
Confidence 85% after that certificate. -/
def RelaxedWidthBand : Prop :=
  ∀ β l : ℝ, 1 / 10 ≤ β → β ≤ 7 / 57 →
    ((∃ P : Set ℝ, RelaxedStrategy β (1 - 2 * β) l P) ↔
      (7 / 57 ≤ l ∧ l ≤ min (3 / 4 - 39 * β / 8) (15 / 16 - 105 * β / 16)))

open ArcTrap in
/-- **Conjecture (computationally certified): no memoryless relaxed strategy above the upper edge.**  The
exclusion half of `RelaxedWidthBand` above `u(β)`.  Confidence 95%.
Certificate (2026-10-10, `experiments/arc_band.py cover`, `test_cover_above_edge`): an exact descent
`P₀ = [0, 1]`, `P_{n+1} = P_n ∩ A₀ ∩ A₁`, `A_d = {a | [a, a + l/3] meets G ∩ (2/3)(P_n + j - d), j ≤ 2}`,
`G = [β, 1 - β - 2l/3] ∪ [1 + β, 2 - β - 2l/3]`, over closed intervals (an over-approximation, so emptiness
is sound), with every endpoint affine in `(β, l)`.  It runs on convex polygons and splits one along any
comparison that changes sign inside it.  Over the two pieces `u(β) < l ≤ 3/2 - 3β` (`β ∈ [1/12, 1/9]` and
`[1/9, 7/57]`), all 35 + 21 leaf polygons empty, within 7 and 8 steps respectively.  Above `3/2 - 3β` the
gate `G` is empty.  The 28 split lines all have a `β` term (none is horizontal), so a point on a split
line, or on `β = 1/10`, is reached by `RelaxedStrategy.mono` from a leaf interior just to its left.
Known-answer control: at `(β, l) = (0.12, 0.1501), (0.105, 0.2382), (0.1, 0.2626)` the exact point descent
empties in 6 steps; at `0.1495, 0.2380, 0.2624` it is live after 12 (`test_measure_twice_edge_point`).  The
live set at `(0.12, 0.1495)` is `P₀ ∩ P₁` of the Rust `k = 1` fixed point, interval for interval.
Proof shape: a Lean twin of the checker over affine forms (one soundness lemma for the symbolic step, then
`native_decide` per polygon), or node lemmas transcribed by a treadmill. -/
def RelaxedAboveUpperEdge : Prop :=
  ∀ β l : ℝ, 1 / 10 ≤ β → β ≤ 7 / 57 → min (3 / 4 - 39 * β / 8) (15 / 16 - 105 * β / 16) < l →
    ∀ P : Set ℝ, ¬ RelaxedStrategy β (1 - 2 * β) l P

/-- **The `k`-memory component game** (no window width).  A state is a window `[x, y]` of positions
`X = ξ (3/2)^n`.  The constructor keeps one component `[max x (j + β), min y (j + 1 - β)]` of the window
inside an arc lift.  Its image under `3/2` is known modulo `2^(k-1)`, and the adversary picks the lift:
every shift by `z 2^(k-1)` must stay in `S`.  For `k = 1` this is the component game of
`ArcTrap.relaxed_barrier`.  Absolute windows carry no extra information: a shift by `2^k` permutes the
moves (`j ↦ j + 2^k`) and moves the children by `3 · 2^(k-1)`, which the `∀ z` already absorbs. -/
def KComponentStrategy (β : ℝ) (k : ℕ) (S : Set (ℝ × ℝ)) : Prop :=
  S.Nonempty ∧ ∀ p ∈ S, ∃ j : ℤ, max p.1 (j + β) < min p.2 (j + 1 - β) ∧
    ∀ z : ℤ, (3 / 2 * max p.1 (j + β) + z * 2 ^ (k - 1),
      3 / 2 * min p.2 (j + 1 - β) + z * 2 ^ (k - 1)) ∈ S

/-- **Conjecture: no finite memory wins the component game past `7/57`.**  A width-free strengthening of
`ArcTrap.FiniteMemoryRelaxedValue` (`finiteMemoryRelaxedValue_of_componentK`), and `k = 1` is the
component game `ArcTrap.relaxed_barrier` already kills.  Confidence 70% (below the relaxed conjecture's 80%:
the constructor may vary the width, and at `k = ∞` this is the orbit problem itself, whose true threshold
is unknown).
Evidence (2026-10-10, exact rational AND-OR search, `k`-memory component game from every start residue, the
first depth at which every start dies): `β = 0.13`: `14, 16, 17, 21, 23` (`k = 1, …, 5`); `β = 1/8`: `19, 21, 22`
(`k = 1, 2, 3`); `β = 0.123` (just above `7/57 ≈ 0.12281`): `25, 29, 32` (`k = 1, 2, 3`).  The depth grows with `k`
(about two moves per bit, as in the fixed-width game), and it grows as `β ↓ 7/57`, as the `k = 1` runaway predicts.
Why it is a better target than the fixed-width game: one parameter fewer, and the `k = 1` proof (funnel
plus the `(0, 1/2, 1/2)` runaway from `10/19`) is already in Lean.  In the runaway the constructor's
components are unique, so its carries are forced and the adversary can set each top bit to produce the
parity it wants `k - 1` moves later.  But the first `k - 1` parities after the window turns clean were
committed earlier.  So the runaway transfers to every `k` only from a clean window whose committed bits
already spell the block pattern, and what stays open is a `k`-uniform funnel that arrives there.
Dead: an oblivious adversary.  At `β = 0.13` no periodic parity word of period `≤ 6` (any phase, played
against a constructor who knows it) kills the memoryless component game within 40 moves; at `β = 0.3`, 122
of the 126 words do (control).  So near `7/57` the adversary's adaptivity is essential, and a `k`-uniform
proof has to use the carries: a constructor who reads a fixed word ahead, with no carries (the delay
game's picture), beats every such word. -/
def ComponentKValue : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ S : Set (ℝ × ℝ), ¬ KComponentStrategy β k S

open ArcTrap in
/-- **Domination: the component game implies the fixed-width conjecture.**  From a live `k`-memory
relaxed strategy `P`, the windows containing some `[m + a, m + a + l]` with `a ∈ P (m mod 2^k)` form a
`KComponentStrategy`: the relaxed sub-window lies in one component, and its child's integer part is
`≡ (3r - r % 2)/2 + J (mod 2^(k-1))` with the top bit free, which is what `∀ z` asks for. -/
theorem finiteMemoryRelaxedValue_of_componentK (h : ComponentKValue) : FiniteMemoryRelaxedValue := by
  sorry

end CollatzMoonshot.Benchmark.ArcDelayGame
