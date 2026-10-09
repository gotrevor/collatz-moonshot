/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcTrap

/-!
# The price of one step of delay in the `k`-memory arc game

`FiniteMemoryRelaxedValue` asks that every memory size `k` lose past `7/57`.  Oblivious kills bound
every `k` at once but stall (near `0.1375` from `[m, m + 3)`, near `0.128` from unit starts), because the
constructor's lookahead keeps its start window wide.  This file sets up the other route: induction on
`k`.  The `k`-memory component game (`experiments/arc_kmemory.py`) is computable, so its kill relation
`advKills` is a `Bool`; `(k+1)`-memory is the `k`-game with each adversary bit committed one move earlier.
If one move of delay costs the adversary a bounded number of extra moves from every position
(`DelayCostBounded`), then the kill at `k = 1` lifts to every `k`.
-/

namespace CollatzMoonshot.Benchmark.ArcDelay

open CollatzMoonshot.Benchmark.ArcTrap

/-- Moves of the `k`-memory component game (`children` in `arc_kmemory.py`).  From window `[lo, hi]`
at residue `r` (`r mod 2` is the parity, so the shift `d = 1/2` or `0`), the constructor keeps a
component `[a, b]` of the window inside `Z + [β, 1 - β]`; the child window is `3/2 [a, b] + d` less its
floor `sh`, and the child residue mod `2^(k-1)` is `(3r - r mod 2)/2 + sh`.  The adversary then sets
the top bit. -/
def children (β : ℚ) (k : ℕ) (lo hi : ℚ) (r : ℕ) : List (ℚ × ℚ × ℕ) :=
  let d : ℚ := if r % 2 = 1 then 1 / 2 else 0
  let half := 2 ^ (k - 1)
  ((List.range (⌊hi⌋ - ⌊lo⌋ + 2).toNat).map fun i => ⌊lo⌋ - 1 + (i : ℤ)).filterMap fun j =>
    let a := max lo (j + β)
    let b := min hi (j + 1 - β)
    if a ≤ b then
      let nl := 3 / 2 * a + d
      let sh := ⌊nl⌋
      some (nl - sh, 3 / 2 * b + d - sh,
        if 1 < half then ((3 * r - r % 2) / 2 + sh.toNat) % half else 0)
    else none

/-- The adversary kills the `k`-memory constructor from `([lo, hi], r)` within `D` moves:
every component the constructor keeps has a top bit that kills its child within `D - 1`. -/
def advKills (β : ℚ) (k : ℕ) : ℕ → ℚ → ℚ → ℕ → Bool
  | 0, _, _, _ => false
  | D + 1, lo, hi, r => (children β k lo hi r).all fun c =>
      advKills β k D c.1 c.2.1 c.2.2 || advKills β k D c.1 c.2.1 (c.2.2 + 2 ^ (k - 1))

/-- **Base case, checked**: at `β = 0.13` the memoryless (`k = 1`) adversary kills `[0, 3]` at both
residues within 14 moves, the exact depth `arc_kmemory.py kill 0.13 1 40` reports. -/
theorem advKills_013_one : (List.range 2).all (fun r => advKills (13 / 100) 1 14 0 3 r) = true := by
  native_decide

/-- **The endgame window at `β = 1/8`, checked.**  Every endgame entry of the `k`-game's optimal kill
tree for `k = 1, 2, 3` (`arc_kmemory.py endgame`: states after which no optimal-tree descendant splits)
lies in `[11/64, 5/16]` or its mirror `[11/16, 53/64]`.  This is the image of the split piece
`[25/32, 7/8]` that touches the gap edge.  The memoryless adversary kills the window within 11 moves at
residue 0, the depth every entry shows.  Entries are anchored at a gap-edge image
(`1.5β`, `1.5β + 1/2`, `1.5(1-β)`, `1.5(1-β) - 1/2` mod 1, since split pieces touch a gap), so the library
is one width per anchor.  Largest entry widths, `k = 1, 2, 3, 4`:
* `β = 1/8`: `0.141, 0.141, 0.141, 0.183` (at `k = 4`, `[1289/2048, 13/16]`, memoryless depth 13 / 17 at residue 0 / 1).
* `β = 0.13`: `0.116, 0.209, 0.116, 0.209`.
* `β = 0.1229`: `0.131, 0.131` (`k = 1, 2`).
All are below the width `1/4` that Mechanism 8 kills at every offset (`obliviousKillAt_1229_tiles`).  So the
endgame is never the obstacle.  The obstacle is the parity string the opening must have committed:
no one string kills both mirror windows (mirroring flips every parity), and for `[11/64, 5/16]` only 4 of the `2^11`
strings kill within 11, and 78 of the `2^14` within 14. -/
theorem advKills_endgame_18 : advKills (1 / 8) 1 11 (11 / 64) (5 / 16) 0 = true ∧
    advKills (1 / 8) 1 10 (11 / 64) (5 / 16) 0 = false := by
  native_decide

/-- The kill relation with every adversary bit forced to `0`: the parities are then the committed
residue's own. -/
def obKills (β : ℚ) (k : ℕ) : ℕ → ℚ → ℚ → ℕ → Bool
  | 0, _, _, _ => false
  | D + 1, lo, hi, r => (children β k lo hi r).all fun c => obKills β k D c.1 c.2.1 c.2.2

/-- **The free ride.**  A bit the adversary sets after move `n` enters the residue at position `k - 1`
and sinks one position per move (carries only go up).  So it first becomes a parity at move `n + k`.
Within `D ≤ k` moves the adversary has no say: its kills are those of the committed residue alone.
Confidence 95%.  Consequence: from `[0, 3]` at every residue the kill depth exceeds `k`, since some
residue's committed parities let the constructor survive `k` moves.  So `StartDelayCostBounded β c`
needs `c ≥ 1` just to pay for the ride.  Measured: the escape window of the stall below costs about
one move per bit and `[0, 3]` about two. -/
theorem advKills_eq_obKills {β : ℚ} {k D : ℕ} (h : D ≤ k) (lo hi : ℚ) (r : ℕ) :
    advKills β k D lo hi r = obKills β k D lo hi r := by
  sorry

/-- **The stall at the real integer `-2`, `β = 0.13`.**  Every critical line of the `k`-game
(`k = 4`, every residue; `β = 1/8`, `k = 3`) has the same shape (`experiments/arc_kmemory.py`, line and
residue printouts):
1. A short opening.
2. The residue reaches `-1 mod 2^k`.
3. A stall of 4 to 5 two-way splits at residue `-2` or `0` (the 2-adic fixed points of
   `m ↦ (3m - p)/2 + sh`), where the window is genuine small reals receding from the fixed point `0`.
   The adversary commits 1-bits that need no information.
4. A tail.

During a stall the constructor's only escape is the same state every move:
`E = [17/400, 61/200]` (the image of the band piece `[1.5β + 1/2, 1 - β]`) at residue `-2`.  Its depth
for `k = 1, …, 9` is `9, 9, 12, 12, 12, 12, 14, 16, 17`.  The plateau is not `k`-uniform: by
`advKills_eq_obKills` a kill within `D ≤ k` is the real kill of `[-1.9575, -1.695]`, which survives 30
real steps.  So the plateau had to break, and it does at `k = 7`, into one move per bit.  At residue `-1`,
`[0, 3]` has depth `14, 16, 17, 19, 22, 22` (`k = 1, …, 6`).
Dead: "the constructor's choices are illusory".  At every split node of the optimal tree (`1/8`,
`k = 1, 2`; `0.13`, `k = 1, 3`) every piece survives 10 moves under some parity string.  Splits per
critical line grow one per bit (`1/8`: 6, 7, 8; `0.13`: 6, 7, 8, 9; `0.1229`: 7, 10), and the opening run
of consecutive splits lengthens by one per bit (`0.13`: 5, 6, 7 for `k = 2, 3, 4`), before a fixed tail. -/
theorem advKills_stall_013 : advKills (13 / 100) 3 12 (17 / 400) (61 / 200) 6 = true ∧
    advKills (13 / 100) 3 11 (17 / 400) (61 / 200) 6 = false := by
  native_decide

/-- **The hold: a waiting room that costs one move per bit, for every `k`.**  The parity word `10`
holds the window `E = [1.5(1.5β + 1/2) - 1, 1.5(1 - β) - 1]` on a single-piece 2-cycle:
1. Clip `E` to `[β, 1.5(1-β) - 1]`.
2. Apply `x ↦ 1.5x + 1/2`.
3. Clip at `1 - β`.
4. Apply `x ↦ 1.5x`, which gives `E + 1`.

The cycle runs around the periodic orbit `{1/5, 4/5}` (valid for `β < 1/5`).  The residue that realizes
it is the 2-adic integer `m = -1/5 = …00110011`, the solution of `(9m + 1)/4 = m`.  This is the only
single-piece periodic hold among the words of length `≤ 10` at `β = 0.13` and at `0.1229`; 3675 and 4516
other periodic orbits split as their window grows.

The constructor never has a choice in the hold, so the adversary loses nothing by committing early.  It
holds through the `k` committed moves and then plays an oblivious kill string from the hold window.
Measured depth from `(E, -1/5 mod 2^k)` at `β = 0.13`, `k = 1, …, 8`: `10, 11, 12, 15, 17, 18, 19, 20`.
That is `k + 12` from `k = 5` on: exactly the free ride (`advKills_eq_obKills`) and no more.  Compare
about two moves per bit from `[0, 3]`.  The proof shape is two finite checks (the cycle, a kill string
from each phase) plus the residue arithmetic that lets the adversary realize any parity string after
`k` moves.  Confidence 90%.  If true, the induction route reduces to an **opening** lemma: from `[0, 3]`
at every residue, reach the hold basin (a window inside the cycle at residue `-1/5 mod 2^k`) within
`k + C` moves.

At `β = 0.1229` the hold costs the same one move per bit with a larger constant (the hold window has
width `0.289`, over Mechanism 8's `1/4`): depth `22, 25, 28, 29, 31`, i.e. `k + 21, 23, 25, 25, 26`, for
`k = 1, …, 5`.

**The opening, measured.**  Forcing the hold basin or a kill from `[0, 3]` at `β = 0.13` takes `6, 10, 14,
15, 17, 19, 21, 22` moves for `k = 1, …, 8`, i.e. `k + 5, 8, 11, 11, 12, 13, 14, 14`: still creeping.
Every critical reach line has one shape:
1. The residue reaches `-1`.
2. A stall at the real integer `-2` or `0`.
3. A fixed exit: `E` (after one fresh top bit), then six more moves into the hold, or a fixed six-move death.

**Why these states.**  `(-1/5, 1/5)` is a decomposition of the real number `0` into a 2-adic integer
part and a fraction.  The stall windows at `-2` and `0` are real neighbourhoods of `0` too.  So the
adversary plays toward the fixed point `0` of `×3/2` on `ℝ × ℤ₂`.  There its digits are a known rational
expansion, which costs nothing to commit early.  What stays open is a `k`-uniform reason the residue can
be steered to `-1` despite the constructor's branching in the last `k` moves. -/
theorem advKills_hold_013 (k : ℕ) (hk : 1 ≤ k) (r : ℕ) (hr : r < 2 ^ k) (h5 : 2 ^ k ∣ 5 * r + 1) :
    advKills (13 / 100) k (k + 12) (17 / 400) (61 / 200) r = true := by
  sorry

/-- Instances of `advKills_hold_013`: the residues `1, 3, 3, 3` are `-1/5` mod `2, 4, 8, 16`. -/
theorem advKills_hold_013_small : advKills (13 / 100) 1 13 (17 / 400) (61 / 200) 1 = true ∧
    advKills (13 / 100) 2 14 (17 / 400) (61 / 200) 3 = true ∧
    advKills (13 / 100) 3 15 (17 / 400) (61 / 200) 3 = true ∧
    advKills (13 / 100) 4 16 (17 / 400) (61 / 200) 3 = true := by
  native_decide

/-- **Conjecture: one move of delay has bounded price.**  From every position, the `(k+1)`-memory
adversary kills within `c` moves of the `k`-memory adversary at the projected residue.  Confidence 30%.
Stronger than the induction needs (`StartDelayCostBounded`).
Evidence (`arc_kmemory.py gaps`, every state reachable in 8 moves from `[0, 3]`, depth cap 60): at
`β = 0.13` the largest price is 10, 10, 12, 13, 13 for `k = 1→2, …, 5→6`, and at `β = 0.125` it is 15,
15, 15, 16 for `k = 1→2, …, 4→5` (over about 1300 to 21000 states each), with no state where the
larger memory escapes.  The worst prices are rare (a few dozen states) and creep up slowly; most states
cost 0 to 2.  The maximum does not grow with depth: at `β = 0.125`, `k = 2→3`, it is 15 over the
positions reachable within 8, 12 and 16 moves (about 2600, 17000 and 100000 states).  The costliest
windows do not carry a growing price: tracked over every residue (`arc_kmemory.py track`, `β = 1/8`),
`[3/16, 543/2048]` costs 15, 2, 10, 7, 13 and `[1/32, 343/2048]` costs 10, 15, 15, 10, 13 for
`k = 1→2, …, 5→6`, while their deepest kill grows 18 → 30 and 14 → 29.  So the price is not the kill
depth in disguise: both depths grow together.  Locally (`arc_kmemory.py lag`, `β = 1/8`, `k = 1, 2, 3`)
some single bit always kills.  At positions with two components one bit is optimal for both 70 to 80%
of the time, with prices of at most 5, 10, 3.  This freedom is not mirror symmetry: no reachable split
has two equal components.  What stays open is why these one-step prices do not add up along a kill.  It is the quantitative form of the measured growth of
the kill depth (about two moves per bit).  A single memory-reduction statement at fixed `β` would only
restate `FiniteMemoryRelaxedValue` (vacuous below `7/57`, equivalent above), so the content is the
uniform constant.  Dead alternative: no simple potential-minimising adversary works for every `k`
(`experiments/arc_greedy.py`; it fails at `0.125` already for `k = 1`). -/
def DelayCostBounded (β : ℚ) (c : ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∀ (D : ℕ) (lo hi : ℚ) (r : ℕ), 0 ≤ lo → r < 2 ^ (k + 1) →
    advKills β k D lo hi (r % 2 ^ k) = true → advKills β (k + 1) (D + c) lo hi r = true

/-- **Conjecture: one move of delay has bounded price from the start.**  The weaker form of
`DelayCostBounded` the induction actually uses: only the start window `[0, 3]`.  Confidence 35%.
Evidence (`arc_kmemory.py mono`, `path`): on the `(k+1)`-game's optimal kill tree the price is nearly
non-increasing from the root (at `β = 1/8`: rises on 0 of 96, 2 of 162 and 1 of 325 edges for
`k = 1→2, 2→3, 3→4`, by at most 3).  Along each critical line the whole price is paid in the opening
from the wide start (3 components), stays flat, and is 0 for the last dozen moves.  The root prices are
the kill-depth increments, at most 5 so far (`β = 1/8`: 2, 1, 5, 1, 4; `β = 0.13`: 2, 1, 4, 2, 2, 2).
At `β = 0.13` rises are 0/89, 2/136, 2/316, 2/568 (`k = 1→2 … 4→5`, by at most 2); at `1/8`,
`k = 4→5`, 19/609 by 1.  The prices up to 16 seen over all reachable positions sit off the optimal
tree, where the adversary has already misplayed.  The endgame is stereotyped: on every critical line
the window stops splitting at width `0.117` or `0.141` (`β = 1/8`, 8 to 14 moves left) or `0.131`
(`β = 0.1229`, 15 moves left), the same across `k`.  From there the constructor has no choices, so the
rest is an oblivious narrow-start kill (Mechanism 8).  The opening's job is to commit bits that serve
as that kill's prefix. -/
def StartDelayCostBounded (β : ℚ) (c : ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∀ (D r : ℕ), r < 2 ^ (k + 1) →
    advKills β k D 0 3 (r % 2 ^ k) = true → advKills β (k + 1) (D + c) 0 3 r = true

theorem DelayCostBounded.start {β : ℚ} {c : ℕ} (h : DelayCostBounded β c) : StartDelayCostBounded β c :=
  fun k hk D r hr => h k hk D 0 3 r le_rfl hr

/-- Bounded delay cost lifts a memoryless kill to every memory size. -/
theorem advKills_of_delayCost {β : ℚ} {c D : ℕ} (h : StartDelayCostBounded β c)
    (h1 : ∀ r < 2, advKills β 1 D 0 3 r = true) :
    ∀ k, 1 ≤ k → ∀ r < 2 ^ k, advKills β k (D + (k - 1) * c) 0 3 r = true := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h1
  | succ k hk ih =>
    intro r hr
    have := h k hk _ r hr (ih _ (Nat.mod_lt _ (by positivity)))
    have e : D + k * c = D + (k - 1) * c + c := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp [add_mul, add_assoc]
    rw [Nat.add_sub_cancel, e]
    exact this

/-- **Soundness: the component game dominates the relaxed game.**  A `k`-memory relaxed strategy
(`KRelaxedStrategy`) keeps a window of width `l` inside one component, so a kill of every residue from
`[0, 3]` in the component game kills it.  Confidence 85% (the domination `arc_kmemory.py` was built on;
the start `[0, 3]` covers the `TrapsResidueClass` window). -/
theorem not_kRelaxedStrategy_of_advKills {β : ℚ} {k D : ℕ} (hk : 1 ≤ k)
    (h : ∀ r < 2 ^ k, advKills β k D 0 3 r = true) (l : ℝ) (P : ℕ → Set ℝ)
    (hne : ∃ r < 2 ^ k, (P r).Nonempty) : ¬ KRelaxedStrategy (β : ℝ) (1 - 2 * β) l k P := by
  sorry

/-- **The induction route to `FiniteMemoryRelaxedValue`**: a bounded delay cost and a memoryless
kill at each rational `β` past `7/57` give the conjecture. -/
theorem finiteMemoryRelaxedValue_of_delayCost
    (h : ∀ β : ℚ, 7 / 57 < β → β < 1 / 2 → ∃ c D : ℕ, StartDelayCostBounded β c ∧
      ∀ r < 2, advKills β 1 D 0 3 r = true) : FiniteMemoryRelaxedValue := by
  intro k hk β hβ hβ' l P hne hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hβ
  have e1 : (7 / 57 : ℝ) = ((7 / 57 : ℚ) : ℝ) := by push_cast; ring
  have e2 : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; ring
  obtain ⟨c, D, hc, h1⟩ := h q (by rw [e1] at hq1; exact_mod_cast hq1)
    (by have := hq2.trans hβ'; rw [e2] at this; exact_mod_cast this)
  exact not_kRelaxedStrategy_of_advKills hk (advKills_of_delayCost hc h1 k hk) l P hne
    (hS.mono hq2.le)

end CollatzMoonshot.Benchmark.ArcDelay
