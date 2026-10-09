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
The prices up to 16 seen over all reachable positions sit off the optimal tree, where the
adversary has already misplayed. -/
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
