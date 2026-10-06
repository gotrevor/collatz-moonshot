/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Trapping `{ξ (3/2)^n}` in an arc: certified nested-interval games

Mahler's Z-numbers are `ξ > 0` with every `{ξ (3/2)^n}` in the arc `[0, 1/2)`.  This file records
the constructive side of the same question: arcs that provably *do* trap some orbit.

**Known (cited):** no arc shorter than `1/3` traps any `ξ > 0` (Flatto–Lagarias–Pollington 1995,
Thm 1.4); `‖ξ (3/2)^n‖ ≥ 4/65` for uncountably many `ξ` (Pollington 1981); `‖ξ (3/2)^n‖ > 5/48` for
infinitely many `ξ` (Dubickas 2008, the best constant found); `‖ξ (3/2)^n‖ < 1/3` for
countably infinitely many `ξ` (Akiyama–Frougny–Sakarovitch / Akiyama 2008).

**New (2026-10-05):** `‖ξ (3/2)^n‖ ≥ 307/2500 = 0.1228` via the memoryless *relaxed* game
(`exists_farFromIntegers_1228`, certificate `experiments/arc_cert_beta_1228_vw_k0.json`), whose value
appears to be exactly `7/57` (`RelaxedValueIsSevenFiftySevenths`).  First pass, window-in-arc game:
`1227/10000` for some `ξ > 0`, beating Dubickas's `5/48 ≈ 0.1042` (novelty ~85%, see the note).  The
certificate is a game strategy that remembers the integer part mod 4 (`experiments/arc_trap_k.py`):
for each residue `r` a finite union `P r` of rational intervals of window left ends, closed under one
step of `×3/2` for both values of the unseen next bit.
-/

namespace CollatzMoonshot.Benchmark.ArcTrap

/-- Every `{ξ (3/2)^n}` lies in the closed arc `[β, 1 - β]`, i.e. `‖ξ (3/2)^n‖ ≥ β`. -/
def FarFromIntegers (β ξ : ℝ) : Prop :=
  ∀ n : ℕ, β ≤ Int.fract (ξ * (3 / 2) ^ n) ∧ Int.fract (ξ * (3 / 2) ^ n) ≤ 1 - β

namespace Literature

/-- Pollington, *Progressions arithmétiques généralisées et le problème des (3/2)^n*,
C. R. Acad. Sci. Paris 292 (1981) 383–384, as cited by Flatto–Lagarias–Pollington, Acta Arith. 70
(1995) p. 128: `Z_{3/2}(4/65, 61/65)` has positive Hausdorff dimension.  Stated weaker (existence). -/
def Pollington1981 : Prop := ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (4 / 65) ξ

/-- Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. 281 (2008) 951–958,
Thm 1.3: every interval `(k, k + 1)` contains `ξ` with `‖ξ (3/2)^n‖ > 5/48` for every `n ≥ 0` (proof by
a two-player game, Lemma 1.4).  Stated weaker (one positive `ξ`, closed arc).  The best published
constant found (2026-10-05); Dubickas notes Pollington had announced `0.088`. -/
def Dubickas2008 : Prop := ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (5 / 48) ξ

/-- Dubickas, *On the distance from a rational power to the nearest integer*, J. Number Theory 117
(2006) 222–239, Cor. 1: for `ξ ≠ 0`, `‖ξ (3/2)^n‖` has a limit point `≤ (1 + T(2/3))/4 = 0.285647…`
(`T` the Thue–Morse product).  Stated weaker: no `ξ > 0` stays `2857/10000` away from the integers.
With `Dubickas2008` it brackets `sup_ξ inf_n ‖ξ (3/2)^n‖` in `[5/48, 0.2857)`. -/
def Dubickas2006 : Prop := ¬ ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (2857 / 10000) ξ

/-- **Flatto 1992, Thm 6.1** (*Z-numbers and β-transformations*, Contemp. Math. 135, pp. 181–201,
doi:10.1090/conm/135/1185087): Z-numbers up to `x` number `O(x^{log₂(3/2)})`.  Stated here for
integer parts below `2^N` (at most one Z-number per unit interval).  Flatto treats only arcs
`[0, t)`; general positions, the `2/3` edge and `finiteMemoryEdgeIsTwoThirds` are not in it. -/
def Flatto1992 : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, (Nat.card {g : Fin (2 ^ N) // ∃ ξ : ℝ, 0 < ξ ∧ ⌊ξ⌋ = ((g : ℕ) : ℤ) ∧
    ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2} : ℝ) ≤ C * (3 / 2) ^ N

end Literature

/-- A `k`-memory strategy for the arc `[s, s + t]` with window width `l`: for each residue
`r mod 2^k` of the integer part, a set `P r` of window left ends `a ∈ [0, 1)` such that the window
`[a, a + l]` sits in the arc mod 1, and one `×3/2` step can always continue.  The step: from integer
part `m ≡ r` and left end `a`, the new left end is `c ∈ [3a/2 + d, 3a/2 + d + l/2]` (relative to
`⌊3m/2⌋`, with `d = (r mod 2)/2`), whose integer offset `j = ⌊c⌋` and fractional part must land in
`P r'` for **both** lifts `r'` of the known `(k-1)` low bits of `⌊3m/2⌋ + j`. -/
def WinningStrategy (k : ℕ) (s t l : ℝ) (P : ℕ → Set ℝ) : Prop :=
  0 < l ∧ (∃ r < 2 ^ k, (P r).Nonempty) ∧
  ∀ r < 2 ^ k, ∀ a ∈ P r,
    (0 ≤ a ∧ a < 1 ∧ ∀ x ∈ Set.Icc a (a + l), s ≤ Int.fract x + (if Int.fract x < s then 1 else 0) ∧
      Int.fract x + (if Int.fract x < s then 1 else 0) ≤ s + t) ∧
    ∃ c : ℝ, 3 * a / 2 + (r % 2 : ℕ) / 2 ≤ c ∧ c ≤ 3 * a / 2 + (r % 2 : ℕ) / 2 + l / 2 ∧
      ∀ r' < 2 ^ k, r' % 2 ^ (k - 1) = ((3 * r - r % 2) / 2 + ⌊c⌋.toNat) % 2 ^ (k - 1) →
        Int.fract c ∈ P r'

/-- **Why soundness needs `0 < k`.**  With `k = 0` the definition never lets the adversary pick
the parity of the integer part, so this trivial strategy "wins" the arc `[0, 1/10]`.  Soundness at
`k = 0` would then trap some `ξ > 0` in an arc shorter than `1/3`, which Flatto–Lagarias–Pollington
1995 (Thm 1.4) rules out. -/
theorem winningStrategy_zero_tiny :
    WinningStrategy 0 0 (1 / 10) (1 / 10) (fun _ => {0}) := by
  refine ⟨by norm_num, ⟨0, by norm_num, ⟨0, rfl⟩⟩, ?_⟩
  intro r hr a ha
  obtain rfl : r = 0 := by simpa using hr
  rw [Set.mem_singleton_iff] at ha
  subst ha
  refine ⟨⟨le_rfl, by norm_num, ?_⟩, 0, by simp, by norm_num, ?_⟩
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0, by linarith⟩
    rw [hf, if_neg (not_lt.mpr hx0)]
    constructor <;> linarith
  · intro r' _ _
    simp

/-- **Soundness of the game.**  A winning `k`-memory strategy yields some `ξ > 0` whose whole
`(3/2)^n` orbit has fractional parts in the arc.
Confidence 90% (the statement's encoding of "both lifts" and of the wrap-around arc needs review).
`0 < k` is needed: at `k = 0` the encoding pins the parity offset `d` to `0` instead of letting the
adversary choose it, and `winningStrategy_zero_tiny` then wins a `1/10` arc, against FLP's `1/3`.
Proof: start at integer part `m₀ ≥ 1` with `m₀ ≡ r` and `a₀ ∈ P r`; the strategy picks nested
closed intervals `J_n = {ξ : ξ (3/2)^n ∈ [m_n + a_n, m_n + a_n + l]}`, each nonempty because
`[c, c + l] ⊆ [y, y + 3l/2]`; take `ξ ∈ ⋂ J_n`. -/
theorem exists_trapped_of_winningStrategy {k : ℕ} {s t l : ℝ} {P : ℕ → Set ℝ} (hk : 0 < k)
    (h : WinningStrategy k s t l P) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x := by
  sorry

/-- **New constant (window-in-arc game; superseded by `exists_farFromIntegers_1228`).**  Some `ξ > 0`
keeps every `(3/2)^n ξ` at distance at least `1227/10000`
from the integers (Dubickas 2008: `5/48 ≈ 0.1042`; Pollington 1981: `4/65 ≈ 0.0615`).
Confidence 85% (exact rational fixed point; an independent exact construction tracking the integer
part ran 250 steps from 5 starts with random valid choices, never stuck, all `‖·‖ ≥ 0.124`; novelty ~85%:
forward citations of FLP 1995, Dubickas 2006 and 2008 checked; Bugeaud's 2012 book unread).
Proof: instantiate `exists_trapped_of_winningStrategy` with `k = 2`, `s = 1227/10000`,
`t = 1 - 2s`, `l = 26411/300000` and the intervals of `experiments/arc_cert_beta_1227_k2.json`; the closure is a finite set of rational inequalities. -/
theorem exists_farFromIntegers_1227 :
    ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (1227 / 10000) ξ := by
  sorry

/-! ### The relaxed, memoryless game

Only the sub-window the next step selects has to lie in the arc, because every `ξ (3/2)^n` of the
final `ξ` lands there.  This game dominates `WinningStrategy` and needs no memory at all: its value for
`[β, 1 - β]` came out as `7/57` to `1e-8` with `0..3` bits of memory alike
(`experiments/arc_trap_k.py`, `solve_vw`). -/

/-- A memoryless relaxed strategy for the arc `[s, s + t]` with window width `l`: a set `P` of window
left ends.  Seeing the parity offset `d ∈ {0, 1/2}` of the current integer part (chosen by an
adversary), the strategy picks a sub-window `[u, u + 2l/3] ⊆ [a, a + l]` lying in a lift of the arc;
the child window `1.5 · (m + [u, u + 2l/3])` has left end `c = 3u/2 + d` past `⌊3m/2⌋`, and
`Int.fract c` must lie in `P` again. -/
def RelaxedStrategy (s t l : ℝ) (P : Set ℝ) : Prop :=
  0 < l ∧ P.Nonempty ∧ P ⊆ Set.Ico 0 1 ∧
  ∀ a ∈ P, ∀ d ∈ ({0, 1 / 2} : Set ℝ), ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
    (∃ k : ℤ, (k : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ k + s + t) ∧ Int.fract (3 * u / 2 + d) ∈ P

/-- **Soundness of the relaxed game.**
Confidence 90%.  Proof: pick `m₀ ≥ 1` and `a₀ ∈ P`; at step `n` the window is `m_n + [a_n, a_n + l]`,
`d = (m_n mod 2)/2`, the strategy gives `u_n`, and `m_{n+1} = ⌊3m_n/2⌋ + ⌊c⌋`, `a_{n+1} = fract c` with
`c = 3u_n/2 + d`, since `3(m_n + u_n)/2 = ⌊3m_n/2⌋ + c`.  The closed intervals
`J_n = (m_n + [u_n, u_n + 2l/3]) / (3/2)^n` are nested and nonempty; any `ξ ∈ ⋂ J_n` has
`ξ (3/2)^n ∈ m_n + [u_n, u_n + 2l/3]`, inside a lift of the arc, and `ξ ≥ m₀ / 1 > 0`. -/
theorem exists_trapped_of_relaxedStrategy {s t l : ℝ} {P : Set ℝ} (h : RelaxedStrategy s t l P) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x := by
  sorry

/-- **New constant, sharpened.**  Some `ξ > 0` keeps every `(3/2)^n ξ` at distance at least
`307/2500 = 0.1228` from the integers (Dubickas 2008: `5/48 ≈ 0.1042`).
Confidence 90% (exact lattice post-fixed point; the independent exact orbit check in
`test_relaxed_certificate_orbits_stay_far`).  Proof: `exists_trapped_of_relaxedStrategy` with
`s = 307/2500`, `t = 1 - 2s`, `l = 123/1000` and the eleven intervals of
`experiments/arc_cert_beta_1228_vw_k0.json` (denominator `2^24`); for `x ∈ [s, 1 - s]`,
`Int.fract x = x`. -/
theorem exists_farFromIntegers_1228 :
    ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (307 / 2500) ξ := by
  sorry

/-- **Above the edge, no memoryless relaxed strategy.**  At `β = 13/100` (arc `[0.13, 0.87]`) no
width and no state set win.
Confidence 85%.  Evidence and proof route: a relaxed strategy is dominated by the component game,
where the constructor keeps a whole component of `W ∩ (arc lifts)` (bigger windows dominate) and
starts from the full arc.  The exact minimax `experiments/arc_minimax.py depth 13/100 1 30` forces it
out at depth 15.  A proof transcribes that finite refutation tree, rational endpoints throughout. -/
theorem not_relaxedStrategy_13_100 (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy (13 / 100) (1 - 2 * (13 / 100)) l P := by
  sorry

/-! ### The quantity itself -/

/-- `E α`: how far an orbit `ξ, ξα, ξα², …` (`ξ > 0`) can stay from the integers, i.e.
`sup_{ξ > 0} inf_{n ≥ 0} ‖ξ αⁿ‖`.  Using `lim inf` instead of `inf` gives the same value: start the
orbit at `ξ α^N`.  Whether the supremum is attained for `α = 3/2` is not known to us. -/
noncomputable def E (α : ℝ) : ℝ :=
  sSup {β : ℝ | ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, β ≤ |ξ * α ^ n - round (ξ * α ^ n)|}

/-- Calibration: `E 2 = 1/3`.  Confidence 95%.  Proof: `ξ = 1/3` gives `2ⁿ/3 ≡ ±1/3`.  Conversely, if
`x` and `2x` both lie in `[β, 1 - β]` mod 1 with `β > 1/3`, then `x ∈ [1/6, 1/3] ∪ [2/3, 5/6]`, which
misses `[β, 1 - β]`. -/
theorem E_two : E 2 = 1 / 3 := by
  sorry

/-- Calibration: `E 3 = 1/2`, via `ξ = 1/2` (every `3ⁿ/2` is a half-integer).  Confidence 98%. -/
theorem E_three : E 3 = 1 / 2 := by
  sorry

/-- Lower bound from the relaxed-game certificate.  Confidence 90%.  Proof: `exists_farFromIntegers_1228`,
and `FarFromIntegers β ξ` gives `β ≤ |y - round y|` for each `y = ξ (3/2)^n`; `E (3/2) ≤ 1/2` bounds
the set. -/
theorem E_three_halves_ge : 307 / 2500 ≤ E (3 / 2) := by
  sorry

/-- Upper bound from Dubickas 2006 (Cor. 1).  Confidence 95% given the literature input. -/
theorem E_three_halves_le (h : Literature.Dubickas2006) : E (3 / 2) ≤ 2857 / 10000 := by
  sorry

/-- **Barrier: above `7/57` no memoryless relaxed strategy exists.**  Treating each parity bit as
adversarial caps the construction at `7/57`.
Confidence 90% (computer-assisted step checked exactly; hand steps below).  Proof route:
* Domination: a relaxed strategy is dominated by the component game.  There the adversary picks
  `d` each step, the constructor keeps a whole component of `W ∩ (arc lifts)`, and `W` becomes
  `1.5 · C + d` mod 1.  Integer shifts are irrelevant and a larger window is never worse.
* Funnel (`experiments/arc_barrier.py verify`): for `β ∈ (7/57, 0.1229]` an adaptive adversary
  forces, within 13 moves, death or a window inside `[x₀, R₀]` with `x₀ > 10/19`, `R₀ = 1 - 9β/4`.
  This is an exact AND-OR search with endpoints affine in `β`: 3 open `β`-pieces and 3 split points.
  The arc's left edge after two `1/2`-steps sits at `9β/4 + 1/4 > 10/19 ⟺ β > 7/57`.
* Runaway: for `β ∈ (4/35, 4/19)` the block `(0, 1/2, 1/2)` either kills `[x, R₀]` (when
  `3x/2 ≥ 1 - β`) or maps it to `[g x, R₀]` with `g x = 27x/8 - 5/4`.  The components are unique
  because `3R₀/2 < 1 + β` and `3R₀/2 > 1 - β`.  `g x - x = (19/8)(x - 10/19)` grows geometrically.
* Monotonicity: for `β > 0.1229` play the `0.1229` adversary against the larger shadow window. -/
theorem relaxed_barrier (β : ℝ) (hβ : 7 / 57 < β) (hβ' : β < 1 / 2) (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy β (1 - 2 * β) l P := by
  sorry

/-- **Mahler barrier: no memoryless relaxed strategy holds any arc of length at most `1/2`.**  In
particular none traps an orbit in Mahler's arc `[0, 1/2]`: a construction that treats every unseen
parity as adversarial cannot produce a Z-number.
Confidence 90%.  Proof route:
* Domination by the component game (as for `relaxed_barrier`).
* Containment: an arc of length `t ≤ 1/2` lies inside `[s, s + 1/2]`, and a smaller arc only helps
  the adversary.
* `experiments/arc_mahler.py verify`: for every position `s ∈ [0, 1)` the adversary kills every path
  within 5 moves.  This is an exact AND-OR search with endpoints affine in `s`: 22 open `s`-pieces and
  22 exact points.
* For `t < 1/2` there is also a hand proof.  `A` and `A + 1/2` are disjoint, so the adversary keeps at
  most half of `1.5 |C|` in the arc and `|C|` shrinks by `3/4` per move.  Once the window is shorter
  than `1/2 - t` it misses `A` or `A - 1/2`, and the adversary picks the parity that misses.
Scope: memoryless strategies.  `finiteMemory_barrier` covers every finite memory, up to length
`13/20`. -/
theorem mahler_barrier (s t : ℝ) (ht : t ≤ 1 / 2) (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy s t l P := by
  sorry

/-- Mahler's own arc. -/
theorem no_relaxedStrategy_mahler_arc (l : ℝ) (P : Set ℝ) : ¬ RelaxedStrategy 0 (1 / 2) l P :=
  mahler_barrier 0 (1 / 2) le_rfl l P

/-! ### Finite memory: a counting barrier (Flatto's entropy method on an arbitrary arc) -/

/-- `g` is the integer part of some `ξ > 0` whose whole orbit `{ξ (3/2)^n}` lies in the arc
`[s, s + t]` (mod 1). -/
def TrappedFloor (s t : ℝ) (g : ℕ) : Prop :=
  ∃ ξ : ℝ, 0 < ξ ∧ ⌊ξ⌋ = (g : ℤ) ∧
    ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x

/-- What a finite-memory construction delivers.  A strategy that reads only `m mod 2^k` wins from
every start `m ≡ r`, so every such `m` has a trapped orbit within `3` of it. -/
def TrapsResidueClass (s t : ℝ) (k r : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m % 2 ^ k = r → ∃ g : ℕ, m ≤ g ∧ g < m + 3 ∧ TrappedFloor s t g

/-- **A memoryless relaxed strategy traps every unit interval.**  The strategy never reads the
integer part, so it runs from the window `[m + a, m + a + l]` for every `m ≥ 1`.  The sub-window
`[u, u + 2l/3]` fits in an arc lift, so `l ≤ 3t/2 ≤ 3/2` and `⌊ξ⌋ < m + 3`.
Confidence 90% (the construction in `exists_trapped_of_relaxedStrategy`, started at `m`; it is
also what `vw_orbit` in `experiments/arc_trap_k.py` plays from any `m0`).  The `k`-memory games of
`arc_trap_k.py` give `TrapsResidueClass s t k r` the same way. -/
theorem trapsResidueClass_of_relaxedStrategy {s t l : ℝ} {P : Set ℝ} (ht : t ≤ 1)
    (h : RelaxedStrategy s t l P) : TrapsResidueClass s t 0 0 := by
  sorry

/-- **Finite-memory barrier: no construction that works on a whole residue class mod `2^k` traps
an orbit in any arc of length at most `13/20`.**  In particular no finite-memory strategy, of any
game version, reaches Mahler's arc.  Flatto's `X^{log₂(3/2)}` count of Z-numbers is the
`[0, 1/2)` case of the counting step below; the rest is new.
Confidence 85% (exact certificate; the hand steps below).  Proof route:
* Digits.  With `g_n = ⌊ξ (3/2)^n⌋` and `f_n` the fractional part, `a_n = g_{n+1} - 3 g_n / 2
  = 3 f_n / 2 - f_{n+1}` lies in `{-1/2, 0, 1/2, 1}`.
* Injectivity.  `3^N g_0 = 2^N g_N - Σ 3^{N-1-n} 2^{n+1} a_n`, so the first `N` digits fix
  `g_0 mod 2^N`.  Hence `#{g < 2^N : TrappedFloor s t g}` is at most `W_N`, the number of digit
  words with every `f_n` in the arc.
* Growth.  `experiments/arc_entropy.py cover 13/20 2000 320` covers every position `s` by the arc
  `[i/2000, i/2000 + 13/20 + 1/2000]`.  For each it builds the transfer matrix on outward-rounded
  states (grid `1/320`, an overcount) and checks a rational `v > 0` with `M v ≤ c v` exactly; the
  worst `c` is `999/500 < 2`.  So `W_N ≤ C (999/500)^N`, and a smaller arc only lowers `W_N`.
* Density.  `TrapsResidueClass s t k r` gives at least `2^{N-k}/3 - 1` trapped floors below
  `2^N + 3`, which beats `C (999/500)^N` for large `N`.
Measured edge: at grid `1/320` the certificate fails at length `33/50`.  The memoryless game's
shortest holdable arc is `≈ 0.683` (at `s ≈ 0.65`), the same for `0..3` bits of memory. -/
theorem finiteMemory_barrier (s t : ℝ) (ht : t ≤ 13 / 20) (k r : ℕ) :
    ¬ TrapsResidueClass s t k r := by
  sorry

/-- The memoryless corollary.  It extends `mahler_barrier` from length `1/2` to `13/20`. -/
theorem relaxed_barrier_13_20 (s t : ℝ) (ht : t ≤ 13 / 20) (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy s t l P := fun h =>
  finiteMemory_barrier s t ht 0 0 (trapsResidueClass_of_relaxedStrategy (by linarith) h)

/-! ### The finite-memory edge is `2/3` -/

/-- A digit word `a` of length `N` is admissible for the arc `[s, s + t]` when some sequence of
fractional parts in the arc follows it: `f_{i+1} = 3 f_i / 2 - a_i / 2` (digit `a_i / 2`). -/
def AdmissibleWord (s t : ℝ) (N : ℕ) (a : Fin N → ℤ) : Prop :=
  ∃ f : Fin (N + 1) → ℝ, (∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x) ∧
    ∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2

/-- **Counting cannot pass `2/3`.**  For every arc of length `2/3` that does not wrap, at least
`2^N` digit words are admissible, so the counting step of `finiteMemory_barrier` fails there.
The same arithmetic puts Flatto–Lagarias–Pollington's edge at `1/3` (one word) and Flatto's
Z-number exponent at `log₂(3/2)` (length `1/2`).
Confidence 85% (hand proof; `arc_entropy.py` brackets the growth at `2` for every position tested,
wrapping arcs included).  Proof: let `(Pφ)(f) = Σ_a φ(3f/2 - a/2)` over admissible digits.  Since
`3/2 · I` has length exactly `1`, almost every `y ∈ I` has exactly two half-integers `a/2` with
`y + a/2 ∈ 3I/2`, so `∫_I Pφ = (2/3) · 2 · ∫_I φ`.  Hence
`Σ_w |C_w| = ∫_I P^N 1 = (4/3)^N · 2/3`.  Each cylinder `C_w` has length at most `(2/3)^N · 2/3`,
because `f ↦ f_N` has slope `(3/2)^N` into `I`.  Dividing gives at least `2^N` words. -/
theorem two_pow_le_card_admissibleWord (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 3) (N : ℕ) :
    2 ^ N ≤ Nat.card {a : Fin N → ℤ // AdmissibleWord s (2 / 3) N a} := by
  sorry

/-- **The game reaches the edge at the Akiyama–Frougny–Sakarovitch arc.**  A memoryless relaxed
strategy holds `[2/3 - 10⁻⁶, 4/3 + 10⁻⁶]`, i.e. `‖ξ (3/2)^n‖ ≤ 1/3 + 10⁻⁶`.  This works from every
integer part, a positive density, whereas AFS give countably many `ξ` with `‖ξ (3/2)^n‖ < 1/3`.
Confidence 85% (exact lattice post-fixed point `solve_vw` with width `l = 1000003/2000000`; exact
orbits from `m₀ = 1, 2, 3, 100` stay within `1/3 + 10⁻⁶`, `test_game_reaches_afs_arc`).  The game
fails on `[2/3, 4/3 + 10⁻⁶]` and on `[2/3 - 10⁻⁶, 4/3]`. -/
theorem relaxedStrategy_near_afs :
    ∃ l P, RelaxedStrategy (2 / 3 - 1 / 10 ^ 6) (2 / 3 + 2 / 10 ^ 6) l P := by
  sorry

theorem trapsResidueClass_near_afs :
    TrapsResidueClass (2 / 3 - 1 / 10 ^ 6) (2 / 3 + 2 / 10 ^ 6) 0 0 := by
  obtain ⟨l, P, h⟩ := relaxedStrategy_near_afs
  exact trapsResidueClass_of_relaxedStrategy (by norm_num) h

/-! ### Below `2/3`: a hand proof that digit words grow slower than `2^N` -/

/-- A digit path of length `N` from `p` to `q` inside the arc: fractional parts `f_0 = p, …,
f_N = q` in the arc with `f_{i+1} = 3 f_i / 2 - a_i / 2`. -/
def ArcPath (s t : ℝ) (N : ℕ) (p q : ℝ) (a : Fin N → ℤ) : Prop :=
  ∃ f : Fin (N + 1) → ℝ, (∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x) ∧
    (∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2) ∧
    f 0 = p ∧ f (Fin.last N) = q

/-- **Forward paths from a point grow at most like Fibonacci (arcs shorter than `3/4`).**
Confidence 90% (hand proof).  A point has at most two successors, `y` and `y + 1/2`.  If both branch
again, their four successors are `z, z + 1/4, z + 1/2, z + 3/4` mod 1, and an arc holding all four
has length at least `3/4`.  So of two sibling successors at most one branches, and the count
`M_n` satisfies `M_n ≤ M_{n-1} + M_{n-2}`. -/
theorem card_forward_le (s t p : ℝ) (ht : t < 3 / 4) (N : ℕ) :
    Nat.card {a : Fin N → ℤ // ∃ q, ArcPath s t N p q a} ≤ Nat.fib (N + 2) := by
  sorry

/-- **Backward paths into a point lose a branch within `K` steps once `(2/3)^(K-1) < 2 - 3t`.**
Confidence 85% (hand proof; `arc_entropy.py backward` samples the full depth, never above the
bound).  Proof: in the coordinate `v = 3 · ((f - s) mod 1) ∈ [0, 3t]`, the predecessors of `v` are
the points of `2v/3 - s + ℤ` in `[0, 3t]`.  These are `w = frac(2v/3 - s)` and also `w + 1` exactly
when `w ≤ τ := 3t - 1`.  In a tree that is full to depth `j`, the depth-`j` values `w` arise from
one point by `j` rounds of `w ↦ frac(2w/3 - s)` and `w ↦ frac(2w/3 + 2/3 - s)`.  Each round
multiplies the largest circular gap by `2/3`, so the gaps are at most `(2/3)^j`.  Once
`(2/3)^j < 1 - τ = 2 - 3t`, some node falls in `(τ, 1)` and has one predecessor. -/
theorem card_backward_le (s t q : ℝ) (ht : t < 2 / 3) (K : ℕ) (hK : 1 ≤ K)
    (hK' : (2 / 3 : ℝ) ^ (K - 1) < 2 - 3 * t) :
    Nat.card {a : Fin K → ℤ // ∃ p, ArcPath s t K p q a} ≤ 2 ^ K - 1 := by
  sorry

/-- **Digit words grow strictly slower than `2^N` on every arc shorter than `2/3`.**
Confidence 85%.  Proof: every component of a word's cylinder has a left endpoint `ℓ` where some
`f_j(ℓ)` is a left edge `b` of the arc (`b = s`, or `b = 0` when the arc wraps).  So the word is a
backward path of length `j` into `b` followed by a forward path of length `N - j` from just right of
`b`.  Hence `W_N ≤ 2 Σ_j B_j M_{N-j} ≤ C (N + 1) λ^N` with `λ = max(φ, (2^K - 1)^{1/K}) < 2`, by
`card_forward_le` and `card_backward_le`. -/
theorem admissibleWord_growth_lt_two (s t : ℝ) (ht : t < 2 / 3) :
    ∃ C lam : ℝ, lam < 2 ∧ ∀ N : ℕ, (Nat.card {a : Fin N → ℤ // AdmissibleWord s t N a} : ℝ) ≤
      C * lam ^ N := by
  sorry

/-- **Finite-memory barrier, all the way to `2/3`.**  No construction that works on a whole residue
class mod `2^k` traps orbits in any arc shorter than `2/3`.
Confidence 85%.  Proof: `admissibleWord_growth_lt_two`, plus the injectivity and density steps of
`finiteMemory_barrier` (`N` digits fix `g_0 mod 2^N`; a residue class gives `≥ 2^{N-k}/3 - 1`
trapped floors below `2^N + 3`). -/
theorem finiteMemory_barrier_two_thirds (s t : ℝ) (ht : t < 2 / 3) (k r : ℕ) :
    ¬ TrapsResidueClass s t k r := by
  sorry

/-- **The finite-memory edge is exactly `2/3`** (stated here; `finiteMemoryEdgeIsTwoThirds` below).  No residue-class construction holds
an arc shorter than `2/3`, and arcs just past the AFS arc `{‖x‖ ≤ 1/3}` are held.  So the
counting obstruction is sharp at the best position.  At other positions the game needs
`0.73`–`0.90`, while the counting edge stays at `≈ 2/3` everywhere.
First half: hand proof (`finiteMemory_barrier_two_thirds`, 85%).  Second half: PROVED from the
closed arc (`relaxedStrategy_afs_closed`, `finiteMemory_min_arc_two_thirds`). -/
def FiniteMemoryEdgeIsTwoThirds : Prop :=
  (∀ s t : ℝ, t < 2 / 3 → ∀ k r : ℕ, ¬ TrapsResidueClass s t k r) ∧
  (∀ ε : ℝ, 0 < ε → TrapsResidueClass (2 / 3 - ε) (2 / 3 + 2 * ε) 0 0)

/-- The conjecture is now exactly its second half: arcs just past the AFS arc are held. -/
theorem finiteMemoryEdgeIsTwoThirds_iff :
    FiniteMemoryEdgeIsTwoThirds ↔
      ∀ ε : ℝ, 0 < ε → TrapsResidueClass (2 / 3 - ε) (2 / 3 + 2 * ε) 0 0 :=
  ⟨fun h => h.2, fun h => ⟨fun s t ht k r => finiteMemory_barrier_two_thirds s t ht k r, h⟩⟩

/-- **The AFS half, by hand: `{‖x‖ ≤ 1/3 + ε}` is held for every `ε > 0`.**  Window width
`l = 1/2 + 3ε/2`; window starts `P = [1/2 - 3ε/2, 2/3) ∪ [5/6 - 3ε/2, 1)`.
Confidence 95% (hand proof; the witnesses are checked against these exact conditions by
`arc_entropy.py afs`, `test_afs_strategy_every_eps`).  Sub-windows have length `1/3 + ε`, so they
fit the arc lift `[2/3 - ε, 4/3 + ε]` exactly when `u ∈ [2/3 - ε, 1]`.  The moves:
* `a < 2/3`, `d = 0`: `u = max a (2/3 - ε) < 2/3` gives `3u/2 ∈ [1 - 3ε/2, 1)`, in the second piece.
  This is the one place that needs `ε > 0`.
* `a < 2/3`, `d = 1/2`: the same `u` gives fractional part `3u/2 - 1/2 ∈ [1/2 - 3ε/2, 1/2)`.
* `a ≥ 5/6 - 3ε/2`, `d = 0`: `u = max a (1 - ε) ≤ 1` gives `3u/2 - 1 ∈ [1/2 - 3ε/2, 1/2]`.
  It fits because `1 - ε ≤ a + 1/6 + ε/2`, which is why the second piece starts at `5/6 - 3ε/2`.
* `a ≥ 5/6 - 3ε/2`, `d = 1/2`: `u = max a (8/9 - ε) < 1` gives `3u/2 - 1/2 ∈ [5/6 - 3ε/2, 1)`. -/
theorem relaxedStrategy_afs (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    RelaxedStrategy (2 / 3 - ε) (2 / 3 + 2 * ε) (1 / 2 + 3 * ε / 2)
      (Set.Ico (1 / 2 - 3 * ε / 2) (2 / 3) ∪ Set.Ico (5 / 6 - 3 * ε / 2) 1) := by
  sorry

/-- A larger arc traps at least as much. -/
theorem trapsResidueClass_mono {s t s' t' : ℝ} {k r : ℕ} (h : TrapsResidueClass s t k r)
    (hs : s' ≤ s) (ht : s + t ≤ s' + t') : TrapsResidueClass s' t' k r := by
  intro m hm hmr
  obtain ⟨g, hg1, hg2, ξ, hξ, hfl, hn⟩ := h m hm hmr
  refine ⟨g, hg1, hg2, ξ, hξ, hfl, fun n => ?_⟩
  obtain ⟨x, hx, hfx⟩ := hn n
  exact ⟨x, ⟨le_trans hs hx.1, le_trans hx.2 ht⟩, hfx⟩

/-- **The closed AFS arc `{‖x‖ ≤ 1/3}` itself is held, with zero slack.**  Window width `1/2`, two
window starts `P = {0, 1/2}`.  From `[0, 1/2]` keep `[0, 1/3]` (lift `[-1/3, 1/3]`); its image
`[0, 1/2] + d` starts at `d`.  From `[1/2, 1]` keep `[2/3, 1]` (lift `[2/3, 4/3]`); its image
`[1, 3/2] + d` starts at `d` mod 1.  The strategy has no interior, which is why the lattice search
(inward rounding) and the interval-shaped `relaxedStrategy_afs` both missed it.
Found by exact minimax of the component game at `s = t = 2/3` (`arc_entropy.py closed`). -/
theorem relaxedStrategy_afs_closed :
    RelaxedStrategy (2 / 3) (2 / 3) (1 / 2) ({0, 1 / 2} : Set ℝ) := by
  have h0 : Int.fract (0 : ℝ) ∈ ({0, 1 / 2} : Set ℝ) := by simp
  have h12 : Int.fract (1 / 2 : ℝ) ∈ ({0, 1 / 2} : Set ℝ) := by
    rw [Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]; simp
  refine ⟨by norm_num, ⟨0, by simp⟩, ?_, ?_⟩
  · rintro x (rfl | rfl | rfl) <;> norm_num
  · intro a ha d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hd
    rcases ha with rfl | rfl
    · refine ⟨0, le_rfl, by norm_num, ⟨-1, by norm_num, by norm_num⟩, ?_⟩
      rcases hd with rfl | rfl
      · simp
      · simpa using h12
    · refine ⟨2 / 3, by norm_num, by norm_num, ⟨0, by norm_num, by norm_num⟩, ?_⟩
      rcases hd with rfl | rfl
      · rw [show (3 * (2 / 3 : ℝ) / 2 + 0) = (0 : ℝ) + ((1 : ℤ) : ℝ) by norm_num,
          Int.fract_add_intCast]
        exact h0
      · rw [show (3 * (2 / 3 : ℝ) / 2 + 1 / 2) = (1 / 2 : ℝ) + ((1 : ℤ) : ℝ) by norm_num,
          Int.fract_add_intCast]
        exact h12

/-- **Every positive integer part traps the closed AFS arc**: a memoryless construction holds
`{‖x‖ ≤ 1/3}` from every starting floor.  (The orbit-level fact is essentially Akiyama-Frougny-
Sakarovitch 2008; the point here is that it needs no memory, so the `2/3` edge is attained.) -/
theorem trapsResidueClass_afs_closed : TrapsResidueClass (2 / 3) (2 / 3) 0 0 :=
  trapsResidueClass_of_relaxedStrategy (by norm_num) relaxedStrategy_afs_closed

/-- **Theorem: the shortest arc any finite-memory construction holds has length exactly `2/3`,
and the minimum is attained** (at the AFS arc).  First half `finiteMemory_barrier_two_thirds`,
second half `trapsResidueClass_afs_closed`. -/
theorem finiteMemory_min_arc_two_thirds :
    (∀ s t : ℝ, t < 2 / 3 → ∀ k r : ℕ, ¬ TrapsResidueClass s t k r) ∧
      TrapsResidueClass (2 / 3) (2 / 3) 0 0 :=
  ⟨fun s t ht k r => finiteMemory_barrier_two_thirds s t ht k r, trapsResidueClass_afs_closed⟩

/-- **Theorem: the finite-memory edge is exactly `2/3`.**  No residue-class construction holds an
arc shorter than `2/3` (`finiteMemory_barrier_two_thirds`), and every neighbourhood of the AFS arc
`{‖x‖ ≤ 1/3}` is held, already by the closed arc's two-point strategy (`relaxedStrategy_afs_closed`;
the interval strategy `relaxedStrategy_afs` is superseded). -/
theorem finiteMemoryEdgeIsTwoThirds : FiniteMemoryEdgeIsTwoThirds :=
  finiteMemoryEdgeIsTwoThirds_iff.2 fun ε hε =>
    trapsResidueClass_mono trapsResidueClass_afs_closed (by linarith) (by linarith)

/-- **Conjecture: among arcs of length exactly `2/3`, only the AFS arc is held memorylessly.**
Confidence 65%.  Evidence: exact minimax of the component game (adversary picks the parity fresh,
constructor keeps a maximal piece; this dominates every `RelaxedStrategy` of width `≤ 1`) from the
window `[0, 3]` survives depth 18 only at `s = 2/3`; it dies by depth 7 at `s = 0, 1/6, 1/3, 3/5`,
by depth 6 at `s = 1/2`, by 8 at `7/10`, by 10 at `13/20`, and by 11 at `2/3 ± 1/100`
(`arc_entropy.py closed S`).  Counting gives no obstruction here (`two_pow_le_card_admissibleWord`),
so a proof needs the game, not entropy. -/
def AfsArcIsolatedAtTwoThirds : Prop :=
  ∀ s : ℝ, (∃ l P, RelaxedStrategy s (2 / 3) l P) → ∃ k : ℤ, s = 2 / 3 + k

/-- **Conjecture (strong Mahler): no orbit `{ξ(3/2)^n}` fits in any arc shorter than `2/3`.**
So the finite-memory edge (`finiteMemory_min_arc_two_thirds`) would be the true edge for every
`ξ`.  It implies Mahler's conjecture (`strongMahler_no_zNumber`) and `E(3/2) ≤ 1/6`
(`strongMahler_far_le_one_sixth`; Dubickas 2006 has `0.2857`).  The known bounds are `1/3` (FLP)
below and `2/3`, attained by AFS (`relaxedStrategy_afs_closed`), above.
Confidence 60% (it contains Mahler's problem; the heuristic below is the standard one for Z-numbers,
extended to all arcs).  Heuristic: `N` digits fix `⌊ξ⌋ mod 2^N` and an arc of length `< 2/3` admits
`~λ^N` words with `λ < 2` (`admissibleWord_growth_lt_two`), so a "random" integer part survives `N`
steps with probability `~(λ/2)^N`, and the expected number of survivors below any fixed `X` tends to
`0`.  Evidence that integer parts really are random here (`experiments/arc_survival.py rate`):
`2 × (survivor decay rate)` matches the entropy growth `λ`, which `arc_entropy.py` computes
independently.
* `[0, 1/2]`: `1.5012` (`m < 2^15`) against `λ ∈ [1.4986, 1.5079]`.
* `[1/6, 23/30]`: `1.7279` against `[1.7183, 1.7270]`.
* `[7/10, 13/10]`: `1.9326` against `[1.9223, 1.9281]`.

No integer part survives beyond its random-model lifetime.  At the critical length (`[0, 2/3]`,
`λ = 2`) survivors decay polynomially, roughly as a critical branching process.  The AFS position
alone survives with no decay, which is exact alignment beating randomness. -/
def StrongMahlerConjecture : Prop :=
  ∀ s t : ℝ, t < 2 / 3 → ¬ ∃ ξ : ℝ, 0 < ξ ∧
    ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x

/-- The strong conjecture implies Mahler's: there are no Z-numbers. -/
theorem strongMahler_no_zNumber (h : StrongMahlerConjecture) :
    ¬ ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2 := by
  rintro ⟨ξ, hξ, hz⟩
  exact h 0 (1 / 2) (by norm_num) ⟨ξ, hξ, fun n =>
    ⟨Int.fract (ξ * (3 / 2) ^ n), ⟨Int.fract_nonneg _, by linarith [hz n]⟩,
      (Int.fract_fract _).symm⟩⟩

/-- The strong conjecture caps the distance constant: `E(3/2) ≤ 1/6`. -/
theorem strongMahler_far_le_one_sixth (h : StrongMahlerConjecture) (β : ℝ) (hβ : 1 / 6 < β) :
    ¬ ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers β ξ := by
  rintro ⟨ξ, hξ, hf⟩
  exact h β (1 - 2 * β) (by linarith) ⟨ξ, hξ, fun n =>
    ⟨Int.fract (ξ * (3 / 2) ^ n), ⟨(hf n).1, by linarith [(hf n).2]⟩, (Int.fract_fract _).symm⟩⟩

/-- **Conjecture: the relaxed game's value is `7/57`.**  The second conjunct is `relaxed_barrier`;
the first, that every `β < 7/57` is winnable, rests on certificates up to `7/57 - 1e-8`.  Every `β < 7/57` admits a memoryless relaxed
strategy for `[β, 1 - β]`, and no width admits one at `β > 7/57`.
Confidence 75% for the first half; the second half is `relaxed_barrier`.  Evidence: bisection to `1e-8` (wins at
`7/57 - 1e-8`, fails at `7/57`), the same edge at `0..3` bits of memory and over width grids.
Mechanism: `4/19 → 6/19 → 9/19` is a 3-cycle of `x ↦ 3x/2 + d (mod 1)` (parities `0, 0, 1/2`), and the
arc's right edge maps to `1/2 - 3β/2 = 6/19` exactly at `β = 7/57`.  Exact minimax of the
just-in-time adversarial-parity game forces the constructor out at depth 26 for `β = 0.1229`. -/
def RelaxedValueIsSevenFiftySevenths : Prop :=
  (∀ β : ℝ, 0 < β → β < 7 / 57 → ∃ l P, RelaxedStrategy β (1 - 2 * β) l P) ∧
  (∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ l P, ¬ RelaxedStrategy β (1 - 2 * β) l P)

end CollatzMoonshot.Benchmark.ArcTrap
