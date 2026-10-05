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

/-- **Conjecture: the relaxed game's value is `7/57`.**  Every `β < 7/57` admits a memoryless relaxed
strategy for `[β, 1 - β]`, and no width admits one at `β > 7/57`.
Confidence 75% for the first half, 65% for the second.  Evidence: bisection to `1e-8` (wins at
`7/57 - 1e-8`, fails at `7/57`), the same edge at `0..3` bits of memory and over width grids.
Mechanism: `4/19 → 6/19 → 9/19` is a 3-cycle of `x ↦ 3x/2 + d (mod 1)` (parities `0, 0, 1/2`), and the
arc's right edge maps to `1/2 - 3β/2 = 6/19` exactly at `β = 7/57`.  Exact minimax of the
just-in-time adversarial-parity game forces the constructor out at depth 26 for `β = 0.1229`. -/
def RelaxedValueIsSevenFiftySevenths : Prop :=
  (∀ β : ℝ, 0 < β → β < 7 / 57 → ∃ l P, RelaxedStrategy β (1 - 2 * β) l P) ∧
  (∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ l P, ¬ RelaxedStrategy β (1 - 2 * β) l P)

end CollatzMoonshot.Benchmark.ArcTrap
