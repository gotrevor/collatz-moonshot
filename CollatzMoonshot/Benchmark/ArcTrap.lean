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

**New (2026-10-05, certificate in `experiments/arc_cert_beta_k2.json`):** `‖ξ (3/2)^n‖ ≥ 7349/61440
≈ 0.1196` for some `ξ > 0`, beating Dubickas's `5/48 ≈ 0.1042` (novelty ~75%, see the note).  The
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
abstract: there are infinitely many `ξ` with `{ξ (3/2)^n} ∈ (5/48, 43/48)` for every `n ≥ 0`.  Stated
weaker (one positive `ξ`, closed arc).  The best published constant this search found (2026-10-05). -/
def Dubickas2008 : Prop := ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (5 / 48) ξ

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

/-- **New constant.**  Some `ξ > 0` keeps every `(3/2)^n ξ` at distance at least `7349/61440 ≈ 0.1196`
from the integers (Dubickas 2008: `5/48 ≈ 0.1042`; Pollington 1981: `4/65 ≈ 0.0615`).
Confidence 85% (exact rational fixed point; an independent exact construction tracking the integer
part ran 250 steps from 5 starts with random valid choices, never stuck, all `‖·‖ ≥ 0.124`; novelty ~75%:
forward citations of FLP 1995 and Dubickas 2008 checked, Bugeaud's 2012 book unread).
Proof: instantiate `exists_trapped_of_winningStrategy` with `k = 2`, `s = 7349/61440`, `t = 1 - 2s`, `l = 23371/230400` and the intervals of
`experiments/arc_cert_beta_k2.json`; the closure is a finite set of rational inequalities. -/
theorem exists_farFromIntegers_7349 :
    ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (7349 / 61440) ξ := by
  sorry

end CollatzMoonshot.Benchmark.ArcTrap
