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

**New (2026-10-05/06):** `‖ξ (3/2)^n‖ ≥ 7/57` via the memoryless *relaxed* game
(`exists_farFromIntegers_757`, seven-interval certificate `relaxedStrategy_757`), and `7/57` is exactly
that game's value (`relaxedStrategy_exists_iff`: won iff `β ≤ 7/57`).  Earlier step: `307/2500`
(`exists_farFromIntegers_1228`).  First pass, window-in-arc game:
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

/-- **Soundness of the relaxed game, from any integer part `m` and any window start `a ∈ P`.**
The nested intervals `J_n = (m_n + [u_n, u_n + 2l/3]) / (3/2)^n` of `exists_trapped_of_relaxedStrategy`,
with `ξ = sup` of their left ends; `ξ ∈ m + [a, a + l]`. -/
theorem exists_trapped_of_relaxedStrategy_from {s t l : ℝ} {P : Set ℝ}
    (h : RelaxedStrategy s t l P) (m : ℤ) (a : ℝ) (ha : a ∈ P) :
    ∃ ξ : ℝ, m + a ≤ ξ ∧ ξ ≤ m + a + l ∧
      ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x := by
  obtain ⟨hl, -, -, hstep⟩ := h
  have hU : ∀ p : {a // a ∈ P} × ℤ, ∃ u : ℝ, p.1.1 ≤ u ∧ u + 2 * l / 3 ≤ p.1.1 + l ∧
      (∃ k : ℤ, (k : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ k + s + t) ∧
      Int.fract (3 * u / 2 + ((p.2 % 2 : ℤ) : ℝ) / 2) ∈ P := by
    rintro ⟨⟨a, ha⟩, M⟩
    have hd : ((M % 2 : ℤ) : ℝ) / 2 ∈ ({0, 1 / 2} : Set ℝ) := by
      rcases Int.emod_two_eq_zero_or_one M with h | h <;> simp [h]
    exact hstep a ha _ hd
  choose U hU1 hU2 hU3 hU4 using hU
  let step : {a // a ∈ P} × ℤ → {a // a ∈ P} × ℤ := fun p =>
    (⟨Int.fract (3 * U p / 2 + ((p.2 % 2 : ℤ) : ℝ) / 2), hU4 p⟩,
      3 * (p.2 / 2) + p.2 % 2 + ⌊3 * U p / 2 + ((p.2 % 2 : ℤ) : ℝ) / 2⌋)
  let S : ℕ → {a // a ∈ P} × ℤ := fun n => step^[n] (⟨a, ha⟩, m)
  have hS : ∀ n, S (n + 1) = step (S n) := fun n => Function.iterate_succ_apply' _ _ _
  -- key identity
  have key : ∀ n, (3 / 2 : ℝ) * ((S n).2 + U (S n)) = (S (n + 1)).2 + (S (n + 1)).1.1 := by
    intro n
    rw [hS n]
    set p := S n
    simp only [step]
    have h1 : p.2 = p.2 % 2 + 2 * (p.2 / 2) := by omega
    have h2 := Int.floor_add_fract (3 * U p / 2 + ((p.2 % 2 : ℤ) : ℝ) / 2)
    have h3 : (p.2 : ℝ) = ((p.2 % 2 : ℤ) : ℝ) + 2 * ((p.2 / 2 : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast
    rw [h3]
    linarith
  set Lo : ℕ → ℝ := fun n => ((S n).2 + U (S n)) / (3 / 2) ^ n
  set Hi : ℕ → ℝ := fun n => ((S n).2 + U (S n) + 2 * l / 3) / (3 / 2) ^ n
  have hpos : ∀ n : ℕ, (0 : ℝ) < (3 / 2) ^ n := fun n => by positivity
  have hLo : ∀ n, Lo n ≤ Lo (n + 1) := by
    intro n
    simp only [Lo]
    rw [div_le_div_iff₀ (hpos n) (hpos _), pow_succ]
    have := key n
    have := hU1 (S (n + 1))
    have := hpos n
    nlinarith
  have hHi : ∀ n, Hi (n + 1) ≤ Hi n := by
    intro n
    simp only [Hi]
    rw [div_le_div_iff₀ (hpos _) (hpos n), pow_succ]
    have := key n
    have := hU2 (S (n + 1))
    have := hpos n
    nlinarith
  have hLH : ∀ n, Lo n ≤ Hi n := by
    intro n
    simp only [Lo, Hi]
    exact div_le_div_of_nonneg_right (by linarith) (hpos n).le
  have hLm : Monotone Lo := monotone_nat_of_le_succ hLo
  have hHa : Antitone Hi := antitone_nat_of_succ_le hHi
  have hLH' : ∀ i j, Lo i ≤ Hi j := fun i j =>
    (hLm (le_max_left i j)).trans ((hLH _).trans (hHa (le_max_right i j)))
  have hbdd : BddAbove (Set.range Lo) := ⟨Hi 0, by rintro _ ⟨i, rfl⟩; exact hLH' i 0⟩
  refine ⟨⨆ n, Lo n, ?_, ?_, ?_⟩
  · refine le_trans ?_ (le_ciSup hbdd 0)
    simp only [Lo, S, Function.iterate_zero, id, pow_zero, div_one]
    linarith [hU1 (⟨a, ha⟩, m)]
  · refine (ciSup_le fun i => hLH' i 0).trans ?_
    simp only [Hi, S, Function.iterate_zero, id, pow_zero, div_one]
    linarith [hU2 (⟨a, ha⟩, m)]
  · intro n
    have h1 : Lo n ≤ ⨆ n, Lo n := le_ciSup hbdd n
    have h2 : (⨆ n, Lo n) ≤ Hi n := ciSup_le fun i => hLH' i n
    simp only [Lo, Hi] at h1 h2
    rw [div_le_iff₀ (hpos n)] at h1
    rw [le_div_iff₀ (hpos n)] at h2
    obtain ⟨k, hk1, hk2⟩ := hU3 (S n)
    refine ⟨(⨆ n, Lo n) * (3 / 2) ^ n - ((S n).2 + k), ⟨by linarith, by linarith⟩, ?_⟩
    rw [show ((S n).2 : ℝ) + (k : ℝ) = ((((S n).2 + k : ℤ)) : ℝ) by push_cast; ring,
      Int.fract_sub_intCast]

/-- **Soundness of the relaxed game.**
PROVED 2026-10-06 (via `exists_trapped_of_relaxedStrategy_from`).  Proof: pick `m₀ ≥ 1` and `a₀ ∈ P`; at step `n` the window is `m_n + [a_n, a_n + l]`,
`d = (m_n mod 2)/2`, the strategy gives `u_n`, and `m_{n+1} = ⌊3m_n/2⌋ + ⌊c⌋`, `a_{n+1} = fract c` with
`c = 3u_n/2 + d`, since `3(m_n + u_n)/2 = ⌊3m_n/2⌋ + c`.  The closed intervals
`J_n = (m_n + [u_n, u_n + 2l/3]) / (3/2)^n` are nested and nonempty; any `ξ ∈ ⋂ J_n` has
`ξ (3/2)^n ∈ m_n + [u_n, u_n + 2l/3]`, inside a lift of the arc, and `ξ ≥ m₀ / 1 > 0`. -/
theorem exists_trapped_of_relaxedStrategy {s t l : ℝ} {P : Set ℝ} (h : RelaxedStrategy s t l P) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x := by
  obtain ⟨a, ha⟩ := h.2.1
  have ha0 := (h.2.2.1 ha).1
  obtain ⟨ξ, h1, -, h3⟩ := exists_trapped_of_relaxedStrategy_from h 1 a ha
  exact ⟨ξ, by push_cast at h1; linarith, h3⟩


/-- One cell of the `1228` certificate: from `a ∈ [lo, hi]`, the clamp `u = max a c` works, landing
`fract (3u/2 + d)` in `[A, B]` (with `3u/2 + d - n ∈ [A, B]`). -/
theorem cell1228 {s t l lo hi c A B d a : ℝ} (n : ℤ) (ha : a ∈ Set.Icc lo hi) (h0 : 0 ≤ l)
    (h1 : c ≤ lo + l / 3) (h2 : s ≤ c) (h3 : hi + 2 * l / 3 ≤ s + t) (h4 : c + 2 * l / 3 ≤ s + t)
    (h5 : A ≤ 3 * c / 2 + d - n) (h6 : 3 * hi / 2 + d - n ≤ B) (h7 : 3 * c / 2 + d - n ≤ B)
    (h8 : 0 ≤ A) (h9 : B < 1) :
    ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
      (∃ k : ℤ, (k : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ k + s + t) ∧
      Int.fract (3 * u / 2 + d) ∈ Set.Icc A B := by
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨max a c, le_max_left _ _, ?_, ⟨0, ?_, ?_⟩, ?_⟩
  · rcases le_total a c with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · push_cast; linarith [le_max_right a c]
  · push_cast
    rcases le_total a c with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · have hA : A ≤ 3 * max a c / 2 + d - n := by linarith [le_max_right a c]
    have hB : 3 * max a c / 2 + d - n ≤ B := by
      rcases le_total a c with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    rw [show Int.fract (3 * max a c / 2 + d) = 3 * max a c / 2 + d - n from
      (Int.fract_eq_iff).2 ⟨by linarith, by linarith, n, by ring⟩]
    exact ⟨hA, hB⟩

/-- The eleven window-start intervals of `experiments/arc_cert_beta_1228_vw_k0.json`. -/
def P1228 : Set ℝ :=
  Set.Icc (1468449 / 16777216 : ℝ) (2060359 / 16777216 : ℝ) ∪
    Set.Icc (2089827 / 16777216 : ℝ) (269809 / 2097152 : ℝ) ∪
    Set.Icc (404309 / 2097152 : ℝ) (809427 / 4194304 : ℝ) ∪
    Set.Icc (2941753 / 8388608 : ℝ) (2943371 / 8388608 : ℝ) ∪
    Set.Icc (3481371 / 8388608 : ℝ) (3515693 / 8388608 : ℝ) ∪
    Set.Icc (7060855 / 16777216 : ℝ) (1913191 / 4194304 : ℝ) ∪
    Set.Icc (7682233 / 16777216 : ℝ) (7750877 / 16777216 : ℝ) ∪
    Set.Icc (8826877 / 16777216 : ℝ) (8830113 / 16777216 : ℝ) ∪
    Set.Icc (11475911 / 16777216 : ℝ) (11479147 / 16777216 : ℝ) ∪
    Set.Icc (12555147 / 16777216 : ℝ) (788987 / 1048576 : ℝ) ∪
    Set.Icc (3163315 / 4194304 : ℝ) (6622585 / 8388608 : ℝ)

theorem relaxedStrategy_1228 :
    RelaxedStrategy (307 / 2500) (943 / 1250) (123 / 1000) P1228 := by
  have S0 : Set.Icc (1468449 / 16777216 : ℝ) (2060359 / 16777216 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S1 : Set.Icc (2089827 / 16777216 : ℝ) (269809 / 2097152 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S2 : Set.Icc (404309 / 2097152 : ℝ) (809427 / 4194304 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S3 : Set.Icc (2941753 / 8388608 : ℝ) (2943371 / 8388608 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S4 : Set.Icc (3481371 / 8388608 : ℝ) (3515693 / 8388608 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S5 : Set.Icc (7060855 / 16777216 : ℝ) (1913191 / 4194304 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S6 : Set.Icc (7682233 / 16777216 : ℝ) (7750877 / 16777216 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S7 : Set.Icc (8826877 / 16777216 : ℝ) (8830113 / 16777216 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S8 : Set.Icc (11475911 / 16777216 : ℝ) (11479147 / 16777216 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S9 : Set.Icc (12555147 / 16777216 : ℝ) (788987 / 1048576 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  have S10 : Set.Icc (3163315 / 4194304 : ℝ) (6622585 / 8388608 : ℝ) ⊆ P1228 := by
    intro x hx; simp only [P1228, Set.mem_union]; tauto
  refine ⟨by norm_num, ⟨_, S0 ⟨le_refl _, by norm_num⟩⟩, ?_, ?_⟩
  · intro x hx
    simp only [P1228, Set.mem_union, Set.mem_Icc] at hx
    constructor <;> rcases hx with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
      linarith [h.1, h.2]
  intro a ha d hd
  simp only [P1228, Set.mem_union] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases ha with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
    rcases hd with rfl | rfl
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (404309 / 3145728 : ℝ)) (A := (404309 / 2097152 : ℝ)) (B := (809427 / 4194304 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (307 / 2500 : ℝ)) (A := (11475911 / 16777216 : ℝ)) (B := (11479147 / 16777216 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S8 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (404309 / 3145728 : ℝ)) (A := (404309 / 2097152 : ℝ)) (B := (809427 / 4194304 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (4166539 / 25165824 : ℝ)) (A := (12555147 / 16777216 : ℝ)) (B := (788987 / 1048576 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S9 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (2941753 / 12582912 : ℝ)) (A := (2941753 / 8388608 : ℝ)) (B := (2943371 / 8388608 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S3 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (1066163 / 6291456 : ℝ)) (A := (3163315 / 4194304 : ℝ)) (B := (6622585 / 8388608 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S10 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (8826877 / 25165824 : ℝ)) (A := (8826877 / 16777216 : ℝ)) (B := (8830113 / 16777216 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S7 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (9857057 / 25165824 : ℝ)) (A := (1468449 / 16777216 : ℝ)) (B := (2060359 / 16777216 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S0 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (11475911 / 25165824 : ℝ)) (A := (11475911 / 16777216 : ℝ)) (B := (11479147 / 16777216 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S8 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (10478435 / 25165824 : ℝ)) (A := (2089827 / 16777216 : ℝ)) (B := (269809 / 2097152 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S1 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (11475911 / 25165824 : ℝ)) (A := (11475911 / 16777216 : ℝ)) (B := (11479147 / 16777216 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S8 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (484295 / 1048576 : ℝ)) (A := (404309 / 2097152 : ℝ)) (B := (809427 / 4194304 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (4185049 / 8388608 : ℝ)) (A := (12555147 / 16777216 : ℝ)) (B := (788987 / 1048576 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S9 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (484295 / 1048576 : ℝ)) (A := (404309 / 2097152 : ℝ)) (B := (809427 / 4194304 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (3163315 / 6291456 : ℝ)) (A := (3163315 / 4194304 : ℝ)) (B := (6622585 / 8388608 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S10 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (7136057 / 12582912 : ℝ)) (A := (2941753 / 8388608 : ℝ)) (B := (2943371 / 8388608 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S3 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (18245665 / 25165824 : ℝ)) (A := (1468449 / 16777216 : ℝ)) (B := (2060359 / 16777216 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S0 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (5738495 / 8388608 : ℝ)) (A := (8826877 / 16777216 : ℝ)) (B := (8830113 / 16777216 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S7 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (18867043 / 25165824 : ℝ)) (A := (2089827 / 16777216 : ℝ)) (B := (269809 / 2097152 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S1 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (19864519 / 25165824 : ℝ)) (A := (11475911 / 16777216 : ℝ)) (B := (11479147 / 16777216 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S8 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 0) (c := (2501461 / 3145728 : ℝ)) (A := (404309 / 2097152 : ℝ)) (B := (809427 / 4194304 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 307 / 2500) (t := 943 / 1250) (l := 123 / 1000) (d := 1 / 2) (c := (19864519 / 25165824 : ℝ)) (A := (11475911 / 16777216 : ℝ)) (B := (11479147 / 16777216 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S8 h4⟩

/-- **New constant, sharpened.**  Some `ξ > 0` keeps every `(3/2)^n ξ` at distance at least
`307/2500 = 0.1228` from the integers (Dubickas 2008: `5/48 ≈ 0.1042`).
PROVED 2026-10-06 (`relaxedStrategy_1228`: 22 clamp cells `u = max a c`, checked by `norm_num`; orbit check in
`test_relaxed_certificate_orbits_stay_far`).  Proof: `exists_trapped_of_relaxedStrategy` with
`s = 307/2500`, `t = 1 - 2s`, `l = 123/1000` and the eleven intervals of
`experiments/arc_cert_beta_1228_vw_k0.json` (denominator `2^24`); for `x ∈ [s, 1 - s]`,
`Int.fract x = x`. -/
theorem exists_farFromIntegers_1228 :
    ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (307 / 2500) ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_trapped_of_relaxedStrategy relaxedStrategy_1228
  refine ⟨ξ, hξ, fun n => ?_⟩
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h n
  have : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
  rw [hx, this]
  constructor <;> linarith

/-! ### The quantity itself -/

/-- `E α`: how far an orbit `ξ, ξα, ξα², …` (`ξ > 0`) can stay from the integers, i.e.
`sup_{ξ > 0} inf_{n ≥ 0} ‖ξ αⁿ‖`.  Using `lim inf` instead of `inf` gives the same value: start the
orbit at `ξ α^N`.  Whether the supremum is attained for `α = 3/2` is not known to us. -/
noncomputable def E (α : ℝ) : ℝ :=
  sSup {β : ℝ | ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, β ≤ |ξ * α ^ n - round (ξ * α ^ n)|}

/-- Calibration: `E 2 = 1/3`.  PROVED.  Proof: `ξ = 1/3` gives `2ⁿ/3 ≡ ±1/3`.  Conversely, if
`x` and `2x` both lie in `[β, 1 - β]` mod 1 with `β > 1/3`, then `x ∈ [1/6, 1/3] ∪ [2/3, 5/6]`, which
misses `[β, 1 - β]`. -/
theorem E_bdd (α : ℝ) :
    BddAbove {β : ℝ | ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, β ≤ |ξ * α ^ n - round (ξ * α ^ n)|} :=
  ⟨1 / 2, fun _ ⟨_, _, h⟩ => (h 0).trans (abs_sub_round _)⟩

theorem E_le_half (α : ℝ) : E α ≤ 1 / 2 :=
  csSup_le ⟨0, 1, one_pos, fun _ => abs_nonneg _⟩ fun _ ⟨_, _, h⟩ => (h 0).trans (abs_sub_round _)

theorem E_ge_of_far {α β ξ : ℝ} (hξ : 0 < ξ)
    (h : ∀ n : ℕ, β ≤ Int.fract (ξ * α ^ n) ∧ Int.fract (ξ * α ^ n) ≤ 1 - β) : β ≤ E α :=
  le_csSup (E_bdd α) ⟨ξ, hξ, fun n => by
    rw [abs_sub_round_eq_min]; exact le_min (h n).1 (by linarith [(h n).2])⟩

theorem E_two : E 2 = 1 / 3 := by
  apply le_antisymm
  · refine csSup_le ⟨0, 1, one_pos, fun _ => abs_nonneg _⟩ fun β ⟨ξ, _, h⟩ => ?_
    have h0 := h 0
    have h1 := h 1
    simp only [pow_zero, mul_one, pow_one] at h0 h1
    set r := round ξ
    have hr := abs_sub_round ξ
    rcases le_total 0 (ξ - r) with he | he
    · have := h1.trans (round_le (ξ * 2) (2 * r + 1))
      push_cast at this
      rw [abs_le] at hr
      rw [abs_of_nonneg he] at h0
      rw [show ξ * 2 - (2 * (r : ℝ) + 1) = -(1 - 2 * (ξ - r)) by ring, abs_neg,
        abs_of_nonneg (by linarith)] at this
      linarith
    · have := h1.trans (round_le (ξ * 2) (2 * r - 1))
      push_cast at this
      rw [abs_le] at hr
      rw [abs_of_nonpos he] at h0
      rw [show ξ * 2 - (2 * (r : ℝ) - 1) = 1 + 2 * (ξ - r) by ring,
        abs_of_nonneg (by linarith)] at this
      linarith
  · refine E_ge_of_far (ξ := 1 / 3) (by norm_num) fun n => ?_
    have hmod : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
      have : 2 ^ n % 3 ≠ 0 := by
        intro h0
        have : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h0
        exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) this) (by norm_num)
      omega
    have hk := Nat.div_add_mod (2 ^ n) 3
    rcases hmod with h1 | h1 <;>
    · have e : (1 / 3 : ℝ) * 2 ^ n = ((2 ^ n / 3 : ℕ) : ℝ) + ((2 ^ n % 3 : ℕ) : ℝ) / 3 := by
        have := congrArg (fun m : ℕ => (m : ℝ)) hk; push_cast at this ⊢; linarith
      rw [e, add_comm, Int.fract_add_natCast, h1, Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
      norm_num

/-- Calibration: `E 3 = 1/2`, via `ξ = 1/2` (every `3ⁿ/2` is a half-integer).  PROVED. -/
theorem E_three : E 3 = 1 / 2 := by
  apply le_antisymm (E_le_half 3)
  refine E_ge_of_far (ξ := 1 / 2) (by norm_num) fun n => ?_
  obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  have : (1 / 2 : ℝ) * 3 ^ n = (k : ℝ) + 1 / 2 := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hk; push_cast at this; rw [this]; ring
  rw [this, add_comm, Int.fract_add_natCast, Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
  norm_num

/-- Lower bound from the relaxed-game certificate.  PROVED.  Proof: `exists_farFromIntegers_1228`,
and `FarFromIntegers β ξ` gives `β ≤ |y - round y|` for each `y = ξ (3/2)^n`; `E (3/2) ≤ 1/2` bounds
the set. -/
theorem E_three_halves_ge : 307 / 2500 ≤ E (3 / 2) := by
  obtain ⟨ξ, hξ, h⟩ := exists_farFromIntegers_1228
  exact E_ge_of_far hξ h

/-- Upper bound from Dubickas 2006 (Cor. 1).  PROVED from the literature input. -/
theorem E_three_halves_le (h : Literature.Dubickas2006) : E (3 / 2) ≤ 2857 / 10000 := by
  refine csSup_le ⟨0, 1, one_pos, fun _ => abs_nonneg _⟩ fun β ⟨ξ, hξ, hn⟩ => ?_
  by_contra hβ
  refine h ⟨ξ, hξ, fun n => ?_⟩
  have := hn n
  rw [abs_sub_round_eq_min] at this
  constructor <;> linarith [min_le_left (Int.fract (ξ * (3 / 2) ^ n)) (1 - Int.fract (ξ * (3 / 2) ^ n)),
    min_le_right (Int.fract (ξ * (3 / 2) ^ n)) (1 - Int.fract (ξ * (3 / 2) ^ n))]


/-! ### Finite memory: a counting barrier (Flatto's entropy method on an arbitrary arc) -/

/-- `g` is the integer part of some `ξ > 0` whose whole orbit `{ξ (3/2)^n}` lies in the arc
`[s, s + t]` (mod 1). -/
def TrappedFloor (s t : ℝ) (g : ℕ) : Prop :=
  ∃ ξ : ℝ, 0 < ξ ∧ ⌊ξ⌋ = (g : ℤ) ∧
    ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x

/-- What a finite-memory construction delivers.  A strategy that reads only `m mod 2^k` wins from
every start `m ≡ r`, so every such `m` has a trapped orbit within `3` of it.
It holds vacuously when `r ≥ 2^k`, so every barrier below assumes `r < 2^k`. -/
def TrapsResidueClass (s t : ℝ) (k r : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m % 2 ^ k = r → ∃ g : ℕ, m ≤ g ∧ g < m + 3 ∧ TrappedFloor s t g

/-- Why the barriers need `r < 2 ^ k`: with no `m` in the class, `TrapsResidueClass` holds for
every arc, even an empty one. -/
theorem trapsResidueClass_vacuous (s t : ℝ) : TrapsResidueClass s t 0 1 := by
  intro m _ h
  exfalso
  simp only [pow_zero] at h
  omega

/-- **A memoryless relaxed strategy traps every unit interval.**  The strategy never reads the
integer part, so it runs from the window `[m + a, m + a + l]` for every `m ≥ 1`.  The sub-window
`[u, u + 2l/3]` fits in an arc lift, so `l ≤ 3t/2 ≤ 3/2` and `⌊ξ⌋ < m + 3`.
PROVED 2026-10-06 (the construction in `exists_trapped_of_relaxedStrategy`, started at `m`; it is
also what `vw_orbit` in `experiments/arc_trap_k.py` plays from any `m0`).  The `k`-memory games of
`arc_trap_k.py` give `TrapsResidueClass s t k r` the same way. -/
theorem trapsResidueClass_of_relaxedStrategy {s t l : ℝ} {P : Set ℝ} (ht : t ≤ 1)
    (h : RelaxedStrategy s t l P) : TrapsResidueClass s t 0 0 := by
  intro m hm _
  obtain ⟨a, ha⟩ := h.2.1
  have ha' := h.2.2.1 ha
  obtain ⟨u, -, -, ⟨k, hk1, hk2⟩, -⟩ := h.2.2.2 a ha 0 (by simp)
  obtain ⟨ξ, h1, h2, h3⟩ := exists_trapped_of_relaxedStrategy_from h m a ha
  push_cast at h1 h2
  have hl : l ≤ 3 / 2 := by linarith
  have hf1 : (m : ℤ) ≤ ⌊ξ⌋ := Int.le_floor.2 (by push_cast; linarith [ha'.1])
  have hf2 : ⌊ξ⌋ < (m : ℤ) + 3 := Int.floor_lt.2 (by push_cast; linarith [ha'.2])
  refine ⟨⌊ξ⌋.toNat, by omega, by omega, ξ, by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [ha'.1], by omega, h3⟩

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


/-! ### Below `2/3`: digit words grow slower than `2^N` (proved) -/

/-- A digit path of length `N` from `p` to `q` inside the arc: fractional parts `f_0 = p, …,
f_N = q` in the arc with `f_{i+1} = 3 f_i / 2 - a_i / 2`. -/
def ArcPath (s t : ℝ) (N : ℕ) (p q : ℝ) (a : Fin N → ℤ) : Prop :=
  ∃ f : Fin (N + 1) → ℝ, (∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x) ∧
    (∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2) ∧
    f 0 = p ∧ f (Fin.last N) = q

/-! #### Helpers for the forward and backward path counts -/

theorem inArc_iff {s t y : ℝ} (ht : t < 1) :
    (∃ x ∈ Set.Icc s (s + t), y = Int.fract x) ↔ (0 ≤ y ∧ y < 1 ∧ Int.fract (y - s) ≤ t) := by
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨Int.fract_nonneg _, Int.fract_lt_one _, ?_⟩
    rw [show Int.fract x - s = (x - s) + ((-⌊x⌋ : ℤ) : ℝ) by rw [Int.fract]; push_cast; ring,
      Int.fract_add_intCast, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨s + Int.fract (y - s), ⟨by linarith [Int.fract_nonneg (y - s)], by linarith⟩, ?_⟩
    rw [show s + Int.fract (y - s) = y + ((-⌊y - s⌋ : ℤ) : ℝ) by rw [Int.fract]; push_cast; ring,
      Int.fract_add_intCast, Int.fract_eq_self.2 ⟨h0, h1⟩]

theorem four_points (w : ℝ) : ∃ j : ℕ, j < 4 ∧ 3 / 4 ≤ Int.fract (w + j / 4) := by
  set i := ⌊4 * Int.fract w⌋
  have h0 := Int.fract_nonneg w
  have h1 := Int.fract_lt_one w
  have hi0 : 0 ≤ i := Int.floor_nonneg.2 (by linarith)
  have hi3 : i ≤ 3 := Int.le_of_lt_add_one (Int.floor_lt.2 (by push_cast; linarith))
  have hl := Int.floor_le (4 * Int.fract w)
  have hu := Int.lt_floor_add_one (4 * Int.fract w)
  refine ⟨(3 - i).toNat, by omega, ?_⟩
  have hc : (((3 - i).toNat : ℕ) : ℝ) = 3 - (i : ℝ) := by
    rw [show (((3 - i).toNat : ℕ) : ℝ) = (((3 - i).toNat : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  rw [hc, ← Int.floor_add_fract w, show (⌊w⌋ : ℝ) + Int.fract w + (3 - i) / 4 =
    (Int.fract w + (3 - i) / 4) + (⌊w⌋ : ℤ) by ring, Int.fract_add_intCast,
    Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  linarith

/-- Four points spaced `1/4` apart cannot all lie in an arc shorter than `3/4`. -/
theorem quarters_false {b s t : ℝ} (ht : t < 3 / 4)
    (h : ∀ j : ℕ, j < 4 → ∃ n : ℤ, Int.fract (b + j / 4 + n - s) ≤ t) : False := by
  obtain ⟨j, hj, hj'⟩ := four_points (b - s)
  obtain ⟨n, hn⟩ := h j hj
  rw [show b + j / 4 + n - s = (b - s + j / 4) + n by ring, Int.fract_add_intCast] at hn
  linarith

/-- The words of forward paths of length `N` from `p`. -/
def fwdSet (s t : ℝ) (N : ℕ) (p : ℝ) : Set (Fin N → ℤ) := {a | ∃ q, ArcPath s t N p q a}

theorem fwdSet_subset_box (s t : ℝ) (N : ℕ) (p : ℝ) :
    fwdSet s t N p ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℤ) 2) := by
  rintro a ⟨q, f, hf, hstep, -, -⟩ i -
  obtain ⟨x, -, hx⟩ := hf i.castSucc
  obtain ⟨y, -, hy⟩ := hf i.succ
  have h1 := hstep i
  have := Int.fract_nonneg x; have := Int.fract_lt_one x
  have := Int.fract_nonneg y; have := Int.fract_lt_one y
  have hlo : (-2 : ℝ) < a i := by linarith
  have hhi : (a i : ℝ) < 3 := by linarith
  constructor
  · have : (-2 : ℤ) < a i := by exact_mod_cast hlo
    omega
  · have : a i < (3 : ℤ) := by exact_mod_cast hhi
    omega

theorem fwdSet_finite (s t : ℝ) (N : ℕ) (p : ℝ) : (fwdSet s t N p).Finite :=
  (Set.Finite.pi (fun _ => Set.finite_Icc (-1 : ℤ) 2)).subset (fwdSet_subset_box s t N p)

theorem inArc_of_fwdSet_nonempty {s t : ℝ} {N : ℕ} {p : ℝ} (h : (fwdSet s t N p).Nonempty) :
    ∃ x ∈ Set.Icc s (s + t), p = Int.fract x := by
  obtain ⟨a, q, f, hf, -, h0, -⟩ := h
  rw [← h0]; exact hf 0

theorem fwdSet_zero_ncard (s t p : ℝ) : (fwdSet s t 0 p).ncard ≤ 1 := by
  rw [Set.ncard_le_one_iff_subsingleton]  -- maybe
  intro a _ b _
  exact Subsingleton.elim a b

/-- The child of `p` along digit `c`. -/
noncomputable def child (p : ℝ) (c : ℤ) : ℝ := 3 / 2 * p - c / 2

theorem fwdSet_succ_subset (s t : ℝ) (N : ℕ) (p : ℝ) :
    fwdSet s t (N + 1) p ⊆ Fin.cons (⌊3 * p⌋ - 1) '' fwdSet s t N (child p (⌊3 * p⌋ - 1)) ∪
      Fin.cons ⌊3 * p⌋ '' fwdSet s t N (child p ⌊3 * p⌋) := by
  rintro a ⟨q, f, hf, hstep, h0, hl⟩
  have htail : Fin.tail a ∈ fwdSet s t N (child p (a 0)) := by
    refine ⟨q, fun i => f i.succ, fun i => hf _, fun i => ?_, ?_, ?_⟩
    · have := hstep i.succ
      show f i.succ.succ = 3 / 2 * f i.castSucc.succ - (a i.succ : ℝ) / 2
      rw [Fin.succ_castSucc]; exact this
    · have := hstep 0
      simp only [Fin.succ_zero_eq_one', Fin.castSucc_zero] at this
      rw [child, ← h0]; simpa using this
    · rw [← hl]; rfl
  have ha : a = Fin.cons (a 0) (Fin.tail a) := (Fin.cons_self_tail a).symm
  obtain ⟨x, -, hx⟩ := hf 1
  have := Int.fract_nonneg x; have := Int.fract_lt_one x
  have h1 := hstep 0
  simp only [Fin.castSucc_zero] at h1
  rw [h0] at h1
  have e1 : f (Fin.succ 0) = f 1 := rfl
  rw [e1, hx] at h1
  have hlo : (a 0 : ℝ) ≤ 3 * p := by linarith
  have hhi : 3 * p - 2 < (a 0 : ℝ) := by linarith
  have c1 : a 0 ≤ ⌊3 * p⌋ := Int.le_floor.2 hlo
  have c2 : ⌊3 * p⌋ - 1 ≤ a 0 := by
    have := Int.floor_le (3 * p)
    have : ((⌊3 * p⌋ : ℤ) : ℝ) - 2 < a 0 := by linarith
    have : ⌊3 * p⌋ - 2 < a 0 := by exact_mod_cast this
    omega
  rcases (show a 0 = ⌊3 * p⌋ - 1 ∨ a 0 = ⌊3 * p⌋ by omega) with h | h
  · left; exact ⟨Fin.tail a, h ▸ htail, by rw [ha, h]; rfl⟩
  · right; exact ⟨Fin.tail a, h ▸ htail, by rw [ha, h]; rfl⟩

theorem fwdSet_succ_ncard (s t : ℝ) (N : ℕ) (p : ℝ) :
    (fwdSet s t (N + 1) p).ncard ≤ (fwdSet s t N (child p (⌊3 * p⌋ - 1))).ncard +
      (fwdSet s t N (child p ⌊3 * p⌋)).ncard := by
  refine (Set.ncard_le_ncard (fwdSet_succ_subset s t N p)
    (((fwdSet_finite _ _ _ _).image _).union ((fwdSet_finite _ _ _ _).image _))).trans ?_
  refine (Set.ncard_union_le _ _).trans ?_
  rw [Set.ncard_image_of_injective _ (Fin.cons_right_injective _),
    Set.ncard_image_of_injective _ (Fin.cons_right_injective _)]

theorem fract_le_of_fwdSet_nonempty {s t : ℝ} (ht : t < 1) {N : ℕ} {g : ℝ}
    (h : (fwdSet s t N g).Nonempty) : Int.fract (g - s) ≤ t :=
  ((inArc_iff ht).1 (inArc_of_fwdSet_nonempty h)).2.2

theorem fwd_fib (s t : ℝ) (ht : t < 3 / 4) : ∀ n : ℕ, ∀ p : ℝ,
    (fwdSet s t n p).ncard ≤ Nat.fib (n + 2) ∧ (fwdSet s t (n + 1) p).ncard ≤ Nat.fib (n + 3) := by
  intro n
  induction n with
  | zero =>
    intro p
    refine ⟨by simpa using fwdSet_zero_ncard s t p, ?_⟩
    have := fwdSet_succ_ncard s t 0 p
    have := fwdSet_zero_ncard s t (child p (⌊3 * p⌋ - 1))
    have := fwdSet_zero_ncard s t (child p ⌊3 * p⌋)
    have h3 : Nat.fib 3 = 2 := rfl
    simp only [zero_add, h3]
    omega
  | succ n ih =>
    intro p
    refine ⟨(ih p).2, ?_⟩
    have hp := fwdSet_succ_ncard s t (n + 1) p
    set y1 := child p (⌊3 * p⌋ - 1) with hy1
    set y2 := child p ⌊3 * p⌋ with hy2
    have h1 := fwdSet_succ_ncard s t n y1
    have h2 := fwdSet_succ_ncard s t n y2
    set g11 := child y1 (⌊3 * y1⌋ - 1) with hg11
    set g12 := child y1 ⌊3 * y1⌋ with hg12
    set g21 := child y2 (⌊3 * y2⌋ - 1) with hg21
    set g22 := child y2 ⌊3 * y2⌋ with hg22
    have b11 := (ih g11).1; have b12 := (ih g12).1
    have b21 := (ih g21).1; have b22 := (ih g22).1
    have c1 := (ih y1).2; have c2 := (ih y2).2
    have hfib : Nat.fib (n + 1 + 3) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
      rw [show n + 1 + 3 = (n + 2) + 2 by ring, Nat.fib_add_two]
    rw [hfib]
    have key : ¬ ((fwdSet s t n g11).Nonempty ∧ (fwdSet s t n g12).Nonempty ∧
        (fwdSet s t n g21).Nonempty ∧ (fwdSet s t n g22).Nonempty) := by
      rintro ⟨n11, n12, n21, n22⟩
      have ht1 : t < 1 := by linarith
      have f11 := fract_le_of_fwdSet_nonempty ht1 n11
      have f12 := fract_le_of_fwdSet_nonempty ht1 n12
      have f21 := fract_le_of_fwdSet_nonempty ht1 n21
      have f22 := fract_le_of_fwdSet_nonempty ht1 n22
      have hy : y2 = y1 - 1 / 2 := by simp only [hy1, hy2, child]; push_cast; ring
      obtain ⟨q, hq⟩ := Int.even_or_odd' (⌊3 * y1⌋ - ⌊3 * y2⌋)
      have fl : ∀ g : ℝ, Int.fract (g - s) ≤ t → ∀ (j : ℕ) (n : ℤ),
          g12 + (j : ℝ) / 4 + n - s = g - s → Int.fract (g12 + (j : ℝ) / 4 + n - s) ≤ t :=
        fun g hg j n h => h ▸ hg
      have e12 : g12 = 3 / 2 * y1 - (⌊3 * y1⌋ : ℝ) / 2 := rfl
      have e11 : g11 = 3 / 2 * y1 - ((⌊3 * y1⌋ : ℝ) - 1) / 2 := by
        simp only [hg11, child]; push_cast; ring
      have e21 : g21 = 3 / 2 * y2 - ((⌊3 * y2⌋ : ℝ) - 1) / 2 := by
        simp only [hg21, child]; push_cast; ring
      have e22 : g22 = 3 / 2 * y2 - (⌊3 * y2⌋ : ℝ) / 2 := rfl
      refine quarters_false (b := g12) (s := s) ht fun j hj => ?_
      interval_cases j
      · exact ⟨0, fl g12 f12 0 0 (by push_cast; ring)⟩
      · rcases hq with hq | hq
        · have hq' : (⌊3 * y2⌋ : ℝ) = ⌊3 * y1⌋ - 2 * q := by
            have : ⌊3 * y2⌋ = ⌊3 * y1⌋ - 2 * q := by omega
            exact_mod_cast this
          exact ⟨q - 1, fl g22 f22 1 (q - 1) (by rw [e22, e12]; push_cast; linarith)⟩
        · have hq' : (⌊3 * y2⌋ : ℝ) = ⌊3 * y1⌋ - 2 * q - 1 := by
            have : ⌊3 * y2⌋ = ⌊3 * y1⌋ - 2 * q - 1 := by omega
            exact_mod_cast this
          exact ⟨q, fl g21 f21 1 q (by rw [e21, e12]; push_cast; linarith)⟩
      · exact ⟨0, fl g11 f11 2 0 (by rw [e11, e12]; push_cast; linarith)⟩
      · rcases hq with hq | hq
        · have hq' : (⌊3 * y2⌋ : ℝ) = ⌊3 * y1⌋ - 2 * q := by
            have : ⌊3 * y2⌋ = ⌊3 * y1⌋ - 2 * q := by omega
            exact_mod_cast this
          exact ⟨q - 1, fl g21 f21 3 (q - 1) (by rw [e21, e12]; push_cast; linarith)⟩
        · have hq' : (⌊3 * y2⌋ : ℝ) = ⌊3 * y1⌋ - 2 * q - 1 := by
            have : ⌊3 * y2⌋ = ⌊3 * y1⌋ - 2 * q - 1 := by omega
            exact_mod_cast this
          exact ⟨q - 1, fl g22 f22 3 (q - 1) (by rw [e22, e12]; push_cast; linarith)⟩
    simp only [not_and_or, Set.not_nonempty_iff_eq_empty] at key
    rcases key with h | h | h | h <;> simp only [h, Set.ncard_empty] at h1 h2 <;> omega

theorem arcPath_digit_box {s t : ℝ} {N : ℕ} {p q : ℝ} {a : Fin N → ℤ} (h : ArcPath s t N p q a) :
    a ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℤ) 2) := by
  obtain ⟨f, hf, hstep, -, -⟩ := h
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨x, -, hx⟩ := hf i.castSucc
  obtain ⟨y, -, hy⟩ := hf i.succ
  have h1 := hstep i
  have := Int.fract_nonneg x; have := Int.fract_lt_one x
  have := Int.fract_nonneg y; have := Int.fract_lt_one y
  have hlo : (-2 : ℝ) < a i := by linarith
  have hhi : (a i : ℝ) < 3 := by linarith
  constructor
  · have : (-2 : ℤ) < a i := by exact_mod_cast hlo
    omega
  · have : a i < (3 : ℤ) := by exact_mod_cast hhi
    omega

/-- The words of backward paths of length `K` into `q`. -/
def bwdSet (s t : ℝ) (K : ℕ) (q : ℝ) : Set (Fin K → ℤ) := {a | ∃ p, ArcPath s t K p q a}

theorem bwdSet_finite (s t : ℝ) (K : ℕ) (q : ℝ) : (bwdSet s t K q).Finite :=
  (Set.Finite.pi (fun _ => Set.finite_Icc (-1 : ℤ) 2)).subset fun _ ⟨_, h⟩ => arcPath_digit_box h

theorem inArc_of_bwdSet_nonempty {s t : ℝ} {K : ℕ} {q : ℝ} (h : (bwdSet s t K q).Nonempty) :
    ∃ x ∈ Set.Icc s (s + t), q = Int.fract x := by
  obtain ⟨a, p, f, hf, -, -, hl⟩ := h
  rw [← hl]; exact hf _

/-- The base of `q`: `3 · fract(p - s) ≡ 2q - 3s` for every predecessor `p`. -/
noncomputable def bbase (s q : ℝ) : ℝ := Int.fract (2 * q - 3 * s)

/-- The base maps: the base of the predecessor in branch `k`. -/
noncomputable def phi (s : ℝ) (k : ℕ) (w : ℝ) : ℝ := Int.fract (2 * (w + k) / 3 - s)

/-- The candidate predecessor of `q` in branch `k ∈ {0, 1}`. -/
noncomputable def bpred (s q : ℝ) (k : ℕ) : ℝ := Int.fract (s + (bbase s q + k) / 3)

theorem bbase_bpred (s q : ℝ) (k : ℕ) : bbase s (bpred s q k) = phi s k (bbase s q) := by
  show Int.fract (2 * bpred s q k - 3 * s) = _
  unfold bpred phi
  rw [Int.fract_eq_fract]
  refine ⟨-2 * ⌊s + (bbase s q + k) / 3⌋, ?_⟩
  have := Int.floor_add_fract (s + (bbase s q + k) / 3)
  push_cast; linarith

/-- Every predecessor in the arc is `bpred s q 0` or `bpred s q 1`, and the second only when the
base is at most `τ = 3t - 1`. -/
theorem pred_cases {s t q p : ℝ} (ht : t < 2 / 3) (c : ℤ) (hq : q = 3 / 2 * p - (c : ℝ) / 2)
    (hp : ∃ x ∈ Set.Icc s (s + t), p = Int.fract x) :
    p = bpred s q 0 ∨ (p = bpred s q 1 ∧ bbase s q ≤ 3 * t - 1) := by
  obtain ⟨hp0, hp1, hu⟩ := (inArc_iff (by linarith)).1 hp
  set u := Int.fract (p - s) with hu_def
  have hu0 : 0 ≤ u := Int.fract_nonneg _
  -- 3u ≡ 2q - 3s
  have h3u : Int.fract (3 * u) = bbase s q := by
    unfold bbase
    rw [Int.fract_eq_fract]
    refine ⟨c - 3 * ⌊p - s⌋, ?_⟩
    have := Int.floor_add_fract (p - s)
    rw [hu_def, hq]; push_cast; linarith
  have hfl := Int.floor_add_fract (3 * u)
  have hk0 : 0 ≤ ⌊3 * u⌋ := Int.floor_nonneg.2 (by linarith)
  have hk1 : ⌊3 * u⌋ ≤ 1 := by
    have : ⌊3 * u⌋ < 2 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  -- p = fract (s + u)
  have hpu : p = Int.fract (s + u) := by
    rw [eq_comm, Int.fract_eq_iff]
    refine ⟨hp0, hp1, -⌊p - s⌋, ?_⟩
    have := Int.floor_add_fract (p - s)
    rw [hu_def]; push_cast; linarith
  rcases (show ⌊3 * u⌋ = 0 ∨ ⌊3 * u⌋ = 1 by omega) with h | h
  · left
    rw [hpu, bpred, ← h3u]
    congr 2
    rw [h] at hfl; push_cast at hfl ⊢; linarith
  · right
    refine ⟨?_, ?_⟩
    · rw [hpu, bpred, ← h3u]
      congr 2
      rw [h] at hfl; push_cast at hfl ⊢; linarith
    · rw [← h3u]; rw [h] at hfl; push_cast at hfl; linarith

/-- The last digit of a backward path is determined by its predecessor. -/
theorem bwdSet_succ_subset (s t : ℝ) (ht : t < 2 / 3) (j : ℕ) (q : ℝ) :
    bwdSet s t (j + 1) q ⊆
      (fun a' => Fin.snoc a' ⌊3 * bpred s q 0 - 2 * q⌋) '' bwdSet s t j (bpred s q 0) ∪
      (fun a' => Fin.snoc a' ⌊3 * bpred s q 1 - 2 * q⌋) '' bwdSet s t j (bpred s q 1) := by
  rintro a ⟨p, f, hf, hstep, h0, hl⟩
  set c := a (Fin.last j)
  have hq : q = 3 / 2 * f (Fin.last j).castSucc - (c : ℝ) / 2 := by
    rw [← hl, ← hstep (Fin.last j)]; rfl
  have hinit : Fin.init a ∈ bwdSet s t j (f (Fin.last j).castSucc) := by
    refine ⟨p, fun i => f i.castSucc, fun i => hf _, fun i => ?_, h0, rfl⟩
    have := hstep i.castSucc
    show f i.castSucc.succ = 3 / 2 * f i.castSucc.castSucc - (a i.castSucc : ℝ) / 2
    rw [Fin.succ_castSucc]; exact this
  have hc : ∀ p', f (Fin.last j).castSucc = p' → ⌊3 * p' - 2 * q⌋ = c := by
    rintro p' rfl
    rw [hq, show 3 * f (Fin.last j).castSucc - 2 * (3 / 2 * f (Fin.last j).castSucc - (c : ℝ) / 2) =
      (c : ℝ) by ring, Int.floor_intCast]
  have ha : a = Fin.snoc (Fin.init a) c := (Fin.snoc_init_self a).symm
  rcases pred_cases ht c hq (hf _) with h | ⟨h, -⟩
  · left; exact ⟨Fin.init a, h ▸ hinit, by rw [hc _ h]; exact ha.symm⟩
  · right; exact ⟨Fin.init a, h ▸ hinit, by rw [hc _ h]; exact ha.symm⟩

theorem bwdSet_succ_ncard (s t : ℝ) (ht : t < 2 / 3) (j : ℕ) (q : ℝ) :
    (bwdSet s t (j + 1) q).ncard ≤
      (bwdSet s t j (bpred s q 0)).ncard + (bwdSet s t j (bpred s q 1)).ncard := by
  refine (Set.ncard_le_ncard (bwdSet_succ_subset s t ht j q)
    (((bwdSet_finite _ _ _ _).image _).union ((bwdSet_finite _ _ _ _).image _))).trans ?_
  refine (Set.ncard_union_le _ _).trans ?_
  exact add_le_add (Set.ncard_image_le (bwdSet_finite _ _ _ _))
    (Set.ncard_image_le (bwdSet_finite _ _ _ _))

theorem bwdSet_pred1_empty {s t q : ℝ} (ht : t < 2 / 3) (j : ℕ) (hb : 3 * t - 1 < bbase s q) :
    bwdSet s t j (bpred s q 1) = ∅ := by
  by_contra hne
  obtain ⟨-, -, hu⟩ := (inArc_iff (by linarith)).1
    (inArc_of_bwdSet_nonempty (Set.nonempty_iff_ne_empty.2 hne))
  have hb0 : 0 ≤ bbase s q := Int.fract_nonneg _
  have hb1 : bbase s q < 1 := Int.fract_lt_one _
  have e : Int.fract (bpred s q 1 - s) = (bbase s q + 1) / 3 := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -⌊s + (bbase s q + ((1 : ℕ) : ℝ)) / 3⌋, ?_⟩
    have := Int.floor_add_fract (s + (bbase s q + ((1 : ℕ) : ℝ)) / 3)
    unfold bpred; push_cast at this ⊢; linarith
  rw [e] at hu
  linarith

/-- The tree of bases below `b` is everywhere at most `τ` to depth `j`. -/
def BaseGood (s τ : ℝ) : ℕ → ℝ → Prop
  | 0, _ => True
  | j + 1, b => b ≤ τ ∧ BaseGood s τ j (phi s 0 b) ∧ BaseGood s τ j (phi s 1 b)

theorem bwd_count (s t : ℝ) (ht : t < 2 / 3) : ∀ j : ℕ, ∀ q : ℝ,
    (bwdSet s t j q).ncard ≤ 2 ^ j ∧ (2 ^ j ≤ (bwdSet s t j q).ncard → BaseGood s (3 * t - 1) j (bbase s q)) := by
  intro j
  induction j with
  | zero =>
    intro q
    refine ⟨?_, fun _ => trivial⟩
    rw [pow_zero, Set.ncard_le_one_iff_subsingleton]
    intro a _ b _; exact Subsingleton.elim a b
  | succ j ih =>
    intro q
    have h := bwdSet_succ_ncard s t ht j q
    obtain ⟨b0, g0⟩ := ih (bpred s q 0)
    obtain ⟨b1, g1⟩ := ih (bpred s q 1)
    refine ⟨by rw [pow_succ]; omega, fun hge => ?_⟩
    rw [pow_succ] at hge
    have e0 : 2 ^ j ≤ (bwdSet s t j (bpred s q 0)).ncard := by omega
    have e1 : 2 ^ j ≤ (bwdSet s t j (bpred s q 1)).ncard := by omega
    refine ⟨?_, by rw [← bbase_bpred]; exact g0 e0, by rw [← bbase_bpred]; exact g1 e1⟩
    by_contra hlt
    rw [bwdSet_pred1_empty ht j (not_le.1 hlt), Set.ncard_empty] at e1
    have := Nat.one_le_two_pow (n := j)
    omega

/-- Leaf-side reachability of bases. -/
def BaseReach (s : ℝ) : ℕ → ℝ → ℝ → Prop
  | 0, b, w => w = b
  | j + 1, b, w => ∃ w', BaseReach s j b w' ∧ (w = phi s 0 w' ∨ w = phi s 1 w')

theorem reach_succ_iff (s : ℝ) : ∀ j : ℕ, ∀ b w : ℝ,
    BaseReach s (j + 1) b w ↔ BaseReach s j (phi s 0 b) w ∨ BaseReach s j (phi s 1 b) w := by
  intro j
  induction j with
  | zero => intro b w; simp [BaseReach]
  | succ j ih =>
    intro b w
    show (∃ w', BaseReach s (j + 1) b w' ∧ _) ↔ (∃ w', BaseReach s j _ w' ∧ _) ∨ (∃ w', BaseReach s j _ w' ∧ _)
    simp only [ih]
    constructor
    · rintro ⟨w', h1 | h1, h2⟩
      · exact Or.inl ⟨w', h1, h2⟩
      · exact Or.inr ⟨w', h1, h2⟩
    · rintro (⟨w', h1, h2⟩ | ⟨w', h1, h2⟩)
      · exact ⟨w', Or.inl h1, h2⟩
      · exact ⟨w', Or.inr h1, h2⟩

theorem good_reach (s τ : ℝ) : ∀ j : ℕ, ∀ b : ℝ, BaseGood s τ j b →
    ∀ i < j, ∀ w, BaseReach s i b w → w ≤ τ := by
  intro j
  induction j with
  | zero => intro b _ i hi; omega
  | succ j ih =>
    rintro b ⟨hb, h0, h1⟩ i hi w hw
    cases i with
    | zero => rw [show w = b from hw]; exact hb
    | succ i =>
      rcases (reach_succ_iff s i b w).1 hw with hw | hw
      · exact ih _ h0 i (by omega) w hw
      · exact ih _ h1 i (by omega) w hw

theorem reach_mem (s : ℝ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∀ j : ℕ, ∀ w, BaseReach s j b w → 0 ≤ w ∧ w < 1 := by
  intro j
  induction j with
  | zero => intro w hw; rw [show w = b from hw]; exact ⟨hb0, hb1⟩
  | succ j _ =>
    rintro w ⟨w', -, rfl | rfl⟩ <;> exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **Gap contraction.**  The reachable bases at depth `j` leave no forward gap of length
`(2/3)^j`. -/
theorem reach_dense (s : ℝ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∀ j : ℕ, ∀ x : ℝ, ∃ w, BaseReach s j b w ∧ Int.fract (w - x) < (2 / 3) ^ j := by
  intro j
  induction j with
  | zero => intro x; exact ⟨b, rfl, by simpa using Int.fract_lt_one (b - x)⟩
  | succ j ih =>
    intro x
    set G : ℝ := (2 / 3) ^ j
    set y := Int.fract (x + s) with hy
    have hy0 : 0 ≤ y := Int.fract_nonneg _
    have hy1 : y < 1 := Int.fract_lt_one _
    -- `fract (z - x) = fract (z + s - y)` shifted
    have shift : ∀ z : ℝ, Int.fract (Int.fract z - x) = Int.fract (z + s - y) := by
      intro z
      rw [Int.fract_eq_fract]
      refine ⟨-⌊z⌋ - ⌊x + s⌋, ?_⟩
      have h1 := Int.floor_add_fract z
      have h2 := Int.floor_add_fract (x + s)
      rw [hy]; push_cast; linarith
    -- reduce to an explicit bound
    have fin : ∀ w : ℝ, BaseReach s j b w → ∀ k : ℕ, (k = 0 ∨ k = 1) → ∀ e : ℝ, 0 ≤ e → e < 2 / 3 * G →
        (∃ n : ℤ, 2 * (w + k) / 3 - s + s - y = e + n) →
        ∃ w, BaseReach s (j + 1) b w ∧ Int.fract (w - x) < (2 / 3) ^ (j + 1) := by
      rintro w hw k hk e he0 he1 ⟨n, hn⟩
      refine ⟨phi s k w, ⟨w, hw, ?_⟩, ?_⟩
      · rcases hk with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rw [phi, shift, hn, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨he0, by
          have : G ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          linarith⟩, pow_succ]
        linarith
    have hG0 : 0 < G := by positivity
    by_cases hy2 : y < 2 / 3
    · obtain ⟨w, hw, hwx⟩ := ih (3 * y / 2)
      obtain ⟨hw0, hw1⟩ := reach_mem s hb0 hb1 j w hw
      by_cases hle : 3 * y / 2 ≤ w
      · rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at hwx
        exact fin w hw 0 (Or.inl rfl) (2 * (w - 3 * y / 2) / 3) (by linarith) (by linarith) ⟨0, by push_cast; ring⟩
      · have hfr : Int.fract (w - 3 * y / 2) = w - 3 * y / 2 + 1 := by
          rw [Int.fract_eq_iff]
          exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
        rw [hfr] at hwx
        exact fin w hw 1 (Or.inr rfl) (2 * (w - 3 * y / 2 + 1) / 3) (by linarith) (by linarith)
          ⟨0, by push_cast; ring⟩
    · push_neg at hy2
      obtain ⟨w, hw, hwx⟩ := ih (3 * y / 2 - 1)
      obtain ⟨hw0, hw1⟩ := reach_mem s hb0 hb1 j w hw
      by_cases hle : 3 * y / 2 - 1 ≤ w
      · rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at hwx
        exact fin w hw 1 (Or.inr rfl) (2 * (w - (3 * y / 2 - 1)) / 3) (by linarith) (by linarith)
          ⟨0, by push_cast; ring⟩
      · have hfr : Int.fract (w - (3 * y / 2 - 1)) = w - (3 * y / 2 - 1) + 1 := by
          rw [Int.fract_eq_iff]
          exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
        rw [hfr] at hwx
        exact fin w hw 0 (Or.inl rfl) (2 * (w - (3 * y / 2 - 1) + 1) / 3 - 1 / 3) (by linarith) (by linarith)
          ⟨-1, by push_cast; ring⟩

/-- **Forward paths from a point grow at most like Fibonacci (arcs shorter than `3/4`).**
PROVED 2026-10-06.  A point has at most two successors, `y` and `y + 1/2`.  If both branch
again, their four successors are `z, z + 1/4, z + 1/2, z + 3/4` mod 1, and an arc holding all four
has length at least `3/4`.  So of two sibling successors at most one branches, and the count
`M_n` satisfies `M_n ≤ M_{n-1} + M_{n-2}`. -/
theorem card_forward_le (s t p : ℝ) (ht : t < 3 / 4) (N : ℕ) :
    Nat.card {a : Fin N → ℤ // ∃ q, ArcPath s t N p q a} ≤ Nat.fib (N + 2) := by
  change Nat.card (fwdSet s t N p) ≤ _
  rw [Nat.card_coe_set_eq]
  exact (fwd_fib s t ht N p).1

/-- **Backward paths into a point lose a branch within `K` steps once `(2/3)^(K-1) < 2 - 3t`.**
PROVED 2026-10-06 (`arc_entropy.py backward` also samples the full depth, never above the
bound).  Proof: in the coordinate `v = 3 · ((f - s) mod 1) ∈ [0, 3t]`, the predecessors of `v` are
the points of `2v/3 - s + ℤ` in `[0, 3t]`.  These are `w = frac(2v/3 - s)` and also `w + 1` exactly
when `w ≤ τ := 3t - 1`.  In a tree that is full to depth `j`, the depth-`j` values `w` arise from
one point by `j` rounds of `w ↦ frac(2w/3 - s)` and `w ↦ frac(2w/3 + 2/3 - s)`.  Each round
multiplies the largest circular gap by `2/3`, so the gaps are at most `(2/3)^j`.  Once
`(2/3)^j < 1 - τ = 2 - 3t`, some node falls in `(τ, 1)` and has one predecessor. -/
theorem card_backward_le (s t q : ℝ) (ht : t < 2 / 3) (K : ℕ) (hK : 1 ≤ K)
    (hK' : (2 / 3 : ℝ) ^ (K - 1) < 2 - 3 * t) :
    Nat.card {a : Fin K → ℤ // ∃ p, ArcPath s t K p q a} ≤ 2 ^ K - 1 := by
  change Nat.card (bwdSet s t K q) ≤ _
  rw [Nat.card_coe_set_eq]
  obtain ⟨hle, hgood⟩ := bwd_count s t ht K q
  by_contra hlt
  have hge : 2 ^ K ≤ (bwdSet s t K q).ncard := by
    have := Nat.one_le_two_pow (n := K); omega
  have hg := hgood hge
  have hb0 : 0 ≤ bbase s q := Int.fract_nonneg _
  have hb1 : bbase s q < 1 := Int.fract_lt_one _
  set G : ℝ := (2 / 3) ^ (K - 1)
  have hG0 : 0 < G := by positivity
  obtain ⟨w, hw, hwx⟩ := reach_dense s hb0 hb1 (K - 1) (1 - G)
  obtain ⟨hw0, hw1⟩ := reach_mem s hb0 hb1 _ w hw
  have hwτ := good_reach s _ K _ hg (K - 1) (by omega) w hw
  by_cases hle' : 1 - G ≤ w
  · linarith
  · have : Int.fract (w - (1 - G)) = w - (1 - G) + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [this] at hwx
    linarith

/-! #### Helpers for the growth bound -/

/-- **Left edge.**  Every admissible word has a path that touches a left edge of the arc,
`fract s` or `0`: lower the start until some `f_j` hits an edge. -/
theorem exists_edge_path {s t : ℝ} (ht : t < 1) {N : ℕ} {a : Fin N → ℤ}
    (h : AdmissibleWord s t N a) :
    ∃ f : Fin (N + 1) → ℝ, (∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x) ∧
      (∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2) ∧
      ∃ j : Fin (N + 1), f j = Int.fract s ∨ f j = 0 := by
  obtain ⟨f, hf, hstep⟩ := h
  have hf' : ∀ i, 0 ≤ f i ∧ f i < 1 ∧ Int.fract (f i - s) ≤ t := fun i => (inArc_iff ht).1 (hf i)
  set e : Fin (N + 1) → ℝ := fun i => min (f i) (Int.fract (f i - s)) / (3 / 2) ^ (i : ℕ) with he
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  set δ := e j
  have hpos : ∀ n : ℕ, (0 : ℝ) < (3 / 2) ^ n := fun n => by positivity
  have hδ0 : 0 ≤ δ := div_nonneg (le_min (hf' j).1 (Int.fract_nonneg _)) (hpos _).le
  have hd : ∀ i : Fin (N + 1), (3 / 2 : ℝ) ^ (i : ℕ) * δ ≤ min (f i) (Int.fract (f i - s)) := by
    intro i
    have := hj i (Finset.mem_univ _)
    rw [he] at this
    simp only at this
    rw [le_div_iff₀ (hpos _)] at this
    linarith
  refine ⟨fun i => f i - (3 / 2) ^ (i : ℕ) * δ, fun i => ?_, fun i => ?_, j, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hf' i
    have hdi := hd i
    have hm1 := min_le_left (f i) (Int.fract (f i - s))
    have hm2 := min_le_right (f i) (Int.fract (f i - s))
    have hdp : 0 ≤ (3 / 2 : ℝ) ^ (i : ℕ) * δ := mul_nonneg (hpos _).le hδ0
    refine (inArc_iff ht).2 ⟨by linarith, by linarith, ?_⟩
    have : Int.fract (f i - (3 / 2) ^ (i : ℕ) * δ - s) =
        Int.fract (f i - s) - (3 / 2) ^ (i : ℕ) * δ := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith [Int.fract_lt_one (f i - s)], ⌊f i - s⌋, ?_⟩
      have := Int.floor_add_fract (f i - s)
      linarith
    rw [this]; linarith
  · simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    rw [hstep i]; ring
  · simp only
    have h0 := (hf' j).1
    have h1 := (hf' j).2.1
    have hdj : (3 / 2 : ℝ) ^ (j : ℕ) * δ = min (f j) (Int.fract (f j - s)) := by
      simp only [δ, he]
      field_simp
    rw [hdj]
    rcases min_choice (f j) (Int.fract (f j - s)) with hm | hm
    · right; rw [hm]; ring
    · left
      rw [hm, eq_comm, Int.fract_eq_iff]
      have hm2 : Int.fract (f j - s) ≤ f j := hm ▸ min_le_left _ _
      refine ⟨by linarith, by linarith [Int.fract_nonneg (f j - s)], -⌊f j - s⌋, ?_⟩
      have := Int.floor_add_fract (f j - s)
      push_cast; linarith

/-- Prefix and suffix of a word at position `j`. -/
def wpre {N : ℕ} (j : Fin (N + 1)) (a : Fin N → ℤ) : Fin j → ℤ :=
  fun i => a ⟨i, by have := j.isLt; omega⟩

def wsuf {N : ℕ} (j : Fin (N + 1)) (a : Fin N → ℤ) : Fin (N - j) → ℤ :=
  fun i => a ⟨j + i, by have := i.isLt; omega⟩

theorem wpre_wsuf_injective {N : ℕ} (j : Fin (N + 1)) {a b : Fin N → ℤ}
    (h1 : wpre j a = wpre j b) (h2 : wsuf j a = wsuf j b) : a = b := by
  funext k
  by_cases hk : (k : ℕ) < j
  · have := congrFun h1 ⟨k, hk⟩
    simpa [wpre] using this
  · have := congrFun h2 ⟨k - j, by have := k.isLt; omega⟩
    simp only [wsuf] at this
    convert this using 2 <;> ext <;> simp <;> omega

/-- The edge pieces: words that split at `j` into a backward path into `b` and a forward path
out of `b`. -/
def edgePiece (s t : ℝ) (N : ℕ) (j : Fin (N + 1)) (b : ℝ) : Set (Fin N → ℤ) :=
  {a | wpre j a ∈ bwdSet s t j b ∧ wsuf j a ∈ fwdSet s t (N - j) b}

theorem edgePiece_ncard (s t : ℝ) (N : ℕ) (j : Fin (N + 1)) (b : ℝ) :
    (edgePiece s t N j b).ncard ≤ (bwdSet s t j b).ncard * (fwdSet s t (N - j) b).ncard := by
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn (fun a => (wpre j a, wsuf j a)) (fun a ha => ha)
    (fun a _ b _ h => ?_) ((bwdSet_finite _ _ _ _).prod (fwdSet_finite _ _ _ _))
  simp only [Prod.mk.injEq] at h
  exact wpre_wsuf_injective j h.1 h.2

theorem edgePiece_finite (s t : ℝ) (N : ℕ) (j : Fin (N + 1)) (b : ℝ) :
    (edgePiece s t N j b).Finite := by
  refine Set.Finite.of_finite_image (f := fun a => (wpre j a, wsuf j a)) ?_ ?_
  · refine ((bwdSet_finite s t j b).prod (fwdSet_finite s t (N - j) b)).subset ?_
    rintro _ ⟨a, ha, rfl⟩; exact ha
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact wpre_wsuf_injective j h.1 h.2

/-- Split a path at an interior point. -/
theorem split_path {s t : ℝ} {N : ℕ} {a : Fin N → ℤ} (f : Fin (N + 1) → ℝ)
    (hf : ∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x)
    (hstep : ∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2) (j : Fin (N + 1)) :
    wpre j a ∈ bwdSet s t j (f j) ∧ wsuf j a ∈ fwdSet s t (N - j) (f j) := by
  have hj := j.isLt
  constructor
  · refine ⟨f 0, fun i => f ⟨i, by omega⟩, fun i => hf _, fun i => ?_, rfl, ?_⟩
    · have := hstep ⟨i, by omega⟩
      simp only [wpre]
      convert this using 3 <;> first | exact congrArg f (Fin.ext (by simp)) | (simp <;> omega)
    · simp
  · refine ⟨f (Fin.last N), fun i => f ⟨j + i, by omega⟩, fun i => hf _, fun i => ?_, by simp, ?_⟩
    · have := hstep ⟨j + i, by omega⟩
      simp only [wsuf]
      convert this using 3 <;> first | exact congrArg f (Fin.ext (by simp)) | (simp <;> omega)
    · exact congrArg f (Fin.ext (by simp; omega))

theorem admissible_ncard_le (s t : ℝ) (ht : t < 1) (N : ℕ) :
    {a : Fin N → ℤ | AdmissibleWord s t N a}.ncard ≤
      ∑ j : Fin (N + 1), ((bwdSet s t j (Int.fract s)).ncard * (fwdSet s t (N - j) (Int.fract s)).ncard
        + (bwdSet s t j 0).ncard * (fwdSet s t (N - j) 0).ncard) := by
  have hsub : {a : Fin N → ℤ | AdmissibleWord s t N a} ⊆
      ⋃ j : Fin (N + 1), (edgePiece s t N j (Int.fract s) ∪ edgePiece s t N j 0) := by
    intro a ha
    obtain ⟨f, hf, hstep, j, hj⟩ := exists_edge_path ht ha
    have := split_path f hf hstep j
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rcases hj with hj | hj
    · left; rw [← hj]; exact this
    · right; rw [← hj]; exact this
  have hfin : (⋃ j : Fin (N + 1), (edgePiece s t N j (Int.fract s) ∪ edgePiece s t N j 0)).Finite :=
    Set.finite_iUnion fun j => (edgePiece_finite _ _ _ _ _).union (edgePiece_finite _ _ _ _ _)
  refine (Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_iUnion_le_of_fintype _).trans ?_)
  refine Finset.sum_le_sum fun j _ => (Set.ncard_union_le _ _).trans ?_
  exact add_le_add (edgePiece_ncard _ _ _ _ _) (edgePiece_ncard _ _ _ _ _)

/-- Split an arc path at an interior point, keeping endpoints. -/
theorem split_arcPath {s t : ℝ} {N : ℕ} {a : Fin N → ℤ} (f : Fin (N + 1) → ℝ)
    (hf : ∀ i, ∃ x ∈ Set.Icc s (s + t), f i = Int.fract x)
    (hstep : ∀ i : Fin N, f i.succ = 3 / 2 * f i.castSucc - (a i : ℝ) / 2) (j : Fin (N + 1)) :
    ArcPath s t j (f 0) (f j) (wpre j a) ∧ ArcPath s t (N - j) (f j) (f (Fin.last N)) (wsuf j a) := by
  have hj := j.isLt
  constructor
  · refine ⟨fun i => f ⟨i, by omega⟩, fun i => hf _, fun i => ?_, rfl, ?_⟩
    · have := hstep ⟨i, by omega⟩
      simp only [wpre]
      convert this using 3 <;> first | exact congrArg f (Fin.ext (by simp)) | (simp <;> omega)
    · simp
  · refine ⟨fun i => f ⟨j + i, by omega⟩, fun i => hf _, fun i => ?_, by simp, ?_⟩
    · have := hstep ⟨j + i, by omega⟩
      simp only [wsuf]
      convert this using 3 <;> first | exact congrArg f (Fin.ext (by simp)) | (simp <;> omega)
    · exact congrArg f (Fin.ext (by simp; omega))

/-- A backward path is determined by its endpoint and digits. -/
theorem arcPath_start_unique {s t : ℝ} {K : ℕ} {p p' q : ℝ} {a : Fin K → ℤ}
    (h : ArcPath s t K p q a) (h' : ArcPath s t K p' q a) : p = p' := by
  obtain ⟨f, -, hs, h0, hl⟩ := h
  obtain ⟨f', -, hs', h0', hl'⟩ := h'
  have key : ∀ m i : ℕ, (hi : i ≤ K) → i + m = K →
      f ⟨i, by omega⟩ = f' ⟨i, by omega⟩ := by
    intro m
    induction m with
    | zero =>
      intro i hi him
      have e : (⟨i, by omega⟩ : Fin (K + 1)) = Fin.last K := Fin.ext (by simp; omega)
      rw [e, hl, hl']
    | succ m ih =>
      intro i hi him
      have h1 := hs ⟨i, by omega⟩
      have h2 := hs' ⟨i, by omega⟩
      have h3 := ih (i + 1) (by omega) (by omega)
      simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
      linarith
  rw [← h0, ← h0']
  exact key K 0 (by omega) (by omega)

/-- **Backward submultiplicativity.** -/
theorem bwd_submult (s t : ℝ) {N : ℕ} (j : Fin (N + 1)) (q : ℝ) (X : ℕ)
    (hX : ∀ q', (bwdSet s t j q').ncard ≤ X) :
    (bwdSet s t N q).ncard ≤ (bwdSet s t (N - j) q).ncard * X := by
  classical
  set T := bwdSet s t (N - j) q
  let r : (Fin (N - j) → ℤ) → ℝ := fun σ => Classical.epsilon (fun p => ArcPath s t (N - j) p q σ)
  let F : (Fin (N - j) → ℤ) → Set (Fin N → ℤ) :=
    fun σ => {a | wsuf j a = σ ∧ wpre j a ∈ bwdSet s t j (r σ)}
  have hFinj : ∀ σ, Set.InjOn (wpre j) (F σ) := by
    intro σ a ha b hb h
    exact wpre_wsuf_injective j h (ha.1.trans hb.1.symm)
  have hFfin : ∀ σ, (F σ).Finite := fun σ =>
    Set.Finite.of_finite_image ((bwdSet_finite s t j (r σ)).subset (by
      rintro _ ⟨a, ha, rfl⟩; exact ha.2)) (hFinj σ)
  have hsub : bwdSet s t N q ⊆ ⋃ σ ∈ (bwdSet_finite s t (N - j) q).toFinset, F σ := by
    rintro a ⟨p, f, hf, hstep, h0, hl⟩
    obtain ⟨h1, h2⟩ := split_arcPath f hf hstep j
    rw [hl] at h2
    have hσ : wsuf j a ∈ T := ⟨f j, h2⟩
    have hr : r (wsuf j a) = f j :=
      arcPath_start_unique (Classical.epsilon_spec (p := fun p => ArcPath s t (N - j) p q (wsuf j a))
        ⟨f j, h2⟩) h2
    refine Set.mem_biUnion (x := wsuf j a) (by simpa using hσ) ⟨rfl, ?_⟩
    rw [hr]; exact ⟨f 0, h1⟩
  have hfin : (⋃ σ ∈ (bwdSet_finite s t (N - j) q).toFinset, F σ).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun σ _ => hFfin σ
  refine (Set.ncard_le_ncard hsub hfin).trans ((Finset.set_ncard_biUnion_le _ _).trans ?_)
  rw [Set.ncard_eq_toFinset_card _ (bwdSet_finite s t (N - j) q), ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  exact (Set.ncard_le_ncard_of_injOn (wpre j) (fun a ha => ha.2) (hFinj σ)
    (bwdSet_finite _ _ _ _)).trans (hX _)

theorem bwd_count_le (s t : ℝ) (ht : t < 2 / 3) (j : ℕ) (q : ℝ) :
    (bwdSet s t j q).ncard ≤ 2 ^ j :=
  (bwd_count s t ht j q).1

theorem fib_le_real : ∀ n : ℕ, (Nat.fib (n + 2) : ℝ) ≤ 2 * (7 / 4) ^ n ∧
    (Nat.fib (n + 3) : ℝ) ≤ 2 * (7 / 4) ^ (n + 1) := by
  intro n
  induction n with
  | zero => norm_num [Nat.fib_add_two]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 3 = (n + 2) + 2 by ring, Nat.fib_add_two]
    push_cast
    have hx : (0 : ℝ) ≤ (7 / 4) ^ n := by positivity
    have h1 := ih.1; have h2 := ih.2
    rw [show n + 2 + 1 = n + 3 by ring]
    rw [pow_succ] at h2
    rw [pow_succ, pow_succ]
    linarith

theorem rho_exists (K : ℕ) : ∃ ρ : ℝ, 7 / 4 < ρ ∧ ρ < 2 ∧ (2 : ℝ) ^ K - 1 ≤ ρ ^ K := by
  set ε : ℝ := 1 / (K * 2 ^ K + 8) with hε
  have hden : (0 : ℝ) < K * 2 ^ K + 8 := by positivity
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 8 := by
    rw [hε]; apply one_div_le_one_div_of_le (by norm_num); have : (0 : ℝ) ≤ K * 2 ^ K := by positivity
    linarith
  have hKε : (K : ℝ) * 2 ^ K * ε ≤ 1 := by
    rw [hε, mul_one_div, div_le_one hden]; linarith
  refine ⟨2 - ε, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -(ε / 2)) (by linarith) K
  have : (2 - ε) ^ K = 2 ^ K * (1 + -(ε / 2)) ^ K := by
    rw [← mul_pow]; congr 1; ring
  rw [this]
  have h2 : (0 : ℝ) ≤ 2 ^ K := by positivity
  nlinarith

theorem bwd_geom (s t : ℝ) (ht : t < 2 / 3) (K : ℕ) (hK : 1 ≤ K)
    (hKb : (2 / 3 : ℝ) ^ (K - 1) < 2 - 3 * t) (ρ : ℝ) (hρ1 : 1 ≤ ρ)
    (hρK : (2 : ℝ) ^ K - 1 ≤ ρ ^ K) : ∀ N q, ((bwdSet s t N q).ncard : ℝ) ≤ 2 ^ K * ρ ^ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro q
    by_cases hNK : N < K
    · have h1 : ((bwdSet s t N q).ncard : ℝ) ≤ 2 ^ N := by exact_mod_cast bwd_count_le s t ht N q
      have h2 : (2 : ℝ) ^ N ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hNK.le
      have h3 : (1 : ℝ) ≤ ρ ^ N := one_le_pow₀ hρ1
      have h4 : (0 : ℝ) ≤ 2 ^ K := by positivity
      nlinarith
    · push_neg at hNK
      set j : Fin (N + 1) := ⟨N - K, by omega⟩
      have hX : ∀ q', (bwdSet s t j q').ncard ≤ ⌊(2 : ℝ) ^ K * ρ ^ (N - K)⌋₊ := fun q' =>
        Nat.le_floor (ih (N - K) (by omega) q')
      have hsm := bwd_submult s t j q _ hX
      have hjK : N - (j : ℕ) = K := by simp [j]; omega
      have hBK : (bwdSet s t (N - j) q).ncard ≤ 2 ^ K - 1 := by
        rw [hjK]
        have := card_backward_le s t q ht K hK hKb
        rwa [show Nat.card {a : Fin K → ℤ // ∃ p, ArcPath s t K p q a} = (bwdSet s t K q).ncard
          from Nat.card_coe_set_eq _] at this
      have hfl : (⌊(2 : ℝ) ^ K * ρ ^ (N - K)⌋₊ : ℝ) ≤ 2 ^ K * ρ ^ (N - K) :=
        Nat.floor_le (by positivity)
      have hcast : ((2 ^ K - 1 : ℕ) : ℝ) = (2 : ℝ) ^ K - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
      have e1 : ((bwdSet s t N q).ncard : ℝ) ≤
          ((2 ^ K - 1 : ℕ) : ℝ) * (⌊(2 : ℝ) ^ K * ρ ^ (N - K)⌋₊ : ℝ) := by
        exact_mod_cast hsm.trans (Nat.mul_le_mul_right _ hBK)
      rw [hcast] at e1
      have hpos : (0 : ℝ) ≤ 2 ^ K - 1 := by
        have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num); linarith
      have e2 : ((2 : ℝ) ^ K - 1) * (⌊(2 : ℝ) ^ K * ρ ^ (N - K)⌋₊ : ℝ) ≤
          ρ ^ K * (2 ^ K * ρ ^ (N - K)) :=
        mul_le_mul hρK hfl (Nat.cast_nonneg _) (by positivity)
      calc ((bwdSet s t N q).ncard : ℝ) ≤ ρ ^ K * (2 ^ K * ρ ^ (N - K)) := e1.trans e2
        _ = 2 ^ K * ρ ^ N := by
          rw [show N = K + (N - K) by omega, pow_add]; simp only [Nat.add_sub_cancel_left]; ring

/-- The growth bound with a nonnegative rate, in `ncard` form. -/
theorem admissibleWord_growth_pos (s t : ℝ) (ht : t < 2 / 3) :
    ∃ C lam : ℝ, 0 ≤ lam ∧ lam < 2 ∧ ∀ N : ℕ,
      ({a : Fin N → ℤ | AdmissibleWord s t N a}.ncard : ℝ) ≤ C * lam ^ N := by
  have h23 : (0 : ℝ) < 2 - 3 * t := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h23 (show (2 / 3 : ℝ) < 1 by norm_num)
  set K := n + 1
  have hKb : (2 / 3 : ℝ) ^ (K - 1) < 2 - 3 * t := by simpa [K] using hn
  obtain ⟨ρ, hρ1, hρ2, hρK⟩ := rho_exists K
  set r : ℝ := 7 / (4 * ρ) with hr
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
  refine ⟨4 * 2 ^ K / (1 - r), ρ, by linarith, hρ2, fun N => ?_⟩
  have hB := bwd_geom s t ht K (by omega) hKb ρ (by linarith) hρK
  have hM : ∀ m p, ((fwdSet s t m p).ncard : ℝ) ≤ 2 * (7 / 4) ^ m := fun m p =>
    (by exact_mod_cast (fwd_fib s t (by linarith) m p).1 : ((fwdSet s t m p).ncard : ℝ) ≤
      Nat.fib (m + 2)).trans (fib_le_real m).1
  have h0 := admissible_ncard_le s t (by linarith) N
  have h1 : ({a : Fin N → ℤ | AdmissibleWord s t N a}.ncard : ℝ) ≤
      ∑ j : Fin (N + 1), (4 * 2 ^ K) * (ρ ^ N * r ^ (N - (j : ℕ))) := by
    refine (Nat.cast_le.2 h0).trans ?_
    push_cast
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := j.isLt
    have eq : ρ ^ (j : ℕ) * (7 / 4) ^ (N - (j : ℕ)) = ρ ^ N * r ^ (N - (j : ℕ)) := by
      rw [hr, show (7 / 4 : ℝ) = 7 / (4 * ρ) * ρ by field_simp, mul_pow]
      have : ρ ^ N = ρ ^ (j : ℕ) * ρ ^ (N - (j : ℕ)) := by rw [← pow_add]; congr 1; omega
      rw [this]; ring
    have b1 := hB j (Int.fract s); have b2 := hB j 0
    have m1 := hM (N - j) (Int.fract s); have m2 := hM (N - j) 0
    have p1 : (0 : ℝ) ≤ (bwdSet s t j (Int.fract s)).ncard := Nat.cast_nonneg _
    have p2 : (0 : ℝ) ≤ (bwdSet s t j 0).ncard := Nat.cast_nonneg _
    have p3 : (0 : ℝ) ≤ (fwdSet s t (N - j) (Int.fract s)).ncard := Nat.cast_nonneg _
    have p4 : (0 : ℝ) ≤ (fwdSet s t (N - j) 0).ncard := Nat.cast_nonneg _
    calc _ ≤ (2 ^ K * ρ ^ (j : ℕ)) * (2 * (7 / 4) ^ (N - j)) +
          (2 ^ K * ρ ^ (j : ℕ)) * (2 * (7 / 4) ^ (N - j)) :=
          add_le_add (mul_le_mul b1 m1 p3 (by positivity)) (mul_le_mul b2 m2 p4 (by positivity))
      _ = 4 * 2 ^ K * (ρ ^ (j : ℕ) * (7 / 4) ^ (N - (j : ℕ))) := by ring
      _ = _ := by rw [eq]
  have h2 : ∑ j : Fin (N + 1), r ^ (N - (j : ℕ)) ≤ 1 / (1 - r) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => r ^ (N - j)) (N + 1)]
    have := Finset.sum_range_reflect (fun i => r ^ i) (N + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [this, Finset.range_eq_Ico]
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) hr0 hr1
  refine h1.trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hρN : 0 ≤ ρ ^ N := by positivity
  calc 4 * 2 ^ K * (ρ ^ N * ∑ j : Fin (N + 1), r ^ (N - (j : ℕ)))
      ≤ 4 * 2 ^ K * (ρ ^ N * (1 / (1 - r))) := by gcongr
    _ = 4 * 2 ^ K / (1 - r) * ρ ^ N := by ring

/-- **Digit words grow strictly slower than `2^N` on every arc shorter than `2/3`.**
PROVED 2026-10-06 (the `ℓ` is found by lowering the start, `exists_edge_path`).  Proof: every component of a word's cylinder has a left endpoint `ℓ` where some
`f_j(ℓ)` is a left edge `b` of the arc (`b = s`, or `b = 0` when the arc wraps).  So the word is a
backward path of length `j` into `b` followed by a forward path of length `N - j` from just right of
`b`.  Hence `W_N ≤ 2 Σ_j B_j M_{N-j} ≤ C (N + 1) λ^N` with `λ = max(φ, (2^K - 1)^{1/K}) < 2`, by
`card_forward_le` and `card_backward_le`. -/
theorem admissibleWord_growth_lt_two (s t : ℝ) (ht : t < 2 / 3) :
    ∃ C lam : ℝ, lam < 2 ∧ ∀ N : ℕ, (Nat.card {a : Fin N → ℤ // AdmissibleWord s t N a} : ℝ) ≤
      C * lam ^ N := by
  obtain ⟨C, lam, -, hl, h⟩ := admissibleWord_growth_pos s t ht
  exact ⟨C, lam, hl, fun N => by
    rw [show Nat.card {a : Fin N → ℤ // AdmissibleWord s t N a} =
      {a : Fin N → ℤ | AdmissibleWord s t N a}.ncard from Nat.card_coe_set_eq _]
    exact h N⟩

/-! #### Injectivity and density for the barrier -/

theorem admissible_finite (s t : ℝ) (N : ℕ) : {a : Fin N → ℤ | AdmissibleWord s t N a}.Finite :=
  (Set.Finite.pi (fun _ => Set.finite_Icc (-1 : ℤ) 2)).subset fun _ ⟨f, hf, hs⟩ =>
    arcPath_digit_box ⟨f, hf, hs, rfl, rfl⟩

/-- The digit word of a trapped floor (through a chosen witness `ξ`). -/
noncomputable def floorWitness (s t : ℝ) (g : ℕ) : ℝ :=
  open Classical in if h : TrappedFloor s t g then h.choose else 0

theorem floorWitness_spec {s t : ℝ} {g : ℕ} (h : TrappedFloor s t g) :
    0 < floorWitness s t g ∧ ⌊floorWitness s t g⌋ = (g : ℤ) ∧
      ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (floorWitness s t g * (3 / 2) ^ n) = Int.fract x := by
  unfold floorWitness
  rw [dif_pos h]
  exact h.choose_spec

noncomputable def floorWord (s t : ℝ) (N g : ℕ) : Fin N → ℤ :=
  fun i => 2 * ⌊floorWitness s t g * (3 / 2) ^ ((i : ℕ) + 1)⌋ -
    3 * ⌊floorWitness s t g * (3 / 2) ^ (i : ℕ)⌋

theorem floorWord_admissible {s t : ℝ} {g : ℕ} (h : TrappedFloor s t g) (N : ℕ) :
    AdmissibleWord s t N (floorWord s t N g) := by
  obtain ⟨-, -, horb⟩ := floorWitness_spec h
  refine ⟨fun i => Int.fract (floorWitness s t g * (3 / 2) ^ (i : ℕ)), fun i => ?_, fun i => ?_⟩
  · obtain ⟨x, hx, he⟩ := horb i
    exact ⟨x, hx, he⟩
  · simp only [floorWord, Fin.val_succ, Fin.val_castSucc, Int.fract]
    push_cast
    rw [pow_succ]
    ring

theorem floorWord_dvd {s t : ℝ} {g g' : ℕ} (h : TrappedFloor s t g) (h' : TrappedFloor s t g')
    (N : ℕ) (heq : floorWord s t N g = floorWord s t N g') : (2 : ℤ) ^ N ∣ (g : ℤ) - g' := by
  obtain ⟨-, hfl, -⟩ := floorWitness_spec h
  obtain ⟨-, hfl', -⟩ := floorWitness_spec h'
  set G : ℕ → ℤ := fun n => ⌊floorWitness s t g * (3 / 2) ^ n⌋
  set G' : ℕ → ℤ := fun n => ⌊floorWitness s t g' * (3 / 2) ^ n⌋
  have key : ∀ n, n ≤ N → (2 : ℤ) ^ n * (G n - G' n) = 3 ^ n * ((g : ℤ) - g') := by
    intro n
    induction n with
    | zero => intro _; simp [G, G', hfl, hfl']
    | succ n ih =>
      intro hn
      have hd := congrFun heq ⟨n, by omega⟩
      simp only [floorWord] at hd
      have := ih (by omega)
      rw [pow_succ, pow_succ]
      have e : 2 * (G (n + 1) - G' (n + 1)) = 3 * (G n - G' n) := by
        simp only [G, G']; linarith
      calc (2 : ℤ) ^ n * 2 * (G (n + 1) - G' (n + 1)) = 2 ^ n * (2 * (G (n + 1) - G' (n + 1))) := by ring
        _ = 2 ^ n * (3 * (G n - G' n)) := by rw [e]
        _ = 3 * (2 ^ n * (G n - G' n)) := by ring
        _ = _ := by rw [this]; ring
  have hk := key N le_rfl
  have hcop : IsCoprime ((2 : ℤ) ^ N) (3 ^ N) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  exact hcop.dvd_of_dvd_mul_left ⟨G N - G' N, hk.symm⟩

/-- Trapped floors below `2^N` are at most the admissible words of length `N`. -/
theorem trapped_ncard_le (s t : ℝ) (N : ℕ) :
    {g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard ≤
      {a : Fin N → ℤ | AdmissibleWord s t N a}.ncard := by
  refine Set.ncard_le_ncard_of_injOn (floorWord s t N) (fun g hg => floorWord_admissible hg.2 N)
    (fun g hg g' hg' he => ?_) (admissible_finite s t N)
  have hd := floorWord_dvd hg.2 hg'.2 N he
  obtain ⟨c, hc⟩ := hd
  have h1 := hg.1; have h2 := hg'.1
  have hP : (0 : ℤ) < 2 ^ N := by positivity
  have : c = 0 := by
    have hlt : ((g : ℤ) - g') < 2 ^ N := by
      have : (g : ℤ) < 2 ^ N := by exact_mod_cast h1
      linarith [(Int.natCast_nonneg g')]
    have hgt : -(2 ^ N : ℤ) < ((g : ℤ) - g') := by
      have : (g' : ℤ) < 2 ^ N := by exact_mod_cast h2
      linarith [(Int.natCast_nonneg g)]
    rw [hc] at hlt hgt
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · nlinarith
    · nlinarith
  rw [this, mul_zero, sub_eq_zero] at hc
  exact_mod_cast hc

/-- A residue class gives many trapped floors below `2^N`. -/
theorem trapped_ncard_ge {s t : ℝ} {k r : ℕ} (hr : r < 2 ^ k) (hT : TrapsResidueClass s t k r)
    (N : ℕ) : 2 ^ N / (3 * 2 ^ k) - 2 ≤ {g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard := by
  set M := 3 * 2 ^ k with hM
  set L := 2 ^ N / M - 2
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hm : ∀ i : Fin L, ∃ g : ℕ, r + 2 ^ k + i * M ≤ g ∧ g < r + 2 ^ k + i * M + 3 ∧
      TrappedFloor s t g := fun i =>
    hT _ (by omega) (by
      rw [show r + 2 ^ k + i * M = r + 2 ^ k * (1 + 3 * i) by rw [hM]; ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr])
  choose g hg1 hg2 hg3 using hm
  have hdiv : 2 ^ N / M * M ≤ 2 ^ N := Nat.div_mul_le_self _ _
  have hle : ∀ i : Fin L, g i < 2 ^ N := by
    intro i
    have hi : (i : ℕ) + 2 < 2 ^ N / M := by have := i.isLt; omega
    have h1 : ((i : ℕ) + 2 + 1) * M ≤ 2 ^ N / M * M := Nat.mul_le_mul_right _ hi
    have h2 : r + 2 ^ k + 3 ≤ 2 * M := by omega
    have := hg2 i
    nlinarith
  have hinj : Function.Injective g := by
    intro i i' he
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have : ((i : ℕ) + 1) * M ≤ (i' : ℕ) * M := Nat.mul_le_mul_right _ hlt
      have := hg2 i; have := hg1 i'
      have hM3 : 3 ≤ M := by omega
      nlinarith
    · have : ((i' : ℕ) + 1) * M ≤ (i : ℕ) * M := Nat.mul_le_mul_right _ hlt
      have := hg2 i'; have := hg1 i
      have hM3 : 3 ≤ M := by omega
      nlinarith
  have := Set.ncard_le_ncard_of_injOn g (s := (Set.univ : Set (Fin L)))
    (t := {g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}) (fun i _ => ⟨hle i, hg3 i⟩)
    hinj.injOn (Set.Finite.subset (Set.finite_lt_nat (2 ^ N)) fun x hx => hx.1)
  simpa [Set.ncard_univ] using this

/-- **Finite-memory barrier, all the way to `2/3`.**  No construction that works on a whole residue
class mod `2^k` traps orbits in any arc shorter than `2/3`.
PROVED 2026-10-06.  Proof: `admissibleWord_growth_lt_two`, plus the injectivity and density steps of
`finiteMemory_barrier` (`N` digits fix `g_0 mod 2^N`; a residue class gives `≥ 2^{N-k}/3 - 1`
trapped floors below `2^N + 3`). -/
theorem finiteMemory_barrier_two_thirds (s t : ℝ) (ht : t < 2 / 3) (k r : ℕ) (hr : r < 2 ^ k) :
    ¬ TrapsResidueClass s t k r := by
  intro hT
  obtain ⟨C, lam, hl0, hl2, hW⟩ := admissibleWord_growth_pos s t ht
  set c : ℝ := 1 / (3 * 2 ^ k)
  have hc : 0 < c := by positivity
  -- for every N: c 2^N - 3 ≤ C lam^N
  have hbound : ∀ N : ℕ, c * 2 ^ N - 3 ≤ C * lam ^ N := by
    intro N
    have h1 := trapped_ncard_ge hr hT N
    have h2 := trapped_ncard_le s t N
    have h3 := hW N
    have hq : (2 : ℝ) ^ N / (3 * 2 ^ k) - 1 ≤ ((2 ^ N / (3 * 2 ^ k) : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := 2 ^ N) (b := 3 * 2 ^ k) (by positivity)
      have hpos : (0 : ℝ) < 3 * 2 ^ k := by positivity
      rw [div_sub_one hpos.ne', div_le_iff₀ hpos]
      have : ((2 ^ N : ℕ) : ℝ) < ((2 ^ N / (3 * 2 ^ k) * (3 * 2 ^ k) + 3 * 2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at this
      linarith
    have h4 : ((2 ^ N / (3 * 2 ^ k) : ℕ) : ℝ) - 2 ≤
        ({g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard : ℝ) := by
      have : 2 ^ N / (3 * 2 ^ k) ≤ {g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard + 2 := by omega
      have : ((2 ^ N / (3 * 2 ^ k) : ℕ) : ℝ) ≤ ({g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard : ℝ) + 2 := by
        exact_mod_cast this
      linarith
    have h5 : ({g : ℕ | g < 2 ^ N ∧ TrappedFloor s t g}.ncard : ℝ) ≤
        ({a : Fin N → ℤ | AdmissibleWord s t N a}.ncard : ℝ) := by exact_mod_cast h2
    have : c * 2 ^ N = (2 : ℝ) ^ N / (3 * 2 ^ k) := by simp only [c]; ring
    linarith
  -- divide by 2^N and let N → ∞
  have hlim : Filter.Tendsto (fun N : ℕ => C * (lam / 2) ^ N + 3 * (1 / 2 : ℝ) ^ N)
      Filter.atTop (nhds (C * 0 + 3 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith)).const_mul C).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 3)
  simp only [mul_zero, add_zero] at hlim
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 c hc).exists
  have hb := hbound N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have e1 : C * (lam / 2) ^ N * 2 ^ N = C * lam ^ N := by rw [div_pow]; field_simp
  have e2 : 3 * (1 / 2 : ℝ) ^ N * 2 ^ N = 3 := by rw [div_pow, one_pow]; field_simp
  have : (C * (lam / 2) ^ N + 3 * (1 / 2) ^ N) * 2 ^ N < c * 2 ^ N :=
    mul_lt_mul_of_pos_right hN h2N
  rw [add_mul, e1, e2] at this
  linarith

/-- **Finite-memory barrier: no construction that works on a whole residue class mod `2^k` traps
an orbit in any arc of length at most `13/20`.**  In particular no finite-memory strategy, of any
game version, reaches Mahler's arc.  Flatto's `X^{log₂(3/2)}` count of Z-numbers is the
`[0, 1/2)` case of the counting step below; the rest is new.
PROVED 2026-10-06, as a corollary of `finiteMemory_barrier_two_thirds`.  The original certificate route:  Proof route:
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
theorem finiteMemory_barrier (s t : ℝ) (ht : t ≤ 13 / 20) (k r : ℕ) (hr : r < 2 ^ k) :
    ¬ TrapsResidueClass s t k r :=
  finiteMemory_barrier_two_thirds s t (by linarith) k r hr

/-- The memoryless corollary.  It extends `mahler_barrier` from length `1/2` to `13/20`. -/
theorem relaxed_barrier_13_20 (s t : ℝ) (ht : t ≤ 13 / 20) (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy s t l P := fun h =>
  finiteMemory_barrier s t ht 0 0 (by norm_num) (trapsResidueClass_of_relaxedStrategy (by linarith) h)

/-- **Mahler barrier: no memoryless relaxed strategy holds any arc of length at most `1/2`.**  In
particular none traps an orbit in Mahler's arc `[0, 1/2]`: a construction that treats every unseen
parity as adversarial cannot produce a Z-number.
PROVED 2026-10-06 as a corollary of `relaxed_barrier_13_20`.  Original proof route:
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
    ¬ RelaxedStrategy s t l P :=
  relaxed_barrier_13_20 s t (by linarith) l P

/-- Mahler's own arc. -/
theorem no_relaxedStrategy_mahler_arc (l : ℝ) (P : Set ℝ) : ¬ RelaxedStrategy 0 (1 / 2) l P :=
  mahler_barrier 0 (1 / 2) le_rfl l P

/-- **The finite-memory edge is exactly `2/3`** (stated here; `finiteMemoryEdgeIsTwoThirds` below).  No residue-class construction holds
an arc shorter than `2/3`, and arcs just past the AFS arc `{‖x‖ ≤ 1/3}` are held.  So the
counting obstruction is sharp at the best position.  At other positions the game needs
`0.73`–`0.90`, while the counting edge stays at `≈ 2/3` everywhere.
First half: PROVED (`finiteMemory_barrier_two_thirds`, 2026-10-06).  Second half: PROVED from the
closed arc (`relaxedStrategy_afs_closed`, `finiteMemory_min_arc_two_thirds`). -/
def FiniteMemoryEdgeIsTwoThirds : Prop :=
  (∀ s t : ℝ, t < 2 / 3 → ∀ k r : ℕ, r < 2 ^ k → ¬ TrapsResidueClass s t k r) ∧
  (∀ ε : ℝ, 0 < ε → TrapsResidueClass (2 / 3 - ε) (2 / 3 + 2 * ε) 0 0)

/-- The conjecture is now exactly its second half: arcs just past the AFS arc are held. -/
theorem finiteMemoryEdgeIsTwoThirds_iff :
    FiniteMemoryEdgeIsTwoThirds ↔
      ∀ ε : ℝ, 0 < ε → TrapsResidueClass (2 / 3 - ε) (2 / 3 + 2 * ε) 0 0 :=
  ⟨fun h => h.2, fun h => ⟨fun s t ht k r hr => finiteMemory_barrier_two_thirds s t ht k r hr, h⟩⟩

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

/-- A larger arc is held by the same strategy. -/
theorem RelaxedStrategy.mono {s t s' t' l : ℝ} {P : Set ℝ} (h : RelaxedStrategy s t l P)
    (hs : s' ≤ s) (ht : s + t ≤ s' + t') : RelaxedStrategy s' t' l P := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun a ha d hd => ?_⟩
  obtain ⟨u, h1, h2, ⟨k, hk1, hk2⟩, h4⟩ := h.2.2.2 a ha d hd
  exact ⟨u, h1, h2, ⟨k, by linarith, by linarith⟩, h4⟩

/-- **The game reaches the edge at the Akiyama–Frougny–Sakarovitch arc.**  A memoryless relaxed
strategy holds `[2/3 - 10⁻⁶, 4/3 + 10⁻⁶]`, i.e. `‖ξ (3/2)^n‖ ≤ 1/3 + 10⁻⁶`.  This works from every
integer part, a positive density, whereas AFS give countably many `ξ` with `‖ξ (3/2)^n‖ < 1/3`.
PROVED 2026-10-06 from `relaxedStrategy_afs_closed` (`RelaxedStrategy.mono`).  Originally: exact lattice post-fixed point `solve_vw` with width `l = 1000003/2000000`; exact
orbits from `m₀ = 1, 2, 3, 100` stay within `1/3 + 10⁻⁶`, `test_game_reaches_afs_arc`).  The game
fails on `[2/3, 4/3 + 10⁻⁶]` and on `[2/3 - 10⁻⁶, 4/3]`. -/
theorem relaxedStrategy_near_afs :
    ∃ l P, RelaxedStrategy (2 / 3 - 1 / 10 ^ 6) (2 / 3 + 2 / 10 ^ 6) l P :=
  ⟨_, _, relaxedStrategy_afs_closed.mono (by norm_num) (by norm_num)⟩

theorem trapsResidueClass_near_afs :
    TrapsResidueClass (2 / 3 - 1 / 10 ^ 6) (2 / 3 + 2 / 10 ^ 6) 0 0 := by
  obtain ⟨l, P, h⟩ := relaxedStrategy_near_afs
  exact trapsResidueClass_of_relaxedStrategy (by norm_num) h

/-! ### The `7/57` barrier: the component game, adversary side

`BarrierGood P l x y`: some window `[a + m, a + m + l]` of the strategy (`a ∈ P`, `m ∈ ℤ`) fits inside
`[x, y]`.  `barrier_step` is the domination step: whatever parity the adversary names, the strategy's
sub-window lies in one lift `[K + β, K + 1 - β]`, and the scaled component holds a new window.  The
node lemmas `barrierNode*` transcribe the adaptive adversary tree of `experiments/arc_barrier.py` on
the single `β`-piece `(7/57, 7126/58025)`; monotonicity in `β` (`RelaxedStrategy.mono`) covers every
larger `β`. -/

/-- Some strategy window `[a + m, a + m + l]` fits inside `[x, y]`. -/
def BarrierGood (P : Set ℝ) (l x y : ℝ) : Prop :=
  ∃ a ∈ P, ∃ m : ℤ, x ≤ a + m ∧ a + m + l ≤ y

theorem BarrierGood.mono {P : Set ℝ} {l x y x' y' : ℝ} (h : BarrierGood P l x y) (hx : x' ≤ x)
    (hy : y ≤ y') : BarrierGood P l x' y' := by
  obtain ⟨a, ha, m, h1, h2⟩ := h
  exact ⟨a, ha, m, by linarith, by linarith⟩

theorem BarrierGood.shift {P : Set ℝ} {l x y : ℝ} (h : BarrierGood P l x y) (n : ℤ) :
    BarrierGood P l (x + n) (y + n) := by
  obtain ⟨a, ha, m, h1, h2⟩ := h
  exact ⟨a, ha, m + n, by push_cast; linarith, by push_cast; linarith⟩

theorem BarrierGood.add_le {P : Set ℝ} {l x y : ℝ} (h : BarrierGood P l x y) : x + l ≤ y := by
  obtain ⟨a, ha, m, h1, h2⟩ := h
  linarith

theorem fract_half_mem (k : ℤ) : Int.fract ((k : ℝ) / 2) ∈ ({0, 1 / 2} : Set ℝ) := by
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [show ((2 * q : ℤ) : ℝ) / 2 = (q : ℝ) by push_cast; ring, Int.fract_intCast]
  · right
    show Int.fract _ = 1 / 2
    rw [Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, q, by push_cast; ring⟩

/-- **Domination step.**  The adversary names the relative parity `d`; the strategy's next window
sits inside `1.5 · C + d` for a component `C = [max x (K + β), min y (K + 1 - β)]`. -/
theorem barrier_step {β l x y : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hG : BarrierGood P l x y) (d : ℝ) (hd : d ∈ ({0, 1 / 2} : Set ℝ)) :
    ∃ K : ℤ, x < K + 1 - β ∧ (K : ℝ) + β < y ∧
      BarrierGood P l (3 / 2 * max x (K + β) + d) (3 / 2 * min y (K + 1 - β) + d) := by
  obtain ⟨a, ha, m, hx, hy⟩ := hG
  have hl := h.1
  have hd0 : Int.fract (3 * (m : ℝ) / 2 + d) ∈ ({0, 1 / 2} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · convert fract_half_mem (3 * m) using 2; push_cast; ring
    · convert fract_half_mem (3 * m + 1) using 2; push_cast; ring
  obtain ⟨u, hu1, hu2, ⟨k, hk1, hk2⟩, hu4⟩ := h.2.2.2 a ha _ hd0
  refine ⟨k + m, ?_, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith
  · set e := 3 * (m : ℝ) / 2 + d with he
    set c := 3 * u / 2 + Int.fract e with hc
    refine ⟨Int.fract c, hu4, ⌊c⌋ + ⌊e⌋, ?_, ?_⟩
    · have h1 : max x (((k + m : ℤ) : ℝ) + β) ≤ u + m := max_le (by linarith) (by push_cast; linarith)
      have h2 := Int.fract_add_floor c
      have h3 := Int.fract_add_floor e
      push_cast at h1 ⊢
      linarith
    · have h1 : u + m + 2 * l / 3 ≤ min y (((k + m : ℤ) : ℝ) + 1 - β) :=
        le_min (by linarith) (by push_cast; linarith)
      have h2 := Int.fract_add_floor c
      have h3 := Int.fract_add_floor e
      push_cast at h1 ⊢
      linarith

/-- **Runaway block** `(0, 1/2, 1/2)`: from `[x, R₀]`, `R₀ = 1 - 9β/4`, `x > 10/19`, the adversary
reaches `[27x/8 - 5/4, R₀]`. -/
theorem barrier_block {β l x : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) (hx : 10 / 19 < x)
    (hG : BarrierGood P l x (1 - 9 / 4 * β)) : BarrierGood P l (27 / 8 * x - 5 / 4) (1 - 9 / 4 * β) := by
  have hxR := hG.add_le
  have hl := h.1
  -- step 1, d = 0
  obtain ⟨K, h1, h2, hG1⟩ := barrier_step h hG 0 (by norm_num)
  have hK1 : 0 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -1 := by exact_mod_cast (by omega : K ≤ -1)
    linarith
  have hK2 : K ≤ 0 := by
    by_contra hc
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  have hK0 : ((K : ℤ) : ℝ) = 0 := by exact_mod_cast le_antisymm hK2 hK1
  simp only [hK0, zero_add] at hG1
  have hG1' : BarrierGood P l (3 / 2 * x) (3 / 2 * (1 - 9 / 4 * β)) :=
    hG1.mono (by linarith [le_max_left x β])
      (by linarith [min_le_left (1 - 9 / 4 * β) (1 - β)])
  -- step 2, d = 1/2
  obtain ⟨K, h1, h2, hG2⟩ := barrier_step h hG1' (1 / 2) (by norm_num)
  have hK1 : 0 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -1 := by exact_mod_cast (by omega : K ≤ -1)
    linarith
  have hK2 : K ≤ 0 := by
    by_contra hc
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  have hK0 : ((K : ℤ) : ℝ) = 0 := by exact_mod_cast le_antisymm hK2 hK1
  simp only [hK0, zero_add] at hG2
  have hG2' : BarrierGood P l (9 / 4 * x - 1 / 2) (1 - 3 / 2 * β) := by
    have := hG2.shift (-1)
    refine this.mono ?_ ?_
    · have := le_max_left (3 / 2 * x) β; push_cast at *; linarith
    · have := min_le_right (3 / 2 * (1 - 9 / 4 * β)) (1 - β); push_cast at *; linarith
  -- step 3, d = 1/2
  obtain ⟨K, h1, h2, hG3⟩ := barrier_step h hG2' (1 / 2) (by norm_num)
  have hK1 : 0 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -1 := by exact_mod_cast (by omega : K ≤ -1)
    linarith
  have hK2 : K ≤ 0 := by
    by_contra hc
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  have hK0 : ((K : ℤ) : ℝ) = 0 := by exact_mod_cast le_antisymm hK2 hK1
  simp only [hK0, zero_add] at hG3
  have := hG3.shift (-1)
  refine this.mono ?_ ?_
  · have := le_max_left (9 / 4 * x - 1 / 2) β; push_cast at *; linarith
  · have := min_le_left (1 - 3 / 2 * β) (1 - β); push_cast at *; linarith

/-- **Runaway**: `g x = 27x/8 - 5/4` repels from `10/19`, so `[x, R₀]` with `x > 10/19` dies. -/
theorem barrier_runaway {β l x : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) (hx : 10 / 19 < x)
    (hG : BarrierGood P l x (1 - 9 / 4 * β)) : False := by
  have hl := h.1
  have key : ∀ n : ℕ, ∀ x : ℝ, 1 ≤ (27 / 8 : ℝ) ^ n * (x - 10 / 19) →
      ¬ BarrierGood P l x (1 - 9 / 4 * β) := by
    intro n
    induction n with
    | zero =>
      intro x hx hG
      have := hG.add_le
      simp at hx
      linarith
    | succ n ih =>
      intro x hx hG
      have hp : (0 : ℝ) < (27 / 8) ^ n := by positivity
      have hx0 : 10 / 19 < x := by
        by_contra hc
        push_neg at hc
        have : (27 / 8 : ℝ) ^ (n + 1) * (x - 10 / 19) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        linarith
      refine ih (27 / 8 * x - 5 / 4) ?_ (barrier_block h hβ1 hβ2 hx0 hG)
      have e : (27 / 8 : ℝ) ^ n * (27 / 8 * x - 5 / 4 - 10 / 19) =
          (27 / 8 : ℝ) ^ (n + 1) * (x - 10 / 19) := by rw [pow_succ]; ring
      linarith
  have hδ : 0 < x - 10 / 19 := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (x - 10 / 19)) (by norm_num : (1 : ℝ) < 27 / 8)
  rw [div_lt_iff₀ hδ] at hn
  exact key n x hn.le hG

theorem barrierNode0 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) ((53 / 32 : ℝ) + (-243 / 32 : ℝ) * β) := by
  intro hG
  exact barrier_runaway h hβ1 hβ2 (by linarith) (hG.mono le_rfl (by linarith))

theorem barrierNode1 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((23 / 16 : ℝ) + (-81 / 16 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((23 / 16 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((23 / 16 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode0 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode2 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-31 / 64 : ℝ) + (729 / 64 : ℝ) * β) ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((-31 / 64 : ℝ) + (729 / 64 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-31 / 64 : ℝ) + (729 / 64 : ℝ) * β) (K + β)
  have m3 := min_le_left ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode1 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode3 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-21 / 32 : ℝ) + (243 / 32 : ℝ) * β) ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-21 / 32 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-21 / 32 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode2 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode4 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-7 / 16 : ℝ) + (81 / 16 : ℝ) * β) ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-7 / 16 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-7 / 16 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode3 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode5 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-13 / 32 : ℝ) + (243 / 32 : ℝ) * β) ((1 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  exact barrier_runaway h hβ1 hβ2 (by linarith) (hG.mono le_rfl (by linarith))

theorem barrierNode6 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 16 : ℝ) + (81 / 16 : ℝ) * β) ((1 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 16 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 16 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode5 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode7 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 4 : ℝ) + (27 / 8 : ℝ) * β) ((491 / 128 : ℝ) + (-6561 / 256 : ℝ) * β) := by
  intro hG
  exact barrier_runaway h hβ1 hβ2 (by linarith) (hG.mono le_rfl (by linarith))

theorem barrierNode8 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) ((185 / 64 : ℝ) + (-2187 / 128 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((185 / 64 : ℝ) + (-2187 / 128 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((185 / 64 : ℝ) + (-2187 / 128 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode7 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode9 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (3 / 2 : ℝ) * β) ((51 / 32 : ℝ) + (-729 / 64 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((51 / 32 : ℝ) + (-729 / 64 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((51 / 32 : ℝ) + (-729 / 64 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode8 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode10 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) ((33 / 16 : ℝ) + (-243 / 32 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m2 := le_max_right ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m3 := min_le_left ((33 / 16 : ℝ) + (-243 / 32 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((33 / 16 : ℝ) + (-243 / 32 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode6 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode9 h hβ1 hβ2 ((hG'.shift (-2)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode11 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) ((11 / 8 : ℝ) + (-81 / 16 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((11 / 8 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((11 / 8 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode10 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode12 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((5 / 4 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((5 / 4 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((5 / 4 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode11 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode13 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) ((3 / 2 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m2 := le_max_right ((3 / 8 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode4 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode12 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode14 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) ((1 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode13 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode15 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((5 / 4 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((5 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((5 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode14 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode16 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (243 / 32 : ℝ) * β) ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode15 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode17 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (81 / 16 : ℝ) * β) ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode16 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode15 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode18 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (27 / 8 : ℝ) * β) ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode17 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode15 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode19 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (9 / 4 : ℝ) * β) ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode18 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode15 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode20 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (3 / 2 : ℝ) * β) ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode19 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode15 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode21 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-315 / 128 : ℝ) + (6561 / 256 : ℝ) * β) ((9 / 8 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  exact barrier_runaway h hβ1 hβ2 (by linarith) (hG.mono le_rfl (by linarith))

theorem barrierNode22 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-105 / 64 : ℝ) + (2187 / 128 : ℝ) * β) ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-105 / 64 : ℝ) + (2187 / 128 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-105 / 64 : ℝ) + (2187 / 128 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode21 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode23 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-35 / 32 : ℝ) + (729 / 64 : ℝ) * β) ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-35 / 32 : ℝ) + (729 / 64 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-35 / 32 : ℝ) + (729 / 64 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode22 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode24 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-1 / 16 : ℝ) + (243 / 32 : ℝ) * β) ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((-1 / 16 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-1 / 16 : ℝ) + (243 / 32 : ℝ) * β) (K + β)
  have m3 := min_le_left ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode23 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode1 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode25 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-3 / 8 : ℝ) + (81 / 16 : ℝ) * β) ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-3 / 8 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-3 / 8 : ℝ) + (81 / 16 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode24 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode26 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-1 / 4 : ℝ) + (27 / 8 : ℝ) * β) ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-1 / 4 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-1 / 4 : ℝ) + (27 / 8 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode25 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode27 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((13 / 8 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode26 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode1 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode28 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((0 : ℝ) + (3 / 2 : ℝ) * β) ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (1 / 2 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((0 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((3 / 4 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode27 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode29 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((-1 / 4 : ℝ) + (9 / 4 : ℝ) * β) ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    linarith
  have m1 := le_max_left ((-1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m2 := le_max_right ((-1 / 4 : ℝ) + (9 / 4 : ℝ) * β) (K + β)
  have m3 := min_le_left ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((1 / 2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode28 h hβ1 hβ2 ((hG'.shift (0)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode30 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((2 : ℝ) + (-243 / 32 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((2 : ℝ) + (-243 / 32 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((2 : ℝ) + (-243 / 32 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode29 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith
  · push_cast at h1 h2; linarith

theorem barrierNode31 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((2 : ℝ) + (-81 / 16 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((2 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((2 : ℝ) + (-81 / 16 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode29 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode30 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode32 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((2 : ℝ) + (-27 / 8 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((2 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((2 : ℝ) + (-27 / 8 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode29 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode31 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode33 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((2 : ℝ) + (-9 / 4 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((2 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((2 : ℝ) + (-9 / 4 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode29 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode32 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith

theorem barrierNode34 {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) :
    ¬ BarrierGood P l ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) ((2 : ℝ) + (-3 / 2 : ℝ) * β) := by
  intro hG
  obtain ⟨K, h1, h2, hG'⟩ := barrier_step h hG (0 : ℝ) (by norm_num)
  have hK1 : -1 ≤ K := by
    by_contra hc
    have : (K : ℝ) ≤ -2 := by exact_mod_cast (by omega : K ≤ -2)
    linarith
  have hK2 : K ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ K := by exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have m1 := le_max_left ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m2 := le_max_right ((1 / 2 : ℝ) + (3 / 2 : ℝ) * β) (K + β)
  have m3 := min_le_left ((2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  have m4 := min_le_right ((2 : ℝ) + (-3 / 2 : ℝ) * β) (K + 1 - β)
  interval_cases K
  · push_cast at h1 h2; linarith
  · push_cast at *
    exact barrierNode29 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at *
    exact barrierNode33 h hβ1 hβ2 ((hG'.shift (-1)).mono (by push_cast; linarith) (by push_cast; linarith))
  · push_cast at h1 h2; linarith


/-- The barrier on the single piece `β ∈ (7/57, 7126/58025)`: the strategy's first window lies in
`1.5 · (arc + k)`, i.e. (by the parity of `k`) in one of the two root windows. -/
theorem barrier_core {β l : ℝ} {P : Set ℝ} (h : RelaxedStrategy β (1 - 2 * β) l P)
    (hβ1 : 7 / 57 < β) (hβ2 : β < 7126 / 58025) : False := by
  obtain ⟨a, ha⟩ := h.2.1
  obtain ⟨u, hu1, hu2, ⟨k, hk1, hk2⟩, hu4⟩ := h.2.2.2 a ha 0 (by simp)
  have hl := h.1
  set c := 3 * u / 2 + 0 with hc
  have hG : BarrierGood P l (3 / 2 * (k + β)) (3 / 2 * (k + 1 - β)) :=
    ⟨Int.fract c, hu4, ⌊c⌋, by linarith [Int.fract_add_floor c], by linarith [Int.fract_add_floor c]⟩
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' k
  · exact barrierNode20 h hβ1 hβ2 ((hG.shift (-(3 * q))).mono (by push_cast; linarith)
      (by push_cast; linarith))
  · exact barrierNode34 h hβ1 hβ2 ((hG.shift (-(3 * q + 1))).mono (by push_cast; linarith)
      (by push_cast; linarith))


/-- **Barrier: above `7/57` no memoryless relaxed strategy exists.**  Treating each parity bit as
adversarial caps the construction at `7/57`.
PROVED 2026-10-06 (`barrier_core`: `barrier_step` domination, 35 node lemmas `barrierNode*` on the piece `(7/57, 7126/58025)`, `barrier_runaway`; larger `β` by `RelaxedStrategy.mono`).  Original route:
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
  intro h
  set c : ℝ := (7 / 57 + 7126 / 58025) / 2
  have h0 : RelaxedStrategy (min β c) (1 - 2 * min β c) l P :=
    h.mono (min_le_left _ _) (by linarith [min_le_left β c])
  exact barrier_core h0 (lt_min hβ (by norm_num [c])) (lt_of_le_of_lt (min_le_right _ _) (by norm_num [c]))

/-- **Above the edge, no memoryless relaxed strategy.**  At `β = 13/100` (arc `[0.13, 0.87]`) no
width and no state set win.
PROVED 2026-10-06 as a corollary of `relaxed_barrier` (`13/100 > 7/57`).  Original route: a relaxed strategy is dominated by the component game,
where the constructor keeps a whole component of `W ∩ (arc lifts)` (bigger windows dominate) and
starts from the full arc.  The exact minimax `experiments/arc_minimax.py depth 13/100 1 30` forces it
out at depth 15.  A proof transcribes that finite refutation tree, rational endpoints throughout. -/
theorem not_relaxedStrategy_13_100 (l : ℝ) (P : Set ℝ) :
    ¬ RelaxedStrategy (13 / 100) (1 - 2 * (13 / 100)) l P :=
  relaxed_barrier (13 / 100) (by norm_num) (by norm_num) l P

/-- **Every positive integer part traps the closed AFS arc**: a memoryless construction holds
`{‖x‖ ≤ 1/3}` from every starting floor.  (The orbit-level fact is essentially Akiyama-Frougny-
Sakarovitch 2008; the point here is that it needs no memory, so the `2/3` edge is attained.) -/
theorem trapsResidueClass_afs_closed : TrapsResidueClass (2 / 3) (2 / 3) 0 0 :=
  trapsResidueClass_of_relaxedStrategy (by norm_num) relaxedStrategy_afs_closed

/-- **Theorem: the shortest arc any finite-memory construction holds has length exactly `2/3`,
and the minimum is attained** (at the AFS arc).  First half `finiteMemory_barrier_two_thirds`,
second half `trapsResidueClass_afs_closed`. -/
theorem finiteMemory_min_arc_two_thirds :
    (∀ s t : ℝ, t < 2 / 3 → ∀ k r : ℕ, r < 2 ^ k → ¬ TrapsResidueClass s t k r) ∧
      TrapsResidueClass (2 / 3) (2 / 3) 0 0 :=
  ⟨fun s t ht k r hr => finiteMemory_barrier_two_thirds s t ht k r hr, trapsResidueClass_afs_closed⟩

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

/-- **Conjecture: the AFS arc is the unique minimal arc.**  An orbit `{ξ(3/2)^n}` fits in an arc of
length `≤ 2/3` only if that arc is `{‖x‖ ≤ 1/3}` itself.  Strictly stronger than
`StrongMahlerConjecture` (`afsArcIsUniqueMinimal_strongMahler`).
Confidence 35% (the critical case is delicate; the heuristic says each integer part dies with
probability 1, but there are infinitely many of them).  Evidence (`arc_survival.py profile S 2/3 10 400`,
every integer part below `2^10`, depth 400):
* At 18 positions, only `s = 2/3` keeps every integer part alive.
* At generic positions the survivors fit a critical branching process,
  `S(N)/S(0) ≈ 1/(1 + c N)`: `1/S − 1` doubles with `N` (`s = 0`: 1.66, 3.49, 7.45, 13.2 at
  `N = 50, 100, 200, 400`), with `c ≈ 0.02`–`0.04`.
* `c(s) → 0` as `s → 2/3`: `0.0091` at `7/10`, `0.0057` at `19/30`, `0.002` at `13/20`, `0.0007` at `61/90`.
  So decay slows near the AFS arc, but no position plateaus.

Variance-zero alignment is what lets the AFS arc survive; a critical process with positive variance
dies. -/
def AfsArcIsUniqueMinimal : Prop :=
  ∀ s t : ℝ, t ≤ 2 / 3 → (∃ ξ : ℝ, 0 < ξ ∧
    ∀ n : ℕ, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x) →
    t = 2 / 3 ∧ ∃ k : ℤ, s = 2 / 3 + k

theorem afsArcIsUniqueMinimal_strongMahler (h : AfsArcIsUniqueMinimal) : StrongMahlerConjecture :=
  fun s t ht hξ => absurd (h s t ht.le hξ).1 ht.ne

/-- The strong conjecture implies Mahler's: there are no Z-numbers. -/
theorem strongMahler_no_zNumber (h : StrongMahlerConjecture) :
    ¬ ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2 := by
  rintro ⟨ξ, hξ, hz⟩
  exact h 0 (1 / 2) (by norm_num) ⟨ξ, hξ, fun n =>
    ⟨Int.fract (ξ * (3 / 2) ^ n), ⟨Int.fract_nonneg _, by linarith [hz n]⟩,
      (Int.fract_fract _).symm⟩⟩

/-! ### Near the AFS arc: the endpoint-error recursion

Shift the AFS arc by `δ`: lifts `[k - 1/3 + δ, k + 1/3 + δ]`.  A piece anchored at an integer `k`
is `k + [e_L, 1/3 + e_R]` (type 0) or `k + [2/3 + e_L, 1 + e_R]` (type 1); at `δ = 0`,
`e_L = e_R = 0` is `relaxedStrategy_afs_closed`.  Multiplying by `3/2` and cutting by the lifts:

* anchor parity `0`: `(e_L, e_R) ↦ (3e_L/2, δ)`, type 0;
* anchor parity `1`: `(e_L, e_R) ↦ (δ, 3e_R/2)`, type 1;
* the new anchor is `(3k - p)/2 + (previous parity)`.

This is exact while `3e_L/2 - δ` and `3e_R/2 - δ` stay in the windows checked by
`arc_survival.py` (`test_endpoint_error_recursion_is_exact`).  So an error grows by `3/2` along a run
of equal parities and resets to `δ` when the parity changes.  A run of length `R` costs `(3/2)^R |δ|`.
The anchor parities of `g < 2^N` run through every string in `{0,1}^N` exactly once (a triangular
bijection, as for `finiteMemory_barrier`). -/

/-- `g` is the integer part of some `ξ` whose first `N + 1` orbit points lie in the arc. -/
def TrapsToDepth (s t : ℝ) (N g : ℕ) : Prop :=
  ∃ ξ : ℝ, ⌊ξ⌋ = (g : ℤ) ∧
    ∀ n ≤ N, ∃ x ∈ Set.Icc s (s + t), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x

/-- No run of equal letters longer than `R` in a word of length `N`. -/
def NoRunLonger (R N : ℕ) (w : Fin N → Bool) : Prop :=
  ∀ i : ℕ, ∀ h : i + R < N, ∃ k, ∃ hk : k < R, w ⟨i + k, by omega⟩ ≠ w ⟨i + k + 1, by omega⟩

/-- Prefixes of run-bounded words are run-bounded. -/
theorem noRunLonger_prefix {R N M : ℕ} (hMN : M ≤ N) {v : Fin N → Bool} (h : NoRunLonger R N v) :
    NoRunLonger R M (fun j : Fin M => v ⟨j, by omega⟩) := by
  intro i hi
  obtain ⟨k, hk, hne⟩ := h i (by omega)
  exact ⟨k, hk, hne⟩

theorem noRunLonger_short {R N : ℕ} (hN : N ≤ R) (w : Fin N → Bool) : NoRunLonger R N w := by
  intro i h; exfalso; omega

/-- The bad extensions: good prefix, bad word. -/
def badExt (R N : ℕ) : Set (Fin (N + 1) → Bool) :=
  {v | NoRunLonger R N (fun j : Fin N => v ⟨j, by omega⟩) ∧ ¬ NoRunLonger R (N + 1) v}

theorem badExt_window {R N : ℕ} {v : Fin (N + 1) → Bool} (hv : v ∈ badExt R N) :
    R ≤ N ∧ ∀ k (hk : k ≤ R) (h : N - R + k < N + 1), v ⟨N - R + k, h⟩ = v ⟨N - R, by omega⟩ := by
  obtain ⟨hi, hb⟩ := hv
  simp only [NoRunLonger, not_forall, not_exists, not_not] at hb
  obtain ⟨i, hiR, hall⟩ := hb
  have hiN : i + R = N := by
    by_contra hne
    obtain ⟨k, hk, hne'⟩ := hi i (by omega)
    exact hne' (hall k hk)
  refine ⟨by omega, fun k hk _ => ?_⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have := hall k (by omega)
    rw [← ih (by omega) (by omega)]
    have e1 : (⟨N - R + (k + 1), by omega⟩ : Fin (N + 1)) = ⟨i + k + 1, by omega⟩ := Fin.ext (by simp; omega)
    have e2 : (⟨N - R + k, by omega⟩ : Fin (N + 1)) = ⟨i + k, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1, e2]; exact this.symm

theorem badExt_eq {R N : ℕ} {v : Fin (N + 1) → Bool} (hv : v ∈ badExt R N) (j : ℕ)
    (hj1 : N - R ≤ j) (hj2 : j ≤ N) : v ⟨j, by omega⟩ = v ⟨N - R, by omega⟩ := by
  obtain ⟨hRN, hw⟩ := badExt_window hv
  have := hw (j - (N - R)) (by omega) (by omega)
  rw [← this]; exact congrArg v (Fin.ext (by simp; omega))

noncomputable def runCount (R N : ℕ) : ℕ := {w : Fin N → Bool | NoRunLonger R N w}.ncard

theorem runCount_short {R N : ℕ} (hN : N ≤ R) : runCount R N = 2 ^ N := by
  unfold runCount
  rw [show {w : Fin N → Bool | NoRunLonger R N w} = Set.univ from
    Set.eq_univ_of_forall (noRunLonger_short hN), Set.ncard_univ, Nat.card_fun]
  simp

theorem two_mul_runCount_le (R N : ℕ) :
    2 * runCount R N ≤ runCount R (N + 1) + (badExt R N).ncard := by
  set T : Set (Fin (N + 1) → Bool) := {v | NoRunLonger R N (fun j : Fin N => v ⟨j, by omega⟩)}
  have hT : T = (fun p : (Fin N → Bool) × Bool => Fin.snoc p.1 p.2) ''
      ({w : Fin N → Bool | NoRunLonger R N w} ×ˢ Set.univ) := by
    ext v
    constructor
    · intro hv
      refine ⟨(Fin.init v, v (Fin.last N)), ⟨hv, trivial⟩, Fin.snoc_init_self v⟩
    · rintro ⟨⟨w, b⟩, ⟨hw, -⟩, rfl⟩
      simpa [T, Fin.snoc] using hw
  have hTc : T.ncard = 2 * runCount R N := by
    rw [hT, Set.ncard_image_of_injective _ (fun p q h => by
      simpa [Prod.ext_iff] using (Fin.snoc_injective2 h)), Set.ncard_prod, Set.ncard_univ]
    simp [runCount, mul_comm]
  have hsub : T ⊆ {w : Fin (N + 1) → Bool | NoRunLonger R (N + 1) w} ∪ badExt R N := by
    intro v hv
    by_cases h : NoRunLonger R (N + 1) v
    · exact Or.inl h
    · exact Or.inr ⟨hv, h⟩
  rw [← hTc]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)

theorem badExt_le {R N : ℕ} (hRN : R < N) : (badExt R N).ncard ≤ runCount R (N - R) := by
  refine Set.ncard_le_ncard_of_injOn (fun v : Fin (N + 1) → Bool => fun j : Fin (N - R) => v ⟨j, by omega⟩)
    (fun v hv => ?_) (fun v hv v' hv' he => ?_) (Set.toFinite _)
  · have := noRunLonger_prefix (M := N - R) (by omega) hv.1
    exact this
  · obtain ⟨-, hw⟩ := badExt_window hv
    obtain ⟨-, hw'⟩ := badExt_window hv'
    have hpre : ∀ j (hj : j < N - R), v ⟨j, by omega⟩ = v' ⟨j, by omega⟩ := fun j hj =>
      congrFun he ⟨j, hj⟩
    have flip : ∀ u : Fin (N + 1) → Bool, u ∈ badExt R N →
        u ⟨N - R, by omega⟩ ≠ u ⟨N - R - 1, by omega⟩ := by
      intro u hu heq
      obtain ⟨k, hk, hne⟩ := hu.1 (N - R - 1) (by omega)
      apply hne
      simp only
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [show (⟨N - R - 1 + 0, by omega⟩ : Fin (N + 1)) = ⟨N - R - 1, by omega⟩ from
          Fin.ext (by simp), badExt_eq hu (N - R - 1 + 0 + 1) (by omega) (by omega), heq]
      · rw [badExt_eq hu (N - R - 1 + k) (by omega) (by omega),
          badExt_eq hu (N - R - 1 + k + 1) (by omega) (by omega)]
    have h0 : v ⟨N - R, by omega⟩ = v' ⟨N - R, by omega⟩ := by
      have f1 := flip v hv
      have f2 := flip v' hv'
      have hp := hpre (N - R - 1) (by omega)
      revert f1 f2 hp
      cases v ⟨N - R, by omega⟩ <;> cases v' ⟨N - R, by omega⟩ <;>
        cases v ⟨N - R - 1, by omega⟩ <;> cases v' ⟨N - R - 1, by omega⟩ <;> simp
    funext j
    by_cases hj : (j : ℕ) < N - R
    · exact hpre j hj
    · rw [show j = ⟨(j : ℕ), by omega⟩ from rfl, badExt_eq hv j (by omega) (by omega),
        badExt_eq hv' j (by omega) (by omega), h0]

theorem badExt_R_le (R : ℕ) : (badExt R R).ncard ≤ 2 := by
  have := Set.ncard_le_ncard_of_injOn (fun v : Fin (R + 1) → Bool => v 0)
    (s := badExt R R) (t := Set.univ) (fun _ _ => trivial) (fun v hv v' hv' he => ?_) (Set.toFinite _)
  · simpa [Set.ncard_univ] using this
  · obtain ⟨-, hw⟩ := badExt_window hv
    obtain ⟨-, hw'⟩ := badExt_window hv'
    funext j
    have a := hw j (by omega) (by omega)
    have b := hw' j (by omega) (by omega)
    simp only [Nat.sub_self, zero_add] at a b
    have he' : v ⟨0, by omega⟩ = v' ⟨0, by omega⟩ := he
    rw [show j = ⟨(j : ℕ), by omega⟩ from rfl, a, b, he']

theorem two_mul_le_two_pow (R : ℕ) (hR : 1 ≤ R) : 2 * R ≤ 2 ^ R := by
  induction R with
  | zero => omega
  | succ R ih =>
    rcases Nat.eq_zero_or_pos R with rfl | h
    · norm_num
    · have := ih h; rw [pow_succ]; omega

/-- Words with bounded runs are not rare: at least `2^N (1 - 2^{-R})^N` of them.  PROVED 2026-10-06
(ratio induction `c_{N+1} ≥ 2 c_N - c_{N-R}`, `badExt_le`); originally confidence 85%
(checked for `R ≤ 11`, `N < 200` in `test_run_bounded_count_bound`).  Proof sketch: the count obeys
the `R`-bonacci recursion, and its growth rate `φ_R ≥ 2 - 2^{1-R}`, i.e. `φ_R/2 ≥ 1 - 2^{-R}`;
induct on `N` with the ratio of consecutive counts. -/
theorem run_bounded_count_ge (R N : ℕ) (hR : 1 ≤ R) :
    (2 : ℝ) ^ N * (1 - (1 / 2) ^ R) ^ N ≤ Nat.card {w : Fin N → Bool // NoRunLonger R N w} := by
  rw [show Nat.card {w : Fin N → Bool // NoRunLonger R N w} = runCount R N from
    Nat.card_coe_set_eq _]
  set ε : ℝ := (1 / 2) ^ R with hε
  set lam : ℝ := 2 * (1 - ε) with hlam
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by
    rw [hε]; exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans (by norm_num)
  have hlam0 : 0 ≤ lam := by rw [hlam]; linarith
  have hlam2 : lam ≤ 2 := by rw [hlam]; linarith
  -- (1 - ε)^R ≥ 1/2
  have hbern : (1 / 2 : ℝ) ≤ (1 - ε) ^ R := by
    have hb := one_add_mul_le_pow (a := -ε) (by linarith) R
    rw [← sub_eq_add_neg] at hb
    have h2R : (2 * R : ℝ) ≤ 2 ^ R := by exact_mod_cast two_mul_le_two_pow R hR
    have hRε : (R : ℝ) * ε ≤ 1 / 2 := by
      rw [hε, one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]; linarith
    linarith
  -- lam^R * ε * 2 ≥ 1 ... i.e. lam^R (2 - lam) ≥ 1
  have hkey : 1 ≤ lam ^ R * (2 - lam) := by
    have e : lam ^ R * (2 - lam) = 2 * ((1 - ε) ^ R * (2 ^ R * ε)) := by
      rw [hlam, mul_pow]; ring
    have e2 : (2 : ℝ) ^ R * ε = 1 := by rw [hε, ← mul_pow]; norm_num
    rw [e, e2]; linarith
  -- ratio step
  have step : ∀ N, lam * runCount R N ≤ runCount R (N + 1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases lt_trichotomy N R with hlt | heq | hgt
      · rw [runCount_short hlt.le, runCount_short (by omega)]
        push_cast; rw [pow_succ]
        have : (0 : ℝ) ≤ 2 ^ N := by positivity
        nlinarith
      · subst heq
        have h1 := two_mul_runCount_le N N
        have h2 := badExt_R_le N
        rw [runCount_short le_rfl] at h1 ⊢
        have h3 : (2 : ℝ) * 2 ^ N - 2 ≤ runCount N (N + 1) := by
          have : 2 * 2 ^ N ≤ runCount N (N + 1) + 2 := by omega
          have : ((2 * 2 ^ N : ℕ) : ℝ) ≤ ((runCount N (N + 1) + 2 : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this; linarith
        have : lam * ((2 ^ N : ℕ) : ℝ) = 2 * 2 ^ N - 2 := by
          rw [hlam]; push_cast
          have : (2 : ℝ) ^ N * ε = 1 := by rw [hε, ← mul_pow]; norm_num
          linear_combination (-2) * this
        rw [this]; exact h3
      · -- iterate the ratio back R steps
        have back : ∀ j, j ≤ R → lam ^ j * runCount R (N - j) ≤ runCount R N := by
          intro j
          induction j with
          | zero => intro _; simp
          | succ j ihj =>
            intro hj
            have hstep := ih (N - (j + 1)) (by omega)
            rw [show N - (j + 1) + 1 = N - j by omega] at hstep
            have := ihj (by omega)
            rw [pow_succ]
            have hp : 0 ≤ lam ^ j := pow_nonneg hlam0 _
            nlinarith
        have hb := back R le_rfl
        have h1 := two_mul_runCount_le R N
        have h2 := badExt_le hgt
        have h3 : (2 : ℝ) * runCount R N - runCount R (N - R) ≤ runCount R (N + 1) := by
          have : 2 * runCount R N ≤ runCount R (N + 1) + runCount R (N - R) := by omega
          have : ((2 * runCount R N : ℕ) : ℝ) ≤ ((runCount R (N + 1) + runCount R (N - R) : ℕ) : ℝ) := by
            exact_mod_cast this
          push_cast at this; linarith
        -- lam c_N ≤ 2 c_N - c_{N-R}  ⇐  c_{N-R} ≤ (2 - lam) c_N  ⇐ lam^R (2 - lam) ≥ 1
        have hc0 : (0 : ℝ) ≤ runCount R (N - R) := Nat.cast_nonneg _
        have : (runCount R (N - R) : ℝ) ≤ (2 - lam) * runCount R N := by
          have hl : 0 ≤ 2 - lam := by linarith
          calc (runCount R (N - R) : ℝ) ≤ lam ^ R * (2 - lam) * runCount R (N - R) := by nlinarith
            _ = (2 - lam) * (lam ^ R * runCount R (N - R)) := by ring
            _ ≤ (2 - lam) * runCount R N := mul_le_mul_of_nonneg_left hb hl
        linarith
  have hfin : ∀ N, lam ^ N ≤ runCount R N := by
    intro N
    induction N with
    | zero => rw [runCount_short (by omega)]; simp
    | succ N ih =>
      rw [pow_succ]
      have := step N
      nlinarith
  calc (2 : ℝ) ^ N * (1 - ε) ^ N = lam ^ N := by rw [hlam, mul_pow]
    _ ≤ _ := hfin N

/-- One step of the endpoint-error recursion (letter = anchor parity). -/
noncomputable def afsErrStep (δ : ℝ) (e : ℝ × ℝ) (b : Bool) : ℝ × ℝ :=
  if b then (δ, 3 / 2 * e.2) else (3 / 2 * e.1, δ)

/-- The step is exact (one piece, of the same shape) under these conditions on the errors. -/
def AfsStepOk (δ : ℝ) (e : ℝ × ℝ) (b : Bool) : Prop :=
  if b then -1 / 6 < 3 / 2 * e.1 - δ ∧ 3 / 2 * e.1 - δ ≤ 1 / 6 ∧
      -1 / 3 ≤ 3 / 2 * e.2 - δ ∧ 3 / 2 * e.2 - δ ≤ 1 / 3
  else -1 / 3 ≤ 3 / 2 * e.1 - δ ∧ 3 / 2 * e.1 - δ ≤ 1 / 3 ∧
      -1 / 6 ≤ 3 / 2 * e.2 - δ ∧ 3 / 2 * e.2 - δ < 1 / 6

/-- Errors after reading the first `n` letters, from the start piece `g + [0, 1/3 + δ]`. -/
noncomputable def afsErr (δ : ℝ) {N : ℕ} (w : Fin N → Bool) : ℕ → ℝ × ℝ
  | 0 => (0, δ)
  | n + 1 => if h : n < N then afsErrStep δ (afsErr δ w n) (w ⟨n, h⟩) else afsErr δ w n

/-- The AFS-shaped piece survives the whole word unbroken. -/
def AfsUnbroken (δ : ℝ) (N : ℕ) (w : Fin N → Bool) : Prop :=
  ∀ n (h : n < N), AfsStepOk δ (afsErr δ w n) (w ⟨n, h⟩)

/-- Length of the run of `b`s ending just before position `n`. -/
def trail {N : ℕ} (w : Fin N → Bool) (b : Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if h : n < N then (if w ⟨n, h⟩ = b then trail w b n + 1 else 0) else 0

theorem trail_spec {N : ℕ} (w : Fin N → Bool) (b : Bool) : ∀ n, n ≤ N →
    trail w b n ≤ n ∧ ∀ k (hk : k < trail w b n) (h : n - 1 - k < N), w ⟨n - 1 - k, h⟩ = b := by
  intro n
  induction n with
  | zero => intro _; simp [trail]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hnN : n < N := by omega
    by_cases hb : w ⟨n, hnN⟩ = b
    · have e : trail w b (n + 1) = trail w b n + 1 := by simp [trail, hnN, hb]
      refine ⟨by omega, fun k hk _ => ?_⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hb
      · have := h2 (k - 1) (by omega) (by omega)
        rw [← this]; congr 1; ext; simp; omega
    · have e : trail w b (n + 1) = 0 := by simp [trail, hnN, hb]
      refine ⟨by omega, fun k hk _ => by omega⟩

theorem trail_le {R N : ℕ} {w : Fin N → Bool} (hw : NoRunLonger R N w) (b : Bool) (n : ℕ)
    (hn : n ≤ N) : trail w b n ≤ R := by
  obtain ⟨h1, h2⟩ := trail_spec w b n hn
  by_contra hlt
  push_neg at hlt
  obtain ⟨k, hk, hne⟩ := hw (n - (R + 1)) (by omega)
  apply hne
  have a1 := h2 (R - k) (by omega) (by omega)
  have a2 := h2 (R - k - 1) (by omega) (by omega)
  rw [show (⟨n - (R + 1) + k, by omega⟩ : Fin N) = ⟨n - 1 - (R - k), by omega⟩ from
      Fin.ext (by simp; omega),
    show (⟨n - (R + 1) + k + 1, by omega⟩ : Fin N) = ⟨n - 1 - (R - k - 1), by omega⟩ from
      Fin.ext (by simp; omega), a1, a2]

theorem afsErr_bound (δ : ℝ) {N : ℕ} (w : Fin N → Bool) : ∀ n, n ≤ N →
    |(afsErr δ w n).1| ≤ (3 / 2) ^ trail w false n * |δ| ∧
      |(afsErr δ w n).2| ≤ (3 / 2) ^ trail w true n * |δ| := by
  intro n
  induction n with
  | zero => intro _; simp [afsErr, trail]
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [afsErr, dif_pos hnN, afsErrStep, trail]
    cases hb : w ⟨n, hnN⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, by simp⟩
      rw [abs_mul, pow_succ]; norm_num
      nlinarith [abs_nonneg δ]
    · simp only [↓reduceIte, Bool.true_eq_false]
      refine ⟨by simp, ?_⟩
      rw [abs_mul, pow_succ]; norm_num
      nlinarith [abs_nonneg δ]

/-- Short runs never break the piece.  PROVED 2026-10-06 (`afsErr_bound`, `trail_le`) (the core of `near_afs_density`).  Proof:
each coordinate is `0`, `δ` or `δ (3/2)^j` with `j` at most the length of the run it is growing in.
So `|3e/2 - δ| ≤ (3/2)^(R+1) |δ| + |δ| < 1/6` at every step. -/
theorem afsUnbroken_of_noRunLonger (δ : ℝ) (R N : ℕ) (hR : (3 / 2) ^ (R + 1) * |δ| + |δ| < 1 / 6)
    (w : Fin N → Bool) (hw : NoRunLonger R N w) : AfsUnbroken δ N w := by
  intro n hn
  obtain ⟨h1, h2⟩ := afsErr_bound δ w n hn.le
  have t1 := trail_le hw false n hn.le
  have t2 := trail_le hw true n hn.le
  have p1 : (3 / 2 : ℝ) ^ trail w false n ≤ (3 / 2) ^ R := pow_le_pow_right₀ (by norm_num) t1
  have p2 : (3 / 2 : ℝ) ^ trail w true n ≤ (3 / 2) ^ R := pow_le_pow_right₀ (by norm_num) t2
  have hd := abs_nonneg δ
  have b1 : |(afsErr δ w n).1| ≤ (3 / 2) ^ R * |δ| := h1.trans (by nlinarith)
  have b2 : |(afsErr δ w n).2| ≤ (3 / 2) ^ R * |δ| := h2.trans (by nlinarith)
  rw [pow_succ] at hR
  have c1 := abs_le.1 b1
  have c2 := abs_le.1 b2
  have d := abs_le.1 (le_refl |δ|)
  unfold AfsStepOk
  split_ifs <;> refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem afsErr_succ (δ : ℝ) {N : ℕ} (w : Fin N → Bool) (n : ℕ) (h : n < N) :
    afsErr δ w (n + 1) = afsErrStep δ (afsErr δ w n) (w ⟨n, h⟩) := by
  simp [afsErr, h]

/-- A flip followed by `m` equal letters always breaks the piece, once
`|δ| ((3/2)^m - 1) > 1/3`.  PROVED 2026-10-06.  Proof: reading `w b` resets the coordinate that the run
then grows to `δ`.  At the `j`-th letter of the run the check reads `3e/2 - δ = δ((3/2)^j - 1)`, and
the continuation window is `[-1/3, 1/3]`. -/
theorem not_afsUnbroken_of_long_run (δ : ℝ) (m N : ℕ) (hm : 1 / 3 < |δ| * ((3 / 2) ^ m - 1))
    (hm1 : 1 ≤ m) (w : Fin N → Bool) (b : ℕ) (hb : b + m < N) (hflip : w ⟨b, by omega⟩ ≠ w ⟨b + 1, by omega⟩)
    (hrun : ∀ j (hj : 1 ≤ j ∧ j ≤ m), w ⟨b + j, by omega⟩ = w ⟨b + 1, by omega⟩) :
    ¬ AfsUnbroken δ N w := by
  intro hU
  have hpow : (1 : ℝ) ≤ (3 / 2) ^ m := one_le_pow₀ (by norm_num)
  have habs : |δ * ((3 / 2) ^ m - 1)| = |δ| * ((3 / 2) ^ m - 1) := by
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (3 / 2) ^ m - 1 by linarith)]
  have hok := hU (b + m) hb
  rw [hrun m ⟨hm1, le_rfl⟩] at hok
  cases hy : w ⟨b + 1, by omega⟩
  · -- run of `false`: the first coordinate grows
    have hx : w ⟨b, by omega⟩ = true := by
      rw [hy] at hflip; simpa using hflip
    have grow : ∀ j, 1 ≤ j → j ≤ m → (afsErr δ w (b + j)).1 = δ * (3 / 2) ^ (j - 1) := by
      intro j hj1 hjm
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [afsErr_succ δ w b (by omega), hx]; simp [afsErrStep]
        · rw [show b + (j + 1) = b + j + 1 by ring, afsErr_succ δ w (b + j) (by omega),
            hrun j ⟨hj0, by omega⟩, hy]
          simp only [afsErrStep, Bool.false_eq_true, ↓reduceIte]
          rw [ih hj0 (by omega), show j + 1 - 1 = (j - 1) + 1 by omega, pow_succ]; ring
    rw [hy] at hok
    simp only [AfsStepOk, Bool.false_eq_true, ↓reduceIte] at hok
    rw [grow m hm1 le_rfl] at hok
    have e : 3 / 2 * (δ * (3 / 2) ^ (m - 1)) - δ = δ * ((3 / 2) ^ m - 1) := by
      rw [show m = (m - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
    rw [e] at hok
    have := abs_le.2 ⟨by linarith [hok.1], hok.2.1⟩
    linarith
  · have hx : w ⟨b, by omega⟩ = false := by
      rw [hy] at hflip; simpa using hflip
    have grow : ∀ j, 1 ≤ j → j ≤ m → (afsErr δ w (b + j)).2 = δ * (3 / 2) ^ (j - 1) := by
      intro j hj1 hjm
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [afsErr_succ δ w b (by omega), hx]; simp [afsErrStep]
        · rw [show b + (j + 1) = b + j + 1 by ring, afsErr_succ δ w (b + j) (by omega),
            hrun j ⟨hj0, by omega⟩, hy]
          simp only [afsErrStep, ↓reduceIte]
          rw [ih hj0 (by omega), show j + 1 - 1 = (j - 1) + 1 by omega, pow_succ]; ring
    rw [hy] at hok
    simp only [AfsStepOk, ↓reduceIte] at hok
    rw [grow m hm1 le_rfl] at hok
    have e : 3 / 2 * (δ * (3 / 2) ^ (m - 1)) - δ = δ * ((3 / 2) ^ m - 1) := by
      rw [show m = (m - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
    rw [e] at hok
    have := abs_le.2 ⟨by linarith [hok.2.2.1], hok.2.2.2⟩
    linarith

/-- The breaking pattern at `b`: a flip, then `m` equal letters. -/
def BreakAt (m N : ℕ) (w : Fin N → Bool) (b : ℕ) (hb : b + m < N) : Prop :=
  w ⟨b, by omega⟩ ≠ w ⟨b + m, hb⟩ ∧ ∀ j (hj : 1 ≤ j ∧ j ≤ m), w ⟨b + j, by omega⟩ = w ⟨b + m, hb⟩

/-- Words with no breaking pattern at any block start `b ≡ 0 mod (m + 1)`. -/
def avoidSet (m N : ℕ) : Set (Fin N → Bool) :=
  {w | ∀ b (hb : b + m < N), (m + 1) ∣ b → ¬ BreakAt m N w b hb}

def goodBlock (m : ℕ) : Set (Fin (m + 1) → Bool) :=
  {u | ¬ BreakAt m (m + 1) u 0 (by omega)}

theorem goodBlock_ncard (m : ℕ) (hm : 1 ≤ m) : (goodBlock m).ncard ≤ 2 ^ (m + 1) - 2 := by
  let p : Bool → Fin (m + 1) → Bool := fun x j => if (j : ℕ) = 0 then x else !x
  have hp : ∀ x, p x ∈ (goodBlock m)ᶜ := by
    intro x
    simp only [goodBlock, Set.mem_compl_iff, Set.mem_setOf_eq, not_not, BreakAt]
    refine ⟨by cases x <;> simp [p] <;> omega, fun j hj => ?_⟩
    simp only [p, Fin.val_mk]; rw [if_neg (by omega), if_neg (by omega)]
  have hne : p true ≠ p false := by
    intro h; have := congrFun h 0; simp [p] at this
  have h2 : 2 ≤ (goodBlock m)ᶜ.ncard := by
    have : ({p true, p false} : Set _) ⊆ (goodBlock m)ᶜ := by
      intro u hu; rcases hu with rfl | rfl <;> exact hp _
    have := Set.ncard_le_ncard this (Set.toFinite _)
    rwa [Set.ncard_pair hne] at this
  have htot := Set.ncard_add_ncard_compl (goodBlock m)
  rw [Nat.card_fun] at htot
  simp at htot
  omega

theorem avoidSet_short {m N : ℕ} (hN : N < m + 1) : (avoidSet m N).ncard ≤ 2 ^ N := by
  calc (avoidSet m N).ncard ≤ (Set.univ : Set (Fin N → Bool)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = 2 ^ N := by rw [Set.ncard_univ, Nat.card_fun]; simp

theorem avoidSet_step (m N : ℕ) (hm : 1 ≤ m) :
    (avoidSet m (N + (m + 1))).ncard ≤ (2 ^ (m + 1) - 2) * (avoidSet m N).ncard := by
  have := Set.ncard_le_ncard_of_injOn
    (fun w : Fin (N + (m + 1)) → Bool =>
      ((fun j : Fin (m + 1) => w ⟨j, by omega⟩), (fun j : Fin N => w ⟨m + 1 + j, by omega⟩)))
    (s := avoidSet m (N + (m + 1))) (t := goodBlock m ×ˢ avoidSet m N) ?_ ?_ (Set.toFinite _)
  · rw [Set.ncard_prod] at this
    exact this.trans (Nat.mul_le_mul_right _ (goodBlock_ncard m hm))
  · intro w hw
    refine ⟨fun hB => hw 0 (by omega) (dvd_zero _) ?_, fun b hb hdiv hB => ?_⟩
    · exact ⟨hB.1, fun j hj => hB.2 j hj⟩
    · refine hw (m + 1 + b) (by omega) (dvd_add (dvd_refl _) hdiv) ⟨?_, fun j hj => ?_⟩
      · have := hB.1; simpa [Nat.add_assoc] using this
      · have := hB.2 j hj; simpa [Nat.add_assoc] using this
  · intro w _ w' _ h
    simp only [Prod.mk.injEq] at h
    funext k
    by_cases hk : (k : ℕ) < m + 1
    · have := congrFun h.1 ⟨k, hk⟩; simpa using this
    · have := congrFun h.2 ⟨k - (m + 1), by omega⟩
      simp only at this
      rw [show k = ⟨m + 1 + (k - (m + 1)), by omega⟩ from Fin.ext (by simp; omega)]
      exact this

theorem avoidSet_bound (m : ℕ) (hm1 : 1 ≤ m) : ∀ N : ℕ,
    ((avoidSet m N).ncard : ℝ) ≤ 2 ^ N * (1 - (1 / 2) ^ m) ^ (N / (m + 1)) := by
  have hblock : ((2 ^ (m + 1) - 2 : ℕ) : ℝ) = 2 ^ (m + 1) * (1 - (1 / 2) ^ m) := by
    have : 2 ≤ 2 ^ (m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub this]; push_cast
    have h : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    rw [pow_succ]; linear_combination 2 * h
  have hε : (0 : ℝ) ≤ 1 - (1 / 2) ^ m := by
    have : ((1 : ℝ) / 2) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < m + 1
    · rw [Nat.div_eq_of_lt hN, pow_zero, mul_one]
      exact_mod_cast avoidSet_short hN
    · push_neg at hN
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + (m + 1) := ⟨N - (m + 1), by omega⟩
      have hstep : ((avoidSet m (N' + (m + 1))).ncard : ℝ) ≤
          ((2 ^ (m + 1) - 2 : ℕ) : ℝ) * (avoidSet m N').ncard := by
        exact_mod_cast avoidSet_step m N' hm1
      have hih := ih N' (by omega)
      rw [hblock] at hstep
      have hdiv : (N' + (m + 1)) / (m + 1) = N' / (m + 1) + 1 := by
        rw [Nat.add_div_right _ (by omega)]
      rw [hdiv, pow_add, pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ (m + 1) * (1 - (1 / 2) ^ m) := by positivity
      calc ((avoidSet m (N' + (m + 1))).ncard : ℝ)
          ≤ 2 ^ (m + 1) * (1 - (1 / 2) ^ m) * (avoidSet m N').ncard := hstep
        _ ≤ 2 ^ (m + 1) * (1 - (1 / 2) ^ m) * (2 ^ N' * (1 - (1 / 2) ^ m) ^ (N' / (m + 1))) :=
          mul_le_mul_of_nonneg_left hih hp
        _ = _ := by ring

/-- **The AFS rigidity breaks at rate `Θ(|δ|^{1/log₂(3/2)})`, up to a logarithm.**  The words that
keep the AFS piece unbroken for `N` steps number between the run-bounded words
(`afsUnbroken_of_noRunLonger`, `run_bounded_count_ge`: at least `2^N (1 - 2^{-R})^N`) and
`2^N (1 - 2^{-m})^{⌊N/(m+1)⌋}`.  Here `R` and `m` are both `log_{3/2}(1/|δ|) + O(1)`.
PROVED 2026-10-06 (`avoidSet_bound`).  Proof of the upper bound: cut the positions into `⌊N/(m+1)⌋` disjoint blocks of
length `m + 1`.  In each block the pattern "flip, then `m` equal letters" has probability `2^{-m}`
independently, and any occurrence breaks the piece (`not_afsUnbroken_of_long_run`).
Checked exhaustively at `δ = 1/30` (`R = 2`, `m = 6`), `N = 8, 12, 14` (`test_afs_event_rate_bounds`). -/
theorem card_afsUnbroken_le (δ : ℝ) (m N : ℕ) (hm : 1 / 3 < |δ| * ((3 / 2) ^ m - 1)) :
    (Nat.card {w : Fin N → Bool // AfsUnbroken δ N w} : ℝ) ≤
      2 ^ N * (1 - (1 / 2) ^ m) ^ (N / (m + 1)) := by
  have hm1 : 1 ≤ m := by
    by_contra h0; push_neg at h0
    interval_cases m; simp at hm; linarith
  rw [show Nat.card {w : Fin N → Bool // AfsUnbroken δ N w} = {w | AfsUnbroken δ N w}.ncard from
    Nat.card_coe_set_eq _]
  have hsub : {w : Fin N → Bool | AfsUnbroken δ N w} ⊆ avoidSet m N := by
    intro w hw b hb _ hB
    have h1 := hB.2 1 ⟨le_rfl, hm1⟩
    refine not_afsUnbroken_of_long_run δ m N hm hm1 w b hb (by rw [h1]; exact hB.1)
      (fun j hj => (hB.2 j hj).trans h1.symm) hw
  have h1 : ({w : Fin N → Bool | AfsUnbroken δ N w}.ncard : ℝ) ≤ (avoidSet m N).ncard := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  exact h1.trans (avoidSet_bound m hm1 N)

/-! ### The anchor-parity bijection: real orbits -/

/-- Anchor and type of the AFS piece after `n` steps from `g + [0, 1/3 + δ]`. -/
def afsAnchor (g : ℤ) : ℕ → ℤ × Bool
  | 0 => (g, false)
  | n + 1 => ((3 * ((afsAnchor g n).1 / 2) + (afsAnchor g n).1 % 2 +
      if (afsAnchor g n).2 then 1 else 0), decide ((afsAnchor g n).1 % 2 = 1))

/-- The single free endpoint error of the piece. -/
noncomputable def afsE (δ : ℝ) (g : ℤ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if decide ((afsAnchor g n).1 % 2 = 1) = (afsAnchor g n).2 then 3 / 2 * afsE δ g n
      else 3 / 2 * δ

/-- The piece: type `false` is `k + [e, 1/3 + δ]`, type `true` is `k + [2/3 + δ, 1 + e]`. -/
def afsPiece (δ : ℝ) (τ : Bool) (k : ℤ) (e : ℝ) : Set ℝ :=
  if τ then Set.Icc (k + 2 / 3 + δ) (k + 1 + e) else Set.Icc (k + e) (k + 1 / 3 + δ)

theorem afsPiece_arc {δ e : ℝ} (hd : |δ| < 1 / 6) (he : |e| < 1 / 6) (τ : Bool) (k : ℤ)
    {y : ℝ} (hy : y ∈ afsPiece δ τ k e) :
    ∃ x ∈ Set.Icc (2 / 3 + δ) (2 / 3 + δ + 2 / 3), Int.fract y = Int.fract x := by
  have a := abs_lt.1 hd; have b := abs_lt.1 he
  cases τ
  · simp only [afsPiece, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] at hy
    refine ⟨y - ((k - 1 : ℤ) : ℝ), ⟨?_, ?_⟩, (Int.fract_sub_intCast _ _).symm⟩ <;>
      push_cast <;> linarith
  · simp only [afsPiece, ↓reduceIte, Set.mem_Icc] at hy
    refine ⟨y - (k : ℝ), ⟨?_, ?_⟩, (Int.fract_sub_intCast _ _).symm⟩ <;> linarith

theorem afsPiece_nonempty {δ e : ℝ} (hd : |δ| < 1 / 6) (he : |e| < 1 / 6) (τ : Bool) (k : ℤ) :
    ∃ y, y ∈ afsPiece δ τ k e := by
  have a := abs_lt.1 hd; have b := abs_lt.1 he
  cases τ
  · exact ⟨k + e, by simp only [afsPiece, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]; constructor <;> linarith⟩
  · exact ⟨k + 2 / 3 + δ, by simp only [afsPiece, ↓reduceIte, Set.mem_Icc]; constructor <;> linarith⟩

theorem afsPiece_step_abs {δ e : ℝ} (h : 3 / 2 * |e| + |δ| < 1 / 6) (τ : Bool) (k : ℤ) {y : ℝ}
    (hy : y ∈ afsPiece δ (decide (k % 2 = 1)) (3 * (k / 2) + k % 2 + if τ then 1 else 0)
      (if decide (k % 2 = 1) = τ then 3 / 2 * e else 3 / 2 * δ)) :
    2 / 3 * y ∈ afsPiece δ τ k e := by
  have hd := abs_le.1 (le_refl |δ|)
  have hee := abs_le.1 (le_refl |e|)
  have hn0 := abs_nonneg e
  have hn1 := abs_nonneg δ
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · have h1 : 2 * j % 2 = 0 := by omega
    have h2 : 2 * j / 2 = j := by omega
    rw [h1, h2] at hy
    cases τ <;> simp [afsPiece] at hy ⊢ <;> push_cast at hy ⊢ <;> constructor <;> linarith
  · have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h1, h2] at hy
    cases τ <;> simp [afsPiece] at hy ⊢ <;> push_cast at hy ⊢ <;> constructor <;> linarith

theorem afsPiece_step {δ : ℝ} (g : ℤ) (n : ℕ) (h : 3 / 2 * |afsE δ g n| + |δ| < 1 / 6) {y : ℝ}
    (hy : y ∈ afsPiece δ (afsAnchor g (n + 1)).2 (afsAnchor g (n + 1)).1 (afsE δ g (n + 1))) :
    2 / 3 * y ∈ afsPiece δ (afsAnchor g n).2 (afsAnchor g n).1 (afsE δ g n) :=
  afsPiece_step_abs h _ _ hy

/-- If the error stays small to depth `N`, the integer part `g` is trapped to depth `N`. -/
theorem afs_trapped_of_bound (δ : ℝ) (g : ℤ) (N : ℕ)
    (hb : ∀ n ≤ N, 3 / 2 * |afsE δ g n| + |δ| < 1 / 6) :
    ∃ ξ : ℝ, ⌊ξ⌋ = g ∧
      ∀ n ≤ N, ∃ x ∈ Set.Icc (2 / 3 + δ) (2 / 3 + δ + 2 / 3), Int.fract (ξ * (3 / 2) ^ n) = Int.fract x := by
  have small : ∀ n ≤ N, |δ| < 1 / 6 ∧ |afsE δ g n| < 1 / 6 := fun n hn => by
    have := hb n hn; have := abs_nonneg δ; have := abs_nonneg (afsE δ g n)
    constructor <;> linarith
  have key : ∀ n ≤ N, ∀ y ∈ afsPiece δ (afsAnchor g n).2 (afsAnchor g n).1 (afsE δ g n),
      ⌊(2 / 3 : ℝ) ^ n * y⌋ = g ∧ ∀ j ≤ n, ∃ x ∈ Set.Icc (2 / 3 + δ) (2 / 3 + δ + 2 / 3),
        Int.fract ((2 / 3 : ℝ) ^ n * y * (3 / 2) ^ j) = Int.fract x := by
    intro n
    induction n with
    | zero =>
      intro hN y hy
      obtain ⟨h1, h2⟩ := small 0 hN
      have hy' := hy
      simp only [afsPiece, afsAnchor, afsE, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] at hy'
      have a := abs_lt.1 h1
      refine ⟨?_, fun j hj => ?_⟩
      · rw [Int.floor_eq_iff]; simp; constructor <;> linarith
      · obtain rfl : j = 0 := by omega
        simpa using afsPiece_arc h1 h2 _ _ hy
    | succ n ih =>
      intro hN y hy
      have hz := afsPiece_step g n (hb n (by omega)) hy
      obtain ⟨f1, f2⟩ := ih (by omega) _ hz
      have e1 : (2 / 3 : ℝ) ^ (n + 1) * y = (2 / 3) ^ n * (2 / 3 * y) := by ring
      refine ⟨by rw [e1]; exact f1, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
      · rw [e1]; exact f2 j (by omega)
      · obtain rfl : j = n + 1 := by omega
        have e2 : (2 / 3 : ℝ) ^ (n + 1) * y * (3 / 2) ^ (n + 1) = y := by
          rw [mul_comm _ y, mul_assoc, ← mul_pow]; norm_num
        rw [e2]
        exact afsPiece_arc (small _ hN).1 (small _ hN).2 _ _ hy
  obtain ⟨y, hy⟩ := afsPiece_nonempty (small N le_rfl).1 (small N le_rfl).2
    (afsAnchor g N).2 (afsAnchor g N).1
  obtain ⟨f1, f2⟩ := key N le_rfl y hy
  exact ⟨(2 / 3) ^ N * y, f1, fun n hn => f2 n hn⟩

/-- The anchor-parity word of `g`, length `N`. -/
def afsWord (g : ℤ) (N : ℕ) : Fin N → Bool := fun i => decide ((afsAnchor g i).1 % 2 = 1)

theorem afsE_bound (δ : ℝ) (g : ℤ) (N : ℕ) : ∀ n ≤ N,
    |afsE δ g n| ≤ (3 / 2) ^ trail (afsWord g N) (afsAnchor g n).2 n * |δ| := by
  intro n
  induction n with
  | zero => intro _; simp only [afsE, abs_zero]; positivity
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    have ih := ih (by omega)
    have ht : trail (afsWord g N) (afsAnchor g (n + 1)).2 (n + 1) =
        trail (afsWord g N) (afsWord g N ⟨n, hnN⟩) n + 1 := by
      simp [trail, hnN, afsWord, afsAnchor]
    rw [ht, pow_succ]
    have hd := abs_nonneg δ
    have hp : (1 : ℝ) ≤ (3 / 2) ^ trail (afsWord g N) (afsWord g N ⟨n, hnN⟩) n :=
      one_le_pow₀ (by norm_num)
    simp only [afsE]
    split_ifs with hc
    · have : afsWord g N ⟨n, hnN⟩ = (afsAnchor g n).2 := by simpa [afsWord] using hc
      rw [this, abs_mul]; norm_num; nlinarith
    · rw [abs_mul]; norm_num; nlinarith

theorem afsAnchor_diff (g g' : ℤ) (N : ℕ) (hw : afsWord g N = afsWord g' N) : ∀ n ≤ N,
    (afsAnchor g n).2 = (afsAnchor g' n).2 ∧
      2 ^ n * ((afsAnchor g n).1 - (afsAnchor g' n).1) = 3 ^ n * (g - g') := by
  intro n
  induction n with
  | zero => intro _; simp [afsAnchor]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hp := congrFun hw ⟨n, by omega⟩
    simp only [afsWord, decide_eq_decide] at hp
    simp only [afsAnchor]
    refine ⟨by simpa using hp, ?_⟩
    have k2 : 2 * ((3 * ((afsAnchor g n).1 / 2) + (afsAnchor g n).1 % 2 +
        if (afsAnchor g n).2 then 1 else 0) - (3 * ((afsAnchor g' n).1 / 2) +
        (afsAnchor g' n).1 % 2 + if (afsAnchor g' n).2 then 1 else 0)) =
        3 * ((afsAnchor g n).1 - (afsAnchor g' n).1) := by
      rw [h1]; split_ifs <;> omega
    rw [pow_succ, pow_succ, mul_assoc, k2, ← mul_assoc, mul_comm _ 3, mul_assoc, h2]; ring

theorem afsWord_injective (N : ℕ) :
    Function.Injective (fun g : Fin (2 ^ N) => afsWord (g : ℤ) N) := by
  intro a b hab
  obtain ⟨_, h⟩ := afsAnchor_diff _ _ N hab N le_rfl
  have hc : IsCoprime ((2 : ℤ) ^ N) (3 ^ N) :=
    (Int.isCoprime_iff_gcd_eq_one.2 (by norm_num)).pow
  have hdvd : (2 : ℤ) ^ N ∣ ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨(afsAnchor ((a : ℕ) : ℤ) N).1 - (afsAnchor ((b : ℕ) : ℤ) N).1, by linear_combination -h⟩
  have ha := a.2; have hb := b.2
  have h2 : ((2 ^ N : ℕ) : ℤ) = 2 ^ N := by push_cast; ring
  rw [← h2] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have : c = 0 := by
    rcases lt_trichotomy c 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst this
  exact Fin.ext (by omega)

theorem afs_bound_of_run (δ : ℝ) (R N : ℕ) (G : ℤ) (hR : (3 / 2) ^ (R + 1) * |δ| + |δ| < 1 / 6)
    {w : Fin N → Bool} (hrun : NoRunLonger R N w) (hw : afsWord G N = w) :
    ∀ n ≤ N, 3 / 2 * |afsE δ G n| + |δ| < 1 / 6 := by
  subst hw
  intro n hn
  have b := afsE_bound δ G N n hn
  have t := trail_le hrun (afsAnchor G n).2 n hn
  have p : (3 / 2 : ℝ) ^ trail (afsWord G N) (afsAnchor G n).2 n ≤ (3 / 2) ^ R :=
    pow_le_pow_right₀ (by norm_num) t
  rw [pow_succ] at hR
  nlinarith [abs_nonneg δ]

/-- **Near-AFS density theorem.**  If runs of length `R` cost less than the slack,
`(3/2)^(R+1) |δ| + |δ| < 1/6`, then at least as many integer parts below `2^N` are trapped to
depth `N` in the shifted arc as there are binary words of length `N` with no run longer than `R`.
PROVED 2026-10-06 (`afs_trapped_of_bound`, `afsWord_injective`).  Proof: start from the piece `g + [0, 1/3 + δ]` (errors `0, δ`).  Under the run
bound every error is at most `(3/2)^R |δ|`, so every step obeys the recursion's conditions.  The nested
pieces are nonempty, and they stay in `[g, g + 1)`.  The anchor-parity map is a bijection from
`g mod 2^N` onto words.
With `run_bounded_count_ge` this gives density `≥ (1 - 2^{-R})^N`, where
`2^{-R} ≍ |δ|^{1/log₂(3/2)} = |δ|^{1.7095…}`.  So a typical integer part lives at least
`~|δ|^{-1.71}` steps.  The worst one lives only `~log_{3/2}(1/|δ|)` steps (`near_afs_every_floor`). -/
theorem near_afs_density (δ : ℝ) (R N : ℕ) (hR : (3 / 2) ^ (R + 1) * |δ| + |δ| < 1 / 6) :
    Nat.card {w : Fin N → Bool // NoRunLonger R N w} ≤
      Nat.card {g : Fin (2 ^ N) // TrapsToDepth (2 / 3 + δ) (2 / 3) N g} := by
  have hbij : Function.Bijective (fun g : Fin (2 ^ N) => afsWord (g : ℤ) N) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨afsWord_injective N, by simp⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (2 ^ N) ≃ (Fin N → Bool), ∀ g, e g = afsWord ((g : ℕ) : ℤ) N :=
    ⟨Equiv.ofBijective _ hbij, fun _ => rfl⟩
  refine Nat.card_le_card_of_injective
    (fun w => ⟨e.symm w.1, ?_⟩) (fun a b h => Subtype.ext (e.symm.injective (congrArg Subtype.val h)))
  have hw : afsWord ((e.symm w.1 : ℕ) : ℤ) N = w.1 := by rw [← he]; simp
  obtain ⟨ξ, h1, h2⟩ := afs_trapped_of_bound δ _ N (afs_bound_of_run δ R N _ hR w.2 hw)
  exact ⟨ξ, h1, h2⟩

/-- **Every integer part survives `~log_{3/2}(1/|δ|)` steps near the AFS arc.**  PROVED 2026-10-06 (`afs_trapped_of_bound`).
Proof: the recursion of `near_afs_density` with `R = N`; no word of length `N` has a longer run.
The component game shows this is the right order: from `[0, 3]` the adversary kills at exactly
depth `8 + k` at `δ = ±(1/30)(2/3)^k`, `k = 0..8` (from the AFS
window `[0, 1/2]`: `7 + k` and `6 + k`) (`arc_entropy.py` `test_adversarial_depth_ladder`). -/
theorem near_afs_every_floor (δ : ℝ) (N g : ℕ) (hN : (3 / 2) ^ (N + 1) * |δ| + |δ| < 1 / 6) :
    TrapsToDepth (2 / 3 + δ) (2 / 3) N g := by
  obtain ⟨ξ, h1, h2⟩ := afs_trapped_of_bound δ g N fun n hn => by
    have b := afsE_bound δ g N n hn
    have t := (trail_spec (afsWord (g : ℤ) N) (afsAnchor (g : ℤ) n).2 n hn).1
    have p : (3 / 2 : ℝ) ^ trail (afsWord (g : ℤ) N) (afsAnchor (g : ℤ) n).2 n ≤ (3 / 2) ^ N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at hN
    nlinarith [abs_nonneg δ]
  exact ⟨ξ, h1, h2⟩

/-- **Conjecture: the near-AFS decay rate is `|δ|^{1/log₂(3/2)}`.**
What is proved: the AFS piece breaks at rate `Θ(|δ|^{1/log₂(3/2)})` up to a log
(`card_afsUnbroken_le`, `near_afs_density`).  What is missing: turning that event rate into the
critical decay constant.  Two things block it.  (1) Most breaks are harmless shape changes: at
`δ = 1/30` the break rate is `≈ 0.08` per step, while `c ≈ 0.007`.  (2) The pieces of one integer
part draw their parities from the same bits.  Two pieces whose anchors differ by `D` have parities
differing by `D mod 2`, so Kolmogorov's critical-branching theorem does not apply directly.  No
mechanism is known for either.
  At length `2/3` the survivors
decay as a critical branching process, `S(N)/S(0) ≈ 1/(1 + c(δ) N)` (`AfsArcIsUniqueMinimal`), and
`c(δ) = Θ(|δ|^{1/log₂(3/2)})`: events (a death, or a branch) need a run of length
`R(δ) = log_{3/2}(1/|δ|) + O(1)`, which a fair parity sequence produces at rate `2^{-R}`.
Confidence 55%.  Evidence inside the horizon (the conjecture's own setting): 1023 integer parts drawn
uniformly below `2^N`, so the parities are exactly uniform.
* `δ = 1/30`: survival `0.659, 0.444, 0.258, 0.153` at `N = 100, 200, 400, 800`, so `c ≈ 0.0070`.
* `δ = 1/45`: `0.640, 0.438, 0.264, 0.144` at `N = 200, 400, 800, 1600`, so `c ≈ 0.0036`.
* One rung of `2/3` in `δ` divides `c` by `1.94`; predicted `2`.
* Controls: `δ = 0` keeps `1.000`; a generic position (`s = 1/6`) gives `c ≈ 0.024`.

Beyond the horizon (all integer parts below `2^10`, `profile`) the same law holds with `c` about
`1.3`–`1.45` times larger.
* `δ = 1/30, 1/45, 2/135, 4/405`: `c = 0.0102, 0.0047, 0.0025, 0.0014`.
* Mirror side `δ = -1/30, -1/45, -2/135`: `c = 0.0058, 0.0042, 0.0017`.

`near_afs_density` proves the lower bound on lifetimes inside the 2-adic horizon.  The matching upper
bound is a statement about the transfer operator, not about the integers. -/
def NearAfsDecayExponent : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, δ ≠ 0 → |δ| ≤ 1 / 30 →
    ∀ N : ℕ, (Nat.card {g : Fin (2 ^ N) // TrapsToDepth (2 / 3 + δ) (2 / 3) N g} : ℝ) ≤
      2 ^ N * (C / (C + |δ| ^ (1 / Real.logb 2 (3 / 2)) * N))

/-- The strong conjecture caps the distance constant: `E(3/2) ≤ 1/6`. -/
theorem strongMahler_far_le_one_sixth (h : StrongMahlerConjecture) (β : ℝ) (hβ : 1 / 6 < β) :
    ¬ ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers β ξ := by
  rintro ⟨ξ, hξ, hf⟩
  exact h β (1 - 2 * β) (by linarith) ⟨ξ, hξ, fun n =>
    ⟨Int.fract (ξ * (3 / 2) ^ n), ⟨(hf n).1, by linarith [(hf n).2]⟩, (Int.fract_fract _).symm⟩⟩

/-- **The relaxed game's value is `7/57`.**  Every `β < 7/57` admits a memoryless relaxed
strategy for `[β, 1 - β]`, and no width admits one at `β > 7/57`.
PROVED 2026-10-06 (`relaxedValueIsSevenFiftySevenths`; sharper: `relaxedStrategy_exists_iff`, the value is
attained at `β = 7/57` by the seven-interval certificate `relaxedStrategy_757`).  The lattice solver had
reported a loss at `7/57` itself only because it drops one-point intersections.
Mechanism: `4/19 → 6/19 → 9/19` is a 3-cycle of `x ↦ 3x/2 + d (mod 1)` (parities `0, 0, 1/2`), and the
arc's right edge maps to `1/2 - 3β/2 = 6/19` exactly at `β = 7/57`.  Exact minimax of the
just-in-time adversarial-parity game forces the constructor out at depth 26 for `β = 0.1229`. -/
def RelaxedValueIsSevenFiftySevenths : Prop :=
  (∀ β : ℝ, 0 < β → β < 7 / 57 → ∃ l P, RelaxedStrategy β (1 - 2 * β) l P) ∧
  (∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ l P, ¬ RelaxedStrategy β (1 - 2 * β) l P)

/-! ### The memoryless value is exactly `7/57`, and it is attained -/

/-- The seven window-start intervals of the `7/57` certificate (width `l = 1/8`).  Found by `solve_vw` near
`7/57`, where the lattice fixed point stops moving with `β`; its endpoints are the rationals below
(denominators divide `8 · 9 · 19`). -/
def P757 : Set ℝ :=
  Set.Icc (13 / 152 : ℝ) (22 / 171 : ℝ) ∪
    Set.Icc (29 / 152 : ℝ) (11 / 57 : ℝ) ∪
    Set.Icc (53 / 152 : ℝ) (20 / 57 : ℝ) ∪
    Set.Icc (565 / 1368 : ℝ) (79 / 171 : ℝ) ∪
    Set.Icc (239 / 456 : ℝ) (10 / 19 : ℝ) ∪
    Set.Icc (311 / 456 : ℝ) (13 / 19 : ℝ) ∪
    Set.Icc (1021 / 1368 : ℝ) (15 / 19 : ℝ)

/-- **The memoryless relaxed game is won at exactly `β = 7/57`.**  Eighteen clamp cells `u = max a c`
(`cell1228`), four of the fourteen (interval, parity) pairs split once.  Closed-interval check and
exact orbit play: `experiments/arc_value_757.py`. -/
theorem relaxedStrategy_757 : RelaxedStrategy (7 / 57) (43 / 57) (1 / 8) P757 := by
  have S0 : Set.Icc (13 / 152 : ℝ) (22 / 171 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S1 : Set.Icc (29 / 152 : ℝ) (11 / 57 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S2 : Set.Icc (53 / 152 : ℝ) (20 / 57 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S3 : Set.Icc (565 / 1368 : ℝ) (79 / 171 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S4 : Set.Icc (239 / 456 : ℝ) (10 / 19 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S5 : Set.Icc (311 / 456 : ℝ) (13 / 19 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  have S6 : Set.Icc (1021 / 1368 : ℝ) (15 / 19 : ℝ) ⊆ P757 := by
    intro x hx; simp only [P757, Set.mem_union]; tauto
  refine ⟨by norm_num, ⟨_, S0 ⟨le_refl _, by norm_num⟩⟩, ?_, ?_⟩
  · intro x hx
    simp only [P757, Set.mem_union, Set.mem_Icc] at hx
    constructor <;> rcases hx with ((((((h | h) | h) | h) | h) | h) | h) <;>
      linarith [h.1, h.2]
  intro a ha d hd
  simp only [P757, Set.mem_union] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases ha with ((((((h | h) | h) | h) | h) | h) | h) <;>
    rcases hd with rfl | rfl
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (29 / 228 : ℝ)) (A := (29 / 152 : ℝ)) (B := (11 / 57 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S1 h4⟩
  · rcases le_total a (7 / 57 : ℝ) with hm | hm
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (7 / 57 : ℝ)) (A := (311 / 456 : ℝ)) (B := (13 / 19 : ℝ)) 0 ⟨h.1, hm⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S5 h4⟩
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (337 / 2052 : ℝ)) (A := (1021 / 1368 : ℝ)) (B := (15 / 19 : ℝ)) 0 ⟨hm, h.2⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S6 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (53 / 228 : ℝ)) (A := (53 / 152 : ℝ)) (B := (20 / 57 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (337 / 2052 : ℝ)) (A := (1021 / 1368 : ℝ)) (B := (15 / 19 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S6 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (239 / 684 : ℝ)) (A := (239 / 456 : ℝ)) (B := (10 / 19 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S4 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (89 / 228 : ℝ)) (A := (13 / 152 : ℝ)) (B := (22 / 171 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S0 h4⟩
  · rcases le_total a (26 / 57 : ℝ) with hm | hm
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (311 / 684 : ℝ)) (A := (311 / 456 : ℝ)) (B := (13 / 19 : ℝ)) 0 ⟨h.1, hm⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S5 h4⟩
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (1021 / 2052 : ℝ)) (A := (1021 / 1368 : ℝ)) (B := (15 / 19 : ℝ)) 0 ⟨hm, h.2⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S6 h4⟩
  · rcases le_total a (215 / 513 : ℝ) with hm | hm
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (89 / 228 : ℝ)) (A := (13 / 152 : ℝ)) (B := (22 / 171 : ℝ)) 1 ⟨h.1, hm⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S0 h4⟩
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (35 / 76 : ℝ)) (A := (29 / 152 : ℝ)) (B := (11 / 57 : ℝ)) 1 ⟨hm, h.2⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S1 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (1021 / 2052 : ℝ)) (A := (1021 / 1368 : ℝ)) (B := (15 / 19 : ℝ)) 0 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S6 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (43 / 76 : ℝ)) (A := (53 / 152 : ℝ)) (B := (20 / 57 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S2 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (55 / 76 : ℝ)) (A := (13 / 152 : ℝ)) (B := (22 / 171 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S0 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (467 / 684 : ℝ)) (A := (239 / 456 : ℝ)) (B := (10 / 19 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S4 h4⟩
  · rcases le_total a (386 / 513 : ℝ) with hm | hm
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (55 / 76 : ℝ)) (A := (13 / 152 : ℝ)) (B := (22 / 171 : ℝ)) 1 ⟨h.1, hm⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S0 h4⟩
    · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 0) (c := (181 / 228 : ℝ)) (A := (29 / 152 : ℝ)) (B := (11 / 57 : ℝ)) 1 ⟨hm, h.2⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨u, h1, h2, h3, S1 h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := cell1228 (s := 7 / 57) (t := 43 / 57) (l := 1 / 8) (d := 1 / 2) (c := (539 / 684 : ℝ)) (A := (311 / 456 : ℝ)) (B := (13 / 19 : ℝ)) 1 h
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨u, h1, h2, h3, S5 h4⟩

/-- **`‖ξ (3/2)^n‖ ≥ 7/57` for some `ξ > 0`**, the exact limit of memoryless constructions
(`relaxed_barrier`).  Supersedes `exists_farFromIntegers_1228` (`307/2500 < 7/57`). -/
theorem exists_farFromIntegers_757 : ∃ ξ : ℝ, 0 < ξ ∧ FarFromIntegers (7 / 57) ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_trapped_of_relaxedStrategy relaxedStrategy_757
  refine ⟨ξ, hξ, fun n => ?_⟩
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h n
  have : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
  rw [hx, this]
  constructor <;> linarith

/-- `7/57 ≤ E(3/2)`. -/
theorem E_three_halves_ge_757 : 7 / 57 ≤ E (3 / 2) := by
  obtain ⟨ξ, hξ, h⟩ := exists_farFromIntegers_757
  exact E_ge_of_far hξ h

/-- **The memoryless relaxed game's value is exactly `7/57`, and it is attained.**  For `0 < β < 1/2`,
a memoryless relaxed strategy for `[β, 1 - β]` exists iff `β ≤ 7/57`: one certificate
(`relaxedStrategy_757`, monotonicity) below, `relaxed_barrier` above. -/
theorem relaxedStrategy_exists_iff (β : ℝ) (hβ' : β < 1 / 2) :
    (∃ l P, RelaxedStrategy β (1 - 2 * β) l P) ↔ β ≤ 7 / 57 := by
  constructor
  · rintro ⟨l, P, h⟩
    by_contra hb
    exact relaxed_barrier β (not_le.1 hb) hβ' l P h
  · intro hb
    exact ⟨1 / 8, P757, relaxedStrategy_757.mono hb (by linarith)⟩

/-- `RelaxedValueIsSevenFiftySevenths` holds. -/
theorem relaxedValueIsSevenFiftySevenths : RelaxedValueIsSevenFiftySevenths :=
  ⟨fun β _ hβ => (relaxedStrategy_exists_iff β (by linarith)).2 hβ.le,
    fun β hβ hβ' l P => relaxed_barrier β hβ hβ' l P⟩

/-! ### Finite memory past `7/57`?  The horizon question for the far-from-integers game -/

/-- **`k`-memory relaxed strategy** (`solve_vw` in `experiments/arc_trap_k.py`, `k ≥ 1`).  `P r` holds the
window left ends allowed when the integer part `m` has `m ≡ r (mod 2^k)`, so the parity
`d = (r mod 2)/2` is known.  The child's integer part is `⌊3m/2⌋ + ⌊3u/2 + d⌋`; its residue mod
`2^(k-1)` is determined by `r` and the move, its top bit is not, so the child must be allowed for both
values `b` of that bit.  `k = 1` is the memoryless game (`kRelaxedStrategy_one`). -/
def KRelaxedStrategy (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ) : Prop :=
  0 < l ∧ (∀ r, P r ⊆ Set.Ico 0 1) ∧
  ∀ r < 2 ^ k, ∀ a ∈ P r, ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b < 2, Int.fract (3 * u / 2 + ((r % 2 : ℕ) : ℝ) / 2) ∈
      P (((3 * r - r % 2) / 2 + (⌊3 * u / 2 + ((r % 2 : ℕ) : ℝ) / 2⌋).toNat) % 2 ^ (k - 1) +
        b * 2 ^ (k - 1))

/-- With one bit of memory the strategy only learns the parity it was going to be told anyway:
`P 0 ∩ P 1` is a memoryless relaxed strategy. -/
theorem kRelaxedStrategy_one {s t l : ℝ} {P : ℕ → Set ℝ} (h : KRelaxedStrategy s t l 1 P)
    (hne : (P 0 ∪ P 1).Nonempty) : RelaxedStrategy s t l (P 0 ∩ P 1) := by
  obtain ⟨hl, hP, hm⟩ := h
  have key : ∀ r < 2, ∀ a ∈ P r, ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
      (∃ j : ℤ, (j : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ j + s + t) ∧
      Int.fract (3 * u / 2 + ((r % 2 : ℕ) : ℝ) / 2) ∈ P 0 ∩ P 1 := by
    intro r hr a ha
    obtain ⟨u, h1, h2, h3, h4⟩ := hm r (by simpa using hr) a ha
    refine ⟨u, h1, h2, h3, ?_, ?_⟩
    · simpa [Nat.mod_one] using h4 0 (by norm_num)
    · simpa [Nat.mod_one] using h4 1 (by norm_num)
  refine ⟨hl, ?_, fun x hx => hP 0 hx.1, ?_⟩
  · obtain ⟨a, ha⟩ := hne
    rcases ha with ha | ha
    · obtain ⟨u, -, -, -, h4⟩ := key 0 (by norm_num) a ha; exact ⟨_, h4⟩
    · obtain ⟨u, -, -, -, h4⟩ := key 1 (by norm_num) a ha; exact ⟨_, h4⟩
  intro a ha d hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · obtain ⟨u, h1, h2, h3, h4⟩ := key 0 (by norm_num) a ha.1
    exact ⟨u, h1, h2, h3, by simpa using h4⟩
  · obtain ⟨u, h1, h2, h3, h4⟩ := key 1 (by norm_num) a ha.2
    exact ⟨u, h1, h2, h3, by norm_num at h4 ⊢; exact h4⟩

/-- **Conjecture: no finite memory passes `7/57`.**  For every `k ≥ 1` and `β > 7/57` (with `β < 1/2`),
no `k`-memory relaxed strategy holds `[β, 1 - β]` from any residue.  Proved for `k = 1`
(`finiteMemoryRelaxedValue_one`).  Confidence 85% that it is true; ~10% that the present methods
prove it for all `k`.
Evidence: `solve_vw` loses at `7/57 + 10⁻⁶` for `k = 0, …, 6, 8, 10, 12, 14` (and at `0.1235`, `0.125` for
`k = 8, 10`); the exact `k`-memory component game (`experiments/arc_kmemory.py`) kills every residue at
`β = 0.1229` within 26, 30, 33 steps for `k = 1, 2, 3`; at `β = 0.13` within 14, 16, 17, 21, 23, 25,
27 steps for `k = 1, …, 7`, and at `β = 0.135` within 12, 15, 16, 17, 18, 21, 22, 27 for `k = 1, …, 8`
(about two extra steps per bit of memory).
Uniform in `k` from `0.13` up (`finiteMemoryRelaxedValue_ge_013`, given `KRelaxedLiveEverywhere`):
oblivious certificates per window width bound every memory size at once, so the open range is
`(7/57, 0.13)`.  Relaxed kills already reach `0.1229` at width `3/20`
(`relaxedObliviousKill_1229_width_3_20`), and at `0.1229` every width `l ≤ (1/9)(2/3)^k` dies with no
liveness hypothesis (`not_kRelaxedStrategy_1229_small_width`: the adversary sees the start before
choosing the high digits, then narrow-start kills finish it).  So at `0.1229` the open widths are
`((1/9)(2/3)^k, 1.11]` minus `3/20`.  At `β = 1/8` the kill depths
are 19, 21, 22, 27, 28, 32 for `k = 1, …, 6`.
Difficulty locus: oblivious kills stop near `0.1375` (depths 20, 25, 36, 51, 53, 62, 66 at `0.15`,
`0.145`, `0.14`, `0.138`, `0.1379`, `0.1378`, `0.1377`; width-20000 beams under three scores find none at
`0.137`, `0.1365`, `0.136` to depth 70 to 90).  So in `(7/57, 0.1375)` no fixed parity sequence kills (`FullInformationBeatsSevenFiftySevenths`), and a proof must use the adversary's
adaptivity, delayed by `k - 1` steps, quantitatively in `k`.  No general memory reduction exists
(`MemoryHelpsOffCentre`). -/
def FiniteMemoryRelaxedValue : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, 7 / 57 < β → β < 1 / 2 → ∀ (l : ℝ) (P : ℕ → Set ℝ),
    (∃ r < 2 ^ k, (P r).Nonempty) → ¬ KRelaxedStrategy β (1 - 2 * β) l k P

/-- The `k = 1` case of `FiniteMemoryRelaxedValue`. -/
theorem finiteMemoryRelaxedValue_one (β : ℝ) (hβ : 7 / 57 < β) (hβ' : β < 1 / 2) (l : ℝ)
    (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 1, (P r).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l 1 P := by
  intro h
  obtain ⟨r, hr, a, ha⟩ := hne
  have : (P 0 ∪ P 1).Nonempty := by
    interval_cases r
    · exact ⟨a, Or.inl ha⟩
    · exact ⟨a, Or.inr ha⟩
  exact relaxed_barrier β hβ hβ' l _ (kRelaxedStrategy_one h this)

/-- **Soundness of `k`-memory strategies.**  A `k`-memory relaxed strategy with `P r` nonempty traps a
floor in `[m, m + 3)` for every `m ≡ r (mod 2^k)`, as `trapsResidueClass_of_relaxedStrategy` does for
`k = 0`.  Confidence 95% (the same nested intervals, tracking `m mod 2^k`). -/
theorem trapsResidueClass_of_kRelaxedStrategy {s t l : ℝ} {k r : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (ht : t ≤ 1) (hr : r < 2 ^ k) (h : KRelaxedStrategy s t l k P) (hne : (P r).Nonempty) :
    TrapsResidueClass s t k r := by
  sorry

/-- **Conjecture: memory helps off the symmetric position.**  For the arc `[2/5, 2/5 + 87/100]`
(it wraps), three bits of memory win and no memoryless strategy does.  Confidence 80%.  Evidence:
`solve_vw` wins at `k = 3` (width `87/100 · 86/400`) and loses at `k = 0, 1, 2` for all 132 widths
`87/100 · j/400`, `j = 5, 8, …, 398` (regression `test_memory_helps_off_centre`); bisected shortest arcs at
`s = 2/5` are `0.916, 0.907, 0.841` for `k = 0, 2, 3`, and `s = 1/10, 1/5, 3/10` show smaller gains.
So any proof of `FiniteMemoryRelaxedValue` must use the symmetric arc, not a general reduction. -/
def MemoryHelpsOffCentre : Prop :=
  (∃ (l : ℝ) (P : ℕ → Set ℝ), (∃ r < 2 ^ 3, (P r).Nonempty) ∧ KRelaxedStrategy (2 / 5) (87 / 100) l 3 P) ∧
    ∀ (l : ℝ) (P : Set ℝ), ¬ RelaxedStrategy (2 / 5) (87 / 100) l P

/-- **Conjecture: with full information, every integer part beats `7/57`.**  Every `m ≥ 1` is within
`3` of the integer part of some `ξ` with `‖ξ (3/2)^n‖ ≥ 13/100` for all `n`.  Confidence 80%.
Adversarial digit search beats random sampling only slightly: kills reach `0.1377`
(`obliviousKill_1377`) and stop near `0.1375` (none at `0.137`, `0.1365`, `0.136`), well above
this statement's `13/100`.
Evidence (`experiments/arc_fullinfo.py`): the exact interval tree from `[m, m + 1)` keeps some branch
`0.14`-far for 200 steps for every `m < 200` (worst `m = 175` at `0.1422`, stable from depth 50 to 200),
and for 150 random `m` at each of `10³, 10⁶, 10¹², 10³⁰` the worst `β_m` (depth 150) is `0.138`–`0.142`.
Read with `FiniteMemoryRelaxedValue`: bounded 2-adic memory stops at `7/57`, full knowledge of the
integer part does not, and the gap is the horizon's price. -/
def FullInformationBeatsSevenFiftySevenths : Prop :=
  TrapsResidueClass (13 / 100) (74 / 100) 0 0

/-- **The residue-class route cannot reach a `7/57` barrier.**  If every integer part beats `7/57`
with full information, then the residue-class property (`TrapsResidueClass`, which the `2/3` barrier
uses) holds above `7/57`, so a finite-memory barrier at `7/57` must use the strategy's positional
structure. -/
theorem not_trapsBarrier_of_fullInformation (h : FullInformationBeatsSevenFiftySevenths) :
    ¬ ∀ k r : ℕ, r < 2 ^ k → ¬ TrapsResidueClass (13 / 100) (74 / 100) k r :=
  fun hb => hb 0 0 (by norm_num) h

/-! ### Oblivious kills: one integer part that defeats every memory size -/

/-- **An oblivious kill.**  No `ξ ∈ [M, M + 3)` keeps every `{ξ (3/2)^n}` in `[β, 1 - β]`.  Only
`M mod 2^N` matters for the first `N` steps, so a kill found by a finite search is a fact about a
whole residue class, chosen in advance, with no adaptivity. -/
def ObliviousKill (β : ℝ) (M : ℕ) : Prop :=
  ∀ ξ : ℝ, (M : ℝ) ≤ ξ → ξ < M + 3 → ∃ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) ∉ Set.Icc β (1 - β)

/-- An oblivious kill at `β₀` refutes the residue-class property at every `β ≥ β₀`, for every memory
size `k`, at the class of `M`. -/
theorem not_trapsResidueClass_of_obliviousKill {β₀ β : ℝ} {M : ℕ} (hM : 0 < M) (hβ₀ : β₀ ≤ β)
    (hβ : 0 < β) (h : ObliviousKill β₀ M) (k : ℕ) :
    ¬ TrapsResidueClass β (1 - 2 * β) k (M % 2 ^ k) := by
  intro hT
  obtain ⟨g, hg1, hg2, ξ, -, hfl, hall⟩ := hT M hM rfl
  have h1 : (g : ℝ) ≤ ξ := by
    have := Int.floor_le ξ; rw [hfl] at this; exact_mod_cast this
  have h2 : ξ < g + 1 := by
    have := Int.lt_floor_add_one ξ; rw [hfl] at this; exact_mod_cast this
  have hgM : (M : ℝ) ≤ g := by exact_mod_cast hg1
  have hgM' : (g : ℝ) + 1 ≤ M + 3 := by exact_mod_cast (show g + 1 ≤ M + 3 by omega)
  obtain ⟨n, hn⟩ := h ξ (by linarith) (by linarith)
  obtain ⟨x, hx, hfx⟩ := hall n
  apply hn
  have hx' : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hfx, hx']
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- So an oblivious kill bounds **every** finite memory: no `k`-memory relaxed strategy at any
`β ≥ β₀` is live at the residue of `M`.  (Through `trapsResidueClass_of_kRelaxedStrategy`.) -/
theorem not_kRelaxedStrategy_of_obliviousKill {β₀ β l : ℝ} {M k : ℕ} {P : ℕ → Set ℝ} (hM : 0 < M)
    (hk : 1 ≤ k) (hβ₀ : β₀ ≤ β) (hβ : 0 < β) (h : ObliviousKill β₀ M)
    (hne : (P (M % 2 ^ k)).Nonempty) : ¬ KRelaxedStrategy β (1 - 2 * β) l k P := fun hS =>
  not_trapsResidueClass_of_obliviousKill hM hβ₀ hβ h k
    (trapsResidueClass_of_kRelaxedStrategy hk (by linarith) (Nat.mod_lt _ (by positivity)) hS hne)

/-- **An oblivious kill at `0.138`**, below every random integer part sampled before
(`FullInformationBeatsSevenFiftySevenths` evidence: worst random `β_m ≈ 0.138`).  Every `ξ` in
`[M, M + 3)`, `M = 356318813878270`, has `‖ξ (3/2)^n‖ < 69/500` for some `n ≤ 51`.  Confidence 99%.
Evidence: found by a beam search over the binary digits of `M` (`experiments/arc_oblivious.py`), then
re-checked by the independent exact interval tree `arc_fullinfo.survives` (dies at depth `51`,
survives depth `50`).  A finite rational-interval certificate, a treadmill candidate.  The same
search kills `3/20` (depth `20`), `29/200` (`25`) and `7/50` (`36`); kill depth grows fast as `β`
falls, and below `0.138` the open question is where the oblivious threshold sits. -/
theorem obliviousKill_138 : ObliviousKill (69 / 500) 356318813878270 := by
  sorry

/-- **No finite memory reaches `0.138`** at the class of `356318813878270`: a uniform-in-`k` bound,
where every earlier finite-memory barrier fixed `k`.  So the finite-memory value lies in
`[7/57, 0.138]` for every `k`. -/
theorem not_kRelaxedStrategy_138 {β l : ℝ} {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (hβ : 69 / 500 ≤ β) (hne : (P (356318813878270 % 2 ^ k)).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P :=
  not_kRelaxedStrategy_of_obliviousKill (by norm_num) hk hβ (by linarith) obliviousKill_138 hne

/-- **An oblivious kill at `0.1377`**, the lowest found: every `ξ ∈ [M, M + 3)`,
`M = 31982856860489480190`, has `‖ξ (3/2)^n‖ < 1377/10000` for some `n ≤ 66`.  Confidence 99%.
Evidence: `arc_oblivious.py search 1377/10000 250 20000 1.0`, re-checked by `arc_fullinfo.survives`
(dies at depth 66, survives 65).  Beams of width 20000 find no kill at `0.137`, `0.1365`, `0.136`. -/
theorem obliviousKill_1377 : ObliviousKill (1377 / 10000) 31982856860489480190 := by
  sorry

/-- **No finite memory reaches `0.1377`** at the class of `31982856860489480190`. -/
theorem not_kRelaxedStrategy_1377 {β l : ℝ} {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (hβ : 1377 / 10000 ≤ β) (hne : (P (31982856860489480190 % 2 ^ k)).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P :=
  not_kRelaxedStrategy_of_obliviousKill (by norm_num) hk hβ (by linarith) obliviousKill_1377 hne

/-- **Refuted (90%): every live `k`-strategy is live at every residue.**  This was the original form of
`KRelaxedLiveEverywhere`; the weaker form below (some strategy is live everywhere) is all the kills use.  `not_kRelaxedStrategy_138` needs the
strategy live at the class of one specific `m`, while `FiniteMemoryRelaxedValue` allows any live
residue.  The adversary picks the top bit of each new residue, but the constructor's floor choices
perturb the carries below it (for `k = 2` the low bit is `a + p + c mod 2`, with `c` the constructor's
floor), so a strategy might steer clear of some classes.  Evidence for the strong form at small `k`: the greatest
`solve_vw` fixed points for the off-centre `k = 3` winner (`MemoryHelpsOffCentre`, widths
`87/100 · j/400`, `j = 86, 92`) are live at all 8 residues, and at `j = 80` at none
(regression `test_live_everywhere_off_centre`); no partially live winner has been seen.
Direct test of this statement (2026-10-09, `arc_trap_k.py live-forbid`): start the fixed point with one
class `m` empty, so it computes the largest strategy avoiding `m`.  Over 224 winners (`k = 1, …, 4`; four
symmetric arcs `β = 0.11, …, 0.122` and twelve random off-centre arcs, widths `t · j/400`), forbidding any
single class empties the fixed point every time, within 3 or 4 iterations (a few classes die, then all at
once).  These are emptiness results on the `1/2^20` lattice (the solver rounds inward), so a thin exact
dodge could be missed; the `k = 6` counterexample below is the sound (nonempty, certificate) direction.
Regression `test_forbidding_any_class_kills_the_strategy`.
**Counterexample at `k = 6`**: the off-centre arc `[2/5, 2/5 + 87/100]`, widths `87/100 · j/400`,
`j = 100, 130`, has a strategy live at 63 of the 64 classes, dead only at `27`, and another dead only at
`59` (both `≡ -5 mod 32`).  Each converges in 39 iterations, and 36 true-integer orbit checks
(`vw_orbit`, 60 moves) never get stuck.  The 90% is solver soundness (inward-rounded post-fixed point),
not a Lean certificate.  The same arc's unforbidden fixed point is live at all 64 classes, and over 48
winners at `k = 5, 6` (including the symmetric arcs `β = 0.11, 0.122`) no other class is dodgeable.
Dead route: carry combinatorics alone.  Let the constructor choose the floor `sh ∈ {0, 1, 2}` freely per
residue, with both top-bit children required live.  Then it can keep its live set off any one class, and
off any adjacent pair `{m, m + 1}`, forever, for every `k = 3, …, 14` (a safety-game fixed point).  So a
proof must use the geometry that ties `sh` to the fractional position (`sh = ⌊3u/2 + p/2⌋` with `u` in the
band).  The geometry in fact pins `sh ∈ {0, 1}` on the symmetric arc, yet the carry game with
`sh ∈ {0, 1}` still dodges every class and every adjacent pair from `k = 4`; what the carry game
lacks is that `sh` is a function of the position, not a free choice per residue. -/
def KRelaxedLiveEverywhereStrong : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → KRelaxedStrategy s t l k P →
    (∃ r < 2 ^ k, (P r).Nonempty) → ∀ r < 2 ^ k, (P r).Nonempty

/-- The `k = 6` counterexample above.  Confidence 90%.  Greedy maximal dodge (forbid classes one at a
time while the fixed point stays nonempty): at both `j = 100` and `j = 130` the largest avoidable set is
`{27, 59}`, the two lifts of the single base `-5 mod 32`, and nothing else.  So the dodge is one base
the constructor never lands on (a choice of floor it never needs), not a sparse live set. -/
theorem not_kRelaxedLiveEverywhereStrong : ¬ KRelaxedLiveEverywhereStrong := by
  sorry

/-- **Open: a live `k`-strategy can be made live at every residue.**  The strategies form a family closed
under unions, so this says the greatest one (the union of all) is live everywhere.  Confidence 75%.
Edge scan (2026-10-09): eight arcs (three named, five random), widths `t · j/400` for every even `j`, `k = 3, …, 6`:
2016 winning cases, every greatest fixed point live at all classes, including the widths where memory `k`
first wins (the only place a failure can occur, by `KRelaxedStrategy.lift`).
Every winner measured so far satisfies it: 224 at `k ≤ 4` and 48 at `k = 5, 6` (`arc_trap_k.py
live-forbid`, the unforbidden fixed point), including the `k = 6` arc that refutes the strong form
(`not_kRelaxedLiveEverywhereStrong`).  What a proof must explain is that a dodging strategy is never
maximal. -/
def KRelaxedLiveEverywhere : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → KRelaxedStrategy s t l k P →
    (∃ r < 2 ^ k, (P r).Nonempty) →
      ∃ Q : ℕ → Set ℝ, KRelaxedStrategy s t l k Q ∧ ∀ r < 2 ^ k, (Q r).Nonempty

/-- **Every base is good**: some strategy has, at every base `b < 2^(k-1)`, a common start for both lifts
`b` and `b + 2^(k-1)`.  This is the target set a move must hit (both lifts, since the adversary picks the
top bit), so it is the natural inductive invariant behind `KRelaxedLiveEverywhere`, which it implies
(`KRelaxedAllBasesGood.liveEverywhere`).  Confidence 70%.  Evidence (2026-10-09): every greatest
fixed point among 371 winners (`k = 2, …, 5`; four arcs, `j ≡ 4 mod 6`) has all bases good, and at the
`k = 6` dodge (`not_kRelaxedLiveEverywhereStrong`) the greatest fixed point has all 32 good while the
dodging strategy lacks exactly base `27`.  Mechanism sketch: the start is free, so a class `m` is live
as soon as a move from some `a` reaches a good base `⌊3m/2⌋ + J`, `J ∈ {0, 1}`, and `m ↦ ⌊3m/2⌋` is
exactly two-to-one from `ℤ/2^k` onto `ℤ/2^(k-1)`.
Split-mask probe (2026-10-09, with Astra; `arc_trap_k.split_seeds`): cap the two lifts of a base onto
opposite sides of their shared starts and take the greatest strategy under the cap.  Over `k = 3, 4, 5`
(10 arcs, every 40th width) no result keeps both lifts live without a shared start; every descent
kills a lift outright.  So on the `1/2^20` lattice the only deficiency seen is a whole dead base (the
`k = 6` dodges, eleven seeds on three arcs, each restored by one predecessor layer:
`ArcReview.PredecessorSaturationAllBases`).  Thin (Cantor-like) strategies are invisible to the solver.
Open route to solver completeness at fixed `k` (with Astra, 2026-10-09; hand-reviewed, NOT proved): by
`ArcFattening.LiftedStrategy.fatten` (with the arc widened by `e/2` per end, starts `|z| ≤ e/12`, moves
perturbed by `|q| ≤ e/24`), a winner at `(β, l)` gives winners with positive move and start margins at arc
`β - e0/2` for every width in `[l + e0/2, l + e0]` (`KRelaxedStrategy.mono` for the arc).  So lattice
emptiness of `solve_vw` at every width of a mesh finer than `e0/2` up to `3t'/2` (`t' = t + e0`), on a grid
fine for margins `≍ e0`, would exclude every winner, thin or fat, at `β`.  NOW PROVED end to end
(2026-10-10) as `ArcSolverInclusion.no_kRelaxedStrategy_of_sweep` with `ArcFattening.kToLiftedBridge`
(Astra); the only unproved input is that the solver code contains the abstract rounded step.  Results:
`ArcSolverInclusion.no_kRelaxedStrategy_7_57_plus` (`k ≤ 6`).  Uniform-in-`k` is a separate target.
Solver-inclusion check (2026-10-10, `arc_trap_k.fatten_residue` / `rounded_post_fixed_failures`): the
fattened `k = 3` off-centre winner, converted to residue form (a start pushed below its integer part
moves to residue `r - 1`), is a post-fixed point of the rounded step at `N = 2^20` for `e = 1/100` down to
`10⁻⁶`, and the greatest fixed point contains it; the unfattened winner at the widened parameters is not
post-fixed.  At `N = 2^16` inclusion breaks once `e N / 24` falls to `≈ 0.14`; every case with
`e N / 24 ≥ 1` (the margin bound's regime) passed.  Evidence for the step, on fat strategies only.
How the one-layer repair works (2026-10-09): call a class `c mod 2^j` good at level `j` when all its lifts
mod `2^k` share a start (level `k - 1` is this Prop).  The `k = 6` dodge's dead base `27` moves to bases
`f + J` with `f = ⌊3·27/2⌋`; for `J = 0, 1, 2` the pairs `(8, 24), (9, 25), (10, 26)` are good at level
`k - 2` (all four lifts share a start).  So a SINGLE move serves both dead lifts, and the obligation drops one
level down the ladder rather than closing.  Ladders (good classes mod `2^6, …, 2^0`): greatest fixed point
`64, 32, 16, 8, 4, 2, 1` at `j = 100` but `64, 32, 16, 8, 3, 0, 0` at `j = 130`; dodge `62, 31, 15, 4, 0, 0, 0`.
Dead route: a common core (one interval inside every base's shared starts, level 0).  It is often empty:
the greatest fixed point at `j = 130`, every dodge, and the symmetric `β = 0.11` arc at every `k`.
Dead route: level `k - 2` goodness everywhere (which would make every repair a single move).  In 10 of 233
greatest fixed points (`k = 3, 4, 5`, five arcs) NO class is good at level `k - 2`, though every base is good,
so there the two lifts use different moves and the obligation is `ArcOverlap`'s `|u - v| ≤ l/3`.
That obligation holds with slack: across the same 233, the closest legal landing points of the two lifts
(in `c = 3u/2 + d`, arc band applied) are at most `0.33 l` apart, against the `l/2` allowed.  Dead route:
target density (every shared-start set `l/2`-dense), true in only 21 of 233.
Exact witnesses (`arc_trap_k.py witnesses`, JSON in `experiments/witnesses_*.json`): at `k = 5`, arc
`(23/50, 22/25)`, `j = 40` and `k = 4`, arc `(1/2, 9/10)`, `j = 64` (no class good at level `k - 2`), the
nearest usable pair has the SAME gap at every base (`0.082 l` and `0.019 l`), the same floor for both
lifts, and successor bases exactly `2^(k-2)` apart. -/
def KRelaxedAllBasesGood : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k → KRelaxedStrategy s t l k P →
    (∃ r < 2 ^ k, (P r).Nonempty) →
      ∃ Q : ℕ → Set ℝ, KRelaxedStrategy s t l k Q ∧
        ∀ b < 2 ^ (k - 1), (Q b ∩ Q (b + 2 ^ (k - 1))).Nonempty

theorem KRelaxedAllBasesGood.liveEverywhere (h : KRelaxedAllBasesGood) : KRelaxedLiveEverywhere := by
  intro s t l k P hk hP hne
  obtain ⟨Q, hQ, hg⟩ := h s t l k P hk hP hne
  refine ⟨Q, hQ, fun r hr => ?_⟩
  have hpow : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  rcases lt_or_ge r (2 ^ (k - 1)) with h1 | h1
  · exact (hg r h1).mono Set.inter_subset_left
  · have := (hg (r - 2 ^ (k - 1)) (by omega)).mono Set.inter_subset_right
    rwa [Nat.sub_add_cancel h1] at this

/-- **More memory never hurts**: forgetting the top bit turns a `k`-strategy into a `(k + 1)`-strategy.  The
`(k + 1)` move lands in one specific lift of the `k`-target base, and the `k`-strategy already has both
lifts live.  Confidence 97% (residue arithmetic; `test_awareness_never_hurts` checks it on the solver).
So a counterexample to `KRelaxedLiveEverywhere` can only occur at the least memory that wins: a strategy
live everywhere at `k` lifts to one live everywhere at `k + 1`, and every `k = 0` strategy is live
everywhere. -/
theorem KRelaxedStrategy.lift {s t l : ℝ} {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (h : KRelaxedStrategy s t l k P) : KRelaxedStrategy s t l (k + 1) (fun r => P (r % 2 ^ k)) := by
  sorry

/-- Given `KRelaxedLiveEverywhere`, `FiniteMemoryRelaxedValue` holds on `[0.138, 1/2)` for every `k`. -/
theorem finiteMemoryRelaxedValue_ge_138 (hL : KRelaxedLiveEverywhere) {k : ℕ} (hk : 1 ≤ k) {β : ℝ}
    (hβ : 69 / 500 ≤ β) (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P := fun hS => by
  obtain ⟨Q, hQ, hQl⟩ := hL _ _ _ k P hk hS hne
  exact not_kRelaxedStrategy_138 hk hβ (hQl _ (Nat.mod_lt _ (by positivity))) hQ

/-! ### Relaxed oblivious kills: fixed window width -/

/-- **A relaxed oblivious kill** for window width `l`: no run of the relaxed move, in actual numbers
(integer parts included), starts with a left end in `[M, M + 1)` and lasts forever.  The move keeps
`u ∈ [V, V + l/3]` with `[u, u + 2l/3]` inside a lift of `[β, 1 - β]`, and the next left end is `3u/2`.
This is weaker for the constructor than `ObliviousKill`, which lets it keep whole components. -/
def RelaxedObliviousKill (β l : ℝ) (M : ℕ) : Prop :=
  ¬ ∃ V : ℕ → ℝ, (M : ℝ) ≤ V 0 ∧ V 0 < M + 1 ∧ ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l / 3 ∧
    (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2

/-- **Soundness, path form.**  A `k`-memory relaxed strategy live at the class of `M` runs forever
from some left end in `[M, M + 1)`: play it on the actual integer parts of the orbit, whose residues
it reads.  Confidence 95% (the nested-interval bookkeeping of
`trapsResidueClass_of_kRelaxedStrategy`, without passing to the limit point). -/
theorem exists_relaxedPath_of_kRelaxedStrategy {β l : ℝ} {k M : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (h : KRelaxedStrategy β (1 - 2 * β) l k P) (hne : (P (M % 2 ^ k)).Nonempty) :
    ∃ V : ℕ → ℝ, (M : ℝ) ≤ V 0 ∧ V 0 < M + 1 ∧ ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l / 3 ∧
      (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2 := by
  sorry

/-- A relaxed oblivious kill at width `l` defeats every memory size at that width. -/
theorem not_kRelaxedStrategy_of_relaxedObliviousKill {β l : ℝ} {k M : ℕ} {P : ℕ → Set ℝ}
    (hk : 1 ≤ k) (h : RelaxedObliviousKill β l M) (hne : (P (M % 2 ^ k)).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P := fun hS =>
  h (exists_relaxedPath_of_kRelaxedStrategy hk hS hne)

/-- **A relaxed oblivious kill at `β = 1/8`, `l = 1/8`**, the memoryless optimum's width and far
below the component-game threshold `≈ 0.1375`: from `M = 604160` every relaxed run dies within 22
moves.  Confidence 99%.  Evidence: beam search over the digits of `M` (`arc_oblivious.py`
relaxed mode), and an independent check in this file's own residue bookkeeping (state `(r mod 2^K, a)`,
the `KRelaxedStrategy` update), which dies at depth 22, while `M + 1` and `β = 0.12` survive. -/
theorem relaxedObliviousKill_1_8 : RelaxedObliviousKill (1 / 8) (1 / 8) 604160 := by
  sorry

/-- **No finite memory holds `[1/8, 7/8]` at width `1/8`** (at the class of `604160`), for every `k`. -/
theorem not_kRelaxedStrategy_1_8_width_1_8 {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (hne : (P (604160 % 2 ^ k)).Nonempty) :
    ¬ KRelaxedStrategy (1 / 8) (1 - 2 * (1 / 8)) (1 / 8) k P :=
  not_kRelaxedStrategy_of_relaxedObliviousKill hk relaxedObliviousKill_1_8 hne

/-- **A relaxed oblivious kill `10⁻⁴` above `7/57`**, at width `3/20`: from `M = 13187072` every
relaxed run for `[0.1229, 0.8771]` dies within 25 moves.  Confidence 99%.  Evidence:
`arc_oblivious.py relaxed`, re-checked by `relaxed_check` (dies at 25; `M + 1` and `β = 0.12` survive).
At `β = 0.1229` widths `3/20` and `1/5` die this way; `1/8` and `1/10` gave no kill within 300 s of
beam (width 2000).  As `l → 0` the relaxed game tends to the component game, whose oblivious kills
stop near `0.1375`, so oblivious kills alone cannot settle `FiniteMemoryRelaxedValue` at small widths. -/
theorem relaxedObliviousKill_1229_width_3_20 :
    RelaxedObliviousKill (1229 / 10000) (3 / 20) 13187072 := by
  sorry

/-- **No finite memory holds `[0.1229, 0.8771]` at width `3/20`** (at the class of `13187072`). -/
theorem not_kRelaxedStrategy_1229_width_3_20 {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (hne : (P (13187072 % 2 ^ k)).Nonempty) :
    ¬ KRelaxedStrategy (1229 / 10000) (1 - 2 * (1229 / 10000)) (3 / 20) k P :=
  not_kRelaxedStrategy_of_relaxedObliviousKill hk relaxedObliviousKill_1229_width_3_20 hne

/-! ### Component kills from a narrow start cover every small width -/

/-- An oblivious kill from the start window `[M, M + w)`.  `ObliviousKill β M` is `w = 3`. -/
def ObliviousKillFrom (β w : ℝ) (M : ℕ) : Prop :=
  ∀ ξ : ℝ, (M : ℝ) ≤ ξ → ξ < M + w → ∃ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) ∉ Set.Icc β (1 - β)

/-- **A relaxed run traps a point.**  The kept sub-windows `[u_n, u_n + 2l/3]` pulled back by
`(2/3)^n` are nested compact intervals, so some `ξ ∈ [M, M + 1 + l)` has every `ξ (3/2)^n` in
`[u_n, u_n + 2l/3]`, inside a lift of `[β, 1 - β]`.  Confidence 97% (nested intervals). -/
theorem exists_trapped_of_relaxedPath {β l : ℝ} {M : ℕ} (hl : 0 < l) (V : ℕ → ℝ)
    (h0 : (M : ℝ) ≤ V 0) (h1 : V 0 < M + 1) (hV : ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l / 3 ∧
      (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2) :
    ∃ ξ : ℝ, (M : ℝ) ≤ ξ ∧ ξ < M + 1 + l ∧ ∀ n, Int.fract (ξ * (3 / 2) ^ n) ∈ Set.Icc β (1 - β) := by
  sorry

/-- So a component kill from `[M, M + 1 + l₀)` is a relaxed oblivious kill at every width
`0 < l ≤ l₀`: one certificate for the whole small-width range, where relaxed kills alone fail. -/
theorem relaxedObliviousKill_of_obliviousKillFrom {β l l₀ : ℝ} {M : ℕ} (hl : 0 < l) (hll : l ≤ l₀)
    (h : ObliviousKillFrom β (1 + l₀) M) : RelaxedObliviousKill β l M := by
  rintro ⟨V, h0, h1, hV⟩
  obtain ⟨ξ, hξ0, hξ1, hall⟩ := exists_trapped_of_relaxedPath hl V h0 h1 hV
  obtain ⟨n, hn⟩ := h ξ hξ0 (by linarith)
  exact hn (hall n)

/-- A relaxed oblivious kill for every width in `[l₁, l₂]` at once: the run may spread by `l₂/3` but
must keep the margin `2l₁/3`, so each width's runs are runs here. -/
def RelaxedObliviousKillRange (β l₁ l₂ : ℝ) (M : ℕ) : Prop :=
  ¬ ∃ V : ℕ → ℝ, (M : ℝ) ≤ V 0 ∧ V 0 < M + 1 ∧ ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l₂ / 3 ∧
    (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l₁ / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2

theorem RelaxedObliviousKillRange.kill {β l₁ l₂ l : ℝ} {M : ℕ} (h : RelaxedObliviousKillRange β l₁ l₂ M)
    (h₁ : l₁ ≤ l) (h₂ : l ≤ l₂) : RelaxedObliviousKill β l M := by
  rintro ⟨V, h0, h1, hV⟩
  refine h ⟨V, h0, h1, fun n => ?_⟩
  obtain ⟨u, hu1, hu2, ⟨j, hj1, hj2⟩, hn⟩ := hV n
  exact ⟨u, hu1, by linarith, ⟨j, hj1, by linarith⟩, hn⟩

/-- Relaxed strategies only get easier on a longer arc. -/
theorem KRelaxedStrategy.mono {β β₀ l : ℝ} {k : ℕ} {P : ℕ → Set ℝ} (hβ : β₀ ≤ β)
    (h : KRelaxedStrategy β (1 - 2 * β) l k P) : KRelaxedStrategy β₀ (1 - 2 * β₀) l k P := by
  refine ⟨h.1, h.2.1, fun r hr a ha => ?_⟩
  obtain ⟨u, h1, h2, ⟨j, hj1, hj2⟩, h4⟩ := h.2.2 r hr a ha
  exact ⟨u, h1, h2, ⟨j, by linarith, by linarith⟩, h4⟩

/-- The window width of a live relaxed strategy fits in the arc: `2l/3 ≤ t`. -/
theorem KRelaxedStrategy.width_le {s t l : ℝ} {k r : ℕ} {P : ℕ → Set ℝ} (hr : r < 2 ^ k)
    (h : KRelaxedStrategy s t l k P) (hne : (P r).Nonempty) : 2 * l / 3 ≤ t := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨u, -, -, ⟨j, hj1, hj2⟩, -⟩ := h.2.2 r hr a ha
  linarith

/-- **Certificate 1 at `0.13`** (small widths): every `ξ ∈ [M, M + 3/2)`, `M = 13060715579013119`,
has `‖ξ (3/2)^n‖ < 0.13` for some `n ≤ 56`.  Confidence 99%: `arc_oblivious.py search 13/100 200
10000 1.0 3/2`, re-checked by `arc_fullinfo.survives` (dies at 56, survives 55).  Note the start
width: from `[M, M + 3)` component kills stop near `0.1375`, from `[M, M + 1)` they reach `0.13`. -/
theorem obliviousKillFrom_013 : ObliviousKillFrom (13 / 100) (3 / 2) 13060715579013119 := by
  sorry

/-- **Certificate 2 at `0.13`**: widths `[1/2, 3/4]` from `M = 2^20` die within 5 moves.  Confidence
99%: `arc_oblivious.py relaxed`, re-checked by `relaxed_check` (depth 5). -/
theorem relaxedObliviousKillRange_013_a : RelaxedObliviousKillRange (13 / 100) (1 / 2) (3 / 4) 1048576 := by
  sorry

/-- **Certificate 3 at `0.13`**: widths `[3/4, 111/100]` from `M = 2^20 + 8` die within 7 moves.
Confidence 99%: `arc_oblivious.py relaxed`, re-checked by `relaxed_check` (depth 7). -/
theorem relaxedObliviousKillRange_013_b :
    RelaxedObliviousKillRange (13 / 100) (3 / 4) (111 / 100) 1048584 := by
  sorry

/-- **No finite memory reaches `0.13`.**  Given that some strategy is live at every residue
(`KRelaxedLiveEverywhere`), `FiniteMemoryRelaxedValue` holds on `[0.13, 1/2)` for every `k`.  Three
oblivious certificates cover every window width: one component kill from `[M, M + 3/2)` for
`l ≤ 1/2` (through `exists_trapped_of_relaxedPath`), two relaxed range kills for `[1/2, 3/4]` and
`[3/4, 1.11]`, and `l > 1.11` cannot fit the arc.  So the finite-memory value lies in `[7/57, 0.13]`
for every `k`, where full information reaches `0.14` for typical integer parts. -/
theorem finiteMemoryRelaxedValue_ge_013 (hL : KRelaxedLiveEverywhere) {k : ℕ} (hk : 1 ≤ k) {β : ℝ}
    (hβ : 13 / 100 ≤ β) (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P := by
  intro hS
  obtain ⟨Q, h0, hQl⟩ := hL _ _ _ k P hk (hS.mono hβ) hne
  have hl : 0 < l := hS.1
  have live : ∀ M : ℕ, (Q (M % 2 ^ k)).Nonempty := fun M =>
    hQl _ (Nat.mod_lt _ (by positivity))
  have hw : 2 * l / 3 ≤ 1 - 2 * (13 / 100 : ℝ) := by
    exact h0.width_le (pow_pos (by norm_num) k) (hQl 0 (pow_pos (by norm_num) k))
  rcases le_or_gt l (1 / 2) with h1 | h1
  · exact not_kRelaxedStrategy_of_relaxedObliviousKill hk
      (relaxedObliviousKill_of_obliviousKillFrom (l₀ := 1 / 2) hl h1
        (show ObliviousKillFrom (13 / 100) (1 + 1 / 2) 13060715579013119 by
          norm_num; exact obliviousKillFrom_013)) (live _) h0
  rcases le_or_gt l (3 / 4) with h2 | h2
  · exact not_kRelaxedStrategy_of_relaxedObliviousKill hk
      (relaxedObliviousKillRange_013_a.kill h1.le h2) (live _) h0
  · exact not_kRelaxedStrategy_of_relaxedObliviousKill hk
      (relaxedObliviousKillRange_013_b.kill h2.le (by linarith)) (live _) h0

/-! ### Receding horizon: narrow-start kills, no liveness hypothesis -/

/-- An oblivious kill within `D` moves from the closed window `[N + c, N + c + w]`. -/
def ObliviousKillAt (β c w : ℝ) (N : ℤ) (D : ℕ) : Prop :=
  ∀ η : ℝ, (N : ℝ) + c ≤ η → η ≤ N + c + w → ∃ n ≤ D, Int.fract (η * (3 / 2) ^ n) ∉ Set.Icc β (1 - β)

/-- Shifting by a multiple of `2^D` leaves the first `D` fractional parts alone. -/
theorem fract_three_halves_pow_add (η : ℝ) (j : ℤ) {n D : ℕ} (h : n ≤ D) :
    Int.fract ((η + 2 ^ D * j) * (3 / 2) ^ n) = Int.fract (η * (3 / 2) ^ n) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (η + 2 ^ (n + e) * j) * (3 / 2) ^ n = η * (3 / 2) ^ n + ((3 ^ n * 2 ^ e * j : ℤ) : ℝ) := by
    push_cast; rw [pow_add, div_pow]; field_simp
  rw [this, Int.fract_add_intCast]

/-- **Soundness from a chosen start.**  Playing a `k`-memory relaxed strategy on the actual integer
parts from `M + a`, `a ∈ P (M mod 2^k)`, runs forever.  Confidence 95% (the bookkeeping of
`exists_relaxedPath_of_kRelaxedStrategy`, which starts the same way). -/
theorem exists_relaxedPath_from_mem {β l : ℝ} {k M : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (h : KRelaxedStrategy β (1 - 2 * β) l k P) {a : ℝ} (ha : a ∈ P (M % 2 ^ k)) :
    ∃ V : ℕ → ℝ, V 0 = M + a ∧ ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l / 3 ∧
      (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2 := by
  sorry

/-- **A relaxed run traps a point within `l` of its start** (the nested intervals of
`exists_trapped_of_relaxedPath`: the first kept window is `[u₀, u₀ + 2l/3] ⊆ [V 0, V 0 + l]`).
Confidence 97%. -/
theorem exists_trapped_of_relaxedPath_from {β l : ℝ} (hl : 0 < l) (V : ℕ → ℝ)
    (hV : ∀ n, ∃ u : ℝ, V n ≤ u ∧ u ≤ V n + l / 3 ∧
      (∃ j : ℤ, (j : ℝ) + β ≤ u ∧ u + 2 * l / 3 ≤ j + 1 - β) ∧ V (n + 1) = 3 * u / 2) :
    ∃ ξ : ℝ, V 0 ≤ ξ ∧ ξ ≤ V 0 + l ∧ ∀ n, Int.fract (ξ * (3 / 2) ^ n) ∈ Set.Icc β (1 - β) := by
  sorry

/-- `3^k` is invertible mod `2^D`. -/
theorem exists_three_pow_mul_eq (k D : ℕ) (N : ℤ) : ∃ M' : ℕ, ∃ j : ℤ, (3 : ℤ) ^ k * M' = N + 2 ^ D * j := by
  have hc : Nat.Coprime 3 (2 ^ D) := Nat.Coprime.pow_right _ (by norm_num)
  set u : (ZMod (2 ^ D))ˣ := ZMod.unitOfCoprime 3 hc ^ k with hu
  have hu3 : ((u : (ZMod (2 ^ D))ˣ) : ZMod (2 ^ D)) = 3 ^ k := by
    rw [hu, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]; push_cast; rfl
  refine ⟨((N : ZMod (2 ^ D)) * ↑u⁻¹).val, ?_⟩
  have h0 : (((3 : ℤ) ^ k * (((N : ZMod (2 ^ D)) * ↑u⁻¹).val : ℕ) - N : ℤ) : ZMod (2 ^ D)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ← hu3, mul_left_comm, Units.mul_inv, mul_one, sub_self]
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  exact ⟨j, by push_cast at hj; linarith⟩

/-- **Receding horizon.**  Against a `k`-memory relaxed strategy of width `l`, the adversary fixes the
low `k` digits to a live residue `r`, sees the start `a ∈ P r`, and only then chooses the higher digits.
The trapped point satisfies `ξ (3/2)^k ∈ 3^k M' + (r + a)(3/2)^k + [0, l (3/2)^k]`, and `3^k M'` reaches
every class mod `2^D`, so oblivious kills from narrow windows at every offset finish it.  No
`KRelaxedLiveEverywhere`: the adversary chooses which live residue to play. -/
theorem not_kRelaxedStrategy_of_narrowKills {β l w : ℝ} {k : ℕ} {P : ℕ → Set ℝ} (hk : 1 ≤ k)
    (hkill : ∀ c : ℝ, ∃ N : ℤ, ∃ D : ℕ, ObliviousKillAt β c w N D) (hw : l * (3 / 2) ^ k ≤ w)
    (hne : ∃ r < 2 ^ k, (P r).Nonempty) : ¬ KRelaxedStrategy β (1 - 2 * β) l k P := by
  intro hS
  obtain ⟨r, hr, a, ha⟩ := hne
  obtain ⟨N, D, hK⟩ := hkill ((r + a) * (3 / 2) ^ k)
  obtain ⟨M', j, hj⟩ := exists_three_pow_mul_eq k D N
  have hM : (r + 2 ^ k * M') % 2 ^ k = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  obtain ⟨V, hV0, hV⟩ := exists_relaxedPath_from_mem (M := r + 2 ^ k * M') hk hS (hM ▸ ha)
  obtain ⟨ξ, hξ0, hξ1, hall⟩ := exists_trapped_of_relaxedPath_from hS.1 V hV
  have hjR : (3 : ℝ) ^ k * M' = N + 2 ^ D * j := by exact_mod_cast hj
  have h32 : (2 : ℝ) ^ k * (3 / 2) ^ k = 3 ^ k := by rw [div_pow]; field_simp
  have hpos : (0 : ℝ) ≤ (3 / 2) ^ k := by positivity
  set η := ξ * (3 / 2) ^ k - 2 ^ D * j with hη
  have hξη : ξ * (3 / 2) ^ k = η + 2 ^ D * j := by rw [hη]; ring
  push_cast at hV0
  have key : ξ * (3 / 2) ^ k = (N : ℝ) + (r + a) * (3 / 2) ^ k + 2 ^ D * j +
      (ξ - (r + 2 ^ k * M' + a)) * (3 / 2) ^ k := by
    have : (2 : ℝ) ^ k * M' * (3 / 2) ^ k = N + 2 ^ D * j := by rw [← hjR, ← h32]; ring
    linear_combination this
  have hδ0 : 0 ≤ (ξ - (r + 2 ^ k * M' + a)) * (3 / 2) ^ k :=
    mul_nonneg (by rw [hV0] at hξ0; linarith) hpos
  have hδ1 : (ξ - (r + 2 ^ k * M' + a)) * (3 / 2) ^ k ≤ l * (3 / 2) ^ k :=
    mul_le_mul_of_nonneg_right (by rw [hV0] at hξ1; linarith) hpos
  obtain ⟨n, hn, hout⟩ := hK η (by linarith) (by linarith)
  apply hout
  rw [← fract_three_halves_pow_add η j hn, ← hξη, mul_assoc, ← pow_add]
  exact hall (k + n)

/-- Kills shrink with their window. -/
theorem ObliviousKillAt.mono {β c w c' w' : ℝ} {N N' : ℤ} {D : ℕ} (h : ObliviousKillAt β c w N D)
    (h₁ : (N : ℝ) + c ≤ N' + c') (h₂ : (N' : ℝ) + c' + w' ≤ N + c + w) : ObliviousKillAt β c' w' N' D :=
  fun η h₃ h₄ => h η (by linarith) (by linarith)

/-- **Eight narrow kills `10⁻⁴` above `7/57`**: for `i < 8`, every `η ∈ [m_i + i/8, m_i + i/8 + 1/4]`
has `‖η (3/2)^n‖ < 0.1229` for some `n ≤ D_i`, with `m = 568234, 58965761, 1077873, 17399807417632,
1019278, 8143102, 480341, 3` and `D = 21, 27, 22, 47, 22, 27, 21, 4`.  Confidence 99%:
`arc_oblivious.py search 0.1229 150 2000 1.0 1/4 i/8`, re-checked on closed windows by
`arc_fullinfo.survives` (`test_tiles_1229`).  Start width is everything: from width `1/4` kills reach
`0.1229` at every offset, from width `1/2` at offsets `0, 1/2` they stop between `0.1229` and
`0.1235`, from width `1` near `0.128`, from width `3` near `0.1375`.  At `0.12285` the tile at offset
`3/8` gave no kill (beam 2000, depth 150). -/
theorem obliviousKillAt_1229_tiles (i : ℕ) (hi : i < 8) :
    ObliviousKillAt (1229 / 10000) (i / 8) (1 / 4)
      (![568234, 58965761, 1077873, 17399807417632, 1019278, 8143102, 480341, 3] ⟨i, hi⟩)
      (![21, 27, 22, 47, 22, 27, 21, 4] ⟨i, hi⟩) := by
  sorry

/-- The eight tiles cover every offset with a window of width `1/9`. -/
theorem obliviousKillAt_1229 (c : ℝ) : ∃ N : ℤ, ∃ D : ℕ, ObliviousKillAt (1229 / 10000) c (1 / 9) N D := by
  have hf0 := Int.fract_nonneg c
  have hf1 := Int.fract_lt_one c
  have hz0 : 0 ≤ ⌊8 * Int.fract c⌋ := Int.floor_nonneg.2 (by positivity)
  have hz8 : ⌊8 * Int.fract c⌋ < 8 := Int.floor_lt.2 (by push_cast; linarith)
  have hzl : (⌊8 * Int.fract c⌋ : ℝ) ≤ 8 * Int.fract c := Int.floor_le _
  have hzu : 8 * Int.fract c < ⌊8 * Int.fract c⌋ + 1 := Int.lt_floor_add_one _
  set i := (⌊8 * Int.fract c⌋).toNat with hi
  have hiz : ((i : ℤ) : ℝ) = (⌊8 * Int.fract c⌋ : ℝ) := by rw [hi, Int.toNat_of_nonneg hz0]
  push_cast at hiz
  have hi8 : i < 8 := by omega
  have hc : c = ⌊c⌋ + Int.fract c := (Int.floor_add_fract c).symm
  obtain ⟨N, D, T⟩ : ∃ N : ℤ, ∃ D : ℕ, ObliviousKillAt (1229 / 10000) (i / 8) (1 / 4) N D :=
    ⟨_, _, obliviousKillAt_1229_tiles i hi8⟩
  refine ⟨N - ⌊c⌋, D, T.mono ?_ ?_⟩
  · push_cast; linarith
  · push_cast; linarith

/-- **No finite memory holds `[0.1229, 0.8771]` at small width**: for every `k`, a `k`-memory relaxed
strategy needs `l (3/2)^k > 1/9`.  Unconditional (no `KRelaxedLiveEverywhere`), modulo the two bridges
and the tile certificate.  The gap left at `0.1229`: widths `(1/9)(2/3)^k < l`, below the relaxed
kills' `3/20` (`relaxedObliviousKill_1229_width_3_20`). -/
theorem not_kRelaxedStrategy_1229_small_width {k : ℕ} (hk : 1 ≤ k) {β l : ℝ} (hβ : 1229 / 10000 ≤ β)
    (hl : l * (3 / 2) ^ k ≤ 1 / 9) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ KRelaxedStrategy β (1 - 2 * β) l k P := fun hS =>
  not_kRelaxedStrategy_of_narrowKills hk obliviousKillAt_1229 hl hne (hS.mono hβ)

end CollatzMoonshot.Benchmark.ArcTrap
