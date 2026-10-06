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

/-- **Near-AFS density theorem.**  If runs of length `R` cost less than the slack,
`(3/2)^(R+1) |δ| + |δ| < 1/6`, then at least as many integer parts below `2^N` are trapped to
depth `N` in the shifted arc as there are binary words of length `N` with no run longer than `R`.
Confidence 85%.  Proof: start from the piece `g + [0, 1/3 + δ]` (errors `0, δ`).  Under the run
bound every error is at most `(3/2)^R |δ|`, so every step obeys the recursion's conditions.  The nested
pieces are nonempty, and they stay in `[g, g + 1)`.  The anchor-parity map is a bijection from
`g mod 2^N` onto words.
With `run_bounded_count_ge` this gives density `≥ (1 - 2^{-R})^N`, where
`2^{-R} ≍ |δ|^{1/log₂(3/2)} = |δ|^{1.7095…}`.  So a typical integer part lives at least
`~|δ|^{-1.71}` steps.  The worst one lives only `~log_{3/2}(1/|δ|)` steps (`near_afs_every_floor`). -/
theorem near_afs_density (δ : ℝ) (R N : ℕ) (hR : (3 / 2) ^ (R + 1) * |δ| + |δ| < 1 / 6) :
    Nat.card {w : Fin N → Bool // NoRunLonger R N w} ≤
      Nat.card {g : Fin (2 ^ N) // TrapsToDepth (2 / 3 + δ) (2 / 3) N g} := by
  sorry

/-- **Every integer part survives `~log_{3/2}(1/|δ|)` steps near the AFS arc.**  Confidence 90%.
Proof: the recursion of `near_afs_density` with `R = N`; no word of length `N` has a longer run.
The component game shows this is the right order: from `[0, 3]` the adversary kills at exactly
depth `8 + k` at `δ = ±(1/30)(2/3)^k`, `k = 0..8` (from the AFS
window `[0, 1/2]`: `7 + k` and `6 + k`) (`arc_entropy.py` `test_adversarial_depth_ladder`). -/
theorem near_afs_every_floor (δ : ℝ) (N g : ℕ) (hN : (3 / 2) ^ (N + 1) * |δ| + |δ| < 1 / 6) :
    TrapsToDepth (2 / 3 + δ) (2 / 3) N g := by
  sorry

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

/-- Short runs never break the piece.  Confidence 90% (the core of `near_afs_density`).  Proof:
each coordinate is `0`, `δ` or `δ (3/2)^j` with `j` at most the length of the run it is growing in.
So `|3e/2 - δ| ≤ (3/2)^(R+1) |δ| + |δ| < 1/6` at every step. -/
theorem afsUnbroken_of_noRunLonger (δ : ℝ) (R N : ℕ) (hR : (3 / 2) ^ (R + 1) * |δ| + |δ| < 1 / 6)
    (w : Fin N → Bool) (hw : NoRunLonger R N w) : AfsUnbroken δ N w := by
  sorry

/-- A flip followed by `m` equal letters always breaks the piece, once
`|δ| ((3/2)^m - 1) > 1/3`.  Confidence 90%.  Proof: reading `w b` resets the coordinate that the run
then grows to `δ`.  At the `j`-th letter of the run the check reads `3e/2 - δ = δ((3/2)^j - 1)`, and
the continuation window is `[-1/3, 1/3]`. -/
theorem not_afsUnbroken_of_long_run (δ : ℝ) (m N : ℕ) (hm : 1 / 3 < |δ| * ((3 / 2) ^ m - 1))
    (hm1 : 1 ≤ m) (w : Fin N → Bool) (b : ℕ) (hb : b + m < N) (hflip : w ⟨b, by omega⟩ ≠ w ⟨b + 1, by omega⟩)
    (hrun : ∀ j (hj : 1 ≤ j ∧ j ≤ m), w ⟨b + j, by omega⟩ = w ⟨b + 1, by omega⟩) :
    ¬ AfsUnbroken δ N w := by
  sorry

/-- **The AFS rigidity breaks at rate `Θ(|δ|^{1/log₂(3/2)})`, up to a logarithm.**  The words that
keep the AFS piece unbroken for `N` steps number between the run-bounded words
(`afsUnbroken_of_noRunLonger`, `run_bounded_count_ge`: at least `2^N (1 - 2^{-R})^N`) and
`2^N (1 - 2^{-m})^{⌊N/(m+1)⌋}`.  Here `R` and `m` are both `log_{3/2}(1/|δ|) + O(1)`.
Confidence 90%.  Proof of the upper bound: cut the positions into `⌊N/(m+1)⌋` disjoint blocks of
length `m + 1`.  In each block the pattern "flip, then `m` equal letters" has probability `2^{-m}`
independently, and any occurrence breaks the piece (`not_afsUnbroken_of_long_run`).
Checked exhaustively at `δ = 1/30` (`R = 2`, `m = 6`), `N = 8, 12, 14` (`test_afs_event_rate_bounds`). -/
theorem card_afsUnbroken_le (δ : ℝ) (m N : ℕ) (hm : 1 / 3 < |δ| * ((3 / 2) ^ m - 1)) :
    (Nat.card {w : Fin N → Bool // AfsUnbroken δ N w} : ℝ) ≤
      2 ^ N * (1 - (1 / 2) ^ m) ^ (N / (m + 1)) := by
  sorry

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
