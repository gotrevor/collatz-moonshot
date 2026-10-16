/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap

/-!
# The rational members of the Wythoff family: traps, parity chains, a solved mirror

The Wythoff (Beatty-merge) family `W_α(2k) = ⌊kα⌋`, `W_α(2k−1) = ⌊kβ⌋`, `1/α + 1/β = 1`,
passes through `U` at `α = 3` (research note `wythoff`).  At a rational `r = p/q > 1`
(`s = r/(r−1) = p/(p−q)`, `R := p − q`) the two one-sided limits are the maps

* `W_{r+}(2k) = ⌊kr⌋`,      `W_{r+}(2k−1) = ⌈ks⌉ − 1`,
* `W_{r−}(2k) = ⌈kr⌉ − 1`,  `W_{r−}(2k−1) = ⌊ks⌋`.

We define them on all of `ℤ` by the same formulas (`wythoff`), where each is a permutation
(`wythoffPerm`, explicit inverse `wythoffInv`) preserving `ℕ⁺`, and affine on residue classes:
`W(n + 2qm) = W n + pm` for even `n`, `W(n + 2Rm) = W n + pm` for odd `n`.  So every result about
`ℕ⁺` is a result about the restriction, and `AmusicalTrap`'s orbit notions apply verbatim.

1. **Lemma 1 (image parities).**  For even `p` coprime to `q`, among the `q` even-branch images
   `W(2t)`, `t < q`, exactly `(q+1)/2` (`+`) or `(q−1)/2` (`−`) are even; among the `R` odd-branch
   images `W(2u+1)`, `u < R`, exactly `(R−1)/2` (`+`) or `(R+1)/2` (`−`).  Proof: `t ↦ q − t`.
2. **The parity chains** `fwdProb`, `bwdProb` read off Lemma 1 (Theorem M, in
   `WythoffRationalMarkov`, says the parity itineraries follow them exactly).
3. **Theorem T.**  A parity class is forward-invariant under `W_{p/q±}` iff `p` is even, the side
   is `+`, and `q = 1` or `R = 1`; equivalently (even `p`) the chains have an absorbing state.
4. **Theorem E** (`r = 2j ≥ 4`, `+`).  `{1}` is the only finite orbit in `ℕ⁺`; every other orbit
   meets `E = 2ℕ⁺ ∖ 2jℕ⁺` exactly once, at its minimum; infinitely many infinite orbits (the
   evens are a trap with entry set `E`).
5. **Theorem E′** (`r = 2j/(2j−1)`, `+`).  `W_{r+}(n) = W_{2j+}(n+1) − 1` on `ℤ`; so no finite
   orbit in `ℕ⁺`, orbit minima are `E − 1`, infinitely many infinite orbits.
6. **Prop D (drift ordering).**  The stationary laws of the chains tilt the forward and backward
   log-drifts above the i.i.d. drifts on the `+` side and below them on the `−` side.

Theorem C of the note (the density ceiling `≤ c_M`) is not stated here: it needs natural
densities and Markov-walk survival constants (≈ 800+ lines).
-/

namespace CollatzMoonshot.WythoffRational

open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits
  infinitelyManyInfiniteOrbits_of_trap)

/-! ## The maps -/

/-- Which one-sided limit of the Beatty family at `r = p/q`. -/
inductive Side
  | plus
  | minus
  deriving DecidableEq, Repr

/-- `W_{p/q±}` on `ℤ` (`Int.ediv` floors, the divisors being positive when `0 < q < p`):
`+`: `2k ↦ ⌊kp/q⌋`, `2k − 1 ↦ ⌊(kp − 1)/R⌋`; `−`: `2k ↦ ⌊(kp − 1)/q⌋`, `2k − 1 ↦ ⌊kp/R⌋`. -/
def wythoff : Side → ℕ → ℕ → ℤ → ℤ
  | .plus, p, q, n =>
    if n % 2 = 0 then n / 2 * p / q else ((n + 1) / 2 * p - 1) / ((p : ℤ) - q)
  | .minus, p, q, n =>
    if n % 2 = 0 then (n / 2 * p - 1) / q else (n + 1) / 2 * p / ((p : ℤ) - q)

/-- The inverse of `wythoff`.  `+`: with `k = ⌈mq/p⌉` (the multiple `kp` of `p` in
`[mq, mq + p)`), `m` is an even-branch value iff `kp < mq + q`, with preimage `2k`; otherwise its
preimage is `2(m + 1 − k) − 1`.  `−`: the same with `k = ⌊mq/p⌋ + 1` and `kp ≤ mq + q`. -/
def wythoffInv : Side → ℕ → ℕ → ℤ → ℤ
  | .plus, p, q, m =>
    if ((m * q + p - 1) / p) * p - m * q < q then 2 * ((m * q + p - 1) / p)
    else 2 * (m + 1 - (m * q + p - 1) / p) - 1
  | .minus, p, q, m =>
    if (m * q / p + 1) * p - m * q ≤ q then 2 * (m * q / p + 1)
    else 2 * (m + 1 - (m * q / p + 1)) - 1


/-! ## Branch helpers -/

section Helpers

/-- Floor division characterized by its bracket. -/
theorem ediv_eq_iff {a d m : ℤ} (hd : 0 < d) : a / d = m ↔ m * d ≤ a ∧ a < m * d + d := by
  rw [show m * d + d = (m + 1) * d by ring, ← Int.le_ediv_iff_mul_le hd,
    ← Int.ediv_lt_iff_lt_mul hd]
  omega

/-- Positivity of a floor quotient. -/
theorem ediv_pos_iff' {a d : ℤ} (hd : 0 < d) : 0 < a / d ↔ d ≤ a := by
  rw [show (0 : ℤ) < a / d ↔ 1 ≤ a / d by omega, Int.le_ediv_iff_mul_le hd, one_mul]

variable {p q : ℕ}

theorem wythoff_plus_even (k : ℤ) : wythoff .plus p q (2 * k) = k * p / q := by
  rw [wythoff, if_pos (by omega), show 2 * k / 2 = k by omega]

theorem wythoff_plus_odd (k : ℤ) :
    wythoff .plus p q (2 * k - 1) = (k * p - 1) / ((p : ℤ) - q) := by
  rw [wythoff, if_neg (by omega), show (2 * k - 1 + 1) / 2 = k by omega]

theorem wythoff_minus_even (k : ℤ) : wythoff .minus p q (2 * k) = (k * p - 1) / q := by
  rw [wythoff, if_pos (by omega), show 2 * k / 2 = k by omega]

theorem wythoff_minus_odd (k : ℤ) :
    wythoff .minus p q (2 * k - 1) = k * p / ((p : ℤ) - q) := by
  rw [wythoff, if_neg (by omega), show (2 * k - 1 + 1) / 2 = k by omega]

theorem wythoffInv_plus_eq {m k : ℤ} (hk : (m * q + p - 1) / p = k) :
    wythoffInv .plus p q m = if k * p - m * q < q then 2 * k else 2 * (m + 1 - k) - 1 := by
  subst hk; rfl

theorem wythoffInv_minus_eq {m k : ℤ} (hk : m * q / p = k - 1) :
    wythoffInv .minus p q m = if k * p - m * q ≤ q then 2 * k else 2 * (m + 1 - k) - 1 := by
  simp only [wythoffInv, hk, sub_add_cancel]

theorem even_or_odd_two_mul (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k - 1 :=
  ⟨(n + 1) / 2, by omega⟩

end Helpers

section Bijection

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  `wythoffInv` is a left inverse.  Paper proof: the one-sided Beatty partition
of `ℤ` (wythoff note P1): the multiple of `p` in `[mq, mq + p)` lies in `[mq, mq + q)` (even
branch hits `m`) or in `[mq + q, mq + p)` (odd branch hits `m`, reflected by `kp ↦ (m+1)p − kp`);
`−` side with `(mq, mq + p]`. -/
theorem wythoffInv_wythoff (hq : 0 < q) (hqp : q < p) (n : ℤ) :
    wythoffInv s p q (wythoff s p q n) = n := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqp' : (q : ℤ) < p := by exact_mod_cast hqp
  have hp' : (0 : ℤ) < p := by omega
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_two_mul n <;> cases s
  · rw [wythoff_plus_even]
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hq').1 (rfl : k * p / q = _)
    rw [wythoffInv_plus_eq (k := k) ((ediv_eq_iff hp').2 ⟨by linarith, by linarith⟩),
      if_pos (by linarith)]
  · rw [wythoff_minus_even]
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hq').1 (rfl : (k * p - 1) / q = _)
    rw [wythoffInv_minus_eq (k := k) ((ediv_eq_iff hp').2 ⟨by linarith, by linarith⟩),
      if_pos (by linarith)]
  · rw [wythoff_plus_odd]
    set m := (k * p - 1) / ((p : ℤ) - q) with hm
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hR).1 hm.symm
    rw [wythoffInv_plus_eq (k := m + 1 - k) ((ediv_eq_iff hp').2 ⟨by linarith, by linarith⟩),
      if_neg (by linarith)]
    ring
  · rw [wythoff_minus_odd]
    set m := k * p / ((p : ℤ) - q) with hm
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hR).1 hm.symm
    rw [wythoffInv_minus_eq (k := m + 1 - k) ((ediv_eq_iff hp').2 ⟨by linarith, by linarith⟩),
      if_neg (by linarith)]
    ring

/-- **(ratified).**  `wythoffInv` is a right inverse. -/
theorem wythoff_wythoffInv (hq : 0 < q) (hqp : q < p) (m : ℤ) :
    wythoff s p q (wythoffInv s p q m) = m := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqp' : (q : ℤ) < p := by exact_mod_cast hqp
  have hp' : (0 : ℤ) < p := by omega
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  cases s
  · set k := (m * q + p - 1) / p with hk
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hp').1 hk.symm
    rw [wythoffInv_plus_eq hk.symm]
    split_ifs with h
    · rw [wythoff_plus_even, ediv_eq_iff hq']; constructor <;> linarith
    · rw [wythoff_plus_odd, ediv_eq_iff hR]; constructor <;> linarith
  · set k := m * q / p + 1 with hk
    obtain ⟨h1, h2⟩ := (ediv_eq_iff hp').1 (show m * q / p = k - 1 by omega)
    rw [wythoffInv_minus_eq (show m * q / p = k - 1 by omega)]
    split_ifs with h
    · rw [wythoff_minus_even, ediv_eq_iff hq']; constructor <;> linarith
    · rw [wythoff_minus_odd, ediv_eq_iff hR]; constructor <;> linarith

/-- `W_{p/q±}` as a permutation of `ℤ`. -/
def wythoffPerm (hq : 0 < q) (hqp : q < p) : Equiv.Perm ℤ where
  toFun := wythoff s p q
  invFun := wythoffInv s p q
  left_inv := wythoffInv_wythoff s hq hqp
  right_inv := wythoff_wythoffInv s hq hqp

/-- **(ratified).**  `W` preserves `ℕ⁺` (and hence `ℤ≤0`).  Paper proof: for `k ≥ 1`,
`⌊kp/q⌋ ≥ 1` and `⌊(kp−1)/R⌋ ≥ ⌊(p−1)/R⌋ ≥ 1`; for `k ≤ 0` the numerators are `≤ 0` resp.
`< 0`. -/
theorem wythoff_pos_iff (hq : 0 < q) (hqp : q < p) (n : ℤ) :
    0 < wythoff s p q n ↔ 0 < n := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqp' : (q : ℤ) < p := by exact_mod_cast hqp
  have hp' : (0 : ℤ) < p := by omega
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  have key : ∀ k : ℤ, (0 < k → (p : ℤ) ≤ k * p) ∧ (k ≤ 0 → k * p ≤ 0) := fun k =>
    ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_two_mul n <;> cases s <;>
    simp only [wythoff_plus_even, wythoff_minus_even, wythoff_plus_odd, wythoff_minus_odd,
      ediv_pos_iff' hq', ediv_pos_iff' hR] <;>
    rcases lt_or_ge 0 k with hk | hk <;> have := (key k).1 <;> have := (key k).2 <;>
    constructor <;> intro h <;> omega

/-- **(ratified).**  `W` restricts to a bijection of `ℕ⁺`. -/
theorem wythoff_bijOn_pos (hq : 0 < q) (hqp : q < p) :
    Set.BijOn (wythoff s p q) {n : ℤ | 0 < n} {n : ℤ | 0 < n} := by
  refine ⟨fun n hn => (wythoff_pos_iff s hq hqp n).2 hn,
    fun a _ b _ h => (wythoffPerm s hq hqp).injective h, fun m hm => ?_⟩
  refine ⟨wythoffInv s p q m, ?_, wythoff_wythoffInv s hq hqp m⟩
  have := (wythoff_pos_iff s hq hqp (wythoffInv s p q m)).1
  rw [wythoff_wythoffInv s hq hqp] at this
  exact this hm

end Bijection

section Beatty

variable {p q : ℕ}

/-- **(ratified).**  The paper's floor form, `+` even branch: `W_{r+}(2k) = ⌊kr⌋`. -/
theorem wythoff_plus_two_mul (hq : 0 < q) (k : ℤ) :
    wythoff .plus p q (2 * k) = ⌊(k * p / q : ℚ)⌋ := by
  rw [wythoff_plus_even, show (k * p / q : ℚ) = ((k * p : ℤ) : ℚ) / (q : ℕ) by push_cast; ring,
    Rat.floor_intCast_div_natCast]

/-- **(ratified).**  `W_{r+}(2k − 1) = ⌈ks⌉ − 1`, `s = p/(p − q)`. -/
theorem wythoff_plus_two_mul_sub_one (hqp : q < p) (k : ℤ) :
    wythoff .plus p q (2 * k - 1) = ⌈(k * p / ((p : ℚ) - q) : ℚ)⌉ - 1 := by
  have hR : (0 : ℤ) < ((p - q : ℕ) : ℤ) := by omega
  rw [wythoff_plus_odd, show (k * p / ((p : ℚ) - q) : ℚ) = ((k * p : ℤ) : ℚ) / (p - q : ℕ) by
      rw [Nat.cast_sub hqp.le]; push_cast; ring,
    Rat.ceil_intCast_div_natCast, show ((p : ℤ) - q) = ((p - q : ℕ) : ℤ) by omega,
    ediv_eq_iff hR]
  obtain ⟨h1, h2⟩ := (ediv_eq_iff hR).1 (rfl : (-(k * p)) / ((p - q : ℕ) : ℤ) = _)
  constructor <;> linarith

/-- **(ratified).**  `W_{r−}(2k) = ⌈kr⌉ − 1`. -/
theorem wythoff_minus_two_mul (hq : 0 < q) (k : ℤ) :
    wythoff .minus p q (2 * k) = ⌈(k * p / q : ℚ)⌉ - 1 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [wythoff_minus_even, show (k * p / q : ℚ) = ((k * p : ℤ) : ℚ) / (q : ℕ) by push_cast; ring,
    Rat.ceil_intCast_div_natCast, ediv_eq_iff hq']
  obtain ⟨h1, h2⟩ := (ediv_eq_iff hq').1 (rfl : (-(k * p)) / (q : ℤ) = _)
  constructor <;> linarith

/-- **(ratified).**  `W_{r−}(2k − 1) = ⌊ks⌋`. -/
theorem wythoff_minus_two_mul_sub_one (hqp : q < p) (k : ℤ) :
    wythoff .minus p q (2 * k - 1) = ⌊(k * p / ((p : ℚ) - q) : ℚ)⌋ := by
  rw [wythoff_minus_odd, show (k * p / ((p : ℚ) - q) : ℚ) = ((k * p : ℤ) : ℚ) / (p - q : ℕ) by
      rw [Nat.cast_sub hqp.le]; push_cast; ring,
    Rat.floor_intCast_div_natCast, show ((p : ℤ) - q) = ((p - q : ℕ) : ℤ) by omega]

end Beatty

/-! ## Pieces: `W` is affine on residue classes -/

section Pieces

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  Even branch: `W(n + 2qm) = W n + pm`.  Paper proof: `n = 2k`,
`⌊(k + qm)p/q⌋ = ⌊kp/q⌋ + pm` (`Int.add_mul_ediv_right`). -/
theorem wythoff_add_even (hq : 0 < q) {n : ℤ} (hn : n % 2 = 0) (m : ℤ) :
    wythoff s p q (n + 2 * q * m) = wythoff s p q n + p * m := by
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [show 2 * k + 2 * q * m = 2 * (k + q * m) by ring]
  cases s
  · rw [wythoff_plus_even, wythoff_plus_even,
      show (k + q * m) * p = k * p + q * (p * m) by ring, Int.add_mul_ediv_left _ _ hq']
  · rw [wythoff_minus_even, wythoff_minus_even,
      show (k + q * m) * p - 1 = k * p - 1 + q * (p * m) by ring, Int.add_mul_ediv_left _ _ hq']

/-- **(ratified).**  Odd branch: `W(n + 2Rm) = W n + pm`. -/
theorem wythoff_add_odd (hqp : q < p) {n : ℤ} (hn : n % 2 = 1) (m : ℤ) :
    wythoff s p q (n + 2 * ((p : ℤ) - q) * m) = wythoff s p q n + p * m := by
  have hR : (p : ℤ) - q ≠ 0 := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  rw [show 2 * k - 1 + 2 * ((p : ℤ) - q) * m = 2 * (k + ((p : ℤ) - q) * m) - 1 by ring]
  cases s
  · rw [wythoff_plus_odd, wythoff_plus_odd,
      show (k + ((p : ℤ) - q) * m) * p - 1 = k * p - 1 + ((p : ℤ) - q) * (p * m) by ring,
      Int.add_mul_ediv_left _ _ hR]
  · rw [wythoff_minus_odd, wythoff_minus_odd,
      show (k + ((p : ℤ) - q) * m) * p = k * p + ((p : ℤ) - q) * (p * m) by ring,
      Int.add_mul_ediv_left _ _ hR]

/-- **(ratified).**  For even `p` the parity of `W n` depends only on `n mod 2qR` (the branch
piece of `n`). -/
theorem wythoff_parity_periodic (hp : Even p) (hq : 0 < q) (hqp : q < p) (n m : ℤ) :
    (wythoff s p q (n + 2 * (q * ((p : ℤ) - q)) * m) : ZMod 2) = (wythoff s p q n : ZMod 2) := by
  have hp2 : ((p : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff_even).2 hp
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  · rw [show n + 2 * (q * ((p : ℤ) - q)) * m = n + 2 * q * (((p : ℤ) - q) * m) by ring,
      wythoff_add_even s hq hn]
    rw [Int.cast_add, Int.cast_mul, hp2, zero_mul, add_zero]
  · rw [show n + 2 * (q * ((p : ℤ) - q)) * m = n + 2 * ((p : ℤ) - q) * (q * m) by ring,
      wythoff_add_odd s hqp hn]
    rw [Int.cast_add, Int.cast_mul, hp2, zero_mul, add_zero]

end Pieces

/-! ## Lemma 1: image parities -/

section Lemma1Helpers

/-- Peel the first index off a filtered `range`. -/
theorem card_filter_range_succ' (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.range (n + 1)).filter P).card =
      ((Finset.range n).filter fun i => P (i + 1)).card + (if P 0 then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']

/-- Peel the last index off a filtered `range`. -/
theorem card_filter_range_succ (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.range (n + 1)).filter P).card =
      ((Finset.range n).filter P).card + (if P n then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]

/-- A predicate swapped with its negation by `i ↦ n − 1 − i` holds on exactly half of
`range n`. -/
theorem two_mul_card_filter_of_flip (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ)
    (h : ∀ i < n, Q (n - 1 - i) ↔ ¬ Q i) :
    2 * ((Finset.range n).filter Q).card = n := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range n) Q
  have h2 : ((Finset.range n).filter Q).card =
      ((Finset.range n).filter fun i => ¬ Q i).card := by
    apply Finset.card_nbij' (fun i => n - 1 - i) (fun i => n - 1 - i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨by omega, fun hq => (h i hi.1).1 hq hi.2⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      refine ⟨by omega, ?_⟩
      by_contra hc
      exact hi.2 (by have := (h (n - 1 - i) (by omega)).2 hc; rwa [show n - 1 - (n - 1 - i) = i by
        omega] at this)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
      simp only; omega
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
      simp only; omega
  rw [Finset.card_range] at h1
  omega

/-- The reflection `t ↦ D − t` of floor quotients, for `D ∤ tP`. -/
theorem flip_floor {D P t : ℤ} (hD : 0 < D) (hndvd : ¬ D ∣ t * P) :
    (D - t) * P / D = P - 1 - t * P / D ∧ (t * P - 1) / D = t * P / D := by
  set a := t * P / D with ha
  obtain ⟨h1, h2⟩ := (ediv_eq_iff hD).1 ha.symm
  have h3 : a * D ≠ t * P := fun h => hndvd ⟨a, by rw [← h]; ring⟩
  have h4 : a * D + 1 ≤ t * P := by omega
  exact ⟨(ediv_eq_iff hD).2 ⟨by linarith, by linarith⟩,
    (ediv_eq_iff hD).2 ⟨by linarith, by linarith⟩⟩

theorem not_dvd_mul_of_coprime {D p t : ℕ} (hcop : Nat.Coprime p D) (ht1 : 1 ≤ t)
    (ht2 : t < D) : ¬ (D : ℤ) ∣ (t : ℤ) * p := by
  intro h
  rw [← Nat.cast_mul, Int.natCast_dvd_natCast] at h
  have := Nat.le_of_dvd ht1 (hcop.symm.dvd_of_dvd_mul_right h)
  omega

theorem odd_of_even_coprime {p q : ℕ} (hp : Even p) (hcop : Nat.Coprime p q) : q % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ Nat.gcd p q := Nat.dvd_gcd (even_iff_two_dvd.1 hp) (by omega)
  rw [hcop] at h2
  omega

variable (s : Side) {p q : ℕ}

/-- Even branch at `t = i + 1 ∈ [1, q − 1]`: both sides give `⌊tp/q⌋`, and the reflection
`t ↦ q − t` gives `p − 1 − ⌊tp/q⌋`. -/
theorem wythoff_even_flip (hcop : Nat.Coprime p q) (hq : 0 < q) {i : ℕ} (hi : i + 1 < q) :
    wythoff s p q (2 * ((i + 1 : ℕ) : ℤ)) = ((i : ℤ) + 1) * p / q ∧
      wythoff s p q (2 * ((q - 1 - 1 - i + 1 : ℕ) : ℤ)) = p - 1 - ((i : ℤ) + 1) * p / q := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hnd := not_dvd_mul_of_coprime hcop (t := i + 1) (by omega) hi
  push_cast at hnd
  obtain ⟨f1, f2⟩ := flip_floor hq' hnd
  rw [show ((q - 1 - 1 - i + 1 : ℕ) : ℤ) = (q : ℤ) - ((i : ℤ) + 1) by omega]
  push_cast
  cases s
  · rw [wythoff_plus_even, wythoff_plus_even, f1]; exact ⟨rfl, rfl⟩
  · rw [wythoff_minus_even, wythoff_minus_even, f2]
    refine ⟨rfl, ?_⟩
    have hnd' : ¬ (q : ℤ) ∣ (q - ((i : ℤ) + 1)) * p := by
      intro h; apply hnd
      have : (q : ℤ) ∣ q * p := dvd_mul_right _ _
      have := dvd_sub this h
      rwa [show (q : ℤ) * p - (q - ((i : ℤ) + 1)) * p = ((i : ℤ) + 1) * p by ring] at this
    rw [(flip_floor hq' hnd').2, f1]

/-- Odd branch at `k = u + 1 ∈ [1, R − 1]`. -/
theorem wythoff_odd_flip (hcop : Nat.Coprime p q) (hqp : q < p) {u : ℕ} (hu : u + 1 < p - q) :
    wythoff s p q (2 * (u : ℤ) + 1) = ((u : ℤ) + 1) * p / ((p : ℤ) - q) ∧
      wythoff s p q (2 * ((p - q - 1 - 1 - u : ℕ) : ℤ) + 1) =
        p - 1 - ((u : ℤ) + 1) * p / ((p : ℤ) - q) := by
  have hR : (0 : ℤ) < (p - q : ℕ) := by omega
  have hcop' : Nat.Coprime p (p - q) := (Nat.coprime_self_sub_right hqp.le).2 hcop
  have hnd := not_dvd_mul_of_coprime hcop' (t := u + 1) (by omega) hu
  have hnd' := not_dvd_mul_of_coprime hcop' (t := p - q - (u + 1)) (by omega) (by omega)
  have hRc : ((p - q : ℕ) : ℤ) = (p : ℤ) - q := by omega
  rw [hRc] at hR hnd hnd'
  push_cast at hnd
  rw [show ((p - q - (u + 1) : ℕ) : ℤ) = ((p : ℤ) - q) - ((u : ℤ) + 1) by omega] at hnd'
  obtain ⟨f1, f2⟩ := flip_floor hR hnd
  have f3 := (flip_floor hR hnd').2
  rw [show 2 * ((p - q - 1 - 1 - u : ℕ) : ℤ) + 1 = 2 * (((p : ℤ) - q) - ((u : ℤ) + 1)) - 1 by
      omega, show 2 * (u : ℤ) + 1 = 2 * ((u : ℤ) + 1) - 1 by ring]
  cases s
  · rw [wythoff_plus_odd, wythoff_plus_odd, f2, f3, f1]; exact ⟨rfl, rfl⟩
  · rw [wythoff_minus_odd, wythoff_minus_odd, f1]; exact ⟨rfl, rfl⟩

end Lemma1Helpers

section Lemma1

variable (s : Side) {p q : ℕ}

/-- **(ratified, Lemma 1, even branch).**  Paper proof: for `1 ≤ t ≤ q − 1`, `tp/q ∉ ℤ`
(coprime), and `t ↦ q − t` sends `⌊tp/q⌋` to `p − 1 − ⌊tp/q⌋`, of the other parity (`p` even,
`q` odd, no fixed point).  `+` adds `t = 0` (image `0`, even); for `−` the residue `t = 0` has
image `−1` (odd; it stands for the paper's `t = q`, image `p − 1`). -/
theorem card_even_image_even (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    ((Finset.range q).filter fun t : ℕ => wythoff s p q (2 * (t : ℤ)) % 2 = 0).card =
      if s = .plus then (q + 1) / 2 else (q - 1) / 2 := by
  have hq2 := odd_of_even_coprime hp hcop
  obtain ⟨r, hr⟩ := hp
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hrange : Finset.range q = Finset.range (q - 1 + 1) := by rw [Nat.sub_add_cancel hq]
  rw [hrange, card_filter_range_succ']
  have hinner : 2 * ((Finset.range (q - 1)).filter fun i : ℕ =>
      wythoff s p q (2 * ((i + 1 : ℕ) : ℤ)) % 2 = 0).card = q - 1 := by
    apply two_mul_card_filter_of_flip
    intro i hi
    obtain ⟨h1, h2⟩ := wythoff_even_flip s hcop hq (i := i) (by omega)
    rw [h1, h2]
    have : (p : ℤ) = r + r := by exact_mod_cast hr
    omega
  cases s
  · have h0 : wythoff .plus p q (2 * ((0 : ℕ) : ℤ)) = 0 := by
      rw [Nat.cast_zero, wythoff_plus_even]; simp
    rw [h0, if_pos (by norm_num), if_pos rfl]; omega
  · have h0 : wythoff .minus p q (2 * ((0 : ℕ) : ℤ)) = -1 := by
      rw [Nat.cast_zero, wythoff_minus_even, ediv_eq_iff hq']
      constructor <;> linarith
    rw [h0, if_neg (by norm_num), if_neg (by decide)]; omega

/-- **(ratified, Lemma 1, odd branch).**  The same with `R = p − q`: `u ↦ R − u` on the images
`W(2u + 1)`, `u < R`; `+` adds the odd image `p − 1` (at `u = R − 1`), `−` the even image `0`. -/
theorem card_even_image_odd (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    ((Finset.range (p - q)).filter fun u : ℕ => wythoff s p q (2 * (u : ℤ) + 1) % 2 = 0).card =
      if s = .plus then (p - q - 1) / 2 else (p - q + 1) / 2 := by
  have hq2 := odd_of_even_coprime hp hcop
  obtain ⟨r, hr⟩ := hp
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  have hrange : Finset.range (p - q) = Finset.range (p - q - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
  rw [hrange, card_filter_range_succ]
  have hinner : 2 * ((Finset.range (p - q - 1)).filter fun u : ℕ =>
      wythoff s p q (2 * (u : ℤ) + 1) % 2 = 0).card = p - q - 1 := by
    apply two_mul_card_filter_of_flip
    intro u hu
    obtain ⟨h1, h2⟩ := wythoff_odd_flip s hcop hqp (u := u) (by omega)
    rw [h1, h2]
    have : (p : ℤ) = r + r := by exact_mod_cast hr
    omega
  have hlast : 2 * ((p - q - 1 : ℕ) : ℤ) + 1 = 2 * ((p : ℤ) - q) - 1 := by omega
  cases s
  · have h0 : wythoff .plus p q (2 * ((p - q - 1 : ℕ) : ℤ) + 1) = p - 1 := by
      rw [hlast, wythoff_plus_odd, ediv_eq_iff hR]
      constructor <;> nlinarith
    rw [h0, if_neg (by have : (p : ℤ) = r + r := by exact_mod_cast hr
                       omega), if_pos rfl]
    omega
  · have h0 : wythoff .minus p q (2 * ((p - q - 1 : ℕ) : ℤ) + 1) = p := by
      rw [hlast, wythoff_minus_odd, mul_comm, Int.mul_ediv_cancel _ hR.ne']
    rw [h0, if_pos (by have : (p : ℤ) = r + r := by exact_mod_cast hr
                       omega), if_neg (by decide)]
    omega

end Lemma1

/-! ## The parity chains -/

/-- Forward chain: probability that `W x` is even given the parity `e` of `x` (Lemma 1 count
over `Q_e`).  `+`: `E→E = (q+1)/(2q)`, `O→E = (R−1)/(2R)`; `−`: `(q−1)/(2q)`, `(R+1)/(2R)`. -/
def fwdEven (s : Side) (p q : ℕ) (e : ZMod 2) : ℚ :=
  match s with
  | .plus => if e = 0 then ((q : ℚ) + 1) / (2 * q) else ((p : ℚ) - q - 1) / (2 * ((p : ℚ) - q))
  | .minus => if e = 0 then ((q : ℚ) - 1) / (2 * q) else ((p : ℚ) - q + 1) / (2 * ((p : ℚ) - q))

/-- Backward chain: probability that `W⁻¹ m` is even given the parity `e` of `m`
(`#{even-branch pieces with image parity e}/(p/2)`).  `+`: `E→E = (q+1)/p`, `O→E = (q−1)/p`;
`−`: `(q−1)/p`, `(q+1)/p`. -/
def bwdEven (s : Side) (p q : ℕ) (e : ZMod 2) : ℚ :=
  match s with
  | .plus => if e = 0 then ((q : ℚ) + 1) / p else ((q : ℚ) - 1) / p
  | .minus => if e = 0 then ((q : ℚ) - 1) / p else ((q : ℚ) + 1) / p

/-- Forward transition probability `F(e → f)`. -/
def fwdProb (s : Side) (p q : ℕ) (e f : ZMod 2) : ℚ :=
  if f = 0 then fwdEven s p q e else 1 - fwdEven s p q e

/-- Backward transition probability `B(e → f)`. -/
def bwdProb (s : Side) (p q : ℕ) (e f : ZMod 2) : ℚ :=
  if f = 0 then bwdEven s p q e else 1 - bwdEven s p q e

/-! ## Theorem T: where the traps are -/

section ZModTwo

theorem zmod2_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by revert e; decide

theorem intCast_zmod2_eq_zero_iff (n : ℤ) : (n : ZMod 2) = 0 ↔ n % 2 = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]; norm_num

theorem intCast_zmod2_eq_one_iff (n : ℤ) : (n : ZMod 2) = 1 ↔ n % 2 = 1 := by
  rcases zmod2_cases (n : ZMod 2) with h | h
  · have := (intCast_zmod2_eq_zero_iff n).1 h
    rw [h]; constructor
    · intro h'; exact absurd h' (by decide)
    · intro h'; omega
  · rw [h]; refine ⟨fun _ => ?_, fun _ => rfl⟩
    by_contra h'
    rw [(intCast_zmod2_eq_zero_iff n).2 (by omega)] at h
    exact absurd h (by decide)

theorem natCast_zmod2_of_even {p : ℕ} (hp : Even p) : ((p : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff_even).2 hp

end ZModTwo

section TheoremT

variable (s : Side) {p q : ℕ}

/-- **(ratified, Theorem T, map form).**  Some parity class is mapped into itself iff `p` is
even, the side is `+`, and `q = 1` or `p − q = 1`.  Paper proof: for odd `p`, `W(n + 2qm) =
W n + pm` takes both parities on every even-branch class.  For even `p`, `W` keeps the parity
class `e` iff every piece of type `e` has image parity `e`, i.e. (Lemma 1) `(q+1)/2 = q`
(`q = 1`, evens) or `(R−1)/2 = 0` (`R = 1`, odds) on `+`; on `−` the counts `(q−1)/2 < q` and
`(R+1)/2 > 0` never allow it. -/
theorem parityClass_invariant_iff (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    (∃ e : ZMod 2, ∀ n : ℤ, (n : ZMod 2) = e → (wythoff s p q n : ZMod 2) = e) ↔
      Even p ∧ s = .plus ∧ (q = 1 ∨ p - q = 1) := by
  constructor
  · rintro ⟨e, he⟩
    have hpe : Even p := by
      rw [← ZMod.natCast_eq_zero_iff_even, ← Int.cast_natCast]
      rcases zmod2_cases e with rfl | rfl
      · have h1 := he 0 (by simp)
        have h2 := he (0 + 2 * q * 1) ((intCast_zmod2_eq_zero_iff _).2 (by omega))
        rw [wythoff_add_even s hq (by norm_num : (0 : ℤ) % 2 = 0), Int.cast_add, h1] at h2
        simpa using h2
      · have h1 := he 1 (by simp)
        have h2 := he (1 + 2 * ((p : ℤ) - q) * 1) ((intCast_zmod2_eq_one_iff _).2 (by omega))
        rw [wythoff_add_odd s hqp (by norm_num : (1 : ℤ) % 2 = 1), Int.cast_add, h1] at h2
        simpa using h2
    have hq2 := odd_of_even_coprime hpe hcop
    obtain ⟨r, hr⟩ := hpe
    rcases zmod2_cases e with rfl | rfl
    · have hc := card_even_image_even s ⟨r, hr⟩ hcop hq hqp
      rw [Finset.filter_true_of_mem (fun t _ => (intCast_zmod2_eq_zero_iff _).1
        (he _ ((intCast_zmod2_eq_zero_iff _).2 (by omega)))), Finset.card_range] at hc
      cases s
      · exact ⟨⟨r, hr⟩, rfl, Or.inl (by simp at hc; omega)⟩
      · simp at hc; omega
    · have hc := card_even_image_odd s ⟨r, hr⟩ hcop hq hqp
      rw [Finset.filter_false_of_mem (fun u _ => by
        have := (intCast_zmod2_eq_one_iff _).1
          (he _ ((intCast_zmod2_eq_one_iff (2 * (u : ℤ) + 1)).2 (by omega)))
        omega), Finset.card_empty] at hc
      cases s
      · exact ⟨⟨r, hr⟩, rfl, Or.inr (by simp at hc; omega)⟩
      · simp at hc; omega
  · rintro ⟨hpe, rfl, h | h⟩
    · subst h
      refine ⟨0, fun n hn => ?_⟩
      have := (intCast_zmod2_eq_zero_iff n).1 hn
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      rw [wythoff_plus_even, Nat.cast_one, Int.ediv_one, Int.cast_mul, natCast_zmod2_of_even hpe,
        mul_zero]
    · refine ⟨1, fun n hn => ?_⟩
      have := (intCast_zmod2_eq_one_iff n).1 hn
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
      rw [wythoff_plus_odd, show (p : ℤ) - q = 1 by omega, Int.ediv_one, Int.cast_sub,
        Int.cast_mul, natCast_zmod2_of_even hpe, mul_zero, Int.cast_one, zero_sub]
      decide

/-- **(ratified, Theorem T, chain form).**  For even `p` the forward or backward parity chain has
an absorbing state iff the side is `+` and `q = 1` or `p − q = 1`.  Paper proof: read off the
diagonal entries.  `+`: `F(E→E) = (q+1)/(2q)` and `B(O→O) = (R+1)/p` are `1` iff `q = 1`;
`F(O→O) = (R+1)/(2R)` and `B(E→E) = (q+1)/p` are `1` iff `R = 1`.  `−`: the diagonal entries
`(q−1)/(2q)`, `(R−1)/(2R)`, `(q−1)/p`, `(R−1)/p` are all `< 1`. -/
theorem absorbing_iff (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    (∃ e : ZMod 2, fwdProb s p q e e = 1 ∨ bwdProb s p q e e = 1) ↔
      s = .plus ∧ (q = 1 ∨ p - q = 1) := by
  have hQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hQP : (q : ℚ) < p := by exact_mod_cast hqp
  have hP0 : (p : ℚ) ≠ 0 := (by linarith : (0 : ℚ) < p).ne'
  have hQ0 : (q : ℚ) ≠ 0 := hQ.ne'
  have hR0 : (p : ℚ) - q ≠ 0 := (sub_pos.2 hQP).ne'
  have hpq : p - q = 1 ↔ (p : ℚ) - q = 1 := by
    constructor
    · intro h
      rw [show p = q + 1 by omega]; push_cast; ring
    · intro h
      have : p = q + 1 := by exact_mod_cast (by linarith : (p : ℚ) = q + 1)
      omega
  have hq1 : q = 1 ↔ (q : ℚ) = 1 := by norm_cast
  rw [hpq, hq1]
  constructor
  · rintro ⟨e, h⟩
    rcases zmod2_cases e with rfl | rfl <;> cases s <;>
      simp (config := {decide := true}) only [fwdProb, fwdEven, bwdProb, bwdEven, if_true,
        if_false] at h <;>
      rcases h with h | h <;> field_simp at h <;>
      first
        | exact ⟨rfl, Or.inl (by linarith)⟩
        | exact ⟨rfl, Or.inr (by linarith)⟩
        | (exfalso; linarith)
  · rintro ⟨rfl, h | h⟩
    · refine ⟨0, Or.inl ?_⟩
      simp [fwdProb, fwdEven, h]
    · refine ⟨1, Or.inl ?_⟩
      simp [fwdProb, fwdEven, h]

end TheoremT

/-! ## Theorem E: the even integers `r = 2j` are solved -/

section OrbitHelpers

theorem mem_permOrbit_self (σ : Equiv.Perm ℤ) (x : ℤ) : x ∈ permOrbit σ x := ⟨0, by simp⟩

theorem apply_mem_permOrbit (σ : Equiv.Perm ℤ) (x : ℤ) : σ x ∈ permOrbit σ x := ⟨1, by simp⟩

theorem inv_apply_mem_permOrbit (σ : Equiv.Perm ℤ) (x : ℤ) : σ⁻¹ x ∈ permOrbit σ x :=
  ⟨-1, by simp⟩

/-- The orbit of any of its members. -/
theorem permOrbit_eq_of_mem (σ : Equiv.Perm ℤ) {x y : ℤ} (h : y ∈ permOrbit σ x) :
    permOrbit σ y = permOrbit σ x := by
  obtain ⟨a, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b + a, by simp only [zpow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b - a, by simp only [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel]⟩

theorem mem_permOrbit_comm (σ : Equiv.Perm ℤ) {x y : ℤ} (h : y ∈ permOrbit σ x) :
    x ∈ permOrbit σ y := by
  rw [permOrbit_eq_of_mem σ h]; exact mem_permOrbit_self σ x

/-- A permutation preserving positivity preserves it along whole orbits. -/
theorem zpow_pos_iff (σ : Equiv.Perm ℤ) (hσ : ∀ n, 0 < σ n ↔ 0 < n) (x : ℤ) (z : ℤ) :
    0 < (σ ^ z) x ↔ 0 < x := by
  have hinv : ∀ n, 0 < σ⁻¹ n ↔ 0 < n := fun n => by
    rw [← hσ (σ⁻¹ n)]; simp
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply, hσ]; exact ih
  | pred i ih =>
    rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
      hinv]; exact ih

end OrbitHelpers

section TheoremE

variable {j : ℕ}

/-- `W_{2j+}` (`p = 2j`, `q = 1`) as a permutation of `ℤ`. -/
def evenPerm (j : ℕ) (hj : 1 ≤ j) : Equiv.Perm ℤ :=
  wythoffPerm .plus (p := 2 * j) (q := 1) Nat.one_pos (by omega)

/-- The entry set `E = 2ℕ⁺ ∖ 2jℕ⁺`. -/
def entrySet (j : ℕ) : Set ℤ :=
  {x | 0 < x ∧ x % 2 = 0 ∧ x % (2 * j) ≠ 0}

/-- **(ratified).**  `W_{2j+}(2k) = 2jk`. -/
theorem evenPerm_two_mul (hj : 1 ≤ j) (k : ℤ) : evenPerm j hj (2 * k) = 2 * j * k := by
  show wythoff .plus (2 * j) 1 (2 * k) = _
  rw [wythoff_plus_even]; push_cast; rw [Int.ediv_one]; ring

/-- **(ratified).**  `W_{2j+}(2k − 1) = k + ⌊(k − 1)/(2j − 1)⌋`, the `k`-th non-multiple of
`2j`. -/
theorem evenPerm_two_mul_sub_one (hj : 1 ≤ j) (k : ℤ) :
    evenPerm j hj (2 * k - 1) = k + (k - 1) / (2 * j - 1) := by
  show wythoff .plus (2 * j) 1 (2 * k - 1) = _
  have h0 : (2 * (j : ℤ) - 1) ≠ 0 := by omega
  rw [wythoff_plus_odd]; push_cast
  rw [show k * (2 * (j : ℤ)) - 1 = (k - 1) + (2 * (j : ℤ) - 1) * k by ring,
    Int.add_mul_ediv_left _ _ h0, add_comm]

/-- **(ratified).**  `1` is a fixed point: `{1}` is a finite orbit. -/
theorem permOrbit_evenPerm_one (hj : 1 ≤ j) : permOrbit (evenPerm j hj) 1 = {1} := by
  have h1 : evenPerm j hj 1 = 1 := by
    have := evenPerm_two_mul_sub_one hj 1
    norm_num at this
    exact this
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h1 z
  · rintro rfl; exact mem_permOrbit_self _ _

/-- **(ratified).**  The evens are a trap whose entry points are exactly `E` on `ℕ⁺`
(`σ(2ℤ) = 2jℤ`). -/
theorem evenPerm_entry_iff (hj : 1 ≤ j) {x : ℤ} (hx : 0 < x) :
    x ∈ {y : ℤ | y % 2 = 0} \ evenPerm j hj '' {y : ℤ | y % 2 = 0} ↔ x ∈ entrySet j := by
  simp only [entrySet, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h2, hnot⟩
    refine ⟨hx, h2, fun hd => hnot ?_⟩
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hd
    exact ⟨2 * c, by omega, by rw [evenPerm_two_mul, hc]⟩
  · rintro ⟨-, h2, hd⟩
    refine ⟨h2, ?_⟩
    rintro ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    rw [evenPerm_two_mul] at hd
    exact hd (Int.emod_eq_zero_of_dvd ⟨k, rfl⟩)

theorem evenPerm_one (hj : 1 ≤ j) : evenPerm j hj 1 = 1 := by
  have := evenPerm_two_mul_sub_one hj 1
  norm_num at this
  exact this

theorem evenPerm_pos_iff (hj : 1 ≤ j) (n : ℤ) : 0 < evenPerm j hj n ↔ 0 < n :=
  wythoff_pos_iff .plus (p := 2 * j) (q := 1) Nat.one_pos (by omega) n

/-- Fact (e): on the evens `σ y = j y`, and the evens are a trap. -/
theorem evenPerm_even (hj : 1 ≤ j) {y : ℤ} (hy : y % 2 = 0) :
    evenPerm j hj y = j * y ∧ evenPerm j hj y % 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
  rw [evenPerm_two_mul]
  exact ⟨by ring, by rw [show 2 * (j : ℤ) * k = 2 * (j * k) by ring]; omega⟩

theorem evenPerm_trap (hj : 1 ≤ j) :
    ∀ y ∈ {y : ℤ | y % 2 = 0}, evenPerm j hj y ∈ {y : ℤ | y % 2 = 0} :=
  fun _ hy => (evenPerm_even hj hy).2

/-- Fact (b): odd `y ≥ 3` go down, staying `> 1`. -/
theorem evenPerm_odd_lt (hj : 2 ≤ j) {y : ℤ} (hy : y % 2 = 1) (h3 : 3 ≤ y) :
    1 < evenPerm j (by omega) y ∧ evenPerm j (by omega) y < y := by
  obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k - 1 := ⟨(y + 1) / 2, by omega⟩
  rw [evenPerm_two_mul_sub_one]
  have hd : (0 : ℤ) < 2 * j - 1 := by omega
  set d := (k - 1) / (2 * (j : ℤ) - 1) with hd'
  obtain ⟨h1, h2⟩ := (ediv_eq_iff hd).1 hd'.symm
  have hd0 : 0 ≤ d := Int.ediv_nonneg (by omega) hd.le
  constructor
  · omega
  · nlinarith [mul_nonneg hd0 (show (0 : ℤ) ≤ 2 * j - 1 - 3 by omega)]

/-- Fact (c): the preimage of an odd `m > 1` is odd and larger. -/
theorem evenPerm_inv_odd (hj : 2 ≤ j) {m : ℤ} (hm : m % 2 = 1) (h1 : 1 < m) :
    (evenPerm j (by omega))⁻¹ m % 2 = 1 ∧ m < (evenPerm j (by omega))⁻¹ m := by
  have hj1 : 1 ≤ j := by omega
  set y := (evenPerm j hj1)⁻¹ m with hy
  have hσy : evenPerm j hj1 y = m := by simp [hy]
  have hy1 : y % 2 = 1 := by
    by_contra h
    have := (evenPerm_even hj1 (by omega : y % 2 = 0)).2
    rw [hσy] at this; omega
  have hypos : 0 < y := (evenPerm_pos_iff hj1 y).1 (by omega)
  have hy3 : 3 ≤ y := by
    by_contra h
    have h1' : y = 1 := by omega
    rw [h1', evenPerm_one] at hσy; omega
  exact ⟨hy1, by have := (evenPerm_odd_lt hj hy1 hy3).2; rwa [hσy] at this⟩

/-- Existence half of Theorem E's structure: descend to a point of `E`. -/
theorem exists_entry_mem_orbit (hj : 2 ≤ j) {x : ℤ} (hx : 1 < x) :
    ∃ e ∈ entrySet j, e ∈ permOrbit (evenPerm j (by omega)) x := by
  have hj1 : 1 ≤ j := by omega
  suffices H : ∀ n : ℕ, ∀ x : ℤ, x.toNat = n → 1 < x →
      ∃ e ∈ entrySet j, e ∈ permOrbit (evenPerm j hj1) x from H _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hxn hx
  rcases Int.emod_two_eq_zero_or_one x with h2 | h2
  · by_cases hd : x % (2 * j) = 0
    · obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hd
      have hc0 : 0 < c := by
        by_contra h
        have : 2 * (j : ℤ) * c ≤ 0 := by nlinarith
        omega
      have hσ : (evenPerm j hj1) (2 * c) = x := by rw [evenPerm_two_mul, hc]
      have hlt : 2 * c < x := by nlinarith
      obtain ⟨e, he, hmem⟩ := ih (2 * c).toNat (by omega) (2 * c) rfl (by omega)
      refine ⟨e, he, ?_⟩
      rw [← permOrbit_eq_of_mem _ (mem_permOrbit_comm _
        (hσ ▸ apply_mem_permOrbit (evenPerm j hj1) (2 * c)))]
      exact hmem
    · exact ⟨x, ⟨by omega, h2, hd⟩, mem_permOrbit_self _ _⟩
  · obtain ⟨h1, hlt⟩ : 1 < (evenPerm j hj1) x ∧ (evenPerm j hj1) x < x :=
      evenPerm_odd_lt hj h2 (by omega)
    obtain ⟨e, he, hmem⟩ := ih ((evenPerm j hj1) x).toNat (by omega) ((evenPerm j hj1) x) rfl h1
    exact ⟨e, he, by
      rw [← permOrbit_eq_of_mem _ (apply_mem_permOrbit (evenPerm j hj1) x)]; exact hmem⟩

/-- **(ratified, Theorem E, structure).**  For `j ≥ 2`, every orbit through `x > 1` meets `E`
in exactly one point.  Paper proof: evens go up into `2jℕ⁺` (`×j`); odd `n ≥ 3` go down
(`k + ⌊(k−1)/(2j−1)⌋ < 2k − 1`); the preimage of an odd is odd and larger; backward from `2jk`
the preimage `2k` is smaller.  So the orbit is (increasing odd backward tail) → one point of
`E` → (increasing even forward tail in `2jℕ⁺`). -/
theorem existsUnique_entry_mem_orbit (hj : 2 ≤ j) {x : ℤ} (hx : 1 < x) :
    ∃! e, e ∈ entrySet j ∧ e ∈ permOrbit (evenPerm j (by omega)) x := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨e, he, hmem⟩ := exists_entry_mem_orbit hj hx
  refine ⟨e, ⟨he, hmem⟩, fun e' ⟨he', hmem'⟩ => ?_⟩
  apply AmusicalTrap.permOrbit_injOn_entry _ (evenPerm_trap hj1)
    ((evenPerm_entry_iff hj1 he'.1).2 he') ((evenPerm_entry_iff hj1 he.1).2 he)
  rw [permOrbit_eq_of_mem _ hmem', permOrbit_eq_of_mem _ hmem]

/-- **(ratified, Theorem E, minimum).**  That point of `E` is the minimum of the orbit. -/
theorem entry_le_of_mem_orbit (hj : 2 ≤ j) {x e : ℤ} (hx : 1 < x) (he : e ∈ entrySet j)
    (heo : e ∈ permOrbit (evenPerm j (by omega)) x) :
    ∀ y ∈ permOrbit (evenPerm j (by omega)) x, e ≤ y := by
  have hj1 : 1 ≤ j := by omega
  intro y hy
  rw [← permOrbit_eq_of_mem (evenPerm j hj1) heo] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨he0, he2, hed⟩ := he
  dsimp only
  rcases z with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    have key : ∀ n : ℕ, e ≤ ((evenPerm j hj1) ^ n) e ∧ ((evenPerm j hj1) ^ n) e % 2 = 0 := by
      intro n
      induction n with
      | zero => simp [he2]
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        obtain ⟨h1, h2⟩ := evenPerm_even hj1 ih.2
        refine ⟨?_, h2⟩
        rw [h1]; nlinarith
    exact (key n).1
  · rw [zpow_negSucc, ← inv_pow]
    have key : ∀ n : ℕ, e < ((evenPerm j hj1)⁻¹ ^ (n + 1)) e ∧
        ((evenPerm j hj1)⁻¹ ^ (n + 1)) e % 2 = 1 := by
      intro n
      induction n with
      | zero =>
        simp only [zero_add, pow_one]
        set y := (evenPerm j hj1)⁻¹ e with hy
        have hσy : (evenPerm j hj1) y = e := by simp [hy]
        have hy1 : y % 2 = 1 := by
          by_contra h
          exact ((evenPerm_entry_iff hj1 he0).2 ⟨he0, he2, hed⟩).2
            ⟨y, show y % 2 = 0 by omega, hσy⟩
        have hypos : 0 < y := (evenPerm_pos_iff hj1 y).1 (by omega)
        have hy3 : 3 ≤ y := by
          by_contra h
          have h1' : y = 1 := by omega
          rw [h1', evenPerm_one] at hσy; omega
        exact ⟨by have := (evenPerm_odd_lt hj hy1 hy3).2; omega, hy1⟩
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        obtain ⟨h1, h2⟩ := evenPerm_inv_odd hj ih.2 (by omega)
        exact ⟨by omega, h1⟩
    exact (key n).1.le

/-- **(ratified, Theorem E, no other finite orbit).**  Every orbit through `x > 1` is
infinite. -/
theorem permOrbit_evenPerm_infinite (hj : 2 ≤ j) {x : ℤ} (hx : 1 < x) :
    (permOrbit (evenPerm j (by omega)) x).Infinite := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨e, he, hmem⟩ := exists_entry_mem_orbit hj hx
  rw [← permOrbit_eq_of_mem _ hmem]
  exact AmusicalTrap.permOrbit_infinite_of_entry _ (evenPerm_trap hj1)
    ((evenPerm_entry_iff hj1 he.1).2 he)

/-- **(ratified, Theorem E, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x = 1` or `x ∈ E`. -/
theorem isOrbitMin_iff (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (evenPerm j (by omega)) x, x ≤ y) ↔ x = 1 ∨ x ∈ entrySet j := by
  constructor
  · intro h
    rcases eq_or_lt_of_le (show 1 ≤ x by omega) with h1 | h1
    · exact Or.inl h1.symm
    · obtain ⟨e, he, hmem⟩ := exists_entry_mem_orbit hj h1
      have h2 := entry_le_of_mem_orbit hj h1 he hmem x (mem_permOrbit_self _ _)
      have h3 := h e hmem
      exact Or.inr (by rw [show x = e by omega]; exact he)
  · rintro (rfl | he)
    · intro y hy
      rw [permOrbit_evenPerm_one] at hy
      rw [Set.mem_singleton_iff.1 hy]
    · exact entry_le_of_mem_orbit hj (by have := he.2.1; omega) he (mem_permOrbit_self _ _)

/-- **(ratified, Theorem E, indexing).**  The orbits meeting `ℕ⁺` are indexed by `{1} ∪ E`. -/
theorem permOrbit_bijOn (hj : 2 ≤ j) :
    Set.BijOn (permOrbit (evenPerm j (by omega))) ({1} ∪ entrySet j)
      {O | ∃ x : ℤ, 0 < x ∧ O = permOrbit (evenPerm j (by omega)) x} := by
  have hj1 : 1 ≤ j := by omega
  have hne : ∀ b ∈ entrySet j, permOrbit (evenPerm j hj1) 1 ≠ permOrbit (evenPerm j hj1) b := by
    intro b hb h
    have := mem_permOrbit_self (evenPerm j hj1) b
    rw [← h, permOrbit_evenPerm_one, Set.mem_singleton_iff] at this
    have := hb.2.1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rintro a (ha | ha)
    · exact ⟨1, one_pos, by rw [Set.mem_singleton_iff.1 ha]⟩
    · exact ⟨a, ha.1, rfl⟩
  · rintro a ha b hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
    · rw [Set.mem_singleton_iff.1 ha] at hab; exact absurd hab (hne b hb)
    · rw [Set.mem_singleton_iff.1 hb] at hab; exact absurd hab.symm (hne a ha)
    · exact AmusicalTrap.permOrbit_injOn_entry _ (evenPerm_trap hj1)
        ((evenPerm_entry_iff hj1 ha.1).2 ha) ((evenPerm_entry_iff hj1 hb.1).2 hb) hab
  · rintro O ⟨x, hx, rfl⟩
    rcases eq_or_lt_of_le (show 1 ≤ x by omega) with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1]⟩
    · obtain ⟨e, he, hmem⟩ := exists_entry_mem_orbit hj h1
      exact ⟨e, Or.inr he, permOrbit_eq_of_mem _ hmem⟩

/-- **(ratified, Theorem E, count).**  `#{orbit minima ≤ X} = 1 + ⌊X/2⌋ − ⌊X/2j⌋`. -/
theorem card_orbitMin_le (hj : 2 ≤ j) (X : ℕ) (hX : 1 ≤ X) :
    ((Finset.Icc (1 : ℤ) X).filter fun x : ℤ => x = 1 ∨ (x % 2 = 0 ∧ x % (2 * (j : ℤ)) ≠ 0)).card =
      1 + X / 2 - X / (2 * j) := by
  induction X, hX using Nat.le_induction with
  | base =>
    rw [Nat.cast_one, Finset.Icc_self, Finset.filter_singleton, if_pos (Or.inl rfl),
      Finset.card_singleton, Nat.div_eq_of_lt (by omega : 1 < 2 * j)]
  | succ X hX ih =>
    have hnot : (X : ℤ) + 1 ∉ Finset.Icc (1 : ℤ) X := by simp
    rw [Nat.cast_succ, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      Finset.card_filter, Finset.sum_insert hnot, ← Finset.card_filter, ih, Nat.succ_div,
      Nat.succ_div (b := 2 * j)]
    have hd' : ((X : ℤ) + 1) % (2 * (j : ℤ)) = 0 ↔ 2 * j ∣ X + 1 := by
      rw [← Int.dvd_iff_emod_eq_zero]; norm_cast
    have hle : X / (2 * j) ≤ X / 2 := Nat.div_le_div_left (by omega) (by omega)
    by_cases hd : 2 * j ∣ X + 1
    · have h2 : 2 ∣ X + 1 := (Dvd.intro _ rfl).trans hd
      rw [if_neg (by rw [hd'.2 hd]; omega), if_pos hd, if_pos h2]
      omega
    · rw [if_neg hd]
      by_cases h2 : 2 ∣ X + 1
      · rw [if_pos (Or.inr ⟨by omega, fun h => hd (hd'.1 h)⟩), if_pos h2]
        omega
      · rw [if_neg (by omega), if_neg h2]
        omega

/-- **(ratified, Theorem E, conclusion).**  `W_{2j+}` has infinitely many infinite orbits.
Paper proof: `infinitelyManyInfiniteOrbits_of_trap` with `C` the evens and entry set `E`. -/
theorem evenPerm_infinitelyManyInfiniteOrbits (hj : 2 ≤ j) :
    InfinitelyManyInfiniteOrbits (evenPerm j (by omega)) := by
  have hj1 : 1 ≤ j := by omega
  apply infinitelyManyInfiniteOrbits_of_trap _ (evenPerm_trap hj1)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * (j : ℤ) * n + 2) ?_ ?_
  · intro a b hab
    simp only [add_left_inj] at hab
    exact_mod_cast mul_left_cancel₀ (by omega : (2 * (j : ℤ)) ≠ 0) hab
  · intro n
    have hpos : 0 < 2 * (j : ℤ) * n + 2 := by positivity
    refine ⟨hpos.le, (evenPerm_entry_iff hj1 hpos).2 ⟨hpos, ?_, ?_⟩⟩
    · rw [show 2 * (j : ℤ) * n + 2 = 2 * (j * n + 1) by ring]; omega
    · rw [show 2 * (j : ℤ) * n + 2 = 2 + 2 * j * n by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by norm_num) (by omega)]
      norm_num

end TheoremE

/-! ## Theorem E′: the mirror `r = 2j/(2j−1)` is a shift of `W_{2j+}` -/

section TheoremE'

variable {j : ℕ}

/-- `W_{2j/(2j−1)+}` as a permutation of `ℤ`. -/
def mirrorPerm (j : ℕ) (hj : 1 ≤ j) : Equiv.Perm ℤ :=
  wythoffPerm .plus (p := 2 * j) (q := 2 * j - 1) (by omega) (by omega)

/-- **(ratified, Theorem E′).**  `W_{2j/(2j−1)+}(n) = W_{2j+}(n + 1) − 1` on all of `ℤ`.  Paper
proof: odd `n = 2k − 1`: both sides are `2jk − 1`.  Even `n = 2k`, `N = 2j − 1`: the left side is
`k + ⌊k/N⌋`, the right side `k − 1 + ⌈(k+1)/N⌉`, and `⌈(k+1)/N⌉ = ⌊k/N⌋ + 1`. -/
theorem mirrorPerm_apply (hj : 1 ≤ j) (n : ℤ) :
    mirrorPerm j hj n = evenPerm j hj (n + 1) - 1 := by
  show wythoff .plus (2 * j) (2 * j - 1) n = _
  have hc : ((2 * j - 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by omega
  have h0 : (2 * (j : ℤ) - 1) ≠ 0 := by omega
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_two_mul n
  · rw [wythoff_plus_even, show 2 * k + 1 = 2 * (k + 1) - 1 by ring, evenPerm_two_mul_sub_one,
      hc]
    push_cast
    rw [show k * (2 * (j : ℤ)) = k + (2 * (j : ℤ) - 1) * k by ring, Int.add_mul_ediv_left _ _ h0,
      add_sub_cancel_right]
    ring
  · rw [wythoff_plus_odd, show 2 * k - 1 + 1 = 2 * k by ring, evenPerm_two_mul, hc]
    push_cast
    rw [show (2 * (j : ℤ)) - (2 * (j : ℤ) - 1) = 1 by ring, Int.ediv_one]
    ring

/-- **(ratified).**  Orbits of the mirror are the shifted orbits of `W_{2j+}`. -/
theorem permOrbit_mirrorPerm (hj : 1 ≤ j) (x : ℤ) :
    permOrbit (mirrorPerm j hj) x = (· - 1) '' permOrbit (evenPerm j hj) (x + 1) := by
  have key : ∀ z : ℤ, ∀ x : ℤ, (mirrorPerm j hj ^ z) x = (evenPerm j hj ^ z) (x + 1) - 1 := by
    intro z
    induction z using Int.induction_on with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
        mirrorPerm_apply, sub_add_cancel]
    | pred i ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      congr 2
      have h1 : evenPerm j hj ((mirrorPerm j hj)⁻¹ x + 1) - 1 = x := by
        rw [← mirrorPerm_apply]; simp
      rw [Equiv.Perm.eq_inv_iff_eq]
      omega
  unfold permOrbit
  rw [← Set.range_comp]
  congr 1
  funext z
  simp only [Function.comp_apply, key]

/-- **(ratified, Theorem E′, no finite orbit in `ℕ⁺`).** -/
theorem permOrbit_mirrorPerm_infinite (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (permOrbit (mirrorPerm j (by omega)) x).Infinite := by
  rw [permOrbit_mirrorPerm]
  exact (permOrbit_evenPerm_infinite hj (by omega)).image (sub_left_injective).injOn

/-- Membership in a mirror orbit, transported. -/
theorem mem_permOrbit_mirror (hj : 1 ≤ j) (x y : ℤ) :
    y ∈ permOrbit (mirrorPerm j hj) x ↔ y + 1 ∈ permOrbit (evenPerm j hj) (x + 1) := by
  rw [permOrbit_mirrorPerm]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨y + 1, h, by ring⟩

/-- **(ratified, Theorem E′, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x + 1 ∈ E`, and every orbit through `x > 0` has exactly one such point. -/
theorem mirror_isOrbitMin_iff (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (mirrorPerm j (by omega)) x, x ≤ y) ↔ x + 1 ∈ entrySet j := by
  have hj1 : 1 ≤ j := by omega
  have key : (∀ y ∈ permOrbit (mirrorPerm j hj1) x, x ≤ y) ↔
      (∀ y ∈ permOrbit (evenPerm j hj1) (x + 1), x + 1 ≤ y) := by
    constructor
    · intro h y hy
      have := h (y - 1) ((mem_permOrbit_mirror hj1 _ _).2 (by simpa using hy))
      omega
    · intro h y hy
      have := h (y + 1) ((mem_permOrbit_mirror hj1 _ _).1 hy)
      omega
  rw [key, isOrbitMin_iff hj (by omega)]
  constructor
  · rintro (h | h)
    · omega
    · exact h
  · exact Or.inr

/-- **(ratified, Theorem E′, indexing).** -/
theorem mirror_existsUnique (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    ∃! e, e + 1 ∈ entrySet j ∧ e ∈ permOrbit (mirrorPerm j (by omega)) x := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨e, ⟨he, hmem⟩, huniq⟩ := existsUnique_entry_mem_orbit hj (x := x + 1) (by omega)
  refine ⟨e - 1, ⟨by simpa using he, (mem_permOrbit_mirror hj1 _ _).2 (by simpa using hmem)⟩,
    fun e' ⟨he', hmem'⟩ => ?_⟩
  have := huniq (e' + 1) ⟨he', (mem_permOrbit_mirror hj1 _ _).1 hmem'⟩
  omega

/-- **(ratified, Theorem E′, conclusion).** -/
theorem mirrorPerm_infinitelyManyInfiniteOrbits (hj : 2 ≤ j) :
    InfinitelyManyInfiniteOrbits (mirrorPerm j (by omega)) := by
  have hj1 : 1 ≤ j := by omega
  have hodd : ∀ k : ℤ, mirrorPerm j hj1 (2 * k - 1) = 2 * j * k - 1 := fun k => by
    rw [mirrorPerm_apply, sub_add_cancel, evenPerm_two_mul]
  apply infinitelyManyInfiniteOrbits_of_trap _ (C := {y : ℤ | y % 2 = 1})
  · intro y hy
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k - 1 := ⟨(y + 1) / 2, by simp at hy; omega⟩
    show mirrorPerm j hj1 (2 * k - 1) % 2 = 1
    rw [hodd, show 2 * (j : ℤ) * k - 1 = 2 * (j * k - 1) + 1 by ring]
    omega
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * (j : ℤ) * n + 1) ?_ ?_
  · intro a b hab
    simp only [add_left_inj] at hab
    exact_mod_cast mul_left_cancel₀ (by omega : (2 * (j : ℤ)) ≠ 0) hab
  · intro n
    refine ⟨by positivity, ?_, ?_⟩
    · show (2 * (j : ℤ) * n + 1) % 2 = 1
      rw [show 2 * (j : ℤ) * n + 1 = 2 * (j * n) + 1 by ring]; omega
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k - 1 := ⟨(y + 1) / 2, by simp at hy; omega⟩
      rw [hodd] at hyx
      have h1 : (j : ℤ) * (k - n) = 1 := by linarith
      rcases le_or_gt (k - n) 0 with h | h <;> nlinarith

end TheoremE'

/-! ## Prop D: drift ordering -/

section PropD

variable {p q : ℕ}

/-- Stationary even-frequency of the forward chain: `q(R−1)/(2qR−q−R)` (`+`),
`q(R+1)/(2qR+q+R)` (`−`). -/
def fwdStat (s : Side) (p q : ℕ) : ℚ :=
  match s with
  | .plus => q * ((p : ℚ) - q - 1) / (2 * q * ((p : ℚ) - q) - q - ((p : ℚ) - q))
  | .minus => q * ((p : ℚ) - q + 1) / (2 * q * ((p : ℚ) - q) + q + ((p : ℚ) - q))

/-- Stationary even-frequency of the backward chain: `(q−1)/(p−2)` (`+`), `(q+1)/(p+2)` (`−`). -/
def bwdStat (s : Side) (p q : ℕ) : ℚ :=
  match s with
  | .plus => ((q : ℚ) - 1) / ((p : ℚ) - 2)
  | .minus => ((q : ℚ) + 1) / ((p : ℚ) + 2)

/-- **(ratified).**  `fwdStat` is stationary for `fwdProb` (`p ≥ 3`, so `2qR − q − R > 0`). -/
theorem fwdStat_stationary (s : Side) (hq : 0 < q) (hqp : q < p) (hp : 3 ≤ p) :
    fwdStat s p q * fwdProb s p q 0 0 + (1 - fwdStat s p q) * fwdProb s p q 1 0 =
      fwdStat s p q := by
  have hQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hQP : (q : ℚ) + 1 ≤ p := by exact_mod_cast hqp
  have hP : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hQ0 : (q : ℚ) ≠ 0 := by positivity
  have hR0 : (p : ℚ) - q ≠ 0 := (by linarith : (0 : ℚ) < p - q).ne'
  cases s
  · have hD : 2 * (q : ℚ) * ((p : ℚ) - q) - q - ((p : ℚ) - q) ≠ 0 :=
      (by nlinarith [mul_nonneg (sub_nonneg.2 hQ) (by linarith : (0 : ℚ) ≤ (p : ℚ) - q - 1)] :
        (0 : ℚ) < _).ne'
    simp (config := {decide := true}) only [fwdStat, fwdProb, fwdEven, if_true, if_false]
    generalize hDd : 2 * (q : ℚ) * ((p : ℚ) - q) - q - ((p : ℚ) - q) = D at hD ⊢
    field_simp
    subst hDd
    ring
  · have hD : 2 * (q : ℚ) * ((p : ℚ) - q) + q + ((p : ℚ) - q) ≠ 0 :=
      (by nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ q) (by linarith : (0 : ℚ) ≤ (p : ℚ) - q)] :
        (0 : ℚ) < _).ne'
    simp (config := {decide := true}) only [fwdStat, fwdProb, fwdEven, if_true, if_false]
    generalize hDd : 2 * (q : ℚ) * ((p : ℚ) - q) + q + ((p : ℚ) - q) = D at hD ⊢
    field_simp
    subst hDd
    ring

/-- **(ratified).**  `bwdStat` is stationary for `bwdProb`. -/
theorem bwdStat_stationary (s : Side) (hq : 0 < q) (hqp : q < p) (hp : 3 ≤ p) :
    bwdStat s p q * bwdProb s p q 0 0 + (1 - bwdStat s p q) * bwdProb s p q 1 0 =
      bwdStat s p q := by
  have hP : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hP0 : (p : ℚ) ≠ 0 := (by linarith : (0 : ℚ) < p).ne'
  have hP2 : (p : ℚ) - 2 ≠ 0 := (by linarith : (0 : ℚ) < p - 2).ne'
  have hP2' : (p : ℚ) + 2 ≠ 0 := (by linarith : (0 : ℚ) < p + 2).ne'
  cases s <;>
  · simp (config := {decide := true}) only [bwdStat, bwdProb, bwdEven, if_true, if_false]
    field_simp
    ring

/-- Forward log-drift of the stationary chain: steps `log(r/2)` (even) and `log(s/2)` (odd). -/
noncomputable def fwdDrift (s : Side) (p q : ℕ) : ℝ :=
  (fwdStat s p q : ℝ) * Real.log ((p : ℝ) / q / 2) +
    (1 - (fwdStat s p q : ℝ)) * Real.log ((p : ℝ) / ((p : ℝ) - q) / 2)

/-- The i.i.d. forward drift `½ log(r/2) + ½ log(s/2)`. -/
noncomputable def iidFwdDrift (p q : ℕ) : ℝ :=
  (Real.log ((p : ℝ) / q / 2) + Real.log ((p : ℝ) / ((p : ℝ) - q) / 2)) / 2

/-- Backward log-drift of the stationary chain: steps `log(2/r)` and `log(2/s)`. -/
noncomputable def bwdDrift (s : Side) (p q : ℕ) : ℝ :=
  (bwdStat s p q : ℝ) * Real.log (2 / ((p : ℝ) / q)) +
    (1 - (bwdStat s p q : ℝ)) * Real.log (2 / ((p : ℝ) / ((p : ℝ) - q)))

/-- The i.i.d. backward drift, weights `(q/p, R/p)`. -/
noncomputable def iidBwdDrift (p q : ℕ) : ℝ :=
  (q : ℝ) / p * Real.log (2 / ((p : ℝ) / q)) +
    ((p : ℝ) - q) / p * Real.log (2 / ((p : ℝ) / ((p : ℝ) - q)))

/-- Shared bounds for Prop D. -/
theorem propD_setup (hq : 0 < q) (hqp : q < p) (hne : q ≠ p - q) :
    (1 : ℝ) ≤ q ∧ (1 : ℝ) ≤ (p : ℝ) - q ∧ (3 : ℝ) ≤ p ∧ (q : ℝ) ≠ (p : ℝ) - q := by
  have h3 : 3 ≤ p := by omega
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQP : (q : ℝ) + 1 ≤ p := by exact_mod_cast hqp
  refine ⟨hQ, by linarith, by exact_mod_cast h3, fun h => hne ?_⟩
  have : (p : ℝ) = q + q := by linarith
  have : p = q + q := by exact_mod_cast this
  omega

/-- `(R − Q)(log R − log Q) > 0` off the diagonal. -/
theorem sub_mul_log_sub_pos {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hne : Q ≠ R) :
    0 < (R - Q) * (Real.log R - Real.log Q) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact mul_pos (by linarith) (by linarith [Real.log_lt_log hQ h])
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith [Real.log_lt_log hR h])

theorem log_div_div_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x / y / 2) = Real.log x - Real.log y - Real.log 2 := by
  rw [Real.log_div (by positivity) (by norm_num), Real.log_div hx.ne' hy.ne']

theorem log_two_div_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (2 / (x / y)) = Real.log 2 - Real.log x + Real.log y := by
  rw [Real.log_div (by norm_num) (by positivity), Real.log_div hx.ne' hy.ne']; ring

/-- The forward drift excess: `(π − ½)(log R − log q)`. -/
theorem fwdDrift_sub (s : Side) (hq : 0 < q) (hqp : q < p) :
    fwdDrift s p q - iidFwdDrift p q =
      (((fwdStat s p q : ℚ) : ℝ) - 1 / 2) * (Real.log ((p : ℝ) - q) - Real.log q) := by
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq
  have hQP : (q : ℝ) < p := by exact_mod_cast hqp
  unfold fwdDrift iidFwdDrift
  rw [log_div_div_two (by linarith) hQ, log_div_div_two (by linarith) (by linarith)]
  ring

/-- The backward drift excess: `(π_b − q/p)(log q − log R)`. -/
theorem bwdDrift_sub (s : Side) (hq : 0 < q) (hqp : q < p) :
    bwdDrift s p q - iidBwdDrift p q =
      (((bwdStat s p q : ℚ) : ℝ) - q / p) * (Real.log q - Real.log ((p : ℝ) - q)) := by
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq
  have hQP : (q : ℝ) < p := by exact_mod_cast hqp
  have hR : ((p : ℝ) - q) / p = 1 - q / p := by
    rw [sub_div, div_self (by linarith : (0 : ℝ) < p).ne']
  unfold bwdDrift iidBwdDrift
  rw [log_two_div_div (by linarith) hQ, log_two_div_div (by linarith) (by linarith), hR]
  ring

/-- **(ratified, Prop D, `+`).**  Off `r = 2`, both drifts exceed the i.i.d. drifts.  Paper
proof: drift − iid `= (π_E − ½) log(R/q)` with `π_E⁺ − ½ = (R−q)/(2(2qR−q−R))`; backward
`(π_E^b − q/p) log(q/R) = (q−R) log(q/R)/(p(p−2))`. -/
theorem propD_plus (hq : 0 < q) (hqp : q < p) (hne : q ≠ p - q) :
    iidFwdDrift p q < fwdDrift .plus p q ∧ iidBwdDrift p q < bwdDrift .plus p q := by
  obtain ⟨hQ, hR, hP, hne'⟩ := propD_setup hq hqp hne
  have hsign := sub_mul_log_sub_pos (by linarith : (0 : ℝ) < q)
    (by linarith : (0 : ℝ) < (p : ℝ) - q) hne'
  have hD : 0 < 2 * (q : ℝ) * ((p : ℝ) - q) - q - ((p : ℝ) - q) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hQ) (sub_nonneg.2 hR)]
  have hD0 := hD.ne'
  have hP0 : (p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  have hP2 : (p : ℝ) - 2 ≠ 0 := (by linarith : (0 : ℝ) < p - 2).ne'
  constructor
  · have hπ : ((fwdStat .plus p q : ℚ) : ℝ) - 1 / 2 =
        (((p : ℝ) - q) - q) / (2 * (2 * (q : ℝ) * ((p : ℝ) - q) - q - ((p : ℝ) - q))) := by
      simp only [fwdStat]; push_cast
      generalize hDd : 2 * (q : ℝ) * ((p : ℝ) - q) - q - ((p : ℝ) - q) = D at hD0 ⊢
      field_simp
      subst hDd
      ring
    have h1 := fwdDrift_sub .plus hq hqp
    rw [hπ, div_mul_eq_mul_div] at h1
    have : 0 < (((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) /
        (2 * (2 * (q : ℝ) * ((p : ℝ) - q) - q - ((p : ℝ) - q))) := div_pos hsign (by linarith)
    linarith
  · have hπ : ((bwdStat .plus p q : ℚ) : ℝ) - q / p =
        ((q : ℝ) - ((p : ℝ) - q)) / (p * (p - 2)) := by
      simp only [bwdStat]; push_cast; field_simp; ring
    have h1 := bwdDrift_sub .plus hq hqp
    rw [hπ, div_mul_eq_mul_div] at h1
    have : 0 < ((q : ℝ) - ((p : ℝ) - q)) * (Real.log q - Real.log ((p : ℝ) - q)) /
        (p * (p - 2)) := by
      apply div_pos _ (by nlinarith)
      rw [show ((q : ℝ) - ((p : ℝ) - q)) * (Real.log q - Real.log ((p : ℝ) - q)) =
        (((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) by ring]
      exact hsign
    linarith

/-- **(ratified, Prop D, `−`).**  Off `r = 2`, both drifts fall below the i.i.d. drifts:
`π_E⁻ − ½ = (q−R)/(2(2qR+q+R))`, `π_E^{b−} − q/p = (R−q)/(p(p+2))`. -/
theorem propD_minus (hq : 0 < q) (hqp : q < p) (hne : q ≠ p - q) :
    fwdDrift .minus p q < iidFwdDrift p q ∧ bwdDrift .minus p q < iidBwdDrift p q := by
  obtain ⟨hQ, hR, hP, hne'⟩ := propD_setup hq hqp hne
  have hsign := sub_mul_log_sub_pos (by linarith : (0 : ℝ) < q)
    (by linarith : (0 : ℝ) < (p : ℝ) - q) hne'
  have hD : 0 < 2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ (p : ℝ) - q)]
  have hD0 := hD.ne'
  have hP0 : (p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  have hP2 : (p : ℝ) + 2 ≠ 0 := (by linarith : (0 : ℝ) < p + 2).ne'
  constructor
  · have hπ : ((fwdStat .minus p q : ℚ) : ℝ) - 1 / 2 =
        ((q : ℝ) - ((p : ℝ) - q)) / (2 * (2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q))) := by
      simp only [fwdStat]; push_cast
      generalize hDd : 2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q) = D at hD0 ⊢
      field_simp
      subst hDd
      ring
    have h1 := fwdDrift_sub .minus hq hqp
    rw [hπ, div_mul_eq_mul_div] at h1
    have : 0 < (((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) /
        (2 * (2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q))) := div_pos hsign (by linarith)
    have h2 : ((q : ℝ) - ((p : ℝ) - q)) * (Real.log ((p : ℝ) - q) - Real.log q) /
        (2 * (2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q))) =
        -((((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) /
        (2 * (2 * (q : ℝ) * ((p : ℝ) - q) + q + ((p : ℝ) - q)))) := by ring
    linarith
  · have hπ : ((bwdStat .minus p q : ℚ) : ℝ) - q / p =
        (((p : ℝ) - q) - q) / (p * (p + 2)) := by
      simp only [bwdStat]; push_cast; field_simp; ring
    have h1 := bwdDrift_sub .minus hq hqp
    rw [hπ, div_mul_eq_mul_div] at h1
    have : 0 < (((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) /
        (p * (p + 2)) := div_pos hsign (by nlinarith)
    have h2 : (((p : ℝ) - q) - q) * (Real.log q - Real.log ((p : ℝ) - q)) / (p * (p + 2)) =
        -((((p : ℝ) - q) - q) * (Real.log ((p : ℝ) - q) - Real.log q) / (p * (p + 2))) := by
      ring
    linarith

end PropD

end CollatzMoonshot.WythoffRational
