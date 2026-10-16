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

section Lemma1

variable (s : Side) {p q : ℕ}

/-- **(ratified, Lemma 1, even branch).**  Paper proof: for `1 ≤ t ≤ q − 1`, `tp/q ∉ ℤ`
(coprime), and `t ↦ q − t` sends `⌊tp/q⌋` to `p − 1 − ⌊tp/q⌋`, of the other parity (`p` even,
`q` odd, no fixed point).  `+` adds `t = 0` (image `0`, even); for `−` the residue `t = 0` has
image `−1` (odd; it stands for the paper's `t = q`, image `p − 1`). -/
theorem card_even_image_even (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    ((Finset.range q).filter fun t : ℕ => wythoff s p q (2 * (t : ℤ)) % 2 = 0).card =
      if s = .plus then (q + 1) / 2 else (q - 1) / 2 := by
  sorry

/-- **(ratified, Lemma 1, odd branch).**  The same with `R = p − q`: `u ↦ R − u` on the images
`W(2u + 1)`, `u < R`; `+` adds the odd image `p − 1` (at `u = R − 1`), `−` the even image `0`. -/
theorem card_even_image_odd (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    ((Finset.range (p - q)).filter fun u : ℕ => wythoff s p q (2 * (u : ℤ) + 1) % 2 = 0).card =
      if s = .plus then (p - q - 1) / 2 else (p - q + 1) / 2 := by
  sorry

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
  sorry

/-- **(ratified, Theorem T, chain form).**  For even `p` the forward or backward parity chain has
an absorbing state iff the side is `+` and `q = 1` or `p − q = 1`.  Paper proof: read off the
diagonal entries.  `+`: `F(E→E) = (q+1)/(2q)` and `B(O→O) = (R+1)/p` are `1` iff `q = 1`;
`F(O→O) = (R+1)/(2R)` and `B(E→E) = (q+1)/p` are `1` iff `R = 1`.  `−`: the diagonal entries
`(q−1)/(2q)`, `(R−1)/(2R)`, `(q−1)/p`, `(R−1)/p` are all `< 1`. -/
theorem absorbing_iff (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p) :
    (∃ e : ZMod 2, fwdProb s p q e e = 1 ∨ bwdProb s p q e e = 1) ↔
      s = .plus ∧ (q = 1 ∨ p - q = 1) := by
  sorry

end TheoremT

/-! ## Theorem E: the even integers `r = 2j` are solved -/

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
  sorry

/-- **(ratified).**  `W_{2j+}(2k − 1) = k + ⌊(k − 1)/(2j − 1)⌋`, the `k`-th non-multiple of
`2j`. -/
theorem evenPerm_two_mul_sub_one (hj : 1 ≤ j) (k : ℤ) :
    evenPerm j hj (2 * k - 1) = k + (k - 1) / (2 * j - 1) := by
  sorry

/-- **(ratified).**  `1` is a fixed point: `{1}` is a finite orbit. -/
theorem permOrbit_evenPerm_one (hj : 1 ≤ j) : permOrbit (evenPerm j hj) 1 = {1} := by
  sorry

/-- **(ratified).**  The evens are a trap whose entry points are exactly `E` on `ℕ⁺`
(`σ(2ℤ) = 2jℤ`). -/
theorem evenPerm_entry_iff (hj : 1 ≤ j) {x : ℤ} (hx : 0 < x) :
    x ∈ {y : ℤ | y % 2 = 0} \ evenPerm j hj '' {y : ℤ | y % 2 = 0} ↔ x ∈ entrySet j := by
  sorry

/-- **(ratified, Theorem E, structure).**  For `j ≥ 2`, every orbit through `x > 1` meets `E`
in exactly one point.  Paper proof: evens go up into `2jℕ⁺` (`×j`); odd `n ≥ 3` go down
(`k + ⌊(k−1)/(2j−1)⌋ < 2k − 1`); the preimage of an odd is odd and larger; backward from `2jk`
the preimage `2k` is smaller.  So the orbit is (increasing odd backward tail) → one point of
`E` → (increasing even forward tail in `2jℕ⁺`). -/
theorem existsUnique_entry_mem_orbit (hj : 2 ≤ j) {x : ℤ} (hx : 1 < x) :
    ∃! e, e ∈ entrySet j ∧ e ∈ permOrbit (evenPerm j (by omega)) x := by
  sorry

/-- **(ratified, Theorem E, minimum).**  That point of `E` is the minimum of the orbit. -/
theorem entry_le_of_mem_orbit (hj : 2 ≤ j) {x e : ℤ} (hx : 1 < x) (he : e ∈ entrySet j)
    (heo : e ∈ permOrbit (evenPerm j (by omega)) x) :
    ∀ y ∈ permOrbit (evenPerm j (by omega)) x, e ≤ y := by
  sorry

/-- **(ratified, Theorem E, no other finite orbit).**  Every orbit through `x > 1` is
infinite. -/
theorem permOrbit_evenPerm_infinite (hj : 2 ≤ j) {x : ℤ} (hx : 1 < x) :
    (permOrbit (evenPerm j (by omega)) x).Infinite := by
  sorry

/-- **(ratified, Theorem E, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x = 1` or `x ∈ E`. -/
theorem isOrbitMin_iff (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (evenPerm j (by omega)) x, x ≤ y) ↔ x = 1 ∨ x ∈ entrySet j := by
  sorry

/-- **(ratified, Theorem E, indexing).**  The orbits meeting `ℕ⁺` are indexed by `{1} ∪ E`. -/
theorem permOrbit_bijOn (hj : 2 ≤ j) :
    Set.BijOn (permOrbit (evenPerm j (by omega))) ({1} ∪ entrySet j)
      {O | ∃ x : ℤ, 0 < x ∧ O = permOrbit (evenPerm j (by omega)) x} := by
  sorry

/-- **(ratified, Theorem E, count).**  `#{orbit minima ≤ X} = 1 + ⌊X/2⌋ − ⌊X/2j⌋`. -/
theorem card_orbitMin_le (hj : 2 ≤ j) (X : ℕ) (hX : 1 ≤ X) :
    ((Finset.Icc (1 : ℤ) X).filter fun x : ℤ => x = 1 ∨ (x % 2 = 0 ∧ x % (2 * (j : ℤ)) ≠ 0)).card =
      1 + X / 2 - X / (2 * j) := by
  sorry

/-- **(ratified, Theorem E, conclusion).**  `W_{2j+}` has infinitely many infinite orbits.
Paper proof: `infinitelyManyInfiniteOrbits_of_trap` with `C` the evens and entry set `E`. -/
theorem evenPerm_infinitelyManyInfiniteOrbits (hj : 2 ≤ j) :
    InfinitelyManyInfiniteOrbits (evenPerm j (by omega)) := by
  sorry

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
  sorry

/-- **(ratified).**  Orbits of the mirror are the shifted orbits of `W_{2j+}`. -/
theorem permOrbit_mirrorPerm (hj : 1 ≤ j) (x : ℤ) :
    permOrbit (mirrorPerm j hj) x = (· - 1) '' permOrbit (evenPerm j hj) (x + 1) := by
  sorry

/-- **(ratified, Theorem E′, no finite orbit in `ℕ⁺`).** -/
theorem permOrbit_mirrorPerm_infinite (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (permOrbit (mirrorPerm j (by omega)) x).Infinite := by
  sorry

/-- **(ratified, Theorem E′, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x + 1 ∈ E`, and every orbit through `x > 0` has exactly one such point. -/
theorem mirror_isOrbitMin_iff (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (mirrorPerm j (by omega)) x, x ≤ y) ↔ x + 1 ∈ entrySet j := by
  sorry

/-- **(ratified, Theorem E′, indexing).** -/
theorem mirror_existsUnique (hj : 2 ≤ j) {x : ℤ} (hx : 0 < x) :
    ∃! e, e + 1 ∈ entrySet j ∧ e ∈ permOrbit (mirrorPerm j (by omega)) x := by
  sorry

/-- **(ratified, Theorem E′, conclusion).** -/
theorem mirrorPerm_infinitelyManyInfiniteOrbits (hj : 2 ≤ j) :
    InfinitelyManyInfiniteOrbits (mirrorPerm j (by omega)) := by
  sorry

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
  sorry

/-- **(ratified).**  `bwdStat` is stationary for `bwdProb`. -/
theorem bwdStat_stationary (s : Side) (hq : 0 < q) (hqp : q < p) (hp : 3 ≤ p) :
    bwdStat s p q * bwdProb s p q 0 0 + (1 - bwdStat s p q) * bwdProb s p q 1 0 =
      bwdStat s p q := by
  sorry

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

/-- **(ratified, Prop D, `+`).**  Off `r = 2`, both drifts exceed the i.i.d. drifts.  Paper
proof: drift − iid `= (π_E − ½) log(R/q)` with `π_E⁺ − ½ = (R−q)/(2(2qR−q−R))`; backward
`(π_E^b − q/p) log(q/R) = (q−R) log(q/R)/(p(p−2))`. -/
theorem propD_plus (hq : 0 < q) (hqp : q < p) (hne : q ≠ p - q) :
    iidFwdDrift p q < fwdDrift .plus p q ∧ iidBwdDrift p q < bwdDrift .plus p q := by
  sorry

/-- **(ratified, Prop D, `−`).**  Off `r = 2`, both drifts fall below the i.i.d. drifts:
`π_E⁻ − ½ = (q−R)/(2(2qR+q+R))`, `π_E^{b−} − q/p = (R−q)/(p(p+2))`. -/
theorem propD_minus (hq : 0 < q) (hqp : q < p) (hne : q ≠ p - q) :
    fwdDrift .minus p q < iidFwdDrift p q ∧ bwdDrift .minus p q < iidBwdDrift p q := by
  sorry

end PropD

end CollatzMoonshot.WythoffRational
