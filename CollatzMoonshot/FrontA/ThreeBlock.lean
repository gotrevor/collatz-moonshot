/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Paradoxical

/-!
# Front A: the three-odd-block rung of the paradoxical ladder

`FrontA/Paradoxical.lean` closes rungs 1 and 2 of the *odd-block ladder* for acyclic paradoxical
shortcut segments: a word whose ones form one block (`headBlock_not_acyclicParadoxical`,
Rozier--Terracol Appendix A) or two blocks (`le_two_blocks_not_acyclicParadoxical`) realizes no
acyclic paradoxical start.  Rung 2 is **sharp**: `acyclicParadoxical_seven_eight` is a genuine
three-block witness (`n = 7`, `m = 8`).

This module opens **rung 3**, the first rung whose answer is a *classification* rather than an
exclusion:

> **Rung-3 conjecture.**  Every acyclic paradoxical segment whose word has three odd blocks has
> length `8`.

Exactly four front-normalized three-block words admit an acyclic paradoxical start, all of
length `8` (`experiments/block_ladder_probe.py`, exhaustive to length `26`):
`(b,c,d,e,f,g) = (1,1,2,2,2,0)` from `n = 25`, `(1,1,3,1,1,1)` from `n = 9`,
`(2,2,2,1,1,0)` from `n = 19`, and `(3,1,1,2,1,0)` from `n = 7`.

## What this module proves (sorry-free)

Write a three-block word as `[T]^b [F]^c [T]^d [F]^e [T]^f [F]^g` (`b,c,d,e,f ≥ 1`, `g ≥ 0`),
`m = b+c+d+e+f+g`, `k = b+d+f`, `D = 2^m - 3^k`, and split the itinerary at the two joints:
`n → X → Z → y`.  The three head-block segment identities are

    (I)   2^(b+c) X + 2^b = 3^b (n+1)
    (II)  2^(d+e) Z + 2^d = 3^d (X+1)
    (III) 2^(f+g) y + 2^f = 3^f (Z+1).

* **`threeBlock_le_of_AB_C` / `threeBlock_le_of_A_BC` — the block-merge reduction.**  Rung 2 is
  reused as a black box on the two-block sub-segments.  If `[T]^b[F]^c[T]^d[F]^e` is subcritical
  then `Z ≤ n`, and if additionally `[T]^f[F]^g` is subcritical then `y ≤ Z ≤ n`; symmetrically
  from the other end.  Hence an acyclic paradoxical three-block segment must have
  `(¬subcrit AB ∨ ¬subcrit C)` **and** `(¬subcrit A ∨ ¬subcrit BC)`
  (`threeBlock_merge_reduction`).  Host census: this cuts the length-`≤24` search space from
  126824 subcritical words to 34832.
* **`threeBlock_master`** — the exact `ℤ` identity obtained by eliminating `X` and `Z`.
* **`threeBlock_cascade`** — the 2-adic normal form.  `2^b ∣ n+1`, `2^d ∣ X+1`, `2^f ∣ Z+1`,
  and with `n+1 = 2^b w₁`, `X+1 = 2^d w₂`, `Z+1 = 2^f w₃` the whole segment becomes the
  **integer cascade**

      3^b w₁ + 2^c = 2^(c+d) w₂ + 1,   3^d w₂ + 2^e = 2^(e+f) w₃ + 1,   3^f w₃ = 2^g y + 1.

* **`threeBlock_criterion`** — acyclicity is *equivalent* to one inequality in `w₁`:

      n < y   ↔   D · w₁ ≤ 3^f · T − 2^(c+d+e+f),   T = 2^(c+d+e) − 2^(c+d) + 3^d (2^c − 1).

* **`threeBlock_of_gap`** — if the corresponding `∀`-gap over integer cascade triples holds, the
  segment is not acyclic paradoxical.  This is the rung-3 analogue of `core_of_gap`.

## Where the deep content sits (`threeBlock_containment`, disclosed)

Eliminating `w₂` from the cascade gives `3^(b+d) w₁ = 2^(c+d+e+f) w₃ − T`, so `w₃ ≥ 1` alone
yields the division-free **real relaxation**

    (R3)   D · (2^(c+d+e+f) − T)  ≤  3^(b+d) · 2^(c+d+e) · (3^f − 2^f).

Equivalently (divide by `2^(c+d+e+f)` and use `2^m = 2^(c+d+e+f)·2^(b+g)`), the whole content of
`w₃ ≥ 1` is the single division-free inequality `3^(b+d)(3^f − 1) < 2^(b+g)·U`, which is exactly
what `threeBlock_gap_of_real` consumes.

**(R3) is provably insufficient** (host census, exact integers): the number of tuples that
*fail* it grows without bound — 18 at `m = 8`, 317 at `m = 16`, 2931 at `m = 27`, 88718 in total
for `m ≤ 40`.  This mirrors the rung-2 finding that the real relaxation of `b+d ≤ 5` is feasible
at unbounded `g`.

**The integrality of the *interior* joint is what makes rung 3 finite.**  Keeping `w₂ ∈ ℕ` —
i.e. `w₂ ≥ ⌈(2^(e+f) − 2^e + 1)/3^d⌉` before dividing again by `3^b` — collapses the same
search to **27 tuples in total**, at lengths `m ∈ {5, 8, 16, 27}` only, exhaustively verified
for all `m ≤ 130` and all `k` with `3^k/2^m > 1/8`.  Seventeen of the 27 sit at `m = 8`
(where the four true solutions live).

That is a genuine *effectivity asymmetry* against Front B's `m`-cycle ladder: rung 3 of the
odd-block ladder is cut to a finite explicit list by a **two-level integer ceiling**, with no
linear form in logarithms — whereas rung 2 needed the Baker-grade `sep_two_three`, and Front B's
`m`-cycle ladder needs Baker at every rung.
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot CollatzMoonshot.FrontB

/-! ## Identity-level head-block tools -/

/-- **Head-block endpoint bound, identity form.**  The word hypothesis of
`headBlock_endpoint_le` is only ever used to produce the segment identity, so state the bound
directly from it: this is what lets rung 2 be reused on *interior* sub-segments of a longer
word, where no `traceWord` equation is available. -/
theorem headBlock_le_of_identity {n q t y : ℕ}
    (hid : 2 ^ (q + t) * y + 2 ^ q = 3 ^ q * (n + 1))
    (hsub : 3 ^ q < 2 ^ (q + t)) :
    y ≤ n := by
  have hlt : 3 ^ q * (n + 1) < 2 ^ (q + t) * (n + 1) :=
    Nat.mul_lt_mul_of_pos_right hsub (Nat.succ_pos n)
  have h2q : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hy : 2 ^ (q + t) * y < 2 ^ (q + t) * (n + 1) := by omega
  have := Nat.lt_of_mul_lt_mul_left hy
  omega

/-- **2-adic normal form of a head block.**  From `2^(q+t) y + 2^q = 3^q (n+1)`: the odd run
forces `2^q ∣ n+1`, and writing `n + 1 = 2^q w` the identity becomes `3^q w = 2^t y + 1`.
(The `u = x+1` conjugation of `headBlock_dvd_succ`, in identity form.) -/
theorem headBlock_scale {n q t y : ℕ}
    (hid : 2 ^ (q + t) * y + 2 ^ q = 3 ^ q * (n + 1)) :
    ∃ w : ℕ, n + 1 = 2 ^ q * w ∧ 3 ^ q * w = 2 ^ t * y + 1 := by
  have key : 3 ^ q * (n + 1) = 2 ^ q * (2 ^ t * y + 1) := by rw [← hid, pow_add]; ring
  have hcop : Nat.Coprime (2 ^ q) (3 ^ q) :=
    Nat.Coprime.pow_right q (Nat.Coprime.pow_left q (show Nat.Coprime 2 3 by decide))
  obtain ⟨w, hw⟩ : (2 : ℕ) ^ q ∣ (n + 1) := hcop.dvd_of_dvd_mul_left ⟨2 ^ t * y + 1, key⟩
  refine ⟨w, hw, ?_⟩
  have h : 2 ^ q * (3 ^ q * w) = 2 ^ q * (2 ^ t * y + 1) := by rw [← key, hw]; ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-! ## The block-merge reduction (rung 2 reused as a black box) -/

/-- **Merge from the left.**  If the two-block prefix `[T]^b[F]^c[T]^d[F]^e` is subcritical and
the trailing block `[T]^f[F]^g` is subcritical, the whole three-block segment ends at or below
its start.  `two_block_residue_core` gives `Z ≤ n`, then the head-block bound gives `y ≤ Z`. -/
theorem threeBlock_le_of_AB_C {b c d e f g n X Z y : ℕ} (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hAB : 3 ^ (b + d) < 2 ^ (b + c + d + e))
    (hC : 3 ^ f < 2 ^ (f + g)) :
    y ≤ n :=
  le_trans (headBlock_le_of_identity hIII hC)
    (two_block_residue_core b c d e n X Z hb hd hI hII hAB)

/-- **Merge from the right.**  If the head block `[T]^b[F]^c` is subcritical and the two-block
suffix `[T]^d[F]^e[T]^f[F]^g` is subcritical, the segment ends at or below its start. -/
theorem threeBlock_le_of_A_BC {b c d e f g n X Z y : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hA : 3 ^ b < 2 ^ (b + c))
    (hBC : 3 ^ (d + f) < 2 ^ (d + e + f + g)) :
    y ≤ n :=
  le_trans (two_block_residue_core d e f g X Z y hd hf hII hIII hBC)
    (headBlock_le_of_identity hI hA)

/-- **The block-merge reduction.**  An acyclic three-block segment must defeat *both* two-block
splittings: the `AB | C` split needs `AB` or `C` supercritical, and the `A | BC` split needs `A`
or `BC` supercritical.  Host census (exact integers, all lengths `≤ 24`): this removes 91992 of
the 126824 subcritical three-block words. -/
theorem threeBlock_merge_reduction {b c d e f g n X Z y : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hlt : n < y) :
    (¬ 3 ^ (b + d) < 2 ^ (b + c + d + e) ∨ ¬ 3 ^ f < 2 ^ (f + g)) ∧
      (¬ 3 ^ b < 2 ^ (b + c) ∨ ¬ 3 ^ (d + f) < 2 ^ (d + e + f + g)) := by
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hAB, hC⟩ := hcon
    exact absurd (threeBlock_le_of_AB_C hb hd hI hII hIII (by simpa using hAB)
      (by simpa using hC)) (by omega)
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hA, hBC⟩ := hcon
    exact absurd (threeBlock_le_of_A_BC hd hf hI hII hIII (by simpa using hA)
      (by simpa using hBC)) (by omega)

/-! ## The exact three-block criterion -/

/-- **The three-block master identity.**  Eliminating the two interior values `X`, `Z` from the
segment identities leaves an exact `ℤ` identity between the endpoint `y` and the start `n`. -/
theorem threeBlock_master {b c d e f g n X Z y : ℕ}
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1)) :
    (2 : ℤ) ^ (b + c + d + e + f + g) * y + 2 ^ (b + c + d + e + f)
        + 3 ^ f * 2 ^ (b + c + d) + 3 ^ (d + f) * 2 ^ b
      = 3 ^ (b + d + f) * ((n : ℤ) + 1) + 3 ^ f * 2 ^ (b + c + d + e)
        + 3 ^ (d + f) * 2 ^ (b + c) := by
  have hIz : (2 : ℤ) ^ (b + c) * X + 2 ^ b = 3 ^ b * ((n : ℤ) + 1) := by exact_mod_cast hI
  have hIIz : (2 : ℤ) ^ (d + e) * Z + 2 ^ d = 3 ^ d * ((X : ℤ) + 1) := by exact_mod_cast hII
  have hIIIz : (2 : ℤ) ^ (f + g) * y + 2 ^ f = 3 ^ f * ((Z : ℤ) + 1) := by exact_mod_cast hIII
  linear_combination (3 : ℤ) ^ (d + f) * hIz + (2 : ℤ) ^ (b + c) * 3 ^ f * hIIz
    + (2 : ℤ) ^ (b + c + d + e) * hIIIz

/-- **The three-block slack identity.**  With `n + 1 = 2^b w₁`, the criterion defect and the
endpoint defect are the *same* quantity up to the two scales:

    2^b · (RHS − D·w₁)  =  2^m · (y − (n+1)),
    D = 2^m − 3^k,  RHS = 3^f·T − 2^(c+d+e+f),  T = 2^(c+d+e) − 2^(c+d) + 3^d(2^c − 1).

The rung-3 analogue of `slack_identity`; both directions of `threeBlock_criterion` fall out. -/
theorem threeBlock_slack {b c d e f g n X Z y w₁ : ℕ}
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hw : n + 1 = 2 ^ b * w₁) :
    (2 : ℤ) ^ b * ((3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f))
        - ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁))
      = 2 ^ (b + c + d + e + f + g) * ((y : ℤ) - 2 ^ b * w₁) := by
  have hM := threeBlock_master hI hII hIII
  have hwz : (n : ℤ) + 1 = 2 ^ b * w₁ := by exact_mod_cast hw
  rw [hwz] at hM
  linear_combination -hM

/-- **The three-block criterion.**  With `n + 1 = 2^b w₁`, the acyclic condition `n < y` is
*equivalent* to a single inequality in `w₁`:

    (2^m − 3^k) · w₁  ≤  3^f · T − 2^(c+d+e+f),
    T = 2^(c+d+e) − 2^(c+d) + 3^d (2^c − 1),  m = b+c+d+e+f+g,  k = b+d+f.

This is the rung-3 analogue of the `hUP` step inside `core_of_gap`.  Note the sharp form uses
`y ≥ n + 1` rather than `y > n` scaled by `2^m` — worth a whole factor `2^(m−b)` on the right,
and the difference between a finite and an infinite relaxation. -/
theorem threeBlock_criterion {b c d e f g n X Z y w₁ : ℕ}
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hw : n + 1 = 2 ^ b * w₁) :
    n < y ↔ ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁
      ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)) - 2 ^ (c + d + e + f) := by
  have hs := threeBlock_slack hI hII hIII hw
  have hwz : (n : ℤ) + 1 = 2 ^ b * w₁ := by exact_mod_cast hw
  have hpos : (0 : ℤ) < 2 ^ b := by positivity
  have hmpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) := by positivity
  constructor
  · intro hlt
    have hy : (n : ℤ) + 1 ≤ y := by exact_mod_cast hlt
    have h1 : (0 : ℤ) ≤ (y : ℤ) - 2 ^ b * w₁ := by linarith [hwz, hy]
    have h3 : (2 : ℤ) ^ b * 0
        ≤ 2 ^ b * ((3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
              - 2 ^ (c + d + e + f))
            - ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁)) := by
      rw [hs]; simpa using mul_nonneg hmpos.le h1
    have := le_of_mul_le_mul_left h3 hpos
    linarith
  · intro hle
    have h3 : (2 : ℤ) ^ (b + c + d + e + f + g) * 0
        ≤ 2 ^ (b + c + d + e + f + g) * ((y : ℤ) - 2 ^ b * w₁) := by
      rw [← hs]
      simpa using mul_nonneg hpos.le (by linarith :
        (0 : ℤ) ≤ (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f))
          - ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁))
    have h4 := le_of_mul_le_mul_left h3 hmpos
    have : (n : ℤ) < y := by linarith [hwz, h4]
    exact_mod_cast this

/-! ## The integer cascade and the gap form -/

/-- **The integer cascade.**  Every three-block segment carries three 2-adic scales
`w₁, w₂, w₃ ≥ 1` (`n+1 = 2^b w₁`, `X+1 = 2^d w₂`, `Z+1 = 2^f w₃`) linked by two exact integer
equations.  These — and specifically the requirement that the *interior* `w₂` be an integer —
are what makes the rung-3 search space finite. -/
theorem threeBlock_cascade {b c d e f g n X Z y : ℕ}
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1)) :
    ∃ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ ∧ n + 1 = 2 ^ b * w₁ ∧
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 ∧
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 ∧
      3 ^ f * w₃ = 2 ^ g * y + 1 := by
  obtain ⟨w₁, hw₁, he₁⟩ := headBlock_scale hI
  obtain ⟨w₂, hw₂, he₂⟩ := headBlock_scale hII
  obtain ⟨w₃, hw₃, he₃⟩ := headBlock_scale hIII
  have h3 : 1 ≤ w₃ := by
    rcases Nat.eq_zero_or_pos w₃ with h | h
    · simp [h] at hw₃
    · exact h
  refine ⟨w₁, w₂, w₃, h3, hw₁, ?_, ?_, he₃⟩
  · -- `3^b w₁ = 2^c X + 1` and `X + 1 = 2^d w₂`.
    have : 2 ^ c * X + 1 + 2 ^ c = 2 ^ c * (X + 1) + 1 := by ring
    rw [he₁, this, hw₂, ← mul_assoc, ← pow_add]
  · have : 2 ^ e * Z + 1 + 2 ^ e = 2 ^ e * (Z + 1) + 1 := by ring
    rw [he₂, this, hw₃, ← mul_assoc, ← pow_add]

/-- **Gap ⟹ exclusion (the rung-3 analogue of `core_of_gap`).**  If no integer cascade triple
`(w₁,w₂,w₃)` can satisfy the criterion inequality, the segment is not acyclic. -/
theorem threeBlock_of_gap {b c d e f g n X Z y : ℕ}
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * Z + 2 ^ d = 3 ^ d * (X + 1))
    (hIII : 2 ^ (f + g) * y + 2 ^ f = 3 ^ f * (Z + 1))
    (hgap : ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
        3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
        3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
        (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f) : ℤ)
          < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁) :
    y ≤ n := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₁, w₂, w₃, h3, hw, hc₁, hc₂, -⟩ := threeBlock_cascade hI hII hIII
  exact absurd ((threeBlock_criterion hI hII hIII hw).1 hcon)
    (not_le.2 (hgap w₁ w₂ w₃ h3 hc₁ hc₂))

/-! ## From the parity word to the three segment identities -/

/-- **Segment identity from a head-block word.**  The identity-level content of
`headBlock_endpoint_le`, kept separately because the three-block proof needs it at interior
positions of the itinerary. -/
theorem segment_identity_of_word {N q t : ℕ}
    (h : traceWord N (q + t) = List.replicate q true ++ List.replicate t false) :
    2 ^ (q + t) * tstep^[q + t] N + 2 ^ q = 3 ^ q * (N + 1) := by
  have hid := tstep_iterate_identity (q + t) N
  rw [h] at hid
  have hones : ones (List.replicate q true ++ List.replicate t false) = q := by
    rw [ones_append]; simp
  have hnum : numer (List.replicate q true ++ List.replicate t false) = 3 ^ q - 2 ^ q := by
    have := numer_singleBlock 0 q t; simpa using this
  rw [hones, hnum] at hid
  have h2q : (2 : ℕ) ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by norm_num) q
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **The three segment identities of a three-odd-block word.**  Splitting the itinerary at the
two block joints `b+c` and `b+c+d+e` turns the single `traceWord` hypothesis into the three
head-block identities that the whole rung-3 machinery consumes. -/
theorem threeBlock_segment_identities {b c d e f g n : ℕ}
    (hword : traceWord n (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false) :
    2 ^ (b + c) * tstep^[b + c] n + 2 ^ b = 3 ^ b * (n + 1) ∧
      2 ^ (d + e) * tstep^[b + c + d + e] n + 2 ^ d = 3 ^ d * (tstep^[b + c] n + 1) ∧
      2 ^ (f + g) * tstep^[b + c + d + e + f + g] n + 2 ^ f
        = 3 ^ f * (tstep^[b + c + d + e] n + 1) := by
  -- Split off the first block.
  have hadd1 : traceWord n (b + c + d + e + f + g)
      = traceWord n (b + c) ++ traceWord (tstep^[b + c] n) (d + e + f + g) := by
    have h := traceWord_add n (b + c) (d + e + f + g)
    rwa [show b + c + (d + e + f + g) = b + c + d + e + f + g by ring] at h
  have hW1 : traceWord n (b + c) ++ traceWord (tstep^[b + c] n) (d + e + f + g)
      = (List.replicate b true ++ List.replicate c false)
        ++ (List.replicate d true ++ List.replicate e false ++ List.replicate f true
            ++ List.replicate g false) := by
    rw [← hadd1, hword]; simp only [List.append_assoc]
  have hlen1 : (traceWord n (b + c)).length
      = (List.replicate b true ++ List.replicate c false).length := by simp
  obtain ⟨hseg1, hrest1⟩ := List.append_inj hW1 hlen1
  -- Split off the second block.
  have hXZ : tstep^[d + e] (tstep^[b + c] n) = tstep^[b + c + d + e] n := by
    rw [← Function.iterate_add_apply]; congr 1; ring
  have hadd2 : traceWord (tstep^[b + c] n) (d + e + f + g)
      = traceWord (tstep^[b + c] n) (d + e) ++ traceWord (tstep^[b + c + d + e] n) (f + g) := by
    have h := traceWord_add (tstep^[b + c] n) (d + e) (f + g)
    rwa [show d + e + (f + g) = d + e + f + g by ring, hXZ] at h
  have hW2 : traceWord (tstep^[b + c] n) (d + e)
        ++ traceWord (tstep^[b + c + d + e] n) (f + g)
      = (List.replicate d true ++ List.replicate e false)
        ++ (List.replicate f true ++ List.replicate g false) := by
    rw [← hadd2, hrest1]; simp only [List.append_assoc]
  have hlen2 : (traceWord (tstep^[b + c] n) (d + e)).length
      = (List.replicate d true ++ List.replicate e false).length := by simp
  obtain ⟨hseg2, hseg3⟩ := List.append_inj hW2 hlen2
  -- The endpoint of the whole word is the endpoint of the third segment.
  have hend : tstep^[f + g] (tstep^[b + c + d + e] n) = tstep^[b + c + d + e + f + g] n := by
    rw [← Function.iterate_add_apply]; congr 1; ring
  refine ⟨segment_identity_of_word hseg1, ?_, ?_⟩
  · have := segment_identity_of_word hseg2; rwa [hXZ] at this
  · have := segment_identity_of_word hseg3; rwa [hend] at this

/-! ## Rung 3 -/

/-- **The block-merge reduction, word form.**  An acyclic paradoxical three-odd-block segment
must defeat both two-block splittings of its word.  Sorry-free: rungs 1 and 2 of the ladder are
reused as black boxes on the sub-segments. -/
theorem threeBlock_criticality_of_acyclicParadoxical {b c d e f g n : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hword : traceWord n (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false)
    (hap : AcyclicParadoxical n (b + c + d + e + f + g)) :
    (¬ 3 ^ (b + d) < 2 ^ (b + c + d + e) ∨ ¬ 3 ^ f < 2 ^ (f + g)) ∧
      (¬ 3 ^ b < 2 ^ (b + c) ∨ ¬ 3 ^ (d + f) < 2 ^ (d + e + f + g)) := by
  obtain ⟨hI, hII, hIII⟩ := threeBlock_segment_identities hword
  exact threeBlock_merge_reduction hb hd hf hI hII hIII hap.2.2.2

/-! ### Chipping the census: eliminate the interior scale, then split off the real relaxation -/

/-- **Eliminating the interior scale `w₂` from the cascade.**  The two cascade equations
collapse to one exact relation between the outer scales:

    3^(b+d) · w₁ + T  =  2^(c+d+e+f) · w₃,    T = 2^(c+d+e) − 2^(c+d) + 3^d(2^c − 1).

So `w₁` is *determined* by `w₃`, and `w₃ ≥ 1` alone gives `3^(b+d) w₁ ≥ U := 2^(c+d+e+f) − T`. -/
theorem threeBlock_cascade_elim {b c d e f w₁ w₂ w₃ : ℕ}
    (h₁ : 3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1)
    (h₂ : 3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1) :
    (3 : ℤ) ^ (b + d) * w₁ + (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
      = 2 ^ (c + d + e + f) * w₃ := by
  have e₁ : (3 : ℤ) ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 := by exact_mod_cast h₁
  have e₂ : (3 : ℤ) ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 := by exact_mod_cast h₂
  linear_combination (3 : ℤ) ^ d * e₁ + (2 : ℤ) ^ (c + d) * e₂

/-- **Leaf schema.**  Any lower bound `B ≤ 3^(b+d)·w₁` discharges the rung-3 gap once
`3^(b+d)·RHS < D·B`.  The three positivity leaves below instantiate it at the three levels of
the cascade (`w₃ ≥ 1`, `w₂ ≥ 1`, `w₁ ≥ 1`); together they already cut the census to 58 tuples at
`m ∈ {5,8,16,27}` (host scan, exhaustive `m ≤ 55`) with **no** fractional ceiling used. -/
theorem threeBlock_gap_of_scaled_lower {b c d e f g w₁ : ℕ} {B : ℤ}
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hlb : B ≤ (3 : ℤ) ^ (b + d) * w₁)
    (hB : (3 : ℤ) ^ (b + d) * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f))
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * B) :
    (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
        - 2 ^ (c + d + e + f) : ℤ)
      < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ := by
  have hDpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f) := by
    have : (3 : ℤ) ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by exact_mod_cast hsub
    linarith
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ (b + d) := by positivity
  refine lt_of_mul_lt_mul_left ?_ h3pos.le
  calc (3 : ℤ) ^ (b + d) * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f))
      < (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * B := hB
    _ ≤ (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * ((3 : ℤ) ^ (b + d) * w₁) :=
        mul_le_mul_of_nonneg_left hlb hDpos.le
    _ = 3 ^ (b + d) * ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁) := by ring

/-- `w₂ ≥ 1` follows from `w₃ ≥ 1` and the second cascade equation (`f ≥ 1`); `w₁ ≥ 1` then
follows from the first (`d ≥ 1`). -/
theorem threeBlock_cascade_pos {b c d e f w₁ w₂ w₃ : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f)
    (h3 : 1 ≤ w₃)
    (h₁ : 3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1)
    (h₂ : 3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1) :
    1 ≤ w₂ ∧ 1 ≤ w₁ := by
  have hef : 2 ^ e < 2 ^ (e + f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw₂ : 1 ≤ w₂ := by
    rcases Nat.eq_zero_or_pos w₂ with h | h
    · subst h
      have : 2 ^ (e + f) ≤ 2 ^ (e + f) * w₃ := Nat.le_mul_of_pos_right _ h3
      simp only [Nat.mul_zero, Nat.zero_add] at h₂
      omega
    · exact h
  refine ⟨hw₂, ?_⟩
  have hcd : 2 ^ c < 2 ^ (c + d) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos w₁ with h | h
  · subst h
    have : 2 ^ (c + d) ≤ 2 ^ (c + d) * w₂ := Nat.le_mul_of_pos_right _ hw₂
    simp only [Nat.mul_zero, Nat.zero_add] at h₁
    omega
  · exact h

/-- **Positivity leaf at the head scale (`w₁ ≥ 1`) — PROVED.**  If `D > RHS` the gap is
immediate. -/
theorem threeBlock_gap_of_w1 {b c d e f g : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hW : (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) :
    ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
      (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ := by
  intro w₁ w₂ w₃ h3 h₁ h₂
  obtain ⟨-, hw₁⟩ := threeBlock_cascade_pos hd hf h3 h₁ h₂
  have hw₁z : (1 : ℤ) ≤ (w₁ : ℤ) := by exact_mod_cast hw₁
  refine threeBlock_gap_of_scaled_lower (B := (3 : ℤ) ^ (b + d)) hsub ?_ ?_
  · nlinarith [hw₁z, (by positivity : (0 : ℤ) < (3 : ℤ) ^ (b + d))]
  · have hDpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f) := by
      have : (3 : ℤ) ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by exact_mod_cast hsub
      linarith
    have h3pos : (0 : ℤ) < (3 : ℤ) ^ (b + d) := by positivity
    calc (3 : ℤ) ^ (b + d) * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f))
        < 3 ^ (b + d) * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) :=
          mul_lt_mul_of_pos_left hW h3pos
      _ = (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 3 ^ (b + d) := by ring

/-- **Positivity leaf at the interior scale (`w₂ ≥ 1`) — PROVED.**  With
`V = 2^(c+d) − 2^c + 1` (the value of `3^b w₁` at `w₂ = 1`), the gap holds once
`3^b · RHS < D · V`.  This is the leaf that carries the regime `3^d > 2^(e+f)`, where the
head-scale bound from `w₃ ≥ 1` degenerates. -/
theorem threeBlock_gap_of_w2 {b c d e f g : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hV : (3 : ℤ) ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f))
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
            * (2 ^ (c + d) - 2 ^ c + 1)) :
    ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
      (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ := by
  intro w₁ w₂ w₃ h3 h₁ h₂
  obtain ⟨hw₂, -⟩ := threeBlock_cascade_pos hd hf h3 h₁ h₂
  have hw₂z : (1 : ℤ) ≤ (w₂ : ℤ) := by exact_mod_cast hw₂
  have e₁ : (3 : ℤ) ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 := by exact_mod_cast h₁
  refine threeBlock_gap_of_scaled_lower (B := (3 : ℤ) ^ d * (2 ^ (c + d) - 2 ^ c + 1)) hsub ?_ ?_
  · have hcd : (0 : ℤ) < 2 ^ (c + d) := by positivity
    have h3d : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
    have hb : (3 : ℤ) ^ (b + d) = 3 ^ d * 3 ^ b := by rw [← pow_add]; ring_nf
    rw [hb, mul_assoc]
    have : (2 : ℤ) ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w₁ := by nlinarith [e₁, hw₂z, hcd]
    exact mul_le_mul_of_nonneg_left this h3d.le
  · have h3d : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
    have hb : (3 : ℤ) ^ (b + d) = 3 ^ d * 3 ^ b := by rw [← pow_add]; ring_nf
    rw [hb]
    have := mul_lt_mul_of_pos_left hV h3d
    calc (3 : ℤ) ^ d * 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f))
        = 3 ^ d * (3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f))) := by ring
      _ < 3 ^ d * ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
            * (2 ^ (c + d) - 2 ^ c + 1)) := this
      _ = (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
            * (3 ^ d * (2 ^ (c + d) - 2 ^ c + 1)) := by ring

/-- **The real-relaxation leaf of the census — PROVED.**  `w₃ ≥ 1` alone closes the rung-3 gap
for every tuple satisfying the division-free inequality

    (R3)   3^(b+d) · (3^f − 1)  <  2^(b+g) · U,    U = 2^(c+d+e+f) − T.

Nothing but `w₃ ≥ 1` and `3^k < 2^m` is used, so this is the *entire* elementary content of the
census: what survives it is exactly the set of tuples where the two integer ceilings (`w₂ ∈ ℕ`
and `w₁ ∈ ℕ`) have to do the work.  Host census: (R3) alone leaves an infinite set (18 tuples at
`m = 8`, 258 at `m = 16`, 2489 at `m = 27`, 18324 at `m = 46`), which is precisely why the
residual node below is stated in terms of the ceilings. -/
theorem threeBlock_gap_of_real {b c d e f g : ℕ}
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hR3 : (3 : ℤ) ^ (b + d) * (3 ^ f - 1)
      < 2 ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))) :
    ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
      (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ := by
  intro w₁ w₂ w₃ h3 h₁ h₂
  set T : ℤ := 2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1) with hT
  set U : ℤ := 2 ^ (c + d + e + f) - T with hU
  have hDpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f) := by
    have : (3 : ℤ) ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by exact_mod_cast hsub
    linarith
  have h3z : (1 : ℤ) ≤ (w₃ : ℤ) := by exact_mod_cast h3
  -- `3^(b+d) w₁ = 2^(c+d+e+f) w₃ − T ≥ U`.
  have helim := threeBlock_cascade_elim h₁ h₂
  have hw₁lb : U ≤ (3 : ℤ) ^ (b + d) * w₁ := by
    have hpow : (0 : ℤ) < 2 ^ (c + d + e + f) := by positivity
    nlinarith [helim, h3z, hpow]
  -- `D·U > 3^(b+d)·RHS`, because `D·U − 3^(b+d)·RHS = 2^(c+d+e+f)·(2^(b+g)U − 3^(b+d)(3^f−1))`.
  have hsplit : (2 : ℤ) ^ (b + c + d + e + f + g)
      = 2 ^ (c + d + e + f) * 2 ^ (b + g) := by rw [← pow_add]; ring_nf
  have hkey : (3 : ℤ) ^ (b + d) * (3 ^ f * T - 2 ^ (c + d + e + f))
      < (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * U := by
    have hpow : (0 : ℤ) < 2 ^ (c + d + e + f) := by positivity
    have hexp : (3 : ℤ) ^ (b + d + f) = 3 ^ (b + d) * 3 ^ f := by rw [← pow_add]
    have hmul : (2 : ℤ) ^ (c + d + e + f) * ((3 : ℤ) ^ (b + d) * (3 ^ f - 1))
        < 2 ^ (c + d + e + f) * (2 ^ (b + g) * U) :=
      mul_lt_mul_of_pos_left hR3 hpow
    rw [hsplit, hexp, hU]
    nlinarith [hmul]
  -- Multiply the `w₁` lower bound by `D > 0` and divide by `3^(b+d) > 0`.
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ (b + d) := by positivity
  have hchain : (3 : ℤ) ^ (b + d) * (3 ^ f * T - 2 ^ (c + d + e + f))
      < 3 ^ (b + d) * ((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁) := by
    have := mul_le_mul_of_nonneg_left hw₁lb hDpos.le
    nlinarith [hkey, this]
  exact lt_of_mul_lt_mul_left hchain h3pos.le

/-! ### Rung-3 census (host instrument, exact integers)

Combining `threeBlock_criterion` with
the integer cascade of `threeBlock_cascade` — minimising `w₁` over integer triples with
`w₃ ≥ 1` — leaves exactly **27** three-block tuples, at lengths `m ∈ {5, 8, 16, 27}`,
exhaustively for all `m ≤ 130` and all `k` with `3^k / 2^m > 1/8`
(`experiments/block_ladder_probe.py`, `scratchpad` scan of 2026-09-02):

```
m =  5, k =  3 :  1 tuple    (1,1,1,1,1,0)
m =  8, k =  5 : 17 tuples   (contains the four realized solutions)
m = 16, k = 10 :  5 tuples   (4,5,3,1,3,0) (4,2,4,4,2,0) (5,4,2,2,3,0) (5,5,2,1,3,0) (5,5,3,1,2,0)
m = 27, k = 17 :  4 tuples   (6,1,8,9,3,0) (7,5,6,5,4,0) (8,8,4,1,5,1) (8,9,4,1,5,0)
```

Dropping the integrality of the *interior* scale `w₂` — i.e. keeping only what `w₃ ≥ 1` gives,
the division-free `2^(b+g)·U ≤ 3^(b+d)(3^f − 1)` — makes the same set **infinite**: 18 tuples at
`m = 8`, 317 at `m = 16`, 2931 at `m = 27`, 88718 in total for `m ≤ 40`, growing steadily.
So the finiteness of rung 3 is carried by a
**two-level integer ceiling**, not by a linear form in logarithms; contrast rung 2, whose
crux `b + d ≤ 5` provably needs the Baker-grade `sep_two_three`.

**Narrowed (2026-09-02, same lap).**  The three *positivity* leaves — `threeBlock_gap_of_real`
(`w₃ ≥ 1`), `threeBlock_gap_of_w2` (`w₂ ≥ 1`) and `threeBlock_gap_of_w1` (`w₁ ≥ 1`), all proved
sorry-free — discharge every tuple that satisfies any one of their three division-free
inequalities.  A host scan exhaustive for `m ≤ 55` shows what is left: **58 tuples**, at
`m ∈ {5, 8, 16, 27}` only, with *no fractional ceiling used anywhere*.  So the finiteness of
rung 3 is carried by the **maximum of three cascade-level positivity bounds**, not by the
rounding — a sharper statement than the ceiling census, and an entirely elementary one.

`threeBlock_ceiling_gap` is the residual: the census restricted to tuples that fail all three
leaves.  Chipping it is the rung-3 crux; see `PENDING_WORK.md`. -/
/-! ### The residual, reduced to the exponents alone

The three positivity leaves are *division-free*: their hypotheses mention only `b,c,d,e,f,g`.
So the residual census is a statement about the **exponent tuple alone** — the cascade scales
`w₁, w₂, w₃` have been eliminated entirely.  `threeBlock_leaves_infeasible` says exactly that,
and `threeBlock_ceiling_gap` is then a one-line consequence.  The three `threeBlock_relax_*`
lemmas below strip the tuple down further, replacing `T` by the two-term envelope
`2^c·(2^(d+e) + 3^d)`; in the relaxed variables the system reads (with `R = 3^k/2^m`,
`X = (3/2)^d/2^e`, `Y = (3/2)^f`)

    (A*)  (1−R)·2^f        <  1 + X
    (W*)  (1−R)·2^(b+g)+1  <  Y·(1 + X)
    (V*)  (1−R)·2^d        ≤  2·Y·(3/2)^b·(1 + X)/2^e · 2^e

i.e. every one of them is an upper bound on `1 − R` — which is why the surviving lengths are
exactly the continued-fraction convergents `m/k ∈ {5/3, 8/5, 13/8, 16/10, 27/17}` of `log₂3`.
**Finding (the effectivity question `DIRECTION.md` asks):** the residual regime is the
near-critical one, `3^k < 2^m < 2·3^k`, so rung 3's *residual* does consume a two-log
separation after all — `sep_two_three` is the intended input, exactly as in rung 2's
`bd_reduction`.  What the ceiling census showed is only that the *bulk* of rung 3 (all but 58
tuples) is elementary. -/

/-- **Relaxation (A\*) of the failed real-relaxation leaf.**  `hR3` (the negation of
`threeBlock_gap_of_real`'s hypothesis) implies `D·2^(c+d+e+f) < 2^m·T`, and `T` is below the
envelope `2^c·(2^(d+e) + 3^d)`; cancelling `2^c` gives a relation free of `c`. -/
theorem threeBlock_relax_A {b c d e f g : ℕ}
    (hR3 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
        ≤ 3 ^ (b + d) * (3 ^ f - 1)) :
    ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (d + e + f)
      < 2 ^ (b + c + d + e + f + g) * (2 ^ (d + e) + 3 ^ d) := by
  have hMpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) := by positivity
  have hcpos : (0 : ℤ) < (2 : ℤ) ^ c := by positivity
  set T : ℤ := 2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1) with hT
  have hsplitc : (2 : ℤ) ^ (c + d + e + f) = 2 ^ c * 2 ^ (d + e + f) := by
    rw [← pow_add]; congr 1; omega
  have hTlt : T < 2 ^ c * (2 ^ (d + e) + 3 ^ d) := by
    have h1 : (2 : ℤ) ^ (c + d + e) = 2 ^ c * 2 ^ (d + e) := by rw [← pow_add]; congr 1; omega
    have h4 : (2 : ℤ) ^ (c + d) = 2 ^ c * 2 ^ d := by rw [← pow_add]
    have h2 : (0 : ℤ) < (2 : ℤ) ^ c * 2 ^ d := by positivity
    have h3 : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
    rw [hT, h1, h4]; ring_nf; nlinarith [h2, h3]
  have key : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (c + d + e + f)
      < 2 ^ (b + c + d + e + f + g) * T := by
    have hm : (2 : ℤ) ^ (b + c + d + e + f + g) = 2 ^ (b + g) * 2 ^ (c + d + e + f) := by
      rw [← pow_add]; congr 1; omega
    have hk : (3 : ℤ) ^ (b + d + f) = 3 ^ (b + d) * 3 ^ f := by rw [← pow_add]
    have hbd : (0 : ℤ) < (3 : ℤ) ^ (b + d) := by positivity
    have h1 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f) - T) < 3 ^ (b + d + f) := by
      rw [hk]; nlinarith [hR3, hbd]
    have h2 := mul_lt_mul_of_pos_right h1 (show (0:ℤ) < 2 ^ (c + d + e + f) by positivity)
    rw [hm]; nlinarith [h2]
  refine lt_of_mul_lt_mul_left ?_ hcpos.le
  calc (2 : ℤ) ^ c * (((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (d + e + f))
      = ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (c + d + e + f) := by
        rw [hsplitc]; ring
    _ < 2 ^ (b + c + d + e + f + g) * T := key
    _ < 2 ^ (b + c + d + e + f + g) * (2 ^ c * (2 ^ (d + e) + 3 ^ d)) :=
        mul_lt_mul_of_pos_left hTlt hMpos
    _ = 2 ^ c * (2 ^ (b + c + d + e + f + g) * (2 ^ (d + e) + 3 ^ d)) := by ring

/-- **Relaxation (W\*) of the failed head-scale leaf.** -/
theorem threeBlock_relax_W {b c d e f g : ℕ}
    (hW : (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
        ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)) :
    ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) + 2 ^ (c + d + e + f)
      < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d) := by
  have hTlt : (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1) : ℤ)
      < 2 ^ c * (2 ^ (d + e) + 3 ^ d) := by
    have h1 : (2 : ℤ) ^ (c + d + e) = 2 ^ c * 2 ^ (d + e) := by rw [← pow_add]; congr 1; omega
    have h4 : (2 : ℤ) ^ (c + d) = 2 ^ c * 2 ^ d := by rw [← pow_add]
    have h2 : (0 : ℤ) < (2 : ℤ) ^ c * 2 ^ d := by positivity
    have h3 : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
    rw [h1, h4]; ring_nf; nlinarith [h2, h3]
  have hfpos : (0 : ℤ) < (3 : ℤ) ^ f := by positivity
  nlinarith [hW, mul_lt_mul_of_pos_left hTlt hfpos]

/-- **Relaxation (V\*) of the failed interior-scale leaf.**  Uses `1 ≤ d` through
`2·(2^(c+d) − 2^c + 1) ≥ 2^(c+d)`. -/
theorem threeBlock_relax_V {b c d e f g : ℕ} (hd : 1 ≤ d)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
          * (2 ^ (c + d) - 2 ^ c + 1)
        ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f))) :
    ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ d
      ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d) := by
  have hcpos : (0 : ℤ) < (2 : ℤ) ^ c := by positivity
  have hDpos : (0 : ℤ) < 2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f) := by
    have : (3 : ℤ) ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by exact_mod_cast hsub
    linarith
  have hTlt : (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1) : ℤ)
      < 2 ^ c * (2 ^ (d + e) + 3 ^ d) := by
    have h1 : (2 : ℤ) ^ (c + d + e) = 2 ^ c * 2 ^ (d + e) := by rw [← pow_add]; congr 1; omega
    have h4 : (2 : ℤ) ^ (c + d) = 2 ^ c * 2 ^ d := by rw [← pow_add]
    have h2 : (0 : ℤ) < (2 : ℤ) ^ c * 2 ^ d := by positivity
    have h3 : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
    rw [h1, h4]; ring_nf; nlinarith [h2, h3]
  -- `2·(2^(c+d) − 2^c + 1) ≥ 2^(c+d)` because `2^(c+d) ≥ 2^(c+1)`.
  have hVlow : (2 : ℤ) ^ (c + d) ≤ 2 * (2 ^ (c + d) - 2 ^ c + 1) := by
    have h1 : (2 : ℤ) ^ (c + 1) ≤ 2 ^ (c + d) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    have h2 : (2 : ℤ) ^ (c + 1) = 2 * 2 ^ c := by rw [pow_succ]; ring
    linarith
  have hbfpos : (0 : ℤ) < (3 : ℤ) ^ b * 3 ^ f := by positivity
  have hstep : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (c + d)
      ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ c * (2 ^ (d + e) + 3 ^ d)) := by
    have h1 := mul_le_mul_of_nonneg_left hVlow hDpos.le
    have h2 : (0 : ℤ) < (3 : ℤ) ^ f := by positivity
    have h3 : (0 : ℤ) < (2 : ℤ) ^ (c + d + e + f) := by positivity
    nlinarith [hV, mul_lt_mul_of_pos_left hTlt (show (0:ℤ) < (3:ℤ)^b * 3^f by positivity), h1, h2, h3]
  have hsplit : (2 : ℤ) ^ (c + d) = 2 ^ c * 2 ^ d := by rw [← pow_add]
  refine le_of_mul_le_mul_left ?_ hcpos
  calc (2 : ℤ) ^ c * (((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ d)
      = ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (c + d) := by
        rw [hsplit]; ring
    _ ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ c * (2 ^ (d + e) + 3 ^ d)) := hstep
    _ = 2 ^ c * (2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d)) := by ring

/-! ### The non-window branch `2·3^k ≤ 2^m` — elementary and bounded

If the tuple is *not* near-critical then `D = 2^m − 3^k ≥ 2^(m−1)`, and the three relaxed
inequalities lose their `2^m` scale entirely: what is left is a system in `b, d, e, f, g` with
absolute constants, which forces `f ≤ 2`, `b + g ≤ 5`, and finally `m ≤ 25`.  So the whole
residual census lives in the near-critical window `3^k < 2^m < 2·3^k` — the regime where the
Rhin-lite polynomial measure `rhinLite_log23_measure` applies.  (That is the effectivity finding
recorded above, now with a proof route rather than a scan.)

The three `_S*` lemmas are stated over abstract positive `D, M, Pb, Bg` so that the `2^m`
bookkeeping happens once, at the point of use. -/

/-- Scale-free form of relaxation (A\*) when `2^m ≤ 2D`. -/
theorem threeBlock_nonwindow_S2 {d e f : ℕ} {D M : ℤ} (hD : 0 < D) (hMpos : 0 < M)
    (hM : M ≤ 2 * D) (hA : D * 2 ^ (d + e + f) < M * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ (d + e + f) < 2 * (2 ^ (d + e) + 3 ^ d) := by
  have hp : (0 : ℤ) < 2 ^ (d + e + f) := by positivity
  refine lt_of_mul_lt_mul_left ?_ hMpos.le
  nlinarith [hA, hM, hp]

/-- Scale-free form of relaxation (V\*) when `3^k ≤ D` (`Pb = 3^(b+f)`). -/
theorem threeBlock_nonwindow_S1 {d e : ℕ} {D Pb : ℤ} (hD : 0 < D)
    (hPb : Pb * 3 ^ d ≤ D) (hV : D * 2 ^ d ≤ 2 * Pb * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ d * 3 ^ d ≤ 2 * (2 ^ (d + e) + 3 ^ d) := by
  have h3 : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
  have hsum : (0 : ℤ) < (2 : ℤ) ^ (d + e) + 3 ^ d := by positivity
  refine le_of_mul_le_mul_left ?_ hD
  nlinarith [hV, hPb, h3, hsum]

/-- Scale-free form of relaxation (W\*) when `2^m ≤ 2D`, `2^m = 2^(b+g)·2^(c+d+e+f)`. -/
theorem threeBlock_nonwindow_S3 {c d e f : ℕ} {D Bg : ℤ} (hBg : 0 < Bg)
    (hm : Bg * 2 ^ (c + d + e + f) ≤ 2 * D)
    (hW : D + 2 ^ (c + d + e + f) < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ (d + e + f) * (Bg + 2) < 2 * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) := by
  have hsplit : (2 : ℤ) ^ (c + d + e + f) = 2 ^ c * 2 ^ (d + e + f) := by
    rw [← pow_add]; congr 1; omega
  have hcpos : (0 : ℤ) < (2 : ℤ) ^ c := by positivity
  refine lt_of_mul_lt_mul_left ?_ hcpos.le
  rw [hsplit] at hm hW
  nlinarith [hm, hW]

/-- `F1`: the interior scale is pinned — `3^d ≤ 2^(e+2)`. -/
theorem threeBlock_nonwindow_F1 {d e : ℕ} (hd : 1 ≤ d)
    (h : 2 ^ d * 3 ^ d ≤ 2 * (2 ^ (d + e) + 3 ^ d)) : 3 ^ d ≤ 2 ^ (e + 2) := by
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · interval_cases d
    · calc (3 : ℕ) ^ 1 = 3 := by norm_num
        _ ≤ 2 ^ (e + 2) := by
            calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hde : (2 : ℕ) ^ (d + e) = 2 ^ d * 2 ^ e := pow_add 2 d e
    have he2 : (2 : ℕ) ^ (e + 2) = 4 * 2 ^ e := by rw [pow_add]; ring
    have h4 : (4 : ℕ) ≤ 2 ^ d := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd2
    have h2 : 4 * 3 ^ d ≤ 2 ^ d * 3 ^ d := Nat.mul_le_mul_right _ h4
    rw [hde] at h
    have hkey : 2 ^ d * 3 ^ d ≤ 2 ^ d * (4 * 2 ^ e) := by linarith
    have hdpos : 0 < (2 : ℕ) ^ d := by positivity
    rw [he2]
    exact Nat.le_of_mul_le_mul_left hkey hdpos

/-- `F2`: the third block is short — `f ≤ 2`. -/
theorem threeBlock_nonwindow_F2 {d e f : ℕ} (hd : 1 ≤ d)
    (h3d : 3 ^ d ≤ 2 ^ (e + 2))
    (h : 2 ^ (d + e + f) < 2 * (2 ^ (d + e) + 3 ^ d)) : f ≤ 2 := by
  have e1 : (2 : ℕ) ^ (d + e + 1) = 2 * 2 ^ (d + e) := by rw [pow_succ]; ring
  have e2 : (2 : ℕ) ^ (e + 3) = 2 * 2 ^ (e + 2) := by rw [pow_succ]; ring
  have e3 : (2 : ℕ) ^ (e + 3) ≤ 2 ^ (d + e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e4 : (2 : ℕ) ^ (d + e + 2) = 2 * 2 ^ (d + e + 1) := by rw [pow_succ]; ring
  have e5 : (2 : ℕ) ^ (d + e + 3) = 2 * 2 ^ (d + e + 2) := by rw [pow_succ]; ring
  have hlt : (2 : ℕ) ^ (d + e + f) < 2 ^ (d + e + 3) := by
    have : 2 * (2 ^ (d + e) + 3 ^ d) ≤ 2 ^ (d + e + 1) + 2 ^ (e + 3) := by
      rw [e1, e2]; omega
    omega
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
  omega

/-- `F3`: the head block and the tail are short — `b + g ≤ 4`. -/
theorem threeBlock_nonwindow_F3 {b d e f g : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f) (hf2 : f ≤ 2)
    (h3d : 3 ^ d ≤ 2 ^ (e + 2))
    (h : 2 ^ (d + e + f) * (2 ^ (b + g) + 2) < 2 * (3 ^ f * (2 ^ (d + e) + 3 ^ d))) :
    b + g ≤ 4 := by
  have h3f : (3 : ℕ) ^ f ≤ 9 := by
    calc (3 : ℕ) ^ f ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hf2
      _ = 9 := by norm_num
  have he2 : (2 : ℕ) ^ (e + 2) ≤ 2 ^ (d + e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℕ) ^ (d + e + 1) = 2 * 2 ^ (d + e) := by rw [pow_succ]; ring
  have hR : 2 * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) ≤ 54 * 2 ^ (d + e) := by
    have h1 : (2 : ℕ) ^ (d + e) + 3 ^ d ≤ 3 * 2 ^ (d + e) := by omega
    calc 2 * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) ≤ 2 * (9 * (3 * 2 ^ (d + e))) := by
          have := Nat.mul_le_mul h3f h1
          omega
      _ = 54 * 2 ^ (d + e) := by ring
  have hL : 2 * 2 ^ (b + g) * 2 ^ (d + e) ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2) := by
    have hfge : (2 : ℕ) ^ (d + e + 1) ≤ 2 ^ (d + e + f) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * 2 ^ (b + g) * 2 ^ (d + e) = 2 ^ (d + e + 1) * 2 ^ (b + g) := by rw [e1]; ring
      _ ≤ 2 ^ (d + e + f) * 2 ^ (b + g) := Nat.mul_le_mul_right _ hfge
      _ ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2) := Nat.mul_le_mul_left _ (by omega)
  have hde : 0 < (2 : ℕ) ^ (d + e) := by positivity
  have hkey : 2 * 2 ^ (b + g) < 54 := by
    have : 2 * 2 ^ (b + g) * 2 ^ (d + e) < 54 * 2 ^ (d + e) := by omega
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hbg : (2 : ℕ) ^ (b + g) < 27 := by omega
  by_contra hcon
  have : (2 : ℕ) ^ 5 ≤ 2 ^ (b + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at this
  omega

/-- `2^(d+e) ≤ 2·3^d` with `d ≤ 13` forces `e ≤ 8` (worst case `d = 13`: `(3/2)^13 < 256`). -/
theorem threeBlock_nonwindow_e_bound {d e : ℕ} (hd13 : d ≤ 13) (h : 2 ^ (d + e) ≤ 2 * 3 ^ d) :
    e ≤ 8 := by
  by_contra hcon
  have h9 : (2 : ℕ) ^ (d + 9) ≤ 2 * 3 ^ d :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h
  rw [pow_add] at h9
  interval_cases d <;> norm_num at h9

set_option maxHeartbeats 1200000 in
/-- **The non-window branch — PROVED.**  If the tuple is not near-critical (`2·3^k ≤ 2^m`) then
its length is at most `22`, hence inside the finite range `m ≤ 27` where the census is decided by
explicit check.  So every residual tuple of length `> 27` satisfies `3^k < 2^m < 2·3^k`. -/
theorem threeBlock_nonwindow (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hbig : 2 * 3 ^ (b + d + f) ≤ 2 ^ (b + c + d + e + f + g))
    (hA : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (d + e + f)
        < 2 ^ (b + c + d + e + f + g) * (2 ^ (d + e) + 3 ^ d))
    (hW : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) + 2 ^ (c + d + e + f)
        < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ d
        ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d)) :
    b + c + d + e + f + g ≤ 22 := by
  set m := b + c + d + e + f + g with hm
  set k := b + d + f with hk
  have hPM : (3 : ℤ) ^ k < 2 ^ m := by exact_mod_cast hsub
  have hbigZ : 2 * (3 : ℤ) ^ k ≤ 2 ^ m := by exact_mod_cast hbig
  have hMpos : (0 : ℤ) < 2 ^ m := by positivity
  have hD : (0 : ℤ) < 2 ^ m - 3 ^ k := by linarith
  have hM2 : (2 : ℤ) ^ m ≤ 2 * (2 ^ m - 3 ^ k) := by linarith
  have hPD : (3 : ℤ) ^ k ≤ 2 ^ m - 3 ^ k := by linarith
  -- the three scale-free inequalities
  have hS2 := threeBlock_nonwindow_S2 hD hMpos hM2 hA
  have hPb : (3 : ℤ) ^ b * 3 ^ f * 3 ^ d = 3 ^ k := by
    rw [hk, ← pow_add, ← pow_add]; congr 1; omega
  have hS1 := threeBlock_nonwindow_S1 hD (by rw [hPb]; exact hPD) hV
  have hBg : (2 : ℤ) ^ (b + g) * 2 ^ (c + d + e + f) = 2 ^ m := by
    rw [hm, ← pow_add]; congr 1; omega
  have hS3 := threeBlock_nonwindow_S3 (show (0:ℤ) < 2 ^ (b + g) by positivity)
    (by rw [hBg]; exact hM2) hW
  -- transport to ℕ
  have n1 : 2 ^ d * 3 ^ d ≤ 2 * (2 ^ (d + e) + 3 ^ d) := by exact_mod_cast hS1
  have n2 : 2 ^ (d + e + f) < 2 * (2 ^ (d + e) + 3 ^ d) := by exact_mod_cast hS2
  have n3 : 2 ^ (d + e + f) * (2 ^ (b + g) + 2) < 2 * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) := by
    exact_mod_cast hS3
  have h3d : 3 ^ d ≤ 2 ^ (e + 2) := threeBlock_nonwindow_F1 hd n1
  have hf2 : f ≤ 2 := threeBlock_nonwindow_F2 hd h3d n2
  have hbg4 : b + g ≤ 4 := threeBlock_nonwindow_F3 hd hf hf2 h3d n3
  -- `3^d ≤ 2·2^(d+e)` and `3^(b+f) ≤ 729`
  have h3dZ : (3 : ℤ) ^ d ≤ 2 * 2 ^ (d + e) := by
    have h1 : (2 : ℕ) ^ (e + 2) ≤ 2 * 2 ^ (d + e) := by
      have : (2 : ℕ) ^ (e + 2) ≤ 2 ^ (d + e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (2 : ℕ) ^ (d + e + 1) = 2 * 2 ^ (d + e) := by rw [pow_succ]; ring
      omega
    have : (3 : ℕ) ^ d ≤ 2 * 2 ^ (d + e) := le_trans h3d h1
    exact_mod_cast this
  have hbfZ : (3 : ℤ) ^ b * 3 ^ f ≤ 729 := by
    have : (3 : ℕ) ^ b * 3 ^ f ≤ 729 := by
      have hbf : b + f ≤ 6 := by omega
      calc (3 : ℕ) ^ b * 3 ^ f = 3 ^ (b + f) := by rw [pow_add]
        _ ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) hbf
        _ = 729 := by norm_num
    exact_mod_cast this
  -- F5 : `D ≤ 4374·2^e`, hence `m ≤ e + 13`
  have hsum3 : (2 : ℤ) ^ (d + e) + 3 ^ d ≤ 3 * 2 ^ (d + e) := by linarith
  have hdpos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  have hF5 : ((2 : ℤ) ^ m - 3 ^ k) * 2 ^ d ≤ 4374 * (2 ^ d * 2 ^ e) := by
    have hsplit : (2 : ℤ) ^ (d + e) = 2 ^ d * 2 ^ e := by rw [← pow_add]
    have hpos : (0 : ℤ) < 2 * (3 ^ b * 3 ^ f) := by positivity
    calc ((2 : ℤ) ^ m - 3 ^ k) * 2 ^ d ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d) := hV
      _ ≤ 2 * (3 ^ b * 3 ^ f) * (3 * 2 ^ (d + e)) := by nlinarith [hsum3, hpos]
      _ ≤ 2 * 729 * (3 * 2 ^ (d + e)) := by nlinarith [hbfZ, (by positivity : (0:ℤ) < 2 ^ (d+e))]
      _ = 4374 * (2 ^ d * 2 ^ e) := by rw [hsplit]; ring
  have hDe : (2 : ℤ) ^ m - 3 ^ k ≤ 4374 * 2 ^ e := le_of_mul_le_mul_right (by nlinarith [hF5]) hdpos
  have hme : m ≤ e + 13 := by
    have hMe : (2 : ℤ) ^ m < 2 ^ (e + 14) := by
      have : (2 : ℤ) ^ (e + 14) = 16384 * 2 ^ e := by rw [pow_add]; ring
      rw [this]; linarith
    have : (2 : ℕ) ^ m < 2 ^ (e + 14) := by exact_mod_cast hMe
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 this
    omega
  have hd13 : d ≤ 13 := by omega
  have hk13 : k ≤ 13 := by omega
  -- F6 : bound `e`, or else `R > 1/4`
  by_cases hX : (2 : ℕ) ^ (d + e) ≤ 2 * 3 ^ d
  · have := threeBlock_nonwindow_e_bound hd13 hX
    omega
  · -- `2·3^d < 2^(d+e)`, so `2(2^(d+e)+3^d) ≤ 3·2^(d+e)`, and `(A*)` gives `2^m < 4·3^k`
    have hXZ : 2 * (3 : ℤ) ^ d < 2 ^ (d + e) := by
      have : 2 * 3 ^ d < (2 : ℕ) ^ (d + e) := by omega
      exact_mod_cast this
    have hde1 : (2 : ℤ) ^ (d + e + f) ≥ 2 * 2 ^ (d + e) := by
      have h1 : (2 : ℤ) ^ (d + e + 1) ≤ 2 ^ (d + e + f) := by
        apply pow_le_pow_right₀ (by norm_num); omega
      have h2 : (2 : ℤ) ^ (d + e + 1) = 2 * 2 ^ (d + e) := by rw [pow_succ]; ring
      linarith
    have hkey : 4 * ((2 : ℤ) ^ m - 3 ^ k) < 3 * 2 ^ m := by
      have hdepos : (0 : ℤ) < (2 : ℤ) ^ (d + e) := by positivity
      nlinarith [hA, hde1, hD, hMpos, hXZ, hdepos]
    have hlt : (2 : ℕ) ^ m < 4 * 3 ^ k := by
      have : (2 : ℤ) ^ m < 4 * 3 ^ k := by linarith
      exact_mod_cast this
    have h3k : (3 : ℕ) ^ k ≤ 3 ^ 13 := Nat.pow_le_pow_right (by norm_num) hk13
    have : (2 : ℕ) ^ m < 2 ^ 23 := by
      have : (4 : ℕ) * 3 ^ 13 < 2 ^ 23 := by norm_num
      omega
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 this
    omega

/-- **Node 1 of the rung-3 crux: the finite range.**  No exponent tuple of length `m ≤ 27` other
than the four census lengths fails all three positivity leaves.  This is a finite check
(≈2·10⁵ tuples, integers below `2^60`) — a `decide`/`native_decide` job, not mathematics. -/
theorem threeBlock_finite_infeasible (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e) (hshort : b + c + d + e + f + g ≤ 27)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ))
    (hR3 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
        ≤ 3 ^ (b + d) * (3 ^ f - 1))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
          * (2 ^ (c + d) - 2 ^ c + 1)
        ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)))
    (hW : (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
        ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)) :
    False := by
  sorry

/-- **The window node's separation input — PROVED.**  In the near-critical window with
`k < 190537`, `sep_strong_190537` gives `3^k ≤ D·2^20`, hence `2^m ≤ 2^21·D`: the deficit
`1 − 3^k/2^m` is bounded below by the *absolute constant* `2^(−21)`, not by `2^(−k/3)`.
This is the hypothesis shape the census argument consumes (`2^m ≤ 2^t·D`, here `t = 21`; the
non-window branch above is the same shape at `t = 1`). -/
theorem threeBlock_window_scale {b c d e f g : ℕ} (hk : 0 < b + d + f) (hklt : b + d + f < 190537)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hwin : 2 ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f)) :
    (2 : ℤ) ^ (b + c + d + e + f + g)
      ≤ 2 ^ 21 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) := by
  have hS := sep_strong_190537 (b + d + f) (b + c + d + e + f + g) hk hklt hsub
  have hSZ : (3 : ℤ) ^ (b + d + f)
      ≤ ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ 20 := by
    have hle : (3 : ℕ) ^ (b + d + f) ≤ 2 ^ (b + c + d + e + f + g) := le_of_lt hsub
    have : ((3 ^ (b + d + f) : ℕ) : ℤ)
        ≤ (((2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ 20 : ℕ) : ℤ) := by
      exact_mod_cast hS
    push_cast [Nat.cast_sub hle] at this
    linarith
  have hwinZ : (2 : ℤ) ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f) := by exact_mod_cast hwin
  have : (2 : ℤ) ^ 21 = 2 * 2 ^ 20 := by norm_num
  rw [this]
  linarith

/-- **Node 2 of the rung-3 crux — THE crux.**  The near-critical window `3^k < 2^m < 2·3^k` at
length `m ≥ 28`.  Route (worked out 2026-09-02, see the module notes above): the Rhin-lite
*polynomial* measure `rhinLite_log23_measure` gives `1 − R ≥ rhinLiteSepC/(2·k^436)` with
`R = 3^k/2^m`; writing `L = log₂(1/(1−R)) = O(log k)` and `X = (3/2)^d/2^e`, the three relaxed
inequalities `threeBlock_relax_A/W/V` read

    f ≤ L + log₂(1+X),   d ≤ L + 1 + log₂(1+1/X),   b + g ≤ L + f·log₂(3/2) + log₂(1+X),

and with `e ≤ m − k ≤ 0.585k + 1` these close as `k ≤ 5.09·L + 6`, i.e. `k` bounded.
⚠️ It is the *polynomial* measure that closes this, **not** `sep_two_three` (`β = 1/3`): at
`β = 1/3` the normalized system has the fixed point `b/k = d/k = f/k = 1/3`, so it is feasible.
Rung 3 therefore needs a strictly stronger separation input than rung 2 does — the effectivity
asymmetry `DIRECTION.md` asks to record. -/
theorem threeBlock_window_infeasible (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e) (hlongm : 28 ≤ b + c + d + e + f + g)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hwin : 2 ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f))
    (hR3 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
        ≤ 3 ^ (b + d) * (3 ^ f - 1))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
          * (2 ^ (c + d) - 2 ^ c + 1)
        ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)))
    (hW : (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
        ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)) :
    False := by
  sorry

/-- **THE RUNG-3 CRUX, in exponent form.**  The residual census, with the cascade scales
`w₁, w₂, w₃` eliminated: no exponent tuple of length outside `{5, 8, 16, 27}` fails all three
positivity leaves at once.  Host scan (`experiments/rung3_census.py leaves`, exhaustive
`m ≤ 80`): the failures number 58 and sit at `m ∈ {5, 8, 16, 27}` exactly.  The relaxed system
`threeBlock_relax_A/W/V` — which drops `c` from two of the three — is already finite:
exhaustively for `m ≤ 70` its solutions have `m ∈ {5,6,7,8,10,12,13,16,27}`, all with
`3^k < 2^m < 2·3^k` except one at `m = 6`.  So the intended proof is
*near-critical window ⇒ `sep_two_three` ⇒ `k` bounded ⇒ finite check*, the same shape as rung 2's
`bd_reduction`. -/
theorem threeBlock_leaves_infeasible (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ))
    (hR3 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
        ≤ 3 ^ (b + d) * (3 ^ f - 1))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
          * (2 ^ (c + d) - 2 ^ c + 1)
        ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)))
    (hW : (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
        ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)) :
    False := by
  by_cases hshort : b + c + d + e + f + g ≤ 27
  · exact threeBlock_finite_infeasible b c d e f g hb hd hf hc he hshort hsub hlong hR3 hV hW
  by_cases hwin : 2 ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f)
  · exact threeBlock_window_infeasible b c d e f g hb hd hf hc he (by omega) hsub hwin hR3 hV hW
  · have hbig : 2 * 3 ^ (b + d + f) ≤ 2 ^ (b + c + d + e + f + g) := by omega
    have := threeBlock_nonwindow b c d e f g hb hd hf hc he hsub hbig
      (threeBlock_relax_A hR3) (threeBlock_relax_W hW) (threeBlock_relax_V hd hsub hV)
    omega

/-- The residual node of the census, now a one-line consequence of the exponent-only
`threeBlock_leaves_infeasible`: its hypotheses never mention `w₁, w₂, w₃`. -/
theorem threeBlock_ceiling_gap (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ))
    (hR3 : (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
        ≤ 3 ^ (b + d) * (3 ^ f - 1))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f))
          * (2 ^ (c + d) - 2 ^ c + 1)
        ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)))
    (hW : (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
        ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
            - 2 ^ (c + d + e + f)) :
    ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
      (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ :=
  (threeBlock_leaves_infeasible b c d e f g hb hd hf hc he hsub hlong hR3 hV hW).elim

/-- **The rung-3 census gap.**  Assembled from the three proved positivity leaves and the
disclosed residual `threeBlock_ceiling_gap`. -/
theorem threeBlock_gap_of_long (b c d e f g : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hc : 1 ≤ c) (he : 1 ≤ e)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ)) :
    ∀ w₁ w₂ w₃ : ℕ, 1 ≤ w₃ →
      3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1 →
      3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1 →
      (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f) : ℤ)
        < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * w₁ := by
  by_cases hR3 : (3 : ℤ) ^ (b + d) * (3 ^ f - 1)
      < 2 ^ (b + g) * (2 ^ (c + d + e + f)
          - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
  · exact threeBlock_gap_of_real hsub hR3
  by_cases hV : (3 : ℤ) ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
          - 2 ^ (c + d + e + f))
      < ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * (2 ^ (c + d) - 2 ^ c + 1)
  · exact threeBlock_gap_of_w2 hd hf hsub hV
  by_cases hW : (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
        - 2 ^ (c + d + e + f) : ℤ)
      < (2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)
  · exact threeBlock_gap_of_w1 hd hf hsub hW
  exact threeBlock_ceiling_gap b c d e f g hb hd hf hc he hsub hlong (not_lt.1 hR3)
    (not_lt.1 hV) (not_lt.1 hW)

/-- **Rung 3, the long-length half.**  Modulo the disclosed census gap `threeBlock_gap_of_long`,
no three-odd-block word of length outside `{5, 8, 16, 27}` is acyclic paradoxical.  The four
realized solutions all have length `8`; lengths `5`, `16`, `27` carry ceiling-passing tuples
that are killed by the true realizing residue (a finite check, not yet formalized). -/
theorem threeBlock_not_acyclicParadoxical_of_long {b c d e f g n : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ))
    (hword : traceWord n (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false) :
    ¬ AcyclicParadoxical n (b + c + d + e + f + g) := by
  rintro ⟨hn, hm, hsub, hlt⟩
  obtain ⟨hI, hII, hIII⟩ := threeBlock_segment_identities hword
  have hones : ones (traceWord n (b + c + d + e + f + g)) = b + d + f := by
    rw [hword, ones_append, ones_append, ones_append, ones_append, ones_append]
    simp
  rw [hones] at hsub
  exact absurd hlt
    (by have := threeBlock_of_gap hI hII hIII
          (threeBlock_gap_of_long b c d e f g hb hd hf hc he hsub hlong)
        omega)

end CollatzMoonshot.FrontA
