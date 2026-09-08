/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Paradoxical
import CollatzMoonshot.FrontA.ParityReconstruction

/-!
# Front A: the three-odd-block rung of the paradoxical ladder

`FrontA/Paradoxical.lean` closes rungs 1 and 2 of the *odd-block ladder* for acyclic paradoxical
shortcut segments: a word whose ones form one block (`headBlock_not_acyclicParadoxical`,
Rozier--Terracol Appendix A) or two blocks (`le_two_blocks_not_acyclicParadoxical`) realizes no
acyclic paradoxical start.  Rung 2 is **sharp**: `acyclicParadoxical_seven_eight` is a genuine
three-block witness (`n = 7`, `m = 8`).

This module closes **rung 3**, the first rung whose answer is a *classification* rather than an
exclusion:

> **Rung-3 theorem (front-normalized).**  Every acyclic paradoxical segment whose word has three
> odd blocks has length `8`.

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
* **`threeBlock_length_eq_eight_of_acyclicParadoxical`** — the full front-normalized
  classification.  The window argument excludes every length outside `{5,8,16,27}`; one
  kernel-checked finite certificate computes the least realizing residue at the ten remaining
  tuples of lengths `5`, `16`, and `27` and rejects them by the exact acyclic criterion.

## Where the deep content sits

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

The final proof uses the repo's Rhin-lite polynomial measure to make this empirical finiteness
effective, then a stronger convergent bracket and the sharp `3^5 ≤ 2^8` scaled algebra to contract
to a small exact census.  Thus rung 3 does consume a two-log measure, but unlike Front B's
`m`-cycle ladder its exponent system contracts to one bounded native certificate.
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

**Closed (2026-09-08).**  The residual is now proved by `threeBlock_window_infeasible` and the
single pruned `threeBlock_residual_cert`; `threeBlock_ceiling_gap` is a theorem with no `sorry`. -/
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
near-critical one, `3^k < 2^m < 2·3^k`, so rung 3's *residual* consumes the stronger polynomial
Rhin-lite measure rather than rung 2's `2^(-k/3)` consequence.  That measure enters only to
bootstrap into a fixed convergent bracket; the sharp scaled system then contracts the exact
census to `k ≤ 53`, `m ≤ 106`. -/

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

/-! ### The census chain at a general scale `2^m ≤ 2^t·D`

The non-window chain above is the case `t = 1`.  The initial lemmas record a coarse linear bound;
`threeBlock_scaled_k_bound` below sharpens it with `3^5 ≤ 2^8` to `k ≤ 6t+5`.  The window proof
uses this first at `t=26`, then at the exact small-range scale `t=8`. -/

/-- (A\*) at scale `t`. -/
theorem threeBlock_scaled_S2 {d e f t : ℕ} {D M : ℤ} (hD : 0 < D) (hMpos : 0 < M)
    (hM : M ≤ 2 ^ t * D) (hA : D * 2 ^ (d + e + f) < M * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d) := by
  have hp : (0 : ℤ) < 2 ^ (d + e + f) := by positivity
  have ht : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
  refine lt_of_mul_lt_mul_left ?_ hMpos.le
  nlinarith [hA, hM, hp, ht]

/-- (V\*) at scale `t`. -/
theorem threeBlock_scaled_S1 {d e t : ℕ} {D Pb : ℤ} (hD : 0 < D)
    (hPb : Pb * 3 ^ d ≤ 2 ^ t * D) (hV : D * 2 ^ d ≤ 2 * Pb * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ d * 3 ^ d ≤ 2 ^ (t + 1) * (2 ^ (d + e) + 3 ^ d) := by
  have h3 : (0 : ℤ) < (3 : ℤ) ^ d := by positivity
  have hsum : (0 : ℤ) < (2 : ℤ) ^ (d + e) + 3 ^ d := by positivity
  have hpow : (2 : ℤ) ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
  rw [hpow]
  refine le_of_mul_le_mul_left ?_ hD
  nlinarith [hV, hPb, h3, hsum]

/-- (W\*) at scale `t`. -/
theorem threeBlock_scaled_S3 {c d e f t : ℕ} {D Bg : ℤ} (hBg : 0 < Bg)
    (hm : Bg * 2 ^ (c + d + e + f) ≤ 2 ^ t * D)
    (hW : D + 2 ^ (c + d + e + f) < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d)) :
    (2 : ℤ) ^ (d + e + f) * (Bg + 2 ^ t) < 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) := by
  have hsplit : (2 : ℤ) ^ (c + d + e + f) = 2 ^ c * 2 ^ (d + e + f) := by
    rw [← pow_add]; congr 1; omega
  have hcpos : (0 : ℤ) < (2 : ℤ) ^ c := by positivity
  have ht : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
  refine lt_of_mul_lt_mul_left ?_ hcpos.le
  rw [hsplit] at hm hW
  nlinarith [hm, hW, ht]

/-- `F1` at scale `t`: `3^d ≤ 2^(2t+4+e)`. -/
theorem threeBlock_scaled_F1 {d e t : ℕ}
    (h : 2 ^ d * 3 ^ d ≤ 2 ^ (t + 1) * (2 ^ (d + e) + 3 ^ d)) : 3 ^ d ≤ 2 ^ (2 * t + 4 + e) := by
  rcases Nat.lt_or_ge d (t + 2) with hd | hd
  · calc (3 : ℕ) ^ d ≤ 4 ^ d := Nat.pow_le_pow_left (by norm_num) d
      _ = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (2 * t + 4 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- `2·2^(t+1) ≤ 2^d`, so the `3^d` term on the right absorbs into the left
    have habs : 2 * 2 ^ (t + 1) ≤ 2 ^ d := by
      have : (2 : ℕ) ^ (t + 2) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
      calc 2 * 2 ^ (t + 1) = 2 ^ (t + 2) := by rw [pow_succ]; ring
        _ ≤ 2 ^ d := this
    have h3 : 0 < (3 : ℕ) ^ d := by positivity
    have hmul : 2 * 2 ^ (t + 1) * 3 ^ d ≤ 2 ^ d * 3 ^ d := Nat.mul_le_mul_right _ habs
    have hde : (2 : ℕ) ^ (d + e) = 2 ^ d * 2 ^ e := pow_add 2 d e
    rw [hde] at h
    have hkey : 2 ^ d * 3 ^ d ≤ 2 ^ d * (2 ^ (t + 2) * 2 ^ e) := by
      have e1 : (2 : ℕ) ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring
      have : 2 * (2 ^ d * 3 ^ d) ≤ 2 * (2 ^ (t + 1) * (2 ^ d * 2 ^ e)) + 2 ^ d * 3 ^ d := by
        nlinarith [h, hmul]
      calc 2 ^ d * 3 ^ d ≤ 2 * (2 ^ (t + 1) * (2 ^ d * 2 ^ e)) := by omega
        _ = 2 ^ d * (2 ^ (t + 2) * 2 ^ e) := by rw [e1]; ring
    have hdpos : 0 < (2 : ℕ) ^ d := by positivity
    have := Nat.le_of_mul_le_mul_left hkey hdpos
    calc (3 : ℕ) ^ d ≤ 2 ^ (t + 2) * 2 ^ e := this
      _ = 2 ^ (t + 2 + e) := (pow_add 2 (t + 2) e).symm
      _ ≤ 2 ^ (2 * t + 4 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The envelope `2^(d+e) + 3^d ≤ 2^(2t+4+d+e)` used throughout (needs `1 ≤ d`). -/
theorem threeBlock_scaled_env {d e t : ℕ} (hd : 1 ≤ d) (h3d : 3 ^ d ≤ 2 ^ (2 * t + 4 + e)) :
    2 ^ (d + e) + 3 ^ d ≤ 2 ^ (2 * t + 4 + d + e) := by
  have h1 : (2 : ℕ) ^ (d + e) ≤ 2 ^ (2 * t + 3 + d + e) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (3 : ℕ) ^ d ≤ 2 ^ (2 * t + 3 + d + e) :=
    le_trans h3d (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : (2 : ℕ) ^ (2 * t + 4 + d + e) = 2 * 2 ^ (2 * t + 3 + d + e) := by
    rw [show 2 * t + 4 + d + e = (2 * t + 3 + d + e) + 1 by omega, pow_succ]; ring
  omega

/-- `F2` at scale `t`: `f ≤ 3t + 4`. -/
theorem threeBlock_scaled_F2 {d e f t : ℕ} (hd : 1 ≤ d) (h3d : 3 ^ d ≤ 2 ^ (2 * t + 4 + e))
    (h : 2 ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d)) : f ≤ 3 * t + 4 := by
  have henv := threeBlock_scaled_env hd h3d
  have hlt : (2 : ℕ) ^ (d + e + f) < 2 ^ (t + (2 * t + 4 + d + e)) := by
    calc (2 : ℕ) ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d) := h
      _ ≤ 2 ^ t * 2 ^ (2 * t + 4 + d + e) := Nat.mul_le_mul_left _ henv
      _ = 2 ^ (t + (2 * t + 4 + d + e)) := (pow_add 2 t (2 * t + 4 + d + e)).symm
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
  omega

/-- `F3` at scale `t`: `b + g ≤ 9t + 11`. -/
theorem threeBlock_scaled_F3 {b d e f g t : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f) (hf3 : f ≤ 3 * t + 4)
    (h3d : 3 ^ d ≤ 2 ^ (2 * t + 4 + e))
    (h : 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) < 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))) :
    b + g ≤ 9 * t + 11 := by
  have henv := threeBlock_scaled_env hd h3d
  have h3f : (3 : ℕ) ^ f ≤ 2 ^ (6 * t + 8) := by
    calc (3 : ℕ) ^ f ≤ 4 ^ f := Nat.pow_le_pow_left (by norm_num) f
      _ = 2 ^ (2 * f) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (6 * t + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hR : 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) ≤ 2 ^ (9 * t + 12 + d + e) := by
    calc 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))
        ≤ 2 ^ t * (2 ^ (6 * t + 8) * 2 ^ (2 * t + 4 + d + e)) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h3f henv)
      _ = 2 ^ (9 * t + 12 + d + e) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hL : 2 ^ (d + e + 1) * 2 ^ (b + g) ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) := by
    have hfge : (2 : ℕ) ^ (d + e + 1) ≤ 2 ^ (d + e + f) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (d + e + 1) * 2 ^ (b + g) ≤ 2 ^ (d + e + f) * 2 ^ (b + g) :=
          Nat.mul_le_mul_right _ hfge
      _ ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hlt : (2 : ℕ) ^ (d + e + 1 + (b + g)) < 2 ^ (9 * t + 12 + d + e) := by
    calc (2 : ℕ) ^ (d + e + 1 + (b + g)) = 2 ^ (d + e + 1) * 2 ^ (b + g) := by rw [pow_add]
      _ ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) := hL
      _ < 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) := h
      _ ≤ 2 ^ (9 * t + 12 + d + e) := hR
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
  omega

/-- The elementary sharp comparison `3^n ≤ 2^⌈8n/5⌉`, packaged with a Nat-valued ceiling.
This is the quantitative improvement over `3^n ≤ 4^n` needed by the window bootstrap. -/
theorem three_pow_le_two_pow_eight_fifths (n : ℕ) :
    3 ^ n ≤ 2 ^ (n + (3 * n + 4) / 5) := by
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hn : n = 5 * (n / 5) + n % 5 := by omega
  have hblock : (3 : ℕ) ^ (5 * (n / 5)) ≤ 2 ^ (8 * (n / 5)) := by
    simpa only [pow_mul] using
      Nat.pow_le_pow_left (show (3 : ℕ) ^ 5 ≤ 2 ^ 8 by norm_num) (n / 5)
  have hrem : (3 : ℕ) ^ (n % 5) ≤ 2 ^ (n % 5 + (3 * (n % 5) + 4) / 5) := by
    have hc : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hc with h | h | h | h | h <;> simp [h]
  calc 3 ^ n = 3 ^ (5 * (n / 5)) * 3 ^ (n % 5) := by
          conv_lhs => rw [hn, pow_add]
    _
      ≤ 2 ^ (8 * (n / 5)) * 2 ^ (n % 5 + (3 * (n % 5) + 4) / 5) :=
        Nat.mul_le_mul hblock hrem
    _ = 2 ^ (n + (3 * n + 4) / 5) := by rw [← pow_add]; congr 1; omega

/-- In the large-`d` branch, `S1` absorbs its own `3^d` term and loses only `t+2`. -/
theorem threeBlock_scaled_F1_large {d e t : ℕ} (hd : t + 2 ≤ d)
    (h : 2 ^ d * 3 ^ d ≤ 2 ^ (t + 1) * (2 ^ (d + e) + 3 ^ d)) :
    3 ^ d ≤ 2 ^ (t + 2 + e) := by
  have habs : 2 * 2 ^ (t + 1) ≤ 2 ^ d := by
    have : (2 : ℕ) ^ (t + 2) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    calc 2 * 2 ^ (t + 1) = 2 ^ (t + 2) := by rw [pow_succ]; ring
      _ ≤ 2 ^ d := this
  have hmul : 2 * 2 ^ (t + 1) * 3 ^ d ≤ 2 ^ d * 3 ^ d := Nat.mul_le_mul_right _ habs
  have hde : (2 : ℕ) ^ (d + e) = 2 ^ d * 2 ^ e := pow_add 2 d e
  rw [hde] at h
  have hkey : 2 ^ d * 3 ^ d ≤ 2 ^ d * (2 ^ (t + 2) * 2 ^ e) := by
    have e1 : (2 : ℕ) ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring
    have : 2 * (2 ^ d * 3 ^ d) ≤ 2 * (2 ^ (t + 1) * (2 ^ d * 2 ^ e)) + 2 ^ d * 3 ^ d := by
      nlinarith [h, hmul]
    calc 2 ^ d * 3 ^ d ≤ 2 * (2 ^ (t + 1) * (2 ^ d * 2 ^ e)) := by omega
      _ = 2 ^ d * (2 ^ (t + 2) * 2 ^ e) := by rw [e1]; ring
  have := Nat.le_of_mul_le_mul_left hkey (show 0 < (2 : ℕ) ^ d by positivity)
  calc (3 : ℕ) ^ d ≤ 2 ^ (t + 2) * 2 ^ e := this
    _ = 2 ^ (t + 2 + e) := (pow_add 2 (t + 2) e).symm

/-- Sharp closure of the `d < t+2` branch of the scaled system. -/
theorem threeBlock_scaled_small_d_bound {b d e f g t : ℕ} (hdsmall : d < t + 2)
    (hS2 : 2 ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d))
    (hS3 : 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t)
      < 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))) :
    b + d + f ≤ 6 * t + 5 := by
  set s := (3 * d + 4) / 5 with hs
  have h3d : (3 : ℕ) ^ d ≤ 2 ^ (d + s) := by
    rw [hs]
    exact three_pow_le_two_pow_eight_fifths d
  have hsum : (2 : ℕ) ^ (d + e) + 3 ^ d ≤ 2 ^ (d + e + s + 1) := by
    have h1 : (2 : ℕ) ^ (d + e) ≤ 2 ^ (d + e + s) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (3 : ℕ) ^ d ≤ 2 ^ (d + e + s) :=
      le_trans h3d (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc (2 : ℕ) ^ (d + e) + 3 ^ d ≤ 2 ^ (d + e + s) + 2 ^ (d + e + s) :=
          Nat.add_le_add h1 h2
      _ = 2 ^ (d + e + s + 1) := by rw [pow_succ]; ring
  have hf : f ≤ t + s := by
    have hlt : (2 : ℕ) ^ (d + e + f) < 2 ^ (t + (d + e + s + 1)) := by
      calc (2 : ℕ) ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d) := hS2
        _ ≤ 2 ^ t * 2 ^ (d + e + s + 1) := Nat.mul_le_mul_left _ hsum
        _ = 2 ^ (t + (d + e + s + 1)) := (pow_add 2 t _).symm
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
    omega
  set q := (3 * f + 4) / 5 with hq
  have h3f : (3 : ℕ) ^ f ≤ 2 ^ (f + q) := by
    rw [hq]
    exact three_pow_le_two_pow_eight_fifths f
  have hbg : b + g ≤ t + q + s := by
    have hL : (2 : ℕ) ^ (d + e + f + (b + g))
        ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) := by
      calc (2 : ℕ) ^ (d + e + f + (b + g))
          = 2 ^ (d + e + f) * 2 ^ (b + g) := by rw [pow_add]
        _ ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hR : 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))
        ≤ 2 ^ (t + (f + q) + (d + e + s + 1)) := by
      calc 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))
          ≤ 2 ^ t * (2 ^ (f + q) * 2 ^ (d + e + s + 1)) := by gcongr
        _ = 2 ^ (t + (f + q) + (d + e + s + 1)) := by
          rw [← pow_add, ← pow_add]
          congr 1 <;> omega
    have hlt : (2 : ℕ) ^ (d + e + f + (b + g))
        < 2 ^ (t + (f + q) + (d + e + s + 1)) := lt_of_le_of_lt hL (lt_of_lt_of_le hS3 hR)
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
    omega
  rw [hs] at hf hbg
  rw [hq] at hbg
  have hsle : (3 * d + 4) / 5 ≤ t + 1 := by omega
  omega

set_option maxHeartbeats 2400000 in
/-- **Sharp parameterized closure.**  The three failed-leaf inequalities at deficit scale
`2^m ≤ 2^t(2^m-3^k)` force `k ≤ 6t+5`.  The proof splits at `d=t+2`: below it the
`3^5≤2^8` envelope controls `f` and `b+g`; above it `S1` absorbs the `3^d` term, after which
`S2`, `S3`, and `V` give the same slope. -/
theorem threeBlock_scaled_k_bound (b c d e f g t : ℕ) (hc : 1 ≤ c)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hscale : (2 : ℤ) ^ (b + c + d + e + f + g)
      ≤ 2 ^ t * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)))
    (hA : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (d + e + f)
        < 2 ^ (b + c + d + e + f + g) * (2 ^ (d + e) + 3 ^ d))
    (hW : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) + 2 ^ (c + d + e + f)
        < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ d
        ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d)) :
    b + d + f ≤ 6 * t + 5 := by
  set m := b + c + d + e + f + g with hm
  set k := b + d + f with hk
  have hMpos : (0 : ℤ) < 2 ^ m := by positivity
  have hD : (0 : ℤ) < 2 ^ m - 3 ^ k := by
    have : (3 : ℤ) ^ k < 2 ^ m := by exact_mod_cast hsub
    linarith
  have hS2 := threeBlock_scaled_S2 hD hMpos hscale hA
  have hPb : (3 : ℤ) ^ b * 3 ^ f * 3 ^ d = 3 ^ k := by
    rw [hk, ← pow_add, ← pow_add]; congr 1; omega
  have hPD : (3 : ℤ) ^ b * 3 ^ f * 3 ^ d ≤ 2 ^ t * (2 ^ m - 3 ^ k) := by
    rw [hPb]
    have h3 : (0 : ℤ) < 3 ^ k := by positivity
    nlinarith [hscale]
  have hS1 := threeBlock_scaled_S1 hD hPD hV
  have hBg : (2 : ℤ) ^ (b + g) * 2 ^ (c + d + e + f) = 2 ^ m := by
    rw [hm, ← pow_add]; congr 1; omega
  have hS3 := threeBlock_scaled_S3 (show (0 : ℤ) < 2 ^ (b + g) by positivity)
    (by rw [hBg]; exact hscale) hW
  have n1 : 2 ^ d * 3 ^ d ≤ 2 ^ (t + 1) * (2 ^ (d + e) + 3 ^ d) := by exact_mod_cast hS1
  have n2 : 2 ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d) := by exact_mod_cast hS2
  have n3 : 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t)
      < 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d)) := by exact_mod_cast hS3
  by_cases hdsmall : d < t + 2
  · rw [hk]
    exact threeBlock_scaled_small_d_bound hdsmall n2 n3
  have hdlarge : t + 2 ≤ d := by omega
  have h3d : 3 ^ d ≤ 2 ^ (t + 2 + e) := threeBlock_scaled_F1_large hdlarge n1
  have hsum : (2 : ℕ) ^ (d + e) + 3 ^ d ≤ 2 ^ (d + e + 1) := by
    have h3d' : (3 : ℕ) ^ d ≤ 2 ^ (d + e) :=
      le_trans h3d (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc (2 : ℕ) ^ (d + e) + 3 ^ d ≤ 2 ^ (d + e) + 2 ^ (d + e) :=
          Nat.add_le_add_left h3d' _
      _ = 2 ^ (d + e + 1) := by rw [pow_succ]; ring
  have hf : f ≤ t := by
    have hlt : (2 : ℕ) ^ (d + e + f) < 2 ^ (t + (d + e + 1)) := by
      calc (2 : ℕ) ^ (d + e + f) < 2 ^ t * (2 ^ (d + e) + 3 ^ d) := n2
        _ ≤ 2 ^ t * 2 ^ (d + e + 1) := Nat.mul_le_mul_left _ hsum
        _ = 2 ^ (t + (d + e + 1)) := (pow_add 2 t _).symm
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
    omega
  set q := (3 * f + 4) / 5 with hq
  have h3f : (3 : ℕ) ^ f ≤ 2 ^ (f + q) := by
    rw [hq]
    exact three_pow_le_two_pow_eight_fifths f
  have hbg : b + g ≤ t + q := by
    have hL : (2 : ℕ) ^ (d + e + f + (b + g))
        ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) := by
      calc (2 : ℕ) ^ (d + e + f + (b + g))
          = 2 ^ (d + e + f) * 2 ^ (b + g) := by rw [pow_add]
        _ ≤ 2 ^ (d + e + f) * (2 ^ (b + g) + 2 ^ t) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hR : 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))
        ≤ 2 ^ (t + (f + q) + (d + e + 1)) := by
      calc 2 ^ t * (3 ^ f * (2 ^ (d + e) + 3 ^ d))
          ≤ 2 ^ t * (2 ^ (f + q) * 2 ^ (d + e + 1)) := by gcongr
        _ = 2 ^ (t + (f + q) + (d + e + 1)) := by
          rw [← pow_add, ← pow_add]
          congr 1 <;> omega
    have hlt : (2 : ℕ) ^ (d + e + f + (b + g))
        < 2 ^ (t + (f + q) + (d + e + 1)) := lt_of_le_of_lt hL (lt_of_lt_of_le n3 hR)
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hlt
    omega
  set r := (3 * (b + f) + 4) / 5 with hr
  have h3bf : (3 : ℕ) ^ b * 3 ^ f ≤ 2 ^ (b + f + r) := by
    calc (3 : ℕ) ^ b * 3 ^ f = 3 ^ (b + f) := by rw [pow_add]
      _ ≤ 2 ^ (b + f + (3 * (b + f) + 4) / 5) :=
        three_pow_le_two_pow_eight_fifths (b + f)
      _ = 2 ^ (b + f + r) := by rw [hr]
  have hVnat : (2 ^ m - 3 ^ k) * 2 ^ d
      ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d) := by
    have hle : (3 : ℕ) ^ k ≤ 2 ^ m := le_of_lt hsub
    rw [hm, hk] at hV hle
    exact_mod_cast hV
  have hDpow : (2 ^ m - 3 ^ k) * 2 ^ d ≤ 2 ^ (b + f + r + d + e + 2) := by
    calc (2 ^ m - 3 ^ k) * 2 ^ d
        ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d) := hVnat
      _ ≤ 2 * 2 ^ (b + f + r) * 2 ^ (d + e + 1) := by gcongr
      _ = 2 ^ (b + f + r + d + e + 2) := by
        change (2 ^ 1 * 2 ^ (b + f + r)) * 2 ^ (d + e + 1) = _
        rw [← pow_add, ← pow_add]
        congr 1 <;> omega
  have hDpow' : 2 ^ m - 3 ^ k ≤ 2 ^ (b + f + r + e + 2) := by
    exact Nat.le_of_mul_le_mul_right (by
      calc (2 ^ m - 3 ^ k) * 2 ^ d ≤ 2 ^ (b + f + r + d + e + 2) := hDpow
        _ = 2 ^ (b + f + r + e + 2) * 2 ^ d := by rw [← pow_add]; congr 1; omega)
      (show 0 < (2 : ℕ) ^ d by positivity)
  have hscaleNat : 2 ^ m ≤ 2 ^ t * (2 ^ m - 3 ^ k) := by
    have hle : (3 : ℕ) ^ k ≤ 2 ^ m := le_of_lt hsub
    exact_mod_cast hscale
  have hMpow : 2 ^ m ≤ 2 ^ (t + (b + f + r + e + 2)) := by
    calc 2 ^ m ≤ 2 ^ t * (2 ^ m - 3 ^ k) := hscaleNat
      _ ≤ 2 ^ t * 2 ^ (b + f + r + e + 2) := Nat.mul_le_mul_left _ hDpow'
      _ = 2 ^ (t + (b + f + r + e + 2)) := (pow_add 2 t _).symm
  have hme : m ≤ t + (b + f + r + e + 2) :=
    (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).1 hMpow
  rw [hm] at hme
  rw [hk, hq, hr] at *
  omega

/-- One pruned decision procedure covers both residual regimes: the old `m ≤ 27` node and the
near-critical window after it has been contracted to `k ≤ 53`, `m ≤ 106`.  Indexing first by
`(k,m)` and deriving `f,g` from the totals avoids a six-dimensional rectangular search. -/
private theorem threeBlock_residual_cert :
    ∀ k ∈ List.range 54, ∀ m ∈ List.range 107,
      m ∉ ({5, 8, 16, 27} : Finset ℕ) →
      3 ^ k < 2 ^ m → (m ≤ 27 ∨ 2 ^ m < 2 * 3 ^ k) →
      ∀ b ∈ List.range (k + 1), 1 ≤ b →
      ∀ d ∈ List.range (k - b + 1), 1 ≤ d →
      let f := k - b - d
      1 ≤ f →
      ∀ c ∈ List.range (m - k + 1), 1 ≤ c →
      ∀ e ∈ List.range (m - k - c + 1), 1 ≤ e →
      let g := m - k - c - e
      (2 : ℤ) ^ (b + g) * (2 ^ (c + d + e + f)
            - (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)))
          ≤ 3 ^ (b + d) * (3 ^ f - 1) →
      ((2 : ℤ) ^ m - 3 ^ k) * (2 ^ (c + d) - 2 ^ c + 1)
          ≤ 3 ^ b * (3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
              - 2 ^ (c + d + e + f)) →
      (2 : ℤ) ^ m - 3 ^ k
          ≤ 3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1))
              - 2 ^ (c + d + e + f) →
      False := by
  native_decide

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
  have hfdef : b + d + f - b - d = f := by omega
  have hgdef : b + c + d + e + f + g - (b + d + f) - c - e = g := by omega
  exact threeBlock_residual_cert (b + d + f) (by simp; omega)
    (b + c + d + e + f + g) (by simp; omega) hlong hsub (Or.inl hshort)
    b (by simp; omega) hb d (by simp; omega) hd (by omega)
    c (by simp; omega) hc e (by simp; omega) he
    (by simpa only [hfdef, hgdef] using hR3)
    (by simpa only [hfdef] using hV)
    (by simpa only [hfdef] using hW)

/-! ### Polynomial-measure bootstrap into the strong-bracket range -/

/-- The explicit Rhin-lite real linear-form measure implies a deliberately loose pure-`ℕ`
polynomial deficit bound.  Dropping the helpful factor `5^6000` keeps the later power-of-two
envelope simple and is still strong enough for the window bootstrap. -/
theorem rhinLite_nat_measure_loose (k m : ℕ) (hk : 1 ≤ k) (hsub : 3 ^ k < 2 ^ m)
    (hwin : 2 ^ m < 2 * 3 ^ k) :
    3 ^ k ≤ (2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436 := by
  have hmeas := rhinLite_log23_measure k m hk hsub hwin
  set Λ : ℝ := (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 with hΛ
  have e2 : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have e3 : (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hprod : (3 : ℝ) ^ k * Real.exp Λ = (2 : ℝ) ^ m := by
    rw [e3, ← Real.exp_add, e2]; congr 1; rw [hΛ]; ring
  have hDfac : (3 : ℝ) ^ k * (Real.exp Λ - 1) = (2 : ℝ) ^ m - (3 : ℝ) ^ k := by
    rw [mul_sub, mul_one, hprod]
  have hc : (1 : ℝ) / (2 * 396 ^ 6000 * 6 ^ 436) ≤ rhinLiteSepC := by
    unfold rhinLiteSepC
    have hp : (396 / 5 : ℝ) ^ 6000 ≤ 396 ^ 6000 :=
      pow_le_pow_left₀ (by positivity) (by norm_num) _
    apply one_div_le_one_div_of_le (by positivity)
    calc 2 * ((396 / 5 : ℝ) ^ 6000 * 6 ^ 436)
        ≤ 2 * (396 ^ 6000 * 6 ^ 436) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = 2 * 396 ^ 6000 * 6 ^ 436 := by ring
  have hkpow : (0 : ℝ) < (k : ℝ) ^ 436 := by positivity
  have hlow : (1 : ℝ) / ((2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436) ≤ Λ := by
    calc (1 : ℝ) / ((2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436)
        = (1 / (2 * 396 ^ 6000 * 6 ^ 436)) / k ^ 436 := by rw [div_div]
      _ ≤ rhinLiteSepC / k ^ 436 := div_le_div_of_nonneg_right hc hkpow.le
      _ ≤ Λ := by simpa [hΛ] using hmeas
  have hDreal : (3 : ℝ) ^ k /
      ((2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436)
      ≤ (2 : ℝ) ^ m - (3 : ℝ) ^ k := by
    calc (3 : ℝ) ^ k / ((2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436)
        = 3 ^ k * (1 / ((2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436)) := by ring
      _ ≤ 3 ^ k * Λ := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ 3 ^ k * (Real.exp Λ - 1) := by
        gcongr
        have := Real.add_one_le_exp Λ
        linarith
      _ = (2 : ℝ) ^ m - (3 : ℝ) ^ k := hDfac
  have hden : (0 : ℝ) < (2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436 := by positivity
  have hcross : (3 : ℝ) ^ k ≤ ((2 : ℝ) ^ m - (3 : ℝ) ^ k) *
      ((2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436) := by
    exact (div_le_iff₀ hden).mp hDreal
  have hcast : (((2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436 : ℕ) : ℝ)
      = ((2 : ℝ) ^ m - (3 : ℝ) ^ k) *
          ((2 * 396 ^ 6000 * 6 ^ 436 : ℝ) * (k : ℝ) ^ 436) := by
    push_cast [Nat.cast_sub (le_of_lt hsub)]
    ring
  have hreal : ((3 ^ k : ℕ) : ℝ) ≤
      (((2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436 : ℕ) : ℝ) := by
    rw [hcast]
    exact_mod_cast hcross
  exact_mod_cast hreal

/-- Kernel certificate for the deliberately loose Rhin-lite constant. -/
theorem rhinLite_loose_constant_le_two_pow :
    2 * 396 ^ 6000 * 6 ^ 436 ≤ 2 ^ 52905 := by
  decide +kernel

/-- Turn the polynomial measure into a power-of-two deficit scale using the binary length of
`k`.  This is the scale consumed by `threeBlock_scaled_k_bound`. -/
theorem threeBlock_polynomial_window_scale (k m : ℕ) (hk : 1 ≤ k)
    (hsub : 3 ^ k < 2 ^ m) (hwin : 2 ^ m < 2 * 3 ^ k) :
    2 ^ m ≤ 2 ^ (52906 + 436 * (Nat.log 2 k + 1)) * (2 ^ m - 3 ^ k) := by
  have hmeas := rhinLite_nat_measure_loose k m hk hsub hwin
  have hklt : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hkpow : k ^ 436 ≤ 2 ^ (436 * (Nat.log 2 k + 1)) := by
    calc k ^ 436 ≤ (2 ^ (Nat.log 2 k + 1)) ^ 436 :=
          Nat.pow_le_pow_left (le_of_lt hklt) _
      _ = 2 ^ (436 * (Nat.log 2 k + 1)) := by rw [← pow_mul]; congr 1; omega
  have hC : (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436
      ≤ 2 ^ (52905 + 436 * (Nat.log 2 k + 1)) := by
    calc (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436
        ≤ 2 ^ 52905 * 2 ^ (436 * (Nat.log 2 k + 1)) :=
          Nat.mul_le_mul rhinLite_loose_constant_le_two_pow hkpow
      _ = 2 ^ (52905 + 436 * (Nat.log 2 k + 1)) := (pow_add 2 _ _).symm
  have hDC : (2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436
      ≤ (2 ^ m - 3 ^ k) * 2 ^ (52905 + 436 * (Nat.log 2 k + 1)) := by
    calc (2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436
        = (2 ^ m - 3 ^ k) * ((2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436) := by ring
      _ ≤ (2 ^ m - 3 ^ k) * 2 ^ (52905 + 436 * (Nat.log 2 k + 1)) :=
        Nat.mul_le_mul_left _ hC
  calc 2 ^ m ≤ 2 * 3 ^ k := by omega
    _ ≤ 2 * ((2 ^ m - 3 ^ k) * (2 * 396 ^ 6000 * 6 ^ 436) * k ^ 436) :=
      Nat.mul_le_mul_left _ hmeas
    _ ≤ 2 * ((2 ^ m - 3 ^ k) * 2 ^ (52905 + 436 * (Nat.log 2 k + 1))) :=
      Nat.mul_le_mul_left _ hDC
    _ = 2 ^ (52906 + 436 * (Nat.log 2 k + 1)) * (2 ^ m - 3 ^ k) := by
      rw [show 52906 + 436 * (Nat.log 2 k + 1) =
        (52905 + 436 * (Nat.log 2 k + 1)) + 1 by omega, pow_succ]
      ring

/-- A small elementary crossover used only to make the polynomial bootstrap numerical. -/
theorem ten_thousand_mul_le_two_pow (n : ℕ) (hn : 18 ≤ n) : 10000 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hten : 10000 ≤ 2 ^ n := by
        have : 10000 ≤ 10000 * n := by omega
        omega
      rw [pow_succ]
      omega

/-- The polynomial Rhin-lite measure and the sharp scaled closure put every residual window
tuple below `492276`, exactly the range of the next strong convergent bracket. -/
theorem threeBlock_polynomial_k_lt (b c d e f g : ℕ) (hc : 1 ≤ c)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g))
    (hwin : 2 ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f))
    (hA : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ (d + e + f)
        < 2 ^ (b + c + d + e + f + g) * (2 ^ (d + e) + 3 ^ d))
    (hW : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) + 2 ^ (c + d + e + f)
        < 3 ^ f * 2 ^ c * (2 ^ (d + e) + 3 ^ d))
    (hV : ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ d
        ≤ 2 * (3 ^ b * 3 ^ f) * (2 ^ (d + e) + 3 ^ d)) :
    b + d + f < 492276 := by
  set k := b + d + f with hk
  set m := b + c + d + e + f + g with hm
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hsub hwin
    norm_num at hsub hwin
    have hm0 : m = 0 := by
      by_contra hm
      have hm1 : 1 ≤ m := by omega
      have htwo : (2 : ℕ) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
      norm_num at htwo
      omega
    exact hsub hm0
  set t := 52906 + 436 * (Nat.log 2 k + 1) with ht
  have hscaleNat := threeBlock_polynomial_window_scale k m hkpos hsub hwin
  have hscaleZ : (2 : ℤ) ^ m ≤ 2 ^ t * (2 ^ m - 3 ^ k) := by
    have hle : (3 : ℕ) ^ k ≤ 2 ^ m := le_of_lt hsub
    rw [ht]
    exact_mod_cast hscaleNat
  have hkbound : k ≤ 6 * t + 5 := by
    rw [hk, hm] at hsub hA hW hV hscaleZ
    exact threeBlock_scaled_k_bound b c d e f g t hc hsub hscaleZ hA hW hV
  by_contra hnot
  have hklarge : 492276 ≤ k := by omega
  have hpow18 : 2 ^ 18 ≤ k := by omega
  have hlog18 : 18 ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by norm_num) hpow18
  have hlogpow := ten_thousand_mul_le_two_pow (Nat.log 2 k) hlog18
  have hkne : k ≠ 0 := by omega
  have hpowlow : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hkne
  have hlogle : 10000 * Nat.log 2 k ≤ k := le_trans hlogpow hpowlow
  rw [ht] at hkbound
  omega

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

/-- The extra convergent bracket closes the interval left between the polynomial bootstrap and
`sep_strong_190537`.  Its separation exponent is `25`, hence the whole power `2^m` has scale
`26` relative to the deficit. -/
theorem threeBlock_window_scale_492276 {b c d e f g : ℕ} (hk : 0 < b + d + f)
    (hklt : b + d + f < 492276)
    (hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g)) :
    (2 : ℤ) ^ (b + c + d + e + f + g)
      ≤ 2 ^ 26 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) := by
  have hS := sep_strong_492276 (b + d + f) (b + c + d + e + f + g) hk hklt hsub
  have hle : (3 : ℕ) ^ (b + d + f) ≤ 2 ^ (b + c + d + e + f + g) := le_of_lt hsub
  have hSN : 2 ^ (b + c + d + e + f + g)
      ≤ 2 ^ 26 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) := by
    calc
      2 ^ (b + c + d + e + f + g) =
          (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) + 3 ^ (b + d + f) := by omega
      _
          ≤ (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) +
              (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * 2 ^ 25 :=
            Nat.add_le_add_left hS _
      _ ≤ 2 ^ 26 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) := by
        nlinarith
  have hSNZ : ((2 ^ (b + c + d + e + f + g) : ℕ) : ℤ)
      ≤ ((2 ^ 26 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) : ℕ) : ℤ) := by
    exact_mod_cast hSN
  push_cast [Nat.cast_sub hle] at hSNZ
  exact hSNZ

/-- Exact small-range separation scale.  This finite certificate is only over the two aggregate
exponents; it is deliberately separate from the six-exponent leaf census below. -/
private theorem threeBlock_small_scale_cert :
    ∀ k ∈ List.range 162, ∀ m ∈ List.range 323,
      0 < k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
      2 ^ m ≤ 2 ^ 8 * (2 ^ m - 3 ^ k) := by
  decide +kernel

theorem threeBlock_small_window_scale (k m : ℕ) (hk : 0 < k) (hk161 : k ≤ 161)
    (hsub : 3 ^ k < 2 ^ m) (hwin : 2 ^ m < 2 * 3 ^ k) :
    2 ^ m ≤ 2 ^ 8 * (2 ^ m - 3 ^ k) := by
  have h3 : 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) _
  have hm : m ≤ 2 * k := by
    have hp : 2 ^ m < 2 ^ (2 * k + 1) := by
      calc
        2 ^ m < 2 * 3 ^ k := hwin
        _ ≤ 2 * 4 ^ k := Nat.mul_le_mul_left 2 h3
        _ = 2 ^ (2 * k + 1) := by rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hp
    omega
  exact threeBlock_small_scale_cert k (by simp; omega) m (by simp; omega) hk hsub hwin

/-- **Node 2 of the rung-3 crux — PROVED.**  In the near-critical window, the Rhin-lite
polynomial measure and `threeBlock_scaled_k_bound` first give `k < 492276`.  The next convergent
bracket gives deficit scale `t=26`, hence `k ≤ 161`; an exact two-exponent certificate improves
the scale to `t=8`, hence `k ≤ 53` and `m ≤ 106`.  The shared residual certificate then closes
the six-exponent leaves. -/
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
  have hArel := threeBlock_relax_A hR3
  have hWrel := threeBlock_relax_W hW
  have hVrel := threeBlock_relax_V hd hsub hV
  have hkpos : 0 < b + d + f := by omega
  have hkpoly := threeBlock_polynomial_k_lt b c d e f g hc hsub hwin hArel hWrel hVrel
  have hscale26 := threeBlock_window_scale_492276 hkpos hkpoly hsub
  have hk161 : b + d + f ≤ 161 := by
    have := threeBlock_scaled_k_bound b c d e f g 26 hc hsub hscale26 hArel hWrel hVrel
    norm_num at this ⊢
    exact this
  have hscale8N := threeBlock_small_window_scale (b + d + f)
    (b + c + d + e + f + g) hkpos hk161 hsub hwin
  have hscale8 : (2 : ℤ) ^ (b + c + d + e + f + g)
      ≤ 2 ^ 8 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) := by
    have hscale8Z : ((2 ^ (b + c + d + e + f + g) : ℕ) : ℤ)
        ≤ ((2 ^ 8 * (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) : ℕ) : ℤ) := by
      exact_mod_cast hscale8N
    push_cast [Nat.cast_sub (le_of_lt hsub)] at hscale8Z
    exact hscale8Z
  have hk53 : b + d + f ≤ 53 := by
    have := threeBlock_scaled_k_bound b c d e f g 8 hc hsub hscale8 hArel hWrel hVrel
    norm_num at this ⊢
    exact this
  have hm106 : b + c + d + e + f + g ≤ 106 := by
    have h3 : 3 ^ (b + d + f) ≤ 4 ^ (b + d + f) := Nat.pow_le_pow_left (by norm_num) _
    have hp : 2 ^ (b + c + d + e + f + g) < 2 ^ (2 * (b + d + f) + 1) := by
      calc
        2 ^ (b + c + d + e + f + g) < 2 * 3 ^ (b + d + f) := hwin
        _ ≤ 2 * 4 ^ (b + d + f) := Nat.mul_le_mul_left 2 h3
        _ = 2 ^ (2 * (b + d + f) + 1) := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]
          ring
    have hm2k := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hp
    omega
  have hfdef : b + d + f - b - d = f := by omega
  have hgdef : b + c + d + e + f + g - (b + d + f) - c - e = g := by omega
  have hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ) := by
    simp
    omega
  exact threeBlock_residual_cert (b + d + f) (by simp; omega)
    (b + c + d + e + f + g) (by simp; omega) hlong hsub (Or.inr hwin)
    b (by simp; omega) hb d (by simp; omega) hd (by omega)
    c (by simp; omega) hc e (by simp; omega) he
    (by simpa only [hfdef, hgdef] using hR3)
    (by simpa only [hfdef] using hV)
    (by simpa only [hfdef] using hW)

/-- **THE RUNG-3 CRUX, in exponent form.**  The residual census, with the cascade scales
`w₁, w₂, w₃` eliminated: no exponent tuple of length outside `{5, 8, 16, 27}` fails all three
positivity leaves at once.  Host scan (`experiments/rung3_census.py leaves`, exhaustive
`m ≤ 80`): the failures number 58 and sit at `m ∈ {5, 8, 16, 27}` exactly.  The proved route is
*near-critical window ⇒ polynomial Rhin-lite measure ⇒ fixed convergent bracket ⇒ sharp scaled
contraction ⇒ one pruned finite check*. -/
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

/-- **The rung-3 census gap.**  Assembled from the three positivity leaves and the proved
residual `threeBlock_ceiling_gap`. -/
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

/-- **Rung 3, the long-length half.**  No three-odd-block word of length outside
`{5, 8, 16, 27}` is acyclic paradoxical.  The four
realized solutions all have length `8`; lengths `5`, `16`, `27` carry ceiling-passing tuples
that are killed below by a kernel-checked true-realizing-residue certificate. -/
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

/-! ### The exceptional finite tail and the full classification -/

/-- The least possible interior scale when only the second cascade equation and `w₃ ≥ 1`
are retained. -/
private def threeBlock_minW₂ (d e f : ℕ) : ℕ :=
  (2 ^ (e + f) - 2 ^ e + 1) ⌈/⌉ 3 ^ d

/-- The corresponding least possible head scale, retaining both cascade equations. -/
private def threeBlock_minW₁ (b c d e f : ℕ) : ℕ :=
  (2 ^ (c + d) * threeBlock_minW₂ d e f - 2 ^ c + 1) ⌈/⌉ 3 ^ b

/-- The nested ceilings really are lower bounds for every integer cascade triple. -/
private theorem threeBlock_minW₁_le {b c d e f w₁ w₂ w₃ : ℕ}
    (hd : 1 ≤ d) (hf : 1 ≤ f) (h₃ : 1 ≤ w₃)
    (h₁ : 3 ^ b * w₁ + 2 ^ c = 2 ^ (c + d) * w₂ + 1)
    (h₂ : 3 ^ d * w₂ + 2 ^ e = 2 ^ (e + f) * w₃ + 1) :
    threeBlock_minW₁ b c d e f ≤ w₁ := by
  obtain ⟨hw₂pos, -⟩ := threeBlock_cascade_pos hd hf h₃ h₁ h₂
  have hL₂ : 2 ^ (e + f) - 2 ^ e + 1 ≤ 3 ^ d * w₂ := by
    have hpow : 2 ^ e ≤ 2 ^ (e + f) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmul : 2 ^ (e + f) ≤ 2 ^ (e + f) * w₃ := by
      simpa using Nat.mul_le_mul_left (2 ^ (e + f)) h₃
    omega
  have hw₂ : threeBlock_minW₂ d e f ≤ w₂ := by
    exact (ceilDiv_le_iff_le_mul (show 0 < 3 ^ d by positivity)).2 hL₂
  have hmul : 2 ^ (c + d) * threeBlock_minW₂ d e f ≤ 2 ^ (c + d) * w₂ :=
    Nat.mul_le_mul_left _ hw₂
  have hbase : 2 ^ (c + d) * threeBlock_minW₂ d e f - 2 ^ c + 1 ≤ 3 ^ b * w₁ := by
    have hpow : 2 ^ c ≤ 2 ^ (c + d) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : 2 ^ c ≤ 2 ^ (c + d) * w₂ := by
      calc 2 ^ c ≤ 2 ^ (c + d) := hpow
        _ ≤ 2 ^ (c + d) * w₂ := by
          simpa using Nat.mul_le_mul_left (2 ^ (c + d)) hw₂pos
    have heq : 2 ^ (c + d) * w₂ - 2 ^ c + 1 = 3 ^ b * w₁ := by omega
    rw [← heq]
    exact Nat.add_le_add_right (Nat.sub_le_sub_right hmul _) _
  exact (ceilDiv_le_iff_le_mul (show 0 < 3 ^ b by positivity)).2 hbase

private def threeBlockWord (b c d e f g : ℕ) : List Bool :=
  List.replicate b true ++ List.replicate c false ++ List.replicate d true ++
    List.replicate e false ++ List.replicate f true ++ List.replicate g false

/-- Least realizing starts above `2` for the ten ceiling-passing tuples at the exceptional
lengths `5`, `16`, and `27`.  The certificate below independently checks which entry applies,
its whole parity trace, its canonical-residue property, and failure of the acyclic criterion. -/
private def threeBlockExceptionalStarts : List ℕ :=
  [33, 63759, 41679, 18783, 60255, 64351, 80553407, 50946431, 110715135, 120086783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- **Kernel-checked exceptional-tail certificate.**  The nested cascade ceiling first reduces
the three exceptional lengths to ten tuples.  For each tuple this certificate supplies its least
realizing start above `2` and checks that the exact word numerator is no larger than the
subcritical deficit times that start. -/
private theorem threeBlock_exceptional_residue_cert :
    ∀ m ∈ ([5, 16, 27] : List ℕ),
    ∀ k ∈ List.range 28, 3 ^ k < 2 ^ m →
    ∀ b ∈ List.range (k + 1), 1 ≤ b →
    ∀ d ∈ List.range (k - b + 1), 1 ≤ d →
    let f := k - b - d
    1 ≤ f →
    ∀ c ∈ List.range (m - k + 1), 1 ≤ c →
    ∀ e ∈ List.range (m - k - c + 1), 1 ≤ e →
    let g := m - k - c - e
    ((2 : ℤ) ^ m - 3 ^ k) * threeBlock_minW₁ b c d e f ≤
      3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)) -
        2 ^ (c + d + e + f) →
    ∃ r ∈ threeBlockExceptionalStarts,
      traceWord r m = threeBlockWord b c d e f g ∧
      r = (if r % 2 ^ m ≤ 2 then r % 2 ^ m + 2 ^ m else r % 2 ^ m) ∧
      numer (threeBlockWord b c d e f g) ≤ (2 ^ m - 3 ^ k) * r := by
  decide +kernel

/-- A canonical representative of a residue class modulo `M`, chosen to be the least member
strictly above `2`, is below every other member of that class strictly above `2`. -/
private theorem canonicalResidueAboveTwo_le {r n M : ℕ} (hM : 0 < M) (hn : 2 < n)
    (hr : r = if r % M ≤ 2 then r % M + M else r % M)
    (hmod : r ≡ n [MOD M]) : r ≤ n := by
  unfold Nat.ModEq at hmod
  split at hr
  · rename_i hsmall
    have hnM : M ≤ n := by
      by_contra h
      have hnmod : n % M = n := Nat.mod_eq_of_lt (by omega)
      omega
    have hq : 1 ≤ n / M := (Nat.one_le_div_iff hM).2 hnM
    have hMmul : M ≤ M * (n / M) := by
      calc M = M * 1 := by simp
        _ ≤ M * (n / M) := Nat.mul_le_mul_left M hq
    have hdecomp := Nat.mod_add_div n M
    omega
  · rw [hr, hmod]
    exact Nat.mod_le n M

/-- **The exceptional tail.**  A front-normalized three-block word at one of the three
ceiling-passing lengths other than `8` cannot be acyclic paradoxical.  The proof obtains the
actual cascade scale `w₁`, lowers it to the nested ceiling, invokes the finite certificate, and
uses parity-trace residue determinacy to compare an arbitrary realizing start with the certified
least one. -/
theorem threeBlock_not_acyclicParadoxical_of_exceptional {b c d e f g n : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hexceptional : b + c + d + e + f + g ∈ ({5, 16, 27} : Finset ℕ))
    (hword : traceWord n (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false) :
    ¬ AcyclicParadoxical n (b + c + d + e + f + g) := by
  rintro ⟨hn, -, hsubTrace, hlt⟩
  have hones : ones (traceWord n (b + c + d + e + f + g)) = b + d + f := by
    rw [hword, ones_append, ones_append, ones_append, ones_append, ones_append]
    simp
  have hsub : 3 ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by
    rwa [hones] at hsubTrace
  obtain ⟨hI, hII, hIII⟩ := threeBlock_segment_identities hword
  obtain ⟨w₁, w₂, w₃, hw₃, hw, hc₁, hc₂, -⟩ := threeBlock_cascade hI hII hIII
  have hwmin : threeBlock_minW₁ b c d e f ≤ w₁ :=
    threeBlock_minW₁_le hd hf hw₃ hc₁ hc₂
  have hcriterion := (threeBlock_criterion hI hII hIII hw).1 hlt
  have hDnonneg : (0 : ℤ) ≤ 2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f) := by
    have : (3 : ℤ) ^ (b + d + f) < 2 ^ (b + c + d + e + f + g) := by
      exact_mod_cast hsub
    omega
  have hwminZ : (threeBlock_minW₁ b c d e f : ℤ) ≤ w₁ := by exact_mod_cast hwmin
  have hminCriterion :
      ((2 : ℤ) ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) *
          threeBlock_minW₁ b c d e f ≤
        3 ^ f * (2 ^ (c + d + e) - 2 ^ (c + d) + 3 ^ d * (2 ^ c - 1)) -
          2 ^ (c + d + e + f) :=
    le_trans (mul_le_mul_of_nonneg_left hwminZ hDnonneg) hcriterion
  have hfdef : b + d + f - b - d = f := by omega
  have hgdef : b + c + d + e + f + g - (b + d + f) - c - e = g := by omega
  have hmle : b + c + d + e + f + g ≤ 27 := by
    have hex := hexceptional
    simp at hex
    omega
  have hkle : b + d + f ≤ b + c + d + e + f + g := by omega
  have hmList : b + c + d + e + f + g ∈ ([5, 16, 27] : List ℕ) := by
    simpa using hexceptional
  obtain ⟨r, -, hrtrace, hrcanonical, hfail⟩ :=
    threeBlock_exceptional_residue_cert (b + c + d + e + f + g) hmList
      (b + d + f) (by simp; omega) hsub
      b (by simp; omega) hb d (by simp; omega) hd (by omega)
      c (by simp; omega) hc e (by simp; omega) he
      (by simpa only [hfdef] using hminCriterion)
  have hrtrace' : traceWord r (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false := by
    simpa only [hfdef, hgdef, threeBlockWord] using hrtrace
  have hmod : r ≡ n [MOD 2 ^ (b + c + d + e + f + g)] :=
    traceWord_eq_imp_modEq (hrtrace'.trans hword.symm)
  have hrle : r ≤ n := canonicalResidueAboveTwo_le (by positivity) hn hrcanonical hmod
  have hDmul :
      (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * r ≤
        (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * n :=
    Nat.mul_le_mul_left _ hrle
  have hfail' :
      numer (List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false)
        ≤ (2 ^ (b + c + d + e + f + g) - 3 ^ (b + d + f)) * r := by
    simpa only [hfdef, hgdef, threeBlockWord] using hfail
  have hacrit :=
    (acyclicParadoxical_criterion n (b + c + d + e + f + g) hsubTrace).1 hlt
  rw [hones, hword] at hacrit
  exact (not_lt_of_ge (hfail'.trans hDmul)) hacrit

/-- **Rung 3, full front-normalized classification.**  A three-odd-block acyclic paradoxical
segment has length exactly `8`. -/
theorem threeBlock_length_eq_eight_of_acyclicParadoxical {b c d e f g n : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hword : traceWord n (b + c + d + e + f + g)
      = List.replicate b true ++ List.replicate c false ++ List.replicate d true
          ++ List.replicate e false ++ List.replicate f true ++ List.replicate g false)
    (hap : AcyclicParadoxical n (b + c + d + e + f + g)) :
    b + c + d + e + f + g = 8 := by
  by_contra hne
  by_cases hexceptional : b + c + d + e + f + g ∈ ({5, 16, 27} : Finset ℕ)
  · exact (threeBlock_not_acyclicParadoxical_of_exceptional hb hd hf hc he hexceptional hword) hap
  · have hlong : b + c + d + e + f + g ∉ ({5, 8, 16, 27} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hexceptional ⊢
      omega
    exact (threeBlock_not_acyclicParadoxical_of_long hb hd hf hc he hlong hword) hap

end CollatzMoonshot.FrontA
