# The 3x+1 conjugacy as a complexity ladder: beyond-Terras mixing, and whether `Q` preserves normality

Ren on Fable, 2026-10-21 (00:30-05:30 session, Trevor's brief: "brand new, not the open lanes").
A new object for this repo, sitting between Collatz and the normal-numbers programme.  Nothing here
is a lever on the run-count gap; it is a different question about the same map.  Lean:
`CollatzMoonshot/Conjugacy/Ladder.lean` (branch `ren/conjugacy-ladder`).  Scratch and probes:
`~/personal/tmp/ren-qladder-20261021/` (`bias.py`, `decomp.py`, `profile.py`, `qnorm.py`,
`siblings.py`, `modk.py`, `threeadic.py`).

## 0. Summary

Let `T(n) = n/2` (even), `(3n+1)/2` (odd), on `ℤ₂`, and `Q(x) = (T^i(x) mod 2)_i` the parity
word (Terras: `x mod 2^k ↔ (w_0..w_{k-1})`).  Three things were done tonight.

1. **A new statistic.**  `E_j := Σ_{r<2^j} (−1)^{T^j(r)}`, the excess of even over odd `j`-th
   iterates over all `j`-bit inputs - the first parity *past* the Terras range.  Exact values
   `j = 1..28`: `2, 2, 6, 6, 14, 18, 34, 34, 30, 14, 38, 42, 114, 178, 282, 362, 354, 570, 790,
   1042, 2482, 4206, 4254, 8054, 12150, 13738, 16890, 28682, 33986, 56482, 83458` (`j = 29..31` from `bigE.py`).  Not in OEIS (three queries); no
   source states it (Lagarias's two bibliographies, Kontorovich-Lagarias 2009 §3.1, Feix-Muriel-
   Rouet 1994, Tao 2022 Prop. 1.9 all stop at the Terras boundary).  Empirically
   `E_j ≍ 2^{j/2}` (ratio `E_j/2^{j/2}` in `[0.44, 3.0]`, mostly `1-2`) and **positive for every
   `j ≤ 31`**.  Siblings `3x+5`, `3x+7`, `5x+1`, `7x+1` have the same `2^{j/2}` size with
   *fluctuating* sign; `3x−1` is tied exactly by `E_j(3,−1) = 2 − E_j(3,1)` (negation symmetry).
2. **Exact structure.**  `T^j(r) < 3^{a}` for every `r < 2^j` (`a` = number of odd steps), so
   `T^j(r)` *is* the least residue `N_v·2^{−j} mod 3^a`; the sign sum obeys the exact recursion
   `E_m = 2E_{m−1} − 2·G_{m−1}(c_m)` (`G` the sum over one residue class mod 3, `c_m = 2 − 2^{m−1}
   mod 3`), which is the total mass of a 3-adic renormalisation of the signed measure
   `μ_m = Σ_{r<2^m} (−1)^{T^m r} δ_r` on `ℤ₃` (§3).  In 3-adic Fourier terms
   `E_m = (4/3)E_{m−1} + (2/3)·(mod-3 Fourier coefficients of μ_{m−1})`; the constant mode alone
   would give `b_m = E_m/2^m ≍ (2/3)^m`, and the data say the fine-frequency feed dominates.
3. **`Q` scrambles.**  Thue-Morse, period-doubling, Fibonacci (Sturmian), Champernowne, a
   golden-mean word (no `11`) and a biased coin all come out of `Q` and of `Q^{−1}` with block
   statistics indistinguishable from iid at `M = 30000` digits (lengths `1..10`).  So, numerically,
   `Q` preserves normality in neither direction, and the Collatz orbit of the Thue-Morse 2-adic
   integer is equidistributed.  López-Stoll 2009 (Integers 9, A13) checked full factor complexity
   of `Q^{−1}(Sturmian)` to length 5 and suggested it holds in general; the normality framing, the
   forward direction, and the automatic / Champernowne / biased inputs are not in print.

The ladder (§5): finite digits ⇒ eventually periodic word is **Collatz**; rational ⇒ rational is
**Lagarias's periodicity conjecture** (one direction proved); automatic ⇒ normal (conjectured
here); normal ⇏ normal (conjectured here, both ways).  `Q` preserves Kolmogorov dimension exactly
and, conjecturally, nothing finite-state above the rational rung.

## 1. The object, and what is already known

Write `x = Σ ε_j 2^j ∈ ℤ₂`.  Then (Bernstein-Lagarias 1996, Canad. J. Math. 48, Lemma B.5 for
the whole class of maps; re-derived tonight before the literature check)

    w_j = ε_j ⊕ f_j(ε_0, …, ε_{j−1}),      f_j = parity of T^j(x mod 2^j).

So `Q` is a *triangular* automorphism of `{0,1}^ℕ` with feedback `f`.  `f_0 = f_1 = 0` (so
`Q(x) ≡ x mod 4`, readable from B-L Table 2.1, `Φ̂₂ = id`), `f_2 = ε_0 ∧ ¬ε_1` (B-L Table 2.1 row
`n = 3`, the transposition `1 ↔ 5 mod 8`).  Known: `Q` is a measure-preserving homeomorphism
(Lagarias 1985 Thm L), a 2-adic isometry (B-L Cor. A.3 - Terras restated), nowhere differentiable
(Müller 1991/94).  Lagarias's **periodicity conjecture**: `Q(x)` eventually periodic ⟺ `x ∈ ℚ`;
proved direction: eventually periodic word ⇒ rational `x` (Bernstein's formula
`Q^{−1}(w) = −Σ_i 2^{d_i} 3^{−(i+1)}`, `d_i` the positions of the ones).

The engine of everything below is the shift identity (proved in Lean tonight, L1):

    T^j(r + 2^j) = T^j(r) + 3^{a_j(r)},

so the parity of `T^j` flips between the two lifts, `f_j` is the parity of the *lower* lift, and

    b_j := E_j / 2^j = E_{ε uniform}[(−1)^{f_j}] = E_{x ∈ ℤ₂}[(−1)^{ε_j(x) + w_j(x)}],

the correlation between the `j`-th binary digit and the `j`-th parity letter.  Equivalently: the
conditional expectation of the `j`-th digit given `T^j(x) = y` is `b_j · (−1)^{y}` - knowing the
`j`-th image's parity tells you the `j`-th digit with advantage `b_j`.  `b_0 = b_1 = 1`,
`b_2 = 1/2`, `b_3 = 3/4`, then decay.

## 2. Numerics

### 2.1 The bias

| `j` | `E_j` | `E_j/2^{j/2}` | `j` | `E_j` | `E_j/2^{j/2}` |
|---|---|---|---|---|---|
| 10 | 14 | 0.44 | 20 | 1042 | 1.02 |
| 12 | 42 | 0.66 | 22 | 4206 | 2.05 |
| 14 | 178 | 1.39 | 24 | 8054 | 1.97 |
| 16 | 362 | 1.41 | 26 | 13738 | 1.68 |
| 18 | 570 | 1.11 | 28 | 28682 | 1.75 |
| 19 | 790 | 1.09 | 30 | 56482 | 1.72 |
| 21 | 2482 | 1.71 | 31 | 83458 | 1.80 |

`|b_j|^{1/j}` sits at `0.71-0.73` from `j = 14` on (`2^{−1/2} = 0.707`).  The increments
`F_k = E_{k+1} − E_k = Σ_{s<2^k} (−1)^{T^k(3s+2)}` (the odd-start half) are positive for 24 of
the 27 values and carry the drift.

### 2.2 Where the sign lives: `ν mod 4`

Split the `2^j` values `ν = T^j(r)` by residue mod 4 (deviation from `2^{j−2}`, `j = 20`):
`ν ≡ 0: +231`, `≡ 1: +213`, `≡ 2: +290`, `≡ 3: −734`.  The same shape at `j = 16, 18`: the class
`ν ≡ 3 (mod 4)`, i.e. the two-letter continuation `11` right after the Terras range, is deficient
by about `2^{(j−1)/2}`, and the other three classes share the surplus.  Mod 16 the deviations and
the Walsh spectrum are all `O(1)·2^{j/2}` with no single dominant mask (`modk.out`), so at the
`2^{j/2}` scale the picture is random-walk-like **except** for the persistent sign.  The cycle
entrants (`r < 2^j` whose orbit has reached `{1,2}` by step `j`, about `3.7·(4/3)^j` of them,
phase-biased `+0.14` at `j = 20`) account for only 161 of `E_20 = 1042`; the bulk is in flight.
The sign is unexplained (§6).

**Localisation (`signprobe.py`, `j = 18, 20, 22`).**  Split `E_j` by the last two parity letters
`(w_{j−2}, w_{j−1})`: classes `00, 01, 10, 11` contribute `(−0.61, +1.24, +0.39, +0.09)`,
`(−0.52, +1.12, +0.19, +0.22)`, `(−0.07, +1.61, +0.53, −0.02)` times `2^{j/2}`.  **The excess
sits in the words ending `01`.**  Exactly: with `n_c = #{r < 2^j : T^{j−2}(r) ≡ c (mod 8)}` and
`dev(c) = n_c − 2^{j−3}`, one bit short of the Terras range gives `dev(c) = −dev(c+4)`, and

    E_j = 2·[dev(0) − dev(1) + dev(2) + dev(3)],   class `01` = 2·dev(2),

so the sign is the statement that `T^{j−2}(r) ≡ 2 (mod 8)` is over-represented, and `≡ 6`
under-represented, among `j`-bit `r` by about `0.6·2^{j/2}`.  Writing `r = r₀ + 2^{j−2}s`
(`s < 4`), `T^{j−2}(r) ≡ ν₀ + 3^a s (mod 8)` runs over a 4-term window of the 8 residues with odd
step `3^a mod 8`, so the deviation is a statement about the joint law of `(ν₀ mod 8, a mod 2)`
at depth `j − 2`: the recursion does not close, but it names the object.

### 2.3 The mixing profile beyond the range (`profile.py`, `j = 20`)

`b_{j,t} := 2^{−j} Σ_{n<2^j} (−1)^{T^{j+t}(n)}`.  For `t ≤ 20` it stays at `10^{−3}..10^{−2}`
(`2^{−10}..2^{−7}`), drifting up slowly; the fraction of orbits inside `{1,2}` grows from `0.1%`
(`t = 0`) to `6%` (`t = 20`), `27%` (`t = 40`), `51%` (`t = 64`), `95%` (`t = 128`); the in-flight
population's bias turns negative around `t ≈ 24-72` (slow orbits are odd-heavy: selection) and
positive again later.  So the window in which the parity letters of `j`-bit integers are nearly
unbiased extends about `j` steps past the Terras boundary, and is then eaten by the cycle.

### 2.4 Scrambling (`qnorm.py`, `M = 30000`)

Max relative block-frequency deviation, lengths `1..10`, for the OUTPUT of `Q` and `Q^{−1}`:

| input | input dev (L=1,4,8) | `Q(input)` (L=1,4,8) | `Q^{−1}(input)` (L=1,4,8) |
|---|---|---|---|
| iid control | 0.007 0.061 0.283 | 0.009 0.051 0.249 | 0.005 0.076 0.340 |
| biased coin 1/3 | 0.337 2.21 8.84 | 0.005 0.032 0.238 | 0.004 0.049 0.314 |
| Thue-Morse | 0 1.67 20.3 | 0.003 0.039 0.343 | 0.005 0.023 0.257 |
| period-doubling | 0.333 1.67 20.3 | 0.014 0.051 0.368 | 0.002 0.041 0.306 |
| Fibonacci (Sturmian) | 0.236 2.78 36.4 | 0.008 0.056 0.257 | 0.002 0.026 0.289 |
| Champernowne | 0.050 0.308 0.684 | 0.010 0.080 0.383 | 0.012 0.077 0.306 |
| golden-mean (no `11`) | 0.452 1.80 5.79 | 0.005 0.052 0.326 | 0.011 0.045 0.274 |

Every output row matches the iid control.  Read: `Q^{−1}(golden-mean)` is a 2-adically normal
integer whose parity word avoids `11` (normal ⇏ Collatz-generic), `Q(biased coin)` is a normal
parity word of a non-normal 2-adic integer (Collatz-generic ⇏ normal), and `Q(Thue-Morse)`,
`Q(Sturmian)` look normal: zero-entropy inputs come out with full entropy.  (Irrationality of
`Q^{−1}(w)` for these `w` is immediate: an aperiodic word of upper 1-density below `log 2/log 3`
gives a bounded, hence eventually periodic, `3x+q` integer orbit if `x` were rational - the
López-Stoll 2021 observation.)

## 3. Exact structure (proved tonight; Lean in `Conjugacy/Ladder.lean`, commit `247e0095`)

Lean status (agent, 2026-10-21 01:40): `lake build CollatzMoonshot` green (8836 jobs), Maze audit
passes, no `sorry`, no `native_decide`, every theorem below on exactly
`[propext, Classical.choice, Quot.sound]`.  Proved: the shift identity
`tstep_iterate_add_mul_two_pow` (`T^j(r + c·2^j) = T^j r + c·3^{a_j(r)}`) and its corollaries
(`accWord_add_two_pow`: the `j`-th letter flips; `accWord_congr_mod`: it depends only on
`r mod 2^{j+1}`); the size bound `tstep_iterate_lt_three_pow` (restating
`FrontA.tstep_iterate_lt_pow_ones`) with `tstep_iterate_eq_of_modEq` (the `j`-th iterate of a
`j`-bit start is the unique `y < 3^a` with `2^j y ≡ numer(v) (mod 3^a)`); the triangular pair
`Qword`/`Qinv` with `Qword_Qinv`, `Qinv_Qword`, `QwordEquiv : (ℕ → Bool) ≃ (ℕ → Bool)`;
`Qword_eq_xor` (`w_j = ε_j ⊕ feedback`); `feedback_zero/one/two`; the integer rung
`Qword_natDigits : Qword (natDigits n) = accWord n`, `not_diverges_of_integerRung`,
`integerRung_of_rationalRung`; and `bias 0..8 = 1, 2, 2, 6, 6, 14, 18, 34, 34` by `decide`
(`+kernel` for 7, 8).  Frozen Props: `IntegerRung`, `RationalRung`, `BiasDecays`, `BiasSqrtLaw`,
`BiasPositive`, `QNotNormalityPreserving`, `QinvNotNormalityPreserving`,
`ThueMorseCollatzGeneric`, `SturmianCollatzGeneric` (Fibonacci word via `Real.goldenRatio`).

**(3.1) Size.**  For `r < 2^j`: `T^j(r) < 3^{a_j(r)}`.  (Induction with the shift identity: `T^j`
of a `(j+1)`-bit number is `< 2·3^a`; the even child is `< 3^a`, the odd child
`≤ (3(2·3^a − 1)+1)/2 = 3^{a+1} − 1`.)  Hence `T^j(r) = ν_v := (N_v·2^{−j}) mod 3^{a_v}` exactly
(no wrap; `decomp.py` confirms `kmax = 0` to `j = 22`), where `v` is the parity word and
`N_v = Σ_i 3^{a−1−i} 2^{d_i}`.  Corollary: `T^j(r) ≥ 3^a/2 ⟺ bit_{j−1}(r) = 1`.

**(3.2) Two-child recursion on residues.**  From a node `(ν, a)` with `ν < 3^a`, the two
children are `(T(y), a + ℓ)` where `y ∈ {ν, ν + 3^a}` is the one with parity `ℓ`.  The child's
parity is `bit_1(y)`, and `bit_1(ν + 3^a) = bit_1(ν) ⊕ bit_0(ν) ⊕ [a odd]`, so

    E_{j+1} = 2 · Σ_{|v| = j,  ν_v ≡ a_v (mod 2)} (−1)^{bit_1(ν_v)}.

**(3.3) Mod-3 recursion.**  Splitting `E_m` by the parity of `r` and reading the odd branch
`r = 2s+1 ↦ 3s+2` as the residue class `2 mod 3` of `[0, 3·2^{m−1})`, the shift identity on the
three blocks of length `2^{m−1}` gives signs `+,−,+` and the CRT picks one block per residue
mod 3:

    E_m = 2E_{m−1} − 2·G_{m−1}(c_m),   G_k(c) := Σ_{y<2^k, y≡c (3)} (−1)^{T^k y},   c_m = 2 − 2^{m−1} mod 3,

equivalently `E_m = 2·Σ_{y<2^{m−1}, y ≢ c_m (3)} (−1)^{T^{m−1} y}`.  Checked exactly for
`m ≤ 28` (`threeadic.py`, column `ok`).

**(3.4) The signed measure and its renormalisation.**  Let `μ_m = Σ_{y<2^m} (−1)^{T^m y} δ_y`
as a signed measure on `ℤ₃`.  Then, with `A_k = {z ≡ 2 − k·2^{m−1} (mod 3)}` (a partition of
`ℤ₃`) and `ψ_k(z) = (2z − 1 + k·2^m)/3` (an inverse Collatz branch, affine, expanding `A_k` onto
`ℤ₃`),

    μ_m = (×2)_* μ_{m−1} + Σ_{k=0}^{2} (−1)^k (ψ_k)_* (μ_{m−1}|_{A_k}).

The even branch is a 3-adic isometry; the odd branch spreads each third of the measure over the
whole space with alternating signs.  In 3-adic Fourier terms (`μ̂(ξ) = Σ (−1)^{T^m y} e(ξy)`,
`ξ ∈ ℤ[1/3]/ℤ`):

    μ̂_m(ξ) = μ̂_{m−1}(2ξ) + (1/3) Σ_{t ∈ ℤ/3} C_m(ξ,t) · μ̂_{m−1}((2ξ+t)/3),   |C_m| = |1 − ω + ω²|, ω = e(2^{m−1}(2ξ+t)/3),

so `E_m = μ̂_m(0) = (4/3)E_{m−1} + (2/3)·(unit-modulus combination of μ̂_{m−1}(±1/3))`.
Information flows from fine 3-adic frequencies to coarse ones, one level per odd step.  Measured
(`threeadic.py`): `|μ̂_m(1/3)|, |μ̂_m(1/9)| = (0.1..2.3)·2^{m/2}`, i.e. at the noise level, and
`(4/3)^m/2^{m/2} → 0` (`0.19` at `m = 28`), so the coarse mode is not what carries `E_m`.  This
pins the question: **`b_m → 0` is the statement that the parity signs are equidistributed at
every 3-adic scale simultaneously**, with the odd branch's `(+,−,+)` alternation as the only
cancellation mechanism.

**(3.5) What the residue picture says about the sign.**  `ν_v` is never `≡ 0 (mod 3)` once
`a ≥ 1`; uniform-on-units would give zero parity bias, so the bias is a non-uniformity of the
`2^j` residues `ν_v` in `[0, 3^a)` - at the `2^{j/2}` scale, consistently in one direction.

## 4. Conjectures (frozen as Props, `Conjugacy/Ladder.lean`)

- **C1 `BiasDecays`** (85%): `b_j → 0`.  The first-letter-past-Terras equidistribution.  Even this
  is not in the literature; Feix-Muriel-Rouet 1994 prove uniformity of `T^k(n) mod 2^k` over a
  *full* residue class mod `2^k`, not over the finite window `[0, 2^j)`.
- **C2 `BiasSqrtLaw`** (60%): `|E_j| ≤ C·2^{j/2}`; **`BiasPositive`** (60%): `E_j > 0` for all
  `j ≥ 1`.  The second is the puzzle: 28 of 28, while every sibling map flips.
- **C3** (80% each): `Q` does not preserve normality (`∃ ε` normal with `Q(ε)` not normal) and
  neither does `Q^{−1}`.  Candidate witnesses: `Q^{−1}(w)` for `w` a golden-mean word (Parry-
  measure-a.e. `w`, or a specific one); `Q(x)` for `x` with iid biased digits.  A proof needs a
  *mixing lemma* for the feedback: `f_j` asymptotically balanced and independent of the last `L`
  digits (equivalently `g_j(w_{<j}) = `parity of `T^j` of the least lift of a parity prefix).
- **C4 `ThueMorseCollatzGeneric`** (70%): the parity word of `τ = Σ t_n 2^n` is normal, i.e. the
  `T`-orbit of the Thue-Morse 2-adic integer is Haar-equidistributed.  Same for the Fibonacci
  2-adic integer.  These are explicit "Collatz-generic" points; a proof would be a normality proof
  for a specific sequence and is out of reach without new structure.

**(3.6) Not yet in Lean:** the mod-3 recursion (3.3), the renormalisation (3.4), and the
one-bit-short antisymmetry `dev(c) = −dev(c + 2^{K−1})` of §2.2; all three are `decide`-checkable
at small `m` and routine inductions.  Next-lap targets.

## 5. The ladder, and why Collatz is its bottom rung

Order 2-adic integers (equivalently words) by complexity: finite support ⊂ eventually periodic
(`ℚ ∩ ℤ₂`) ⊂ automatic ⊂ zero entropy ⊂ finite-state dimension `< 1` ⊂ normal.  Ask whether `Q`
maps rung `k` into rung `k`.

| rung | `Q` maps it into | status |
|---|---|---|
| finite support (`ℕ`) | eventually `(10)^∞` | **the Collatz conjecture** (no-divergence + no-cycle) |
| `ℚ ∩ ℤ₂` | eventually periodic | **Lagarias periodicity conjecture**; converse proved |
| automatic (Thue-Morse, period-doubling) | normal-looking | C4; "normal" is the opposite end |
| Sturmian | full-complexity (López-Stoll, to length 5); normal-looking here | C4 |
| finite-state dim `< 1` (biased coin) | normal-looking | C3 |
| normal | not necessarily normal (`Q^{−1}` golden-mean) | C3 |
| Kolmogorov dimension `d` | dimension `d` | **exact**: `Q_k` is a computable bijection on prefixes |

The repo's Maze already records that an *integer's* parity word is never normal
(`accWord_not_normal_of_diverges`: divergence forces 1-density `≥ log 2/log 3`, and convergence
forces periodicity).  So on the integers `Q` is maximally structure-preserving, and one rung up
it is (conjecturally) maximally scrambling.  Collatz is the statement that the scrambling
*fails* on exactly the finite-support inputs, forced by integrality: the parity letters of `n` past
`log₂ n` are the pure feedback `f_j(bits(n), 0, 0, …)`, look random for about `log₂ n` more steps
(§2.3), and must then lock into `1010…`.  The periodicity conjecture is the same statement for the
`3x+q` maps at once.

**A rung between rational and normal: transcendence.**  Adamczewski-Bugeaud (2007) say a real
number with an automatic non-periodic expansion is transcendental.  The conjugacy analogue:
*if the parity vector of `x ∈ ℤ₂` is automatic and not eventually periodic, is `x` a 2-adic
transcendental?*  Irrationality is known when the 1-density is below `log 2/log 3` (bounded
`3x+q` orbit); nothing is known about algebraicity.  The rational-orbit argument fails for
algebraic `x` because `T^k(x) = (3^{a_k}x + N_k)/2^k` acquires denominators at the *other* places
of `ℚ(x)` above 2.  López-Stoll's continued fraction for `Q^{−1}(Sturmian)` is the only structural
handle in print.  Named, not frozen: `AutomaticParityTranscendental` (confidence 55% true, 10%
provable soon).

**The Collatz-Champernowne constant.**  Concatenate, for `n = 1, 2, 3, …`, the first
`⌈C log₂ n⌉` parity letters of `n` (`C ≥ 1` fixed; `C = ∞` with "stop at 1" needs Collatz to be
well defined).  Normality of this binary sequence is *equivalent* to a short-interval,
beyond-Terras equidistribution: for `n` in an initial segment of `[2^k, 2^{k+1})` of length `m`,
the letters at positions `> log₂ m` are feedback bits of `(log₂ m)`-bit integers with fixed high
bits.  Even `C = 1` is not automatic (the Terras order of the `k`-bit words is not an arbitrary
order; a block-adversarial order of all `k`-words breaks Champernowne's argument at the half-block).
Frozen as prose here; a Lean statement is the natural next node.

## 6. The sign puzzle, and what a proof of C1 would need

Dead tonight: (i) the `(4/3)^j` constant mode (too small by `j = 28`); (ii) the cycle entrants
(`≈ 3.7·(4/3)^j`, wrong continuation pattern: they avoid both `00` and `11`, the data lose only
`11`); (iii) a wrap term (there is none, (3.1)); (iv) uniform-on-units (gives zero).  Open: why
`ν ≡ 3 (mod 4)` is deficient over `[0, 2^j)`, equivalently why `(ν ≡ 0, a odd)` and `(ν ≡ 2, a
even)` are in excess (the lift `ν + 3^a` of the missing class).  A correlation between `ν mod 4`
and `a mod 2` among `j`-bit integers is the exact thing to explain.

For C1 the honest route is (3.4): show the signed measure `μ_m/2^m` tends to zero weakly on `ℤ₃`.
The crude `L²` bound gives no contraction (the even branch is an isometry, the odd branch is
`1/√3`-contracting per piece and there are three pieces); the gain must come from the `(+,−,+)`
alternation across the three translates by `2^{m−1}`, a 3-adic *unit*, i.e. from decorrelation of
the parity signs under translation by a unit.  That is a Gelfond-type statement
(sum-of-base-3-digits parity of `T^j(r)` equidistributes over the structured set of residues
`ν_v`), and the words give an averaging that the deterministic Erdős question (base-3 digits of
`2^n`) lacks.  Confidence that C1 has an elementary proof along these lines: 35%.


**One crux for the whole ladder.**  Every rung above the rational one reduces to the same
mechanism.  C3 in either direction needs a positive-density set of digits (or letters) steered
through the feedback while the rest stay normal, and that is exactly "`g_j(w_{<j})` (the parity
of `T^j` of the least lift of a parity prefix) is asymptotically balanced and decorrelated from
the recent letters"; a density-zero steering set changes nothing (normality is insensitive to
it), and no exact trick avoids the feedback because `ε_j = w_j ⊕ g_j` is the only freedom.  C1 is
the first moment of that statement.  So the ladder has one open node: **mixing of the Terras
feedback**, with `b_j → 0` as its cheapest consequence and the beyond-Terras window (§2.3) as its
quantitative shadow.

## 7. Siblings (control)

`E_j/2^{j/2}` at `j = 15..20`: `3x+1`: `1.56 1.41 0.98 1.11 1.09 1.02`; `3x+5`: `0.08 −0.24
−0.56 −1.14 −0.68 −0.43`; `3x+7`: `0.77 0.33 −0.48 −0.28 −0.09 0.20`; `5x+1`: `0.54 0.35 0.41
0.36 −0.83 0.00`; `7x+1`: `−0.65 −0.34 0.05 −0.28 0.89 0.94`; `x+1`: `−2^{j/2}` exactly (`T^j(r) =
⌈r/2^j⌉ = 1` for `r ≥ 1`).  The `2^{j/2}` size is generic for the class `qx+c`; the sign is not.

## 8. Novelty (literature pass 2026-10-21, sources read in full: B-L 1996, both Lagarias
bibliographies, K-L 2009, López-Stoll 2009)

- Triangular form, `Q ≡ id mod 4`, `f_2`: **B-L 1996 Lemma B.5 / Table 2.1**.  Cited, not claimed.
- `E_j`, the beyond-Terras bias, its size and sign, the mixing profile: **not found** (and not in
  OEIS).
- `Q` versus normality, both directions; automatic and biased inputs; the Thue-Morse Collatz-generic
  point: **not found**.  López-Stoll 2009 is the nearest (Sturmian, full complexity, length 5).
- The 3-adic signed-measure renormalisation (3.4): not found; it is elementary once asked.
- Collatz-Champernowne constant: not found.

## 9. Next

1. Explain the sign (§6): tabulate `(ν mod 4, a mod 2)` jointly; test whether the deficit is a
   last-letters effect (words ending in `…1`, `…01`) by splitting on `v_{j−1}, v_{j−2}`.
2. Push `E_j` to `j = 32` (chunked numpy, minutes) to see whether the sign survives; a single
   negative value settles `BiasPositive`.
3. Lean: the Collatz-Champernowne constant and its equivalence with short-interval
   equidistribution; the (3.3) recursion as a theorem (`decide`-checkable to small `m`).
4. C1 via (3.4): a treadmill-shaped target is the `L²` estimate for one odd step with the
   alternating translates; measure the actual contraction ratio `‖μ_m‖₂/‖μ_{m−1}‖₂` first.
