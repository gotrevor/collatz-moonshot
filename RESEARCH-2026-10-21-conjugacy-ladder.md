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

**(3.6) Lean status after the second half (§10.5):** the mod-3 recursion (3.3) is `bias_succ`
(`Recursion.lean`, proved), the one-bit-short antisymmetry is `depth_antisymm` (proved, from
`depth_count`); the renormalisation (3.4) as a measure identity is not in Lean (its mod-3 shadow,
`biasDecays_iff_classFluct`, is).

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
| density zero (`Σ 2^{n²}`, `Σ 2^{2^n}`, primes) | normal-looking, both directions | §10.3b, C4c-d |
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
0.36 −0.83 0.00`; `7x+1`: `−0.65 −0.34 0.05 −0.28 0.89 0.94`; `x+1`: `E_j = 2 − 2^j` exactly (`T^j(r) = ⌈r/2^j⌉ = 1` for `r ≥ 1`).  The `2^{j/2}` size is generic for the class `qx+c`; the sign is not.

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

## 10. Second half (02:00-05:30): exact consequences, the band law, the Champernowne threshold

### 10.1 Exact (Lean: `Conjugacy/Recursion.lean`, `Conjugacy/Bands.lean`; status in §10.5)

- **`bias j ≡ 2 (mod 4)` for every `j ≥ 1`, hence `bias j ≠ 0`.**  The first beyond-Terras letter
  is never exactly balanced over `[0, 2^j)`.  From the mod-3 recursion: `E_m = 2(E_{m−1} −
  G_{m−1}(c_m))`, and `E_{m−1} − G_{m−1}(c_m)` is odd because `E_{m−1}` is even, `G_{m−1}(c) ≡
  #{y < 2^{m−1} : y ≡ c (3)} (mod 2)`, and the class `c_m` has `(2^{m−1} − 1)/3` (`m−1` even,
  `c_m = 1`) or `(2^{m−1} + 1)/3` (`m−1` odd, `c_m = 0`) elements, both odd.  Matches all 31
  computed values (`E_j mod 4 = 2`; mod 8 shows no pattern).
- **Aligned-window invariance.**  `Σ_{r ∈ [c·2^j, (c+1)·2^j)} (−1)^{T^j r} = (−1)^c E_j` (lift
  identity).  The bias is a constant of the level, not a small-numbers effect; the sign question is
  exactly "lower half versus upper half of each period `2^{j+1}`", i.e. the correlation between
  bit `j` and letter `j`, and `E_j = Σ_{r<2^j} (−1)^{f_j(r)}` is the Walsh coefficient `f̂_j(∅)` of
  the feedback.  All other digit-letter correlations vanish: `E[(−1)^{ε_i + w_j}] = δ_{ij} b_j`.
- **Terras at depth `j`.**  `#{r < 2^{j+i} : T^j r ≡ c (mod 2^i)} = 2^j` for every `c < 2^i`
  (induction on `i` with the lift identity: the two lifts `r₀`, `r₀ + 2^{j+i}` have `T^j` values
  differing by `2^i·3^a`, an odd multiple of `2^i`).  Hence one bit beyond the range `dev(c) =
  −dev(c + 2^i)`, §2.2 generalised, and `E_j = 2 Σ_{c<2^L} dev_L(c)(−1)^{w_L(c)}` for every `L`.
- **Digit form of the bias.**  For `u = {d_0 < … < d_{a−1}} ⊂ [0, j)` put `S(u) := Σ_{i<a}
  2^{d_i}/3^{i+1} ∈ ℤ₂` (so `S(u) = N_v/3^a`, and `S({d_0} ∪ u') = (2^{d_0} + S(u'))/3`).  Then
  `r_u = (−S(u)) mod 2^j`, `T^j(r_u) = 3^a (r_u + S(u))/2^j`, and since `S(u)` has a one at
  `d_0 < j`, the parity of `T^j(r_u)` is `¬ s_j(S(u))` (`s_j` = the `j`-th 2-adic digit), so

      E_j = 1 − Σ_{∅ ≠ u ⊂ [0,j)} (−1)^{s_j(S(u))}.

  `BiasPositive` ⟺ among the nonempty `u`, the `j`-th 2-adic digit of `Σ_i 2^{d_i}/3^{i+1}` is `1`
  strictly more often than `0`.  The digit sequence of the rational `N/3^a` is the parity sequence
  of the halving dynamics `t ↦ t·2^{−1} mod 3^a`, i.e. the binary digits of the real `N/3^a` read
  backwards within each period: the beyond-Terras parity is a *binary digit of a fraction with
  denominator `3^a`*, Erdős-style, averaged over the structured set of numerators `N_v`.  Lean:
  `bias_eq_one_add_digitSum` (`Digits.lean`, proved; `digitSum j = Σ_{u≠∅} (if s_j then 1 else −1)
  = −Σ (−1)^{s_j}`), with the per-element lemma `tstep_iterate_even_iff_padicDigit` and the Terras
  bijection `onesSet_injOn`/`onesSet_surjOn` as theorems.  Also proved there: the digit-letter
  correlation matrix is diagonal (`corr_diag`, `corr_off`).
- **Small bands** (`E_{j,a} := Σ_{r<2^j, a(r)=a} (−1)^{T^j r}`): `E_{j,0} = E_{j,j} = 1` (`r = 0`,
  `r = 2^j − 1`), `E_{j,1} = j mod 2` (one odd step at position `d`: `T^j(r) = 1` if `j − d` even,
  `2` if odd), `E_{j,2} = O(j)` (`4, 13` at `j = 8, 26`).

### 10.2 The band law (numerics: `tmp/ren-qladder-b-20261021/aband.py`, `aband2.py`)

Split `E_j` by `a = ` number of odd steps; the band has `C(j,a)` members (Terras).  At `j = 26`,
`a = 2..24`: `13, 56, 160, 358, 560, 564, 393, 574, 131, 1752, −2454, 1456, 4440, 1866, −1333,
1500, 2167, 1210, 182, 28, 84, 24, 5` - 21 positive, 2 negative, each of size `(0.1..1.7)·√C(j,a)`.
Over `j = 16..26` the inner bands `2 ≤ a ≤ j−2` are positive 156 times and negative 41, with
mean normalised value `E_{j,a}/√C(j,a) = +0.40 .. +0.67` (rising slowly in `j`) and spread
`≈ 0.6`.  So:

**Within a level, the bands share a sign.**  In a random-sign model the bands would be `±1` in
these units with mean `0`; here they are coherent, at the `√C(j,a)` scale, with no privileged band:
not the cycle, not the `(4/3)^j` boundary mode (`= Σ_a C(j,a)/3^a`, the `ξ = 0` term below), not
the small-`a` bands (exactly computable, `O(j)`).  Frozen as `BandCoherence` (`Bands.lean`).

**Control (siblings, `aband2.py`, `j = 18..24`).**  The within-level coherence is *generic*: for
`3x+5`, `3x+7`, `5x+1`, `7x+1` the bands of a level also share a sign - but that sign wanders with
`j` (`3x+5`: band mean `−0.65` at `j = 18`, `+0.24` at `j = 24`, `E_j` from `−586` to `+7970`;
`3x+7`: `−0.24 → +0.12`; `7x+1`: `+0.2 .. +0.55`, 16 of 18 bands positive at `j = 21`), and
`3x−1` mirrors `3x+1` band by band (`E_j(3x−1) = 2 − E_j(3x+1)`).  So "coherent bands" is a
property of the family, and "persistent sign" is specific to `3x+1` (and its mirror).

**Mechanism of the coherence: inheritance.**  Splitting the mod-3 recursion by band,

    E_{m,a} = E_{m−1,a} + E_{m−1,a−1} − 2·G_{m−1,a−1}(c_m),

band `a` at level `m` is the sum of bands `a` and `a−1` at level `m−1` minus twice the class-`c_m`
slice of band `a−1`: a Pascal recursion with a leak of about one third.  Signs propagate down the
triangle from common ancestors, which is why a level's bands agree; the `√C(j,a)` size is the
accumulated leak noise along the inheritance paths (the exactly-positive seeds `E_{j,0} = E_{j,j} =
1` and the odd-interval mean `C(j,a)/3^a` are negligible against it).  The band law
`E_{j,a} ≈ κ_j √C(j,a)` therefore just re-expresses `b̃_j := E_j/2^{j/2} = Σ_a κ_{j,a}
√(C(j,a)/2^j) ≈ κ_j (2πj)^{1/4}` with a *level-dependent* `κ_j`; a `j^{1/4}` growth of `b̃_j`
would need `κ_j` to stay put, and §10.4 says it need not (frozen anyway as `BiasQuarterPowerLaw`,
25%).

Where this moves the puzzle.  The archimedean constraint is automatic (`2^j ν − N_v = 3^a r_v ≥
0`), so the multiplicity of a residue is purely 3-adic: `m_a(y) = M_a(y) := #{v : ones(v) = a,
N_v ≡ 2^j y (mod 3^a)}`, and

    E_{j,a} = Σ_{z ∈ ℤ/3^a} P_j(z) M_a(z),   P_j(z) = (−1)^{least residue of 2^{−j} z}.

Fourier on `ℤ/3^a`: `P̂_j(ξ) = 2/(1 + e(−2^j ξ/3^a))` (modulus `1/|cos(π 2^j ξ/3^a)|`, large at the
parity frequencies `2^j ξ ≈ 3^a/2`), and `M̂_a(ξ) = Σ_{d_0<…<d_{a−1}} Π_i e(ξ 2^{d_i}/3^{i+1})`, a
rank-indexed product - a 3-adic Horner transform of the binomial lattice, in which the `i`-th one
sees `ξ` only mod `3^{i+1}` and its position only mod `2·3^i`.  The `√C(j,a)` coherence has to
come from the pairing of `P̂_j` with `M̂_a` at the parity frequencies.  That is the object to
compute next; it is a finite transfer-matrix calculation per `(j, a)`.

### 10.3 The Collatz-Champernowne family (Lean: `Conjugacy/Champernowne.lean`)

`𝒞_C` := the concatenation, over `n = 1, 2, 3, …`, of the first `C·size(n)` parity letters of `n`
(`size` = bit length).  Three statements, all new:

1. **`𝒞_1` is normal, unconditionally** (believed, 85%; frozen with `sorry`).  For `n ∈ [2^{k−1},
   2^k)` the word is the `k`-letter Terras word; its first `k−1` letters depend only on `n mod
   2^{k−1}` and run bijectively over all `(k−1)`-words across the stage, so every block fully inside
   them has exact frequency `2^{−L}`; the one feedback-determined letter per word and the word
   boundaries are `O(L/k)` of the letters.  Initial segments: a run of `m` consecutive `n`
   decomposes into dyadic blocks of length `2^b` whose `n mod 2^b` cover all residues once, so the
   determined letters number `≤ 2m(k − log₂ m + 2)`, `o` of the prefix length `≥ (k−2)2^{k−1}`
   uniformly in `m`.  Champernowne with the within-stage order permuted; no Collatz input.  The §5
   remark "even `C = 1` is not automatic" was too pessimistic: the partial-stage problem is
   handled by the dyadic decomposition.
2. **`C ≥ 2`: normality ⟸ short-interval beyond-Terras mixing** (`ShortIntervalMixing C`: for every
   block `p`, the letters at positions `t ∈ [k, Ck]` of `n` in every initial segment of
   `[2^{k−1}, 2^k)` are jointly uniform with error `o(2^k)`, uniformly in `t` and the segment).
   The converse yields only the `t`-average.  Evidence for the hypothesis: §2.3 (`b_{j,t} ≈
   10^{−3}..10^{−2}` for `t ≤ j` at `j = 20`), and `b_j ≍ 2^{−j/2}` for the first letter.
   **Proved edge** (`biasDecays_of_shortIntervalMixing`, with `shortIntervalMixing_mono`):
   `ShortIntervalMixing C → BiasDecays` for every `C ≥ 2` - the bias over `[0, 2^K)` is the sum
   over dyadic stages of the letter-`K` imbalance, the stages `i > K/2` have that letter inside
   their beyond-range window `[i, 2i)`, and the stages `i ≤ K/2` hold at most `2^{K/2+1}`
   integers.  So C1 is the single-letter, full-stage shadow of the hypothesis behind the
   normality of `𝒞_2`: the conjecture graph now has the edge mixing ⇒ decay ⇔ 3-adic class
   equidistribution (`biasDecays_iff_classFluct`).
3. **A normality threshold at the stopping-time constant.**  For `C > C* := 2/(2 − log₂ 3) ≈
   4.82` (the Kontorovich-Lagarias total-stopping-time constant, `σ_∞(n) ≈ C* log₂ n` with
   `O(√log n)` fluctuations in the stochastic model), a density-one set of words contain the cycle
   tail `1010…` on a positive fraction of their letters, so the alternating block `(10)^{L/2}` has
   a density bounded below independently of `L` against the required `2^{−L}`, and `𝒞_C` is not
   normal (the agent's correction: a deficit of `11` alone could be compensated by in-flight
   letters, the alternating block cannot; the premise is frozen as `EarlyArrival C`, the
   implication `not_normal_of_earlyArrival` at 90%); for `C < C*` the beyond-range letters are in flight and (conjecturally)
   mixing.  Frozen: `ChampernowneNormalBelowThreshold` (`C ≤ 4`, 70%),
   `ChampernowneNotNormalAboveThreshold` (`C ≥ 5`, 80%, conditional on stopping-time concentration,
   itself open - Tao 2019 controls almost-bounded values in logarithmic density, not total stopping
   times).  So *the normality threshold of the Collatz-Champernowne family is the Collatz
   stopping-time constant*: a normal-numbers statement whose critical value is `2/(2 − log₂ 3)`.
4. **`𝒞_⋆`** (stop at 1): word of `n` = its letters until the orbit first reaches `1`.  The
   definition is total exactly when every `n ≥ 1` reaches `1` - a binary sequence whose
   well-definedness *is* the Collatz conjecture and whose normality (`ChampernowneStopNormal`, 65%)
   is the mixing conjecture; the forced approach `…, 8, 4, 2, 1` contributes `O(1)` letters per word.

Not in print (same search as §8; "Collatz Champernowne" has no hits in either Lagarias
bibliography).  The nearest objects are the Copeland-Erdős and Champernowne constants themselves
and the "concatenate `f(n)`" normality results (Nakai-Shiokawa for polynomials), none with a
feedback-defined word or a threshold.

**Numerics (`champ.py`, `champstage.py`; evidence with its limits).**  First `4·10^6` letters,
max relative block-frequency deviation at `L = 1..8` against the iid level `2.5·√(2^L/M)`:
`𝒞_1` sits at or below the iid level at every `L` (`f(11) = 0.2502`), no cycle-tail letters at
all; `𝒞_2`: `5-10×` the iid level (`f(11) = 0.2464`, tail letters `0.7%`); `𝒞_3, 𝒞_4, 𝒞_5, 𝒞_8`:
`f(11) = 0.235, 0.221, 0.203, 0.144` with cycle-tail fractions `5.8%, 13.8%, 22%, 43%` - the
threshold mechanism, visible as stated.  Per stage `k` (the `2^{k−1}` words of `k`-bit `n`,
beyond-range positions only): for `C = 2` the `L = 2` deviation falls `0.103, 0.089, 0.064,
0.056, 0.041, 0.039, 0.032, 0.026, 0.023, 0.016, 0.013` over `k = 10..20` (about `2^{−0.3k}`,
slower than the noise `2^{−k/2}`, so it is structure that *decays*), tracking the share of
orbits that reach `1` within `2k` steps (`14.5% → 2.5%`); the beyond-range single-letter bias is
`−0.002..−0.004` at `k = 20`.  For `C = 4` the share finishing inside the window is still `42%` at
`k = 18` (down from `55%` at `k = 10`, about `1.5` points per level) and `f(11) = 0.216`, so the
`C ≤ 4` side of the threshold converges only as the stopping-time distribution concentrates -
`O(1/√k)` relative width - and no finite computation at this size can separate `C = 4` from
`C = 5`.  The asymptotic claims rest on the stochastic model, not on these numbers.

**`𝒞_⋆` numerics (`champstop.py`, `4·10^6` letters, `n ≤ 58636`).**  Mean word length `4.74·size(n)`
(the stopping-time constant `C* = 4.82`, approached from below at this size).  Block deviations:
`L = 2: 0.026` (`f(00) = 0.2566`), `L = 4: 0.24`, `L = 8: 2.2` - far above iid, and accounted for
by the forced ending of every word: each orbit enters `1` through `8 → 4 → 2`, so every word ends
`1000` (via `5 → 8`) or `0000` (via `16 → 8`), a fixed 4-letter suffix once per `≈ 4.8k` letters;
that is a `1/k` effect (`≈ 1/75` per position here, matching the `0.24` at `L = 4`), vanishing but
slowly.  So the evidence for `ChampernowneStopNormal` is "consistent, with `O(1/log n)`
convergence dominated by the suffix", not "looks iid".

### 10.3b The sparse rung (`qsparse.py`, `M = 30000`)

Zero-density inputs of a different kind from the automatic and Sturmian ones of §2.4: the
characteristic words of the squares (`x = Σ 2^{n²}`, not automatic), of the powers of two
(`Σ 2^{2^n}`, 2-automatic and sparse), and of the primes (density `0.108` at this length).
`Q` and `Q^{−1}` of all three come out at the iid level (`L = 1..10` deviations `0.001 .. 0.74`
against the control's `0.007 .. 0.71`; ones-density `0.497-0.503`).  Two readings:

- **A single-orbit Collatz-Champernowne sequence.**  For `x = Σ 2^{n²}` the digits between
  consecutive ones are `0`, so the letters `w_j`, `n² < j < (n+1)²`, are the pure feedback bits of
  the *integer* `N_n = Σ_{k≤n} 2^{k²}`: `Q(x)` is the concatenation of the first `2n+1`
  beyond-Terras letters of the specific integers `N_n`, with no averaging over starts - and it
  looks normal.  For `Σ 2^{2^n}` the stretch between ones has length `2^n`, the full in-flight
  window `[k, 2k)` of a `(2^n + 1)`-bit integer: the `C = 2` Champernowne stretch for one integer
  per stage.  The §10.3 family averages over all `k`-bit integers; here the same statement is
  being asked of one orbit per stage, and the numerics do not object.
- **The Collatz number of the primes.**  `Q^{−1}(primes)` is the 2-adic integer whose Collatz
  parity word is the characteristic word of the primes (an irrational, by López-Stoll: density
  `0 < log 2/log 3`); its binary digits look normal.  `Q(primes)`, the parity word of
  `Σ_p 2^p`, likewise.

Frozen as `SquaresCollatzGeneric`, `PrimesCollatzGeneric`, `PrimesQinvNormal` (Ladder.lean,
C4c-d, 70%).  Rung added to the §5 table: *density zero (Liouville-type, primes)* → normal-looking,
both directions.

### 10.3c The parity walk and orbit coalescence (`walk.py`, `autocorr.py`, `coalesce.py`)

By the aligned-window theorem the sign sum over any shifted window `[s, s + 2^j)` is `E_j − 2P_j(s)`
with `P_j(s) := Σ_{r<s} (−1)^{T^j r}` - so the natural object behind every "initial segment"
statement is the **walk** `s ↦ P_j(s)` on `[0, 2^j]`, endpoint `E_j`.  It is not Brownian.  At
`j = 28` the increment variance per unit length over blocks of length `2^i` is `8.8` (`i = 6`),
`26.9` (`i = 10`), `38.5` (`i = 14 ≈ j/2`), then `16.3, 12.0, 3.5, 3.0, 1.2` (`i = 18..26`), with
lag-one block autocorrelation `+0.37` at small scales and `−0.59` at `i = 24`; the walk is positive
for `99.8-100%` of `s`, with a single hump (max `≈ 1.2·E_j` at `s/2^j ≈ 0.33-0.56`).  So the letter
signs of nearby starts are strongly *positively* correlated out to scale `≈ 2^{j/2}` and
anticorrelated beyond (the exact `R_j(2^j) = −1` is the extreme case).

**Autocorrelation.**  `R_j(d) := 2^{−(j+1)} Σ_r g_j(r) g_j(r+d)`, `g_j = (−1)^{T^j ·}` on `ℤ/2^{j+1}`:
`R_20(1..8) = +0.384, +0.254, +0.137, +0.168, +0.152, +0.097, +0.080, +0.109`, `R(2^i) ≈ 0.38·0.65^i`
for `i ≤ 7` (a power law `≈ d^{−0.6}`), slowly *increasing* with `j` at fixed `d` (`R_16(1) =
0.360`, `R_20(1) = 0.384`).  Consecutive `j`-bit starts have the same first beyond-Terras letter
`69%` of the time.

**Mechanism: orbit coalescence, exactly.**  Let `coal_j(d)` be the fraction of `r < 2^j` whose
orbit has *merged* with that of `r + d` by step `j` (`T^k r = T^k (r+d)` for some `k ≤ j`; the
classical example is `r ≡ 4 (mod 8)`, which merges with `r+1` at `k = 3`).  Merged pairs have equal
letters forever, so `R_j(d) = coal_j(d) + (1 − coal_j(d))·R^{nc}_j(d)` with `R^{nc}` the
correlation among the non-merged pairs - and the data at `j = 20` give `R^{nc}_j(d) = −0.03 .. −0.01`
for every `d ≤ 256`: **the correlation of beyond-Terras letters across starts is the coalescence
density, with the non-merged pairs essentially uncorrelated** (`coal_20(d) = 0.402, 0.280, 0.167,
0.198, 0.182, 0.129, 0.110, 0.140` for `d = 1..8`; `0.063, 0.039, 0.013, 0.003` for `d = 32, 64,
256, 1024`).  The power law in `d` is the coalescence probability of two orbits started `d`
apart; the anticorrelation at large scales is the lift identity (`d = 2^j` flips the letter).
Coalescence of consecutive integers is classical (Garner 1985 on equal heights of `n` and `n+1`;
the density value here, `0.40` within 20 steps, is to be checked against that literature), the
identification with the letter autocorrelation is not in print to my knowledge, and the small
negative `R^{nc}` is a new, unexplained number.  Lean: `Coalescence.lean` (§10.5).

What it does to the ladder: nothing for the mean (merged pairs double the variance, not the
bias), but it fixes the *second* moment: the walk's variance profile is the integrated coalescence
density, so "short-interval" statements (`ShortIntervalMixing`, the Champernowne family) live on a
walk with long-range positive dependence of a known origin, and the `2^{j/2}` scale at which the
block variance peaks is where coalescence gives way to the lift-identity anticorrelation.

### 10.4 The sign, recalibrated (`ar1.py`)

The mod-3 recursion `E_m = 2E_{m−1} − 2G_{m−1}(c_m)`, with `G_{m−1}(c_m) = E_{m−1}/3 + ξ_m`, reads
in normalised units `b̃_m = E_m/2^{m/2}` as

    b̃_m = ρ₀ b̃_{m−1} + η_m,    ρ₀ = (4/3)/√2 = 0.943,    η_m = −2ξ_m/2^{m/2}.

So the normalised bias is an AR(1) process with memory `1/(1−ρ₀) ≈ 17` levels, for *every* map in
the family; the `(4/3)^m` mode is its homogeneous solution and adds no innovation.  Fitted on
`j = 10..31`: innovations `η` have mean `+0.14`, sd `0.33` (the through-origin regression gives
`ρ̂ = 0.99-1.01`, consistent with `ρ₀` plus drift).  A stationary Gaussian AR(1) with `ρ₀` crosses
zero `arccos(ρ₀)/π = 0.108` times per level; simulating the zero-mean null from the observed
`b̃_9 = 1.33` gives **`P(all 22 values j = 10..31 positive) = 0.40`** and `P(run mean ≥ observed
1.41) = 0.13`.

Consequences.  (i) `BiasPositive` has, at this depth, no evidential support beyond the
recursion's memory and a positive start: confidence down from 60% to **35%**.  (ii) The sibling
sign flips (§7, §10.2) are exactly what `ρ₀ = 0.943` predicts (one crossing per ~9 levels).  (iii)
`BiasSqrtLaw` is what the null predicts (stationary `b̃`), so it stays at 60%, and the `j^{1/4}`
refinement is disfavoured.  (iv) The one residual signal is the innovation drift `+0.14 ± 0.33`
per level (`t ≈ 2.0` over 22 roughly independent innovations): a genuine arithmetic bias would be
"the class-`c_m` mass `G_{m−1}(c_m)` sits *below* `E_{m−1}/3` by about `0.07·2^{(m−1)/2}` on
average", a statement about the 3-adic class split of the signs, not about the parity sum itself.
Under drift the stationary mean of `b̃` is `0.14/(1−ρ₀) ≈ 2.5`; under the null `b̃` relaxes toward
`0`.  The `j = 32..38` run (§10.5) is the discriminator: `b̃_38 ≳ 2.2` favours drift, `≲ 1.2`
favours the null, and a negative value refutes `BiasPositive` outright.

**The whole family (`ar1sib.py`, `drift.py`).**  For `T(n) = n/2 | (qn + c)/2` the odd branch
lands in one residue class mod `q` of `[0, q·2^{m−1})`, the `q` blocks of length `2^{m−1}` carry
signs `(−1)^k` by the lift identity, and under the uniform-class null `E_m = (1 + 1/q)E_{m−1} +
innovation`, so `ρ₀(q) = (1 + 1/q)/√2`: `0.943, 0.849, 0.808` for `q = 3, 5, 7`, memories `17,
6.6, 5.2` levels.  Fitted on `j = 11..24`: `ρ̂ = 1.04, 1.02, 0.99, 1.04` for `3x+1, 3x+5, 3x+7,
3x−1` (0, 3, 2, 0 sign flips), `0.34, 0.76` for `5x+1, 5x+3` (3, 4 flips), `0.70, 0.56` for `7x+1,
7x+3` (6, 3 flips): the memory ordering is as predicted, and the `q = 3` fits sit above `ρ₀`
because of the trend.  Every non-mirror map has a positive innovation mean over this window
(`+0.04 .. +0.18`; `3x−1` the mirror value `−0.18`), each individually weak; a 16-map run to
`j = 26` is in §10.5.  If that drift is real it is a *family* property (the classes receiving the
`−` sign carry less than their share of the signed mass), not a `3x+1` fact.

**What this does to the ladder.**  Nothing: the crux (§6) was never the sign but the decay
`b_j → 0`, i.e. `|η|` summable against `ρ₀^m`, and the AR(1) reading makes the decay statement
precise: `BiasDecays` ⟺ the class-mass fluctuations `ξ_m = G_{m−1}(c_m) − E_{m−1}/3` are
`o(2^{m−1})`, i.e. **the signs are equidistributed across the three residue classes of the start
mod 3 at the scale of the level** - the first non-trivial 3-adic equidistribution statement, and
the honest target for a proof (a `3x+1`-specific sign result is not on the table until the drift
is established).

### 10.5 Results that arrived late (`bige_rs`, `drift.py`), and the Lean status

**`E_j` to `j = 38`** (Rust, 16 threads, `u64`, 10 min for `j = 38`; `j = 39, 40` in `u128` were
running at the time of writing - `experiments/conjugacy/bias_rust_j32_38.out`, `bias_rust_j39_40.out`):

| `j` | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 |
|---|---|---|---|---|---|---|---|---|
| `E_j` | 83458 | 77334 | 83582 | 99598 | 116298 | 180842 | 216810 | 332758 |
| `E_j/2^{j/2}` | 1.80 | 1.18 | 0.90 | 0.76 | 0.63 | 0.69 | 0.585 | 0.635 |
| `E_j mod 4` | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| bands `+/−` | | 24/5 | 19/11 | 20/11 | 18/14 | 22/11 | 24/10 | 23/12 |

The normalised bias falls from `1.80` to `0.585` over six levels (then `0.635` at `j = 38`) - the relaxation
toward `0` that the zero-mean null of §10.4 predicts (`1.80·0.943^6 = 1.27`; the observed fall is
faster, innovations `−0.52, −0.21, −0.09, −0.09, +0.10, −0.07`).  **The `+0.14` innovation drift
of §10.4 was a fluctuation**: over `j = 10..37` the mean innovation is `≈ +0.08` (`t ≈ 1.2`), and
under drift `b̃` would have risen toward `2.5`.  `BiasPositive` survives to `j = 37` (`E_j ≡ 2
(mod 4)` throughout, as proved), but with `b̃_37 = 0.585` and innovation sd `0.33` a sign change
within the next ten levels is now the likelier outcome: confidence **25%**.  The within-level band
coherence weakens with it (`+0.33..+0.44` mean, `18/14` at `j = 35`).  `BiasSqrtLaw` (stationary
`b̃`) is what the data now look like: 60% → **70%**.

**Family drift (`drift.py`, 16 maps `qx+c`, `j = 11..26`).**  Innovation means `η̄ ∈ [−0.20,
+0.16]`, positive for 13 of 16, mean of means `+0.044 ± 0.090`, `t = 1.97` - borderline on its own
and contradicted by `3x+1`'s own reversal at `j = 32..37`.  Verdict: no established drift in the
family; the AR(1) null with `ρ₀(q) = (1 + 1/q)/√2` is the working model, and the open statement
is `BiasDecays`, equivalently `biasDecays_iff_classFluct` (the class-`c_m` signed mass is
asymptotically one third of the total).

**Lean status (commit after this note).**  `Conjugacy/Ladder.lean` (first half) + four new modules,
all wired into the root build (`lake build CollatzMoonshot` green): `Recursion.lean` (all proved:
`bias_succ`, `bias_mod_four`, `bias_ne_zero`, `depth_count`, `depth_antisymm`, `bias_window`,
`bias_eq_two_mul_card_sub`, `biasDecays_iff_classFluct`, `biasDecays_of_weakDecayOnZ3`; node `WeakDecayOnZ3`
= C1⁺, decay at every 3-adic scale, 80%), `Bands.lean` (all proved: `card_band`,
`biasBand_zero/top/one`, `sum_biasBand`, `biasBand_succ_succ_inherit`; frozen `BandCoherence` 60%,
`BiasQuarterPowerLaw` 25%), `Digits.lean` (all proved: `corr_diag`, `corr_off`,
`bias_eq_one_add_digitSum`, Terras bijection `onesSet_injOn`/`onesSet_surjOn`),
`Champernowne.lean` (`concat_apply`, `collatzChampernowne_apply`, `threshold_bounds`,
`biasDecays_of_shortIntervalMixing`, `shortIntervalMixing_mono` proved; three
believed theorems with `sorry`: `collatzChampernowne_one_normal` 85%, `normal_of_shortIntervalMixing`
75%, `not_normal_of_earlyArrival` 90%; nodes `ShortIntervalMixing`, `EarlyArrival`,
`ChampernowneNormalBelowThreshold` 70%, `ChampernowneNotNormalAboveThreshold` 80%,
`ChampernowneStopNormal` 65%), `Bridges.lean` (all proved: `not_shortIntervalMixing_of_earlyArrival`
for every `C`, via the `1010…` tail lemma `accWord_of_reaches_one` and the count `2^L − 2` of
non-alternating blocks; `earlyArrival_mono`).  So the threshold picture is a graph: `EarlyArrival C`
⇒ `¬ ShortIntervalMixing C` (proved) and ⇒ `¬ Normal 𝒞_C` (believed, 90%); `ShortIntervalMixing C`
⇒ `Normal 𝒞_C` (believed, 75%) and ⇒ `BiasDecays` (proved, `C ≥ 2`).  Ladder.lean gained `SquaresCollatzGeneric`, `PrimesCollatzGeneric`,
`PrimesQinvNormal` (70%) and the recalibrated confidences (`BiasPositive` 25%, `BiasSqrtLaw` 70%).
Every proved theorem is on `[propext, Classical.choice, Quot.sound]` per the agents' `#print axioms`
(verified 2026-10-21); no `native_decide` in the Conjugacy modules.

**What is new tonight, in one list**: the beyond-Terras bias `E_j` and its exact structure (lift
identity, residue reading, mod-3 recursion, `E_j ≡ 2 (mod 4)`, aligned-window invariance, Terras at
depth `j`, the digit form, the band decomposition with its exact small bands and inheritance
recursion, the AR(1) reading with `ρ₀(q)`); the conjugacy complexity ladder with `Q` scrambling
every zero-entropy input tried; the Collatz-Champernowne family with its conjectured normality
threshold at `2/(2 − log₂ 3)`; and the recalibration that the sign of `E_j` is memory, not
arithmetic, at the depth reachable tonight.
