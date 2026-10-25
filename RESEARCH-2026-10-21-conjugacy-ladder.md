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
Coalescence of consecutive integers is classical: Garner 1985 (*On heights in the Collatz 3n+1
problem*, Discrete Math. 55, 57-64; citation verified via OEIS A078417/A006666) gave a sufficient
condition in terms of parity vectors for `n`, `n+1` to have equal height and conjectured it
necessary; Elia-Tucker 2015 (Integers 15, arXiv:1511.09141, abstract read) give an infinite family
of counterexamples to the necessity; Gao 1993 (Discrete Math. 112) is the other reference.  No
density statement was found in what I could open tonight, so the value `coal_20(1) = 0.40` (merging
within 20 steps) stands as a measurement to be compared with Garner's paper itself.  The
identification with the letter autocorrelation is not in print to my knowledge, and the small
negative `R^{nc}` is a new number.  Lean: `Coalescence.lean` (§10.5).

**Anatomy of `R^{nc}` (`mergenext.py`, `j = 20`, `d = 1, 2, 4, 16`).**  Split the non-merged pairs by
the step at which they merge later.  Pairs merging at exactly `j+1` have sign product **`−1.000`**
- a theorem: two distinct starts with the same image have opposite parities (`y/2 = (3y'+1)/2`
forces `y` even, `y'` odd).  Pairs merging at `j+2` have product `+0.998` (the relation
`T(y) = 3T(y') + 1` with `T(y)` even allows `(y, y') = (3y'+2, y')` both even or `(9y'+5, y')` with
`y'` odd; the ratio-9 case is rare), at `j+3`: `+0.10..+0.16`, `j+4`: `−0.13..−0.21`, `j+5`:
`−0.07..−0.10`, later: `≈ −0.01`.  These classes are each `0.3-0.6%` of pairs and roughly cancel;
the pairs that have not merged by `j + 40` (`52-76%` of all pairs) carry `−0.031 .. −0.041`
themselves.  So the negative remainder is a property of in-flight orbits that stay apart, not a
boundary or about-to-merge effect; open (a selection effect of non-merging on the odd-step counts
is the natural guess).  Asymptotically every pair either merges or reaches the cycle in opposite
phase (product `−1` forever), so for fixed `r` the pair correlation is eventually `±1`; the
average over `r < 2^j` stays in flight.  **Eventual fates (`coalfinal.py`, `r ≤ 2^22`, 400
steps, none undecided):** consecutive pairs merge before either reaches the cycle `48.95%` of the
time, arrive in phase `25.2%`, in antiphase `25.8%` (fixed-start limit correlation `+0.48`); for
`d = 2, 3, 4`: merge `0.39, 0.30, 0.33`, with the non-merged half split evenly.  So about half of
all consecutive integers share their orbit before reaching `1`.  The within-`j` fraction
`coal_j(1)` climbs `0.344, 0.361, 0.375, 0.385, 0.394, 0.402, 0.409` for `j = 10, 12, …, 22`,
toward the eventual value.

**The parity recursion at even distance (`coalrec.py`, ~04:00).**  For an even gap `2d` the first
step splits the pair by the parity of the start: `(2r, 2r+2d) ↦ (r, r+d)` and
`(2r+1, 2r+1+2d) ↦ (3r+2, 3r+2+3d)`, so exactly

    coal_j(2d) = ½·coal_{j−1}(d) + ½·coal^{odd}_{j−1}(3d),

where `coal^{odd}_{j−1}(3d)` counts merges within `j−1` steps over the odd-image starts `3r+2`,
`r < 2^{j−1}` (the even half is `coalesces_two_mul` run backwards, the odd half the same peel;
Lean in `Coalescence.lean`, status §10.5).  The content is numerical: **the odd-image starts
coalesce at the uniform rate.**  At `j = 20`, `coal^{odd}_{19}(3) = 0.1609 = coal_{19}(3)`, and
likewise `0.1221/0.1221`, `0.0967/0.0967`, `0.0878/0.0878` for `3d = 6, 9, 12`; the gap is
`≤ 0.0008` at `j = 14` and below `0.0001` at `j = 20`.  So the closed recursion
`coal_j(2d) ≈ (coal_{j−1}(d) + coal_{j−1}(3d))/2` holds to four decimals (`coal_20(2) = 0.2796`,
`coal_20(4) = 0.1982`, `coal_20(6) = 0.1288`, `coal_20(8) = 0.1397`, each reproduced), and the
whole even-distance profile is a parity mixture of the odd-distance profile: `coal(2) = ½(coal(1)
+ coal(3))`, `coal(4) = ½(coal(2) + coal(6))`, and so on.  The odd distances, `d = 1` first, are
the irreducible base case: for odd `d` the two starts have opposite parity, one halves and one
triples, and the gap after one step depends on `r`, so no closed recursion of this shape exists.
Directly, `coal_19(1) = 0.3984`, and `(0.3984 + 0.1609)/2 = 0.2796 = coal_20(2)` closes the `d = 1 → 2` step
exactly to four decimals.

**Why the odd-image rate is uniform (`mergeodd.py`, ~04:05).**  By the iterate identity
`2^k·T^k s = 3^a·s + numer(v)` (`tstep_iterate_identity`; `a = ones v`, `v` the parity trace of
`s` over `k` steps, a function of `s mod 2^k`), a merge `T^k s = T^k(s+D)` at a step with **equal
odd-step counts** `a = a'` is the condition `numer(v) − numer(v') = 3^a·D` on the two traces
alone, hence a property of `s mod 2^k`; with `a ≠ a'` it is a linear equation in `s` with at most
one solution per pair of traces.  Measured at `j = 20`, every in-window merge has `a = a'` except
`2-3·10^{−5}` of starts (`D = 1`: none to four decimals; `D = 2, 3, 4, 6, 9, 12`: `0.0001-0.0003`
of merges).  So `coal_j(D)` is, up to that coincidence term, a function of the residue `s mod 2^j`,
and every complete residue system gives the same density - the odd-image set `3r+2`, `r < 2^{j−1}`,
is one mod `2^{j−1}` because `3` is a unit.  That is the four-decimal agreement above, and the
`≤ 10^{−4}` gap is the coincidence term.  Lean: `GenericCoalesces` (merging with equal odd
counts) and its `2^j`-periodicity, status §10.5.

**The generic density is monotone in the window (~04:15).**  Because a generic merge at step `k`
is a cylinder condition on `s mod 2^k`, every merging residue class mod `2^j` lifts to the two
classes `s, s + 2^j` mod `2^{j+1}`, so `2·genericCoalCount_j(D) ≤ genericCoalCount_{j+1}(D)`: the
generic density `coal^gen_j(D)` is nondecreasing in `j`, bounded by `1`, and **converges** - its
limit `L(D)` is the Haar measure of the 2-adic open set of starts that merge generically with
`s + D`.  That is the climb `0.344 → 0.409` of `coal_j(1)` over `j = 10..22` seen above (the
measured `coal_j` and the generic count differ by the `10^{−5}` coincidence term).  What the
theorem does not say: the value of `L(1)`.  The eventual-fate measurement (`coalfinal.py`,
`48.95%` of `r ≤ 2^22` merge at *some* step before the cycle) counts merges beyond the window too,
and orbits of `s ≈ 2^j` take about `j` shortcut steps to reach `1`, so the window genuinely
truncates; `0.409 ≤ L(1)` at `j = 22`, and `L(1) ≤ 0.49` is expected, not proved.  Lean:
`two_mul_genericCoalCount_le`, `genericCoalDensity_tendsto` (status §10.5).

**Which constant is `L(1)`?  Not the eventual merge density (`mergetime.py`, ~04:20).**  The
merge-time profile of consecutive pairs `(s, s+1)`, `s < 2^j`, first step `k` with
`T^k s = T^k(s+1)`, in units of `j`:

| `j` | window `coal_j(1)` (`k ≤ j`) | pre-cycle merge, any `k` | late mass (`k > j`) | in-phase cycle arrival | antiphase forever |
|---|---|---|---|---|---|
| 12 | 0.3613 | 0.3965 | 0.035 | 0.3059 | 0.2976 |
| 14 | 0.3745 | 0.4233 | 0.049 | 0.2893 | 0.2874 |
| 16 | 0.3853 | 0.4452 | 0.060 | 0.2773 | 0.2775 |
| 18 | 0.3943 | 0.4631 | 0.069 | 0.2655 | 0.2714 |
| 20 | 0.4021 | 0.4777 | 0.076 | 0.2577 | 0.2646 |
| 22 | 0.4090 | 0.4895 | 0.081 | 0.2524 | 0.2581 |

In-phase arrival at the cycle happens at `k ≈ 5.4j` (mean `k/j = 5.3-5.5` at every `j`), outside
every window, so the window limit never sees it.  The pre-cycle merges beyond the window are not a
vanishing boundary effect: their mass *grows* with `j` (`0.035 → 0.081`, increments shrinking
`0.012, 0.011, 0.009, 0.007, 0.005`), the mean merge time `k/j` drifts up (`0.52 → 0.58`), and the
`(2j, 3j]` bin alone grows `0.002 → 0.022`.  So the limit `L(1)` of `genericCoalDensity_tendsto`
and the eventual pre-cycle merge density `E(1)` are apparently two different constants: a
geometric extrapolation of the increments gives `L(1) ≈ 0.45` and `E(1) ≈ 0.54` (40%; the
increments decay slowly and the extrapolation is crude).  Both the in-phase and the antiphase
fractions fall with `j` (`0.306 → 0.252`, `0.298 → 0.258`, decrements `≈ 0.005-0.010` per two
levels and shrinking), so whether *almost all* consecutive integers share their orbit before
reaching `1` (`E(1) = 1`) or a positive fraction stays apart is open on this evidence; the data
favour a positive antiphase limit but not strongly.  Known or new?  Garner 1985 and Gao 1993
concern consecutive integers of equal height, which is the in-phase-or-merged event, not the
window density; I did not find the three-way fate split or the window/eventual distinction in
what I could open tonight.  Lean (~04:25): `EventuallyMerges s D := ∃ k, T^k s = T^k(s+D)`; the
parity recursion lifts verbatim (`eventuallyMerges_two_mul_iff`, `eventuallyMerges_odd_iff`), the
window count is bounded by the eventual count (`coalCount_le_eventualMergeCount`, a classical
filter since eventual merging is an unbounded search), and three frozen nodes carry the numbers:
`EventualMergeDensityConverges` 80%, `WindowLimitLtEventual` 90%, `ConsecutiveAntiphasePositive`
55% (status §10.5).

**Where the late merges happen (`latevalue.py`, ~04:26): in the descent, at height `≈ s^{0.55}`.**
Record the merge value `m = T^k s` at the first merge.  Merges inside the window (`k ≤ j`) happen
at `log₂ m / j` with median `0.83-0.88` (percentiles `10/50/90`: `0.72 / 0.88 / 0.96` at `j = 20`),
the orbit's typical height during the window (`T^j s ≈ 2^{0.79j}` since each shortcut step
multiplies by `3/2` or `1/2`, mean `log₂` factor `−0.2075`).  The late merges (`k > j`) happen at
median `log₂ m / j ≈ 0.55` (`0.28 / 0.53 / 0.74` at `j = 20`), `38-43%` of them below `2^{j/2}`,
with a profile that is stable in units of `j` across `j = 14..20`.  Reading: an integer `s < 2^j`
is the 2-adic number `s` followed by zeros, so its orbit beyond step `j` is the orbit of the
*small* integer `T^j s` descending to `1` over the next `≈ 4j` steps, and the pair keeps a chance
to merge all the way down; a generic 2-adic start never descends, and the window limit
`L = μ(U)` of `genericCoalDensity_tendsto` is exactly the generic-start merge measure.  That is
the mechanism of `WindowLimitLtEventual` (80%): the gap `E − L` is the descent's share of the
merging, invisible to every finite window because the window is measured at the start's own
scale.

What it does to the ladder: nothing for the mean (merged pairs double the variance, not the
bias), but it fixes the *second* moment: the walk's variance profile is the integrated coalescence
density, so "short-interval" statements (`ShortIntervalMixing`, the Champernowne family) live on a
walk with long-range positive dependence of a known origin, and the `2^{j/2}` scale at which the
block variance peaks is where coalescence gives way to the lift-identity anticorrelation.

### 10.3d The Walsh spectrum of the beyond-Terras letter: the √-law at every cylinder depth (`walsh.py`, ~04:28)

Read the beyond-Terras letter `g_j(r) = (−1)^{T^j r}` as a function of the parity word
`v = (v_1, …, v_j)` of `r` (Terras), and expand it in the Walsh basis: `ĝ(S)` = correlation of
the next letter with the XOR of the letters in `S ⊆ {1..j}`; `ĝ(∅) = E_j/2^j`; Parseval
`Σ ĝ(S)² = 1`.  Two findings at `j = 12, 16, 20`:

- **The reach is geometric, exactly.**  The energy on sets whose most recent letter is `m`
  letters back is `2^{−(m+1)}`: `0.500, 0.249, 0.125, 0.061, 0.037, 0.010, 0.007, 0.005, …`
  (`j = 20`, from position `j` backwards), identical at `j = 16` and `j = 12` to two decimals.
  Cumulatively, the energy within the last `1, 2, 3, 4, 6, 8` letters is
  `0.500, 0.749, 0.874, 0.935, 0.982, 0.994` against the fair-coin `1 − 2^{−m}` =
  `0.5, 0.75, 0.875, 0.9375, 0.984, 0.996`.
- **The degree is high.**  The energy sits at degree `6-10` and beyond (`j = 20`: degree `≤ 8`
  carries `31%`, the rest is higher); the next letter is a high-degree function of the word, with
  no single small set of letters explaining it (largest `|ĝ(S)|` is `0.013` at `j = 20`).

What the first finding says: by Parseval on the cylinder filtration, the energy on sets with
`max S ≤ j − m` is the mean square of the conditional bias of the next letter given the first
`j − m` letters, i.e. `2^{−(j+m)} Σ_{c mod 2^{j−m}} (Σ_{r ≡ c} g_j(r))²` - the normalised variance
of the sum of the `2^m` beyond-Terras letters in a cylinder (an arithmetic progression of step
`2^{j−m}`).  The law `= 2^{−m}` says **the beyond-Terras letters in a cylinder sum like fair
coins**, so the `√`-law `E_j ≈ 2^{j/2}` (`BiasSqrtLaw`, the `m = j` case: `(E_j/2^j)² = 9.8·10^{−7}`
vs `2^{−20} = 9.5·10^{−7}` at `j = 20`) holds at *every* cylinder depth.  The ratio to the
fair-coin value, computed directly (`rhocheck.py`, `j = 20`), is `ρ_j(m) = 1.000, 1.004, 1.006,
1.040, 0.886, 1.160, 1.410, 1.562` at `m = 1..8` - unity within sampling noise (`≈ 0.003`) at the
three largest scales, then *not* monotone: the exact identity
`ρ_j(m) = 1 + 2 Σ_{i<2^m} A_j(i·2^{j−m})` (expand the square; `A_j(d)` the window autocorrelation
at lag `d`, checked to four decimals at every `m`) reads the dyadic autocorrelation
`A_20(2^{19}, …, 2^{12}) = +0.0000, +0.0009, +0.0010, +0.0067, −0.0343, +0.0544, +0.0109, −0.0280`,
which is zero at the top scales and *sign-alternating* from spacing `2^{15}` down, the block
anticorrelation of the walk (§10.3c) seen letter by letter.  So the Walsh spectrum in the
parity-word basis is the autocorrelation function read at dyadic spacings, and the geometric
reach is its vanishing at the three largest scales.  Conjecture (`CylinderFairCoin`, not yet in
Lean, 75%): `ρ_j(m) → 1` for each fixed `m ≤ 3`, i.e. the window autocorrelation at spacings
`2^{j−1}, 2^{j−2}, 2^{j−3}` vanishes as `j → ∞`; what happens at `m ≈ j/4..j/2` is the walk's
block structure and is not conjectured here.  The Parseval identity behind the reading is
standard harmonic analysis on `(ℤ/2)^j` and is a candidate for `Digits.lean` when wanted.

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

**`E_j` to `j = 40`** (Rust, 16 threads; `u64` to `j = 38`, 10 min for 38; `u128` for `j = 39, 40`, 37 and 70
min - `experiments/conjugacy/bias_rust_j32_38.out`, `bias_rust_j39_40.out`):

| `j` | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|
| `E_j` | 83458 | 77334 | 83582 | 99598 | 116298 | 180842 | 216810 | 332758 | 590942 | 686434 |
| `E_j/2^{j/2}` | 1.80 | 1.18 | 0.90 | 0.76 | 0.63 | 0.69 | 0.585 | 0.635 | 0.797 | 0.655 |
| `E_j mod 4` | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| bands `+/−` | | 24/5 | 19/11 | 20/11 | 18/14 | 22/11 | 24/10 | 23/12 | 24/12 | 27/10 |

The normalised bias falls from `1.80` to `0.585` over six levels (then `0.635`, `0.797`, `0.655` at `j = 38, 39, 40`: innovations `+0.04`, `+0.20`, `−0.10` - wandering, as the null says) - the relaxation
toward `0` that the zero-mean null of §10.4 predicts (`1.80·0.943^6 = 1.27`; the observed fall is
faster, innovations `−0.52, −0.21, −0.09, −0.09, +0.10, −0.07`).  **The `+0.14` innovation drift
of §10.4 was a fluctuation**: over `j = 10..37` the mean innovation is `≈ +0.08` (`t ≈ 1.2`), and
under drift `b̃` would have risen toward `2.5`.  `BiasPositive` survives to `j = 40` (`E_j ≡ 2
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
`ChampernowneStopNormal` 65%), `Coalescence.lean` (all proved: `letterCorr_eq` and the refined
`letterCorr_eq_refined` - the autocorrelation of the beyond-Terras letter is the coalescence count
minus the merge-next count plus the still-apart remainder; `coalesces_four_mod_eight`,
`coalCount_one_ge` (`2^j/8 ≤ coalCount j 1`), `coalescenceDensityPositive_one`,
`mod_two_ne_of_tstep_eq`; the parity recursion at even distance `coalCount_succ_two_mul`
(`coalCount (j+1) (2d) = coalCount j d + oddImageCoalCount j (3d)`, exact, via
`coalesces_two_mul_iff` and `coalesces_odd_iff`), the inequality
`coalCount_le_coalCount_succ_two_mul`, and `decide` teeth at `j = 4, 5`; equal-odd-count merging
`GenericCoalesces` is `2^j`-periodic in the start (`genericCoalesces_add_pow_two_mul_iff`,
`genericCoalesces_iff_mod`, via the cylinder offset `tstep_iterate_pow_two_offset`), so the
odd-image starts `3r+2` see exactly the uniform count (`oddImage_genericCoalCount`, the bijection
`r ↦ (3r+2) mod 2^j`); teeth `genericCoalCount = coalCount` at `j ≤ 5`; the generic density is
monotone in the window and converges (`two_mul_genericCoalCount_le`, `genericCoalDensity_mono`,
`genericCoalDensity_le_one`, **`genericCoalDensity_tendsto`**: `∃ L ≤ 1`, the Haar measure of a
2-adic open set); eventual merging `EventuallyMerges` with the parity recursion lifted
(`eventuallyMerges_two_mul_iff`, `eventuallyMerges_odd_iff`), `eventuallyMerges_four_mod_eight`,
`coalCount_le_eventualMergeCount`, `eventualMergeDensity`; frozen `EventualMergeDensityConverges`
80%, `WindowLimitLtEventual` 90%, `ConsecutiveAntiphasePositive` 55%, and the earlier
`NonCoalescedDecorrelated` 65% ⇔ `LetterCorrIsCoalescence`,
`CoalescenceDensityPositive` 90%), `Bridges.lean` (all proved: `not_shortIntervalMixing_of_earlyArrival`
for every `C`, via the `1010…` tail lemma `accWord_of_reaches_one` and the count `2^L − 2` of
non-alternating blocks; `earlyArrival_mono`).  So the threshold picture is a graph: `EarlyArrival C`
⇒ `¬ ShortIntervalMixing C` (proved) and ⇒ `¬ Normal 𝒞_C` (believed, 90%); `ShortIntervalMixing C`
⇒ `Normal 𝒞_C` (believed, 75%) and ⇒ `BiasDecays` (proved, `C ≥ 2`).  Ladder.lean gained `SquaresCollatzGeneric`, `PrimesCollatzGeneric`,
`PrimesQinvNormal` (70%) and the recalibrated confidences (`BiasPositive` 25%, `BiasSqrtLaw` 70%).
Every proved theorem is on `[propext, Classical.choice, Quot.sound]` per the agents' `#print axioms`
(verified 2026-10-21; the parity-recursion and periodicity theorems re-verified by my own
`lake env lean` `#print axioms` runs at ~04:05, ~04:13, ~04:18 and ~04:25); no `native_decide` in the Conjugacy modules.

### 10.6 Against Tao 2019: no bridge, an exact mirror, and why the method does not transfer (~07:15)

**The question.**  Does Tao's fine-scale mixing (Prop 1.14, proved in Lean as `fine_scale_mixing` in
`gotrevor/tao-collatz`, read from `origin/main` at `95a7172`) give `WeakDecayOnZ3` or `BiasDecays`?
**No, not by a lemma** (90%).  Tao bounds `osc m n (syracZ n)`: the unweighted law of a 3-adic
random variable, the Syracuse offset `X_n = Σ_{k=1}^n 3^{k−1} 2^{−T_k}` in `ℤ/3^n`, with `T_k` the
partial sums of iid `Geom(2)`.  Our conjectures are *signed* statements: residue classes of the
start mod `3^k` (`WeakDecayOnZ3`) or the whole window (`BiasDecays`), weighted by the
beyond-Terras sign `(−1)^{T^j r}`.  Tao's law says nothing about that weight.  The earlier 30% for
a bridge is withdrawn; 5%.

**The exact mirror.**  The digit form (`bias_eq_one_add_digitSum`, Digits.lean) reads the bias off
`Y = N_u/3^a = Σ_{i=1}^a 3^{−i} 2^{t_i}` in `ℤ₂`, with `t_1 < … < t_a` the odd-step times of a
uniform `j`-letter word.  Those gaps are iid `Geom(2)` too.  So `Y` is Tao's `X` with the primes
swapped and the exponents inverted: the same random input, read 2-adically.  Terras is the mirror's
exact half: `Y mod 2^j` is uniform (verified, a bijection at every `j ≤ 22`, `mirror.py`), and
`BiasDecays` is the balance of digit `j` (the digit form reproduces `E_j` at every `j ≤ 22`).  On the
3-adic side nothing is exact (`Syrac(ℤ/3)` puts mass `2/3, 1/3` on `2, 1`), and Tao proves
approximate uniformity at fine scales instead.

**The mirror recursion (exact; numerics to `10^{−16}`, `recur.py`; proof is the two-line parity
split).**  Let `G_j(ξ) = 2^{−(j+1)} Σ_{r mod 2^{j+1}} g_j(r) e(ξr/2^{j+1})`, the Fourier transform of
the beyond-Terras sign.  It lives on odd `ξ` (`g_j` is `2^j`-antiperiodic).  From `g_j(2s) =
g_{j−1}(s)` and `g_j(2s+1) = g_{j−1}(3s+2)`, with `u = 3^{−1} mod 2^{j+1}`,

    G_j(ξ) = ½ [ G_{j−1}(ξ) + e(ξ(1−4u)/2^{j+1}) · G_{j−1}(uξ) ].

This is the 2-adic twin of Tao's Lemma 1.12 recursion (`syracZ_recursion` in the repo), with one
difference that decides everything: Tao's step multiplies frequencies by the *random* `2^{−a}`,
`a ~ Geom(2)`, which spreads them; ours multiplies by the *deterministic* `3^{−1}`.  For `ξ = 3^k`
the phase is `e(−3^{k−1}/2^{j+1}) ≈ 1` and `uξ = 3^{k−1}` exactly, so the powers of 3 form a
**coherent chain**.

**Consequence: the literal mirror of Tao's Prop 1.17 is false.**  Tao gets
`|E e(ξX_n/3^n)| ≪ n^{−A}` for every `A`, uniformly in `ξ` prime to 3.  In the mirror,
`sup_{ξ odd} |G_j(ξ)| ≈ 1.5/j` (`sup·j = 1.45, 1.46, 1.49` at `j = 16, 18, 20`), attained at `ξ = 3^k`
near `2^{j/2}` (`729, 729, 2187`), against a median `≈ 0.55·2^{−j/2}`.  The profile of `|G_j(3^k)|`
in `k` is a bell centred near `k ≈ j/2 − 2.5`; a weaker chain `13·3^k` also shows.  So uniform
character decay is not available, and the crude sufficient condition `sup = o(1/j)` (from the
square-wave expansion of the top digit) fails by a constant factor.

**But the resonance is harmless for the bias.**  Exactly, `|bias_j|/2^j ≤ W_j := 2^{−j} Σ_{ξ odd}
|G_j(ξ)| / sin(πξ/2^{j+1})`, and the resonant frequencies are large, so their weight is small.
Measured (`weighted.py`): `W_j = 0.290, 0.173, 0.090, 0.052, 0.029, 0.015, 0.0078, 0.0047` at
`j = 8, 10, …, 22`, i.e. `W_j ≈ 0.45·j·2^{−j/2}`, with the `3^k` chain carrying about a quarter.
So `W_j → 0` is a Fourier-side sufficient condition for `BiasDecays` that the data satisfy
comfortably (node candidate `WeightedCharDecay`, 80%, not yet in Lean).  In the recursion, the
first branch contracts the weighted sum by exactly `1/√2` per level (pair `ξ, ξ + 2^j`:
`1/sin x + 1/cos x ≤ 2√2 · 1/sin 2x`), which matches the observed `2^{−j/2}` rate.  The second
branch scrambles the weights through `ξ ↦ 3^{−1}ξ`, and that is where a proof would have to work.

**Reading for the moonshot.**  Collatz is "3 deterministic, 2 random".  Tao works on the side
where the randomness acts as the multiplier and mixes; the beyond-Terras questions live on the
mirror side, where the deterministic `×3` makes frequencies resonate.  That is a concrete
reason the almost-all methods stop short of the per-level bias, not a vague one.  Known or new?
The 2-adic recursion is elementary and may well be folklore; the resonance measurements and the
weighted criterion I have not seen.

**What is new tonight, in one list**: the beyond-Terras bias `E_j` and its exact structure (lift
identity, residue reading, mod-3 recursion, `E_j ≡ 2 (mod 4)`, aligned-window invariance, Terras at
depth `j`, the digit form, the band decomposition with its exact small bands and inheritance
recursion, the AR(1) reading with `ρ₀(q)`); the conjugacy complexity ladder with `Q` scrambling
every zero-entropy input tried; the Collatz-Champernowne family with its conjectured normality
threshold at `2/(2 − log₂ 3)`; the identification of the beyond-Terras letter autocorrelation with
orbit coalescence (exact decomposition, merge-next anticorrelation, the parity recursion at even
distance, the residue-class mechanism behind its uniform odd-image rate, the convergent window
density, and the measured gap between it and the eventual merge density); the Walsh spectrum of the
beyond-Terras letter in the parity-word basis, with its exact geometric reach (the √-law at every
cylinder depth); and the recalibration that the sign of `E_j` is memory, not
arithmetic, at the depth reachable tonight.

## 11. The 3-adic bridge: `BiasDecays` from truncated fine-scale mixing (2026-10-24, Ren on Opus 5.5)

§10.6 withdrew the Tao bridge because "our conjectures are signed statements … Tao's law says
nothing about that weight".  On the 3-adic side that is not so.  The sign is a function of the
Syracuse value itself.

**The identification (exact).**  For `r < 2^j` with `a = oddCount r j`, `T^j r < 3^a`
(`tstep_iterate_lt_three_pow`), and `T^j r ≡ Σ_{k=1}^{a} 3^{k−1} 2^{−T_k} (mod 3^a)`, where
`T_k = j − d_{a+1−k}` and `d_1 < … < d_a` are the odd-step times.  So `T^j r` is the least residue
of Tao's Syracuse variable at level `a`.  By Terras the word is uniform, so given `a` the set
`{T_k}` is a uniform `a`-subset of `[1, j]`.  That is iid geometric gaps sliced at
`T_a ≤ j < T_{a+1}`, and the slice is the same for every gap parameter `p`.

**The reduction (exact; `Bridge3.lean` `abs_levelSign_le`, proof owed).**  Write `μ_{j,a}` for
the slice law on `ℤ/3^a`.  For every `m ≤ a`,

    |E_{μ_{j,a}} (−1)^{T^j r}|  ≤  osc_{m,a}(μ_{j,a}) + 3^{m−a},

because the `3^{a−m}` lifts `c + 3^m t` of a least residue alternate in parity.
`experiments/conjugacy/fsm_bridge.py` checks it at every `j ≤ 20`, every `a` in the binomial
bulk, and every `m`, with no violation.  It also reproduces `E_16 = 362` and `E_20 = 1042`.
The best bound at `a ≈ j/2` is `0.375` (`j = 16`) and `0.291` (`j = 20`), falling at
polynomial speed.  At high `a` it degenerates: past `a/j ≈ 0.63` the slice has about `3^a`
atoms or fewer and cannot mix, but that range has mass `≲ e^{−0.034 j}`.

**The input it needs, measured (`twisted_charfn.py`).**  Fine-scale mixing for a sliced law
follows, as in Tao's deduction of Prop 1.14 from 1.17, from characteristic-function decay
**twisted by `e(θ T_n)`, uniformly in `θ`**.  Exact via Tao's recursion plus the twist,
`φ_n(ξ, θ) = Σ_g P(g) e(θg) e(ξ 2^{−g}/3^n) φ_{n−1}(ξ 2^{−g}, θ)`:

| `n` | `sup_ξ |φ_n|`, `θ = 0` (Tao, control) | `sup_{ξ, θ} |φ_n|` |
|---|---|---|
| 5 | 0.129 | 0.145 |
| 8 | 0.061 | 0.066 |
| 10 | 0.038 | 0.048 |
| 11 | 0.032 | 0.042 |

The twist costs a bounded factor and the decay continues.  No `θ` resonates.  The worst `ξ` are
powers of 2: the 3-adic mirror of §10.6's `3^k` chain, and here harmless.  Tilted gap laws,
needed for `a` away from `j/2`, behave as entropy predicts.  At `p = 0.4` (mean gap 2.5) the
decay is fast, `0.018` at `n = 9`.  At `p = 0.6` (mean 1.67, entropy 1.62 bits, just above
`log₂ 3 = 1.585`) it is slow, `0.143`.

**The graph (`Bridge3.lean`).**

- **Node `TwistedSyracCharDecay` (prose):** for gap laws in an entropy-safe range,
  `sup_θ |E e(ξ X_n/3^n + θ T_n)| ≪_A n^{−A}` uniformly in `ξ` prime to 3.  Odds: 75% true,
  35% that Tao's §6-7 proof adapts.  It uses memorylessness, which every geometric law has, and
  `|e(θg)| = 1`.
- **Node `TruncatedSyracMixing` (Lean):** slice fine-scale mixing for `a ≤ 11j/20`.  80% true.
- **Edges, proofs owed:** `abs_levelSign_le` (elementary), `bias_eq_sum_levelSign` (fiberwise
  sum), and `biasDecays_of_truncatedSyracMixing` (adds the binomial tail).  The missing middle
  edge is `TwistedSyracCharDecay ⇒ TruncatedSyracMixing`, Tao's 1.17 ⇒ 1.14 deduction for a
  sliced law.
- **Teeth:** `levelSign_four`, `levelSign_five` and `levelSet_card_five` are kernel-checked.

**What changes.**  C1 is no longer "mechanism: none".  It now sits on the almost-all side of
Collatz, where Tao's methods live.  The obstruction §10.6 found, the deterministic `×3`
resonance, belongs to the 2-adic Fourier picture and does not arise here.  The sign `E_j > 0`
(C2b) stays unexplained: mixing bounds give `|b_j| → 0` at polynomial rate at best, nowhere near
`2^{−j/2}`.  So this route reaches C1 and nothing finer.  Known or new: I have not seen the
identification of the beyond-Terras bias with a sliced Syracuse least-residue parity; not
searched.

## 12. The Fourier side: decay of each fixed frequency suffices (2026-10-24, Ren on Opus, `Conjugacy/Fourier.lean`)

Complements §11 (the 3-adic bridge through Tao's Syracuse variable); this section stays on the 2-adic Fourier side of §10.6.  Statements first, all in `Conjugacy/Fourier.lean`, frozen with `sorry` and confidences; build green with both modules.

- **`bias_div_le_lowFreq_add_tail`** (97%): for every `K ≥ 1`, `|bias j|/2^j ≤ Σ_{odd ξ ≤ K} 2‖G_j(ξ)‖/ξ + √(2/K)`.  Parseval (`sum_norm_sq_fourierCoeff`: `Σ_ξ ‖G_j(ξ)‖² = 1`) and Cauchy–Schwarz pay for every frequency above `K` at once; Jordan's inequality turns §10.6's `1/sin` weight into `1/|ξ|`.  Checked at every `(j ≤ 24, K ≤ 729)` with positive slack; **teeth**: with the `√(2/K)` term deleted the inequality fails from `j = 13` (`lowfreq.py`).
- **Node `LowFreqDecay`** (85%) and edge **`biasDecays_of_lowFreqDecay`**: if each fixed odd frequency's coefficient tends to `0`, then C1.  This is strictly weaker than §10.6's `W_j → 0` (`WeightedCharDecay`, never frozen; superseded) because it asks nothing uniform in `ξ`, which matters: on the chain `ξ = 3^k` the normalised coefficient `‖G_j(3^k)‖·2^{j/2}` rises before it falls (`27`: peak 7.8 at `j = 13`; `81`: 16.9 at `j = 22`).  Off the chain, `‖G_j(ξ)‖·2^{j/2} ∈ [0.04, 2.8]` for `ξ = 1, 3, 5, 7, 15`.
- **`fourierCoeff_succ`** (97%): the mirror recursion in exact complex form, `G_{j+1}(ξ) = ½G_j(ξ) + ½e(ξ(1−4u)/2^{j+2})G_j(uξ)`, `3u ≡ 1 (mod 2^{j+1})`; error `1.8e-11` over every `ξ < 2^{j+2}`, `j ≤ 17`; **teeth**: without the phase, error `0.65` (`recurcheck.py`).
- **Magnitudes alone prove nothing** (exact, one line): the recursion bounds `‖G_{j+1}(ξ)‖` by the mean of `‖G_j(ξ)‖, ‖G_j(uξ)‖`, and from `‖G_0‖ = 1` on its single odd class that gives only `‖G_j‖ ≤ 1`.  So any proof of `LowFreqDecay` is an exponential-sum statement that must use the phases.  What one level of the triangle inequality does (`wbranch.py`, control: reproduces §10.6's `W_j` to three figures at `j = 8..22`): `W_j ≤ A_j + B_j` with `A_j/W_{j−1} ≈ 0.52` (the first branch gives about `½`, not the worst-case `1/√2`, because the mass sits at low frequency) and `B_j/W_{j−1} ≈ 0.36–0.41`, total `0.88–0.96` for `j ≥ 11`.  It contracts only because the actual `‖G_{j−1}‖` already carries earlier cancellation.
- **Node `TwoAdicFreqDecay`** (80%) and edge **`lowFreqDecay_of_twoAdicFreqDecay`**: unrolling the first branch, `‖G_j(ξ)‖ ≤ Σ_m 2^{−m}‖G_{j−m}(ξ/3)‖ + 2^{−j}` with `ξ/3` read in `ℤ₂`, so decay at an integer frequency is fed by decay at the 2-adic "third point" `ξ/3`.  The node asks for decay at every fixed 2-adic unit frequency; it is closed under `η ↦ η/3`.  Measured (`twoadicfreq.py`): `η = ±1/3, 1/9, 5/7, 1/27` and a random 64-bit unit all stay at `‖G_j(η)‖·2^{j/2} ∈ [0.14, 1.6]`, `j ≤ 24`; the `±1/3` pair agrees to every digit (conjugate symmetry, a sanity control).  No resonance at `η = 1/3^k`: the resonance lives on the integer chain `3^k`, not its inverse.

**Where the two sides meet.**  §11 reduces C1 to Tao-style fine-scale mixing twisted by `e(θT_n)`, uniformly in `θ`; here C1 reduces to pointwise decay at fixed 2-adic frequencies.  Both are exponential-sum statements about the same random input (iid `Geom(2)` gaps), read 3-adically there and 2-adically here.  The 2-adic side has the cleaner closure (`η ↦ η/3`) and the harder resonance (the coherent `3^k` chain); **No direct edge** (personal-c5, 2026-10-24, on §11's side): the twist `e(θT_n)` sees only the total length, while `TwoAdicFreqDecay` correlates the sign with a 2-adic character of the start `r`.  A bridge would need joint mixing of the 3-adic Syracuse value with a 2-adic phase of `r`, a two-place statement that neither section supplies.  So the two reductions are parallel, not nested.

**The sup is on the chain, and it decays like `j^{−1/2}` (measured to `j = 33`; ~14:50).**  `supfreq.py` (full FFT, `j ≤ 24`) finds that for every `j` from `8` to `24` the maximum of `‖G_j(ξ)‖` over odd `ξ` sits on `±3^k`; `chainsup.py` (chunked direct sum over the chain, control: reproduces the FFT values at `j = 22, 24` to every printed digit) extends the chain maximum to `j = 33`.  `sup_ξ ‖G_j(ξ)‖ = 0.104, 0.075, 0.065, 0.058, 0.0525, 0.0515` at `j = 14, 20, 24, 28, 32, 33`.  Normalised, `sup · √j` falls slowly (`0.388 → 0.296`) while `sup · j` rises (`1.45 → 1.70`), so on this range the uniform rate is between `1/j` and `1/√j`, and a uniform bound `sup ≤ C/j` is false-looking, as recorded above.  The maximising exponent drifts upward, `k/j = 0.33` at `j = 24` to `0.42` at `j = 33`.

A heuristic for both facts (not a proof; confidence 60%).  Unroll the mirror recursion from `ξ = 3^k` at level `j`: each level either keeps the frequency or divides it by `3` with phase `e(−3^{k'−1}/2^{j'+2})`, which is `≈ 1` while `3^{k'} ≪ 2^{j'}`.  At `k ≤ j/2` the typical path keeps that margin (its `log₂` gap shrinks by `≈ 0.21` per level from `(1 − k log₂3/j)·j`) until the frequency reaches `1`, at a level `L ≈ j − 2k` with Gaussian spread `√j`; from there it contributes `G_L(1) ≈ 2^{−L/2}`.  Averaging over `L` gives `‖G_j(3^k)‖ ≈ (1/√j) Σ_L 2^{−L/2}`, largest for `k → j/2`, i.e. `sup ≍ j^{−1/2}` with `k/j → 1/2`.  Paths that overshoot past `1` into `3^{−m}` meet decorrelated phases (§12's measured third points).  If the picture is right, the resonance is coherent **transport** of the frequency `3^k` down to `1`, and the uniform node `sup_ξ ‖G_j(ξ)‖ → 0` (stronger than `TwoAdicFreqDecay`, which it implies at once) is true, at confidence about 65%.  Frozen in `Conjugacy/FourierSup.lean`: `SupFreqDecay` (65%), the rate `SupFreqSqrtBound` (`‖G_j(ξ)‖ ≤ C/√j`, 50%), and the edges `supFreqDecay_of_sqrtBound` and `twoAdicFreqDecay_of_supFreqDecay`, now proved axiom-clean (PR #83).  What would refute the heuristic is `sup · √j` turning upward, or `k/j` stalling well below `1/2`, at larger `j`.

**The lattice formula: one frequency costs `j²`, not `2^j` (~16:00; Lean `Conjugacy/FourierLattice.lean`).**  The mirror recursion sends a frequency `f` only to `f` and `f/3`, so `G_j(ξ)` involves only `ξ · 3^{−m}`, `m ≤ j`, at each level: `V_{n+1}(m) = ½V_n(m) + ½ e(−⟨ξ3^{−(m+1)}⟩_{n+2}) V_n(m+1)`, `V_0 ≡ 1`, `G_j(ξ) = V_j(0)`, where `⟨x⟩_k = (x mod 2^k)/2^k` and the phase uses `1 − 4u ≡ −3⁻¹`.  Unrolled, `G_j(ξ)` is the expectation over a uniform random subset `S = {s₁ > s₂ > ⋯} ⊆ {0..j−1}` of `e(−Σ_t ⟨ξ·3^{−t}⟩_{s_t+2})`: a multiplicative functional of a simple random walk in the space-time environment of the `2`-adic digits of `ξ·3^{−t}`, each power used once, read at a random level.  So `LowFreqDecay` is a weighted equidistribution statement about binary digits of powers of `3`.  Proved as `fourierCoeff_eq_latticeCoeff` (induction on `fourierCoeff_succ`), axiom-clean (verified 2026-10-24, PR #83).  Control (`latticedp.py`): matches the FFT at every `j ≤ 18`, ten frequencies each, error `2.6e-16`; **teeth**: phase deleted, error `1.23`.  Since every odd residue mod `2^{n+1}` is `±3^k`, the whole spectrum at level `n` is `k ↦ G_n(3^k)` on `ℤ/2^{n−1}`.

Measured with it (`latticerun.py`, `latticemp.py`):
- **Chain sup to `N = 4096`.**  Over `|k| ≤ N`, `sup · √N = 0.2352, 0.2306, 0.2284, 0.2272, 0.2267` at `N = 256, 512, …, 4096`, maximiser `k/N = 0.488, 0.494, 0.497, 0.499, 0.499`; reproduces `chainsup.py` at `N = 24, 28, 32, 33` to every printed digit.  The transport heuristic's two predictions (`j^{−1/2}`, `k/N → 1/2`) both hold.  `SupFreqDecay` to 80%, `SupFreqSqrtBound` to 75%.  Caveat: the window `|k| ≤ N` is a vanishing part of `ℤ/2^{N−1}`; that the global sup sits there is checked by FFT only to `N = 24`.
- **Fixed frequencies decay exponentially, faster than square-root cancellation.**  `log₂‖G_n(ξ)‖/n ∈ [−0.530, −0.520]` for `n = 1000..1600` at `ξ = 1, 5, 7, 27`, at the `2`-adic `1/3`, `5/7`, and at a random 64-bit unit; at `ξ = 1` it is `−0.541, −0.527, −0.524, −0.529, −0.526, −0.528, −0.526, −0.526` for `n = 200, 400, …, 1600`.  60-digit rerun agrees with the float DP to relative `2.5e-13` at `n = 1000`.  The exponent `≈ 0.526` is unidentified.  Frozen for integer frequencies as `FixedFreqExpDecay` (`∃ δ > 0`, rate `2^{−(1/2+δ)j}`, 55%) with the edge to `LowFreqDecay` (proved, PR #83).
- **The exponential rate is not uniform over `2`-adic units** (construction, conditional on the chain measurement).  Write `η = 3^a`, `a ∈ ℤ₂`; `η mod 2^{n+1} = 3^{a mod 2^{n−1}}`.  Take `a = Σ_i 2^{m_i}` with `m_{i+1} ≥ 2^{m_i+2}`, `k_i = Σ_{l≤i} 2^{m_l}`, `n_i = 2k_i`: then `m_i < n_i − 1 ≤ m_{i+1}`, so `η mod 2^{n_i+1} = 3^{k_i}` with `k_i = n_i/2`, where the chain value is `≈ 0.22/√n_i`.  So `TwoAdicFreqDecay` must stay rate-free, and a proof of it must survive polynomial rates at such Liouville-type `η`; `SupFreqDecay ⇒ TwoAdicFreqDecay` covers them.  Integer `ξ` have generic-looking `2`-adic logarithms, consistent with the measured exponential rate.

**The exponent `0.52` is the `×3` structure, not randomness (~16:50; `polymer.py`, `polymer2.py`, `polymer3.py`, `polymer4.py`).**  The lattice sum is a 1+1 directed polymer with unit complex weights, so the natural explanation of a better-than-`2^{−n/2}` rate would be the quenched-vs-annealed gap of a random-phase polymer (the annealed value is exactly `E|G_n|² = 2^{−n}` for any iid unit-modulus environment).  Tested on the same lattice, by the least-squares slope of `log₂|G_n|` over `n ∈ [N/2, N]` (which damps accidental near-zeros of the complex sum).  Control: the Collatz rows reproduce `latticerun.py` digit for digit.
- **Collatz environment**, 5 independent frequencies (`1, 5, 7, 5/7`, a 64-bit integer; `27` and `1/3` are the `ξ = 1` environment shifted along the orbit, and agree with it to 4 digits): slope `−0.5221 ± 0.0026` (sd) at `N = 3200`, range `[−0.5261, −0.5197]`.
- **Same structure from uniformly random 2-adic `ξ`**: `−0.5250 ± 0.0036` (`N = 1600`, 12 draws), `−0.5241 ± 0.0029` (`N = 3200`, 8 draws).  So the effect is generic in `ξ`, not special to integers.
- **Null A, iid uniform phases**: `−0.5122 ± 0.0036` (`N = 3200`, 20 seeds).
- **Null B, the fair one**: keep the truncation structure, `w(n, m) = e(−⟨x_{m+1}⟩_{n+2})`, but with the `x_t` independent uniform 2-adic integers: `−0.5132` (`N = 1600`), `−0.5086` (`N = 3200`), drifting toward `−1/2`.
- Gap Collatz − null B: `−0.0117` (`N = 1600`, Welch `z = −9.5`) and `−0.0155` (`N = 3200`, `z = −12.6`); no overlap between the samples at either `N`.

So independent 2-adic digits give (at most barely) square-root cancellation, and the extra cancellation comes from the coupling `x_t = 3·x_{t+1}` between consecutive powers.  The phase field `Θ(k, t) = ⟨ξ·3^{−t}⟩_k` satisfies `2Θ(k+1, t) ≡ Θ(k, t)` and `3Θ(k, t+1) ≡ Θ(k, t) (mod 1)`: the environment is a compatible `×2`/`×3` family on the circle, i.e. the Fourier side of C1 is a polymer partition function in a Furstenberg `×2×3` environment.  That names the tool family to read for `TwoAdicFreqDecay`: equidistribution of `×3` orbits under `×2` structure (Host-type theorems, Rudolph–Johnson, Lindenstrauss), for what they teach about proving cancellation, not as precedent.  Open: the null-B slope may converge to exactly `−1/2` (quenched = annealed) or to something just below; the Collatz value has been stable at `≈ −0.524` from `N = 1600` to `3200`.  Confidence that the gap is real and not a finite-size effect: 80%.

**Where the extra cancellation comes from: the spectrum is multifractal (~17:30; `massconc.py`, `masswhere.py`, `polymer5.py`).**  Parseval fixes the *mean* of `|G_j(ξ)|²` over odd `ξ` at exactly `2^{−j}`, for the Collatz sign just as for any null; so "extra cancellation" at fixed frequencies is a gap between the typical and the mean value, and the `L²` mass must concentrate.
- **Concentration** (full FFT, `j ≤ 24`; control: mean exactly `2^{−j}`): `log₂(median |G|²)/j ≈ −1.083`, and half the mass sits on `18.4%, 9.2%, 4.6%, 2.8%` of the odd frequencies at `j = 8, 14, 20, 24`, shrinking like `≈ 2^{−0.18 j}`.  For a random sign function `|G|²` is asymptotically exponential and that fraction is the constant `18.7%`.
- **Which frequencies** (index odd `ξ = ±3^k`, `k mod 2^{j−1}`; control: shares sum to `1` to 12 digits): by the scale of `|k|`, only the resonance window `|k| ∈ [4, 16)` is enriched (`600–1300×`, 3.9% of the mass at `j = 20`); every larger scale bin holds its fair share.  By popcount of `k` outside `|k| < 64`: popcount 1 is not enriched (`0.90×`), popcounts `2, 3, 4, 5` are enriched `5.2, 3.8, 2.2, 1.6×` at `j = 20` and `17.4, 11.0, 5.5, 2.6×` at `j = 24`, growing with `j`.  Reading: **multi-scale resonance.**  Since `3^{2^a} ≡ 1 (mod 2^{a+2})`, `3^{2^a + 2^b}` looks like the chain element `3^{2^b}` at every level below about `a`, and inherits the resonance there when `2^b` is near half that level; `3^{2^a}` looks like the non-resonant frequency `1`.  This is the same mechanism as the sparse-log units that defeat a uniform exponential rate (above), now seen as the carrier of the mass.  Confidence in the reading 60%.
- **Coherence length** (block nulls: keep `x_t = 3x_{t+1}` within blocks of `L` consecutive powers, independent 2-adic integers across blocks; `N = 1600`, 12 seeds each; known answers `L = 1` and `L = ∞` reproduce `polymer4.py`): slope `−0.5116, −0.5140, −0.5147, −0.5154, −0.5175, −0.5228, −0.5229, −0.5250` at `L = 1, 2, 3, 4, 8, 16, 64, ∞` (sd `≈ 0.005`).  Pairs carry at most ~18% of the gap (not significant); the coupling must hold across ~10–16 consecutive powers to recover most of it.  So the pair-phase identity this probe was looking for does not exist in a simple form (the lead is now ~5%).

**Tao's pairing transfers pointwise: `LowFreqDecay` from a positive walk (~18:00; Lean `Conjugacy/FourierPair.lean`; `pairbound.py`, `protect.py`).**  A literature pass (Host, BLMV, Hochman, Hochman–Shmerkin, Tao 2019 §7; report in this session) found Tao's §7 the closest tool: `G_n = E ψ₂(−ξ Σ_t 3^{−t} 2^{−k_t})` is his Syracuse characteristic function with the primes swapped.  The *uniform* mirror of Prop 1.17 is false (§10.6; today's `sup ≈ 0.227/√N`), and the geometry says why: Tao's unit condition (7.16) protects the start of his walk, while ours starts at the fine level `k = n+1`, where for `ξ = 3^{n/2}` the factors `Θ(n+1, t) = 3^{n/2−t}/2^{n+1}` are tiny along the whole walk.  But two pieces transfer **pointwise**:
- **Pairing** (Tao eq. 7.5, Lemma 7.2).  Two levels at a time, the middle coefficient is `¼(φ(2i,m) + φ(2i+1,m))` with the two exponents truncations of one `2`-adic number, so its modulus is `½|cos πΘ(2i+3, m+1)|`.  Hence `|G_{2i}(ξ)| ≤ U_i(0)` for a **positive** walk `U` (`pairBound`; proved `norm_latticeCoeff_le_pairBound`, axiom-clean, PR #84).  Checked: `U ≥ |G|` at every even `n ≤ 200`, seven frequencies, minimum slack `1.1e-9` (nearly attained: the check has teeth).  Measured: `log₂ U_n/n ≈ −0.146` at `ξ = 1, 5, 27` and a random 2-adic unit, stable `n = 400..1600`; at the resonance `U_n(3^{n/2}) = 0.38, 0.23, 0.13` at `n = 64, 256, 1024`.  Note how much the pairing keeps: the per-level triangle inequality gives only `‖G‖ ≤ 1` (above).
- **Protection** (the mirror of Tao 7.16, but in the `t` direction).  If `3^t ∤ ξ` and `ξ < 2^k`, then `‖Θ(k, t)‖ ≥ (1 − ξ/2^k)/3^t`: with `q = 3^t`, `qX = ξ + 2^k M` gives `Θ = M/q + ξ/(q2^k)` and `M ≢ 0 (mod q)`.  Exhaustive check, equality attained (`protect.py`; proved `pairTheta_far`, axiom-clean, PR #84).  So for a fixed integer frequency the walk starts in a strip of small `t` where every factor is `≤ cos(π/(2·3^t))`-ish, and the strip vanishes exactly when `3^t | ξ`, the resonance.

**So the oscillatory node is replaced by a positive one**: `PairBoundDecay` (85%) ⇒ `LowFreqDecay` ⇒ `BiasDecays`, the first edge proved as `lowFreqDecay_of_pairBoundDecay` (axiom-clean, verified 2026-10-24, PR #84).  `PairBoundDecay` is the analogue of Tao's Prop 7.3, a renewal statement: the walk meets factors bounded away from `1` often enough.  The remaining work is to transport Tao's black/white triangle geometry (his Lemma 7.4 and Prop 7.3) to the field `Θ(k, t)`, whose relations `Θ(k−1, t) = 2Θ(k, t)`, `Θ(k, t−1) = 3Θ(k, t)` make black triangles open toward lower `k` and lower `t` with hypotenuse slope `−log 2/log 3 ≈ −0.63`, against the walk's mean slope `−1/2` (two levels per pair, about one step); the slopes are close, as Tao's are (`4` vs `3.17`), so the separation argument is needed.  **The direct port of Prop 7.3 fails the one quantitative check (~18:30; read from Tao 2019 §7.4, confirmed independently by personal-c5 from the `tao-collatz` Lean port).**  Tao's Case 3 needs a walk inside a triangle to exit before it runs out of room: by (7.52) a triangle met with `m` steps left has height `≤ (log 9/log 2) m`, and the walk (slope 4) climbs out within `(log 9/(4 log 2)) m ≈ 0.79m` steps ("noting that `0.8 > ¼ log 9/log 2`"), leaving `≥ 0.2m` to collect white points.  In the mirror, the walk (one step per pair, slope `1`) is *shallower* than the triangles (hypotenuse slope `log 4/log 3 ≈ 1.26`), the same ratio `1.26` on the wrong side, so a trap can consume all the remaining time: the resonance is exactly that.  Both margins are the inequality `½ < log 2/log 3`, the Collatz contraction: it helps on the 3-adic side and hurts on the mirror side (§10.6's "3 deterministic, 2 random", now quantitative).
- What is generic and should port (personal-c5's reading of the Lean port): the triangle decomposition (Lemma 7.4) with metric `(log 4, log 3)` and the protection at the end of the walk (`Θ(2, t) = ±1/4`), the holding-time and first-passage machinery (Lemmas 7.6, 7.7), Lemmas 7.9–7.10.  What does not: the budget (7.52) and the monotone induction it feeds (Prop 7.8).
- A repair for fixed `ξ` (sketch, not checked): `pairTheta_far` bounds a triangle whose corner sits at row `t` to size `≤ t log 3 + log ε`, so a trap entered near position `p` with its corner near the walk lasts `≤ ~0.79p` more pairs; if every trap obeyed that, the walk would exit `≫ log n` traps, each exit landing on a white point (Claim (*)), giving `U_n ≤ n^{−c}`, enough for `LowFreqDecay`.  The gap: traps whose corner sits far above the walk.  Such a corner is a near-coincidence `3^t y − 2^k z = ξ` with `y/2^k` tiny, so ruling out enough of them is a Diophantine input of the linear-forms-in-logarithms kind (Tao's Remark 7.5 mentions Baker and deliberately avoids it).
- **Far-corner traps, measured (~19:00; `traps.py`, `runs.py`, Lean `Conjugacy/FourierTraps.lean`).**  For fixed `ξ` the field `Θ(k, t)` does not depend on the walk length; the walk runs along `k + 2t ≈ n+1`, so traps are intersections of fixed black components with walk lines.  Field `k ≤ 4000`, `t ≤ 2000`, `ε = 0.02`, ~80,000 components: the longest trap is `9, 8, 8` pairs at `ξ = 1, 5, 7` (walks up to 2000 pairs), sizes `≈ 11–12` = the extreme value `log(#points · ε)` of a random field; worst `L/t_in = 1.2` at `t_in = 5` (a small far-corner trap exactly at the protection cap, size `7.07 = 10 log 3 + log ε`).  Control: `ξ = 3^{1000}` gives one trap of `L = 1000`, the whole walk.  The empirical run exponent `max log(1/‖Θ‖)/log(k+t)` is `2.09, 2.28, 1.95, 2.00` (`ξ = 1, 5, 7, 11`) and `1.94, 1.90, 1.95, 1.87` over `k + t ≥ 1000`: the random-field critical value `2`, not creeping up.  Frozen: `NoLongRuns` (`‖Θ(k,t)‖ ≥ (k+t)^{−C}` off the resonant columns `3^t | ξ`, 75%) and the frontier edge `pairBoundDecay_of_noLongRuns` (55%; Tao §7.2–7.4 rebuilt with the budget (7.52) replaced by the run bound, giving `U_n ≤ exp(−cε³n/log n) + o(1)`).
- **Duality.**  For `ξ = 1`, `Θ(k, t) = (2^{−k} mod 3^t)/3^t` up to `1/(3^t 2^k)`: a long binary run of `3^{−t}` at bit `k` is a long run of ternary `0`s or `2`s of `2^{−k}` at position `t`, both the near-coincidence `|2^k a − 3^t b|` small.  That is why Tao's triangle lemma ports (his `θ(j, l)` reads `2^{−l} mod 3^n`), and it places `NoLongRuns` next to Erdős's ternary-digits-of-`2^n` problem: pointwise, hard.  What might be provable instead is an *averaged* version (few long runs in the walk's tube), the kind of statement Korobov's `p`-adic method gives for `2^k mod 3^t` over short ranges of `k`; a pointer for the next reading, not checked.
- **What would suffice, averaged.**  `U_n ≤ P(X < n/8) + exp(−ε³n/8)` with `X` the number of white single-step pairs, and single-step pairs number `≈ n/4` with overwhelming probability; so `PairBoundDecay` follows from a large-deviation bound on the walk's black visits.  Two inputs would plausibly give that through a renewal argument: (A) black density `O(ε)` in the walk's `√n`-tube (`δ = ε` fixed), and (B) no triangle of size `≥ o(n)` in the tube (far weaker than `NoLongRuns`).
- **The literature does not reach either (~19:40; reading-agent report, sources: Vandehey arXiv 1606.07911 quoting Korobov 1972 Thm 4 and Korobov's book Thms 32–33; Bennett–Bugeaud 2012 Thm 2.1 quoting Bugeaud–Laurent 1996; Lagarias math/0512006 Thm 1.4; Tao 1909.03562 §7).**  Our ranges have `≈ log(modulus)` points (`k ≤ Ct` against modulus `3^t`).  Korobov's `p`-adic bound `|Σ_{n≤N} e(a b^n/p^α)| < 3N exp(−γ(log N)³/(log p^α)²)` is nontrivial only for `N ≥ exp(C(log m)^{2/3})`, and every other exponential-sum route (Vandehey's digit-string counts, Bourgain) needs longer ranges still: nothing for (A).  `p`-adic linear forms in two logarithms give, for `‖a2^{−k}/3^t‖ < δ`, only `δ ≥ 3^{−t} e^{ct/(log k)²}`, the protection lemma improved by a `(log k)^{−2}` fraction of the exponent: traps still `∝` position, nothing for (B).  The ternary-digit theorems (Narkiewicz, Lagarias, Dupuy–Weirich) are full-period counts on the bottom digits; ours are the top digits of residues mod `3^t` over short ranges.  The agent's exact CRT form of the duality: with `v = 2^{−k} mod 3^t`, `u = 3^{−t} mod 2^k`, `av/3^t + au/2^k ≡ a/(2^k 3^t) (mod 1)` (checked on 3,000 random triples).
- **So the Fourier route to C1 is blocked at a recognisable frontier**: the distribution of `2^{−k} mod 3^t` (equivalently the top binary digits of `3^{−t}` mod `2^k`) over ranges of `k` as short as `t`.  That is the "deterministic `×3`" side of Collatz in its sharpest form; on Tao's side the random `2`-multiplier supplies the same averaging for free, which is why his walk is steep enough and ours is not.  Revised confidence that this route proves C1: 4% (down from 12%). **Weaker theorems checked, no free lunch (2026-10-25):** (i) *C1 along a density-one set of `j`*: by Markov, `U_j ≤ 8E[black visits_j]/j + e^{−ε³j/8} + e^{−cj}`, and each `(k, t)` lies on `O(1)` walk lines in expectation, so the Cesàro mean of `U_j` is bounded by the 2-D black density of `Θ` over `k + 2t ≤ J`; but by the duality every slice of that region is again a short orbit (column `t`: the first `J − 2t` binary digits of `ξ·3^{−t}`, period `2·3^{t−1}`; row `k`: the first `≈ k` ternary digits of `ξ·2^{−k}`), so the 2-D average sits at the same Korobov frontier.  (ii) *`TwoAdicFreqDecay` for Haar-almost every unit*: provable, by Parseval (`E_η|G_j(η)|² = 2^{−j}`) and Borel–Cantelli, with rate `2^{−(1/2−ε)j}`; but the integer frequencies the bias reduction needs are null, so it misses C1 (the same a.e.-versus-every gap as Host's theorem).  The Fourier lane closes here at a clean checkpoint.  The frozen nodes (`PairBoundDecay` 85%, `NoLongRuns` 75%) stay as the clean statements of what is missing; the 3-adic side (§11, `SliceCharDecay`), where Tao's slope check passes, is the better bet for C1.  `PairBoundDecay` itself stays at 85%: the positive walk decays fast numerically (`2^{−0.146 n}`); what is missing is a proof technique, not evidence.

**Status (15:30).**  The five `sorry`s in `Fourier.lean` are proved: Parseval, the reduction, `biasDecays_of_lowFreqDecay`, the mirror recursion and the 2-adic edge, all axiom-clean (`#print axioms`: `propext, Classical.choice, Quot.sound`, verified 2026-10-24 on a local build; treadmill run `collatz-moonshot-fourier-20261024-140934-090000`, 6 laps, PR #82).  Frozen statements unchanged from `daad7a1`.  So on this side the chain `TwoAdicFreqDecay ⇒ LowFreqDecay ⇒ BiasDecays` is a theorem, and the open content is the node `TwoAdicFreqDecay` (or the stronger `SupFreqDecay`).  On §11's side, `TruncatedSyracMixing ⇒ BiasDecays` is likewise proved (personal-c5, Bridge3, PR #81).

**Next.**  The math target is `TwoAdicFreqDecay` itself: an exponential sum over a branching process whose frequency multiplier is the deterministic `3^{−1}`.

## 13. Tao §7 at `Pascal(p)`: the input for the 3-adic route (2026-10-25, Ren on Opus 5.5, `Conjugacy/SliceSeven.lean`)

Split agreed with personal-c5: this section and `SliceSeven.lean` are personal-2c's; §11, `Bridge3*.lean` and `SliceDecay.lean` stay personal-c5's.

**What `SliceCharDecay` needs.**  The slice law is iid `Geom(p)` gaps conditioned on `T_a ≤ j < T_{a+1}`, for every `p`, and the conditioning reweights each gap vector by `(1−p)^{j−T_a} ≤ 1`; after Tao's pairing the slice character is at most `pascalDamping a p ξ / P_p(slice)`.  Only `p = a/j` makes `P_p(slice)` polynomial (`≍ j^{−1/2}`): at `p = 1/2` it is exponentially small against Tao's `n^{−A}`.  So the input is Tao's (7.5) damping bound at `Pascal(p)`, **uniformly** in `p ∈ [1/5, 3/5]`: frozen as `PascalDampingDecay` (80%), with the edge `sliceCharDecay_of_pascalDampingDecay` (**proved**, axiom-clean, PR #85, `de72803`).

**Tao's proof transfers at the paper level** (read line by line for every `½`-specific constant).  `q = P(b = 3) = 2p²(1−p)`; `Hold = (1, 3) + Σ (1, b′_i)` over `Geom(q) − 1` pair sums conditioned `≠ 3`; `E Hold = (1/q)(1, 2/p)` (`(4, 16)` at `½`); same support, so the same aperiodicity; exponential tails.  Lemma 7.7's first passage sits at `j ≈ sp/2` (`s/4` at `½`).  The deterministic half (field, Lemma 7.4, white points) and Lemma 7.2's `|cos πθ|` do not involve `p`.  Every slope-sensitive step reduces to `p log₂ 3 < 1` (Case 2 after (7.50); Case 3 after (7.52), where Tao's `0.8, 0.9` become thresholds strictly between `p log₂ 3` and `1`; the line after (7.64)), which at `p = 3/5` is `0.951`.  Constants depend continuously on `p`, so are uniform on the window.  Confidence the paper proof goes through: 80%.

**The Lean cost.**  In `tao-collatz` (`95a7172`), `p = ½` is baked into the probabilistic half of §7: `geomQuarter`, `pascalNe3` (mean `13/3`), Hold's `(4, 16)`, `HoldLocal`'s atom masses `1/400` and Chernoff constants `4λ₁ + 16λ₂`, the drift `16j − 5l`, `(3/4)^K` tails, the `0.8/0.9` thresholds: about 19k of §7's 21k lines (`FpLocation, Case3, ManyTriangles, Bridge, BlackEdge, HoldBasics, Monotone, HoldLocal, Reduction, Holding, Unroll`).  `Setup, Triangles, White` are `p`-free.  Generalising is a campaign, to live in `tao-collatz` (a new `p`-parametrised namespace beside the ratified §7, never editing its pins), required by this repo at a SHA.

**Update (2026-10-25, afternoon).**
- **The edge is proved** (PR #85, `de72803`, 3 Codex treadmill laps): `#print axioms sliceCharDecay_of_pascalDampingDecay` = `[propext, Classical.choice, Quot.sound]`, full build green.  The local limit theorem was not needed: `P_p(slice) = P(Bin(j, p) = a)` exactly, and at `p = a/j` the target `a` is the binomial mode, so `P ≥ 1/(j+1)`.  The edge's constant is `4 · 5^(A+3) · C`.  So `PascalDampingDecay ⇒ BiasDecays` now rests on `PascalDampingDecay` and c5's §6 edge `truncatedSyracMixing_of_sliceCharDecay` alone.
- **`SliceCharDecay` was false as first stated**, at `j = a = 0` (`0^(−A) = 0` in Lean's `rpow`, against a one-point slice of character 1; `¬ SliceCharDecay` checked axiom-clean).  Fixed by c5 in `22a9a7b` (`1 ≤ j`), before the edge was attempted.
- **The `PascalDampingDecay` campaign is running** in `tao-collatz` on branch `ren/sec7p-pascal`.  The plant `eb40bf3` copies this file's five definitions verbatim into `TaoCollatz/Sec7P/Statement.lean`.  It pins `pascalDamping_half_decay`, a `p = ½` calibration against the proved §7, and `pascal_damping_decay`, the target, which is this node's body.  The campaign spec is `SEC7P-PLAN.md`.
- **Is `p log₂ 3 = 1` a real threshold or only the method's?**  Geometrically, at `p = 1/log₂ 3` the walk's drift `2/p` equals the slope `log₂ 9` of a black triangle's long edge, so the walk can ride inside one triangle.  Probe: c5's exact DP, `p = 0.50 … 0.80` by `0.02`, `n ≤ 16`, plus controls at `0.9, 0.95, 0.99`.  The 2-step ratio `D(n+2)/D(n)` creeps toward 1 at every `p`, `½` included, so it cannot tell slow decay from none.  The effective exponent `α_n = −Δ log D / Δ log n` can, because super-polynomial decay needs `α_n → ∞`.
  - For `p ≤ 0.64`, `α_n` rises steadily with `n`: at `½` from `0.43` to `0.80`, at `0.64` from `0.19` to `0.35`.
  - For `p ≥ 0.66` it stops trending and wobbles: `0.16–0.29` at `0.66`, `0.05–0.13` at `0.80`.
  - The controls are near zero (`α ≈ 0.04, 0.007, 0.002`), so the instrument does see non-decay.
  - Dips at `0.58–0.64` that move to smaller `n` as `p` grows make part of the break noise.
  - Verdict: suggestive of a regime change near `0.63–0.66`, not shown; a sharp threshold at 50%.  The window `[1/5, 3/5]` is inside the clearly decaying zone either way.
  - The next instrument is `n = 18` at `p ∈ {0.60, 0.64, 0.68, 0.72}`.  If `α_18` still rises at the first two and stays flat at the last two, the threshold goes to about 65%, and a matching non-decay theorem above `1/log₂ 3` becomes a target.
- **C1 now rests on `PascalDampingDecay` alone** (2026-10-25, evening).  c5's `biasDecays_of_sliceCharDecay` (`SliceFourier.lean`, PR #86) bypasses `TruncatedSyracMixing` and the §6 transfer.  The composite `biasDecays_of_pascalDampingDecay` (`Conjugacy/C1.lean`) is axiom-clean.  SliceFourier uses sub-slice ratios up to `3/5` (cutoff `s ≤ j/12`).  So narrowing the node's window would need a re-proved Vandermonde tail with an `o(j)` cutoff, which is a fallback only if Sec7P stalls at the top end.
