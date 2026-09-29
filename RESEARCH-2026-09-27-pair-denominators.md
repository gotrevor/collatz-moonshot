# Odd-prime denominator ledger for pairwise cycle gaps

Run the persistent exact controls from the repo root:

```sh
./experiments/pair_denominators.py test
./experiments/pair_denominators.py ledger 00001111
./experiments/pair_denominators.py scan --depth 18
```

This follows §2 of [catalytic repair](RESEARCH-2026-09-27-catalytic-repair.md) and §2 of the [arithmetic-lifts follow-up](RESEARCH-2026-09-27-arithmetic-lifts-followup.md).  The dyadic valuation was already identified with parity-prefix collisions.  Here the prime divides the common *odd* denominator.  The conclusion is an exact deficit/excess decomposition and a closed-cycle falsification of the claim that all pair gaps remain nonintegral at that prime.  No Collatz exclusion inequality is established.

## Exact odd-prime statement

Let `x_0,...,x_(m-1)` be a primitive rational shortcut cycle for `T(x)=x/2` on even numerator and `T(x)=(3x+1)/2` on odd numerator.  Write every state in lowest terms as `x_i=a_i/d`, with common positive denominator `d`.  The denominator is coprime to 6, and every `a_i` is a unit modulo `d`.  To see the first point, a word with `k` odd symbols has rational closure denominator dividing `2^m-3^k`; each branch then preserves the reduced denominator since the multiplier is a unit modulo it.  Let `p^r || d`.

For `i<j`, put `h=j-i` and let `b` count odd symbols in the intervening word `w_i,...,w_(j-1)`.  Affine composition gives an integer `B` such that

```
2^h(a_j-a_i) = (3^b-2^h)a_i + d B.
```

Since `a_i` and 2 are `p`-units,

```
min(v_p(a_j-a_i),r) = min(v_p(3^b-2^h),r).             (1)
```

Thus the denominator-depth collisions are determined exactly by the multiplicative word prefixes.  Formula (1) deliberately says nothing about valuations *beyond* `r`: the affine term `dB` can affect those.

Let `C=binom(m,2)`, and sum over unordered pairs:

```
D_p = sum_pairs [r-min(v_p(a_j-a_i),r)]
E_p = sum_pairs max(v_p(a_j-a_i)-r,0).
```

For the absolute Vandermonde `V=product_(i<j)|x_j-x_i|`, exact arithmetic gives

```
v_p(V) = E_p-D_p.                                      (2)
```

`D_p` can be computed solely from `(p^r,w)` using (1); `E_p` records the deeper collisions.  In particular `V` is an integer exactly when `E_p>=D_p` for **every** prime `p|d`; it is nonintegral exactly when `E_p<D_p` for **at least one** such prime.  This criterion itself is only a ledger, since the actual rational states and therefore `E_p` are fixed by the same admitted word.

There is a uniform, nonzero forced deficit.  For one edge `h=1`, `3^b-2` equals `-1` or `1`, so its numerator gap is a `p`-unit.  In a primitive cycle of length `m>=3`, its `m` cyclic adjacent edges are different unordered pairs.  Therefore

```
D_p >= m r.                                             (3)
```

For `m=2`, the two edges represent one unordered pair and the lower bound is `r`.  Formula (3) is specific to the `3x+1` shortcut: for a generalized `qx+1` map, an odd edge has multiplier collision `q-2`, which may vanish modulo a denominator prime.  The CLI uses the correct edge-specific lower bound.  A hand control is the **negative** `5x+1` cycle `0011` with states `(-28,-14,-7,-13)/9`: at `p=3`, the four adjacent edges force deficit 6 rather than `mr=8`; all six pairs give `D_3=9`, `E_3=0`.

## A genuine supercollision under full cycle closure

The positive primitive `3x+1` word `00001111` has denominator 35 and states

```
(208,104,52,26,13,37,73,127)/35.
```

The states at indices 2 and 7 have numerator difference `127-52=75=3*5^2`; their rational gap is `15/7`, which is *integral at p=5*.  Hence the tempting stronger statement that every pairwise gap of a nonintegral cycle has negative `p`-valuation is false even with positivity, primitivity and full closure.  Its `p=5` ledger has 22 numerator gaps of valuation 0, five of valuation 1, and one of valuation 2; `D_5=22`, `E_5=1`, and `v_5(V)=-21`.  At `p=7`, `D_7=25`, `E_7=0`, and `v_7(V)=-25`.  The deep collision is real but does not compensate the full deficit.

The older positive rational control `11111000` has denominator 13 and minimum real gap `69/13>1`; here `D_13=26`, `E_13=0`.  The negative `3x+1` cycle `110` has integral states `-5,-7,-10`.  The positive integer `5x+1` cycle `1110000` has states `13,33,83,208,104,52,26`; its denominator ledger is empty.  Those are separate sign and map controls, not positive nonintegral `3x+1` evidence.

## Finite census and next claim

The new real-CLI scan reuses `research_lifts.pair_energy` for exact rational construction, closure and parity checks.  Through word length 18 it examined 26,788 positive primitive `3x+1` cycles, including 26,787 with `d>1`.  Every denominator prime in that finite population had `E_p<D_p`; there was no nonintegral cycle with integer Vandermonde.  The persistent test suite checks hand-computed valuation anchors through the CLI, including the 35-denominator supercollision.  The census is finite evidence only.

The exact open inequality suggested by this ledger is: every positive primitive rational `3x+1` cycle with `d>1` has **some** denominator prime satisfying `E_p<D_p`.  The scan observed the stronger `E_p<D_p` at every denominator prime through length 18, but there is no proof.  Even the suggested inequality would establish only `V integral => d=1`; it would not exclude a nontrivial integer cycle.  Therefore this audit adds a precise odd-prime arithmetic target and a falsification control, but no admission beyond the existing parity-word closure and no general cycle-exclusion mechanism.

The eight-state positive cycle, its common reduced denominator 35, exact closure, and the reduced gap 15/7 are also proved in `CollatzMoonshot/Obstructions/PairDenominatorControl.lean`, theorem `pair_denominator_control`.  The general valuation ledger remains a paper argument.
