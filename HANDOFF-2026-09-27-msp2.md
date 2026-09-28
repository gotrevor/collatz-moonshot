# HANDOFF 2026-09-28 — MSP² formalization: `MSP2/Proved.lean` is `sorry`-free

Task was `KICKOFF-2026-09-27-msp2.md`: discharge every `sorry` in `MSP2/Proved.lean` without
weakening a statement, and record a refutation if any statement turned out false.

**Outcome: all 19 statements are proved as written.  Nothing was weakened, nothing was refuted,
no `axiom` was introduced.**  `lake build MSP2` is green and `#print axioms` on every declaration
reports only `propext`, `Classical.choice`, `Quot.sound`.

## What landed

`MSP2/Order.lean` (new, `sorry`-free) — the one piece of mathematics the article's *distance*
claims need and that mathlib does not have: **`2` is a primitive root modulo `3ⁿ`**.  Everything
descends from a single lifting-the-exponent induction,

```
two_pow_three_pow : ∃ c : ℤ, 2 ^ 3ⁿ = -1 + 3^(n+1) * c  ∧  c % 3 = 1
```

proved by cubing: `(-1 + 3^(n+1)c)^3 = -1 + 3^(n+2)(c - 3^(n+1)c² + 3^(2n+1)c³)`, and the new
cofactor is `≡ c (mod 3)`.  Two independent consequences:

* the `-1` gives `2^(3ⁿ) = -1` in `ZMod (3^(n+1))` and the **exact** 3-adic valuation of
  `2^(2·3ⁿ) - 1` (namely `3^(n+1)`, not `3^(n+2)`), which together kill every proper divisor of
  the order.  Hence `orderOf_two_zmod : orderOf (2 : ZMod (3^(m+1))) = 2 * 3^m`.  The divisor
  bookkeeping is elementary: an odd order would be coprime to 2 and so divide `3^m`, giving
  `2^(3^m) = 1 ≠ -1`; an even order `2·3^j` with `j < m` divides `2·3^(m-1)` and contradicts the
  valuation.
* the refinement `c ≡ 1 (mod 3)` — which is *not* needed for the order — pins the cube root of
  unity `2^(2·3ⁿ) ≡ 1 + 3^(n+1) (mod 3^(n+2))`.  This is exactly what §16.5 needs, and it is what
  explains the alternation in the article's statement (see below).

Also in `Order.lean`: the vertical rule as multiplication by `2⁻¹`.  `tA_iterate_eq` is the
workhorse — *a vertical distance is pinned by a congruence*: for odd `A`, `b, x < A`,

```
2 ^ i * x ≡ b [MOD A]  →  (tA A)^[i] b = x
```

because `tA` preserves `[0, A)` and `2^i · (tA A)^[i] b ≡ b`, and `2^i` is cancellable mod odd `A`.
With it, each of §16.3, §16.5, §16.7.2 becomes one congruence plus one bound.

`MSP2/Proved.lean` — the 19 statements, in the order they fell:

* pure induction/`omega`/`ring`: `blockB_eq`, `blockB_succ_sub`, `bConst_closed`, `bConst_parity`,
  `cLeft_even_eq_bConst`, `delta_closed`, `bConst_succ_via_delta`, `residue_bound`,
  `fam_reproduce`, `step_three_fam_zero`, `covered_fam_zero`, `tA_two_mul`,
  `not_three_dvd_after_run`, `reachesOne_of_covered_upto`.
* `tA_distance` (§16.3): `2^(3^(n+1)+1)·Bₙ ≡ (-1)·(-1) = 1` gives the hit at distance
  `3^(n+1)+1`; an earlier hit at `i` forces `3^(n+2) ∣ 2^(i-1) + 1`, i.e. a `-1` strictly inside
  the half period, which `three_pow_dvd_of_dvd_two_pow_add_one` forbids.
* `tA_period` (§16.7.2): `minimalPeriod (tA (3^n)) b = orderOf (2 : ZMod (3^n))` for `b` prime to
  `3`, both divisibilities via `tA_iterate_eq` and cancellation of `b`.
* `tA_distance_opt2` (§16.5): with `ω := 2^(2·3^(m+1)) ≡ 1 + 3^(m+2)`, and the closed forms
  `2·C_k + 1 = 3^(k+1)` (`k` even), `= 5·3^(k+1)` (`k` odd) — new lemmas `cLeft_closed_even`,
  `cLeft_closed_odd` — both branches reduce to `3^(m+3) ∣ 2·3^(m+3)` resp. `3^(m+3) ∣ 3^(2m+4)`.
* `msp2_odd_run` (§2): the invariant `msp2Step^[i] M + 1 = 3^i · 2^(r-i) · u`.
* `odd_family_unique` (§3): `n + 1 = 2^r(2k+1)` and uniqueness of the 2-adic factorization.
* `covered_iff_msp2` (§16.2): every Collatz iterate is either an MSP² iterate or a skipped image
  `3v+1` with `v` an MSP² iterate; and `3v+1 < N` already forces `v < N`, so **no minimality
  argument is needed** — the skipped value can never be the only dip.

## One reading note for the authors (statement, not proof)

`tA_distance_opt2` is stated with the direction alternating with the level, and that is correct as
stated, but the reason is worth recording: the *congruence* does not alternate.  At `A = 3^(n+2)`
with `d = 2·3^n` one always has `ω · Cₙ ≡ Bₙ`, i.e. `(tA A)^[d] Bₙ = Cₙ`.  What alternates is which
of `Bₙ`, `Cₙ` the article calls the source, because `Cₙ` has two closed forms according to the
parity of `n` (`2Cₙ+1 = 3^(n+1)` vs `5·3^(n+1)`).  The Lean statement matches the article; the
asymmetry is in `cLeft`, not in the vertical rule.

## What is still open in `MSP2/`

Nothing in `src` terms: `MSP2/` has no `sorry` and no `axiom`.  The article's own open step is
`MSP2/Hypothesis.lean`'s `Raccord`, which `Headline.raccord_iff_conjecture` shows is *equivalent*
to Collatz — so it is not a formalization gap but the whole difficulty, and it stays a hypothesis.
The next real increment is the one `MSP2/README.md` already names: the definitions of the inverse
trees (§4-§7) and the Generator Table (§11-§15), so that the finer, checkable form of the open step
can be stated underneath `Raccord`.  That needs Annex A data or the authors' statement.

No successor task.
