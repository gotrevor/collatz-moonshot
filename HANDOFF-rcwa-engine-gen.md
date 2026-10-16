# HANDOFF: RcwaEngineGen (Lemma P for r = 5^j, any j ≥ 1)

Branch `wip/rcwa-engine-gen`.  Kickoff: `KICKOFF-2026-10-16-rcwa-engine-gen.md`.

## State (2026-10-16)

`CollatzMoonshot/RcwaEngineGen.lean` has no `sorry`.  All twelve ratified statements are proved;
`#print axioms` of each is `[propext, Classical.choice, Quot.sound]`.  No `native_decide`.
Ratified statements are unchanged: the diff against `2f89261` removes only the twelve `sorry` lines
and the `**Open.**` docstring prefixes.  Full `lake build` is green.

## Route

This is the `RcwaEngine.lean` (j = 2) proof with `20 ↦ N j`.  The single constructor
`build j e D m s c₁ c₂ := 2^(N c₁ + e) 3^(s + N c₂ + D) m` carries `build_spec`, `decode_spec`
and `scale_build`, as before.  The kernel `decide` facts about `ZMod 25` became these general
lemmas:

* `pow_N_eq_one`: Euler, via `ZMod.pow_totient` on `ZMod.unitOfCoprime` and
  `Nat.totient_prime_pow`.  `two_pow_N` and `three_pow_N` follow.
* `dlog3_lt`: `dlog3 j x < N j` always, from `List.find?_range_eq_some`.  This gives `phase_lt`
  without using the engine hypothesis.
* `dlog3_spec`: if some `k < N` has `3^k = x`, then `dlog3` is a logarithm and the least one.
  `dlog3_three_pow` then uses `pow_injOn_Iio_orderOf` and `orderOf_three_le`
  (`orderOf_le_of_pow_eq_one`).
* `not_five_dvd_of_cast`: if `n ≡ 3^s (mod 5^j)` then `5 ∤ n`, because `(5t)^j = 0` while
  `3^(sj) ≠ 0` (`three_pow_ne_zero`, from `3^N = 1` in the nontrivial ring).
* `le_orderOf_three`: `5^j ∣ 3^k − 1` with `k = orderOf 3 ≥ 1`, so `5^j < 3^k ≤ 5^k`.  This gives
  `j < k`, which is stronger than the stated `j ≤ k`.

Exponent bookkeeping with symbolic `N j`: rewrite `N δ = N (c+δ).toNat − N c`, after which `omega`
treats the products as atoms.  Counters and junk use `Nat.mul_add_div` and `Nat.mul_add_mod`.

## Next

Nothing is open in this file.  The next node is unchanged from `HANDOFF-rcwa-engine.md`: wire
Lemma P into the Theorem C reduction.  That needs a ratified statement first.
