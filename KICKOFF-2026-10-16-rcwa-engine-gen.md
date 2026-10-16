# KICKOFF 2026-10-16: the {2,3}-slope engine for r = 5^j (Lemma P, general)

Repo `collatz-moonshot-rcwa-gen` (branch `wip/rcwa-engine-gen`): close every `sorry` in
`CollatzMoonshot/RcwaEngineGen.lean`.

## Ratified, do not change

Every definition and theorem statement in `RcwaEngineGen.lean`.  No `native_decide`, no new axioms.
Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.
Notes as you go in `HANDOFF-rcwa-engine-gen.md`.  Helper lemmas welcome (above first use).  Python
checked every statement for `j = 1, 2, 3` (3,000 random engine points each, 0 failures).

## Model to copy

`CollatzMoonshot/RcwaEngine.lean` is the PROVED `j = 2` case (`20` in place of `N j`, `ZMod 25`).
Its proofs are the template: the same valuation and `ZMod` bookkeeping, with `20` replaced by
`N j` and the `decide` facts about `ZMod 25` replaced by the general facts below.

## Paper proof (Ren)

General facts (`hj : 1 ≤ j`):
* **Euler.**  `(2 : ZMod (5^j))^(N j) = 1` and `(3 : ZMod (5^j))^(N j) = 1`:
  `Nat.totient (5^j) = 4·5^(j−1)` (`Nat.totient_prime_pow`), and `ZMod.pow_totient` for units
  (`ZMod.unitOfCoprime`).
* **Order.**  `orderOf (3 : ZMod (5^j)) ∣ N j` (from Euler, `orderOf_dvd_of_pow_eq_one`), so it is
  `≤ N j`, and it is positive.  `le_orderOf_three`: with `k = orderOf 3 ≥ 1`, `5^j ∣ 3^k − 1`, so
  `5^j ≤ 3^k − 1 < 3^k`; and `3^k < 5^k`, hence... (careful: need `j ≤ k`).  Since
  `5^j ≤ 3^k − 1 < 3^k ≤ 5^k`, monotonicity of `5^·` gives `j < k + 1`, so `j ≤ k`.
* **dlog uniqueness.**  For `s < orderOf 3`, `dlog3 j (3^s) = s`: `find?` returns the least
  `k < N j` with `3^k = 3^s`; `k < s` would give `3^(s−k) = 1` with `0 < s − k < orderOf 3`.
  For any `x` with `3^k = x` for some `k < N j`, `find?` succeeds and `3^(dlog3 j x) = x`.

Then exactly as in `RcwaEngine.lean` (write `n = 2^a 3^b m`, `m` prime to 6, `s = phase j n`,
`e = a % N`, `D = (b − s) % N`):
* `phase_lt`: `find?` result `< N j` when the `InEngine` equation holds (if `find?` failed,
  `getD 0 = 0 < N j`).
* zero tests: `1 ≤ a / N ↔ N ≤ a ↔ 2^N ∣ n`; `1 ≤ (b − s)/N ↔ N + s ≤ b ↔ 3^(N+s) ∣ n`.
* step: `n' = 2^(a + Nδ₁) 3^(b + Nδ₂ + s' − s) m`, exponents `≥ 0` by `h₁`, `h₂`;
  `n' ≡ n · 2^(Nδ₁) 3^(Nδ₂) 3^(s'−s) ≡ 3^(s') (mod 5^j)` by Euler (multiply out to avoid negative
  exponents, as in `RcwaEngine`), so `phase j n' = s'` by dlog uniqueness (`hs'`) and the
  `InEngine` equation holds; counters move by `δ₁, δ₂`; junk fixed.
* `eq_of_decode_eq`: `a = N·C1 + e`, `b = phase + N·C2 + D`, `m` from the junk.
* `exists_decode`: `n := 2^(N c₁ + e) 3^(s + N c₂ + D) m` with `(e, D, m) = junk j n₀`;
  `2^e 3^D m ≡ 1 (mod 5^j)` from `n₀ ≡ 3^(s₀)`, so `n ≡ 3^s` and `phase j n = s` (`hs`).

Any cleaner route is fine as long as the ratified statements are unchanged.
