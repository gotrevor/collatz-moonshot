# KICKOFF 2026-10-16: the {2,3}-slope counter-machine engine, Lemma P (research §55-§57)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/rcwa-engine`): close every `sorry` in
`CollatzMoonshot/RcwaEngine.lean`.

## Ratified, do not change

Every definition and theorem statement in `RcwaEngine.lean`.  No `native_decide`, no new axioms.
Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.
Notes as you go in `HANDOFF-rcwa-engine.md`.  Helper lemmas welcome (above first use).  Python
checked all statements on 20,000 random engine points (0 failures).

## Paper proof (Ren)

Write `n = 2^a 3^b m`, `m` prime to 6 (`a = v2 n`, `b = v3 n`, `m = n / (2^a 3^b)`, exact; use
`padicValInt` API: `Int.pow_padicValInt_dvd`-style lemmas, or factor via `multiplicity` /
`Int.emultiplicity`; `padicValInt.mul`, `padicValInt.self_pow` style lemmas for products).

* **`dlog3` / `phase_spec`.**  `3` has order 20 in `(ZMod 25)ˣ`; the 20 powers `3^k`, `k < 20`, are
  exactly the units.  `n` prime to 5 ⇒ `(n : ZMod 25)` is a unit (or: `≠ 0, 5, 10, 15, 20`), so
  `find?` succeeds and returns `k < 20` with `3^k = n`.  A clean route: prove
  `∀ x : ZMod 25, (∀ k < 20, 3^k ≠ x) → 5 ∣ x.val` by `decide`, and for `List.find?` use
  `List.find?_some` / `List.find?_eq_none`.  Also useful: `dlog3 ((3 : ZMod 25)^s) = s` for
  `s < 20` (`decide` over `Fin 20`), and `(2 : ZMod 25)^20 = 1`, `(3 : ZMod 25)^20 = 1` (`decide`).
* **`one_le_C1_iff`.**  `1 ≤ a/20 ↔ 20 ≤ a ↔ 2^20 ∣ n` (`padicValInt_dvd_iff` /
  `pow_dvd_iff_le_padicValInt`-style, `n ≠ 0`).
* **`one_le_C2_iff`.**  `1 ≤ (b − s)/20 ↔ 20 + s ≤ b` (as `s ≤ b` on the engine) `↔ 3^(20+s) ∣ n`.
* **Step.**  Let `s = phase n`, `C₂ = (b − s)/20`, `D = (b − s) % 20`, `e = a % 20`.  With `h₁`:
  `a + 20δ₁ = 20(C₁ + δ₁) + e ≥ 0`.  With `h₂`: `b + 20δ₂ + s' − s = 20(C₂ + δ₂) + D + s' ≥ s' ≥ 0`.
  So `n' := 2^{a + 20δ₁} 3^{b + 20δ₂ + s' − s} m` is an integer and equals `scale n …`
  (the division in `scale` is exact: `n · 2^{A⁺} 3^{B⁺} = n' · 2^{A⁻} 3^{B⁻}`; `scale_spec`).
  Then `v2 n' = a + 20δ₁`, `v3 n' = b + 20δ₂ + s' − s`, `n' / (2^{v2} 3^{v3}) = m`;
  `n' ≡ n · 2^{20δ₁} 3^{20δ₂} 3^{s' − s} ≡ 3^s · 3^{s'−s} = 3^{s'} (mod 25)` (as `2^20 ≡ 3^20 ≡ 1`;
  avoid negative exponents by multiplying out: `n' · 2^{A⁻} 3^{B⁻} = n · 2^{A⁺} 3^{B⁺}` in
  `ZMod 25`, where `2, 3` are units), so `phase n' = s'` by `dlog3 (3^{s'}) = s'`.  Hence
  `InEngine n'` (`v3 n' ≥ s'`, `5 ∤ n'` as `5 ∤ m`, `n' ≠ 0`), `C1 n' = C₁ + δ₁`,
  `C2 n' = C₂ + δ₂`, and the junk `(e, D, m)` is unchanged.
* **`eq_of_decode_eq`.**  `a = 20·C1 + e`, `b = phase + 20·C2 + D`, `m` from the junk, and
  `n = 2^a 3^b m`.
* **`exists_decode`.**  With `(e, D, m) = junk n₀`, take `n := 2^{20c₁ + e} 3^{s + 20c₂ + D} m`.
  Mod 25: `n ≡ 2^e 3^D m · 3^s`, and from `n₀ ≡ 3^{s₀}` with `n₀ = 2^{20C₁⁰+e} 3^{s₀+20C₂⁰+D} m`
  we get `2^e 3^D m ≡ 1`, so `n ≡ 3^s` and `phase n = s`.  The rest as in the step.

Any cleaner route is fine as long as the ratified statements are unchanged.
