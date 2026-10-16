# HANDOFF: RcwaEngine (Lemma P, research §55-§57)

Branch `wip/rcwa-engine`.  Kickoff: `KICKOFF-2026-10-16-rcwa-engine.md`.

## State (2026-10-16)

`CollatzMoonshot/RcwaEngine.lean` is sorry-free.  All eleven ratified statements are proved;
`#print axioms` of each is `[propext, Classical.choice, Quot.sound]`.  No `native_decide`.
Ratified statements unchanged (the diff against `1f875b6` removes only `sorry` lines and the
`**Open.**` docstring prefixes).  Full `lake build` green.

## Route

One constructor carries everything:
`build e D m s c₁ c₂ := 2^(20c₁ + e) · 3^(s + 20c₂ + D) · m`.

* `build_spec`: for `e, D, s < 20`, `m` prime to 6 and the **unit condition**
  `2^e 3^D m = 1` in `ZMod 25`, the point is in the engine with phase `s`, counters `(c₁, c₂)`
  and junk `(e, D, m)`.  (`¬5 ∣ m` is not needed separately: it follows from the unit condition.)
* `decode_spec`: every engine point `n` is `build (junk n) (phase n) (C1 n) (C2 n)`, and its junk
  satisfies the unit condition (cancel `3^phase` via `three_pow_cancel`).
* `scale_build` / `build_mul_eq`: `scale (build … s c₁ c₂) (20δ₁) (20δ₂ + s' − s)` is
  `build … s' (c₁+δ₁).toNat (c₂+δ₂).toNat`; the exponent bookkeeping is one `omega` per prime.

Then the step lemmas, `eq_of_decode_eq` and `exists_decode` are one-liners off these.
Valuations go through `padicValInt_pow_mul` (`v_p(p^a k) = a` for `p ∤ k`, from
`padicValInt_dvd_iff` both ways).  The `ZMod 25` facts (`dlog3_spec`, `dlog3_three_pow`,
`five_mul_three_pow_ne`, `3^20 = 2^20 = 1`) are kernel `decide`, each well under a second.

## Next

Nothing open in this file.  The next node is wiring Lemma P into the Theorem C reduction
(counter-machine halting ⇒ orbit counting for `2^ℤ 3^ℤ`-slope RCWA permutations); that needs a
ratified statement first, not in this kickoff's scope.
