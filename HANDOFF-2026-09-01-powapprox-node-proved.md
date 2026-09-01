# HANDOFF 2026-09-01 (later) — the last `src/` sorry PROVED; Front-A paradoxical closer is trust-base clean

## State (end of lap)
- Branch `main`, working tree clean after this commit (nothing pushed; host pushes).
- `lake build` 🟢 **8765 jobs**.  `scripts/check-proof-debt.sh` → **0 disclosed sorries**.
- Real `#print axioms` (this HEAD):
  - `FrontA.two_pow_approx_three_pow_from_above` → `[propext, Classical.choice, Quot.sound]`
  - `Assumed.rozier_terracol_3_2` → `[propext, Classical.choice, Quot.sound]`
  - `finite_acyclicParadoxical_imp_noDivergent` → `[propext, Classical.choice, Quot.sound]`
  - `diverges_imp_infinite_acyclicParadoxical` → `[propext, Classical.choice, Quot.sound]`
- **The `DIRECTION.md` CURRENT DIRECTIVE (discharge `rozier_terracol_3_2`, make the Front-A
  paradoxical closer trust-base clean) is COMPLETE.**  DIRECTION.md itself is altitude-only; an
  altitude lap should retarget it.

## Kickoff-instruction triage (this lap's first decision)
The session kickoff described the `sep_two_three` ↔ `rhinLiteLIMeasure` fork with operator
points (1)–(3).  That fork was already resolved at `d21f006` (see
`HANDOFF-2026-09-01-rhin-axiom-retired.md`): direct re-wiring refuted for exactly point (1)
(`N₀` classical, `c` opaque); explicit constants built (`N₀ = 0`, `κ = 436`, `K = 141000`,
convergent brackets per point (2)); κ-sharpening refuted as low-leverage (point (3)).  The
"in passing" staleness items (README, `RhinLiteApprox.lean` header) were also already fixed.
So the lap went to the newest handoff's START HERE: the PowApprox node.

## What landed — `FrontA/PowApprox.lean`
`∀ M N, ∃ A s, M < A ∧ 3^A < 2^s ∧ (2^s − 3^A)·N ≤ 3^A`, proved **without** logarithms,
irrationality of `log₂3`, Dirichlet, or `native_decide`:
- `three_pow_ne_two_pow_of_pos` — parity.
- `exists_mul_box` — `(1, 2]` covered by `N` multiplicative boxes `((1+1/N)^j, (1+1/N)^(j+1)]`
  (Bernoulli `one_add_mul_le_pow`, `Nat.find`).
- `exists_two_pow_three_pow_ratio_close` — pigeonhole on `A = i(M+1)`, `i ≤ N`, with
  `q A = 2^(⌊log₂3^A⌋+1)/3^A ∈ (1,2]`; a collision gives `a > M`, `b` with both `2^b/3^a` and
  `3^a/2^b` below `1 + 1/N`.
- `approx_from_above_of_ratio_close` — the side-fixing flip: least `u` with `(3^a/2^b)^(u+1) ≥ 2`
  gives `2^(ub+1)/3^(ua) ∈ (1, 3^a/2^b]`.
- `two_pow_approx_three_pow_from_above` — assembly (`N = 0` trivial).
Docs de-staled: `Assumed/Paradoxical.lean` header + docstrings, README, STATUS (banner, ledger
table, short-term list), `PENDING_WORK.md` (new top section + old NEXT ATTACK marked done),
`scripts/check-proof-debt.sh`, `scripts/AxiomAudit.lean` (+3 declarations).

## What remains in the repo (no `sorry` anywhere)
- Hygiene: 13 `native_decide` certificates under `sep_two_three` / the two-block exclusion.
- Cited axioms: `hercher_min_circuit_count`, `hercher_odd_members_bound`,
  `eliahou_min_cycle_length`, `collatz_verified_up_to_two_pow_68`, `collatz_verified_barina_2025`,
  `tao_2019_almost_bounded`, `abc`, `baker_bounded_difference`.
- Open hypotheses of the conditional closers: `FiniteAcyclicParadoxical`, `ParityRigidityW1'`,
  `Compression`.

## Gotchas (corpus-worthy)
- `mul_lt_mul_left` is now the *ordered-monoid* lemma (needs `MulRightStrictMono`, which ℝ
  lacks); for `0 < c → c*a < c*b ↔ a < b` in a field use `lt_of_mul_lt_mul_left h hc.le` /
  `mul_lt_mul_of_pos_left`, or `mul_lt_mul_iff_of_pos_left` (alias of `mul_lt_mul_iff_right₀`).
- `gcongr` on `c * x < c * y` in ℝ can fail with "failed to synthesize MulRightStrictMono ℝ"
  when the goal is a `calc` step whose sides are not syntactically `c * _`; give the lemma
  explicitly.
- `push_neg` is deprecated (prefer `push Not`); `not_le.1` / `not_lt.1` avoid the warning.
- `field_simp` now often closes `x * N = y * (N + 1)`-style goals outright; a trailing `ring`
  then errors with "no goals".
- `simpa using h` normalises `1 / N` to `N⁻¹`, which breaks a later `exact` against a
  statement written with `1 / N`; restate with `rw [mul_one]` instead.
- `one_add_mul_le_pow (H : -2 ≤ a) n : 1 + n * a ≤ (1 + a)^n` — the hypothesis is not a
  `positivity` goal; derive `0 ≤ a` and `linarith`.

No in-flight Aristotle job.
