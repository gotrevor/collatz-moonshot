# KICKOFF 2026-10-13: ping-pong engine (amusical)

Repo `collatz-moonshot-amusical-pingpong`: close every `sorry` in `CollatzMoonshot/AmusicalPingPong.lean`.

## Ratified, do not change

All statements and definitions in that file (`phaseK`, `phaseB`, `RunsPingPong`, `InEngine`,
`PingPongSeed`).  Everything else in the repo is read-only; other treadmills own `AmusicalAntiKohl.lean`
and others.  Helpers go in `CollatzMoonshot/AmusicalPingPong/*.lean`.  No `native_decide`, no new axioms.
Lean lines ≤ 100 characters.

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive word check on 2026-10-13 held 16 GB for 2 h and starved every other box.  The proofs here
are valuation and residue arithmetic.

## Paper proofs (docstrings; agent report transitive.md §2.2)

1. **`amusical_not_eventually_linear`.**  If `Uᵏ x` is even for all `k ≥ N`, then
   `U^(k+1) x = 3 · (Uᵏ x / 2)`.  So `v₂` drops by one per step (`padicValInt 2`, or `emultiplicity`),
   which is impossible for `x ≠ 0` (`U` is injective and `U 0 = 0`, so `Uᵏ x ≠ 0`).
2. **`pingPong_seed_inEngine`.**  Prove a cycle lemma: from a seed with `v₅ x = A`, the next `2A + 2`
   steps are engine steps, and `σ^(2A+2) x` is a seed with `v₅ = 2A + 1`.  Track the invariants
   `(v₅, v₇, x mod 19)` step by step.
   * A-run (`j ≤ A`): `v₅ = A − j`, `v₇ = j`, phase `h · 8^j`, all in `K`.
   * Hand-off: `15x`.
   * B-run: `v₇` drops and `v₅` rises by 2; the phase stays in `B`.
   * `3x` at the end.
   * Then do strong induction on `n` (cycle lengths are positive).  Phase arithmetic: `21/5 ≡ 8`,
     `75/7 ≡ 8 (mod 19)`, and `8` has order 6.  `7 · 8^(3A+1) ≡ 1` for odd `A`.
3. **`infinitelyManyOrbits_of_pingPong`.**
   * A seed `x` with `3 ∤ x` is the first engine-forever point of its orbit.  If `σ⁻¹ x` were
     engine-forever it would be `InEngine`, and every engine image is a multiple of 3.
   * Seeds in the class `4705 mod 9975` are prime to 3.  Map each to its orbit; the map is injective
     on them, since two first points of one orbit coincide.  So the image is infinite.

Notes for the next lap go in `HANDOFF-amusical-pingpong.md`.
