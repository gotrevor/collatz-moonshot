# KICKOFF 2026-10-14: T1 integrality is the 2-adic code (amusical, t1arith)

Repo `collatz-moonshot-amusical-t1arith`: close every `sorry` in
`CollatzMoonshot/AmusicalExcursionCode.lean`.  (Stacked on `wip/amusical-reglue` and
`wip/amusical-ncentropy`; their sorries belong to other treadmills: leave those files alone.)

## Ratified, do not change

The five theorem statements.  No `native_decide`, no new axioms.  Lean lines ≤ 100 characters.  Do
**not** edit `RESEARCH-*.md`.  **Commit after every proved target.**

## Paper proofs (agent "t1arith"; research §42; Ren checked)

1. **`eq_amusical_of_branch`.**  Unfold `amusical`; case on `x % 4` (`Int.emod_emod_of_dvd`,
   `omega`).  `x` even: `3x ± 1` is odd, so `4y = 3x ± 1` is impossible and `y = 3x/2`.
   `x ≡ 1`: `3x` odd, `3x − 1 ≡ 2 (mod 4)`, so `4y = 3x + 1`, `y = 3(x/4) + 1`.  `x ≡ 3`:
   `3x + 1 ≡ 2`, so `4y = 3x − 1`, `y = 3(x/4) + 2`.  Likely one `omega` after `unfold; split_ifs`.
2. **`eq_amusical_of_forall_branch`.**  `funext` + 1.
3. **`defect_mod_delta`.**  `2^a (U^g p − p) − C = (3^g − 2^a) p` by `h`; `Int.ModEq` via
   `Int.emod_emod_of_dvd` / `Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p, by linear_combination …⟩)`.
4. **`gcd_offset_eq_gcd_defect`.**  `C ≡ 2^a d (mod Δ)` (3), so `gcd(C, Δ) = gcd(2^a d, Δ)`
   (`Int.gcd` is invariant under adding multiples of `Δ`).  `Δ = 3^g − 2^a` is odd for `a ≥ 1`, so
   `IsCoprime (2^a) Δ` and `gcd(2^a d, Δ) = gcd(d, Δ)` (`Int.gcd_mul_left_left_of_coprime`-style, or
   `Int.isCoprime_iff_gcd_eq_one` + `IsCoprime.gcd_mul_left_cancel`).
5. **`amusical_iterate_ge_iff_offset`.**  `2^a (U^g p − p) = (3^g − 2^a) p + C` and `2^a > 0`
   (`nlinarith` / `mul_nonneg_iff_of_pos_left`).

Notes for the next lap go in `HANDOFF-amusical-t1arith.md`.
