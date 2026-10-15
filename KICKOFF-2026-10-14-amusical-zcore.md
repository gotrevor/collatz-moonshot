# KICKOFF 2026-10-14: periodic U-invariant functions are constant (Theorem Z core)

Repo `collatz-moonshot-amusical-zcore`: close every `sorry` in
`CollatzMoonshot/AmusicalPeriodicInvariant.lean`.

## Ratified, do not change

The two theorem statements.  No `native_decide`, no new axioms.  Lean lines ≤ 100 characters.  Do
**not** edit `RESEARCH-*.md`.  **Commit after every proved target.**  Write notes to disk as you go.

## Paper proofs (Ren checked)

1. **`periodic_invariant_const`.**  Fix `n`; let `v = f n` and `R = {r : ZMod M | f r.val = v}` (use
   `hper` to show `f k` depends only on `(k : ZMod M)`; `ZMod.intCast_cast`, `Int.emod_emod_of_dvd`,
   induction on the quotient).  The set `{k : ℤ | (k : ZMod M) ∈ R} = {k | f k = v}`.  Since
   `f ∘ U = f` and `U` is a bijection of `ℤ` (`amusicalPerm`), `U '' {f = v} = {f = v}`.  Apply
   `amusical_pow_classUnion_invariant 1 M` (`AmusicalSeventh.lean`): `R = ∅` or `R = univ`; `R ∋ n`,
   so `R = univ` and `f m = v`.
2. **`periodic_eventually_invariant_const`.**  `U (n + 4M) = U n + 3M` or `U n + 6M` (even branch
   `3(n+4M)/2 = 3n/2 + 6M`; odd branches `+ 3M`), so `n ↦ f (U n)` is `4M`-periodic, as is `f`.  For
   any `n`, choose `k` with `|n + 4Mk| ≥ N` (`k = N + |n|` works); then `f (U n) = f (U (n + 4Mk)) =
   f (n + 4Mk) = f n`.  Now apply 1.

Notes for the next lap go in `HANDOFF-amusical-zcore.md`.
