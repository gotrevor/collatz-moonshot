# KICKOFF 2026-10-14: block-swap maps (amusical, gprime)

Repo `collatz-moonshot-amusical-swap`: close every `sorry` in `CollatzMoonshot/AmusicalSwap.lean`.
(Stacked on `wip/amusical-squares`; leave other files alone.)

## Ratified, do not change

`ampSwap` and the six theorem statements.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after every proved target.**

## Paper proofs (research §45; Ren checked)

* `ampSwap_bijective`: explicit inverse `3m ↦ 2m`; `3n+1 ↦ 4n+1` (or `4n+3` if `c n`); `3n+2 ↦ 4n+3`
  (or `4n+1` if `c n`).  `Function.bijective_iff_has_inverse`; both identities by unfolding,
  `split_ifs` / `cases c n` and `omega`.
* `ampSwap_even`, `ampSwap_offset`, `ampSwap_false`: unfold, `split_ifs`, `omega` (offsets are
  `±1, ±5`; `amusical` is `if n % 2 = 0 then 3 * (n / 2) else if n % 4 = 1 then 3 * (n / 4) + 1
  else 3 * (n / 4) + 2` on `ℤ`; push casts).
* `nc_iff_pse_parent`: (→) the same `t`: `x t ≤ x s + D < x u`.  (←) take the least `t' ∈ (s, t]`
  with `x t' ≤ x s + D` (`Nat.find` on `(t' − s).toNat`); points strictly between exceed `x s + D`;
  `x t' > x s` since either `t' = t` or `s < t' < t` gives `x t' > x t > x s`.
* `next_survivor_le`: `hfut 1`, `Function.iterate_one`, `omega`.

Notes for the next lap go in `HANDOFF-amusical-swap.md`.
