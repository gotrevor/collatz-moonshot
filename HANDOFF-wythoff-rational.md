# HANDOFF: Wythoff rational family (`WythoffRational`, `WythoffRationalMarkov`)

Kickoff: `KICKOFF-2026-10-16-wythoff-rational.md`.  Branch `wip/wythoff-rational`.

## Status

* `CollatzMoonshot/WythoffRational.lean`: **sorry-free** (all 36 ratified lemmas, §1-§8).
* `CollatzMoonshot/WythoffRationalMarkov.lean`: in progress (Theorem M).

## Notes (for the next lap)

* `ediv_eq_iff` (bracket characterization of `Int.ediv`) + `linarith` does all floor work; linarith
  normalizes polynomial products (`(m + 1 - k) * p`) as monomials, so no manual expansion needed.
* Branch lemmas `wythoff_{plus,minus}_{even,odd}` (at `2k`, `2k − 1`) and `wythoffInv_{plus,minus}_eq`
  are the API; `even_or_odd_two_mul` splits `n`.
* `omega` treats `σ x` with `σ` a `set`-local and `evenPerm j h x` as different atoms: do not
  `set σ := evenPerm …` in proofs that end in `omega`; write `evenPerm j hj1` out.
* `field_simp` normalizes compound denominators (`2qR − q − R`) and then fails to use the `≠ 0`
  hypothesis; `generalize hD : <denominator> = D at hD0 ⊢; field_simp; subst hD; ring` works.
* Box sometimes hits "Too many open files" on `lake env lean` (host-side); retry after 60 s.
