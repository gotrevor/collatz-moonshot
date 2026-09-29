# HANDOFF 2026-09-29 — local-global borrow at u = 23 (scoped lap, COMPLETE)

Branch: `main`
HEAD at lap end: `fe56a13` Prove prime-power local solvability against the
global 23-borrow obstruction.
Scope was `sorry-free:CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean`.
Status: **met**; stop sentinel written via `box done --green`.

## Done this lap

`CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean` (new, imported from
the root `CollatzMoonshot.lean`).  Both statements frozen by
`KICKOFF-2026-09-28-local-global-borrow.md` are proved, no `sorry`.

* `each_prime_power_has_small_inputs_23 (p k : ℕ) (hp : p.Prime)` — for every
  prime power there exist `c d : Fin 23`, `b : ℕ`, all positive, odd and
  3-free, with `23*b*(3c+1)*(3d+1) ≡ 70*c*d*(3b+1) [MOD p^k]`.
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
* `no_global_small_inputs_23` — no such triple solves the equation over `ℕ`.
  Wraps `no_quadratic_cross_identity_23`; inherits exactly the two
  pre-existing `native_decide` anchors of `BorrowabilityHeight23`
  (`smallDen23_add`, `smallDen23_not_dvd`).  No new axiom introduced.

Root `lake build` green (8815 jobs), verified by the pre-commit hook.

## Proof mechanism (for anyone reworking it)

The cross equation collapses to one linear condition on `b`: `79*b = 35` at
`(c,d) = (1,1)`, and `11*b = 119` at `(13,17)` after cancelling `gcd = 130`.
Neither is solvable in `ℕ` — that is the global obstruction.  Locally take
`(1,1)` unless `p = 79`, else `(13,17)`, so the leading coefficient is
coprime to `p^k`.  Substituting `b = 5 + 6t` (resp. `1 + 6t`) pins
`b ≡ 5 (mod 6)` (resp. `1`), giving positivity/oddness/3-freeness by `omega`,
and leaves `79 t ≡ -60` (resp. `11 t ≡ 18`) mod `p^k`.  Solved by a unit:
`ZMod.isUnit_iff_coprime` → helper `exists_linear_sol`; then
`← ZMod.natCast_eq_natCast_iff`, `push_cast [Fin.val_mk, ZMod.natCast_val,
ZMod.cast_id]`, `linear_combination (780 : ZMod (p^k)) * ht` (resp. `12 *`).
No p-adic machinery, no imports beyond `BorrowabilityHeight23`.

## Quantifier caveat — do not over-quote this pair

The positive statement is `∀ p k, ∃ c d b, …`: the witnesses **depend on**
`p, k`.  It does not assert one `(c,d,b)` good for all moduli, nor
solvability at a finite *joint* modulus — a joint modulus already blocks
every small input pair, since `79 ∤ 35` and `11 ∤ 119` cannot both be
repaired while staying below 23.  So this is a bounded elementary negative
control, not a failure of CRT and not evidence against local-to-global
methods in general.

## Exact next steps

None are owed on this module; it is closed.  Notably **do not** treat it as
opening an optimization or generalization thread (explicit kickoff
instruction).  The write-up of the borrowing obstruction that this file is
the control for is owned by other agents, as are `experiments/`.

Repo-wide direction is unchanged and still governed by `DIRECTION.md`: the
standing objective is the run-count gap on first-crossing near-cycles, and
`DIRECTION.md` authorizes **no lap without a mechanism for the gap node**.
This scoped lap did not touch that campaign, and every `sorry` elsewhere in
the repo remains designated-open.

Working tree at lap end: clean except untracked, operator-owned
`KICKOFF-2026-09-28-local-global-borrow.md` (deliberately not committed).
