# Handoff: local solvability vs. global companion at u = 23

HEAD after this lap: see `git log -1`.  Branch `main`.

## What landed

`CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean`, imported from the
root module.  Both frozen statements are proved; no `sorry`, no new axiom.

* `each_prime_power_has_small_inputs_23 (p k) (hp : p.Prime)` — for every
  prime power `p^k` there are `c d : Fin 23` and `b : ℕ`, all positive, odd
  and 3-free, with
  `23*b*(3c+1)*(3d+1) ≡ 70*c*d*(3b+1) [MOD p^k]`.
* `no_global_small_inputs_23` — no such `(c,d,b)` satisfies the equation over
  `ℕ`.  Thin wrapper over `no_quadratic_cross_identity_23`.

`#print axioms`: the positive theorem is `[propext, Classical.choice,
Quot.sound]`.  The negative one additionally carries the two pre-existing
`native_decide` anchors from `BorrowabilityHeight23`
(`smallDen23_add`, `smallDen23_not_dvd`).

## Mechanism

The cross equation collapses to a single linear condition on `b`:

* `c = d = 1`  →  `79 * b = 35`
* `c = 13, d = 17`  →  `11 * b = 119`  (after cancelling `gcd = 130`)

Neither has a natural-number solution, which is what the finite obstruction
certifies.  Locally, choose the pair `(1,1)` unless `p = 79`, in which case
`(13,17)`; the leading coefficient is then coprime to `p^k`.  Substituting
`b = 5 + 6t` (resp. `b = 1 + 6t`) fixes `b ≡ 5 (mod 6)` (resp. `1 (mod 6)`),
so `b` is automatically positive, odd and 3-free, and leaves the residual
congruence `79 t ≡ -60` (resp. `11 t ≡ 18`) modulo `p^k`.  A modular inverse
is the only input: `ZMod.isUnit_iff_coprime` gives the unit, and
`ZMod.natCast_eq_natCast_iff` + `push_cast` + `linear_combination` closes the
`Nat.ModEq` goal from the `ZMod` identity.  No p-adic machinery, no imports
beyond what `BorrowabilityHeight23` already pulls in.

## The quantifier obstruction — read this before quoting the pair

The positive statement is `∀ p k, ∃ c d b, …`.  The witnesses depend on
`p` and `k`.  It does **not** say:

* that one `(c,d,b)` works for all moduli simultaneously, nor
* that every *finite joint* modulus is solvable — it is not.  A joint modulus
  already blocks all the small input pairs, by taking the lcm of all 66 positive cross denominators and using the existing finite divisibility obstruction for every pair.

So this is a bounded negative control, not a failure of CRT, and it is not
evidence that local-to-global methods fail in general.  The gap here is the
ordinary one between pointwise local solvability and a global integer
solution for a *bounded* search region, and it is bounded precisely because
`c, d < 23`.

## Next

Nothing is owed on this module.  The natural continuation is the research
note on the borrowing obstruction that this file is the control for (other
agents own that note and the experiments); do not treat this lap as opening
an optimization thread.
