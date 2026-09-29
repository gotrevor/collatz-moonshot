# HANDOFF 2026-09-29 — exact affine deformation of a quadratic exchange

**Checkpoint (graceful host stop).** Branch `main`, HEAD `1eb55cc`, working tree
clean, root `lake build` green (8817 jobs). Three commits this lap, all green and
all confined to the two files this lap owned:

| Commit | Content |
|---|---|
| `0cf7c65` | the four frozen statements |
| `c36ed96` | simultaneity criteria; my own conjecture refuted |
| `1eb55cc` | the congruence/divisibility no-go |

**Status: the scoped objective is met and the file is finished for its purpose.**
`CollatzMoonshot/Obstructions/AffineQLift.lean` holds 11 public theorems plus 5
private helpers, zero `sorry`, and `#print axioms` clean on every public theorem
(nothing beyond `propext`, `Classical.choice`, `Quot.sound`). No open obligation
remains in it, so a successor lap should pick a different node — see *Next steps*
at the bottom for what this lap ruled out, which is the part worth reading before
anyone reopens the deformation idea.

Public theorems, in file order: `affineLift_preserves_cross`,
`affineLift_smaller_inputs`, `affineLift_domain`, `liftU_shared_iff`,
`affineLift_simultaneous_shared_head`, `liftX_eq_liftU_iff`,
`affineLift_simultaneous_chained`, `affineLift_dvd`, `affineLift_mod_three`,
`affineLift_mod_six_invariant`, `affineLift_unbounded`.

Scope note: `DIRECTION.md`'s CURRENT DIRECTIVE is "awaiting a new idea; no
execution lap selected". This lap was an operator-assigned bounded node (the same
precedent as the `FrontA/TrunkBound.lean` history note in that directive), not a
launch from the deferred list, and all work stayed inside the two owned files.


## What landed

`CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair`:

- `affineLift_preserves_cross` — the deformation is *exact*, not approximate.
- `affineLift_smaller_inputs` — `liftX < liftU` and `liftZ < liftU`.
- `affineLift_domain` — positive / odd / 3-free is preserved.
- `affineLift_unbounded` — `∀ M, ∃ t, M < liftU u x t`.

## The structural identity (the whole content of statement 1)

Private factors were introduced to name the mechanism:

    F = 1 + 3(3x+1)(3u+1)t      G = 1 + 9u(3x+1)t      H = 1 + 9x(3u+1)t

Then `liftU = uF`, `liftX = xF`, `liftB = bG`, `liftZ = zH`
(`liftU_eq`, `liftX_eq`, `liftB_eq`, `liftZ_eq`), and crucially

    3·liftU + 1 = (3u+1)G        3·liftX + 1 = (3x+1)H

so the two sides of the cross-equation each factor as `F·G·H` times an
affine-in-`t` expression:

    LHS = F·G·H · [ u b (3x+1)(3z+1) + 27·u b x z (3x+1)(3u+1) t ]
    RHS = F·G·H · [ x z (3u+1)(3b+1) + 27·u b x z (3x+1)(3u+1) t ]

The `t`-linear coefficients are *literally the same monomial*, so they cancel
identically and only `hQ` remains. Mechanically: cast to `ℤ`, `push_cast`,
`linear_combination (F*G*H) * hQ'`, then `exact_mod_cast`. (`linear_combination`
needs a ring, so the `ℕ → ℤ` detour is mandatory, not cosmetic.)

## Domain preservation, factored

`mul_domain` isolates the arithmetic: if `m` is positive/odd/3-free and `M ≡ 1
(mod 6)` then so is `m*M`. Each of `F`, `G`, `H` is put in the form `1 + 6c` by
substituting `x = 2k+1` / `u = 2j+1` (available since the originals are odd —
this is where oddness of the *inputs* is consumed, via `3x+1`, `3u+1` even),
after which `omega` finishes. So `F,G,H ≡ 1 (mod 6)` and all four lifted labels
inherit the domain from their single original label.

## Calibration of novelty — read this before reusing the result

This says an isolated numeric `Q` row always sits in an infinite `t`-family, and
that the family respects the smaller-input order and the domain. It does **not**
give:

- recursive closure (the lifted row's *own* borrow obligations are untouched;
  cf. `RecursiveBorrow`),
- unit control (`UnitSupportBound` is not fed by this),
- global repair (`LocalGlobalBorrow23`'s 23-obstruction is unaffected — the
  deformation is local to one row and cannot move a global count).

Concretely: infinitude of solutions to one exchange is cheap. The obstruction
lives in the *compatibility* of several rows, and `F,G,H` deform each row by a
row-specific factor, so two rows sharing a label get incompatible `t`-scalings.
That mismatch is the next thing to formalize if anyone wants to push this: state
and refute (or prove) *simultaneous* liftability of two rows sharing `u`.

## Simultaneity: my own conjecture from earlier this lap is REFUTED

The first half of this lap ended with the conjecture that *simultaneous* lifting
of two rows sharing a label should fail, because `F`, `G`, `H` are row-specific
and two rows sharing a label would get incompatible `t`-scalings. That is wrong,
and the file now proves it wrong in both shapes that matter.

`liftU_shared_iff` (`0 < u`):

    liftU u x t = liftU u x' s  ↔  (3x+1)·t = (3x'+1)·s

`liftX_eq_liftU_iff` (`0 < x`) — the chained shape, where row two's *head* is
row one's smaller input, i.e. exactly what the smaller-input recursion produces:

    liftX u x t = liftU x x₂ s  ↔  (3u+1)·t = (3x₂+1)·s

In both cases the shared-label constraint collapses to a **single linear
Diophantine equation** in `(t,s)`, because `liftU`/`liftX` are `u`/`x` times a
factor that is affine in `t` with the shared label's own `(3·+1)` already pulled
out. A linear equation `at = bs` always has the unbounded solution family
`t = bm`, `s = am`. Hence:

- `affineLift_simultaneous_shared_head` — two rows sharing head `u` admit a
  joint deformation agreeing on `u`, with `u` unbounded and *both* cross
  equations preserved. Witness `t = (3x'+1)m`, `s = (3x+1)m`.
- `affineLift_simultaneous_chained` — same for the chain `(u,b,x,z)` then head
  `x`, matching on `x`, `x` unbounded. Witness `t = (3x₂+1)m`, `s = (3u+1)m`.

### Why this is the useful outcome

The deformation is *more* flexible than hoped, not less, and that sharpens the
calibration rather than weakening it. The exchange equations impose **one linear
condition per shared label and never an incompatibility**. So no obstruction to
recursive repair can be extracted from the quadratic exchanges themselves — at
any chain depth you can keep solving the linear matching conditions. Any real
obstruction has to live in the *borrowing and unit bookkeeping*
(`LocalGlobalBorrow23`, `UnitSupportBound`, `RecursiveBorrow`), which the
deformation does not touch: it multiplies labels by factors `≡ 1 (mod 6)` and so
cannot move a residue-class count such as the 23-obstruction.

Read negatively, this closes off a route: "deform a near-solution into a real
one" cannot fail for exchange-equation reasons, therefore it also cannot succeed
for them — the exchanges are simply not the binding constraint. Do not spend
another lap looking for an exchange-level obstruction.

## The no-go is now proved, not just conjectured

Simultaneity being unobstructed means the deformation route can only fail for
*invariance* reasons: the lifted family must carry the same data any borrow or
unit argument reads. It does, and this is now formal.

- `affineLift_dvd` — `u ∣ liftU`, `b ∣ liftB`, `x ∣ liftX`, `z ∣ liftZ`. Immediate
  from the four `liftV_eq` factorizations. So the deformation never *removes* a
  prime from a label's support; it can only scale support up.
- `affineLift_mod_three` — unconditionally, all four labels keep their class mod
  `3`, for every `t`. (Each added slope carries an explicit factor `3`.)
- `affineLift_mod_six_invariant` — if the two head labels `u`, `x` are odd (note:
  `b` and `z` need *not* be), all four labels keep their class mod `6`, for every
  `t`. Proved by writing each added slope as `6·(…)`, using `3x+1 = 2(3j+2)` and
  `3u+1 = 2(3i+2)`, then `omega`.

**The conclusion for the route.** The affine deformation is simultaneously too
flexible to be obstructed and too rigid to repair:

- too flexible — the exchange equations impose one linear condition per shared
  label and never an incompatibility (`liftU_shared_iff`,
  `liftX_eq_liftU_iff`), so there is no exchange-level obstruction to find at
  any chain depth;
- too rigid — the entire infinite `t`-family sits in one class mod `6` for every
  label, so any deficit stated in terms of residues mod `2` or mod `3` (borrow
  counts, the 3-free condition, run parity) is literally the same for every
  member of the family.

So this route cannot repair a congruence-level deficit, and this is a proof, not
an impression. `LocalGlobalBorrow23`'s global obstruction is untouched by
construction, as the file's original docstring asserted; the assertion is now
backed by `affineLift_mod_six_invariant` rather than by inspection.

## Next steps

1. This file is complete for its purpose: eleven theorems, zero `sorry`,
   `#print axioms` clean throughout. It now states both halves — the deformation
   exists and is unobstructed, *and* it provably cannot repair congruence data.
2. Do **not** spend a lap seeking an exchange-level obstruction to simultaneity
   (none exists) or hoping a cleverer `t` repairs a mod-2/mod-3 deficit (the
   invariance theorem forbids it).
3. If anyone wants to continue the deformation idea, it must be a *different*
   deformation: one whose added slope is not divisible by `6`, hence not of the
   form `orig · (1 + 6c)`. That is the only opening this lap leaves, and the
   `liftV_eq` factorizations show exactly which structure would have to be given
   up (the clean `3·liftU+1 = (3u+1)G` factorization is what forces the slope to
   be divisible by `3`).
4. Other agents own Python/docs.
