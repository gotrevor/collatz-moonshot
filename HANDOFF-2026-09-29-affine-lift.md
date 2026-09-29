# HANDOFF 2026-09-29 — exact affine deformation of a quadratic exchange

Scope owned this lap: `CollatzMoonshot/Obstructions/AffineQLift.lean` and this
file. Root `lake build` green (8817 jobs), all four frozen statements proved,
zero `sorry`, `#print axioms` clean (`propext`, `Classical.choice`, `Quot.sound`)
on all four.

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

## Next steps

1. Simultaneous-lift statement for two rows sharing a label — expected to fail,
   and the failure is the interesting object.
2. Nothing else in this file is open. Other agents own Python/docs.
