# HANDOFF — recursive borrow supply rule (2026-09-28 lap)

Scope owned this lap: `CollatzMoonshot/Obstructions/RecursiveBorrow.lean` and this
file. Nothing else touched (the `CollatzMoonshot.lean` import line was already
present from the parent's working tree).

## Status: both frozen statements proved, sorry-free

`lake build` green (8816 jobs). `#print axioms` on all three new declarations
reports only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReducibleBool` (nothing here leans on `native_decide`).

- `lowerC_recursiveH t : lowerC (recursiveH t) = 5 * recursiveX t`
  With `h = 2 + 95t`: `3689 + 6528*(2+95t) = 16745 + 620160t = 5*(3349+124032t)`.
- `five_head_pair_of_Q5_rev` — new reusable lemma. Same hypotheses as
  `five_head_pair_of_Q5`, concludes the exchange in the *opposite* direction:
  `legalPairMove [n, d] ([n,d], [5n, c])`. Proved by invoking the forward lemma
  and reusing its `certificateValue` equality symmetrically, plus re-permuting
  the positive-odd side condition. No new `certificateValue` computation, no new
  assumptions.
- `recursive_borrow_pair t : legalPairMove [x, z] ([x,z], [lowerC h, b]) = true`
  Instantiates the above at `(n,c,d) = (x,b,z)`. The `Q5` obligation
  `5b(3x+1)(3z+1) = z(15x+1)(3b+1)` is a degree-3 polynomial identity in `t`
  closed by `ring` (it comes from `b = (15x+1)/76`, `z = (15x+5)/64`; at `t=0`
  both sides are `78239555840`).
- `recursive_borrow_height t` — `x, z, b < lowerC h`, and every one of the four
  labels is positive, odd and outside `3ℕ`. All `omega` (each linear form has
  an even/3-divisible `t`-coefficient and a suitable constant residue).

## What this does and does not say

It is one symbolic *step*: on the residue subclass `h = 2 + 95t`, the pair of
strictly smaller labels `[x, z]` legally introduces the lower-family head
`lowerC h` together with the companion `b`, all three inputs/companion below
the introduced label. It does **not** assert that `x, z` are themselves in the
subclass, that they are borrowable, or that any recursion terminates. No
general Collatz claim.

## Next steps (for whoever picks this up)

1. The natural follow-on is closure: is there a `t'` with
   `recursiveX t = lowerC (recursiveH t')` (or `5 * recursiveX t'`)? That is a
   linear Diophantine question in `t, t'` and is what would turn this single
   supply rule into an actual descent, so it is the decisive next probe.
2. `five_head_pair_of_Q5_rev` is now available to any other family in
   `FiveHead.lean` (`observed*`, `lower*`) that wants the reverse orientation.
