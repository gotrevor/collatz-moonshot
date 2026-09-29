# Scoped research formalization: a symbolic smaller-input supply rule

Own only `CollatzMoonshot/Obstructions/RecursiveBorrow.lean` and
`HANDOFF-2026-09-28-recursive-borrow.md`. Parent owns all other files.
Prove the two frozen statements; build root, commit green, stop. No Aristotle.

For h=2+95t, u=lowerC(h)=16745+620160t=5x, with
x=3349+124032t, z=785+29070t, b=661+24480t.
The identity is r_(5x) r_b = r_x r_z, from
b=(15x+1)/76, z=(15x+5)/64.
Reuse five_head_pair_of_Q5 x b z to prove the forward rule, then reverse
certificate equality to construct legalPairMove in the requested direction.
Alternatively copy its certificateValue proof structure; no new assumptions.
All congruences and bounds are elementary omega/simp; cross identity ring.
This is an actual symbolic recurrence *step* on a residue subclass. It does
not assert inputs are themselves in the subclass, borrowable, or convergent.
No general Collatz claim. Host store warm and root was just built this session.
