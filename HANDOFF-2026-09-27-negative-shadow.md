# HANDOFF 2026-09-27 — negative-shadow obstructions formalized (task complete)

**Branch** `main`.  **HEAD at handoff** `52c6cd7` (the commit that added this
document plus the kernel weighted anchors and the research note's formalization
status); the mathematics landed one commit earlier at `3f5cd81`.  `lake build`
green, 8791 jobs.  Scoped objective `sorry-free:CollatzMoonshot/Obstructions/NegativeShadow.lean`
is met, `box done` confirmed it, and no further lap is needed for this task.

**Exact next steps: none are required.**  This bounded task is closed.  If a
later session wants to continue in this area, the only two things left are both
optional and explicitly out of the accepted scope:

1. Replace the depth-10 `native_decide` catalog facts with a kernel `decide`
   (`catalog_ten_six`, `catalog_ten_three`, `catalog_ten_increases`).  At 2^11
   words this is a performance question, not a mathematical one, and the
   architect pinned the current evaluation convention — ask before changing it.
2. Anything *new* in the negative-reference direction must first clear the gate
   stated at the end of `RESEARCH-2026-09-27-negative-shadow.md`: name the
   admissible family, say why its score is finite, say how it handles a change
   of maximizing reference, and survive both the `9 -> 14` denominator example
   and the `(1,2)`-cycle witnesses now formalized here.  The two theorems proved
   this lap are precisely what kills the two obvious candidates, so they are the
   benchmark any successor proposal has to beat, not scaffolding to extend.

Do **not** treat the sorry-free state of this module as licence to start a proof
campaign on a negative-reference mechanism; the repo's research gate in
`DIRECTION.md` is unchanged by a proved obstruction.

Bounded task `KICKOFF-2026-09-27-negative-shadow.md` is finished.  All eleven
acceptance claims are machine-checked, every pinned statement is preserved
verbatim, and `CollatzMoonshot/Obstructions/NegativeShadow.lean` contains no
`sorry` and introduces no axiom.  The module is imported from
`CollatzMoonshot.lean`; `lake build` is green (8791 jobs).

## What the mathematics now says

1. **The unweighted envelope is exactly `(n+1)^2`, unconditionally.**
   `score_le_square` is `2 ^ v2(q) <= q` (`pow_padicValNat_dvd` plus
   `Nat.le_of_dvd`) together with `q = bn + a <= a(n+1)` from `b <= a`.
   Sharpness (`exists_dyadic_ref`) takes `q = 2^k` with
   `b = 2 * ((2^k / (n+1) - 1) / 2) + 1`, the largest odd integer at most
   `2^k/(n+1)`.  The clean structural fact that makes this painless is that
   `a` and the rounding defect coincide: writing `d = 2^k - b(n+1)` one gets
   **`a = b + d` exactly**, with `0 <= d < 2(n+1)`, so the score is
   `(bc+d)^2/(b+d)^2` with `c = n+1` and no floor estimates survive into the
   analysis.  Primitivity is `gcd(a,b) | 2^k` with `b` odd
   (`Nat.eq_one_of_dvd_coprimes`).  `score_sharp_arith` is the whole epsilon
   argument as one rational inequality, and `k = (M+2)(n+1)` with
   `Nat.lt_two_pow_self` supplies `b >= M`.  No reals, no limits.
   `envelope_not_nonincreasing` then only needs LUB uniqueness plus
   `tstep 3 = 5`, `36 > 16`.

2. **The denominator-weighted score is unbounded on the genuine inverse basin
   of -1.**  `A p = 2*4^p - 3^p`, `B p = 3^p`; `B p + A p = 2^(2p+1)` is the
   engine for both admissibility and the closed weighted form
   `W = 3^p * (2^(2p+1))^2 / (A p)^2`, whence `3^p < W`.  The dynamics is the
   part the research note flagged as not being pure rational algebra, and that
   is confirmed: the proof computes the *reduced* numerator with
   `Rat.num_div_eq_of_coprime` at both steps, and the parity test splits as
   `witnessRef (p+1) --odd--> 2 * witnessRef p --even--> witnessRef p`.
   Induction on `p` gives `rationalStep^[2p] (witnessRef p) = -1`.
   `inverse_basin_scores_unbounded` is then range inclusion plus `BddAbove.mono`.

## Audit

`#print axioms` on all eleven headline declarations: only `propext`,
`Classical.choice`, `Quot.sound`.  No `sorryAx` anywhere.  The three depth-10
catalog facts (`catalog_ten_six`, `catalog_ten_three`, `catalog_ten_increases`)
additionally carry their own `native_decide` axioms — that is the pinned
convention for the finite scan and was not changed.  Everything else, including
the weighted anchors `4`, `192/25`, `9216/529` (`weighted_anchor_*`), is proved
in the kernel; the anchors come from the closed form, not from evaluation.

## Nothing is left open in this task

No target was found faulty; nothing was weakened, no range restricted, no score
replaced by its upper bound, and no helper proof lives outside the module.  The
only optional follow-up, not required by acceptance, would be replacing the
depth-10 `native_decide` catalog facts with a kernel `decide`; at 2^11 words
that is a performance question, not a mathematical one, and the architect pinned
the current convention.

Research-gate status is unchanged: these are proved *obstructions*, and per the
research note there is still no surviving bounded statement here that clears the
no-proof-lap-without-a-mechanism gate.
