# KICKOFF 2026-10-12: the amusical permutation (Collatz's original problem)

Exploratory lane for Trevor to play with, attended from his phone over Remote Control.

## The question

Collatz's 1930s permutation of `ℤ`, Conway's "amusical permutation":
`U(2n) = 3n`, `U(4n+1) = 3n+1`, `U(4n+3) = 3n+2`.  Is the orbit of `8` infinite?  Raised by
Klamkin in 1963 (Lagarias, arXiv:2111.02635v1, which says it "remains unsolved").  Conway
(Amer. Math. Monthly 120 (2013) 192-198; our summary `papers/2013-conway-unsettleable-summary.md`)
offers "8 lies on an infinite cycle" as his candidate for the *simplest unsettleable* statement.
Do not expect to settle it.  Aim for dents.

## Where things stand (branch `ren/amusical`, worktree `worktrees/amusical`)

`CollatzMoonshot/Amusical.lean`:
- proved: `amusical` + its three defining equations, `amusicalPerm : Equiv.Perm ℤ`,
  `amusical_orbit_eight_prefix` (first 13 steps), `amusical_small_cycles` (every cycle below 10:
  `{0}`, `{1}`, `{2,3}`, `{4,6,9,7,5}`), `amusicalOrbitOfEightInfinite_iff` (infinite ⇔ 8 never
  returns, a Π⁰₁ statement).
- open node: `AmusicalOrbitOfEightInfinite`; normality-type node `EightEvenDensityHalf`.
- `sorry` (believed ~95%, English proofs in the docstrings): `periodic_eight_even_bound`
  (a period of 8 with `e` evens satisfies `3^e 11^(p-e) ≤ 2^e 16^(p-e)`) and
  `amusicalOrbitOfEightInfinite_of_evenDensityHalf`.

Also new: `CollatzMoonshot/BackwardClosure.lean` (Lagarias's backward formulation, proved
equivalent to `Conjecture`) and `CollatzMoonshot/Literature/TerrasParity.lean` (Terras parity
bijection as a literature `Prop`, transcribed from memory: check it against Terras).

## Heuristic picture

Forward, `U` averages `(9/8)^(1/2) ≈ 1.061` per step (reads residues mod 4).  Backward, `U⁻¹`
(`3m ↦ 2m`, `3m+1 ↦ 4m+1`, `3m+2 ↦ 4m+3`) averages `(32/27)^(1/3) ≈ 1.058` (reads residues mod
3).  So the two-sided orbit of 8 should be infinite in both directions.  Python, 2026-10-12: no
return to 8 within `2·10^5` steps (5224 digits by then; drift predicts ≈5100); control: the same
loop finds the cycle `2 → 3 → 2`.

## Work, in order

0. **Prior-work sweep.**  OEIS (I believe A006368 is the permutation, ~70%), Lagarias's annotated
   bibliographies, Guy's *Unsolved Problems* (E17?), forward citations of Conway 2013, Venturini,
   Matthews.  What is known about cycles of `U`, density of finite orbits, and the orbit of 8?
   Record findings as literature `Prop`s, not prose.
1. **Close the two `sorry`s.**  Routine; keep each attempt short.
2. **Cycle structure through 8.**  `periodic_eight_even_bound` pins a cycle's even share.  Push
   toward a real dent: lower bounds on the length or the maximum of any cycle through 8, via the
   Collatz cycle toolkit (`CycleDiophantine.lean`, the Simons-de Weger m-cycle notes in
   `ON-LINE-FINDINGS-2026-08-24-simons-deweger-m-cycles.md`, linear forms in logarithms).  Name
   the mechanism before building on it, and test it on the known small cycles first.
3. **Backward drift** as a Lean node with the heuristic in its docstring.

**Out of scope: a computational record for "no return within N steps."**  Trevor is not
interested in that.

## Rules

- Statements first: every conclusion gets a Lean declaration the same turn (repo `AGENTS.md`).
- Work in `worktrees/amusical` on `ren/amusical`.  `lake build CollatzMoonshot.Amusical` (or the
  module you touched), never the whole project.  Commit green work and push `ren/amusical`.  `main` moves by
  PR (this repo is not trunk-mode); merge your own PR once CI is green.
- This is an attended, interactive lane.  Ask before any run longer than ~30 min, and propose a
  treadmill for long proof grinds instead of grinding here.
