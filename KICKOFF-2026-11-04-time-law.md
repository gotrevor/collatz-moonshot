# KICKOFF 2026-11-04: the time law

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists, the earlier 2026-11-04 kickoffs and
every older `HANDOFF-*.md` for this branch** (`wip/orbit-word-law`, worktree
`~/src/collatz-moonshot-orbitwords`).  Operator: Ren (Claude), 2026-11-04.  Lane: new mathematics.

## The target

File: `CollatzMoonshot/Conjugacy/OrbitTimeLaw.lean` (planted, two `sorry`s): `timeLaw_upper`, `timeLaw_lower`.
Both statements, and every def they use, are frozen.  Never weaken, restate or re-hypothesise.  Host gate:
`--done-when sorry-free:CollatzMoonshot/Conjugacy/OrbitTimeLaw.lean`.  **Keep every leaf `sorry` in this
file**, siblings carry none.  Settling instrument: `#print axioms timeLaw_upper`, `timeLaw_lower`.  Build only
what you touch; never `lake update`; never `git add -A`.  Commit after each green lemma.

## `timeLaw_lower`

Short: `firstPassage_sharp` with `θ = min (1/2) (β ε / 2)`, so `1/β − ε ≤ (1−θ)/β − ε/2`, plus the bounded set
where `f n > n^θ` fails, through `logDens0_of_bdd`.  Do it first.

## `timeLaw_upper`: the argument

Fix large `X`.  For a start in the window at scale `x`, take `x_j = x^(α^(−j))` for `j ≤ J(x)`, `J(x)` the last
with `x_j ≥ X`.  `J(x)` grows, so `numScales` and `GoodOddUpTo`'s fixed `J` cannot be reused as they stand.
What replaces the fixed-`J` `Tendsto`s is **rates**, and they exist:

1. **The chain error.**  `dTV_chain_step` already has `C_stab * log(x_(j+1))^(−c_stab)`.  Summing,
   `dTV_j ≤ ∑_(i≤j) C log(x_i)^(−c) ≤ C′ log(x_j)^(−c)`, geometric since `log x_i = α^(−i) log x`.
2. **The stage events.**  `card_not_winGood_le` and `probPeriodicLe` give `O_(u,δ,η)(1 / log x)` at one scale
   for fixed `δ, η` and a fixed number of blocks (`OrbitWordLawWhp.lean`; the handoff formula is
   `64 K²|u|/(δ²(2Λ+1)) + K 2^(−M)`).  State a rate version of `winGoodWhp` / `locGood_whp`, with `u = [true]`
   at tolerance `1/100` and fixed `η`.  `LocGoodPassLoc`'s `X₀` is fixed, so `x_j ≥ X ≥ X₀` is all it needs.
3. **The union.**  Over `j ≤ J(x)`, `∑ (1 / log x_j + log(x_j)^(−c)) ≤ g X`, `g X = C″ log(X)^(−c′) → 0`,
   again geometric, dominated by the last scale.  Also `stabilization_atCX`'s first clause bounds
   `¬ passes`, at rate `C_stab x^(−c_stab)`.
4. **The time.**  Choose `θ` small.  Through `N^θ`, use the height line (`goodOddUpTo_of_stages` or
   `heightLawBelowThreshold`): about `(1 − θ) size N / β` steps.  Below `N^θ`, the `[true]` tolerance `1/100`
   makes each stage take `≤ c log₂ x_j` letters (as `StagePasses` does) with `c` absolute, so the rest totals
   `≤ c′ θ size N`, geometric again.  Take `c′ θ < ε / 2`.
5. **Density.**  For the odd bad set with target `g m := ⨅_(n ≥ m) f n` (monotone, `→ ∞`, and `g m ≤ f n` for
   `n ≥ m`): for every `X`, eventually `g ≥ X`, so the window probability of the bad set is `≤ g X + o_x(1)`.
   That is `Tendsto … (𝓝 0)`, so `logDens0OfWindow_holds` applies.  Then `logDens0OddPart_holds`,
   `summableLargeTwoAdic_holds` and the even reduction, as in `heightLawUpTo_of_one_le`: `2^a m` spends `a`
   steps on zeros, and `a ≤ ε′ size m`.  `f` may be negative near `0`; only large `n` matters.

**Stop and report if a step is structural**: say which one, with the arithmetic, in the handoff.  In particular,
if some `o(1)` you need a rate for hides a non-uniform constant, that is a real finding.  Do not work around it
by weakening.  Decomposing into named sub-`sorry`s in `OrbitTimeLaw.lean` is progress.

## How to build it

New siblings `OrbitTimeLaw*.lean`.  Rate versions are new theorems beside the old.  You may generalise in place
only if every existing named theorem keeps its statement, and `orbitWordLaw_of_le_four`,
`logNormal_iff_le_four`, `heightLawBelowThreshold`, `firstPassage_sharp` still build.  Grep `def <name>` under
`Conjugacy/` before naming: clashes appear only at the root import.  No `native_decide`, no `axiom`, no new
`maxHeartbeats`.

Check `#print axioms` from `/tmp`, with a `sorry` control.  Numbers: `experiments/conjugacy/time_law.py` (`.out`).

Wording in the repo: true statements with weights, no claims of priority.  Write your state to
`HANDOFF-2026-11-04-time-law.md` before each lap ends.
