# KICKOFF 2026-11-04: normality for `C ≤ 4`, through the stage word law

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists, the earlier 2026-11-04 kickoffs and
every older `HANDOFF-*.md` for this branch** (`wip/orbit-word-law`, worktree
`~/src/collatz-moonshot-orbitwords`).  Operator: Ren (Claude), 2026-11-04.  Lane: new mathematics.

## The target

File: `CollatzMoonshot/Conjugacy/OrbitStageLaw.lean` (planted, one `sorry`).

    theorem stageWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : StageWordLaw C

`StageWordLaw`, `BadStart`, `WindowMatch` and `normal_iff_le_four` are frozen.  Never weaken, restate or
re-hypothesise.  Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/OrbitStageLaw.lean`.  **Keep every
leaf `sorry` in this file**, siblings carry none.  Settling instrument: `#print axioms normal_iff_le_four`.  Build
only what you touch; never `lake update`; never `git add -A`.  Commit after each green lemma.

## The argument

Read `RESEARCH-2026-11-04-affine-mixing.md` §7, and `~/personal/papers/inselmann-2024-approximation-collatz-stopping-time.pdf`
if the path is visible (Lemmas 2.13-2.16; otherwise §7 is enough).  **No mixing, no Fourier, no `TaoCollatz`.**  A proof
that reaches for Tao's stabilisation has gone wrong.

Call `B ⊆ ℕ` *power-sparse* if `|B ∩ [1, X]| ≤ X^(1−D)` for all large `X`, some `D > 0`.  Natural density `0` follows.

- **P1, Terras events are power-sparse.**  Let `S₀(u, δ, η)` be the `m` whose first `size m` letters have, on every
  prefix (or window) of length `≥ η size m`, the right frequency of `u` and of the letter `1`, within `δ`.  The
  complement is power-sparse.  `CardMatchSet_holds`, in `OrbitWordLawTerras.lean`, is the exact independence.  You
  need **exponential** concentration, `2^(−D k)`, not Chebyshev: Hoeffding or a direct binomial tail on `|u|`-spaced
  subsequences (split `u`-occurrences by offset mod `|u|`, so that each class is independent).  Mathlib has
  `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` in `Probability/Moments/SubGaussian.lean`, with the counting
  measure; a hand-rolled exponential moment over `Finset.range (2^m)` may well be shorter.

- **P2, pullback.**  If `B` is power-sparse, so is `{m : T^(⌊log₂ m⌋) m ∈ B}`.  Let `k = ⌊log₂ m⌋`, `a` the odd
  letters among the first `k`, `M = T^k m`.  Then `2^k M = 3^a m + 2^k · offset`, `offset ≥ 0`.  Off a power-sparse set,
  `k/4 ≤ a ≤ 0.6 k` and `offset ≤ 2^(ε k)`: each term of the offset is `3^c / 2^(ℓ+1)` with `c` the odd letters in a
  suffix of length `ℓ`, so long suffixes (controlled by P1's windows) give terms below `1`, and suffixes shorter than
  `ε′ k` give at most `(3/2)^(ε′ k)`.  Given `M` and `a`, `m` lies in an interval of length `≤ offset · 2^k / 3^a`, and
  `M < 3^(a+1)`.  Hence

      #{good m ∈ [2^k, 2^(k+1)) : M ∈ B} ≤ Σ_a |B ∩ [1, 3^(a+1)]| (2^(εk) 2^k / 3^a + 1) ≪ k 2^(k + εk) 3^(−kD/4),

  using `3^a < 2^k` (`a ≤ 0.6 k`) to absorb the `+ 1`.  Take `ε ≪ D`.  Note the `a`-sum is scale-invariant, so `a` need
  only be bounded away from `0`.  This is the crux; state it as a standalone lemma.

- **P3, the windows.**  `S_(j+1) = S₀ ∩ {m : T^(⌊log₂ m⌋) m ∈ S_j}`, power-sparse complement by P1 and P2, for finitely many
  `j`.  For `m ∈ S_J`, put `M₀ = m`, `M_(j+1) = T^(⌊log₂ M_j⌋) M_j`, `t_j` the cumulative times.  `height_identity` (lower
  bound only, `heightCorr_nonneg`) with the letter-`1` frequency gives `size M_(j+1) ≥ (θ − ε′) size M_j`, `θ = log₂ √3 = 0.7925`.
  Windows cover `(1 + θ + … + θ^(J−1) − O(ε′)) size m` letters.  **`J = 9` gives `4.225`** and `J = 8` only `4.069`:
  use `J = 9`.  Measured at `k = 4000`: `t_9 / k = 4.231`.  Sum the window counts with `wdev_add`, `wdev_shift`; `J |u|` boundary
  letters are absorbed.  Take `δ` small in terms of the target tolerance and `J`.

- **P4, assembly.**  `BadStart C u δ m` with `C ≤ 4` and `m ∈ S_J` large is impossible.  Note that `BadStart` counts `i` with
  `i + |u| ≤ C size m`, `WindowMatch`, against `(C size m) 2^(−|u|)`, tolerance `δ size m`.  No separate even reduction
  should be needed, since Terras holds for even starts too (check this; `⌊log₂ m⌋` and `Nat.size` differ by one, so mind
  the conventions).  A power-sparse complement gives `Tendsto` for `StageWordLaw` over `[2^(k−1), 2^k)`.

**Stop and report if a step is structural**: say which, with the arithmetic, in the handoff.  Do not work around it by
weakening.  Decomposing into named sub-`sorry`s in `OrbitStageLaw.lean` is progress.

## How to build it

New siblings `OrbitStageLaw*.lean`, imported by `OrbitStageLaw.lean`.  Reuse `height_identity`, `CardMatchSet`,
`wdev_add`, `wdev_shift`, `wcnt_true_eq_oddCount`.  Grep `def <name>` under `Conjugacy/` before naming: clashes appear only at
the root import.  No `native_decide`, no `axiom`, no new `maxHeartbeats`.

Check `#print axioms` from `/tmp`, with a `sorry` control.

Wording in the repo: true statements with weights, no claims of priority; cite Inselmann for the pullback.  Write your state to
`HANDOFF-2026-11-04-stage-word-law.md` before each lap ends.
