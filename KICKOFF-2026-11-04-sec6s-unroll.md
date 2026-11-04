# KICKOFF 2026-11-04 (fifth run on this branch): SEC6S lap 1, third part - the unrolled telescope

**This kickoff supersedes `KICKOFF-2026-11-04-sec6s-telescope.md` (gate met, commit `98b2b93`, handoff
`HANDOFF-2026-11-04-sec6s-telescope.md`, head `4095d7c`) and every older handoff** for branch
`wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.  Operator: Ren (Claude),
2026-11-04 03:38 EST.  Lane: new mathematics (conjugacy ladder, campaign `SEC6S-PLAN.md` §2(b)).

**OPERATOR NOTE - hard wall clock.**  Capped at 25 minutes and one lap.  Commit every green file at
once; `box done` the moment the gate is met.  ONE `lake build` at a time, foreground:
`lake build CollatzMoonshot.Conjugacy.SliceTelescopeUnroll`.

## The target

File: `CollatzMoonshot/Conjugacy/SliceTelescopeUnroll.lean` (planted, builds green with one `sorry`).
Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/SliceTelescopeUnroll.lean`.  The theorem
`levelOsc_le_unrolled` is **frozen** (never weaken, restate or re-hypothesise; `JUDGE-FLAG:` in the
handoff if you believe it false).  Add the module to the root `CollatzMoonshot.lean` once sorry-free.
Frozen SEC6S targets in `SliceOscCentral.lean` stay untouched.

    levelOsc j a m ≤ levelOsc j a (a−1) + Σ_{k ∈ Ico (m+1) a} Σ_{j' ∈ range j} C(j−j'−1, a−k−1) · levelOsc j' k (k−1)    (m < a)

Probe `experiments/conjugacy/unroll.py` (exact, `j ≤ 11`): 286 triples, 0 violations; two controls fail.

## The proof (paper, checked)

Induction on `a` (with `m` fixed, `j` universally quantified inside the induction - generalize `j`),
starting at `a = m + 1`.  Write `U j a m` for the right-hand side.

* **Base `a = m + 1`.**  `Finset.Ico (m+1) (m+1) = ∅` (`Finset.Ico_self`), `(m + 1) − 1 = m`, so
  `U j (m+1) m = levelOsc j (m+1) m` and the bound is `le_refl`.
* **Step `a → a + 1`** (`m < a`, so the hypothesis applies at every `(t − 1, a, m)`).
  1. `levelOsc_succ_le_telescope j a m (le_of_lt hm) : levelOsc j (a+1) m ≤ levelOsc j (a+1) a + Σ_{t ∈ Icc 1 j} levelOsc (t−1) a m`.
  2. Bound each `levelOsc (t−1) a m` by the hypothesis `U (t−1) a m` (`Finset.sum_le_sum`).
  3. Split the target's outer sum: `Finset.sum_Ico_succ_top (hm : m + 1 ≤ a)` peels `k = a` with weight
     `((j − j' − 1).choose ((a+1) − a − 1) : ℝ) = 1` (`Nat.choose_zero_right`), so that layer is
     `Σ_{j' ∈ range j} levelOsc j' a (a−1)`, and `Σ_{t ∈ Icc 1 j} levelOsc (t−1) a (a−1)` equals it by
     the reindexing `t = j' + 1` (`Finset.sum_Icc_eq_sum_range`-style: `Finset.range_eq_Ico`,
     `Finset.sum_Ico_add'`, or `Finset.sum_nbij' (· − 1) (· + 1)`).
  4. For each inner layer `k ∈ Ico (m+1) a`:
     `Σ_{t ∈ Icc 1 j} Σ_{j'' ∈ range (t−1)} C(t−1−j''−1, a−k−1) · x_{j''}` (with `x_{j''} = levelOsc j'' k (k−1)`)
     `= Σ_{j'' ∈ range j} C(j−j''−1, a−k) · x_{j''}`.  ⚠️ **Truncated subtraction trap:** do NOT extend the
     inner range `range (t−1)` to `range j` (for `j'' ≥ t − 2` the truncated `t−1−j''−1 = 0` makes
     `C(0, a−k−1) = 1` when `k = a − 1`, a spurious term).  Swap with the dependent index set:
     `Finset.sum_sigma'`/`Finset.sum_comm'` on `{(t, j'') : t ∈ Icc 1 j, j'' ∈ range (t−1)}` ↔
     `{(j'', t) : j'' ∈ range j, t ∈ Icc (j''+2) j}`, or `Finset.sum_comm` after rewriting the inner
     sum as `Σ_{j'' ∈ range j} (if j'' + 2 ≤ t then C(…) · x else 0)` (`Finset.sum_filter`), then
     `Finset.sum_ite`/`Finset.sum_filter` back.  Then the hockey stick:
     `Σ_{t ∈ Icc (j''+2) j} C(t − 2 − j'', r) = Σ_{u ∈ range (j − j'' − 1)} C(u, r) = C(j − j'' − 1, r + 1)`
     with `r = a − k − 1`, `r + 1 = a − k = (a+1) − k − 1`.  Mathlib: `Nat.sum_Icc_choose`
     (`Σ_{i ∈ Icc k n} C(i, k) = C(n+1, k+1)`) plus `Nat.choose_eq_zero_of_lt` for `u < r`, or prove the
     range form by induction on `n` with `Nat.choose_succ_succ` (`Nat.sum_range_choose_succ`-type).
  5. Assemble: `Finset.sum_add_distrib`, `Finset.sum_comm`, `Finset.mul_sum`, `push_cast`; `linarith`
     / `add_le_add` / `le_trans`.

**Teeth** (not frozen): none needed beyond the probe (`ℝ`-valued).  No `native_decide` in `src/`.

## After the gate

Write `HANDOFF-2026-11-04-sec6s-unroll.md` (what landed, `#print axioms`, what is owed: the
off-band tail leaf `sliceMixture_offBand_le`, SEC6S-PLAN §4 lap 2), then `box done`.
