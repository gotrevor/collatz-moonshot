# KICKOFF 2026-11-04 (fourth run on this branch): SEC6S lap 1, second half - the one-step telescope

**This kickoff supersedes `KICKOFF-2026-11-04-sec6s-mixture.md` (its gate is met, commit `673d399`,
handoff `HANDOFF-2026-11-04-sec6s-mixture.md`, head `d4f8ab6`) and every older handoff** for branch
`wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.  Operator: Ren (Claude),
2026-11-04 03:30 EST.  Lane: new mathematics (conjugacy ladder, campaign `SEC6S-PLAN.md` §2(b)/§4 lap 1).

**OPERATOR NOTE - hard wall clock.**  This run is capped at 30 minutes and one lap.  Commit every
green file the moment it is green; `box done` the moment the gate is met.  ONE `lake build` at a
time, foreground.  Build only what you touch: `lake build CollatzMoonshot.Conjugacy.SliceTelescopeStep`.

## The target

File: `CollatzMoonshot/Conjugacy/SliceTelescopeStep.lean` (planted, builds green with one `sorry`).
Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/SliceTelescopeStep.lean`.  The theorem
`levelOsc_succ_le_telescope` is **frozen**: never weaken, restate or re-hypothesise it
(`JUDGE-FLAG:` in the handoff if you believe it false).  Add the module to the root
`CollatzMoonshot.lean` once sorry-free, not before.  Frozen SEC6S targets in `SliceOscCentral.lean`
stay untouched.

    levelOsc j (a+1) m ≤ levelOsc j (a+1) a + Σ_{t ∈ Icc 1 j} levelOsc (t − 1) a m        (m ≤ a)

`levelOsc j a m = Σ_{y ∈ range (3^a)} |(levelMass j a y : ℝ) − (3:ℝ)^m / 3^a * levelClass j a m (y % 3^m)|`
(`Conjugacy/Bridge3.lean`).  Probe `experiments/conjugacy/telescope.py` (exact, `j ≤ 12`): 364 triples,
0 violations; the control with the first term dropped fails 332/364; the bound is attained somewhere.

## The proof (paper, checked; every step elementary)

Write `M y = levelMass j (a+1) y`, `K k c = levelClass j (a+1) k c`.

1. **Consistency of the class counts** (new lemma, same induction as `levelClass_add_succ_eq_sum`):
   `levelClass_succ_eq_sum_levelClass (hm : m ≤ a) : levelClass j (a+1) m c = Σ_{t ∈ Icc 1 j} levelClass (t−1) a m c`.
   Induction on `j`: base `levelClass_zero_succ`; step `levelClass_succ_pascal j a m c hm` and
   `Finset.sum_Icc_succ_top`.  (At `m = a` it is `levelClass_eq_sum_levelMass` + `levelClass_self`,
   but the direct induction covers all `m ≤ a` at once.)
2. **Mass mixture at `a' = a`:** `K a ȳ = Σ_{t ∈ Icc 1 j} levelMass (t−1) a ȳ` from
   `levelClass_eq_sum_levelMass j (a+1) a ȳ (by omega)` with `(a+1) − a − 1 = 0` and
   `Nat.choose_zero_right`, `one_mul`.
3. **Pointwise triangle.**  For `y < 3^{a+1}`, `ȳ := y % 3^a`, `hm : m ≤ a`:
   `y % 3^m = ȳ % 3^m` (`Nat.mod_mod_of_dvd y (pow_dvd_pow 3 hm)`), and
   `(3:ℝ)^m / 3^(a+1) = (1/3) * ((3:ℝ)^m / 3^a)` (`pow_succ`, `field_simp`).  So
   `|M y − 3^m/3^(a+1) · K m (y % 3^m)| ≤ |M y − 3^a/3^(a+1) · K a ȳ| + (1/3) · |K a ȳ − 3^m/3^a · K m (ȳ % 3^m)|`
   (`abs_sub_le`-type: write the first difference as the sum of the two, `abs_add`, `abs_mul`).
4. **Sum over `y`.**  `Finset.sum_le_sum` with 3, then `Finset.sum_add_distrib`.  The first sum is
   `levelOsc j (a+1) a` by definition (`3^a / 3^(a+1)` is literally the weight at `m := a`).  For the
   second: `Σ_{y ∈ range (3^(a+1))} g (y % 3^a) = 3 * Σ_{ȳ ∈ range (3^a)} g ȳ`.  Prove it by
   `pow_succ`/`mul_comm` and `Finset.range_eq_... `: the cleanest is
   `Finset.sum_range_succ_mul_comm`-free route: `range (3 * N)` is the image of `range N ×ˢ range 3`
   under `(ȳ, i) ↦ ȳ + i * N` (`Finset.sum_nbij'` with inverse `y ↦ (y % N, y / N)`, `Nat.div_add_mod`,
   `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`), then `Finset.sum_product`,
   `Finset.sum_const`, `Finset.card_range`.  Alternatively `Finset.sum_fiberwise` with
   `Nat.count_modEq_card`.  The factor `3` cancels the `1/3`.
5. **Subadditivity.**  With 1 and 2 (cast to `ℝ` with `push_cast`, `Finset.sum_mul`,
   `Finset.sum_sub_distrib`):
   `|K a ȳ − 3^m/3^a · K m (ȳ % 3^m)| = |Σ_t (levelMass (t−1) a ȳ − 3^m/3^a · levelClass (t−1) a m (ȳ % 3^m))|`
   `≤ Σ_t |…|` (`Finset.abs_sum_le_sum_abs`); sum over `ȳ`, `Finset.sum_comm`, and each inner sum
   is `levelOsc (t−1) a m` by definition.  Assemble with `add_le_add_left` and `le_trans`.

**Teeth** (not frozen; add if it elaborates quickly): a `decide`/`norm_num` check is awkward over
`ℝ`; instead keep the probe.  No `native_decide` in `src/`.

## After the gate (optional, only if the clock allows)

Unroll: `levelOsc j a m ≤ Σ_{k=m+1}^{a} Σ_{j'} w_k(j') · levelOsc j' k (k−1)` with explicit
binomial weights (iterate the frozen theorem; the weights are `levelClass_eq_sum_levelMass`'s).
Leave any unproved step as a named `sorry` in a NEW declaration with a docstring.  Write
`HANDOFF-2026-11-04-sec6s-telescope.md` (what landed, `#print axioms`, what is owed), then `box done`.
