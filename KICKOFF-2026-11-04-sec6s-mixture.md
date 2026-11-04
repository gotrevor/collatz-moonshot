# KICKOFF 2026-11-04 (third run on this branch): SEC6S lap 1, the slice mixture identity

**This kickoff supersedes `KICKOFF-2026-11-04-beyond-words-aligned.md` (its gate is met, commit
`7895fff`; its deliverables are in `HANDOFF-2026-11-04-beyond-words-aligned.md`, head `96e4f1d`)
and every older handoff** for branch `wip/beyond-words-stretch`, worktree
`~/src/collatz-moonshot-stretch`.  Operator: Ren (Claude), 2026-11-04 03:20 EST.  Lane: new
mathematics (conjugacy ladder, campaign `SEC6S-PLAN.md`, lap 1 of §4).

**OPERATOR NOTE - hard wall clock.**  This run is capped at 40 minutes and one lap.  Commit every
green file the moment it is green; `box done` the moment the gate is met.  ONE `lake build` at a
time, foreground (the shared box memory ceiling OOM-kills a container that runs several, exit 137).
Build only what you touch: `lake build CollatzMoonshot.Conjugacy.SliceTelescope`.

## The target

File: `CollatzMoonshot/Conjugacy/SliceTelescope.lean` (planted, builds green with one `sorry`).
Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/SliceTelescope.lean`.  The theorem
`levelClass_eq_sum_levelMass` is **frozen**: never weaken, restate or re-hypothesise it (a
`JUDGE-FLAG:` in the handoff if you believe it false).  Add the module to the root
`CollatzMoonshot.lean` once sorry-free (the root runs `#barrier_audit`, which fails on an
untagged sorry, so not before).  Do not touch the frozen SEC6S targets in `SliceOscCentral.lean`.

    levelClass j a a' c = Σ_{t ∈ Icc 1 j} C(j − t, a − a' − 1) · levelMass (t − 1) a' c      (a' < a)

`levelSet j a = (range (2^j)).filter (oddCount · j = a)`, `levelMass j a y = #{r ∈ levelSet j a : T^j r = y}`,
`levelClass j a m c = #{r ∈ levelSet j a : T^j r % 3^m = c}` (`Conjugacy/Bridge3.lean`).
Exact check `experiments/conjugacy/mixture.py` / `mixture.out`: 455 triples `(j, a, a')`, `j ≤ 13`,
all `c`, 0 mismatches; the off-by-one control (weight `C(j−t, a−a')`) fails 449/455.

## The proof (paper, checked)

Conventions: `traceWord r j : List Bool` lists the parities of the first `j` steps in order
(`traceWord n (m+1) = traceWord n m ++ [parity (T^m n)]`, `FrontB/Dictionary.lean`);
`oddCount r j = ones (traceWord r j)` (`Conjugacy/Ladder.lean`);
`tstep_iterate_identity (m n) : 2^m · T^m n = 3^(ones (traceWord n m)) · n + numer (traceWord n m)`
(`FrontB/Dictionary.lean:91`); `numer_append_true/false` (`FrontB/Words.lean:71,76`);
`ones_append` (`FrontA/Paradoxical.lean:176`); `traceWord_add_mul (m) (a q) : traceWord (a + q·2^m) m = traceWord a m`
(`FrontA/OrbitPacking.lean:42`); `tstep_iterate_lt_three_pow (hr : r < 2^j) : T^j r < 3^(oddCount r j)`
(`Conjugacy/Ladder.lean:165`); `card_levelSet_eq_choose (j a) : (levelSet j a).card = j.choose a`
(`Conjugacy/SliceSeven.lean:275` - its proof carries the word ↔ start bijection; reuse that
machinery, do not re-derive it from scratch).

1. **Concatenation.**  `numer (u ++ v) = 3^(ones v) · numer u + 2^(u.length) · numer v`, by
   induction on `v` from the right (`List.append_assoc`, `numer_append_true`, `numer_append_false`,
   `ones_append_true/false`).  Equivalent form via `tstep_iterate_identity` at `m = |u|` and
   `m = |u| + |v|` with `T^{|u|+|v|} n = T^{|v|} (T^{|u|} n)` (`Function.iterate_add_apply`).
2. **Residue of a start from its suffix.**  Let `r < 2^j`, `w = traceWord r j`, `ones w = a > a'`.
   Write `w = u ++ v` where `u` ends at the `(a − a')`-th `true` of `w` (so `ones u = a − a'`,
   `ones v = a'`, `u.length = s ≥ 1`, `v.length = j − s`).  Then by `tstep_iterate_identity` and 1,
   `2^j · T^j r = 3^a r + 3^{a'} numer u + 2^s numer v ≡ 2^s numer v (mod 3^{a'})`.
   Let `r' = (T^s r) % 2^{j−s}`; then `traceWord r' (j − s) = v` (`traceWord_add_mul` at `m = j − s`
   with `T^s r = r' + q·2^{j−s}`, and `traceWord (T^s r) (j − s) = v` by the step-shift of trace words:
   `traceWord n (s + k) = traceWord n s ++ traceWord (T^s n) k`, prove it by induction on `k` if the
   repo lacks it).  So `2^{j−s} · T^{j−s} r' = 3^{a'} r' + numer v ≡ numer v`, hence
   `T^j r ≡ T^{j−s} r' (mod 3^{a'})` (cancel `2^{j−s}`, invertible mod `3^{a'}`: `Nat.ModEq` with
   `Nat.Coprime.pow`), and `T^{j−s} r' < 3^{a'}` by `tstep_iterate_lt_three_pow`, so
   `T^j r % 3^{a'} = T^{j−s} r'`.  With `t − 1 = j − s`: the residue class of `r` is the value of a
   start of the slice `(t − 1, a')`.
3. **Counting.**  Starts `r < 2^j` ↔ words of length `j` (the bijection inside
   `card_levelSet_eq_choose`).  Group the words with `a` ones and suffix-residue `c` by `s` (the
   position of the `(a − a')`-th one): the prefix is any word of length `s − 1` with `a − a' − 1` ones
   followed by `true` (`(s−1).choose (a−a'−1) = (j−t).choose (a−a'−1)` of them), the suffix is any
   word of length `t − 1` with `a'` ones whose start has value `c`, i.e. `levelMass (t − 1) a' c`
   many (bijection again at length `t − 1`).  Sum over `s = 1..j` (`t = j − s + 1`, reindex
   `Finset.sum_Icc` by `t ↦ j + 1 − t`, or state the sum over `s` first and reindex at the end).
   Edge cases are automatic: for `t − 1 < a'` the slice `(t − 1, a')` is empty and for `j − t < a − a' − 1`
   the binomial is `0`; `c ≥ 3^{a'}` gives `0 = 0` on both sides (`%` is `< 3^{a'}`, and
   `levelMass (t−1) a' c = 0` by `tstep_iterate_lt_three_pow`).
4. **Alternative if the word bijection is awkward:** induction on `j` peeling the FIRST step, with
   `tstep_iterate_add_mul`-type shift `T^{k} (r' + q 2^{k}) = T^{k} r' + 3^{oddCount r' k} q`
   (lane 7's `tstep_iterate_add_mul`, `BeyondWordsAligned.lean`) to reduce `T r` mod `2^{j−1}`;
   the `3^{oddCount} q` term vanishes mod `3^{a'}` exactly when the remaining word still has `≥ a'`
   ones, which is the case split of the recursion.  Prefer route 1-3.

**Teeth** (not frozen; add if it elaborates in under a minute): `example : levelClass 5 3 1 1 =
∑ t ∈ Finset.Icc 1 5, (5 - t).choose 1 * levelMass (t - 1) 1 1 := by decide`.  No `native_decide`
in `src/`.

## After the gate (optional, only if the clock allows; both go in `SliceTelescope.lean`)

The generic levels triangle of SEC6S §2(b): restate `TaoCollatz.osc_syracZ_levels_triangle`'s
proof for an arbitrary density on `ZMod (3^a)` and its pushforward to `ZMod (3^{a'})`, through the
bridge `levelOsc_eq_osc` (`SliceOscBridge.lean`), as `osc_levels_triangle`; then the telescope
`levelOsc j a m ≤ levelOsc j a (a−1) + Σ_{t ≤ j} C(j−t, 0) · levelOsc (t−1) (a−1) m` at `a' = a − 1`.
Leave any unproved step as a named `sorry` in a NEW declaration with a docstring, never in the
frozen one.  Write `HANDOFF-2026-11-04-sec6s-mixture.md` (what landed, `#print axioms`, what is
owed), then `box done`.
