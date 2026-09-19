# DIRECTION — collatz-moonshot

## Attended operator override: 2026-09-18 late - one Opus-low residue-swap helper

Trevor requested continuation and permits Opus-low helpers.  One bounded lap only.
Create `CollatzMoonshot/FrontA/FirstCrossingSwaps.lean`, importing FirstCrossing.
Do not change any existing theorem or definition.  Parent owns the experiment script;
your only files are this new module, its root import, and your short dated handoff.
Do not edit DIRECTION or experiments.  No successor task and no Aristotle.

Freeze these mathematical targets (namespace FirstCrossing, open FrontB):

1. `numer_adjacent_swap (u w : List Bool)`:
   `numer (u ++ [false,true] ++ w) = numer (u ++ [true,false] ++ w) +
      2 ^ u.length * 3 ^ ones w`.
2. `residue_adjacent_swap {x y m : Nat} (u w : List Bool)` with
   `hx : traceWord x m = u ++ [true,false] ++ w` and
   `hy : traceWord y m = u ++ [false,true] ++ w`:
   `3 ^ (ones u + 1) * y + 2 ^ u.length ≡
      3 ^ (ones u + 1) * x [MOD 2 ^ m]`.
   This is suffix-independent, with no first-crossing assumption needed.
3. Define `NumeratorAntitoneResidue : Prop` as
   `∀ x y m : Nat, 2 ≤ x → 2 ≤ y → x < 2^m → y < 2^m →
       At x m → At y m →
       numer (traceWord x m) ≤ numer (traceWord y m) → y ≤ x`.
   Prove `numeratorAntitoneResidue_false : ¬ NumeratorAntitoneResidue`.
   Hand-checked anchor: x=95,y=175,m=8, words 11111000 and 11110100,
   numerators 211 and 227; both first-crossing, but 175>95.

Proof route: induct on u for the numerator swap; both suffixes have equal odd counts.
Subtract the two affine iterate identities modulo 2^m; use the numerator swap,
factor 3^(ones w), and cancel this unit.  Reuse the Nat.ModEq cancellation pattern
in ParityReconstruction.traceWord_eq_imp_modEq.  The remaining expression is exactly
the frozen residue identity, with the displayed orientation (plus 2^len u on y).

Build, inspect dependencies of the three named results, commit, then `box done --green`.
If a frozen target fails, report the mathematical counterexample; do not weaken it.
This gives local residue transport and refutes monotonicity.  It does NOT prove CST.

## Attended operator override: 2026-09-18 - first-crossing helper COMPLETE

Completed at `94076e2`, handoff checkpoint `792fee0`, with a successful host build.
`FirstCrossingCycles.noNontrivialCycle_of_stoppingCorrect` has the frozen target.
No successor lap is authorized by this directive; do not fall through to an old
dated override below.  The two open inputs remain `StoppingCorrect` and `CrossingExists`.
The parent also proved the first-crossing numerator bound in `FirstCrossing.lean`
and added exact first-crossing geometry/null-baseline diagnostics to
`experiments/parity_reconstruction.py first-crossing 501`.
Research rationale and next gate: the 2026-09-18 headline blueprint and
`moonshot-first-crossing-carry-audit-2026-09-18.md` in the personal KB project leaves.

Original bounded task, preserved for provenance:

Trevor authorized Opus-low helpers in this session.  This is a bounded formalization task,
not permission to attack CST or the Collatz conjecture.  Parent Ren owns the analytic work
outside this repository and will not edit this tree during the helper lap.

**Frozen inputs:** `FrontA.FirstCrossing.At`, `StoppingCorrect`, `CrossingExists` and all
statements in `FrontA/FirstCrossing.lean`.  Do not change their definitions or statements.

**Single target**, in new `CollatzMoonshot/FrontA/FirstCrossingCycles.lean`:

```lean
namespace CollatzMoonshot.FrontA.FirstCrossing
theorem noNontrivialCycle_of_stoppingCorrect
    (h : StoppingCorrect) : CollatzMoonshot.NoNontrivialCycle := by
  -- prove; do not weaken the statement
end CollatzMoonshot.FrontA.FirstCrossing
```

Proof route: a nontrivial cycle has an orbit minimum greater than 2 in shortcut
coordinates.  Its full period is subcritical by the affine identity and positive numerator.
`exists_first_crossing` supplies a first crossing there; `h` gives a descent below
the minimum, contradiction.  Reuse the existing cycle/minimum and map-dictionary lemmas.

Scope: the new module, its root import, and a short dated handoff.  Do not modify other
research modules, old open nodes, citation axioms, or this override.  If the proof exposes a
missing hypothesis, explain it rather than changing the target.  A finite counterexample
would also settle this task, but no empirical check substitutes for the general implication.

Build and check the named theorem's dependencies, commit the completed proof, then
`box done --green`.  One lap only; do not select a successor.  Report the mathematical
implication and any genuine blocker, not a sorry-count metric.

## Attended operator override: 2026-09-16 00:25 EDT — NODE 4, the Eliahou bound at OUR frontier (ACTIVE for this run only; nodes 1–3 DONE at `073b0d2`, host-verified, pushed)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  Same lane (formalizing a known method at a new parameter; no new mechanism).
Hard stop: host kills laps at 05:25 EDT - skeleton with named `sorry` leaves first.  Reconcile
with `git log` and `HANDOFF-2026-09-16-eliahou-axiom-discharged.md` before acting.

🎯 **Node 4.**  Node 3's `FrontB.Eliahou` machinery, re-run with the Farey pair that straddles the
interval `(log₂3, log₂(3 + 2^{−68}))` instead of the 1993 pair.  Host computation
(`mpmath`, 60 digits, Stern–Brocot walk, 2026-09-16 00:20):

```
c₁ = 103768467013 / 65470613321  <  log₂ 3  <  e/a  <  log₂(3 + 2^{−68})  <  c₂ = 10439860591 / 6586818670
65470613321·10439860591 − 103768467013·6586818670 = 1        (Farey neighbours)
q₁ + q₂ = 72057431991 ;  the least-denominator fraction inside is 114208327604 / 72057431991
log₂3 − c₁ ≈ 1.02·10⁻²² ;  c₂ − log₂(3+2^{−68}) ≈ 5.88·10⁻²² ;  interval width ≈ 1.63·10⁻²¹
72057431991 · log₂3 = 114208327603.99999999999205…  (so e ≥ 114208327604 once a ≥ 72057431991)
```

**Target theorems** (new module `CollatzMoonshot/FrontB/EliahouFrontier.lean`, importing
`FrontB.Eliahou`; leave `Assumed/Cycles.lean` alone except to mention the result in its docstring):

```
theorem odd_members_ge_of_two_pow_68 : ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨ 72057431991 ≤ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card
theorem min_cycle_length_two_pow_68 : ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨ 186265759595 ≤ m          -- 114208327604 + 72057431991
```

Ledger must be exactly `[propext, Classical.choice, Quot.sound,
collatz_verified_up_to_two_pow_68]` - **no big-power `native_decide`**: the node-3 certificates
`2^p < 3^q` are infeasible here (`q ≈ 6.5·10¹⁰` means ~10¹¹-bit numbers).  Replace them by
**certified real bounds on `log 2` and `log 3`** to ~26 significant digits:

- `Real.abs_log_sub_add_sum_range_le (h : |x| < 1) (n) : |∑_{i<n} x^{i+1}/(i+1) + log(1−x)| ≤ |x|^{n+1}/(1−|x|)`
  (mathlib, `Analysis/SpecialFunctions/Log/Deriv.lean:217`).  `log 2 = −log(1 − 1/2)` with `n = 90`
  (error `≤ 2^{−90}·2 < 10⁻²⁶`); `log 3 = log 2 + log(3/2)`, `log(3/2) = −log(1 − 1/3)` with `n = 58`
  (error `≤ 3^{−59}·(3/2) < 10⁻²⁷`).  Evaluate the finite rational sums with `norm_num`
  (rationals with ~30-digit denominators; if `norm_num` is slow, `decide`-free `Rat` arithmetic
  via `norm_num [Finset.sum_range_succ]` in chunks, or state the partial sum as a literal
  `p/q` and prove `∑ = p/q` by `norm_num`).  Reference values: `ln 2 =
  0.69314718055994530941723212145817657`, `ln 3 = 1.0986122886681096913952452369225257`.
- From the bounds: `c₁ < log₂3` ⇔ `103768467013 · log 2 < 65470613321 · log 3` (margin
  `≈ 1.0·10⁻²² · 65470613321 · log 2 ≈ 4.6·10⁻¹²` in absolute terms - comfortable), and
  `log₂(3 + 2^{−68}) < c₂` ⇔ `6586818670 · (log 3 + log(1 + 1/(3·2^{68}))) < 10439860591 · log 2`,
  using `log(1+x) ≤ x` (`Real.log_le_sub_one_of_pos`) and `1/(3·2^{68}) < 10⁻²⁰`.
- The cycle side is already abstract in `FrontB.Eliahou`: `3^a < 2^e` gives `a log 3 < e log 2`
  (`Real.log_lt_log` after casting), and `2^e · x^a ≤ (3x+1)^a` with `2^{68} < x` gives
  `e log 2 ≤ a log(3 + 1/x) ≤ a log(3 + 2^{−68})`.  So `c₁ < e/a < c₂` in `ℝ`, and
  `farey_denominator_bound` (node 3) gives `a ≥ 72057431991`; then `e > a·c₁ ≥ 72057431991·c₁`,
  which exceeds `114208327603` (check: `72057431991 · 103768467013 / 65470613321 =
  114208327603.9999999999847…` - the margin is `1.5·10⁻¹¹`, so prove `114208327603 < a·c₁`
  as an exact rational inequality with `norm_num`, never with floats).  Reuse node 3's
  `step_prod_identity`, `three_pow_lt_two_pow`, `two_pow_mul_pow_le`, `two_pow_68_lt_orbit`.
- Docstring: this is Eliahou's 1993 method at the repo's own `2^{68}` frontier; it is **not**
  Hercher 2023 Cor. 29 (`1.375·10¹¹` odd members needs his residue-class computation on top of
  the continued fraction - the pure Farey step at `X₀ = 2075·2^{60}` gives the same `72057431991`,
  host-checked), so `hercher_odd_members_bound` stays a citation axiom.  Cite Eliahou §3.
- `(7,8)`-style control: none needed; instead a kernel/`norm_num` check that the two Farey
  fractions really are neighbours (`b·c − a·d = 1`).

**Rules.**  One writer per file; no new axioms; no experiments, no push; no board-row work.
Review laps rank the open leaves of this node only.  If the 26-digit series bounds resist
`norm_num` within one lap, commit the skeleton with the two log bounds as named `sorry` leaves
(`log_two_bounds_26`, `log_three_bounds_26`) and everything else closed, and say so.

## Attended operator override: 2026-09-16 00:10 EDT — NODE 3, discharge the Eliahou citation axiom (ACTIVE for this run only; Nodes 1–2 of the 23:58 override are DONE at `2a1478b`/`8510836`, host-verified trust triple, pushed)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  Same lane as the 23:58 override (formalizing a known result; no new
mechanism, nothing toward `U.Finite`); the "awaiting a new mechanism" pause otherwise stands.
Hard stop: the host kills every lap by 05:25 EDT - **commit a compiling skeleton with named
`sorry` leaves first**, then close leaves; `box done --green` is the exit while a leaf is open,
`box done` once `src/` is sorry-free again.  Reconcile with `git log` and the newest
`HANDOFF-*.md` before acting.

🎯 **Node 3 - turn `Assumed.eliahou_min_cycle_length` (`CollatzMoonshot/Assumed/Cycles.lean`)
from an `axiom` into a `theorem` with the SAME statement**, standing only on
`collatz_verified_up_to_two_pow_68` (already consumed by
`Conditional.two_pow_68_lt_of_onCycle_nontrivial`) plus the trust triple and, if needed, a
`native_decide` certificate for one big power comparison (disclose it in the docstring; the
Rhin-lite allow-list pattern in `scripts/check-fixed-block-bound.sh` is the model).

**Reference implementation, read-only:** `papers/eliahou-collatz-bounds-tangentstorm/`
(untracked; see its `PROVENANCE.md` - no license, so read for structure and lemma names and
write our own proofs; cite it in the module docstring as "structure follows tangentstorm's
Lean 4.28 formalization, edited by Aristotle").  Its headline `eliahou_bound {L} (c :
CollatzCycle L) (hmin : 2^40 < c.minElem) (hk : 0 < c.numOdd) : 17087915 ≤ L` is stated for the
compressed map `collatzComp` = our `tstep`, over a `Fin L`-indexed cycle structure.  Its
`Sandwich.lean` (ratio bounds) is 113 lines, `ProductFormula.lean` 133, `ContinuedFractions.lean`
211 (Farey pair bound + certified convergent facts `3^10781274 < 2^17087915` via
`native_decide`), `Defs.lean` 126.

**Route, in order (new module `CollatzMoonshot/FrontB/Eliahou.lean`; import it from the
root; keep `Assumed/Cycles.lean`'s docstring, change `axiom` → `theorem … := Eliahou.…`):**
1. **Product identity on a `tstep`-cycle** - we already have
   `FrontA.TrunkBound.tstep_iterate_prod_identity : 2^m·x_m·∏_I 3x_i = 3^a·n·∏_I(3x_i+1)`;
   with `x_m = n` and `n > 0` it gives `2^m ∏_I 3x_i = 3^a ∏_I (3x_i+1)`, i.e. Eliahou's
   `∏_{odd} (3 + 1/x_i) = 2^m`.  No `Fin L` cycle structure needed: index by
   `oddSteps n m` exactly as `TrunkBound`/`HarmonicMean` do.
2. **Sandwich** (Eliahou Thm 2.1): with `x_min = segMin n m` (all cycle elements `≥ x_min`)
   `2^m ≤ (3 + 1/x_min)^a` (this is `min_term_inequality_le` at `x = x_min`, already proved for
   `n ≤ x_m`), and `3^a < 2^m` (strict, from the product identity since every factor
   `3x_i+1 > 3x_i`; equality is impossible for `a ≥ 1`).  So `a·log₂3 < m < a·log₂(3 + 1/x_min)`.
3. **Cycle elements are big**: for a `step`-cycle `n` not in `{1,2,4}`, EVERY element exceeds
   `2^68` - `Conditional.two_pow_68_lt_of_onCycle_nontrivial` gives it for `n`; apply it to each
   element (each is on the same cycle).  Then translate `step`-cycle ↔ `tstep`-cycle: a
   `step`-period `m_s` with `k₁` odd steps is a `tstep`-period `L = m_s − k₁` with the same odd
   elements (each odd `step` is followed by a halving); prove the relation you need
   (`step^[m_s] n = n → ∃ L a, tstep^[L] n = n ∧ a = ones (traceWord n L) ∧ m_s = L + a`).
   `Basic.lean`/`Conjecture.lean` may already have pieces - grep `tstep`, `OnCycle` first.
4. **The Farey/convergent step** (Eliahou §3, the reference's `ContinuedFractions.lean`):
   any fraction `L/a` with `log₂3 < L/a < log₂(3 + 2^{−40})` has `L ≥ 17087915` (and then
   `a ≥ 10781274`, since `a > L/log₂(3+1/x_min)`; hand-checked 2026-09-16 with mpmath at 40
   digits: `17087915/10781274` lies in the interval, `17087915/log₂(3+2^{−40}) − 10781274 ≈
   −3·10⁻⁶` (so with a `2^{40}` cutoff the integer bound holds only because `a` is an integer
   exceeding `10781273.999997`), while `17087915/log₂(3+2^{−68}) − 10781274 ≈ +1.1·10⁻⁸ > 0`.
   **Use the `2^{68}` cutoff we actually have** (`x_min > 2^{68}`), and certify the convergent
   facts with exact integer arithmetic, never floats).
   Ingredients: two convergent facts as big-integer inequalities (`3^{10781274} < 2^{17087915}`,
   and the upper one with `(3·2^{40}+1)^{a}` vs `2^{L}·2^{40a}`), `native_decide` allowed;
   the Farey-pair lemma (`b·c − a·d = 1` ⇒ any `p/q` strictly between `a/b` and `c/d` has
   `q ≥ b + d`) - elementary, prove in the kernel.
5. **Assemble**: `eliahou_min_cycle_length` as a theorem: `m_s = L + a ≥ 17087915 + 10781274 =
   27869189`.  Then `#print axioms` must show `[propext, Classical.choice, Quot.sound,
   collatz_verified_up_to_two_pow_68]` plus at most the named `native_decide` certificate(s).
   Record the exact axiom list in the docstring and the handoff.  Downstream users of the old
   axiom (`grep -rn eliahou_min_cycle_length`) must still build unchanged.

**Rules.**  One writer per file; no edits to `Assumed/Computation.lean`; no new axioms; no
experiments, no Aristotle, no push (host pushes); no work on any board row.  A review lap ranks
the open leaves of this node only.  If step 4's convergent facts do not certify within one lap
(the powers have ~10⁷ bits; `native_decide` on `Nat.pow` with `Nat.blt` should be seconds via
GMP, but measure), fall back to leaving step 4 as ONE named `sorry` leaf `farey_convergent_bound`
with everything else closed, and say so.

## Attended operator override: 2026-09-15 23:58 EDT — operator-assigned BOUNDED FORMALIZATION node (ACTIVE for this run only; the "awaiting a new mechanism" pause below otherwise stands)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  This is the Lean "formalizing known results" lane (rank 10 of the board below),
assigned separately as the reflection permits; it claims **no new mechanism** and nothing here is
a step toward `U.Finite`.  Hard stop: the host kills every lap by 05:25 EDT 2026-09-16 - **commit a
compiling skeleton with named `sorry` leaves before every hard step**.  Read this addendum, the
newest `HANDOFF-*.md`, then `git log`; reconcile before acting.  Finish with `box done` (the repo
is sorry-free; keep it so at every commit, or use `box done --green` if a skeleton leaf is open).

🎯 **Node 1 - Front B statement hygiene, as theorems** (`FrontB/Threads.lean`, small).  The
reflection found two labels that are Front B in costume; make the kernel say so:
- `countingGivesFinite_iff_frontB : CountingGivesFinite ↔ FrontB` (forward: a counterexample `v`
  gives the distinct family `wpow v (j+1)`, all integral and nontrivial by `integerCycle_wpow_iff`
  / `isTrivial_wpow_iff`, lengths `(j+1)·|v|` by `length_wpow`, so the set is infinite; backward:
  empty is finite).  Then `not_finitenessIsNotEmptiness : ¬ FinitenessIsNotEmptiness`.
- `ladderCompletes_iff_frontB : LadderCompletes ↔ FrontB` (forward: take `C := circuits` of the
  primitive root from `exists_primitive_root`; backward: FrontB makes every integral cycle trivial).
- Then add the honest **primitive-population** predicate `PrimitiveCountingGivesFinite :=
  {v | Primitive v ∧ IntegerCycle v ∧ ¬IsTrivial v}.Finite` with a docstring saying it is the
  population Simons–de Weger/Hercher count, and do NOT claim any implication from it to FrontB.
  Fix the two docstrings the reflection called false.  `#print axioms` on each.

🎯 **Node 2 - Rozier–Terracol Theorem 4.2, the all-terms harmonic-mean half**
(`FrontA/TrunkBound.lean` has the easy min-term half; put this in a new
`FrontA/HarmonicMean.lean` importing it).  With `I = oddSteps n m`, `a = |I|`,
`x_i = tstep^[i] n`, `H := ∑_{i∈I} 1/x_i` (so the harmonic mean is `h = a/H`):
- `prod_le_pow_harmonic : ∏_{i∈I} (3x_i+1)/(3x_i) ≤ (1 + H/(3a))^a` for `a ≥ 1` - AM–GM with
  equal weights `1/a` on the factors `1 + 1/(3x_i)` (mathlib
  `Real.geom_mean_le_arith_mean_weighted`, or `Real.inner_le_nnorm_mul_nnorm`-free routes via
  `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` are NOT needed; the weighted AM–GM is the tool).
- `harmonic_mean_inequality : n < x_m → (2:ℝ)^m < (3 + H/a)^a`, from
  `tstep_iterate_prod_identity` exactly as `min_term_inequality` was derived, with the product
  bound above in place of the min-term bound.  This is RT 4.2's `log 2/log(3+1/h) ≤ a/m`.
- Corollary under `3^a < 2^m` (`AcyclicParadoxical`), with `Λ = m log 2 − a log 3 > 0` and
  `h = a/H`: `2^(m/a) < 3 + H/a`, and `2^(m/a) − 3 = 3(exp(Λ/a) − 1) ≥ 3Λ/a`, so
  `harmonicMean_lt_of_subcritical : h < a/(3Λ)` - the same bound `TrunkBound` proves for `x_min`,
  now for the harmonic mean of ALL odd terms (`x_min ≤ h` is the trivial comparison; prove it).
  Add the `(7,8)` control (`H = 1/7+1/11+1/17+1/13+1/5`, `a = 5`, `m = 8`) as `TrunkBound` did.
- Docstring: "hard half of RT Theorem 4.2 (harmonic-mean form); no novelty claimed."

**Rules.**  Trust triple only (`[propext, Classical.choice, Quot.sound]`); the Rhin-lite natives
may be inherited only by a corollary that says so in its docstring.  No new experiments, no
Aristotle, no push (host pushes), no changes to `DIRECTION.md` below this addendum, no work on
any board row.  When both nodes are green and audited (`bash scripts/check-fixed-block-bound.sh`
still FORMALIZE-TIER GREEN), write the handoff and `box done`.  A review lap ranks the open leaves
of these two nodes only.

## CURRENT DIRECTIVE — awaiting a new idea; no execution lap selected

Set by the **2026-09-13 whole-repository reflection**, reconciled through
`6a33554`, from baseline `5a54acc`. This supersedes all older assignments and
rankings in handoffs, route maps, source docstrings, and PENDING_WORK history.

*History note (2026-09-13, operator-assigned bounded node):* `FrontA/TrunkBound.lean` formalizes the easy min-term half of Rozier–Terracol Theorem 4.2 (every paradoxical segment dips below `a/(3Λ)`; Rhin-lite corollary `x_min < a^437/(3c)+a`); the awaiting-a-new-mechanism pause otherwise stands. See `HANDOFF-2026-09-13-trunk-bound.md`.

**Nothing currently on Front A or Front B clears the bar of probability times
magnitude of NEW mathematics for a bounded objective.** Do not launch another
proof lap from the deferred list. This is a judgment about the presently
specified mechanisms, not an impossibility theorem or a claim that Collatz is
unprovable. The completed campaign remains green and useful.

The operator explicitly requested reflection and documentation only. That
instruction overrides reflection.md's generic instruction to implement a proof
step afterward. No Lean proof, new experiment, or Aristotle job is part of this
lap. Its deliverable is this reconciled decision and the verification/handoff.

## What the completed laps actually bought

The git range contains 17 commits after the baseline, including host experiment
commits and direction reviews; it is not 17 independent proof advances.
`5a54acc` itself is dated September 8 and closes the front-normalized rung-3
classification at length 8. It is the settled baseline for this review.

| Commits | Reconciled result | Limit on what follows |
|---|---|---|
| `f8fa4a5`, `cf8d748`, `56304ac`, `5ea1b38`, `9b5dc54` | Rung, word-model, and orbit censuses; recorded length sweep 2..80 has hits at 8,27,46,65,73. | Finite data; a cluster on the trajectory of 27 is not a universal theorem. |
| `26c49b9`, `c3aba74` | Campaign A2: exact trunk slack/criterion, 2305/2313 obstruction, and null-model audit. | Prefix remainder cannot be dropped. The proved model law is not a distribution law for admitted integer traces. |
| `529ccef`, `4a12a68` | Arbitrary-block cascade, rational envelope, and explicit fixed-run length bound. | Complete for each fixed b, not uniform in b. “Campaign B” here is work on Front A, not a proof of the cycle front. |
| `9ae73a3`, `972c772` | Further fixed four-block empty censuses and corrected census commentary (minimum observed run ratio 9/46; first populated rung after 3 is 7). | No global run-density law; no new theorem from editing the summary. |
| `5bdea84`, `882c787` | Rational short-run positivity question selected, then refuted by a primitive Q=2 family at unbounded length. | Rational positivity does not imply integer admission. |
| `bc4158e`, `3a3e838` | Six-letter admission question selected, then refuted by a padded primitive Q=2 family. | The certified filter is exactly P_6; full admission remains separate. |
| `e6cb096`, `6a33554` | Odd-start strict cycle-witness edge selected, then proved; unrestricted pair finiteness now implies Collatz. | New formal dependency information, not a proof of either finiteness hypothesis. |

The fixed-b theorem is

```
odd n ∧ AcyclicParadoxical n m ∧ oddRunCount(traceWord n m) ≤ b
  → m < 4*((2^b−1)*(b+53342))^2+b.
```

It includes a terminal odd run without adding a trajectory step. The rational
small-vertex argument and repeated squaring produce the factor `2^b−1`; the
existing polynomial 2/3 separation closes the feedback. This is a meaningful
extension to strict segments, but its mechanism is the Simons–de Weger pincer
on a new object. Their fixed-circuit finiteness combines an elementary upper
bound with logarithmic-form separation; its rate deteriorates with circuit
count. It is not a source of uniform compression. Source availability is
resolved. [Simons–de Weger v1.44, Theorem 3, Lemmas 7/12, §8](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf).

Do not confuse the benefits: rung classification and fixed-b formalization
advance restricted structure; the obstruction families eliminate relaxations;
cycle repetition clarifies the graph. None supplies the remaining uniform
integer-trajectory input. Another known specialization does not inherit novelty
from having a fresh theorem name.

## Exact statement and dependency graph

`Conjecture` means every positive integer reaches 1 under the standard map
`step`; `NoDivergentOrbit` excludes unbounded positive orbits;
`NoNontrivialCycle` permits only 1,2,4 on positive standard cycles.
Their conjunction is equivalent to Conjecture by `conjecture_iff_split`.
Paradoxical segments instead use the shortcut map `tstep`.

```
AcyclicParadoxical n m :=
  n>2 ∧ m>0 ∧ 3^ones(traceWord n m)<2^m ∧ n<tstep^[m] n
U := {(n,m) | AcyclicParadoxical n m}
O := {(n,m) ∈ U | n is odd}
```

“Acyclic” means strictly unequal endpoints. Interior repetitions are allowed.
The sets count pairs, not distinct starts, primitive words, first returns, or
segments before first descent. These distinctions are load-bearing.

The default build proves:

- `U.Finite → NoDivergentOrbit`.
- `U.Finite → O.Finite → NoNontrivialCycle`.
- Hence `U.Finite → Conjecture`.
- An odd shortcut periodic member n>2 produces infinitely many lengths in O,
  by repeating its period and appending one odd step. Infinitely many starts
  are neither needed nor claimed.
- `ParityRigidityW1' → NoDivergentOrbit`; also
  `RepeatOrDescendCertificate ↔ NoDivergentOrbit`.
- `NoNontrivialCycle ↔ FrontB` in the integral-word dictionary.

All these displayed edges are trust-base clean. **Still open:** O.Finite,
U.Finite, O.Finite→U.Finite, both unconditional fronts, W1', compression and
the other research predicates. `Conjecture → U.Finite` is not supplied by
this graph. Pointwise termination does not supply a uniform pair bound.

The old “Front A only” reading of paradoxical finiteness is now decisively
wrong: even O.Finite carries cycle exclusion. A uniform bound on odd-start
run count, together with fixed-b finiteness, repackages O.Finite; a uniform
length bound does likewise (finitely many words, each with finitely many
starts below its threshold). Neither is a harmless auxiliary assumption.

## Standing obstruction: full admission is the missing information

For a Boolean word v of length m with a ones, put `N=numer(v)` and
`D=2^m−3^a>0`. Its full realizing residue and least allowed start are

```
r_m = [−N*(3^a)^(-1)] mod 2^m
c_m = min {n ∈ ℕ | n>2 and n≡r_m mod 2^m}.
```

A word admits a strict paradoxical start exactly when `D*c_m<N`. All its
admitting starts are the representatives n>2 in that residue class with
`D*n<N`. Keep the least-above-2 correction when r_m≤2. In contrast, the
rational affine fixed point is `N/D`; positivity of it and of every internal
head does not realize the word as a small integer trajectory. For an actual
integer cycle the endpoint equality instead requires `D*n=N`.

`882c787` certifies `(XY)^k XYY`, X=TF, Y=TTF, with bounded run lengths,
primitivity and all rational head slacks positive, for unbounded k. Its common
six-bit residue is 57, above N/D. `3a3e838` certifies
`(XY)^(2j+12) X Y^17`, j≥0, at lengths 10j+113, with the same positivity and
primitivity and now `D*57<N`. Thus even that necessary entry test admits an
unbounded family. Both are mathematical all-parameter arguments with exact
rational scripts, not new Lean theorems.

Evidence boundary: the checked-in second certificate proves P_6 survival,
not an arbitrary-L theorem. Its full-admission rejection check covers 36
parameters. Prior operator context additionally reports universal full
rejection with canonical starts of about m bits; no corresponding universal
proof artifact was added to this repository. The current operator treats
finite-prefix relaxations as exhausted. **All fixed finite-prefix follow-ups
remain retired**, without relabeling the P_6 certificate as a theorem for every
L. Neither that retirement nor these examples refutes every symbolic proof.

At fixed (m,a,N) the full residue is deterministic. A uniform argument must
therefore consume trajectory-side information: the actual small start and
all its parity/carry compatibility. This can be expressed symbolically, but
cannot be replaced by rational head positivity, a fixed-prefix test, or an
independent random-residue model. A2's exact trunk criterion already shows why
retaining only the minimum and subsequent climb loses decisive information.

## Whole-board ranking: all below the bounded-objective bar

This is an ordinal ranking of present research prospects, **not a work queue**.
“High magnitude” means a new mechanism would matter; it does not make an
unspecified mechanism a bounded task. Historical 40%, 55%, and 70% route odds
are conditional speculation about eventual solutions, not success probabilities
for the next lap. They have no scheduling authority.

| Rank | Candidate | Probability × magnitude of NEW mathematics in a bounded lap | Decision / missing deliverable |
|---|---|---|---|
| 1 | Front A: a new trajectory constraint beyond RT's harmonic-mean condition | Low for an unconditional strengthening × high; high for a faithful port × negligible new mathematics | No proposed extra inequality controls admission or couples the mean to length/start strongly enough. Do not assign the port. |
| 2 | O.Finite → U.Finite | Unassessable without a specified map (treat as low) × substantial graph value | No map with target membership and finite fibers is known here. “Normalize even starts” is not an objective. |
| 3 | Coefficient stopping time (CST), or a genuinely new restricted obstruction to its failure | Low × high; known equivalence/verification ports have high probability but low new content | No fresh restricted class and mechanism are specified. Global CST is an open cycle-excluding conjecture. |
| 4 | Carry/transducer or repeat-or-descend certificate | Very low at present × very high | No state space with a proved sound transition invariant and a surviving descent/recurrence certificate. The interface alone is exactly Front A. |
| 5 | W1' parity rigidity / Furstenberg intertwining | Very low × very high | No arithmetic transfer from a positive integer orbit to the joint ×2,×3 action, nor applicable entropy input. The conditional consumer is already complete. |
| 6 | Tao forward/backward saturation; pointwise harmonic growth and packing | Very low × very high | Need actual high-floor harmonic mass AND control of overlap across moving seeds. Neither follows from the completed subharmonic certificates. |
| 7 | Front B primitive compression, bounded denominator, or a new Knight-type identity class | Very low × high | No transformation preserving integrality/nontriviality while reducing complexity, and no new identity class. Fixed-circuit finiteness does not bound circuit count. |
| 8 | Numerator/residue discrepancy or cycle counting | Very low at the useful error scale × high | No estimate reaching an integer exclusion threshold; mean behavior is not enough. Exact conditioning leaves no randomness. |
| 9 | The 4614 cutoff, U.Finite itself, global start/length/run bounds | No credible bounded attack × very high | These are destination conjectures, not reductions. Increasing a census cannot prove their universal quantifiers. |
| 10 | More fixed rungs, sharper fixed-b constants, cycle transport, standard certificate/axiom ports, converse wiring | Often high × little or no new mathematics | Valuable formalization under a separately requested objective, but below this operator's bar. |

RT Theorem 4.2 says `1−C≤E/n≤((3+1/h)^a−3^a)/2^m`, where h is the
harmonic mean of the actual odd terms, C=3^a/2^m and E=N/2^m.
Its upper bound is a product/AM–GM
estimate. It gives a necessary condition, not control of h as the trajectory
varies. CST is `t(n)=τ(n)` for n≥2, including infinite values; equivalently a
paradoxical segment contains an earlier value below its start. Conjecture 6.1
excludes all paradoxical starts above 4614. Those conjectures must not be
assumed as known constraints. [Rozier–Terracol v5, §§1,4,6](https://arxiv.org/html/2502.00948v5).

For rank 2, even-prefix deletion sends the actual 18@8 witness to 9@7,
which is not subcritical. Reanchoring at a minimum does not repair coefficient
control automatically, and forgetting prefix depth does not prove finite
fibers. A real proposal must specify a map `f:U\E→O` for an explicitly finite
exception set E (possibly empty), prove membership for every input, and bound
or otherwise prove each fiber finite. No such map is supplied by this review.
If proved, this would make O.Finite sufficient for full Collatz through the
existing U edge; it still would not prove O.Finite.

For ranks 4–6, distinguish three inputs that an umbrella “rigidity certificate”
can conceal. Pure 2-adic invariant measures are not constrained by positivity
of the original integer: the existing negative-cycle witness defeats the
unconditioned parity claim. Topological Furstenberg rigidity is already proved
in this repo; it supplies neither the missing arithmetic intertwining nor a
measure entropy theorem. W1' uses standard-map threshold `log 2/log 6`, not
the shortcut threshold `log 2/log 3`. Its expected converse is finite-measure
calibration, still only a pinned target here, not new rigidity. W1 without the
prime is stronger and would also exclude nontrivial positive cycles.

Tao's result concerns orbit minima for logarithmically almost all starts.
A large backward basin entering one fixed seed d has orbitMin≤d and is
eventually Tao-good. The existing `mem_taoGood_of_reachesValue` formalizes the
failure of that amplification argument. A useful replacement needs moving
high floors and a positive logarithmic-density contradiction.
[Tao, Almost all orbits attain almost bounded values](https://arxiv.org/abs/1909.03562).
The exponent-4/5 renewal/stopping pipeline is complete; another exponent below
1 does not provide the harmonic budget. The harmonic obstruction excludes the
specified five-floor, constant-lift certificate scheme; it is not a theorem
against every enriched state space. Escaping that scheme without a proposed
invariant, or merely porting a larger table, is not a bounded new idea.

## Front B statement audit: do not trust obsolete labels

Reading `FrontB/Threads.lean` and `Powers.lean` exposes two residual mismatches.
These are source-grounded mathematical deductions recorded here, **not new
kernel theorems or proof assignments**:

1. `CountingGivesFinite` currently counts **all** nontrivial integral words,
   not primitive cycles. If v is one such word, `wpow v (j+1)` remains integral
   and nontrivial by `integerCycle_wpow_iff` and `isTrivial_wpow_iff`.
   `length_wpow` gives length `(j+1)*v.length`; v is nonempty, so the words
   are distinct. Thus that literal finiteness predicate implies FrontB, whose
   converse makes the set empty. `FinitenessIsNotEmptiness`, currently defined
   as this predicate AND `¬FrontB`, is consequently impossible. The comment
   that this is a weaker counting conclusion is false for the written type.
   Finiteness without emptiness is the appropriate warning for **primitive
   cycles** (or cycles modulo powers), a different population.
2. `LadderCompletes` universally quantifies over every circuit bound C.
   Set C to the primitive word's own circuit count and use primitive-root
   decomposition to see that it too is equivalent to FrontB. Fixed-C
   finiteness does not give fixed-C exclusion, let alone this whole ladder.

`NaiveCompression` and `NaiveBoundedDen` already have their power-degeneracy
proofs. Primitive `Compression` avoids that particular defect, but its unknown
constant does not finish the front: one still needs to exclude the finitely
many survivors up to that constant. A bound ≤91 closes only through the named
Hercher citation. The earlier route-map assertion that *any* bounded denominator
or circuit count automatically dies against a known lower bound overclaims.
A bound must be explicit and within verified exclusions, or the survivors
must be eliminated independently. No kernel theorem here says otherwise.

Other board entries have not acquired a mechanism overnight: rotation gcd
harvesting is already killed by unit-multiple equivalence; logarithmic-form
and abc lower bounds alone lack the upper bound/exclusion input; sign-blind
cycle arguments must survive the negative-cycle falsification harness;
sum-product, zero-entropy classification, function-field carry transport,
Cobham rigidity, and independence/Goodstein analogies have no specified
load-bearing lemma. Importing entropy definitions, translating citations, or
formalizing the two accounting corrections above does not clear the novelty
bar. Leave their formal interfaces unchanged in this documentation-only lap.

## Trust, verification, and reopening condition

The default source has zero disclosed sorries. The fixed-b headline inherits
eleven existing Rhin-lite native certificates; it is not bare-trust-base-only.
The new cycle witness and both finiteness edges use exactly `propext`,
`Classical.choice`, `Quot.sound`. RT 3.2, power approximation, and topological
Furstenberg are proved, despite historical file names under Assumed.

Named citation debt remains: Tao, Eliahou/Hercher bounds and computations,
Baker bounded difference; abc is an explicitly conjectural input to conditional
results. Historical Rhin axiom routes in `wip/` are retired and not root
imports. Cited axioms are debt, not permanent mathematical destinations;
discharging them still does not create the missing uniform mechanism.

The handoff records the real full build, fixed-b audit, trust-only graph audit,
existing obstruction certificates, and proof-debt check. No new arithmetic
claim was kernel-proved in this reflection.

**Standing state: awaiting a new idea. No next proof lap is authorized by this
file.** Reopen only when a proposal names an exact bounded statement, a first
attack with concrete mathematical evidence, the new information it consumes,
an acceptance test, and a costume check against the obstructions above.
For the even-start edge the actual finite-to-one map is mandatory. For a
uniform Front-A route the small integer trajectory must be load-bearing.
For Front B the proposal must go beyond fixed-circuit finiteness and preserve
the correct primitive/integral population. These are admission criteria for a
future idea, not assignments to search each row in turn.

The reflection objective is complete. Use `box done` after the green commit,
not `box stuck`: absence of a promising current idea is not an impossible
external condition or a request for an operator decision. Do not resume the
completed cycle edge, enlarge a prefix filter, or substitute routine
formalization merely to keep the treadmill moving.

Newest checkpoint: `HANDOFF-2026-09-13-whole-board-reflection.md`.
Earlier directions remain recoverable in git and dated handoffs.
