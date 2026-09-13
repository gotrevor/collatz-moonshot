# Handoff: Campaign B architecture lap 1 — cyclic potential composition

Date: 2026-09-13. Branch: `main`. No push. Campaign A2 (`c3aba74`) and rung 3 remain complete.

**Running+advancing.** A new composition inequality has a mathematical derivation
and its load-bearing potential induction is kernel-checked; the remaining attack
is the finite cyclic-product bridge to actual block words, then the explicit L(b).

## Concrete advance

Read `BLOCK-COMPOSITION-2026-09-13.md` first. It contains the complete arbitrary
integer cascade, exact prefix recurrence and sharp admission criterion, a
source-grounded audit of the completed two-/three-block contractions, the new
composition derivation and every constant's dependence.

For `b≥1` blocks, `a` odd steps, `m` total steps and `δ=(2^m-3^a)/2^m`, the proposed
inequalities are

```
2^a < (b/δ)^(2^b-1),         2^m < 2^b*3^a,         m<2a+b.
```

These follow in the note even for the larger rational fixed-point positivity
relaxation. Conjugate a head block to `u=x+1`, so `u_next=r*u+s`, with
`r=3^q/2^(q+e)` and `0≤s<1`. The whole subcritical word has a rational affine
fixed point dominating an admitting segment at every block start, hence
`z_i≥2^q_i`. Let M_i be the maximum cyclic partial multiplier product ending at
i, including the empty product. Then

```
M_next=max(1,r_i*M_i),       some M_i=1,
δ*z_i < b*M_i,
2^q_i < (b/δ)*M_i,         M_next ≤ (b/δ)*M_i^2.
```

Cutting at M_i=1 and iterating the last inequality gives the exponent `2^b-1`.
The rational fixed point is never asserted to be an integral Collatz cycle,
and rotation is used on the finite multiplier system, not on an integer trace.
The derivation uses neither global Collatz nor an induction hypothesis equal
to the campaign target.

Existing `rhinLite_nat_measure_loose` and
`rhinLite_loose_constant_le_two_pow` imply
`δ≥2^(-52906)*a^(-436)`. The written feedback calculation proposes

```
L(b)=2*((2^b-1)*(b+53342))^2+b.
```

This is intentionally loose and increasing. It bounds at most b blocks if the
word-to-composition bridge is formalized. **Neither the full composition
inequality about segments nor this L(b) theorem is yet in Lean.** No hidden
axiom or `sorry` claims those missing connections.

## Kernel-checked checkpoint

New default-build module `CollatzMoonshot/FrontA/BlockComposition.lean` proves:

- `headBlock_conjugate`: the rational affine head-block identity;
- `blockCascade_of_identities`: positive integer scales and every joint equation
  for arbitrary block count, given the head identities;
- `blockCascade_compose`: exact prefix elimination, keeping the T remainder;
- `affineFixedPoint_dominates`: domination propagates through a positive affine prefix;
- `blockMultiplier_le_two_pow`, `blockPotential_step`: local potential growth;
- `blockPotential_has_unit`: a subcritical cyclic permutation has a potential
  vertex of value one (multiply the recurrence to contradict R<1 otherwise);
- `blockPotential_mass_bound`: the arbitrary-length induction giving
  `2^(Σq_i)<K^(2^b-1)` from the unit start and local bounds;
- `affineCycle_multiplier_lower`: positivity at each fixed-point vertex gives
  `1<2^b*∏r_i`, which will control the total length.

The actual word-to-head-identities bridge can reuse
`ThreeBlock.segment_identity_of_word`. No need to reopen its three-block
classification. `DIRECTION.md` remains deliberately untouched.

## Exact probes

New `experiments/block_composition.py` checks every prefix correction, each
cyclic affine sum identity, the maximum recurrence, the unit cut, the potential
induction and both proposed composition inequalities with exact arithmetic.

- `--controls`: 4,000 actual segments; equivalence to the existing rung-3
  positivity/ceiling formulas through m=18; all 320 A1 admitting starts through
  start 5000; shared-trunk pair 2305/2313 with prefix numerators 7207/1375 and
  opposite admission; explicit b=2,3,4,5 rational controls refuting removal of
  even one joint's positivity assumption.
- Complete fixed `(b,m,a)` scans: `(1,8,5)`, `(2,8,5)`, `(3,8,5)`, and b=4,5
  at `(m,a)=(16,10),(27,17),(46,29)`. In total **51,411,181 exponent tuples**,
  with the mechanism tested on **816,411 rational-positivity survivors**.
  Every assertion passes. The rung-3 control has four admissions; b=1,2,4,5
  have none at these specific pairs. These are finite tests, not an all-length
  exclusion for rungs 4 and 5.
- The largest scan, `--census 5 46 29`, covers 48,730,500 tuples, with 678,142
  fixed-point positivity survivors, 441,530 sharp positivity-leaf survivors,
  159,101 nested-ceiling survivors, and zero actual admissions.

The full table, first small survivors, negative controls and complete shared-trunk
block tuples are in the architecture note. The new note also corrects two
historical interpretive traps: nested ceilings need not attain a genuine integer
cascade, and the final rung-3 finiteness proof DOES consume the polynomial measure.

## Verification actually run

1. `lake env lean CollatzMoonshot/FrontA/BlockComposition.lean` — green after
   iteration, with the real Lean 4.33.1 compiler.
2. Final real full gate (after the module's final proof edits and root import):

   ```sh
   ~/personal/bin/lean-green ~/src/collatz-moonshot \
     --axioms CollatzMoonshot.FrontA.headBlock_conjugate \
     --axioms CollatzMoonshot.FrontA.blockCascade_compose \
     --axioms CollatzMoonshot.FrontA.blockCascade_of_identities \
     --axioms CollatzMoonshot.FrontA.affineFixedPoint_dominates \
     --axioms CollatzMoonshot.FrontA.blockPotential_step \
     --axioms CollatzMoonshot.FrontA.blockPotential_has_unit \
     --axioms CollatzMoonshot.FrontA.blockPotential_mass_bound \
     --axioms CollatzMoonshot.FrontA.affineCycle_multiplier_lower
   ```

   **8768 jobs, FORMALIZE-TIER GREEN.** All eight ledgers contain exactly
   `[propext, Classical.choice, Quot.sound]`. No new axiom, native artifact or
   sorry. `scripts/AxiomAudit.lean` includes those declarations; the full script
   was not separately rerun because the gate directly audited them.
3. `python3 experiments/block_composition.py --controls` — final version passes.
4. `python3 experiments/block_composition.py --census B M A` for b=4,5 at
   `(27,17)` and `(46,29)`; the smaller five pairs above were run by importing
   and calling the same `census` function in one Python invocation. All pass.
5. `bash scripts/check-proof-debt.sh` — zero disclosed sorries in its stated scope.
6. `git diff --check` — clean.

The read-only reference corpus was searched and relevant separation/build notes
read. No Aristotle tool was available in this session. No subagents were used.

## Current blocker and next highest-value attack

**Formalization boundary, not a mathematical stuck claim:** the word-to-potential
construction remains unproved in Lean. In architecture lap 2:

1. Scrutinize the derivation in the note, especially wraparound in
   `M_next=max(1,r_i*M_i)` and the full-cycle term R<1.
2. Define the b cyclic partial products and prove that recurrence and the cyclic
   affine sum identity. Use the existing kernel-checked unit cut, then transport
   the run-length sum through one full cyclic traversal and apply the mass lemma.
3. Package actual `traceWord` block splits, rational fixed-point domination and
   positivity, then reuse the existing polynomial separation and close L(b).

These are finite algebra/combinatorics and numerical feedback tasks. Do not
replace them with a renamed uniform theorem or an integral-cycle assumption.
Campaign B's two-lap no-progress stopping rule has **not** fired: lap 1 supplies
a new inequality and mechanism. No `box done`/`box stuck` claim is warranted for
the still-unformalized full target at this checkpoint.
