# Authorized finite repair formalization

Trevor requested pursuing the next targets.  The exact Python repair is complete and its data are in the repo.  This bounded Opus/low task proves that repair in Lean.  Own only CollatzMoonshot/Obstructions/Repair71.lean, optional CollatzMoonshot/Obstructions/Repair71Data.lean, and HANDOFF-2026-09-28-repair71.md.  The host owns root imports, other workers own disjoint code and notes.  RepairState, allowedUnit, AllowedMove and seventyOne_repair_restricted in the installed skeleton are frozen.  No additional legal-move constructor, arbitrary-unit insertion, or unproved soundness assumption is allowed.  A false statement calls for a counterexample, not weakening.  Build root, write handoff, commit and stop after the theorem.  Intermediate named lemmas may remain open at a genuine partial checkpoint.  Warm dependencies checked, no downloads.  No general Collatz successor task.

# Frozen finite certificate: 71 repair under the restricted palette

Read the stable data files `experiments/catalytic_palette_71_witness.json` and `experiments/catalytic_palette_71_replay.json`, staged by the catalytic probe.  The old `replay71_wave1.json` is obsolete: it lacked a witness for label 7555.  The final replay has `catalyst_missing_borrowability=[]` and a 96-node topologically ordered `borrow_dag`, ending with the 7555 witness.  This is a finite repair certificate, not a terminating procedure for arbitrary starts.

## Exact acceptance theorem

Define `RepairState := ℕ × Multiset ℕ`; the first coordinate counts factors of 2 and the second counts positive odd generators `r_u`.  Define `AllowedMove` with **only** these constructors:

* a quadratic replacement of two positive odd labels by two positive odd labels when `legalPairMove` in `CatalyticRepair.lean` returns true;
* insertion or removal of the fixed units `U2=(1,{1})`, `U8=(3,{19,25,29,55,83})`, and `U13=(5,{5,7,7,11,17,55,65,83})`;
* the fixed cubic `C5: {5,55,83} ↔ {11,13,17}` at an available multiset context, without changing the factor-2 count.

No constructor may insert an arbitrary value-one word.  In particular, the large `borrow_unit` W must be *derived* by permitted moves, then returned by reversing those moves.

The target theorem is:

```lean
theorem seventyOne_repair_restricted :
    Relation.ReflTransGen AllowedMove
      (16, (certificate71 : Multiset ℕ))
      (28, ((seventyOnePrefix.filter (fun u => u % 2 == 1) : List ℕ) : Multiset ℕ)) := by
  ...
```

`certificate71` and `seventyOnePrefix` are existing definitions.  The first is the published 32-factor certificate; `actualSeventyOne_trace` in `RepairPalette.lean` pins the second to the actual 65-step path from 71 to 1.  Equality of multisets, not list order, is the endpoint check.  If choosing a Boolean checker as the primary artifact, also prove a soundness lemma from its accepted trace to this `Relation.ReflTransGen` theorem; a mere equality of source and target scalar values is not acceptance.

## Replay data and exact interpretation

The witness JSON has 125 Q rows.  Row `k` has signed `coefficient`, `remove`, and `insert`.  The replay JSON's 269 ordered `schedule` actions comprise 9 `insert-U8`, 3 `reverse-cubic`, 3 `remove-U13`, and 254 actions named `Qk`.  For `Qk`, use `remove→insert` if row `k` has positive coefficient and `insert→remove` if negative.  Check each occurrence independently against the *current* multiset using `legalPairMove`; `abs coefficient` counts its occurrences.  `reverse-cubic` means `{11,13,17}→{5,55,83}`.  The `borrowed` annotations in schedule rows are explanatory deficits, not additional legal actions.  The checker must not turn them into unverified insertions.

The replay JSON embeds `source`, `target`, seed units, `borrow_dag`, catalyst and `borrow_unit` as sparse `(label,count)` vectors; label `0` means factors of 2.  Verify source equals `(16,certificate71)` and target equals the path multiset via existing Lean definitions.  The displayed W has 7061 total factors on 109 nonzero labels, but that count is metadata, not evidence of reachability.  Verify the vector claimed as W is exactly the one computed from the DAG and catalyst, and verify it dominates every catalyst coordinate.  Use a compressed sparse vector representation for input data; expand to a `List` or `Multiset` only in the executable checker if needed.

## Borrow-unit DAG

For seed labels, choose witnesses deterministically: label 1 uses U2; any label in U8 uses U8 first (including labels 55 and 83 shared with U13); every remaining seed label uses U13.  The 96 DAG nodes are topologically ordered and have unique `label`s.  A node `{label:u,remove:[a,b],insert:[c,d]}` means that the unit witness for `u` is obtained from the previously proved unit witnesses `W_a` and `W_b` by concatenating them and applying **one** legal quadratic replacement `[a,b]→[c,d]`.  The output must contain `u`; check this, rather than trusting the JSON label.  If `a=b`, use two copies of the witness so the required multiplicity is present.  Each step must check odd positivity, exact two-input/two-output length, input availability, and `certificateValue 0 [a,b]=certificateValue 0 [c,d]` through `legalPairMove`.

Compute `W=Σ_(u,count) in catalyst count·W_u`.  Context closure of `AllowedMove` lets the seed insertion and DAG moves be replayed inside any certificate.  Since all W_u are reachable from the empty state, W is reachable from empty; `W≥catalyst` and its scalar value is one.  For the extra 7555 node, the final input is `[1079,5035]` and output `[1007,7555]`; both inputs occur earlier in the saved DAG.  This is the missing legality bridge in the obsolete wave-one replay.

## Main path and returning W

Let x be the virtual 71 certificate and y the actual 65-step path certificate.  Prove these **three** edges separately:

```
x       ->* x + W       by the checked borrow-unit construction in context x;
x + W   ->* y + W       by all 269 ordered main actions;
y + W   ->* y           by reversing the first construction in context y.
```

The middle endpoint must be checked as an exact multiset equality, including factor-2 count.  This is stronger than checking the integer relation lattice, unit scalar values, or the reported booleans in JSON.  Use an executable `Option RepairState` interpreter that fails on the first unavailable or non-preserving move.  `native_decide` can verify the finite DAG and trace once the data are embedded as Lean constants.  A generic soundness theorem for the interpreter is useful because it binds each accepted Boolean step to an `AllowedMove` constructor.  Keep that soundness theorem limited to this restricted action language; it need not characterize all Collatz repairs.

## Proof and performance suggestions

The high-level soundness proof is induction over the 96-node DAG and then over the 269-step list.  For each DAG node, reuse the context-lifting lemma for a legal Q move.  Prove the fixed units' value one with `short_units_and_cubic_exchange` or `unit_assisted_quadratic_repair_seven`, and the fixed cubic scalar equality with `essential_cubic_and_new_unit`.  Do not recompute a giant rational product of W from 7061 expanded factors; value one follows inductively from seed units and legal Q moves.  The finite checker should operate on multisets or sparse counts, so ordering does not become part of the theorem.  If a full `Relation.ReflTransGen` proof is too costly for one lap, first land the checked borrow DAG and main-path endpoint as separate named propositions, then wire them to the restricted reachability theorem in the next lap.  Do not replace the missing bridge by an arbitrary unit-insertion axiom.

The observable mathematical result is that this particular 71 semigroup certificate has an actual repair to the known path using Q, U2/U8/U13, and C5.  It does not show how to choose a target path for an unknown orbit or how to terminate repairs in general.
