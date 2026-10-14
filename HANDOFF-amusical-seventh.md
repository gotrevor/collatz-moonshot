# HANDOFF: seventh orbit formalization

## 2026-10-14 lap: geometric descent-tail bound proved

### Concrete advance

- Added `sum_ninetyNineHundredths_Icc_le` and `sum_descent_period_errors_le` in
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`.
- Proved `count_descent_between_geometric_le`: the count below `X` of centers admitting a
  forward or backward strict descent at some time `K < i ≤ L` is at most
  `200 * (99/100)^(K+1) * X + 6 * (L+1) * 324^L`.
- This closes the geometric-series bookkeeping left by the preceding lap.  The first term can
  be made an arbitrarily small fraction of `X` by fixing `K`; the second is sublinear after a
  sufficiently conservative logarithmic choice of `L`.  No ratified statement changed, and no
  axiom, `native_decide`, or new `sorry` was introduced.  The original `sparse_sweep` sorry
  remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.count_descent_between_geometric_le` (`FORMALIZE-TIER GREEN`; axiom
  ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` and the 100-character changed-Lean-line check (clean).

### Current blocker

There is no external blocker.  The exceptional-center density estimate is now in its final
quantitative form.  The remaining proof must map each visited point to a nearby centered-window
minimum, split off exceptional centers using this estimate, and bound the nonexceptional fibers
with `windowMin_card_mul_le`.

### Next highest-value attack

Prove the finite counting bridge from visited times to centers below `X`, separating centers
whose chosen minimizer lies outside `[-K,K]`.  On the complement use
`isWindowMin_sub_of_centered_minimizer` and `windowMin_card_mul_le`; then choose fixed `K`, a
logarithmic `L`, and `c` to discharge `sparse_sweep`.

## 2026-10-14 lap: finite descent union bound proved

### Concrete advance

- Added the generic finite-event union estimate `count_exists_mem_le_sum` in
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`.
- Proved `count_descent_between_le`: the count below `X` of centers admitting a forward or
  backward strict descent at some time `K < i ≤ L` is at most
  `Σ i ∈ Icc (K+1) L, (2(99/100)^i X + 4^i + 3^i + 4·324^i)`.
- This packages the one-time Chernoff estimates from the previous lap into the exact finite union
  needed after `centered_minimizer_outside_implies_descent`.  No ratified statement changed, and
  no axiom, `native_decide`, or new `sorry` was introduced.  The original `sparse_sweep` sorry
  remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms CollatzMoonshot.Amusical.count_descent_between_le`
  (`FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` and the 100-character changed-Lean-line check (clean).

### Current blocker

There is no external blocker.  The probabilistic exceptional set is now one explicit finite sum.
It remains to bound its geometric main term by `200 * (99/100)^(K+1) * X` and its additive term
by a constant times `324^(L+1)`, then combine it with the centered-minimizer bridge and packed
window minima.

### Next highest-value attack

Prove the two elementary geometric-sum bounds for `count_descent_between_le`.  Then define a
choice of fixed `K` from `η` and logarithmic `L = ⌊log X / (2 log 324)⌋`; the additive error is
`o(X)` while `L-K → ∞`.  Use `isWindowMin_sub_of_centered_minimizer` and
`windowMin_card_mul_le` to finish the time-window count in `sparse_sweep`.

## 2026-10-14 lap: finite-interval descent bounds proved

### Concrete advance

- Added `count_periodic_le_mul_add_period` in
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`: a periodic predicate with one-period
  proportion at most `q` has at most `q * X + M` members below `X`, including the incomplete
  final period.
- Proved `fwdSlopeDescends_periodic`, `bwdSlopeDescends_periodic`,
  `count_fwdSlopeDescends_le`, and `count_bwdSlopeDescends_le`.  These lift the complete-period
  Chernoff estimates to arbitrary initial intervals, with explicit `4^L` and `3^L` errors.
- Proved `count_iterate_lt_le` and `count_inv_iterate_lt_le`, transferring those estimates to
  the actual events `U^L n < n` and `U^-L n < n`.  The only additional error is the explicit
  Lemma W initial range `2 * 324^L`.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms CollatzMoonshot.Amusical.count_iterate_lt_le`
  (`FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- The same gate for `CollatzMoonshot.Amusical.count_inv_iterate_lt_le` was
  `FORMALIZE-TIER GREEN` with the same axiom ledger.
- `git diff --check` and the 100-character changed-Lean-line check (clean).

### Current blocker

There is no external blocker.  The individual descent events now have the required arbitrary
interval bounds.  The remaining finite Lemma T bookkeeping is the union bound over
`K < i ≤ L`; its additive error is the sum of `4^i + 3^i + 4 * 324^i`, which must be made
`o(X)` by choosing `L` logarithmically below `log X`.  This then feeds the already-proved
centered-minimizer bridge and window-minimum packing.

### Next highest-value attack

Package the union of forward/backward descent events over `Finset.Icc (K+1) L` and prove its
count is bounded by the sum of the two new one-time estimates.  Bound the geometric main term by
`200 * (99/100)^(K+1) * X` and the additive error by a constant times `324^(L+1)`.  Then combine
`centered_minimizer_outside_implies_descent`, `isWindowMin_sub_of_centered_minimizer`, and
`windowMin_card_mul_le` to assemble the final count used by `sparse_sweep`.

## 2026-10-14 lap: actual descents identified with Chernoff slope events

### Concrete advance

- Refactored the proof of Lemma W in `CollatzMoonshot/AmusicalSeventh/Sparse.lean` so its
  load-bearing individual comparison result is public as `iterate_le_iff_words_of_ge`.
  It simultaneously characterizes every forward and backward comparison through time `L` above
  the explicit `2 * 324^L` threshold; `isWindowMin_iff_words_of_ge` is now its short corollary.
- Proved `iterate_lt_iff_fwdSlopeDescends_of_ge` and
  `inv_iterate_lt_iff_bwdSlopeDescends_of_ge`.  Thus the actual events `U^i n < n` and
  `U^-i n < n` are exactly the `FwdSlopeDescends` and `BwdSlopeDescends` residue events already
  controlled by the Chernoff estimates.  The strict conversion explicitly excludes equality of
  the powers of two and three by parity.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; exactly the original
  `sparse_sweep` sorry warning).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.iterate_lt_iff_fwdSlopeDescends_of_ge` (`FORMALIZE-TIER GREEN`; axiom
  ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- The same gate for `CollatzMoonshot.Amusical.inv_iterate_lt_iff_bwdSlopeDescends_of_ge` was
  `FORMALIZE-TIER GREEN` with the same axiom ledger.
- `git diff --check` and the 100-character changed-Lean-line check (clean).

### Current blocker

There is no external blocker.  The comparison-to-Chernoff bridge is complete.  The remaining
finite Lemma T bookkeeping is to lift the complete-period bounds to `[0,X)`, union-bound over
`K < i ≤ L`, and discard the initial range below `2 * 324^L`.  The final headline still needs
that exceptional-set estimate combined with the deterministic minimizer bridge and window-minimum
packing, followed by the elementary choices of `K`, `L`, and `c`.

### Next highest-value attack

Define the forward/backward descent predicates at time `i`, prove their periodicity modulo `4^i`
and `3^i`, and apply `WindowCount.count_periodic_bounds` plus the two
`*_residue_proportion_le_ninetyNineHundredths` theorems.  Sum over `K < i ≤ L`; this gives the
finite geometric exceptional-set bound needed for `sparse_sweep`.

## 2026-10-14 review lap: one-sided Chernoff residue bounds proved

### Concrete advance

- Fresh review confirmed that all four ratified theorem types are unchanged from kickoff commit
  `5fa5871` and that `sparse_sweep` is the sole scoped proof hole.  The minimizer-to-descent
  reduction from the previous lap is therefore still on the direct route to the headline.
- Added the shared forward/backward Chernoff engine to
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`.  The normalized word weight uses factors
  `1 / √6` and `1 / √3`; `sum_descentChernoffWeight` proves its exact total mass is `ρ^L`, where
  `ρ = 1 / √6 + 1 / √3`, and `descentChernoffRate_lt_ninetyNineHundredths` proves
  `ρ < 99 / 100`.
- Proved the two pointwise Markov inequalities `fwdSlopeDescends_weight_lt` and
  `bwdSlopeDescends_weight_lt`.  The same weight handles the uniform forward-word law and the
  nonuniform backward law because a backward word with `a` marked letters has residue-fiber
  weight `2^a / 3^L`.
- Proved generic branch-word fiber decompositions and the load-bearing finite estimates
  `fwdSlopeDescends_residue_proportion_le_ninetyNineHundredths` and
  `bwdSlopeDescends_residue_proportion_le_ninetyNineHundredths`: the share of length-`L`
  forward residues modulo `4^L`, respectively backward residues modulo `3^L`, with descending
  affine slope is at most `(99/100)^L`.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; exactly the original
  `sparse_sweep` sorry warning).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.fwdSlopeDescends_residue_proportion_le_ninetyNineHundredths`
  (`FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- The same gate for
  `CollatzMoonshot.Amusical.bwdSlopeDescends_residue_proportion_le_ninetyNineHundredths`
  was `FORMALIZE-TIER GREEN` with the same axiom ledger.
- `git diff --check` and the 100-character changed-Lean-line check (clean).

### Current blocker

There is no external blocker.  The probabilistic core of Lemma T is now proved at the exact
branch-word/residue level.  What remains is bookkeeping that connects an actual comparison
`U^i n < n` or `U^-i n < n` above the explicit Lemma W threshold to `FwdSlopeDescends i` or
`BwdSlopeDescends i`, lifts the complete-period bounds to an initial interval, and union-bounds
over `K < i ≤ L`.

### Next highest-value attack

Extract the individual forward and backward comparison equivalences from the proof of
`isWindowMin_iff_words_of_ge` (without duplicating its threshold arithmetic).  Then prove the
periodic initial-interval count and finite geometric union bound.  Combine that exceptional-set
bound with `centered_minimizer_outside_implies_descent`,
`isWindowMin_sub_of_centered_minimizer`, and `windowMin_card_mul_le`; the remaining final step is
the elementary choice of `K`, logarithmic `L`, and `c` in `sparse_sweep`.

## 2026-10-14 lap: exceptional minimizers reduced to descent events

### Concrete advance

- Proved `centered_minimizer_outside_implies_descent` in
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`.  On an infinite orbit, if a minimum of the
  centered `L`-window occurs at an offset with `|t| > K`, then either a forward or backward
  iterate at some time `i` with `K < i ≤ L` is strictly below the center.
- The strict inequality uses injectivity of the integer orbit parametrization; this removes the
  equality/periodic case cleanly.  The result reduces the exceptional-offset event to a finite
  union of the exact one-sided descent events to which the weighted Boolean-word Chernoff count
  applies.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh` (`FORMALIZE-TIER GREEN`; exactly the original
  `sparse_sweep` proof debt).
- `git diff --check` and the 100-character Lean line check (clean).

### Current blocker

There is no external blocker.  The remaining load-bearing input is now a finite bound for each
one-sided event `U^i n < n` and `U^-i n < n` over a complete residue system modulo `12^L`.
Summing those bounds for `K < i ≤ L` gives Lemma T via the theorem proved this lap.

### Next highest-value attack

Prove the individual weighted word bounds for `U^i n < n` and `U^-i n < n`.  Use an integer
Chernoff weight (or rational square-root-free upper bound) and the exact forward/backward word
fiber counts already in `AmusicalWindow.lean`; then union-bound over `i > K` and combine with
`isWindowMin_sub_of_centered_minimizer` and `windowMin_card_mul_le`.

## 2026-10-14 lap: deterministic offset-to-window-minimum bridge

### Concrete advance

- Proved `exists_centered_window_minimizer` in
  `CollatzMoonshot/AmusicalSeventh/Sparse.lean`: every finite centered orbit window has an
  offset `t ∈ [-L,L]` whose orbit value is minimal throughout that window.
- Proved `isWindowMin_sub_of_centered_minimizer`: if such a minimizing offset satisfies
  `|t| ≤ K ≤ L`, then the shifted point is an `(L-K)`-window minimum.  The proof explicitly
  transports the forward and backward comparisons through integer powers of `amusicalPerm`.
- This closes the deterministic bridge stated in the paper proof of `sparse_sweep`.  After the
  exceptional offsets `|t| > K` are counted, every remaining visited point maps to a packed
  `(L-K)`-window minimum using this theorem and `windowMin_card_mul_le`.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `ulimit -n 65536; lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `ulimit -n 65536; ~/personal/bin/lean-green
  /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target CollatzMoonshot.AmusicalSeventh`
  (`FORMALIZE-TIER GREEN`; exactly the original
  `sparse_sweep` proof debt).
- `git diff --check` and the 100-character Lean line check (clean).

### Current blocker

There is no external blocker.  The remaining route-decisive result is precisely the probabilistic
half of Lemma T: uniformly count residues modulo `12^L` for which every minimizing offset of the
centered `L`-window lies outside `[-K,K]`.  The target geometric tail is
`2 * sum_{i>K} ρ^i`, with `ρ = 1/√6 + 1/√3 < 1`.

### Next highest-value attack

Define a deterministic least minimizing offset (to avoid choice ambiguity), show that the events
`t > K` and `t < -K` force one-sided descending records of lengths `K+1, K+2, ...`, and bound
their weighted Boolean-word counts.  Package that as a finite residue-cardinality inequality;
then combine `isWindowMin_sub_of_centered_minimizer`, `windowMin_card_mul_le`, and the explicit
`2 * 324^L` low-value error to prove `sparse_sweep`.

## 2026-10-14 lap: explicit Lemma W closed

### Concrete advance

- Proved `isWindowMin_iff_words_of_ge` in `CollatzMoonshot/AmusicalSeventh/Sparse.lean`.
  For every `n ≥ 2 · 324^L`, the condition `IsWindowMin L n` is exactly the conjunction of
  `FwdGood` and `BwdGood` on its two branch words.  Since those words depend respectively on
  `n mod 4^L` and `n mod 3^L`, this is the requested Lemma W residue characterization modulo
  `12^L`.
- The proof writes `n = c + 12^L q`, uses the previous lap's bound that all length-`L`
  iterates of `c` are below `24^L`, and proves `24^L < q` from the ratified threshold via
  `12^L (24^L + 1) ≤ 2 · 324^L`.  The exact affine formulas and slope inequalities from
  `AmusicalWindow.lean` then decide every forward and backward comparison.
- No ratified statement changed, and no axiom, `native_decide`, or new `sorry` was introduced.
  The original `sparse_sweep` sorry remains the sole scoped obligation.

### Verification

- `lake build CollatzMoonshot.AmusicalSeventh.Sparse` (8712 jobs, green).
- `lake build CollatzMoonshot.AmusicalSeventh` (green; only the expected original
  `sparse_sweep` sorry warning).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh` (`FORMALIZE-TIER GREEN`; exactly the original
  `sparse_sweep` proof debt).
- `git diff --check` and the 100-character Lean line check (clean).

### Current blocker

There is no external blocker.  Lemma W is complete.  The route-decisive missing result is now
Lemma T: a uniform finite count on residues modulo `12^L` showing that the minimizing offset of
an `L`-window lies outside `[-K,K]` for at most a geometric `O(ρ^K)` share of residues.  Existing
`FwdGood`/`BwdGood` weighted word counts provide the finite probability space, but the offset-tail
event and its Chernoff estimate have not yet been packaged in Lean.

### Next highest-value attack

Define the least minimizing offset in the finite window and express the one-sided events
`U^i n < n` and `U⁻ᵢ n < n`, using `isWindowMin_iff_words_of_ge` after shifting to the chosen
minimum.  Prove the finite weighted Chernoff bounds over forward and backward branch words, then
combine them into the `2 ∑_{i>K} ρ^i` residue count.  This supplies the exceptional-set term
needed to combine with `windowMin_card_mul_le` and finish `sparse_sweep`.

## 2026-10-13 lap: explicit window-representative growth bound

### Concrete advance

- Added `CollatzMoonshot/AmusicalSeventh/Sparse.lean`, the quantitative helper module for the sole
  remaining target, `sparse_sweep`.
- Proved `amusical_max_step`: on nonnegative integers, both `U` and `U⁻¹` are at most `2z+1`.
- Proved the iterated bounds `amusical_iterate_lt_two_pow_mul` and
  `amusicalInv_iterate_lt_two_pow_mul`.
- Proved the load-bearing finite-representative estimate
  `amusical_window_representative_lt`: if `c < 12^L` and `t ≤ L`, then both `U^t(c)` and
  `U⁻ᵗ(c)` are below `24^L`.  This supplies an explicit bound on the affine offsets in the exact
  residue formulas and replaces the opaque `windowBound` at the start of Lemma W.
- Imported the new helper module into the ratified target file.  No statement was changed, and no
  axiom, `native_decide`, or new `sorry` was introduced.  The original `sparse_sweep` sorry is the
  only scoped obligation.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Sparse.lean` (green).
- `lake build CollatzMoonshot.AmusicalSeventh.Sparse CollatzMoonshot.AmusicalSeventh`
  (8716 jobs, green; only the expected original `sparse_sweep` sorry warning).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh` (8716 jobs, `FORMALIZE-TIER GREEN`; the gate reports exactly
  the original `sparse_sweep` proof debt).
- `git diff --check` (clean).

### Current blocker

There is no external blocker.  Lemma W still needs its comparison step.  Write
`n = c + 4^L q` forward and `n = c + 3^L q` backward, with `c` the appropriate residue of a
joint representative modulo `12^L`.  The new `24^L` bound controls `|U^t(c)-c|` and
`|U⁻ᵗ(c)-c|`; the hypothesis `n ≥ 2·324^L` makes each quotient larger than that error.  Then
`add_mul_le_add_mul_iff` identifies the comparison with the affine slope, hence with the residue.

### Next highest-value attack

Formalize that quotient/error inequality and package Lemma W as an equivalence between
`IsWindowMin L n` and a predicate of `n % 12^L` for `n ≥ 2·324^L`.  Afterward define the offset of
the minimum of the finite `L`-window and prove the integer-weight Chernoff tail over one complete
residue system; this is the remaining probabilistic input before the existing
`windowMin_card_mul_le` packing theorem closes `sparse_sweep`.

## 2026-10-13 review lap: full residue transitivity closed

### Concrete advance

- Proved the ratified `amusical_pow_classUnion_invariant` statement for every positive `m` and
  `M`, without changing its type.  Exactly one target sorry now remains: `sparse_sweep`.
- The fresh review replaced the handoff's proposed simultaneous three-factor CRT construction
  with a smaller proof.  If `S : ℤ → Prop` is periodic modulo `M` and invariant under a long
  `amusical` iterate, exact forward cylinders remove `ordProj[2] M` from its period and exact
  backward cylinders remove `ordProj[3] M`.
- For the remaining period coprime to `6`, the all-`A` branch word and the word consisting of one
  `B` followed by `A`s induce a translation `δ` satisfying
  `4^m · δ ≡ -2 · 3^(m-1)`.  Thus `δ` is a unit, so invariance under its translation makes
  `S` constant.
- Added the proof engine `amusical_pow_classUnion_invariant_of_image_eq` and its cylinder/period
  helpers to `CollatzMoonshot/AmusicalSeventh/Residue.lean`.  No new axiom, `native_decide`, or
  sorry was introduced.

### Verification

- Exhaustive review control: the induced residue graph is strongly connected for
  `1 ≤ M ≤ 80`, `1 ≤ m ≤ 6` (correctly enumerating inputs modulo `M · 4^m`).
- `lake env lean CollatzMoonshot/AmusicalSeventh/Residue.lean` (green).
- `lake build CollatzMoonshot.AmusicalSeventh.Residue` (8710 jobs, green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; only the original `sparse_sweep`
  sorry warning).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.amusical_pow_classUnion_invariant` (8713 jobs,
  `FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` (clean).  The ratified theorem statement is unchanged from kickoff commit
  `5fa5871`; only its proof body changed this lap.

### Current blocker

There is no external blocker.  The sole scoped obligation is now `sparse_sweep`.  Its proof needs
the quantitative finite-residue tail estimate from the paper, not merely the existing asymptotic
`windowMinDensity`: for `L` logarithmic in `X`, all but `ε(K)X + O(12^L)` points below `X` must
have their `L`-window minimum within `K` orbit steps.  The existing window modules provide exact
cylinder transport and the separation theorem, but do not yet package that offset-tail estimate.

### Next highest-value attack

Formalize Lemma W first as a checked finite-residue statement: above an explicit exponential
threshold, the comparisons `amusical^[i] n < n` and `amusicalInv^[i] n < n` for `i ≤ L` depend
only on the corresponding multiplicative slope, hence only on `n mod 12^L`.  Reuse the exact
affine formulas in `AmusicalWindow.lean`, and verify the paper's proposed `2 · 324^L` threshold
rather than assuming it.  Then state the finite Chernoff/counting lemma over those residue classes;
that is the route-decisive input to the final packing argument.

## 2026-10-13 lap: three-primary residue transitivity closed

### Concrete advance

- Extended `CollatzMoonshot/AmusicalSeventh/Residue.lean` with the full residue-transitivity
  theorem for every power-of-three modulus, `amusical_pow_classUnion_invariant_pow_three`.
- Proved `exists_amusical_mul_iterate_modEq_pow_three`: after a time constrained to be a multiple
  of any positive `m`, a point in any prescribed class modulo `3^b` can land in any prescribed
  output class.
- The construction works backward from the output class.  Exact backward-cylinder transport has
  slope a power of two, hence a unit modulo `3^b`; applying the matching forward iterate then
  gives the required point-to-point reachability.
- No ratified statement changed, no axiom or `native_decide` was introduced, and no new `sorry`
  was added.  The two original targets remain open.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Residue.lean` (green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; only the two original target
  sorry warnings).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.amusical_pow_classUnion_invariant_pow_three` (`FORMALIZE-TIER GREEN`;
  axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` (clean).

### Current blocker

There is no external blocker.  Both primary-power components of
`amusical_pow_classUnion_invariant` are complete.  The route-decisive remaining part is
transitivity modulo the factor coprime to `6`, followed by a simultaneous CRT construction that
absorbs the binary prefix and ternary suffix without disturbing that coprime residue.  The
ratified `sparse_sweep` theorem remains untouched.

### Next highest-value attack

Formalize the coprime-modulus affine-word translation.  For `N` coprime to `6`, package the two
branch maps as affine permutations of `ZMod N`; words of length divisible by `m` contain both
`A^m` and `A^(m-1) * B`, whose quotient is the nonzero translation `A^-1 * B`.  Iterate that
translation to connect arbitrary residues, then combine it with the proved power-of-two and
power-of-three cylinders by CRT to discharge the ratified theorem.

## 2026-10-13 lap: two-primary residue transitivity closed

### Concrete advance

- Added `CollatzMoonshot/AmusicalSeventh/Residue.lean` and proved the full residue-transitivity
  theorem for every power-of-two modulus, `amusical_pow_classUnion_invariant_pow_two`.
- Proved generic image-equality infrastructure: equality of a set with its image under a
  permutation makes membership invariant under every multiple of the given iterate.
- Proved `exists_amusical_mul_iterate_modEq_pow_two`: after a time constrained to be a multiple
  of any positive `m`, a point in any prescribed class modulo `2^b` can land in any prescribed
  output class.  The proof uses the exact forward-cylinder formula; its slope `3^t` is a unit
  modulo `2^b`.
- No ratified statement changed, no axiom or `native_decide` was introduced, and no new `sorry`
  was added.  The two original targets remain open.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Residue.lean` (green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; only the two original target
  sorry warnings).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.amusical_pow_classUnion_invariant_pow_two` (`FORMALIZE-TIER GREEN`;
  axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` (clean).

### Current blocker

There is no external blocker.  For `amusical_pow_classUnion_invariant`, the `2`-primary factor is
now complete.  The symmetric backward-cylinder argument should close the `3`-primary factor.
The route-decisive remaining part is transitivity modulo the factor coprime to `6`, where branch
words must generate a translation in the finite affine group.  `sparse_sweep` remains untouched.

### Next highest-value attack

Prove `exists_amusical_mul_iterate_modEq_pow_three` from
`amusicalInv_iterate_add_pow_three_mul_slope`, then package the power-of-three class-union
corollary.  After that isolate a coprime-modulus affine-word translation lemma and combine the
three components by CRT to discharge the ratified theorem.

## 2026-10-13 lap: rewiring barrier closed

### Concrete advance

- Proved the ratified `rewire_single_orbit` statement without changing its type.  Two target
  sorries now remain in `CollatzMoonshot/AmusicalSeventh.lean`.
- The fresh review found that the paper's annular upper bounds are unnecessary for sparsity.
  `sparseCutPoint` enumerates every `(base point, requested time, direction)` and chooses the
  corresponding orbit cut above `(q+1)^2`.  The resulting `sparseOrbitCuts` meets both tails of
  every infinite orbit cofinally, contains only infinite-orbit points, and every decidable subset
  has density zero.
- `nextSparseCut` and `prevSparseCut` are inverse nearest-cut maps.  The finite segments between
  cuts are reconnected so their induced successor is a conjugate of translation by one on `ℤ`.
  This makes all original infinite-orbit points lie on one new orbit and leaves finite orbits
  untouched.
- The changed domain satisfies the explicit stronger bound
  `card {n < N | τ n ≠ σ n} ≤ Nat.sqrt (2*N+1)`, using only the forward half of the ratified
  doubling hypothesis.  Its real square-root majorant proves the required density limit.
- No new axiom and no `native_decide` were introduced.  The two ratified statements still open
  are `amusical_pow_classUnion_invariant` and `sparse_sweep`.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Rewire.lean` (green).
- `lake build CollatzMoonshot.AmusicalSeventh.Rewire` (8710 jobs, green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; warnings only for the two remaining
  target sorries).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms CollatzMoonshot.Amusical.rewire_single_orbit`
  (8711 jobs, `FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`,
  `propext`).
- `git diff --check` (clean).  The ratified theorem statement is unchanged from kickoff commit
  `5fa5871`; only its proof body changed this lap.

### Current blocker

There is no external blocker.  `amusical_pow_classUnion_invariant` is now next by the ratified
order and requires a uniform strong-connectivity argument for the residue graph of every positive
power of `amusical`.  The existing cylinder transport module supplies exact forward and backward
congruence control but does not yet package the mixed `2`/`3`/coprime CRT reachability theorem.
`sparse_sweep` remains the final and heaviest target.

### Next highest-value attack

Attack `amusical_pow_classUnion_invariant`.  First state and prove a point-to-point residue
reachability lemma: for `0 < m,M` and residues `r,s : ZMod M`, choose integers `x ≡ r` and a
positive multiple `L` of `m` with `amusical^[L] x ≡ s`.  Reuse
`amusical_iterate_add_forwardPeriod_mul`, `amusical_iterate_modEq_two`, and
`amusicalInv_iterate_modEq_three`; isolate the modulus coprime to `6` before the final CRT.  Then
derive the target from forward/backward invariance of the class union.  Adversarially test the
reachability statement at small `m,M` before committing its exact quantifiers.

## 2026-10-13 lap: rewiring properness and annulus crossing

### Concrete advance

- Added `CollatzMoonshot/AmusicalSeventh/Rewire.lean`, imported by the scoped target.
- Proved the generic kernel-checked lemma `perm_zpow_apply_injective_of_infinite`: the integer
  parametrization of any infinite permutation orbit is injective.
- Derived `finite_orbit_times_le` and `exists_nat_iterate_gt`: an infinite orbit visits every
  bounded subset at only finitely many integer times and is unbounded in both time directions.
- Proved `exists_forward_backward_mem_Ico`, the first quantitative load-bearing input to
  `rewire_single_orbit`: under the ratified doubling bound, every infinite orbit crosses
  `[Y, 2Y)` both forward and backward whenever its starting point is below `Y`.
- No ratified statement was changed. The three target sorries remain explicit.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Rewire.lean` (green; one non-finding style
  suggestion concerning a local `NeZero` instance).
- `lake build CollatzMoonshot.AmusicalSeventh.Rewire CollatzMoonshot.AmusicalSeventh` (8711 jobs,
  green; only the three expected target-sorry warnings and inherited publish-tier suggestions).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh` (8711 jobs, `FORMALIZE-TIER GREEN`; exactly the three expected
  target sorries remain).

### Current blocker

`rewire_single_orbit` still needs the global combinatorial construction. The analytic/properness
part is now closed. The remaining work is to enumerate infinite orbit classes, choose annular cuts
with a quantitative `O((log N)^2)` support bound, split the original bi-infinite lines into finite
segments, enumerate those segments by `ℤ`, and package the successor relation as an
`Equiv.Perm ℕ` while proving agreement on finite orbits and density zero.

### Next highest-value attack

Define the equivalence relation `a ~ b ↔ ∃ j : ℤ, (σ ^ j) a = b` on the infinite-orbit subtype and
obtain a countable transversal ordered by least natural representative. For orbit number `i`, use
`exists_forward_backward_mem_Ico` at scales `4^k`, `k ≥ i`, to select two cuts. First prove the
standalone counting lemma that these selected cut values have density zero; only then build and
verify the segment-splicing permutation.

## 2026-10-13 lap: cofinite reformulation closed

### Concrete advance

- Proved `atLeastSeven_of_orbit8_not_cofinite` without changing its ratified statement.
- The proof removes the finite `knownCycleMembers` set from the assumed infinite complement of
  `amusicalOrbit 8`, chooses a nonnegative witness `n`, and builds the seven representatives
  `{n, 0, 1, 2, 4, 44, 8}`.
- Separation from the five known finite cycles uses `amusicalOrbit_subset_of_closed`; separation
  from the orbit of `8` uses the witness's membership in the assumed set difference; separation
  among the original six representatives uses `amusical_six_distinct_orbits`.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; warnings only for the three
  remaining ratified target sorries).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.atLeastSeven_of_orbit8_not_cofinite` (8710 jobs,
  `FORMALIZE-TIER GREEN`).  The proved theorem uses exactly `Classical.choice`, `Quot.sound`, and
  `propext`; the gate reports only the three remaining target sorries.

### Current blocker

Three independent targets remain: `sparse_sweep`, `amusical_pow_classUnion_invariant`, and
`rewire_single_orbit`.  There is no external blocker.  Each needs substantial new infrastructure;
the first proof was intentionally closed before opening one of those larger constructions.

### Next highest-value attack

Attack `rewire_single_orbit` next, as directed by the kickoff.  First isolate reusable lemmas that
an infinite orbit of a permutation of `ℕ` visits every bounded interval only finitely often and
therefore crosses each sufficiently high dyadic annulus in both time directions.  Then formalize a
sparse family of cuts before constructing the rewired permutation.  Keep all helpers in
`CollatzMoonshot/AmusicalSeventh/` and leave the four ratified statements unchanged.
