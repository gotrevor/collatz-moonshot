# Handoff: Campaign B complete — uniform explicit fixed-block length bound

Date: 2026-09-13. Branch: `main`. No push. Supersedes the architecture-lap-1
formalization boundary in `HANDOFF-2026-09-13-block-composition.md`.

**Stopped.** Campaign B's target is proved: every odd-start acyclic paradoxical
segment with at most b maximal odd runs has length below the explicit bound
`L(b)=4*((2^b-1)*(b+53342))^2+b`. No Campaign B obligation remains; stop after
this completion checkpoint and `box done`, without starting unassigned work.

## Headline theorem and scope

`CollatzMoonshot.FrontA.acyclicParadoxical_length_lt_of_oddRunCount`
in `CollatzMoonshot/FrontA/FixedBlocks.lean` states:

```lean
theorem acyclicParadoxical_length_lt_of_oddRunCount (n m b : ℕ)
    (hodd : n % 2 = 1) (hap : AcyclicParadoxical n m)
    (hcount : oddRunCount (traceWord n m) ≤ b) :
    m < fixedBlockLengthBound b
```

`fixedBlockLengthBound b = 4*((2^b-1)*(b+53342))^2+b`.
The bound is explicit and monotone. The factor 4 replaces the proposed
architecture factor 2, permitting elementary natural-number numerical feedback.
This is a bound for all starts and lengths, not a finite census or a hypothesis
with the original target hidden inside it. The b=0 case is handled vacuously.

`oddRunCount` counts true-to-false adjacent pairs with a false sentinel after
the word. Each maximal true run contributes exactly its final falling edge,
including a terminal odd run. The sentinel introduces no trajectory step or
endpoint parity requirement. The decomposition theorem extracts exactly that
many positive-odd-length blocks, allowing zero even steps after the last one.

The result does not assert the emptiness of rungs 4 and 5 at all lengths, or
bound the number of runs independently of the segment. Those are not part of
this assigned campaign. Campaign A2 (`c3aba74`) and rung 3 remain settled;
`DIRECTION.md` is deliberately unchanged.

## Decisive composition proof

The original inequality survives, but its proof is simpler than the proposed
maximum-partial-product construction. `FrontA/BlockCycle.lean` proves it for
the larger rational fixed-point positivity relaxation:

```
2^a < (b/δ)^(2^b-1),       2^m < 2^b*3^a,       δ=1-3^a/2^m.
```

For a rational cycle `z_next=r*z+s`, with every `z>0`, `s<1`, and total
multiplier R in `(0,1)`, suppose every z is at least b/(1-R). Set c=(1-R)/b.
Then `(1-c)*z_next<r*z`. Multiplication and cancellation give `(1-c)^b<R`,
contradicting Bernoulli's `R=1-b*c≤(1-c)^b`. Thus a small vertex exists.
This lemma itself works for any finite permutation, even with several cycles.

For each actual block multiplier `r=3^q/2^(q+e)`, q>0 implies
`r+1/2≤2^q`. With `z≥2^q≥2` and s<1 this gives `z_next<z^2`. Starting at
the small vertex, repeated squaring bounds the j-th value by `(b/δ)^(2^j)`.
Multiplying `2^q_j≤z_j` proves the mass inequality, with the cyclic exponent
sum transported by the explicit `finCycle` permutation. This last step uses
a single full cycle. The length inequality uses the existing
`affineCycle_multiplier_lower`.

The rational envelope is also constructed, rather than assumed. Given the
actual path u and prefix products P, set

```
c=(u_b-u_0)/(1-P_b),       z_i=u_i+P_i*c.
```

Then `z_b=z_0`, each `z_i>u_i`, and the affine step identities persist.
This uses the actual endpoint displacement, hence retains the prefix
remainders. It does not posit an integral rotated orbit or integer cycle.
`headBlock_cascade_composition` connects this construction to all integer
head identities, whose positive scales give `u_i≥2^q_i`.

## Numerical feedback and word bridge

`FrontA/BlockLength.lean` supplies the following closed chain. Let
`t=Nat.log 2 a`, `C=2^b-1`, `H=C*(b+53342)`. The existing Rhin-lite polynomial
measure gives, in both the near-critical and complementary regimes,

```
2^m ≤ 2^(52906+436*(t+1))*(2^m-3^a).
```

Composition and b≤2^b give `a<C*(b+52906+436*(t+1))≤H*(t+1)`.
For t≥4, an elementary induction gives `(t+1)^2≤2*2^t≤2a`. Squaring and
cancelling a>0 yields `a<2H^2`. For t<4, a<16 gives the same bound.
Finally `m<b+2a<4H^2+b`. No new Diophantine input is required.

`FrontA/FixedBlocks.lean` extracts the word's maximal runs using the existing
true-/false-run peeling lemmas. It splits `traceWord` at every block to obtain
all actual head identities and the correct endpoint, applies
`headBlock_cascade_length_bound`, and uses monotonicity for at most b runs.

All three new modules are in the default build. No `sorry`, new named axiom,
or new `native_decide` occurs in them. The old maximum-product lemmas remain
valid and untouched; constructing their missing maximum is no longer needed
for this objective.

## Verification actually run

1. Narrow compiler iterations, ending green:
   - `lake env lean CollatzMoonshot/FrontA/BlockCycle.lean`
   - `lake env lean CollatzMoonshot/FrontA/BlockLength.lean`
   - `lake env lean CollatzMoonshot/FrontA/FixedBlocks.lean`
   Dependency builds for `BlockCycle` and `BlockLength` also passed.
2. Final real full gate: `bash scripts/check-fixed-block-bound.sh`.
   It invokes `~/personal/bin/lean-green` on the whole repository, auditing
   six declarations: rational composition, integer-cascade composition,
   numerical feedback, the actual headline theorem, boundary controls, and
   the non-vacuity corollary. **8771 jobs; FORMALIZE-TIER GREEN.**
3. `python3 experiments/block_composition.py --controls` — passes the updated
   small-vertex/squaring checks on 4,000 actual cascades, the rung-3 formula
   controls, and all 320 A1 admitting starts through start 5000. The 2305/2313
   pair retains prefix numerators 7207/1375, opposite admission, and run counts
   13/11. Negative controls still refute dropping one joint's positivity.
4. Updated complete exact probes:
   - `python3 experiments/block_composition.py --census 4 27 17`: 67,200 tuples,
     8,581 fixed-point survivors, 5,052 positivity-leaf survivors, 2,811 ceiling
     survivors, zero admissions.
   - `python3 experiments/block_composition.py --census 5 27 17`: 382,200 tuples,
     125,875 fixed-point survivors, 95,678 positivity-leaf survivors, 74,503
     ceiling survivors, zero admissions.
   All 134,456 fixed-point survivors pass the new mechanism. The historical
   lap-1 46-step exhaustive scans were not repeated.
5. `bash scripts/check-proof-debt.sh` — zero disclosed sorries.
6. `git diff --check` — clean.

The new `oddRunCount_boundary_controls` is `decide +kernel`, with **no axioms**.
It checks singleton/terminal odd runs, 7@8 and 9@8, and both shared-trunk counts.
`fixedBlockLength_nonvacuous` applies the new theorem to the established
`AcyclicParadoxical 7 8` witness.

### Exact trust accounting and the first gate's diagnostic

The rational and integer-cascade composition theorems print exactly the standard
triple `[propext, Classical.choice, Quot.sound]`. The numerical and headline
length theorems additionally inherit eleven existing finite `native_decide`
certificates from the Rhin-lite polynomial measure. These are **not** new
mathematical hypotheses and were already in source before this lap.

The first full build succeeded, but `lean-green --axioms` reported RED because
its built-in native list recognizes only `Lean.ofReduceBool` and
`Lean.trustCompiler`, while this toolchain reports generated certificate names.
Source inspection confirmed all eleven are existing `native_decide` proofs in
`RhinLite.lean`, `RhinLiteCritical.lean`, `RhinLiteInterval.lean`,
`RhinLiteMaximum.lean`, and the local finite certificate in
`RhinLiteApprox.rhinLiteI₁_ratio_base` (line 1822).

The reproducible gate script explicitly allows only those exact eleven names,
as authorized by FORMALIZE policy; it has no wildcard or changed gate logic.
It records the full list, including `_native.native_decide.ax_1_2` for
`rhinLiteI₁_ratio_base` and `ax_1_1` for the other ten. The final gate is green
with this disclosed inherited native trust. **Do not summarize the final
headline as bare-trust-base-only.** `scripts/AxiomAudit.lean` includes the new
API declarations; its entire historical ledger was not separately rerun.

No Aristotle tool was available. No subagents were used. The read-only Lean
reference corpus was searched, including the unconditional-iterate-identity
advice for cyclic proofs. Only the focus repository was edited.

## Stopping decision

The scoped target is met. There is no mathematical or operator blocker and no
remaining Campaign B attack. Call `box done` for the proved explicit uniform
fixed-block bound. A future lap should await a new operator objective rather
than reopen the completed architecture, A2, or rung 3.
