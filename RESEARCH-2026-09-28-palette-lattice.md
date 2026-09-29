# A finite palette repair of the published 71 certificate

```sh
./experiments/catalytic_palette.py test
./experiments/catalytic_palette.py replay71 experiments/catalytic_palette_71_witness.json
./experiments/catalytic_palette.py lattice71 --max-aux-label 100000 --neighbor-waves 1 --wave-width 10
```

This note continues [the count-ledger checkpoint](RESEARCH-2026-09-27-palette-delegation.md)
and the [borrowable-catalyst criterion](RESEARCH-2026-09-27-borrowable-catalysts.md).
It closes the concrete repair question for the published certificate of 71
under the controlled palette: quadratic exchanges, insertions and removals of
U2/U8/U13, and the essential cubic
`{5,55,83} <-> {11,13,17}`.  The destination is the **already known** 65-step
trajectory of 71, so this certificate does not prove termination for an
unknown Collatz start or supply a general repair algorithm.

## Exact integer relation

The virtual certificate has 16 factors of 2 and 16 odd factors, scalar value
71.  The known trajectory certificate has 28 factors of 2 and 37 odd factors.
The four-count ledger forces net `+9 U8`, `-3 U13`, and `-3` forward cubics,
equivalently three reverse cubics; net U2 is zero.  After applying these net
changes formally, the remaining odd-factor difference is an integer sum of
quadratic exchanges.  The saved [witness](experiments/catalytic_palette_71_witness.json)
has 125 signed rows, expanding to 254 oriented quadratic applications.  Its
largest label is 95,381.  Every label in these rules is 3-free.  The exact
integer vector sum is checked coordinate by coordinate; a rational row-span
calculation is never substituted for integer membership.

The search is reproducible.  It starts with all pair fibers whose input
contains a residual label, restricting their four labels to the 526-label
six-round saved borrowability set plus the target labels.  It then adds the
complete quadratic-neighbor lists for residual labels with all labels at
most 100,000.  After an integer remainder remains, one targeted wave expands
the ten largest labels of that remainder.  Sparse Euclidean row reduction
with integer combinations yields zero remainder.  This search procedure is a
way to find the witness, not a completeness claim about the full rule family.

## Positive catalyst and legal move sequence

The [replay artifact](experiments/catalytic_palette_71_replay.json) records
the source and target vectors, the signed quadratic rows, the ordered 269-move
main sequence, a common catalyst C, and a value-one word W containing C.  The
main sequence consists of nine U8 insertions, three reverse cubics, 254
quadratic applications, and three U13 removals, interleaved by a deterministic
availability-first scheduler.  Given C, every move is available and the
endpoint is exactly target+C.

The catalyst C has 40 odd labels.  The explicit borrowed unit W has 7,061
factors, including 2,667 factors of 2, on 109 nonzero labels.  Its largest
label is 6,175,975.  This is intentionally a large, direct certificate, not
an optimized short repair.  Exact rational arithmetic checks W has value one
and W≥C coordinatewise.  Replaying the same 269 moves from source+W checks
that every removal is available and the endpoint is target+W.

W is **constructible** with the restricted unit palette.  The replay JSON
includes the seed words U2/U8/U13 and a topologically ordered `borrow_dag` of
96 derived labels.  For a node

```
{label: u, remove: [a,b], insert: [c,d]},
```

take the previously constructed unit witnesses W_a and W_b, remove their
available `a,b`, then insert `c,d`.  This gives a positive unit word W_u
containing u.  For a label in both U8 and U13, the reconstruction chooses U8.
The saved six-round closure supplies the early nodes; the 125 quadratic
witness rules supply later ones.  The checker validates every dependency and
pair identity, constructs each W_u, and sums the requisite copies to obtain
the displayed W.  Reversing this unit construction removes W after the main
repair reaches target+W.

One extra borrowing edge supplies the only catalyst label absent from the
witness-rule closure:

```
{55,95}     <-> {35,5035}
{1079,5035} <-> {1007,7555}.
```

Labels 55 and 95 are in the saved closure, as is 1079.  Thus 5035, then
7555, are borrowable.  This is recorded as `borrowability_extra_rule` in the
replay artifact.  It is not an unrestricted insertion of an arbitrary
value-one product.

## Validation and boundary

The external pytest suite runs the real CLI.  It has hand-calculated
two-factor identities, the source/target count ledger, a `2Z` versus
`2Z+3Z` control that detects accidental rational-span solving, witness
regeneration, full positive replay, and a deliberately corrupted coefficient
that the replay rejects.  Ten tests pass, including rejection of malformed quadratic arity and even labels.  The saved artifacts are finite
and independently replayable; no large breadth-first certificate search or
Lean grind was used to find them.

The mathematical result is a repair **to a known trajectory**.  It shows the
fixed palette can cross the earlier index obstruction at 71.  It does not
establish that an unknown certificate can be repaired into a path, nor does
it give a termination measure for arbitrary repairs.
