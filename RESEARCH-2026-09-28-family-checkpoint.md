# From finite catalytic repairs to symbolic exchanges

```sh
./experiments/catalytic_palette.py test
./experiments/repair_family.py test
./experiments/catalytic_palette.py replay experiments/catalytic_palette_1031_witness.json
./experiments/repair_family.py growth 6
```

The same canonical inverse-five construction now has exact, legally scheduled repairs for **199, 263 and 1031**, in addition to the Lean theorem for 71.  The new finite repairs are Python rational-arithmetic replays.  Two exchanges extracted from this work are now proved universally in [FiveHead.lean](CollatzMoonshot/Obstructions/FiveHead.lean); their scope is one available pair, not a full repair.

## Finite results and what they measure

| Start | Distinct oriented quadratic rows | Quadratic applications | Factors in the borrowed unit | Result |
|---|---:|---:|---:|---|
| 199 | 134 | 273 | 2520 | Legal repair, borrowed unit returned |
| 263 | 220 | 694 | 29398 | Legal repair, borrowed unit returned |
| 1031 | 16 | 17 | 648 | Legal repair, borrowed unit returned |
| 2375 | | | | Bounded search unresolved |

The 1031 central repair also inserts U8, removes U13 and reverses the essential cubic, for 20 central operations.  Unit construction and return are accounted for separately.  Each replay checks pair legality, factor availability, the borrowing derivation, exact value one of the borrowed word, and the final certificate.  It does not infer reachability from a signed integer relation alone.

All three successful searches used the known trajectory as their target.  The saved [witness comparisons](experiments/repair_family_comparisons.json) expose a serious selection effect: 199 shares 60 target steps with 71; 263 is itself on 71's orbit, so its entire 51-step target tail is inherited.  The 1031 comparison shares only 13 target steps and four constant quadratic rows.  Shared numeric rows are not symbolic rules.

For 2375, the saved [bounded search](experiments/catalytic_palette_2375_bounded.json) examined 58,025 targeted pairs and found 2,683 relations, leaving a nonzero 110-label remainder.  It capped source-neighbor enumeration at label 10,000 and reports `budget-truncated`.  This is neither a full-palette obstruction nor a proof that a repair does not exist.  Separately, starts divisible by 3 lie outside this engine's 3-free search domain, though the formal move relation permits such labels.

## A reusable exchange, with its exact limits

Write `r_u=2u/(3u+1)`.  A five-head exchange satisfies

```
r_(5n) r_c = r_n r_d
iff d(15n+1-12c)=5c(3n+1).
```

The observed `1031` exchange extends to every `h>=0` with

```
n=1031+8868288h, c=1045+8988672h, d=5525+47523840h.
```

Here `c>n`, so it supplies no smaller-label induction step.  A second family has

```
n=9223+16320h, c=3689+6528h, d=5425+9600h,
c<n and d<n.
```

Both families remain in `n=7 mod64` and use positive odd labels coprime to 3.  The second makes a stronger induction hypothesis about legal borrowing relevant: a unit containing `c` would supply the exchange.  Ordinary convergence of smaller integers alone is not a proved borrowing theorem.  The output still contains `d` and the other virtual factors, so neither family gives a complete repair or a decreasing global proof state.

The whole 1031 repair also contains `{25,7733}->{37,77}`.  Keeping 25, 37 and 77 fixed and replacing 7733 by `T(5n)` forces `n=1031`.  Thus parameterizing the one five-head row does not parameterize its 16-row script.  The [symbolic exchange audit](RESEARCH-2026-09-28-quadratic-five-head.md) gives the algebra and this obstruction.

## A stress family that defeats easy-prefix selection

The initially suggested large inputs `2^j+7` and `2^j-57` eventually descend in 11 and 8 steps respectively.  Large size alone did not make them informative.  The [profile study](RESEARCH-2026-09-28-repair-family.md) instead chooses `k` with `81k=-11 mod2^j`, adjusts it to keep `n=64k+7` coprime to 3, and writes `81k+10=2^j s-1`.  Then

```
T^(6+t)n = 3^t 2^(j-t)s-1,  0<=t<=j.
```

There is no descent through step `j+6`.  The first selected control at `j=6` is 2375, reaching 34,262 at step 12.  These formulas are paper arguments with persistent exact CLI controls; they have not yet been formalized in Lean.  For `j>=6` this family is disjoint from the one residue class where the smaller virtual endpoint again lies in `7 mod64`.

## What would constitute the next advance

The catalytic branch needs a transformation of the supplied smaller certificate that selects a balanced output without being given the target trajectory.  For the lower-auxiliary family, the concrete prerequisites are a uniform restricted-palette borrowing derivation for `c`, and an orientation of the remaining exchanges with a decreasing proof state.  One successful pair replacement settles neither prerequisite.  A proposed rule must also specify which inputs it covers; the long-growth controls provide a distinct test domain.

This is progress in extracting and rejecting candidate induction structure, not evidence for a general Collatz proof.  The two other research branches retain their independent missing inputs: an excluding joint arithmetic/order inequality, and an independent anchored-height estimate.  The earlier [novelty audit](RESEARCH-2026-09-28-induction-novelty-audit.md) remains the literature comparison; no priority claim is added here.

## Validation

The two persistent external pytest suites exercise the actual CLIs and pass 20 tests.  They include hand-derived ledger and orbit anchors, malformed-witness rejection, exact finite replay, finite-search status distinctions, and a relation with an unavailable catalyst that must report unresolved borrowability.  New finite replay files are discovery artifacts; the Lean pair-family theorems have the narrower scope stated above.

The bounded Opus/low run completed these three frozen declarations in one lap: `observed_five_head_pair`, `lower_five_head_pair`, and `lower_five_head_height`.  The root build passed in the worker and in the supervisor's host verification.  Independent statement review confirmed the intended coefficients and one-pair scope.
