# Five-head pair families: completed proof handoff

The bounded Opus/low proof run completed in one lap.  The frozen statements and affine definitions in `CollatzMoonshot/Obstructions/FiveHead.lean` are unchanged; the root module imports it.  The proof commit is `83efd19`.  Experiments, integration and the research implications are recorded in [the family checkpoint](RESEARCH-2026-09-28-family-checkpoint.md).

## Mathematical result

For every natural parameter, `observed_five_head_pair` and `lower_five_head_pair` prove legality of the specified exchange `[5*n,c] -> [n,d]` in the state containing that input pair.  `lower_five_head_height` proves both auxiliary labels are smaller than `n` in the second family.

The helper `five_head_pair_of_Q5` reduces pair legality to positivity, oddness and the natural-number equality

```
5*c*(3*n+1)*(3*d+1) = d*(15*n+1)*(3*c+1).
```

`two_tstep_odd` and `odd_ratio` express the shortcut map and its rational ratio.  Clearing denominators proves the generic helper; each affine family then closes by polynomial identity.  No factor availability beyond the stated input pair is assumed or concluded.

## Validation

The worker built the full project and printed the dependencies of all three frozen declarations, obtaining only `propext`, `Classical.choice`, and `Quot.sound`.  The supervisor subsequently verified the full build on the host.  An independent statement audit confirmed the exact coefficients, positivity/oddness, arithmetic progressions and the smaller-label inequalities.

## Remaining research

Embedding this pair exchange in a larger multiset is routine interface work.  It is not the mathematical crux: `Repair71.lean` already contains generic step and run soundness.  The missing ingredients are a uniform legal borrowing construction and a target-free completion that decreases a well-founded proof state.  Smaller auxiliary labels alone do not bound the size or support of the whole borrowed unit.

The observed family has `c>n`.  The lower family has `c,d<n`, but the resulting word still contains `d` and the remaining virtual factors.  Neither theorem proves a full repair or a Collatz descent.  No successor proof lap was launched; a further lap needs a specified mathematical target, not just this completed interface lemma.
