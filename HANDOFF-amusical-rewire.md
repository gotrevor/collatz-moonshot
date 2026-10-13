# HANDOFF: bounded-ratio amusical rewiring

## 2026-10-13 — nonnegative restriction and degenerate branch closed

The target `exists_boundedRatio_rewire` still has its original `sorry`.  This lap isolated and
kernel-checked the entire branch in which there is at most one infinite orbit on `ℕ`:

- `amusicalNatPerm` is the restriction of `amusicalPerm` to `ℕ`; both directions preserve
  nonnegativity, and its forward, inverse, and integer-power cast lemmas are proved.
- `exists_boundedRatio_rewire_of_connected` proves all four target conclusions with `τ = U|ℕ`
  when the infinite natural orbits are already connected.  The change set is empty (`C = 0`),
  so the quantitative and ratio conclusions are exact.
- `exists_boundedRatio_rewire_of_subsingleton_infiniteOrbits` derives that hypothesis from the
  paper proof's degenerate assumption (at most one infinite nonnegative orbit).

Files changed: `CollatzMoonshot/AmusicalRewireRatio/Restriction.lean` and the target module's
import.  The unrelated untracked `CLAUDE.local.md` was preserved.

Verification:

```text
lake build CollatzMoonshot.AmusicalRewireRatio.Restriction
Build completed successfully (8710 jobs).
/Users/gotrevor/personal/bin/lean-green \
  /Users/gotrevor/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
Build completed successfully (8711 jobs).
FORMALIZE-TIER GREEN
```

Current blocker: the main case with at least two infinite orbits.  It needs the explicit sparse
cut-and-splice permutation; no theorem in mathlib or the repository supplies the quantitative
`O(log² N)` and factor-3 conclusions.

Next attack: formalize first-passage cuts at geometric scales.  Start with the load-bearing escape
lemma: an injective two-sided natural orbit eventually leaves every finite range in both time
directions.  Combine it with the elementary bounds on `U` and `U⁻¹` to put each first passage and
its adjacent image in the scale interval required by the ratio estimate.  Only then define the
segment enumeration and successor permutation.
