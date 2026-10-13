# Handoff: amusical escape (2026-10-13)

## Concrete advance

`CollatzMoonshot/AmusicalEscape.lean` now has three unresolved proofs rather than six.  This lap
closed the entire downstream half of the dependency chain without changing any ratified statement
or definition:

- `periodic_of_evenFrequency_lt` is proved from `escape_forward`.  The new private exact identity
  `fwdBits_add_evenCount` shows that the bit average is `2` minus the even-step average away from
  index zero.  Limit arithmetic then produces a fixed positive gap above `log₂ 3`, contradicting
  the arbitrarily late low averages supplied by `escape_forward`.
- `not_reversor_of_evenFrequency_lt` is proved.  The reversor equation is first turned around to
  `ι (U⁻¹ x) = U (ι x)`, then iterated.  Periodicity of `ι n` transfers to backward periodicity of
  `n` by injectivity of `ι`, and applying the forward iterate gives the forbidden forward return.
- `not_reversor_of_backwardNormal` is proved by the bridge plus the exact rational comparison
  `log₂ 3 < 5/3`, certified through `3^3 < 2^5` using the existing power-separation theorem.

No `native_decide`, axiom, heartbeat override, or statement weakening was introduced.  The
pre-existing untracked `CLAUDE.local.md` remains untouched.

## Exact verification

```text
lake build CollatzMoonshot.AmusicalEscape
rg -n '.{101}' CollatzMoonshot/AmusicalEscape.lean
rg -n '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' CollatzMoonshot/AmusicalEscape.lean
git diff --check
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-escape \
  --target CollatzMoonshot.AmusicalEscape
```

The narrow build succeeds (8714 jobs).  The long-line scan and `git diff --check` have no
findings.  The source scan reports only the descriptive module-doc occurrence and the three
remaining proof holes.  The real gate verdict is `FORMALIZE-TIER GREEN`; it lists those three
holes as disclosed proof debt.

## Current blocker

The remaining obligations are:

1. `escape_forward`;
2. `escape_backward`;
3. `evenFrequency_of_backwardNormal`.

The first two are the analytic crux.  Each needs a kernel-friendly iteration of the affine
absolute-value inequality while using nonperiodicity to make all sufficiently late orbit values
large.  The third is finite combinatorics plus limit bookkeeping: partition the balanced fiber of
`f` into exact blocks, sum their normal frequencies, and show that shifting by `s` changes the
count by a bounded amount.

## Next highest-value attack

Attack `escape_forward` first.  Factor reusable helpers for pairwise distinct iterates of an
injective map under the no-return hypothesis, eventual escape from every finite integer interval,
and the multiplicative/logarithmic iteration of `abs_amusical_le`.  The backward proof should then
reuse the same orbit-escape helper and mirror the analytic ledger with `abs_amusicalInv_le`.  Once
both escape lemmas close, finish `evenFrequency_of_backwardNormal` independently and run the
headline axiom audit before calling `box done`.
