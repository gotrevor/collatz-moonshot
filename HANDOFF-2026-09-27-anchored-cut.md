# HANDOFF 2026-09-27 — anchored finite-cut transfer inequality

Frozen node from `KICKOFF-2026-09-27-anchored-cut.md`. **Complete, sorry-free, axiom-clean.**
No successor task; this node is closed.

## Result

`CollatzMoonshot/Obstructions/AnchoredCut.lean`, namespace
`CollatzMoonshot.Obstructions.ArithmeticLifts`:

| Declaration | Status |
| --- | --- |
| `transferReal`, `predecessors`, `incoming` | definitions, exactly as frozen |
| `mem_predecessors` | proved (fiber lemma) |
| `subset_predecessors` | proved |
| `pos_of_mem_predecessors` | proved |
| `sum_transferReal` | proved (the reindexing step) |
| `finiteCut_identity` | **proved** |
| `finiteCut_anchored_lower` | **proved** |
| `finiteCut_unit_lower` | **proved** |

`#print axioms` on all three headlines: `[propext, Classical.choice, Quot.sound]` only —
no `sorry`, no `Lean.ofReduceBool`/`native_decide` in their dependency cone.
`lake build` (root, 8798 jobs) completes successfully.

## Propositions: no changes

All three statements are byte-for-byte the frozen ones, including hypothesis order and the
image-based `predecessors`. The `Finset.range` filter alternative was not needed. No
hypothesis was added, strengthened, or weakened; `a : ℕ → ℝ` stays fully general and signed
for the identity, with `ha` used only in the boundary inequality. The only cosmetic edit is
renaming `mem_predecessors`'s positivity binder to `_hu` — the proof does not need it (the
even branch is carried by `u % 2 = 0` alone), but it is retained in the signature as frozen.

## Proof route as executed

1. `mem_predecessors`: split on `Nat.even_or_odd u`. Even: `u = 2 * (u/2)` and
   `tstep u = u/2`. Odd: `2 * tstep u = 3*u + 1`, from which `omega` gets both
   `tstep u % 3 = 2` and `(2 * tstep u - 1)/3 = u`. Both `%` and `/` are by numerals, so
   `omega` discharges them directly — no manual parity lemmas.
2. `sum_transferReal`: the two images are disjoint by parity (`omega` from
   `(2*w-1)/3 = 2*v`, `w % 3 = 2`, `0 < w`); `v ↦ 2*v` is injective and
   `v ↦ (2*v-1)/3` is injective on the `% 3 = 2` filter (again `omega`, using `hpos`).
   Then `Finset.sum_union` + two `Finset.sum_image` + `Finset.sum_filter` turns the RHS
   into exactly `Finset.sum_add_distrib` of the `transferReal` summand. Holds for signed `a`.
3. `finiteCut_identity`: `Finset.sum_sub_distrib`, `sum_transferReal`, then
   `Finset.sum_sdiff_eq_sub (subset_predecessors …)` closes it by `rfl`.
4. `finiteCut_anchored_lower`: `n ∈ incoming A` from `mem_predecessors hnpos henter` and
   `hnout`; `Finset.single_le_sum` (nonnegativity via `pos_of_mem_predecessors`); rewrite
   back through the identity; then termwise `x ≤ |x| = v * (|x|/v) ≤ M * (|x|/v)`.
5. `finiteCut_unit_lower`: `0 < M` from `hpos (tstep n) henter` and `hM`, then
   `div_le_iff₀` + `linarith`. Note `div_le_iff` is deprecated on this toolchain
   (Lean 4.33.1); `div_le_iff₀` is the live name.

## Review checks discharged in-file

Statement controls at the bottom of the file, all `decide`:
`tstep 2 = 1`, `tstep 1 = 2`, `predecessors {4,2,1} = {8,4,2,1}`, `incoming {4,2,1} = {8}`,
`predecessors {5,8,4,2,1} = {10,16,8,4,2,5,3,1}`, `incoming {5,8,4,2,1} = {10,16,3}`,
plus the two anchored instantiations (even `n = 8`, `M = 4`; odd `n = 3`, `M = 8`) obtained
by applying `finiteCut_unit_lower` itself. My first draft of the second `predecessors`
value omitted `5` (the odd predecessor of `8`); `decide` caught it — the controls are load
bearing, not decoration.

No counterexample found; all three frozen propositions are true as stated.

## Deliberately out of scope

Orbit-cut construction, dyadic-ray extremizer, and the infimum equality are separate nodes.
Nothing in this file touches `wip/`, other Lean modules, root imports, or other notes.
