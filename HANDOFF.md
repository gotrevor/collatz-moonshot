# HANDOFF: Front A barriered backward tree pull 🌲 (2026-08-23)

## State

- Added `experiments/barrier_tree.py`: exact inverse-tree census with every path confined to
  `[d, 2^p d]`, scaled harmonic mass, doubling-spine subtraction, residue classes, and an
  optional raw-basin control.  Default run is small; use `--no-raw` for wide/deep sweeps.
- Added `experiments/barrier_tail.py`: finite future-minimum-record proxy for aggregating
  safe-tree mass along a rising orbit tail.
- Added `experiments/barrier_adversary.py`: nested 3-adic seed stress test for the claimed
  uniform harmonic slope.
- Added `CollatzMoonshot/FrontA/BackwardTree.lean`.  It defines the finite mathematical
  object, proves the exact `3 ∣ d` doubling-spine theorem, proves modulo-`3` unit status is
  forward-invariant, and pins pointwise/uniform harmonic-growth targets as `def`s.
- Updated `FRONT-A-ROUTES.md` with the data and the strength audit.
- Added `CollatzMoonshot/FrontA/BackwardBranching.lean`, now **`sorry`-free**.
  `binaryBarrierSubtreeGrowth` is a theorem: every `d ≥ 2` with `3 ∤ d` has, for each `r`,
  a `2^r`-element `Finset` of units modulo `3` reaching `d` inside `[d, 128^r d]`.  The
  iteration machinery: `reachesInBand_trans` (band-witness composition with a common
  ceiling), `unitOddBlockChild_parent_eq` (children of distinct odd parents cannot collide,
  by 2-adic valuation of `3y+1`), and `exists_binary_level` (`Nat.le_induction` +
  choice-function `biUnion` with `Finset.card_biUnion`).  Axiom audit (observed in real
  output, 2026-08-23): `[propext, Classical.choice, Quot.sound]` — base three only.
- Both FrontA files are imported from `CollatzMoonshot.lean`; `lake build` green.

## Result

For sampled `3 ∤ d`,

```
c_d(p) = (d · ∑_{m ∈ B_d(p)} 1/m - (2 - 2^-p)) / log(2^p)
```

looks positive and stable rather than decaying to spine noise.  Across 120 unit seeds near
`10^6`, at `p=18`: min `0.2213`, median `1.7498`, 90th percentile `5.6077`.  The worst seed
held `0.2254, 0.2213, 0.2195` at `p=12,18,24`, respectively.  Meanwhile, if `3 ∣ d`, Lean
proves the whole backward basin is exactly `{2^k d}`.  Raw/safe mass ratios vary from roughly
`2%` to `100%`, so the floor condition has genuine arithmetic content.

The first unconditional branching chip is also in: every `x ≥ 2`, `3 ∤ x`, has two distinct
larger unit predecessors returning inside `[x,128x]`.  Conversely, nested 3-adic adversarial
seeds drove the measured slope from `0.2195` down to `0.1555` by `p=30` (52.3M safe nodes),
so the uniform-growth pin is now explicitly under pressure.

## Next pull

Do **not** mistake `UniformBarrierHarmonicGrowth` for saturation.  Undoing the scaled mass
costs `1/d`, while high-tail seeds must tend to infinity; basins of successive seeds on one
orbit also nest heavily.  The obvious tail-record proxy was already pulled: the optimistic
budgets `∑ c(d_i)/d_i` were `0.2939`, `1.55e-4`, and `6.85e-6` for excursions starting at
`27`, `77031`, and `837799`.  This is roughly `1/(starting floor)`, before paying any overlap
loss.  The sharpened route now needs both `DivergentTailHarmonicBudget` (or a stronger
coefficient substitute) and an **annular overlap/packing lemma**.  That is enough extra new
mathematics to downgrade A2 relative to A1; do not spend a treadmill merely formalizing the
finite proxy.

The treadmill job is DONE: `binaryBarrierSubtreeGrowth` is proved axiom-clean.  The next
genuine-math attack is a finite residue-plus-height transfer certificate improving the
crude `2 / 128` branching constant (ladder step 2 in `FRONT-A-ROUTES.md`).

---

## Previous: Front B board repair 🧨 — DONE (2026-08-23)

**This lap's finding**: the boarded Route-2 targets (`Compression`, `BoundedDen`) were
**FrontB in disguise** - word powers `wpow v j` keep the member value while `circuits`
telescopes and `den` explodes, so bounding either quantity over *all* nontrivial integral
words is equivalent to asserting no counterexample exists.  Proved axiom-free
(`naiveCompression_iff_frontB`, `naiveBoundedDen_iff_frontB`).  Repaired by quantifying
over `Primitive` words, with the decomposition `exists_primitive_root` carrying the wiring.
Full story: `FRONT-B-ROUTES.md` §2026-08-23; machinery: `CollatzMoonshot/FrontB/Powers.lean`.

## State

- `lake build` green; committed `55ff482`.
- Axiom audit (observed in real output, 2026-08-23): both degeneracy theorems and
  `frontB_of_compression` = base three only; `frontB_of_compression_le_91` = base three
  + exactly `hercher_min_circuit_count`; `finite_shapes_of_boundedDen` = base three +
  exactly `baker_bounded_difference`.
- New THEOREM-grade axiom `hercher_min_circuit_count` (Hercher 2023, m-cycles need
  m ≥ 92; primary source verified 2026-08-22, summary in `papers/`).

## Thread pulls this session (2026-08-23, so nothing gets lost)

1. **Pulled "attack Compression"** → found and repaired the power degeneracy (above);
   sharpened target `frontB_of_compression_le_91` now stands.  Commits `55ff482`,
   `c8430a0`.
2. **Pulled Thread 2 (second extremal family)** → `experiments/knight_reach.py` census,
   `k ≤ 16`: the exact-identity trick's reach beyond balanced words is a **chance floor**
   (expected sporadic hits ~k², thinning density, unstructured words); only Knight's own
   `2^(k−2)` locus on mechanical words is uniform.  **Thread 2 re-priced ~12% → ~5%.**
   Commit `d9ef876`.  Full write-up: `FRONT-B-ROUTES.md` §2026-08-23 (both sections).
3. Not pulled (deliberately left): the compression attack itself (hard open math, wants
   fresh eyes), Front A route map (`FRONT-A-ROUTES.md`, absorbed but unworked),
   `PI02-SKETCH.md`, and two cheap curiosities - Lean-ing the negative-drift argument,
   and the census's bonus datum *"distinct rotations of a primitive word have distinct
   numerators"* (provable: a repeated member value closes the orbit early, contradicting
   primitivity - a pleasant-lemma candidate for `Powers.lean`).

## Next attack

- **The sharpened Route-2 target**: `frontB_of_compression_le_91` reduces Front B to
  *"a primitive nontrivial integral cycle has ≤ 91 circuits"* - one statement, no ladder
  extrapolation.  Nothing formal exists toward proving compression itself; the prose map
  (`FRONT-B-ROUTES.md`) stands, with the new doctrinal note that compression must be
  sign-blind (positivity lives in the ladder).
- Alternative threads: `BoundedDen` on primitive words (**~5% after the census** - a new
  family needs new combinatorial input), Front A route map (`FRONT-A-ROUTES.md`),
  `PI02-SKETCH.md`.
