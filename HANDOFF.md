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
- Added `experiments/barrier_transfer.py` and
  `CollatzMoonshot/FrontA/BackwardTransfer.lean`.  The exact modulo-`9` transfer search found
  the coordinatewise worst reusable-child costs `5,7,11,13,17,19,23,...`.  Lean proves the
  first seven labeled children exist and are distinct at every unit parent, records their
  exact band costs, generalizes cross-parent non-collision to arbitrary exponents, and proves
  `sum (5/6)^j > 1` over those seven costs.  Thus the standard variable-length recurrence has
  counting exponent `log_2(6/5) = 0.263034...`, versus the old crude `1/7`; no axiom was
  added.  The Python checker exhaustively verified `799,992` blocks through `x = 100,000`
  and reports the limiting periodic-envelope exponent `0.266895...`.  Axiom audit (observed
  in real output): `sevenCostTransferAt` and `sevenCostWeightCertificate` use only
  `[propext, Classical.choice, Quot.sound]`; the generalized collision theorem uses only
  `[propext, Quot.sound]`.
- The same transfer script now contains a frozen, exact `36`-state certificate for the
  shrinking `j=1` branch.  States are unit residues modulo `27` times height floors
  `{1,7/4}`; the unknown next ternary digit is treated adversarially.  The earlier `q=7/9`
  calculation charged the gross peak `2^j x`.  Successive odd endpoints instead have scale
  `(2^j x-1)/3`, so the correct asymptotic edge weight refunds the factor `3`.
- Added `CollatzMoonshot/FrontA/BackwardHeightTransfer.lean`, **`sorry`-free**.  It proves
  the two height transitions, the `j=1` source classes, the exact modulo-`9` seven-child
  selectors, the modulo-`9` child formula and its three modulo-`27` lifts, and a general
  odd-parent non-collision lemma covering growing and shrinking edges.  Lean kernel-checks
  all `36` inequalities for exponent `1/2` using the rational underweight
  `(5/3)(7/10)^j < (3/2^j)^(1/2)` (the two checks are just `25 < 27` and `98 < 100`).
  The exact minimum ratio is `1.006096707253...`.  The theorems
  `exists_netHalfGrowingExpansion` and `exists_netHalfShrinkingExpansion` connect the table
  to actual, distinct, floor-safe Collatz children; no `native_decide` or new axiom is used.
  Axiom audit (observed in real output): the table and both expansion theorems use only
  `[propext, Classical.choice, Quot.sound]`; the generalized collision theorem uses only
  `[propext, Quot.sound]`.
- The net-height numerical critical exponent rises with ternary memory: with a stable rich
  height grid, depths `2..7` give about `.436,.611,.689,.734,.761,.780` with `j=1`, versus
  `.370,.416,.435,.449,.460` for the growing-only control through depth `6`.  The exact
  half-exponent certificate is conservative but robust; the trend remains below harmonic
  exponent `1`.
- Added `CollatzMoonshot/FrontA/BackwardRenewal.lean`, **`sorry`-free**.  The crucial repair
  is to replace the non-telescoping rational search weights by the exact real edge weight
  `sqrt(x/y)`.  Lean proves the rational weight is strictly smaller on every actual odd
  block and that exact weights telescope.  Both local child regimes therefore expand exact
  root-to-endpoint mass.  The module also proves positive macro-reachability and the explicit
  `OnCycle` ancestor-repeat alternative, packages every state into a value-injective finite
  child set, introduces the floor/destination-separated `ReachesToInBand` needed by `j=1`,
  and proves endpoint-to-block ceiling bounds.
  Axiom audit (observed in real output): all real-weight, finite-frontier, exact-expansion,
  and cardinality theorems use only `[propext, Classical.choice, Quot.sound]`; the direct
  ancestor-repeat-to-cycle theorem uses only `[propext, Quot.sound]`.
- The finite target `NetHalfStoppingFrontier` is pinned.  Lean proves any such frontier has
  square-root-many distinct endpoints in the exact form
  `V(d) < card(S) * 200 * sqrt(d/H)`.  `NetHalfRepeatOrStoppingGrowth` is the one remaining
  `def`: recursively construct that first-exit frontier, or return the cycle alternative.
- Added `experiments/barrier_stopping.py`.  It performs exactly that first-exit construction
  on odd unit roots and aborts on any repeat.  No repeat occurred in the tested trees.  At
  height ratio `2^18`, seeds `5,13,17` produced respectively `36,194`, `14,892`, and `12,030`
  leaves; their rigorous square-root count floors were only `253.44`, `174.08`, and `140.8`.
  Exact telescoping mass/root ratios were `13.88`, `8.25`, and `8.21`.
- All five barrier-tree FrontA files are imported from `CollatzMoonshot.lean`; targeted
  builds are green.

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

The local renewal mathematics is now Lean-checked through exact telescoping, finite child
sets, collision/cycle wiring, generalized band composition, and the final square-root
cardinality estimate.  The next treadmill-sized task is narrowly recursive: prove
`NetHalfRepeatOrStoppingGrowth` by expanding all endpoints `≤ H`, freezing first exits, and
using finiteness of the `2(H-d+1)` low/high endpoint states to force either termination or an
ancestor repeat.  Cross-parent and within-parent non-collision are already available.  Do
not claim harmonic growth: the resulting exponent is `1/2`, and deeper numerical candidates
still sit below `1`.

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
