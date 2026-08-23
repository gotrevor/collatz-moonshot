# HANDOFF: Front A barriered backward tree pull 🌲 (2026-08-23)

## Update (2026-08-23, newest lap): `TwoThirdsRepeatOrStoppingGrowth` is now a THEOREM

- Added `CollatzMoonshot/FrontA/BackwardTwoThirdsStopping.lean`, **`sorry`-free**, proving
  `twoThirdsRepeatOrStoppingGrowth : TwoThirdsRepeatOrStoppingGrowth` exactly as pinned (the
  target `def` in `BackwardTwoThirdsRenewal.lean` was untouched).  Full `lake build` green
  (8,739 jobs), module imported from `CollatzMoonshot.lean`.  Axiom audit (real output):
  `twoThirdsRepeatOrStoppingGrowth`, `twoThirdsStoppingFrontier_of_noCycle`,
  `twoThirds_stopping_card_bound`, `twoThirdsPotential_ge_min` each depend only on
  `[propext, Classical.choice, Quot.sound]` — base three, no `native_decide`, no new axiom.
- The construction is the five-state analogue of `netHalfRepeatOrStoppingGrowth`: a fuel-`H+1`
  frontier recursion over `TwoThirdsNode = Fin 5 × ℕ`, expanding every node `≤ H` through
  `exists_twoThirdsChildFinset` and freezing first exits.  It **reuses verbatim** the
  state-independent value machinery from `BackwardStopping.lean` (`StoppingChain`, `consChain`,
  `chain_agree`, `chain_reachesValuePos`, `StoppingChain.round_add_le`, `reusable_band_step`,
  `ReusableOddBlockChild.lt_of_le`, `reachesValuePos_self_iff_onCycle`, `weighted_biUnion_expands`);
  only the state wrappers `TwoThirdsStoppingNode`/`TwoThirdsStoppingFront` and the three round
  lemmas (`twoThirdsFront_init`, `twoThirdsFront_step`, `twoThirdsStoppingFrontier_of_no_low`)
  are re-derived over `InFiveHeightState`/`Fin 5` and the exact real edge weight
  `(x/y)^(2/3)` telescoped by `twoThirdsEdgeWeight_mul`.  The potential is `ℕ`-valued so all
  real sums carry an explicit `(· : ℝ)` cast; `InFiveHeightState.le` replaces the two-state
  `.1`; the child-finset call takes the extra `d ≥ 2` argument.
- **Cycle branch**: a new endpoint colliding with a live frontier value or its own ancestry
  splices via `chain_reachesValuePos` into `ReachesValuePos n n`, i.e. `OnCycle n` with `d ≤ n`.
  **Termination**: `StoppingChain.round_add_le` — a low node at round `m` has `m` distinct
  chain values in `[d, H]`, so fuel `H + 1` suffices.  **Mass**: exact `(x/y)^(2/3)`
  telescoping, exits frozen by `filter (· ≤ H)` sum splitting.
- Also added: `twoThirdsStoppingFrontier_of_noCycle` (NoNontrivialCycle wiring eliminating the
  cycle alternative), the kernel-checked `twoThirdsPotential_ge_min` (`100000 ≤ potential` on
  unit residues, `decide +kernel` over `Fin 5 × Fin 81`), and the explicit corollary
  `twoThirds_stopping_card_bound`: assuming no nontrivial cycle, every odd unit `2 ≤ d ≤ H`
  has a value-injective first-exit frontier `S` with
  `100000 < card(S)·1051827·(d/H)^(2/3)`, endpoints in `(H, 2^23 H)`, paths in `[d, 2^25 H]`.
- **Next**: the exponent-`2/3` frontier is now unconditional (matching the `1/2` frontier).
  The open mathematics is step 5 of the `FRONT-A-ROUTES.md` ladder (pointwise vs. uniform
  harmonic growth — the 3-adic adversary) and step 6's overlap/packing question.

## Update (2026-08-23, later lap): the 2/3-exponent renewal layer is Lean-checked

- Added `CollatzMoonshot/FrontA/BackwardTwoThirdsRenewal.lean`, **`sorry`-free**, the exact
  real telescoping layer that upgrades the rational 270-state certificate to the exponent-`2/3`
  edge weight.  Imported from `CollatzMoonshot.lean`; full `lake build` green (8,738 jobs).
  Axiom audit (real output): every headline theorem depends only on
  `[propext, Classical.choice, Quot.sound]`; no `native_decide`.
  * `twoThirdsEdgeWeight x y := ((x:ℝ)/(y:ℝ)) ^ (2/3:ℝ)` (`Real.rpow`), and
    `twoThirdsRationalWeight j := (52/25)·(629/1000)^j`.
  * `twoThirdsRationalWeight_lt_edgeWeight`: on every actual positive odd block
    `3y+1 = 2^j x` the rational weight is strictly below the exact edge weight.  Proved via
    the cube comparison `twoThirdsRationalWeight_cube_lt` (`(52/25)^3 < 9`,
    `4·(629/1000)^3 < 1`) plus `3/2^j < x/y` and `Real.rpow` monotonicity; the cube-root step
    uses `lt_of_pow_lt_pow_left₀` after `((3/2^j)^(2/3))^3 = (3/2^j)^2` from `Real.rpow_mul`.
  * `twoThirdsEdgeWeight_mul`: exact telescoping through positive endpoints via
    `Real.mul_rpow` + `field_simp`.
  * `twoThirdsPotential_pos` (unit residues, every floor) and `twoThirdsPotential_le_max`
    (uniform ceiling `1051827`, `decide +kernel` over `Fin 5 × Fin 81`).
  * `exists_twoThirdsChildFinset`: upgrades `exists_twoThirdsExpansion` to a nonempty,
    value-injective finite child set of `Fin 5 × ℕ` (`TwoThirdsChildAt`,
    `TwoThirdsValuesInjective`) — actual reusable edges, floor-safe five-height states,
    `3 c < 2^23 x`, and strict expansion under the exact real edge weight.
  * `TwoThirdsStoppingFrontier` / `TwoThirdsRepeatOrStoppingGrowth` defined exactly analogous
    to the half-exponent objects, and the cardinal bound
    `TwoThirdsStoppingFrontier.card_bound`:
    `V(0,d) < card(S)·(1051827·(d/H)^(2/3))`.
- **Next**: prove the recursive `TwoThirdsRepeatOrStoppingGrowth` (port the fuel-`H+1`
  frontier recursion from `BackwardStopping.lean`, replacing `InHeightState`/`Bool` nodes by
  `InFiveHeightState`/`Fin 5` nodes, carrying `d ≥ 2`; reuse `weighted_biUnion_expands` with
  `twoThirdsEdgeWeight` telescoping).  This is the analogue of `NetHalfRepeatOrStoppingGrowth`.

## Update (2026-08-23, late lap): the 2/3-exponent certificate is Lean-checked

- Added `CollatzMoonshot/FrontA/BackwardTwoThirds.lean`, **`sorry`-free**, formalizing the
  correlated 270-state local transfer at endpoint-height exponent `2/3` exactly as frozen in
  `experiments/barrier_transfer.py`:
  * the five height floors `{1, 7/4, 5/2, 3, 4}` as `InFiveHeightState` (numerator/denominator
    inequalities, no division), with floor-safe growing (`fiveHeightStep_growing`, cases
    `j = 2`, `j = 3`, `j ≥ 4`) and shrinking (`fiveHeightStep_shrinking`) five-state
    transitions proved by `omega` from the actual block equation and `d ≥ 2`;
  * the shared next ternary digit: `oddBlockChild_mod_eightyOne` proves an actual odd block
    `3y + 1 = 2^j x` has `y % 81 = ((2^j (x % 243) - 1) / 3) % 81` — the *correct* child
    formula including the fixed carry digit produced by the division — and
    `oddBlockChild_sharedLift` shows the single digit `t = x / 81 % 3` steers every child of
    one source at once;
  * the frozen 270-entry integer potential, copied in documented order, and **all 810**
    source-state/lift inequalities for factor `52/25` and `q = 629/1000`, kernel-checked in
    integer-scaled form (scale `25·1000^23`) by one `decide +kernel`
    (`twoThirdsNatCertificate`); a generic bridge (`qpow_scale`, `twoThirdsNatImage_eq`)
    transfers it to the exact rational statement `twoThirdsPotentialCertificateAt`.
  * The acceptance theorem `exists_twoThirdsExpansion` quantifies arbitrary `d ≥ 2` and
    actual reusable `x` in any of the five states: the exact seven growing children (plus the
    actual `j = 1` child precisely when `fiveHasShrink` enables it) exist, are distinct,
    satisfy their Collatz block equations, floor-safe five-state transitions, the size bound
    `3y < 2^23 x`, and the strict rational weighted expansion
    `(52/25)·Σ (629/1000)^j · potential(child)` over the actual child state potentials.  The
    correlation makes each table entry *equal* to the actual child's potential (no
    adversarial three-lift minimum anywhere).
- Axiom audit (observed in real output, 2026-08-23): `twoThirdsNatCertificate` uses only
  `[propext]`; `twoThirdsPotentialCertificateAt` and `exists_twoThirdsExpansion` use the base
  three `[propext, Classical.choice, Quot.sound]`; `twoThirdsPotential_pos_of_unit` uses no
  axioms.  No `native_decide`, no new axiom, no `sorry`.  Full `lake build` green (8,737
  jobs) with the module imported from `CollatzMoonshot.lean`.
- The rational edge underweight is safe for exponent `2/3` because `(52/25)^3 < 9` and
  `4·(629/1000)^3 < 1` (`twoThirdsRationalUnderestimate`).  Exact minimum certificate ratio
  (Python, exact `Fraction`): `1.016618220460`.
- **Next Lean target**: generalize the telescoping/stopping renewal layer
  (`BackwardRenewal` → `BackwardStopping`) from edge weight `sqrt(x/y)` to `(x/y)^(2/3)`,
  driven by `exists_twoThirdsExpansion` in place of
  `exists_netHalfGrowingExpansion`/`exists_netHalfShrinkingExpansion`.  The needed real-edge
  comparison is `(52/25)·(629/1000)^j < (3/2^j)^(2/3)`, the cube-root analogue of the
  existing square-root underweight lemma; the frontier recursion, collision/cycle wiring,
  and cardinality layer should port with the five-state `InFiveHeightState` replacing the
  two-state `InHeightState`.  Note the five-state machine needs `d ≥ 2` in the transition
  lemmas (the old two-state one did not).

## Update (2026-08-23, post-stopping audit): shared ternary lift gives exponent `2/3`

- Independently rebuilt `BackwardStopping`: full `lake build` green (8,736 jobs), and
  `#print axioms` for both `netHalfRepeatOrStoppingGrowth` and
  `NetHalfStoppingFrontier.card_bound` reports exactly
  `[propext, Classical.choice, Quot.sound]`.  The proof's collision splice and fuel bound
  were manually audited; no hidden global-injectivity or termination assumption was found.
- Found a real strengthening in `experiments/barrier_transfer.py`.  The old conservative
  operator minimizes the unknown modulo-`3` lift separately for every child.  Actual
  children of one parent share a **single** next ternary digit: if
  `x = r + t·3^k (mod 3^(k+1))`, then the cost-`j` child is
  `(2^j r-1)/3 + 2^j t·3^(k-1) (mod 3^k)`.  The new operator takes the minimum over the
  three *joint child sums*, preserving this correlation (including the fixed carry digit in
  `(2^j r-1)/3`).
- A compact search using unit residues modulo `81` and height floors
  `{1, 7/4, 5/2, 3, 4}` has 270 states and numerical critical endpoint exponent
  `0.683819575608`.  More importantly, the script now freezes and checks an integer
  potential with the fully rational edge underweight

  ```
  (52/25) * (629/1000)^j < (3/2^j)^(2/3).
  ```

  The comparison is exact because `(52/25)^3 < 9` and
  `4*(629/1000)^3 < 1`.  All `270 × 3 = 810` joint-lift inequalities pass in exact
  `Fraction` arithmetic; minimum ratio `1.016618220460`.  The shared-lift residue formula is
  also checked directly on all 79,992 growing blocks (and every applicable shrinking block)
  through parent `10,000`.  This is certificate-grade computational evidence for replacing
  the proved square-root frontier by a uniform `2/3`-exponent frontier.  It is **not yet
  Lean-checked**.
- Next Lean target: create `FrontA/BackwardTwoThirds.lean`, formalize the five height states,
  the shared modulo-`243` source digit / modulo-`81` child calculation, and the frozen
  270-state table.  Then generalize the exact telescoping/stopping layer from `sqrt(x/y)` to
  `(x/y)^(2/3)`.  Do not spend effort on the old independent-lift operator first.

## Update (2026-08-23, later lap): `NetHalfRepeatOrStoppingGrowth` is now a THEOREM

- Added `CollatzMoonshot/FrontA/BackwardStopping.lean`, **`sorry`-free**, proving
  `netHalfRepeatOrStoppingGrowth : NetHalfRepeatOrStoppingGrowth` exactly as pinned (the
  target `def` in `BackwardRenewal.lean` was not touched).  Axiom audit (observed in real
  output, 2026-08-23): `[propext, Classical.choice, Quot.sound]` — base three only.
- Proof architecture: a fuel-`H+1` frontier recursion.  `StoppingFront d H m F` bundles
  value injectivity, per-node height/band/size invariants, strict telescoping mass above
  `netHalfStatePotential false d`, and a per-node `StoppingChain`: an odd-parent ancestor
  chain of length = creation round, with pairwise-distinct values in `[d, H]` (proper
  ancestors were expanded low nodes).  Each round expands every node `≤ H` through the
  strengthened `exists_netHalfChildFinset`.
  * **Cycle branch**: `3y+1 = 2^j·(odd)` determines the odd parent, so `chain_agree` forces
    two ancestor chains from a common value to coincide while both last; a new endpoint
    value colliding with any live frontier value (chains of different lengths ⇒ `d` recurs
    mid-chain) or with its own ancestry splices, via `chain_reachesValuePos`, into
    `ReachesValuePos n n`, i.e. `OnCycle n` with `d ≤ n`.
  * **Termination**: `StoppingChain.round_add_le` — a low node at round `m` has `m`
    distinct chain values in `Icc d H`, so `m + d ≤ H + 1`; fuel `H + 1` from round `1`
    suffices, and a frontier with no low node is literally `NetHalfStoppingFrontier`.
  * **Mass**: `weighted_biUnion_expands` with root weight `sqrt(d/x)` and edge weight
    `sqrt(x/y)`; exits frozen by sum splitting over `filter (· ≤ H)`.
- `exists_netHalfChildFinset` (and its two private constructors) strengthened with the
  child-size clause `3c < 2^23·x`, recovering the cost bound (`sevenCostsAt ≤ 23`, `j=1`)
  that the packaged interface had forgotten; this feeds the `2^23 H` exit bound and, via
  `reusable_band_step` band composition, the `2^25 H` path ceiling.
- Downstream, now unconditional: composing with `NetHalfStoppingFrontier.card_bound`,
  every odd unit `2 ≤ d ≤ H` has either a positive cycle at/above `d` or more than
  `V(d)·sqrt(H/d)/200` distinct first-exit preimages in `(H, 2^23 H)` with paths in
  `[d, 2^25 H]`.  Step 4 of the chippable ladder in `FRONT-A-ROUTES.md` is closed; the
  open mathematics is now step 5 (pointwise vs. uniform, the 3-adic adversary) and the
  overlap/packing question of step 6.
- `lake build` green with `BackwardStopping` imported from `CollatzMoonshot.lean`.

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
- The finite target `NetHalfStoppingFrontier` is realized by the axiom-clean theorem
  `netHalfRepeatOrStoppingGrowth`.  Lean proves any such frontier has square-root-many
  distinct endpoints in the exact form
  `V(d) < card(S) * 200 * sqrt(d/H)`; bounded recursion either constructs it or returns an
  explicit cycle alternative.
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

The complete square-root renewal theorem is now Lean-checked through exact telescoping,
finite child sets, collision/cycle wiring, generalized band composition, recursive stopping,
and cardinality.  The next treadmill-sized task is the correlated 270-state local transfer
at exponent `2/3`; reuse the stopping proof only after that local certificate and its exact
edge comparison are kernel-checked.  Do not claim harmonic growth: `2/3 < 1`, and even the
correlated numerical critical exponent is only about `0.687` on this compact state space.

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
