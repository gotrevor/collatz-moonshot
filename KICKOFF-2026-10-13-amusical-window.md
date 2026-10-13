# KICKOFF 2026-10-13: window-minimum density for the amusical permutation

Treadmill lane.  One target: close the `sorry` in `windowMinDensity` in
`CollatzMoonshot/AmusicalWindow.lean`.  Done when that file is sorry-free.

## Context (read once)

`U(2n) = 3n`, `U(4n+1) = 3n+1`, `U(4n+3) = 3n+2` (`CollatzMoonshot/Amusical.lean`, inverse
`amusicalInv`).  `IsWindowMin L n`: `n ≤ U^t n` and `n ≤ U^-t n` for `1 ≤ t ≤ L`.  The claim
is that these have natural density `fwdSurv L * bwdSurv L` (exact pattern sums; values
`1/3, 2/9, 1/6, 4/27` for `L = 1..4`, checked by `windowDensity_values`).  `L = 1` is already
proved (`windowMinDensity_one`): use it as the template for the counting and limit steps.
Why it matters: `orbitMin_density_le` turns it into an unconditional upper bound on the
density of orbit minima (the easy half of `AmusicalMinimaDensity`, ≈ `0.0498`).
Background: `RESEARCH-2026-10-13-amusical-single-chain.md`.

## Ratified, do not change

`IsWindowMin`, `fwdSurv`, `bwdSurv`, `WindowMinDensity`, `windowMinDensity`'s statement,
`orbitMin_density_le_of_windowMinDensity`, everything in `Amusical.lean`.  Add helper lemmas
freely, in `AmusicalWindow.lean` or a new `CollatzMoonshot/AmusicalWindow/*.lean` imported by
it.  No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a comment saying why.

## Proof plan

Let `M = 4^L · 3^L`.

1. **Forward residues.**  If `x ≡ x' (mod 4^j)` with `j ≥ 1` then `x, x'` take the same `U`
   branch and `U x ≡ U x' (mod 4^(j-1))` (even branch: difference `3·2^(2j-1)m`; odd
   branches: `3·4^(j-1)m`).  So `n mod 4^L` fixes the first `L` forward branches, and on each
   class `U^t n = (3^t n + c) / 2^k` with `k = t + #odd steps` (the division exact).
2. **Backward residues.**  Same for `amusicalInv` with `3^L`: `U^-t n = (2^k' n + c') / 3^t`.
3. **Threshold.**  For `t ≥ 1`, `3^t ≠ 2^k`, so on each class, for `n ≥ N₀` (one bound for
   all `< M` classes and `t ≤ L`), `n ≤ U^t n` iff `2^k < 3^t`, and `n ≤ U^-t n` iff
   `3^t < 2^k'`.  So for `n ≥ N₀`, `IsWindowMin L n` iff `n mod M ∈ G` for an explicit set `G`
   of residues mod `M` (the classes whose prefix slopes all exceed `1`).
4. **Counting `G`.**  Through the CRT `ZMod M ≃ ZMod 4^L × ZMod 3^L`, goodness factors: forward
   on the `4^L` part, backward on the `3^L` part.  The residues mod `4^L` whose even/odd
   pattern is `w` number exactly `4^L / 2^L` (each step is even on half the classes: induct on
   `L` using step 1's branch bijections).  The residues mod `3^L` whose backward pattern
   (`3 | x` or not) is `v` number `3^L (1/3)^#zero (2/3)^#nonzero`.  So
   `|G| = M · fwdSurv L · bwdSurv L`.
5. **Density.**  `#{n < X : n mod M ∈ G} = |G|·⌊X/M⌋ + O(M)`; the `n < N₀` add `O(N₀)`.  Then
   squeeze as in `windowMinDensity_one`.

Steps 1-2 are the Matthews-Watts residue lemma for this map (Tavares 2013, Lemma 9, is the
backward version).  If step 4's exact count is awkward, an inequality in each direction is
enough.  An alternative to steps 1-3: prove `≤` and `≥` of the density separately, each by
grouping `n` into classes mod `M`.

## Checkpoints

Commit each green helper lemma.  Sanity-check definitions against `scripts/amusical/window.py`
(exact `δ_L`, empirical counts) before building on them.  If a step turns out false as stated,
stop and write `knowledge`-style notes in `HANDOFF-amusical-window.md`; do not weaken the
ratified statements.
