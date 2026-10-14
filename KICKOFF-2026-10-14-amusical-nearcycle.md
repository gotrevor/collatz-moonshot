# KICKOFF 2026-10-14: the quantized ladder and the near-cycle reduction (amusical, fsfloor)

Repo `collatz-moonshot-amusical-nearcycle`: close every `sorry` in `CollatzMoonshot/AmusicalNearCycle.lean`.

## Ratified, do not change

`NearCycleStart` and the four theorem statements.  Everything else is read-only (you may remove
`private` from helpers such as `amusical_iterate_affine` in `AmusicalGlobal.lean`).  Helpers go
in `CollatzMoonshot/AmusicalNearCycle/*.lean`.  No `native_decide`, no new axioms, no `decide`
over more than a few thousand cases.  Lean lines ≤ 100 characters.  Do **not** edit
`RESEARCH-*.md`.  **Commit after every proved target.**

## Paper proofs (agent "fsfloor", research §35)

1. **`bwdSurvivor_odd_separation`** (mirror of `fwdSurvivor_three_separation`).  `n ∈ orbit n'`,
   `n < n'`.  If `n = V^k n'` with `k ≥ 1`, `BwdSurvivor n'` gives `n' ≤ n`: contradiction.  So
   `n = U^k n'`, `k ≥ 1`.  `k = 1`: `n = U n' ≤ (3n' + 1)/4` (`n'` odd: `4q+1 ↦ 3q+1`, `4q+3 ↦ 3q+2`).
   `k ≥ 2`: `U n' = V^(k−1) n`, and `BwdSurvivor n` gives `n ≤ U n'`.
2. **`rung_log_ratio`** (SQ1).  Put `p = V^g n`, `x_k = U^k p = V^(g−k) n` (`x_0 = p`, `x_g = n`).
   * `p ≥ 2` and `p` is even: `p` is a forward survivor (its forward orbit is the `x_k`, `k < g`,
     all `≥ n > p` by `hmin`, then `n`, then `≥ n` by `hn`), and an odd number `> 1` is not
     (`U y < y`; `p ≤ 1` would make `n` a fixed point `0` or `1`).
   * Each step: `x_{k+1} · 2^{d_k} = 3 x_k + e_k`, `d_k ∈ {1,2}`, `e_k ∈ {0,1,−1}`, `e_k = 0` iff `x_k`
     even.  Take `a = Σ d_k`.  Then `log(n/p) = g log 3 − a log 2 + Σ log(1 + e_k/(3 x_k))`.
   * Odd steps have `1 ≤ k < g`, so `x_k > n` (`≥ n` by `hmin`, `≠ n` else `n` periodic and `hdrop`
     contradicts `hmin`).  `|log(1 + u)| ≤ |u|/(1 − |u|)` with `u = ±1/(3x_k)` gives
     `≤ 1/(3x_k − 1) ≤ 1/(3n − 1)`, and there are `≤ g` terms.
3. **`rung_depth_spectrum`** (SQ2).  Divide SQ1 by `log 2`: `|log₂ ρ − (gθ − a)| ≤ ε` with `ε` the
   left side of `hbig`.  `0 < log₂ ρ ≤ θ − 1`: `ρ > 1` by `hdrop`, and `n ≤ U p = 3p/2` (`p` even;
   `U p` is `n` or an intermediate point `≥ n`).  So `gθ − a ∈ (−ε, θ − 1 + ε]`.  Cases on
   `a` vs `⌊gθ⌋`: `a = ⌊gθ⌋` gives `fract ≤ θ − 1 + ε`, and `ε < |fract − (θ − 1)|` forces
   `fract ≤ θ − 1`; `a ≥ ⌊gθ⌋ + 1` gives `gθ − a ≤ fract − 1 < −ε` (by `ε < 1 − fract`); `a ≤ ⌊gθ⌋ − 1`
   gives `gθ − a ≥ 1 + fract > θ − 1 + ε` (`θ − 1 < 0.6`, `ε < 1 − fract`, so `θ − 1 + ε < 1.6 − fract`;
   if this bound is not enough, use `ε < 1 − fract ≤ 1` and `θ < 1.6`; check carefully and, if a
   genuine gap appears, record it in the handoff rather than changing the statement).
4. **`infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null`** (NC′).  By contradiction, `r`
   orbits.  Reuse `AmusicalSurvivorCeiling/Packing.lean` (P′ `fwdSurvivor_le_iterate_inv`-style
   lemma, per-orbit fibering).
   * (i) Per orbit and block `(Y, 2Y]`: the forward survivors `n₁ < … < n_m` of one orbit there
     satisfy `n_m ≤ 2Y` and `n₁ > Y`, and each `n_{i+1}` has `pred = ` the next lower survivor
     `≥ n_i`; telescoping, `#{i : n_{i+1} − pred(n_{i+1}) > D} ≤ (log 3)/log(1 + D/(2Y)) ≤ 4Y/D`
     (any explicit bound linear in `Y/D` works; work multiplicatively in `ℕ`: a product of `k`
     ratios each `≥ (2Y + D)/(2Y)` is `≤ 3·(something)`).
   * (ii) A rung `n` (forward survivor with a backward drop) with gap `n − pred n ≤ D` makes
     `pred n` a `D`-near-cycle start: `g` = depth, intermediate points `> n`; the first re-entry of
     `[0, p + D]` is at time `≤ g`, landing in `(p, p + D]`.
   * (iii) `pred` is injective on rungs (`U^g p = n` with `g` determined by `p`'s first return).
   * (iv) Counting: under `r` orbits at most `r` points are orbit minima; infinitely many blocks
     have `#FS ∩ (Y, 2Y] ≥ δY/2`; choose `D` with `r · 4Y/D ≤ δY/8`; the near-cycle starts in
     `[0, 2Y)` then number `≥ δY/4 − r − O(1)`, contradicting density `0` for that `D`.

Notes for the next lap go in `HANDOFF-amusical-nearcycle.md`.
