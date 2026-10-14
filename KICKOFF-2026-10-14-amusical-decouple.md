# KICKOFF 2026-10-14: the two primes decouple (amusical, Lemma D)

Repo `collatz-moonshot-amusical-decouple`: close every `sorry` in `CollatzMoonshot/AmusicalDecouple.lean`.

## Ratified, do not change

The definition `countBelow` and the four theorem statements.  Everything else is read-only, except:
you may remove `private` from `tendsto_fwdWindowSurvivor_density`, `tendsto_bwdWindowSurvivor_density`,
`isOrbitMin_iff_survivors` (and the `private def`s `FwdWindowSurvivor` / `BwdWindowSurvivor` they
mention, which are definitionally `IsFwdWin` / `IsBwdWin` of `AmusicalLateDrops`) in
`AmusicalGlobal.lean`, and from `amusical_iterate_affine` / `amusicalInv_iterate_affine` if useful.
Helpers go in `CollatzMoonshot/AmusicalDecouple/*.lean`.  No `native_decide`, no new axioms, no
`decide` over more than a few thousand cases.  Lean lines ≤ 100 characters.  **Commit after every
proved target.**

## Suggested order and paper proofs (agent "lfprobe"; research §32)

1. **`not_formalMin_of_three_dvd`** (warm-up).  `t = 1`: `kBwd y 1 = stepBits (amusicalInv y)`;
   `amusicalInv (3m) = 2m` (see the defining equations of `amusicalInv`), which is even, so
   `stepBits = 1` and `3 ^ 1 < 2 ^ 1` is false.
2. **`infinitelyManyOrbits_of_ray`.**  `k ↦ (u^k x).toNat` is injective on `ℕ` (`u > 1`, `x > 0`),
   so the image of the infinite set is an infinite subset of `{n : ℕ | FormalMin n}`; apply
   `infinitelyManyOrbits_of_formalMin_infinite` (`AmusicalFormalMin.lean`).
3. **`tendsto_density_inter_of_two_three` (Lemma D).**  Write `A = ⋂ A_L`, `B = ⋂ B_L`.
   * *Step (i): `B` is equidistributed mod `2ⁿ`.*  For each `n`, `r < 2ⁿ`:
     `countBelow (B ∩ {m | m % 2ⁿ = r}) X / X → β / 2ⁿ`.  Upper: `B ⊆ B_L`, and `B_L ∩ (r + 2ⁿℕ)`
     has density `b L / 2ⁿ` by CRT (`B_L` eventually `3^b`-periodic; `Nat.Coprime (2ⁿ) (3^b)`, so the
     period `2ⁿ 3^b` splits evenly), then `L → ∞`.  Lower: the total minus the upper bounds of the
     other `2ⁿ − 1` classes.
   * *Step (ii).*  `A_L` is eventually `2^a`-periodic, so up to a finite set it is a finite union of
     classes mod `2^a`; with (i), `d(A_L ∩ B) = a L · β`.
   * *Limit.*  Upper: `A ∩ B ⊆ A_L ∩ B`, so `limsup ≤ a L β → αβ`.  Lower: `A ∩ B ⊇ (A_L ∩ B) \ (A_L \ A)`
     and `d(A_L \ A) = a L − α → 0` (`A ⊆ A_L`).
   Work with `limsup`/`liminf` or with `ε`-bounds `∀ᶠ X`, whichever is smoother; a local
   "eventually-periodic set has a density" lemma is worth proving once.
4. **`orbitMin_density_of_survivor_densities` (Corollary MD).**  Apply Lemma D with
   `A L = {n | IsFwdWin L n}`, `B L = {n | IsBwdWin L n}`; `⋂ A_L = {n | FwdSurvivor n}` and likewise
   for `B`; `A ∩ B = {n | IsOrbitMin n}` by `isOrbitMin_iff_survivors`.  `hAL`, `hBL` are the
   (un-privated) window-density lemmas.  `pf * pb = minimaConstant` by uniqueness of limits:
   `windowDensityLimit` says `fwdSurv L * bwdSurv L → minimaConstant`, and `hpf.mul hpb`.
   The real work is **eventual periodicity**:
   * forward: for `n ≥ N_L`, `IsFwdWin L n ↔ IsFwdWin L (n + 2^(2L))`.  The first `t ≤ L` steps of
     `n` and `n + 2^(2L)` have the same branches (each step reads one or two low bits), so
     `Uᵗ(n + 2^(2L)) = Uᵗ n + 3^t 2^(2L − k_t)` with `k_t` the bits read (`kFwd`); and above a height
     `N_L` (e.g. `4^(L+1)`), the sign of `Uᵗ n − n` is the sign of `3^t − 2^(k_t)` (Lemma K,
     `abs_le_four_pow_mul_iterate_sub`, or the affine form `2^k Uᵗ n = 3^t n + C`, `|C| < 4^t`).
   * backward: the same with `V`, period `3^L`.
   If eventual periodicity of the real windows proves too heavy, stop and write it up in the
   handoff; do **not** change the statement.

Notes for the next lap go in `HANDOFF-amusical-decouple.md`.
