# KICKOFF 2026-10-14: powers of 3 separate orbits (amusical, Theorem P3)

Repo `collatz-moonshot-amusical-powers`: close every `sorry` in `CollatzMoonshot/AmusicalPowers.lean`.

## Ratified, do not change

All statements and definitions in that file (`PowerAdmissible` and the five theorems).  Everything
else in the repo is read-only; reuse `amusical_iterate_staircase`, `staircase_fwdSurvivor`
(`AmusicalStaircase.lean`), `fwdSurvivor_three_not_mem_orbit`, `fwdSurvivor_three_not_periodic`,
`infinitelyManyOrbits_of_fwdSurvivors_three` (`AmusicalSurvivorSeparation.lean`).  Helpers go in
`CollatzMoonshot/AmusicalPowers/*.lean` if the file grows past ~300 lines.  No `native_decide`, no
new axioms, no `decide` over more than a few thousand cases.  Lean lines ≤ 100 characters.
**Commit after every proved target** (an uncommitted final lap is lost to the merge).

## Paper proofs (research §30; agent report: lfsep)

Write `p_b = 2^(s−b) 3^b y`; `p_{b+1} = 3 p_b / 2`; `amusical^[j] (2^s y) = p_j` for `j ≤ s`.

1. **`powerAdmissible_window_point`.**  `t = 0` gives `3 · 2^L y ≤ 2 · 3^s y`, so `s ≥ 1`
   (indeed `s ≥ 2`).  `p_1 = 3 · 2^(s−1) y ≤ 3 · 2^(L−2) y < 2^L y`.  Take the least `b ≥ 1` with
   `2^L y ≤ p_b` (exists: `b = s` works, `Nat.find`); then `b ≥ 2` and `p_{b−1} < 2^L y`, so
   `2 p_b = 3 p_{b−1} < 3 · 2^L y`.  Clearing powers: multiply through by `2^b` to stay in `ℤ`.
2. **`powers_not_periodic`.**  Let `n = p_b` from step 1.  `n` is a forward survivor
   (`staircase_fwdSurvivor` with `a = s − b`; `htop` from admissibility since `2n < 3 · 2^L y`),
   `3 ∣ n`, `0 < n`, so `n` is not periodic.  `3^s y = amusical^[s−b] n`, and for an injective map a
   point whose forward image is periodic is itself periodic.
3. **`powers_orbit_ne` (P3).**  Points `n = p_b(s)` and `n' = p_{b'}(s')` from step 1.  `n ≠ n'`:
   equal would force `s − b = s' − b'` and `b = b'` (`y` odd and prime to 3: compare
   `padicValInt 2` and `padicValInt 3`, or `Nat.factorization`), so `s = s'`.  WLOG `n < n'`;
   `fwdSurvivor_three_not_mem_orbit` gives `n' ∉ amusicalOrbit n`.  Orbits: `n ∈ amusicalOrbit (3^s y)`
   (staircase, backward), so `amusicalOrbit n = amusicalOrbit (3^s y)`; an orbit-equality lemma may
   already exist in `Amusical.lean` / `AmusicalGlobal.lean` (search `amusicalOrbit_eq`), else prove
   it from `amusicalPerm ^ (i + j) = …`.  The case `n' < n` is symmetric.
4. **`infinitelyManyOrbits_of_powers`.**  Copy the shape of `infinitelyManyOrbits_of_fwdSurvivors_three`:
   `s ↦ amusicalOrbit (3^s y)` is injective on `T` by step 3, lands in the finite orbit set
   (`3^s y ≥ 0`).
5. **`infinitelyManyOrbits_of_powers_log` (P3′).**  Assume finitely many orbits, `r` of them.
   Blocks: `L₀ = 0`, `L_{j+1} = L_j + L_j / (k+1) + 1`.  For `s ∈ [L_j, L_{j+1})`,
   `PowerAdmissible y (s + s/k + 1) s` implies `PowerAdmissible y L_{j+1} s` (monotone in `L`:
   `L_{j+1} ≤ s + s/k + 1` and `2^L` grows), so each block holds `≤ r` elements of `T` (step 4's
   injectivity).  Count blocks below `S`: `L_j ≥ j` always and `L_{j+1} ≥ (1 + 1/(2k+2)) L_j` once
   `L_j ≥ k + 1`, so `#{j : L_j ≤ S} ≤ C_k (Nat.log 2 S + 1)` for an explicit `C_k` (e.g. a crude
   `C_k = 8 (k + 1)^2` is fine, any explicit bound works).  Take `C = r · C_k`.  Alternative if
   cleaner: dyadic outer blocks `[2^m, 2^(m+1))`, each split into `≤ 2(k+1)` arithmetic sub-blocks of
   length `⌈2^m/(k+1)⌉`; `s` in a sub-block `[a, a + 2^m/(k+1))` with `a ≥ 2^m` is admissible for
   `L = a + 2^m/(k+1)`, since `2^m/(k+1) ≤ s/k`.  Pick whichever partition is easiest in Lean.

Notes for the next lap go in `HANDOFF-amusical-powers.md`.
