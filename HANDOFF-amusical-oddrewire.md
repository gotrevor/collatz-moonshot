# HANDOFF: amusical oddrewire (2026-10-14), done

All three targets in `CollatzMoonshot/AmusicalOddRewire.lean` are proved, `#print axioms` gives only
`propext, Classical.choice, Quot.sound`, and the ratified statements are unchanged.

- `fwdSurvivor_three_separation_of`: the staged proof with `h2` in place of `amusical_two_mul`.
- **GL** `exists_glue` (`AmusicalOddRewire/Glue.lean`): for any `σ : Perm ℕ`, `S`, `F → ∞` there is
  `τ` differing from `σ` only at `GluePt σ S` points of `S` (infinite orbit, `S` met at unboundedly
  late and early integer times), at most `F N` times below `N`, with all gluable points on one
  `τ`-orbit.
  - The reconnection is `IsCutSet.glue` (`AmusicalOddRewire/CutSet.lean`), a copy of the
    `sparselyRewiredPerm` machinery with the cut set as a parameter.  `AmusicalSeventh/Rewire.lean`
    is untouched.
  - Cut choice: index `q = ⟪⟪x, K⟫, side⟫` and pick a time past `K` with the point in `S` and
    `≥ B q + q`, where `F N > q` for `N ≥ B q`.  So the change count is at most `F N` directly, with
    no stage bookkeeping (simpler than the kickoff's `Y_k` / `2k` plan).
- T1★ `exists_oddRewire`: `gluePt_odd_of_infinite` (`OddTails.lean`) with `S` = the odd numbers,
  then GL.
- TT `tail_threshold`: the helpers are in `Threshold.lean`.
  - ⇐: tails are `τ`-rays, through `infinite_tauOrbits_of_rays` with `ε = ±1`.
  - ⇒: GL with `F = id`.  Non-gluable points keep their `U`-orbit (`zpow_eq_of_not_gluePt`) and
    carry an `S`-free tail (`exists_tail_of_not_gluePt`).

Not done (outside this file's scope): kickoff item 9, NG★ (GL with `S_k = 1 mod 6^max k 2`).  It has
no Lean statement yet.  `exists_glue` takes a single `S`, so NG★ needs a stage-dependent variant:
replace `S` by `S (q)` in `glueChange`.
