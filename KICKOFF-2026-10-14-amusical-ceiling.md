# KICKOFF 2026-10-14: the survivor ceiling (amusical, C2 / C2′)

Repo `collatz-moonshot-amusical-ceiling`: close every `sorry` in
`CollatzMoonshot/AmusicalSurvivorCeiling.lean`.

## Ratified, do not change

The three theorem statements in that file.  Everything else in the repo is read-only, except one
permitted change: you may remove `private` from `tendsto_fwdWindowSurvivor_density` in
`AmusicalGlobal.lean` if you need it (you should not; `windowMinDensity` suffices).  Helpers go in
`CollatzMoonshot/AmusicalSurvivorCeiling/*.lean` if the file grows past ~300 lines.  No
`native_decide`, no new axioms, no `decide` over more than a few thousand cases.  Lean lines ≤ 100
characters.  **Commit after every proved target** (an uncommitted final lap is lost to the merge).

## Paper proof and lemma plan (agent "c1verify"; research §31)

Existing decls: `FwdSurvivor`, `BwdSurvivor` (`AmusicalGlobal`), `IsFwdWin`, `IsBwdWin`
(`AmusicalLateDrops`), `IsWindowMin` (`AmusicalWindow`, the pointwise conjunction of the two
windows), `amusicalOrbit`, `amusicalOrbit_eq_of_mem`, `mem_amusicalOrbit_self`,
`amusicalPerm_pow_nat_apply`, `amusicalPerm_pow_neg_nat_apply`, `amusical_amusicalInv`,
`abs_le_four_pow_mul_iterate_sub` (Lemma K, both directions), `windowMinDensity L`
(`#W_L(range X)/X → fwdSurv L · bwdSurv L`), `windowDensityLimit` (`δ_L → minimaConstant`),
`fwdSurvivor_three_separation` (the skeleton for step 2), `infinitelyManyOrbits_of_fwdSurvivors_three`
(the finite-orbit-set bookkeeping pattern).

**Lemma decomposition.**
1. **`exists_bwdDrop`** (~6 lines): `¬ IsBwdWin L n → ∃ t, 1 ≤ t ∧ t ≤ L ∧ amusicalInv^[t] n < n`, by
   `unfold IsBwdWin; push_neg`.  Take `g := Nat.find` and record `Nat.find_spec` and `Nat.find_min'`
   as `hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n`.
2. **`fwdSurvivor_le_iterate_inv`** (P′, ~30 lines):
   `FwdSurvivor n → FwdSurvivor n' → n' < n → n' ∈ amusicalOrbit n → 1 ≤ g →`
   `(∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) → n' ≤ amusicalInv^[g] n`.
   * Skeleton of `fwdSurvivor_three_separation`: `obtain ⟨k, hk⟩`, `Int.eq_nat_or_neg`, the two `pow_apply` lemmas.
   * Nat case: `t = 0` is `hlt.ne`; otherwise `hn t`.
   * Neg case: `rcases lt_trichotomy t g`.  For `t > g`, rewrite `amusicalInv^[t] = amusicalInv^[t−g] ∘ amusicalInv^[g]`
     (`Function.iterate_add_apply`), cancel with `(Function.LeftInverse.iterate amusical_amusicalInv (t−g))`,
     and apply `hn' (t−g)`.
3. **`fwdSurvivor_gap`** (G, ~25 lines):
   `FwdSurvivor n → FwdSurvivor n' → 0 ≤ n' → n' < n → n' ∈ amusicalOrbit n → ¬ IsBwdWin L n → n ≤ 4 ^ L * (n − n' + 1)`.
   Use 1 and 2, then `(abs_le_four_pow_mul_iterate_sub g hg n).2`, `abs_of_nonneg`, `abs_of_neg` on
   `Vᵍ n − n`, and `pow_le_pow_right₀ (by norm_num) hgL`; finish with `nlinarith`.
4. **`card_le_of_sep`** (B, ~30 lines, pure `Finset ℕ`):
   `1 ≤ D → (∀ n ∈ S, A ≤ n ∧ n < B) → (∀ a ∈ S, ∀ b ∈ S, a < b → a + D ≤ b) → S.card ≤ (B − A) / D + 1`.
   Use `Finset.card_le_card_of_injOn (fun n => (n − A) / D)` into `Finset.range ((B − A)/D + 1)`, then
   `Nat.div_le_div_right`.  For injectivity, `Nat.div_add_mod` shows two points of one bucket differ by `< D`.
5. **`sep_arith`** (~20 lines, `omega`/`Nat.div` lemmas): for `1 ≤ M` and `2 * 4^L ≤ X / M`, with
   `D := (X / M) / (2 * 4^L)`: `1 ≤ D`, `(X − X/M)/D ≤ 8 * M * 4^L`, and
   `∀ n ≥ X/M, n ≤ 4^L * (n − n' + 1) → n' + D ≤ n` (in ℤ, then cast).
6. **`card_orbit_fwdOnly_le`** (O, ~30 lines): for any `x : ℤ`,
   `((Finset.Ico (X/M) X).filter fun n : ℕ => (n:ℤ) ∈ amusicalOrbit x ∧ FwdSurvivor n ∧ ¬ IsBwdWin L n).card ≤ 8*M*4^L + 1`.
   Apply 4 with 5.  For separation use 3, with `n' ∈ amusicalOrbit n` from `amusicalOrbit_eq_of_mem`
   applied to both memberships.
7. **`card_fwdOnly_le_of_finite`** (~35 lines): `¬ AmusicalInfinitelyManyOrbits → ∃ r, ∀ L M X, 1 ≤ M → 2*4^L ≤ X/M →`
   `((Finset.Ico (X/M) X).filter fun n : ℕ => FwdSurvivor n ∧ ¬ IsBwdWin L n).card ≤ r * (8*M*4^L + 1)`.
   * `r := hfin'.toFinset.card`, as in `infinitelyManyOrbits_of_fwdSurvivors_three`.
   * `Finset.card_eq_sum_card_fiberwise` with `f n := amusicalOrbit n`.
   * Each fiber `amusicalOrbit n = O` with `O = amusicalOrbit x₀` is bounded by 6 (`mem_amusicalOrbit_self`).
   * Finish with `Finset.sum_le_card_nsmul`.
8. **`card_fwdSurvivor_le_split`** (~25 lines): `#FS(range X) ≤ #W_L(range X) + X/M + #(Ico (X/M) X filter (FS ∧ ¬BwdWin L))`.
   `range X ⊆ range (X/M) ∪ Ico (X/M) X`.  On the upper part, `FwdSurvivor n ∧ IsBwdWin L n → IsWindowMin L n`
   (`IsWindowMin` is the pointwise conjunction; `FwdSurvivor → IsFwdWin`).  Then `card_union_le` twice.
9. **`fwdSurvivor_density_le_of_finite`** (C2, ~40 lines).  Fix `M := ⌈3/ε⌉₊`.
   * `windowMinDensity L` eventually gives `#W_L ≤ (δ_L + ε/3)X`.
   * `X/M ≤ (ε/3)X`.
   * `r(8M4^L+1) ≤ (ε/3)X` eventually (`Filter.eventually_ge_atTop`).
   * Combine with 7 and 8.
10. **`infinitelyManyOrbits_of_fwdSurvivor_density`** (C2′, ~25 lines).  `by_contra hfin`.  `windowDensityLimit`
    gives `L` with `δ_L < minimaConstant + η/2`.  Then 9 with `ε = η/4` is eventually `< (minimaConstant + η) X`,
    which contradicts `h` via `Filter.Frequently.and_eventually` and `Filter.Eventually.exists`.
11. **Mirror** (optional, ~3 × 25 lines): `bwdSurvivor_le_iterate` (P′ with `U`, `V` swapped), its gap via
    `(abs_le_four_pow_mul_iterate_sub g hg n).1`, and the `BwdSurvivor` versions of 6–10.  This gives
    `d_upper(BS) > c ⇒ (a)`, and with both, `FS ∪ BS`.

Effort: about 250–300 Lean lines in total, with no new mathematics needed at any step.  Kernel risk is low:
the only analytic content is two `Filter` limit facts that are already proved.


**P′ in words.**  `n' < n` forward survivors on one orbit, `g` = least `t ∈ [1, L]` with
`Vᵗ n < n`.  Write `n' = Uᵏ n`.  `k ≥ 1` contradicts `FwdSurvivor n`; `k = 0` contradicts `n' < n`.
So `n' = Vᵗ n`, `t ≥ 1`: `t < g` gives `Vᵗ n ≥ n > n'`; `t = g` is equality; `t > g` gives
`Vᵍ n = U^(t−g) (Vᵗ n) = U^(t−g) n' ≥ n'` by `FwdSurvivor n'`.

Notes for the next lap go in `HANDOFF-amusical-ceiling.md`.
