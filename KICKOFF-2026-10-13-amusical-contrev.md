# KICKOFF 2026-10-13: reversors determined by residues (amusical)

Repo `collatz-moonshot-amusical-contrev`: close every `sorry` in
`CollatzMoonshot/AmusicalContinuousReversor.lean`.

## Ratified, do not change

All statements in that file, `stepSym`, `IsAmusicalReversor`, and the Prop
`AmusicalNoContinuousReversor` (open; do not try to prove it).  Everything else in the repo is
read-only.  Helpers go in your own file or `CollatzMoonshot/AmusicalContinuousReversor/*.lean`.
No `native_decide`, no new axioms; `decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Paper proofs

Notation: `V = amusicalInv`.  `ι ∘ U = V ∘ ι` implies `ι ∘ V = U ∘ ι` (apply at `V n` and use
`amusical_amusicalInv`), hence `ι ∘ Uᵏ = Vᵏ ∘ ι` and `ι ∘ Vᵏ = Uᵏ ∘ ι`.

* **F1.**  `n mod 3^m` ↔ backward symbols `stepSym (Vʲ n)`, `1 ≤ j ≤ m`
  (`stepSym (V n)` is `0, 1, 2` as `n ≡ 0, 1, 2 mod 3`): a bijection `ℤ/3^m ≃ Fin m → Fin 3`.
  Induct: on `n = 3q+r`,
  `V n = λq + c` with `λ ∈ {2,4}` a unit mod 3.
* **F2.**  A forward word `w` (symbols of `n, U n, …`) of length `L` cuts out one class mod
  `2^{|w|}`, `|w| = #0 + 2·#{1,2}`; induct with `U` affine of slope `3/2`, `3/4` and `3` a unit
  mod powers of 2.  The window machinery in `AmusicalWindow.lean` (affine branches on classes
  mod `4^L`) may be reusable.
* **Propagation.**  `Uᵏ m mod 2^b` is fixed by `m mod 2^{b+2k}`; `Vᵏ m mod 3^b` by `m mod 3^{b+k}`.

1. **`reversor_eq_of_stepSym_eq`.**  `stepSym (Uᵏ (ι n)) = stepSym (ι (Vᵏ n))`, so `ι n` and
   `ι' n` have the same forward itinerary, hence agree mod `2^j` for all `j` (F2), hence are equal.
2. **`reversor_const_of_twoAdicContinuous`** (Theorem A).  Fix `n, y, b`; `c := c(b)`, `k := c`.
   The forward cylinder `C_w` of `n` of length `k` is a class mod `2^e`, `e ≥ k`, so
   `C_w ⊆ n + 2^c ℤ`.  `Uᵏ` maps `C_w` onto a class mod `3ᵏ`, which meets every class mod
   `2^{c₂}`, `c₂ = c(b+2k)`; pick `z ∈ C_w` with `Uᵏ z ≡ Uᵏ y [2^{c₂}]`.  Then
   `ι (Uᵏ z) ≡ ι (Uᵏ y) [2^{b+2k}]`, and `ι z = Uᵏ (ι (Uᵏ z))`, `ι y = Uᵏ (ι (Uᵏ y))`, so by
   propagation `ι z ≡ ι y [2^b]`; with `ι z ≡ ι n [2^b]` this gives `ι n ≡ ι y [2^b]` for all `b`,
   so `ι n = ι y`.  A constant reversor `v` has `v = V v`, so `v ∈ {-1, 0, 1}`.
3. **`reversor_const_of_threeAdicContinuous`** (Theorem A′).  Mirror: backward cylinders are
   classes mod `3ᵏ`; `Vᵏ` maps one onto a class mod a power of 2, meeting every class mod `3^{c₂}`;
   `ι z = Vᵏ (ι (Vᵏ z))`; `V` propagates `3^{b+k} → 3^b`.
4. **`no_continuous_linear_reversor`** (Theorem C).  Let `g` be the table: `stepSym (ι n)` as a
   function of `n mod 2^c₀ 3^d₀`, `w = c₀ + d₀`.  For `k ≥ c₀`, `stepSym (Uᵏ (ι n)) =
   g (Vᵏ n mod 2^c₀3^d₀) = f(β_{k−c₀+1}(n), …, β_{k+d₀}(n))` (`Vᵏ n mod 2^c₀` is fixed by its first
   `c₀` forward symbols `β_k, …, β_{k−c₀+1}` of `n`; `Vᵏ n mod 3^d₀` by `β_{k+1..k+d₀}`).  `q :=
   #{u : f u = 0}/3^w ≠ 1/2`; `ρ = max(q, 1−q)`, `T = {0}` or `{1,2}` accordingly.  Positions
   `k_i = c₀ + i·w`, `i < L`.  `D := {m : stepSym (U^{k_i} m) ∈ T ∀ i}` is a union of classes mod
   `2^{2(k_{L−1}+1)}` of density `2^{−L}` (F2); `ι⁻¹ D` is a union of classes mod
   `3^{k_{L−1}+d₀}` of density `ρ^L` (disjoint windows, F1).  `ι` maps `ι⁻¹D ∩ [−N, N]` injectively
   into `D ∩ [−(CN+D), CN+D]`; counting classes in intervals (error ≤ modulus) gives
   `ρ^L ≤ C · 2^{−L}` after `N → ∞`, false for `L` large since `2ρ > 1`.  A finite-`N` version
   avoids limits: pick `L` with `(2ρ)^L > 2C+2`, then `N` a large multiple of both moduli.

Notes for the next lap go in `HANDOFF-amusical-contrev.md`.
