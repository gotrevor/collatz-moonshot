/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.WythoffGeneral

/-!
# Theorems A′ and K: the EE identity and the E-cone trap members `α = b + √(b² + 4c)`

Research note `wythoff-2adic`, §3 (Theorem A′, Theorem K).  Write `x = α/2` and suppose
`x² = bx + c` with `b, c ∈ ℤ`; its Galois conjugate is `x′ = b − x`.  For `W = W_α`
(`WythoffGeneral.wy`):

1. **Theorem A′ (EE identity).**  If `W(2k)` is even then
   `W²(2k) = b·W(2k) + c·2k + ⌊x′·{kα}⌋` (`wy_wy_of_even_even`, any real `α`, any `k ∈ ℤ`).
2. **Cone (`0 < x′ < 1`, i.e. `1 ≤ −c ≤ b − 2`).**  The floor vanishes: `W² = bW + cn` on EE,
   which is even, so `T = {n > 0 even : W(n) even}` is a trap (`coneSet_trap`) along which
   `W^{j+2} = b·W^{j+1} + c·W^j` (`wy_iterate_add_two_of_mem_coneSet`).
3. **Anticone (`−1 < x′ < 0`, i.e. `1 ≤ c ≤ b`; e.g. `1 + √5`, `2 + 2√2`).**  For `k ≠ 0`,
   `W² = bW + cn − 1` on EE, which is odd: EE ⇒ O deterministically.
4. **Theorem K.**  In the cone, the entry points `T ∖ W(T)` (the even `n > 0` with `W(n)` even and
   `W⁻¹(n)` odd) are infinite, so by the trap theorem (`AmusicalTrap`) `W_α` has infinitely many
   infinite orbits (`wkPerm_infinitelyManyInfiniteOrbits`, unconditional).  Conditional on Weyl
   equidistribution (`WeylEquidistribution`, a literature hypothesis), the entry points have
   density `(1/4)(1 − 2/α)` (`tendsto_coneEntryCount`).

In both the cone and the anticone `b² + 4c` is automatically not a square (`(b ∓ 1)²` has the
wrong residue mod 4), so `α` is irrational.  Theorem F's members are the cone points
`(b, c) = (2r, −r)` (`alphaK_two_mul_neg`); `3 + √5 = alphaK 3 (−1)` is the `m = 2` multinacci
member of research note `wythoff-solvable` §4(b4).
-/

namespace CollatzMoonshot.WythoffCone

open CollatzMoonshot.WythoffGeneral
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits
  infinitelyManyInfiniteOrbits_of_trap)
open Filter Topology

/-! ## Theorem A′ for an arbitrary real `α` -/

/-- **(ratified, Theorem A′).**  If `x = α/2` satisfies `x² = bx + c` with `b, c ∈ ℤ` and `W(2k)`
is even, then `W²(2k) = b·W(2k) + c·2k + ⌊(b − x)·{kα}⌋`.  Paper proof: `W(2k) = kα − f = 2j`
with `f = {kα}`; `W(2j) = ⌊jα⌋ = ⌊(kα − f)x⌋` and `kα·x = 2kx² = b·kα + 2kc`, so
`jα = b(2j + f) + 2kc − fx = 2bj + 2kc + f(b − x)`; `Int.floor_intCast_add`. -/
theorem wy_wy_of_even_even {α : ℝ} {b c : ℤ} (hx : (α / 2) ^ 2 = b * (α / 2) + c) (k : ℤ)
    (h : wy α (2 * k) % 2 = 0) :
    wy α (wy α (2 * k)) =
      b * wy α (2 * k) + c * (2 * k) + ⌊((b : ℝ) - α / 2) * Int.fract ((k : ℝ) * α)⌋ := by
  sorry

/-! ## The members `α = b + √(b² + 4c)` -/

/-- `α = b + √(b² + 4c)`; `x = α/2` is the larger root of `x² = bx + c`. -/
noncomputable def alphaK (b c : ℤ) : ℝ :=
  b + √((b : ℝ) ^ 2 + 4 * c)

/-- **(ratified).**  `x = α/2` satisfies `x² = bx + c` when `b² + 4c ≥ 0`. -/
theorem alphaK_half_sq {b c : ℤ} (hD : 0 ≤ b ^ 2 + 4 * c) :
    (alphaK b c / 2) ^ 2 = b * (alphaK b c / 2) + c := by
  sorry

/-- **(ratified).**  Theorem F's members are `(b, c) = (2r, −r)`:
`2r + √(4r² − 4r) = 2r + 2√(r² − r)`. -/
theorem alphaK_two_mul_neg (r : ℕ) :
    alphaK (2 * r) (-r) = 2 * r + 2 * √((r : ℝ) ^ 2 - r) := by
  sorry

section Cone

variable {b c : ℤ}

/-- **(ratified).**  In the cone `1 ≤ −c ≤ b − 2`: `b ≥ 3` and `3 < α`. -/
theorem three_lt_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : 3 < alphaK b c := by
  sorry

theorem one_lt_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : 1 < alphaK b c :=
  lt_trans (by norm_num) (three_lt_alphaK_cone h1 h2)

/-- **(ratified).**  In the cone the conjugate `x′ = b − α/2 = (b − √(b² + 4c))/2` lies in
`(0, 1)`: `(b − 2)² < b² + 4c < b²`. -/
theorem conj_mem_Ioo_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    0 < (b : ℝ) - alphaK b c / 2 ∧ (b : ℝ) - alphaK b c / 2 < 1 := by
  sorry

/-- **(ratified).**  In the cone `α` is irrational: `(b − 2)² < b² + 4c < b²`, and the only
square strictly between, `(b − 1)²`, is `≢ b² (mod 4)` while `b² + 4c ≡ b² (mod 4)`. -/
theorem irrational_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : Irrational (alphaK b c) := by
  sorry

/-- `W_α` for a cone member, as a permutation of `ℤ`. -/
noncomputable def wkPerm (b c : ℤ) (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : Equiv.Perm ℤ :=
  wyPerm (alphaK b c) (one_lt_alphaK_cone h1 h2)

theorem wkPerm_apply (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (n : ℤ) :
    wkPerm b c h1 h2 n = wy (alphaK b c) n := rfl

/-- **(ratified, cone identity).**  On EE, `W²(2k) = b·W(2k) + c·2k` (even), for every
`k ∈ ℤ`.  Paper proof: Theorem A′ with `⌊x′f⌋ = 0` (`0 < x′ < 1`, `0 ≤ f < 1`). -/
theorem wy_wy_of_even_even_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (k : ℤ)
    (h : wy (alphaK b c) (2 * k) % 2 = 0) :
    wy (alphaK b c) (wy (alphaK b c) (2 * k)) = b * wy (alphaK b c) (2 * k) + c * (2 * k) := by
  sorry

/-- The E-cone `T = {n > 0 even : W(n) even}`. -/
def coneSet (b c : ℤ) : Set ℤ :=
  {n | 0 < n ∧ n % 2 = 0 ∧ wy (alphaK b c) n % 2 = 0}

/-- **(ratified, Theorem K, trap).**  `W(T) ⊆ T`.  Paper proof: for `n = 2k ∈ T`, `W(n) > 0` is
even and `W(W(n)) = b·W(n) + c·n` is even (`wy_wy_of_even_even_cone`). -/
theorem coneSet_trap (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    ∀ n ∈ coneSet b c, wkPerm b c h1 h2 n ∈ coneSet b c := by
  sorry

/-- **(ratified, Theorem K, recurrence).**  Along the trap, `W^{j+2} = b·W^{j+1} + c·W^j`. -/
theorem wy_iterate_add_two_of_mem_coneSet (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) {n : ℤ}
    (hn : n ∈ coneSet b c) (j : ℕ) :
    (wy (alphaK b c))^[j + 2] n =
      b * (wy (alphaK b c))^[j + 1] n + c * (wy (alphaK b c))^[j] n := by
  sorry

/-- **(ratified, Theorem K, entry points).**  `n ∈ T ∖ W(T)` iff `n > 0` is even, `W(n)` is even
and `W⁻¹(n)` is odd.  Paper proof: for `n ∈ T`, `W⁻¹(n) > 0` (`wy_pos_iff`) and
`W(W⁻¹ n) = n` is even, so `W⁻¹(n) ∈ T` iff `W⁻¹(n)` is even. -/
theorem mem_coneEntry_iff (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (n : ℤ) :
    n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c ↔
      0 < n ∧ n % 2 = 0 ∧ wy (alphaK b c) n % 2 = 0 ∧ (wkPerm b c h1 h2).symm n % 2 = 1 := by
  sorry

/-- **(ratified, Theorem K, infinitely many entry points; unconditional).**  Paper proof: if
`E = T ∖ W(T)` were finite, every `t ∈ T` would lie on the forward orbit of a point of `E`
(read backward inside `T` the values strictly decrease, `W(t) > t` on `T`, so the backward
orbit leaves `T` at an entry point); along `T`, `W(t) ≥ (3/2)t − 1`, so each forward orbit has
`O(log X)` points `≤ X` and `#(T ∩ [1, X]) = O(log X)`.  But `T` is syndetic: pick `q ≥ 1` with
`δ = ‖qα/2‖ ∈ (0, 1/4)` (Dirichlet; `α/2` irrational); along `k, k + q, k + 2q, …` the phase
`{kα/2}` moves by `±δ` per step, so it enters `[0, 1/2)` (i.e. `⌊kα⌋` even) within
`⌈1/δ⌉ + 1` steps, giving `#(T ∩ [1, X]) ≥ X/(2q(⌈1/δ⌉ + 1)) − 1`. -/
theorem coneEntry_infinite (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    {n : ℤ | 0 ≤ n ∧ n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c}.Infinite := by
  sorry

/-- **(ratified, Theorem K).**  Every cone member has infinitely many infinite orbits.  Paper
proof: `infinitelyManyInfiniteOrbits_of_trap` with `coneSet_trap` and `coneEntry_infinite`. -/
theorem wkPerm_infinitelyManyInfiniteOrbits (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    InfinitelyManyInfiniteOrbits (wkPerm b c h1 h2) := by
  sorry

open Classical in
/-- The number of entry points `T ∖ W(T)` in `[1, X]`. -/
noncomputable def coneEntryCount (b c : ℤ) (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun n =>
    n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c).card

/-- **(ratified, Theorem K, entry density, conditional on equidistribution).**  The entry points
have density `(1/4)(1 − 2/α)`, so at least that many infinite orbits per unit meet `[1, X]`.
Paper proof: `⌊kα⌋` is even iff `{kα/2} < 1/2`; by `WeylEquidistribution` (`α/2` irrational)
`#(T ∩ [1, X]) ∼ X/4`.  `W` is injective on `T` and `W(2k) = ⌊kα⌋`, so
`#(W(T) ∩ [1, X]) = #{k ≥ 1 : ⌊kα⌋ even, ⌊kα⌋ ≤ X} ∼ X/(2α)`, and `W(T) ⊆ T`. -/
theorem tendsto_coneEntryCount (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (coneEntryCount b c h1 h2 X : ℝ) / X) atTop
      (𝓝 ((1 - 2 / alphaK b c) / 4)) := by
  sorry

end Cone

section Anticone

variable {b c : ℤ}

/-- **(ratified).**  In the anticone `1 ≤ c ≤ b`: `1 < α`. -/
theorem one_lt_alphaK_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) : 1 < alphaK b c := by
  sorry

/-- **(ratified).**  In the anticone the conjugate lies in `(−1, 0)`: `b² < b² + 4c < (b + 2)²`. -/
theorem conj_mem_Ioo_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) :
    -1 < (b : ℝ) - alphaK b c / 2 ∧ (b : ℝ) - alphaK b c / 2 < 0 := by
  sorry

/-- **(ratified).**  In the anticone `α` is irrational (the only square strictly between `b²` and
`(b + 2)²` is `(b + 1)² ≢ b² (mod 4)`). -/
theorem irrational_alphaK_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) : Irrational (alphaK b c) := by
  sorry

/-- **(ratified, anticone identity).**  For `k ≠ 0` with `W(2k)` even,
`W²(2k) = b·W(2k) + c·2k − 1`, which is odd: EE ⇒ O.  Paper proof: Theorem A′ with
`⌊x′f⌋ = −1` (`−1 < x′ < 0`, and `0 < f = {kα} < 1` since `kα ∉ ℤ`). -/
theorem wy_wy_of_even_even_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) {k : ℤ} (hk : k ≠ 0)
    (h : wy (alphaK b c) (2 * k) % 2 = 0) :
    wy (alphaK b c) (wy (alphaK b c) (2 * k)) =
      b * wy (alphaK b c) (2 * k) + c * (2 * k) - 1 := by
  sorry

end Anticone

end CollatzMoonshot.WythoffCone
