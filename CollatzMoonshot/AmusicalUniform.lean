/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalAntiKohl

/-!
# Weakly sign-uniform maps: reversal and residue-local invariants die

`U` is *weakly sign-uniform*: at each prime its slopes never change valuation sign.  The
2026-10-13 "uniform" agent asked whether such a map can be residue-transitive and still have
provably infinitely many orbits.  The ping-pong example `PP(0)` (`AmusicalPingPong.lean`) only
works because its slope valuations change sign at `5` and `7`.  The question stays open, but
three certificate routes close.

**Reversal at one prime (Theorem NR_p).**  Suppose every slope of an RCWA permutation `σ` has
`v_p ≥ 0` at one prime `p`, and `v_p` of the slope of `σᵏ` is unbounded.  Then no finitely
piecewise-affine bijection reverses `σ` (`no_piecewiseAffine_reversor_of_valNonneg`).  It
generalizes Theorem NR (`no_piecewiseAffine_reversor`, where `p = 3` and every valuation is `1`).
The Gaussian `H` escapes because complex conjugation is semilinear and swaps the two primes over
`2`.  The only ring automorphism of `ℤ` is the identity, so no RCWA map of `ℤ` can play that role.

**Island Lemma.**  A cycle mapped to itself by an RCWA reversor has slope product `±1`
(`island_cycle_slope`).  So `σ^{2L}` is the identity on a whole residue class, and `σ` is not
residue-transitive.  This killed all of the agent's 1400+ random "involution × involution"
candidates.

**Residue-local invariants (Theorem M3/M4).**  The residue Markov chain of a weakly
sign-uniform transitive map realizes every class-to-class path along a single orbit.  For `U`
this is `AmusicalTopologicallyTransitive` (target).  It follows from the agent's M3 together with
`amusical_no_periodic_cone`.  Then any orbit invariant that is constant on two residue classes takes the
same value on both (`amusical_invariant_eq_of_locallyConst`).  This kills every invariant built
from finitely many valuations, leading digits, or the `6`-free part mod `n`.

**Side example `δ`.**  `δ(6k) = 6k+3`, `δ(6k+2) = 6k+1`, `δ(6k+4) = 4k`, `δ(4k+3) = 4k+2`,
`δ(4k+1) = 6k+5`.  It is a product of two class-transposition involutions with slopes `2/3, 1, 3/2`,
and every orbit is finite (`delta_periodic`, target).  Its residue graph is strongly connected
modulo `12, 24, 36, 48, 96, 108` but not modulo `60, 72, 144`, a warning that shallow
transitivity tests mislead.

Paper proofs: agent report `uniform.md`, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §17.  NR_p and the Island Lemma were hand-checked.
`δ` was re-checked independently by `scripts/amusical/delta_ren.py`: bijective on a window,
`10003` finite cycles through `[−30000, 30000]`, SCC counts, with `U` as a strongly connected
control.  Treadmill target: close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-! ## Slopes of iterates -/

/-- The slope of `σᵏ` at `x`, for an RCWA `σ` with coefficient tables `a`, `c` mod `m`. -/
def rcwaIterSlope (σ : ℤ → ℤ) (m : ℕ) (a c : ℤ → ℤ) (k : ℕ) (x : ℤ) : ℚ :=
  ∏ i ∈ Finset.range k, ((a (σ^[i] x % m) : ℚ) / c (σ^[i] x % m))

/-! ## Theorem NR_p -/

/-- **Target (Theorem NR_p).**  Let `σ` be an RCWA permutation whose slopes all have `v_p ≥ 0`
(and those of `σ⁻¹`, their reciprocals, `v_p ≤ 0`), with `v_p` of the slope of `σᵏ` unbounded.
Then no bijection affine on each of finitely many pieces reverses `σ`.  Paper proof (`uniform.md`
§2.1): let `T` bound `|v_p|` of the piece slopes of `ι`; pick a `k`-cylinder class where `σᵏ` has
slope `S` with `v_p S > 2T`; refine to an infinite set on which `ι ∘ σᵏ` and `σ⁻ᵏ ∘ ι` are both
single affine maps (slopes `t_j S` and `t_i / S'`, `v_p S' ≥ 0`); equal affine maps on an infinite
set have equal slopes, so `v_p t_j − v_p t_i ≤ −v_p S < −2T`, a contradiction. -/
theorem no_piecewiseAffine_reversor_of_valNonneg (p : ℕ) [Fact p.Prime] (σ : Equiv.Perm ℤ)
    {m : ℕ} {a b c : ℤ → ℤ} (hσ : IsRCWA σ m a b c)
    {m' : ℕ} {a' b' c' : ℤ → ℤ} (hσ' : IsRCWA σ.symm m' a' b' c')
    (hval : ∀ r : ℤ, 0 ≤ r → r < m → 0 ≤ padicValRat p ((a r : ℚ) / c r))
    (hval' : ∀ r : ℤ, 0 ≤ r → r < m' → padicValRat p ((a' r : ℚ) / c' r) ≤ 0)
    (hacc : ∀ L : ℤ, ∃ (x : ℤ) (k : ℕ), L ≤ padicValRat p (rcwaIterSlope σ m a c k x)) :
    ¬ ∃ (ι : Equiv.Perm ℤ) (n : ℕ) (piece : ℤ → Fin n) (a₀ b₀ c₀ : Fin n → ℤ),
      (∀ j, c₀ j ≠ 0) ∧ (∀ x, c₀ (piece x) * ι x = a₀ (piece x) * x + b₀ (piece x)) ∧
      ι * σ * ι⁻¹ = σ⁻¹ := by
  sorry

/-! ## The Island Lemma -/

/-- **Target (Island Lemma).**  If an RCWA permutation `ι` reverses an RCWA permutation `σ` and
maps a `σ`-cycle `Z` to itself, the slope product of `σ` around `Z` is `±1`.  Paper proof
(`uniform.md` §2.2): near each `x` both sides of `ι σ = σ⁻¹ ι` are affine, so
`t(σx) s(x) = t(x) / s(σ⁻¹ι x)`; multiply over `Z`; the `t` factors telescope, and `σ⁻¹ι = ισ`
permutes `Z`, so `S_Z = 1 / S_Z`. -/
theorem island_cycle_slope (σ ι : Equiv.Perm ℤ) {m : ℕ} {a b c : ℤ → ℤ}
    (hσ : IsRCWA σ m a b c) {m' : ℕ} {a' b' c' : ℤ → ℤ} (hι : IsRCWA ι m' a' b' c')
    (hrev : ι * σ * ι⁻¹ = σ⁻¹) {z : ℤ} {L : ℕ} (hL : 0 < L) (hz : (σ ^ L) z = z)
    (hZ : ∀ i : ℕ, ∃ j : ℕ, ι ((σ ^ i) z) = (σ ^ j) z) :
    rcwaIterSlope σ m a c L z = 1 ∨ rcwaIterSlope σ m a c L z = -1 := by
  sorry

/-! ## Residue-local invariants -/

/-- **Believed (target): `U` is topologically transitive on `Ẑ`.**  Every residue class reaches
every other along a single orbit.  Paper proof: Theorem M3 (`uniform.md` §3.1, the type Markov
chain of a weakly sign-uniform map) applied to the strongly connected residue graphs of
`amusical_no_periodic_cone`.  Checked for `U` with `K = 12, 36, 48, 72` (agent `m3check.py`). -/
def AmusicalTopologicallyTransitive : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ r s : ℤ, ∃ (x : ℤ) (n : ℕ), 0 < n ∧ x ≡ r [ZMOD M] ∧
    amusical^[n] x ≡ s [ZMOD M]

/-- **Target.**  `U` is topologically transitive on `Ẑ` (Theorem M3 for `U`). -/
theorem amusical_topologicallyTransitive : AmusicalTopologicallyTransitive := by
  sorry

/-- **Proved (M4 for `U`).**  Given topological transitivity, an orbit invariant that is constant
on the class of `r` and on the class of `s` (mod the same `M`) takes the same value on both.  So
no residue-local function separates orbits. -/
theorem amusical_invariant_eq_of_locallyConst {α : Type*} (htr : AmusicalTopologicallyTransitive)
    (g : ℤ → α) (hg : ∀ x, g (amusical x) = g x) {M : ℕ} (hM : 0 < M) {r s : ℤ}
    (hr : ∀ x, x ≡ r [ZMOD M] → g x = g r) (hs : ∀ x, x ≡ s [ZMOD M] → g x = g s) :
    g r = g s := by
  obtain ⟨x, n, -, hxr, hxs⟩ := htr M hM r s
  have hiter : ∀ k : ℕ, g (amusical^[k] x) = g x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hg, ih]
  rw [← hr x hxr, ← hiter n, hs _ hxs]

/-! ## The side example `δ` -/

/-- `δ(6k) = 6k+3`, `δ(6k+2) = 6k+1`, `δ(6k+4) = 4k`, `δ(4k+3) = 4k+2`, `δ(4k+1) = 6k+5`. -/
def delta (x : ℤ) : ℤ :=
  if x % 6 = 0 then x + 3
  else if x % 6 = 2 then x - 1
  else if x % 6 = 4 then 4 * (x / 6)
  else if x % 4 = 3 then x - 1
  else 6 * (x / 4) + 5

/-- The inverse of `δ`. -/
def deltaInv (y : ℤ) : ℤ :=
  if y % 6 = 3 then y - 3
  else if y % 6 = 1 then y + 1
  else if y % 4 = 0 then 6 * (y / 4) + 4
  else if y % 4 = 2 then y + 1
  else 4 * (y / 6) + 1

theorem deltaInv_delta (x : ℤ) : deltaInv (delta x) = x := by
  unfold delta deltaInv
  split_ifs <;> omega

theorem delta_deltaInv (y : ℤ) : delta (deltaInv y) = y := by
  unfold delta deltaInv
  split_ifs <;> omega

/-- `δ` as a permutation of `ℤ`. -/
def deltaPerm : Equiv.Perm ℤ where
  toFun := delta
  invFun := deltaInv
  left_inv := deltaInv_delta
  right_inv := delta_deltaInv

/-- At a multiple of four, divisibility of the shifted coordinate by three gives the
contracting edge in the finite `2`-`3` lattice used by `delta_periodic`. -/
theorem delta_four_contract (k : ℤ) (h : 3 ∣ k + 2) :
    delta (4 * k) = 4 * (2 * (k + 2) / 3 - 2) := by
  unfold delta
  split_ifs <;> omega

/-- The contracting edge sends the shifted coordinate `k + 2` to two thirds of itself. -/
theorem delta_four_contract_coordinate (k : ℤ) (h : 3 ∣ k + 2) :
    delta (4 * k) / 4 + 2 = 2 * (k + 2) / 3 := by
  rw [delta_four_contract k h]
  omega

/-- In the inverse direction, an even shifted coordinate gives the expanding edge of the same
finite `2`-`3` lattice. -/
theorem deltaInv_four_expand (k : ℤ) (h : 2 ∣ k + 2) :
    deltaInv (4 * k) = 4 * (3 * (k + 2) / 2 - 2) := by
  unfold deltaInv
  split_ifs <;> omega

/-- The inverse expanding edge sends the shifted coordinate `k + 2` to three halves of itself. -/
theorem deltaInv_four_expand_coordinate (k : ℤ) (h : 2 ∣ k + 2) :
    deltaInv (4 * k) / 4 + 2 = 3 * (k + 2) / 2 := by
  rw [deltaInv_four_expand k h]
  omega

/-- **Target.**  Every orbit of `δ` is finite.  Paper proof (`uniform.md` §5): write the
multiples of `4` as `4k` and put `c = k + 2`; along an orbit the multiples of `4` alternate
`c ↦ (3/2) c` (while `2 ∣ c`) and `c ↦ (2/3) c` (while `3 ∣ c`), ending at fixed points of the
involution `ι₁`.  So the multiples of `4` in a cycle are `{u · 2ⁱ 3^(s−i) : 0 ≤ i ≤ s}`, with
`s = v₂ c + v₃ c` and `u` the `6`-free part of `c`: finitely many. -/
theorem delta_periodic (x : ℤ) : ∃ n : ℕ, 0 < n ∧ delta^[n] x = x := by
  sorry

end CollatzMoonshot.Amusical
