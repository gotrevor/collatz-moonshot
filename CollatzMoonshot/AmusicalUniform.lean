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

/-! ### The finite `2`-`3` lattice of `delta` -/

private theorem delta_three_steps (c : ℤ) (h3 : ¬ 3 ∣ c) :
    delta^[3] (4 * (c - 2)) = 4 * c - 7 := by
  change delta (delta (delta (4 * (c - 2)))) = 4 * c - 7
  have hc0 : c % 3 ≠ 0 := by
    simpa only [Int.dvd_iff_emod_eq_zero] using h3
  have hc : c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hc with hc | hc
  · have h1 : delta (4 * (c - 2)) = 4 * (c - 2) - 1 := by
      unfold delta
      split_ifs <;> omega
    have h2 : delta (4 * (c - 2) - 1) = 4 * (c - 2) - 2 := by
      unfold delta
      split_ifs <;> omega
    have h3 : delta (4 * (c - 2) - 2) = 4 * (c - 2) + 1 := by
      unfold delta
      split_ifs <;> omega
    rw [h1, h2, h3]
    ring
  · have h1 : delta (4 * (c - 2)) = 4 * (c - 2) + 3 := by
      unfold delta
      split_ifs <;> omega
    have h2 : delta (4 * (c - 2) + 3) = 4 * (c - 2) + 2 := by
      unfold delta
      split_ifs <;> omega
    have h3 : delta (4 * (c - 2) + 2) = 4 * (c - 2) + 1 := by
      unfold delta
      split_ifs <;> omega
    rw [h1, h2, h3]
    ring

private theorem delta_four_mul_sub_seven (c : ℤ) :
    delta (4 * c - 7) = 6 * c - 7 := by
  unfold delta
  split_ifs <;> omega

private theorem delta_two_mul_sub_seven (c : ℤ) (hc : Odd c) :
    delta (2 * c - 7) = 2 * c - 8 := by
  rcases hc with ⟨d, rfl⟩
  unfold delta
  split_ifs <;> omega

private theorem delta_six_mul_sub_eight (c : ℤ) :
    delta (6 * c - 8) = 4 * c - 8 := by
  unfold delta
  split_ifs <;> omega

private theorem delta_expand_run (u : ℤ) (n : ℕ) :
    delta^[n] ((2 : ℤ) ^ (n + 1) * u - 7) = 2 * (3 : ℤ) ^ n * u - 7 := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hstep :
          delta ((2 : ℤ) ^ (n + 1 + 1) * u - 7) =
            2 ^ (n + 1) * (3 * u) - 7 := by
        convert delta_four_mul_sub_seven (2 ^ n * u) using 1 <;>
          rw [pow_succ] <;>
          ring
      rw [hstep, ih]
      rw [pow_succ]
      ring

private theorem delta_contract_step (c : ℤ) :
    delta (4 * (3 * c - 2)) = 4 * (2 * c - 2) := by
  unfold delta
  split_ifs <;> omega

private theorem delta_contract_run (u : ℤ) (a b j : ℕ) :
    delta^[j] (4 * (u * 2 ^ a * 3 ^ (b + j) - 2)) =
      4 * (u * 2 ^ (a + j) * 3 ^ b - 2) := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      have hstep :
          delta (4 * (u * 2 ^ a * 3 ^ (b + (j + 1)) - 2)) =
            4 * (u * 2 ^ (a + 1) * 3 ^ (b + j) - 2) := by
        have heq :
            u * 2 ^ a * 3 ^ (b + (j + 1)) = 3 * (u * 2 ^ a * 3 ^ (b + j)) := by
          rw [show b + (j + 1) = (b + j) + 1 by omega, pow_succ]
          ring
        rw [heq, delta_contract_step]
        rw [pow_succ]
        ring_nf
      rw [hstep, ih]
      rw [show a + 1 + j = a + (j + 1) by omega]

private theorem not_three_dvd_mul_two_pow (u : ℤ) (a : ℕ) (hu : ¬ 3 ∣ u) :
    ¬ 3 ∣ u * 2 ^ a := by
  apply (show Prime (3 : ℤ) by norm_num).not_dvd_mul hu
  intro h
  have : (3 : ℤ) ∣ 2 := (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow h
  norm_num at this

private theorem delta_expand_between_multiples (u : ℤ) (a : ℕ) (hu2 : Odd u)
    (hu3 : ¬ 3 ∣ u) :
    delta^[a + 6] (4 * (u * 2 ^ a - 2)) = 4 * (u * 3 ^ a - 2) := by
  have h3 := delta_three_steps (u * 2 ^ a) (not_three_dvd_mul_two_pow u a hu3)
  have hrun := delta_expand_run u (a + 1)
  have hodd : Odd ((3 : ℤ) ^ (a + 1) * u) := by
    exact Int.odd_mul.mpr ⟨(show Odd (3 : ℤ) by norm_num).pow, hu2⟩
  have hlast := delta_two_mul_sub_seven ((3 : ℤ) ^ (a + 1) * u) hodd
  have hend := delta_six_mul_sub_eight ((3 : ℤ) ^ a * u)
  rw [show a + 6 = 2 + (a + 1) + 3 by omega, Function.iterate_add_apply,
    Function.iterate_add_apply, h3]
  rw [show 4 * (u * 2 ^ a) - 7 = (2 : ℤ) ^ (a + 2) * u - 7 by
    rw [pow_add]
    norm_num
    ring_nf]
  rw [show a + 2 = (a + 1) + 1 by omega, hrun]
  simp only [show 2 = Nat.succ (Nat.succ 0) by omega, Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  rw [show 2 * 3 ^ (a + 1) * u - 7 = 2 * (3 ^ (a + 1) * u) - 7 by ring_nf,
    hlast]
  rw [show 2 * (3 ^ (a + 1) * u) - 8 = 6 * (3 ^ a * u) - 8 by
    rw [pow_succ]
    ring]
  rw [hend]
  ring

private theorem int_exists_two_factorization (c : ℤ) (hc : c ≠ 0) :
    ∃ a : ℕ, ∃ u : ℤ, Odd u ∧ c = u * 2 ^ a := by
  have hcabs : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  obtain ⟨a, n, hnodd, habs⟩ := Nat.exists_eq_two_pow_mul_odd hcabs
  refine ⟨a, c.sign * n, ?_, ?_⟩
  · exact Int.odd_mul.mpr ⟨Int.odd_sign_iff.mpr hc, by exact_mod_cast hnodd⟩
  · calc
      c = c.sign * (c.natAbs : ℤ) := (Int.sign_mul_natAbs c).symm
      _ = (c.sign * n) * 2 ^ a := by
        rw [habs]
        push_cast
        ring

private theorem int_exists_two_three_factorization (c : ℤ) (hc : c ≠ 0) :
    ∃ a b : ℕ, ∃ u : ℤ, Odd u ∧ ¬ 3 ∣ u ∧ c = u * 2 ^ a * 3 ^ b := by
  have hcabs : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  obtain ⟨a, m, hmodd, habs⟩ := Nat.exists_eq_two_pow_mul_odd hcabs
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at habs
    exact hc habs
  obtain ⟨b, n, h3n, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hnodd : Odd n := by
    rw [hm, Nat.odd_mul] at hmodd
    exact hmodd.2
  let u : ℤ := c.sign * n
  have huodd : Odd u := by
    exact Int.odd_mul.mpr ⟨Int.odd_sign_iff.mpr hc, by exact_mod_cast hnodd⟩
  have hsignunit : IsUnit c.sign :=
    Int.isUnit_iff_natAbs_eq.mpr (Int.natAbs_sign_of_ne_zero hc)
  have h3sign : ¬ (3 : ℤ) ∣ c.sign := by
    intro h
    have : IsUnit (3 : ℤ) := isUnit_of_dvd_unit h hsignunit
    norm_num [Int.isUnit_iff] at this
  have h3n' : ¬ (3 : ℤ) ∣ (n : ℤ) := by exact_mod_cast h3n
  have h3u : ¬ (3 : ℤ) ∣ u := by
    exact (show Prime (3 : ℤ) by norm_num).not_dvd_mul h3sign h3n'
  refine ⟨a, b, u, huodd, h3u, ?_⟩
  calc
    c = c.sign * (c.natAbs : ℤ) := (Int.sign_mul_natAbs c).symm
    _ = u * 2 ^ a * 3 ^ b := by
      rw [habs, hm]
      push_cast
      dsimp [u]
      ring

/-- Every multiple of four has the explicit period `2 * (v₂(c) + v₃(c)) + 6`, except
the fixed point corresponding to `c = 0`. -/
theorem delta_four_coordinate_periodic (c : ℤ) :
    ∃ n : ℕ, 0 < n ∧ delta^[n] (4 * (c - 2)) = 4 * (c - 2) := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨1, by omega, ?_⟩
    norm_num [delta]
  obtain ⟨a, b, u, hu2, hu3, hfac⟩ := int_exists_two_three_factorization c hc
  have hfirst :
      delta^[b] (4 * (c - 2)) = 4 * (u * 2 ^ (a + b) - 2) := by
    simpa [hfac] using delta_contract_run u a 0 b
  have hmiddle := delta_expand_between_multiples u (a + b) hu2 hu3
  have hlast :
      delta^[a] (4 * (u * 3 ^ (a + b) - 2)) = 4 * (c - 2) := by
    simpa [hfac, Nat.add_comm] using delta_contract_run u 0 b a
  refine ⟨a + (a + b + 6) + b, by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hfirst, hmiddle, hlast]

private theorem delta_one_class_run (u : ℤ) (q : ℕ) (hu : Odd u) :
    delta^[q + 3] ((2 : ℤ) ^ (q + 2) * u - 7) = 4 * (3 ^ q * u - 2) := by
  have hrun := delta_expand_run u (q + 1)
  have hodd : Odd ((3 : ℤ) ^ (q + 1) * u) := by
    exact Int.odd_mul.mpr ⟨(show Odd (3 : ℤ) by norm_num).pow, hu⟩
  have hlast := delta_two_mul_sub_seven ((3 : ℤ) ^ (q + 1) * u) hodd
  have hend := delta_six_mul_sub_eight ((3 : ℤ) ^ q * u)
  rw [show q + 3 = 2 + (q + 1) by omega, Function.iterate_add_apply]
  rw [show q + 2 = (q + 1) + 1 by omega, hrun]
  simp only [show 2 = Nat.succ (Nat.succ 0) by omega, Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  rw [show 2 * 3 ^ (q + 1) * u - 7 = 2 * (3 ^ (q + 1) * u) - 7 by ring_nf,
    hlast]
  rw [show 2 * (3 ^ (q + 1) * u) - 8 = 6 * (3 ^ q * u) - 8 by
    rw [pow_succ]
    ring]
  rw [hend]
  ring

private theorem delta_reaches_of_mod_four_one (x : ℤ) (hx : x % 4 = 1) :
    ∃ m : ℕ, ∃ k : ℤ, delta^[m] x = 4 * k ∨ delta^[m] x = -7 := by
  rcases eq_or_ne x (-7) with rfl | hx7
  · exact ⟨0, 0, Or.inr (by simp)⟩
  let c := (x + 7) / 4
  have hxc : x = 4 * c - 7 := by
    dsimp [c]
    omega
  have hc : c ≠ 0 := by
    intro hc
    rw [hc] at hxc
    omega
  obtain ⟨q, u, hu, hfac⟩ := int_exists_two_factorization c hc
  refine ⟨q + 3, 3 ^ q * u - 2, Or.inl ?_⟩
  rw [hxc, hfac]
  convert delta_one_class_run u q hu using 1 <;>
    rw [pow_add] <;>
    norm_num <;>
    ring

private theorem delta_reaches_of_mod_four_two (x : ℤ) (hx : x % 4 = 2) :
    ∃ m : ℕ, ∃ k : ℤ, delta^[m] x = 4 * k ∨ delta^[m] x = -7 := by
  by_cases h0 : x % 6 = 0
  · have hdx : delta x = x + 3 := by
      unfold delta
      split_ifs <;> omega
    have hx1 : delta x % 4 = 1 := by rw [hdx]; omega
    obtain ⟨m, k, h⟩ := delta_reaches_of_mod_four_one (delta x) hx1
    exact ⟨m + 1, k, by simpa only [Function.iterate_succ_apply] using h⟩
  by_cases h2 : x % 6 = 2
  · have hdx : delta x = x - 1 := by
      unfold delta
      split_ifs <;> omega
    have hx1 : delta x % 4 = 1 := by rw [hdx]; omega
    obtain ⟨m, k, h⟩ := delta_reaches_of_mod_four_one (delta x) hx1
    exact ⟨m + 1, k, by simpa only [Function.iterate_succ_apply] using h⟩
  · have h4 : x % 6 = 4 := by omega
    refine ⟨1, x / 6, Or.inl ?_⟩
    simp only [Function.iterate_one]
    unfold delta
    split_ifs <;> omega

private theorem delta_reaches_of_mod_four_three (x : ℤ) (hx : x % 4 = 3) :
    ∃ m : ℕ, ∃ k : ℤ, delta^[m] x = 4 * k ∨ delta^[m] x = -7 := by
  have hdx : delta x = x - 1 := by
    unfold delta
    split_ifs <;> omega
  have hx2 : delta x % 4 = 2 := by rw [hdx]; omega
  obtain ⟨m, k, h⟩ := delta_reaches_of_mod_four_two (delta x) hx2
  exact ⟨m + 1, k, by simpa only [Function.iterate_succ_apply] using h⟩

/-- Every point either reaches a multiple of four or is the exceptional fixed point `-7`. -/
theorem delta_reaches_multiple_four_or_neg_seven (x : ℤ) :
    ∃ m : ℕ, ∃ k : ℤ, delta^[m] x = 4 * k ∨ delta^[m] x = -7 := by
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases hx with hx | hx | hx | hx
  · exact ⟨0, x / 4, Or.inl (by simp; omega)⟩
  · exact delta_reaches_of_mod_four_one x hx
  · exact delta_reaches_of_mod_four_two x hx
  · exact delta_reaches_of_mod_four_three x hx

private theorem delta_periodic_of_iterate_periodic (x : ℤ) (m : ℕ)
    (h : ∃ n : ℕ, 0 < n ∧ delta^[n] (delta^[m] x) = delta^[m] x) :
    ∃ n : ℕ, 0 < n ∧ delta^[n] x = x := by
  obtain ⟨n, hn, hper⟩ := h
  refine ⟨n, hn, ?_⟩
  have hinj : Function.Injective delta := by
    intro y z hyz
    simpa only [deltaInv_delta] using congrArg deltaInv hyz
  apply Function.Injective.iterate hinj m
  calc
    delta^[m] (delta^[n] x) = delta^[n] (delta^[m] x) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
    _ = delta^[m] x := hper

private theorem delta_neg_seven : delta (-7) = -7 := by
  norm_num [delta]

/-- An injective self-map is periodic at a point as soon as its forward orbit is finite. -/
theorem periodic_of_finite_forwardOrbit {α : Type*} (f : α → α) (hf : Function.Injective f)
    (x : α) (hfin : Set.Finite (Set.range fun n : ℕ => f^[n] x)) :
    ∃ n : ℕ, 0 < n ∧ f^[n] x = x := by
  letI : Fintype (Set.range fun n : ℕ => f^[n] x) := hfin.fintype
  let orbit (n : ℕ) : Set.range fun n : ℕ => f^[n] x :=
    ⟨f^[n] x, Set.mem_range_self n⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite orbit
  have heq' : f^[i] x = f^[j] x := Subtype.ext_iff.mp heq
  have hiter_inj : ∀ n : ℕ, Function.Injective (f^[n]) := by
    intro n
    exact Function.Injective.iterate hf n
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine ⟨j - i, by omega, ?_⟩
    apply hiter_inj i
    rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
    exact heq'.symm
  · refine ⟨i - j, by omega, ?_⟩
    apply hiter_inj j
    rw [← Function.iterate_add_apply, show j + (i - j) = i by omega]
    exact heq'

/-- **Target.**  Every orbit of `δ` is finite.  Paper proof (`uniform.md` §5): write the
multiples of `4` as `4k` and put `c = k + 2`; along an orbit the multiples of `4` alternate
`c ↦ (3/2) c` (while `2 ∣ c`) and `c ↦ (2/3) c` (while `3 ∣ c`), ending at fixed points of the
involution `ι₁`.  So the multiples of `4` in a cycle are `{u · 2ⁱ 3^(s−i) : 0 ≤ i ≤ s}`, with
`s = v₂ c + v₃ c` and `u` the `6`-free part of `c`: finitely many. -/
theorem delta_periodic (x : ℤ) : ∃ n : ℕ, 0 < n ∧ delta^[n] x = x := by
  obtain ⟨m, k, hmul | hfix⟩ := delta_reaches_multiple_four_or_neg_seven x
  · apply delta_periodic_of_iterate_periodic x m
    rw [hmul]
    simpa using delta_four_coordinate_periodic (k + 2)
  · apply delta_periodic_of_iterate_periodic x m
    rw [hfix]
    exact ⟨1, by omega, by simpa only [Function.iterate_one] using delta_neg_seven⟩

end CollatzMoonshot.Amusical
