/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Literature.AmusicalCycles
import CollatzMoonshot.AmusicalEscape
import CollatzMoonshot.AmusicalCycleBound.Step
import CollatzMoonshot.AmusicalCycleBound.MinBound
import CollatzMoonshot.AmusicalCycleBound.Orbit
import CollatzMoonshot.AmusicalCycleBound.Search

/-!
# No new cycles of length at most 31866

Atkin (1966) showed by computer that `U` has no cycles of period `< 200` beyond the known ones
(`Literature.AtkinNoShortCycles`).  The 2026-10-13 "cycles" agent raised this to `31866`.  The
method replaces the "everything small converges" check, which `U` lacks.

**Theorem A★ (`amusical_cycle_min_bound`).**  A cycle's *minimum* is bounded polynomially by
its length, even though its elements are not.  Multiplying `x_{i+1} = (3xᵢ + dᵢ) / 2^{bᵢ}` around a
cycle of length `p` with `e` halvings and `k = e − p` odd steps gives
`2^e ∏(3xᵢ) = 3^p ∏(3xᵢ + dᵢ)`, with each odd ratio within `1/(3m)` of `1`.  So
`3^p (3m−1)^k ≤ 2^e (3m)^k ≤ 3^p (3m+1)^k`, and
`m ≤ M(p, e) = ⌊(k · max(2^e, 3^p) + D) / (3D)⌋` with `D = |2^e − 3^p|` (`cycleMinBound`).  The
maximum over `p ≤ 31866` is `167195612`, attained at `(p, e) = (31202, 49454)`.

**Orbit-minimum search.**  Every `n ≤ 167195612` outside `{1, 2, 4, 44}` either dips below
itself within `15933` steps forward or backward, or has no forward return and no meet
`Uᵃ n = V^{15933} n` (`CycleMinSearch`).  A cycle minimum of period `P ≤ 2 · 15933` does neither
(`noNewCycles_of_search`).  So no new cycle has length `≤ 31866`
(`amusical_noNewCycles_31866`, conditional on the search).

The search runs outside the kernel, as two independent computations:
* the agent's lockstep `U`/`V` meet-in-the-middle search (`scripts/amusical/cycles/cyclemin.c`):
  `158872552` dips, `8323056` survivors, `0` cycles;
* my forward-only GMP search to `2H` steps with a different algorithm
  (`scripts/amusical/cycles/fwd_ren.c`): only `1, 2, 4, 44` return, `1.12·10¹²` steps.  Teeth:
  it finds `1, 2, 4, 44` with period cap `12` and misses `44` with cap `11`.
The bound `167195612` was re-derived independently (`scripts/amusical/cycles/x0_ren.py`).

Also (agent, paper and computer, not in Lean): every new cycle has at least `33` local minima.
That uses Rhin's 1987 linear-form bound, which `Literature` does not yet carry.  The minimum of
a cycle with `m ≥ 2` is `≡ 2, 4 (mod 6)` (`cycle_min_mod_six`).

Paper proofs: agent report `cycles.md`, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §18.

In the kernel, with no search assumed: the same reduction with `X = 4964` and `H = 100` proves
Atkin's bound (`amusical_noNewCycles_199`, `atkinNoShortCycles`).
-/

namespace CollatzMoonshot.Amusical

/-- **Proved (Theorem A★).**  For a cycle of length `p` through `x` whose members are all at
least `m ≥ 1`, with `e` total halvings and `k = e − p` odd steps:
`3^p (3m−1)^k ≤ 2^e (3m)^k ≤ 3^p (3m+1)^k`.  Paper proof in the module docstring: multiply the
step identities `2^{bᵢ} x_{i+1} = 3xᵢ + dᵢ` over the cycle, cancel `∏ xᵢ`, and bound each odd
ratio `(3xᵢ + dᵢ) / (3xᵢ)` between `(3m−1)/(3m)` and `(3m+1)/(3m)`. -/
theorem amusical_cycle_min_bound (x m : ℤ) (p : ℕ) (hp : 0 < p) (hcyc : amusical^[p] x = x)
    (hm : 1 ≤ m) (hmin : ∀ j < p, m ≤ amusical^[j] x) :
    let e := ∑ j ∈ Finset.range p, stepBits (amusical^[j] x)
    let k := e - p
    3 ^ p * (3 * m - 1) ^ k ≤ 2 ^ e * (3 * m) ^ k ∧
      2 ^ e * (3 * m) ^ k ≤ 3 ^ p * (3 * m + 1) ^ k := by
  intro e k
  set a : ℕ → ℤ := fun j => amusical^[j] x with ha
  set S := (Finset.range p).filter fun j => ¬ 2 ∣ a j with hS
  have hk : k = S.card := by
    have he : e = p + S.card := sum_stepBits_eq_add_filter_card x p
    show e - p = _; omega
  have hkp : S.card ≤ p := by
    calc S.card ≤ (Finset.range p).card := Finset.card_filter_le _ _
      _ = p := Finset.card_range p
  have hpos : ∀ j ∈ Finset.range p, 0 < a j := fun j hj =>
    lt_of_lt_of_le (by omega : (0 : ℤ) < m) (hmin j (Finset.mem_range.mp hj))
  have hx0 : x ≠ 0 := (show (0 : ℤ) < x from hpos 0 (Finset.mem_range.mpr hp)).ne'
  have hid := amusical_cycle_product_identity hx0 hcyc
  change 2 ^ e * ∏ j ∈ Finset.range p, a j =
    ∏ j ∈ Finset.range p, (3 * a j + stepDefect (a j)) at hid
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range p) (fun j => ¬ 2 ∣ a j),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.range p) (fun j => ¬ 2 ∣ a j)] at hid
  set T := (Finset.range p).filter fun j => ¬ ¬ 2 ∣ a j with hT
  have heven : ∏ j ∈ T, (3 * a j + stepDefect (a j)) = 3 ^ T.card * ∏ j ∈ T, a j := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have h2 : a j % 2 = 0 := by
      simp only [hT, Finset.mem_filter, not_not] at hj; exact Int.emod_eq_zero_of_dvd hj.2
    rw [stepDefect_eq_zero_of_even h2]; ring
  have hTcard : T.card = p - S.card := by
    have hsum : S.card + T.card = p := by
      convert Finset.card_filter_add_card_filter_not (s := Finset.range p) (fun j => ¬ 2 ∣ a j)
      exact (Finset.card_range p).symm
    omega
  have hTpos : 0 < ∏ j ∈ T, a j :=
    Finset.prod_pos fun j hj => hpos j (Finset.mem_filter.mp hj).1
  rw [heven] at hid
  set A := ∏ j ∈ S, a j
  set B := ∏ j ∈ S, (3 * a j + stepDefect (a j))
  have hstar : 2 ^ e * A = 3 ^ (p - S.card) * B := by
    rw [← hTcard]; apply mul_right_cancel₀ hTpos.ne'; linear_combination hid
  have hApos : 0 < A := Finset.prod_pos fun j hj => hpos j (Finset.mem_filter.mp hj).1
  have h3p : (3 : ℤ) ^ p = 3 ^ (p - S.card) * 3 ^ S.card := by
    rw [← pow_add]; congr 1; omega
  have hSmem : ∀ j ∈ S, m ≤ a j ∧ -1 ≤ stepDefect (a j) ∧ stepDefect (a j) ≤ 1 := fun j hj =>
    ⟨hmin j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1), stepDefect_mem (a j)⟩
  have hlo : (3 * m - 1) ^ S.card * (3 ^ S.card * A) ≤ (3 * m) ^ S.card * B := by
    calc (3 * m - 1) ^ S.card * (3 ^ S.card * A) = ∏ j ∈ S, ((3 * m - 1) * (3 * a j)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_const]
      _ ≤ ∏ j ∈ S, (3 * m * (3 * a j + stepDefect (a j))) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · obtain ⟨h1, -, -⟩ := hSmem j hj; nlinarith
          · obtain ⟨h1, h2, -⟩ := hSmem j hj; nlinarith
      _ = (3 * m) ^ S.card * B := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hhi : (3 * m) ^ S.card * B ≤ (3 * m + 1) ^ S.card * (3 ^ S.card * A) := by
    calc (3 * m) ^ S.card * B = ∏ j ∈ S, (3 * m * (3 * a j + stepDefect (a j))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ ∏ j ∈ S, ((3 * m + 1) * (3 * a j)) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · obtain ⟨h1, h2, -⟩ := hSmem j hj; nlinarith
          · obtain ⟨h1, -, h3⟩ := hSmem j hj; nlinarith
      _ = (3 * m + 1) ^ S.card * (3 ^ S.card * A) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_const]
  rw [hk]
  have h3pk : (0 : ℤ) ≤ 3 ^ (p - S.card) := by positivity
  constructor
  · refine le_of_mul_le_mul_right ?_ hApos
    calc 3 ^ p * (3 * m - 1) ^ S.card * A
        = 3 ^ (p - S.card) * ((3 * m - 1) ^ S.card * (3 ^ S.card * A)) := by rw [h3p]; ring
      _ ≤ 3 ^ (p - S.card) * ((3 * m) ^ S.card * B) := mul_le_mul_of_nonneg_left hlo h3pk
      _ = 2 ^ e * (3 * m) ^ S.card * A := by linear_combination (-(3 * m) ^ S.card) * hstar
  · refine le_of_mul_le_mul_right ?_ hApos
    calc 2 ^ e * (3 * m) ^ S.card * A
        = 3 ^ (p - S.card) * ((3 * m) ^ S.card * B) := by
          linear_combination (3 * m) ^ S.card * hstar
      _ ≤ 3 ^ (p - S.card) * ((3 * m + 1) ^ S.card * (3 ^ S.card * A)) :=
          mul_le_mul_of_nonneg_left hhi h3pk
      _ = 3 ^ p * (3 * m + 1) ^ S.card * A := by rw [h3p]; ring

/-- The Theorem A bound `M(p, e) = ⌊(k · max(2^e, 3^p) + D) / (3D)⌋`, `D = |2^e − 3^p|`,
`k = e − p`, on the minimum of a cycle of length `p` with `e` halvings. -/
def cycleMinBound (p e : ℕ) : ℕ :=
  ((e - p) * max (2 ^ e) (3 ^ p) + Int.natAbs ((2 : ℤ) ^ e - 3 ^ p)) /
    (3 * Int.natAbs ((2 : ℤ) ^ e - 3 ^ p))

/-- `X` bounds `M(p, e)` for every length `p ≤ P` and every halving count `p < e ≤ 2p`. -/
def CycleMinBoundHolds (P X : ℕ) : Prop :=
  ∀ p e : ℕ, 1 ≤ p → p ≤ P → p < e → e ≤ 2 * p → cycleMinBound p e ≤ X

/-- The search certificate: every `n ∈ [1, X]` outside `{1, 2, 4, 44}` dips below itself within
`H` steps forward or backward, or has no forward return within `H` steps and no meet
`Uᵃ n = V^H n` with `1 ≤ a ≤ H`. -/
def CycleMinSearch (X H : ℕ) : Prop :=
  ∀ n : ℤ, 1 ≤ n → n ≤ X → n ∉ ({1, 2, 4, 44} : Finset ℤ) →
    (∃ j, 1 ≤ j ∧ j ≤ H ∧ (amusical^[j] n < n ∨ amusicalInv^[j] n < n)) ∨
    ((∀ j, 1 ≤ j → j ≤ H → amusical^[j] n ≠ n) ∧
      ∀ a, 1 ≤ a → a ≤ H → amusical^[a] n ≠ amusicalInv^[H] n)

/-- Every periodic point of period at most `P` lies on a known cycle (up to sign). -/
def AmusicalNoNewCyclesUpTo (P : ℕ) : Prop :=
  ∀ (y : ℤ) (p : ℕ), 1 ≤ p → p ≤ P → amusical^[p] y = y → |y| ∈ knownCycleMembers

/-- **Proved (orbit-minimum lemma).**  A cycle minimum `n` of period `P ≤ 2H` stays strictly above
`n` for `0 < j < P` in both directions, and either `P ≤ H` or `U^{P−H} n = V^H n`. -/
theorem cycle_min_meet (n : ℤ) (H P : ℕ) (hP : 0 < P) (hPH : P ≤ 2 * H)
    (hcyc : amusical^[P] n = n) (hper : ∀ j, 0 < j → j < P → amusical^[j] n ≠ n)
    (hmin : ∀ j < P, n ≤ amusical^[j] n) :
    (∀ j, 0 < j → j < P → n < amusical^[j] n ∧ n < amusicalInv^[j] n) ∧
      (P ≤ H ∨ amusical^[P - H] n = amusicalInv^[H] n) := by
  have hback (j : ℕ) (hj : j ≤ P) : amusicalInv^[j] n = amusical^[P - j] n := by
    rw [amusicalInv_iterate_eq_perm_pow, amusical_iterate_eq_perm_pow]
    have hcyc' : (amusicalPerm ^ (P : ℤ)) n = n := by
      simpa [amusical_iterate_eq_perm_pow] using hcyc
    calc
      (amusicalPerm ^ (-(j : ℤ))) n =
          (amusicalPerm ^ (-(j : ℤ))) ((amusicalPerm ^ (P : ℤ)) n) := by rw [hcyc']
      _ = (amusicalPerm ^ ((P : ℤ) - j)) n := by
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        congr 2
        omega
      _ = (amusicalPerm ^ ((P - j : ℕ) : ℤ)) n := by
        congr 2
        omega
  constructor
  · intro j hj0 hjP
    have hfwd : n < amusical^[j] n :=
      lt_of_le_of_ne (hmin j hjP) (Ne.symm (hper j hj0 hjP))
    have hsub0 : 0 < P - j := by omega
    have hsubP : P - j < P := by omega
    have hbwd : n < amusicalInv^[j] n := by
      rw [hback j hjP.le]
      exact lt_of_le_of_ne (hmin (P - j) hsubP)
        (Ne.symm (hper (P - j) hsub0 hsubP))
    exact ⟨hfwd, hbwd⟩
  · by_cases hPH' : P ≤ H
    · exact Or.inl hPH'
    · right
      rw [hback H (by omega)]

/-- **Proved (the reduction).**  A bound on cycle minima plus a clean search gives no new cycles.
Paper proof: reduce to `y > 0` by `amusical_neg`; let `n` be the minimum of the cycle and `P` its
minimal period.  Theorem A★ with `cycleMinBound` gives `n ≤ X`.  If `n ∈ {1, 2, 4, 44}`, the cycle
is known.  Otherwise the search contradicts `cycle_min_meet`. -/
theorem noNewCycles_of_search {P X H : ℕ} (hPH : P ≤ 2 * H) (hX : CycleMinBoundHolds P X)
    (hS : CycleMinSearch X H) : AmusicalNoNewCyclesUpTo P := by
  -- The positive case; negatives follow by `amusical_neg`.
  have key : ∀ y : ℤ, 0 < y → ∀ p : ℕ, 1 ≤ p → p ≤ P → amusical^[p] y = y →
      y ∈ knownCycleMembers := by
    intro y hy0 p hp hpP hy
    obtain ⟨n, ⟨jy, hjy⟩, ⟨jn, hjn⟩, hnp, hmin⟩ := exists_orbit_min (by omega : 0 < p) hy
    have hn0 : 0 < n := hjn ▸ amusical_iterate_pos hy0 jn
    have hnper : Function.IsPeriodicPt amusical p n := hnp
    set Q := Function.minimalPeriod amusical n with hQ
    have hQ0 : 0 < Q := hnper.minimalPeriod_pos (by omega)
    have hQp : Q ≤ p := hnper.minimalPeriod_le (by omega)
    have hQcyc : amusical^[Q] n = n := Function.isPeriodicPt_minimalPeriod amusical n
    have hQper : ∀ j, 0 < j → j < Q → amusical^[j] n ≠ n := fun j hj0 hjQ =>
      Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hjQ
    have hQH : Q ≤ 2 * H := by omega
    -- Theorem A★ bounds the minimum.
    have hA := amusical_cycle_min_bound n n Q hQ0 hQcyc (by omega) (fun j _ => hmin j)
    set e := ∑ j ∈ Finset.range Q, stepBits (amusical^[j] n) with he
    have he2 : e ≤ 2 * Q := sum_stepBits_le n Q
    have heQ : Q ≤ e := by rw [he, sum_stepBits_eq_add_filter_card]; omega
    have hnat : n = ((n.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hn0.le).symm
    rw [hnat] at hA
    have hQe : Q < e := by
      by_contra hcon
      have hEq : e = Q := by omega
      have h1 := hA.1
      rw [hEq, Nat.sub_self, pow_zero, pow_zero, mul_one, mul_one] at h1
      have : (2 : ℤ) ^ Q < 3 ^ Q := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
      omega
    have hle : n.toNat ≤ natMinBound Q e :=
      le_natMinBound (by omega) (by omega) hA.1 hA.2
    have hbound : cycleMinBound Q e ≤ X := hX Q e (by omega) (by omega) hQe he2
    unfold cycleMinBound at hbound
    rw [natAbs_two_pow_sub_three_pow] at hbound
    have hnX : n ≤ X := by
      have : n.toNat ≤ X := hle.trans hbound
      omega
    by_cases hknown : n ∈ ({1, 2, 4, 44} : Finset ℤ)
    · have hnk : n ∈ knownCycleMembers := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hknown
        rcases hknown with rfl | rfl | rfl | rfl <;> decide
      exact hjy ▸ amusical_iterate_mem_knownCycleMembers hnk jy
    · exfalso
      obtain ⟨hmeet1, hmeet2⟩ := cycle_min_meet n H Q hQ0 hQH hQcyc hQper (fun j _ => hmin j)
      have hinvper : Function.IsPeriodicPt amusicalInv Q n :=
        amusicalInv_iterate_of_cycle hQcyc
      have hinv : ∀ j, n ≤ amusicalInv^[j] n := by
        intro j
        rw [← hinvper.iterate_mod_apply]
        rcases Nat.eq_zero_or_pos (j % Q) with h0 | h0
        · rw [h0]; exact le_rfl
        · exact (hmeet1 _ h0 (Nat.mod_lt _ hQ0)).2.le
      rcases hS n (by omega) hnX hknown with ⟨j, -, -, hj | hj⟩ | ⟨hret, hmeet⟩
      · exact absurd (hmin j) (not_le.mpr hj)
      · exact absurd (hinv j) (not_le.mpr hj)
      · by_cases hQH' : Q ≤ H
        · exact hret Q hQ0 hQH' hQcyc
        · have hm2 := hmeet2.resolve_left hQH'
          exact hmeet (Q - H) (by omega) (by omega) hm2
  intro y p hp hpP hy
  rcases lt_trichotomy y 0 with hneg | rfl | hpos
  · have h' : amusical^[p] (-y) = -y := by rw [amusical_iterate_neg, hy]
    rw [abs_of_neg hneg]
    exact key (-y) (by omega) p hp hpP h'
  · decide
  · rw [abs_of_pos hpos]
    exact key y hpos p hp hpP hy

/-- **Proved (a kernel computation).**  `M(p, e) ≤ 167195612` for all `p ≤ 31866`.  Only the
`e` with `3^p / 2 < 2^e < 2 · 3^p` need computing: otherwise `D ≥ max / 2` and `M(p, e) ≤ k ≤ p`.
That leaves at most two `e` per `p`, about `6 · 10⁴` comparisons of ≤ 50000-bit numbers.
Checked by one `decide +kernel` call (`natMinBound_le_31866`; 9 s, 3.1 GB measured). -/
theorem cycleMinBound_31866 : CycleMinBoundHolds 31866 167195612 := by
  intro p e hp hpP hpe he
  unfold cycleMinBound
  rw [natAbs_two_pow_sub_three_pow]
  exact natMinBound_le_31866 p e hp hpP hpe he

/-- **Proved modulo the search: Theorem 1.**  If the orbit-minimum search over `[1, 167195612]`
with `H = 15933` is clean, there are no new cycles of length `≤ 31866`. -/
theorem amusical_noNewCycles_31866 (hS : CycleMinSearch 167195612 15933) :
    AmusicalNoNewCyclesUpTo 31866 :=
  noNewCycles_of_search (by norm_num) cycleMinBound_31866 hS

/-- **Proved: Atkin 1966 in the kernel.**  No new cycles of length `≤ 199`.  The bound
is `X = 4964` (`x0_ren.py 200`) and `H = 100`.  `CycleMinSearch 4964 100` is discharged by a fuelled
`Bool` checker (`searchCheck`, sound by `searchCheck_sound`) and one `decide +kernel` call that
also checks the bound (`cycleCheck_199`; 6.5 s of kernel time). -/
theorem amusical_noNewCycles_199 : AmusicalNoNewCyclesUpTo 199 := by
  refine noNewCycles_of_search (X := 4964) (H := 100) (by norm_num) ?_
    (searchCheck_sound searchCheck_4964)
  intro p e hp hpP hpe he
  unfold cycleMinBound
  rw [natAbs_two_pow_sub_three_pow]
  exact natMinBound_le_199 p e hp hpP hpe he

/-- **Proved: Atkin 1966 in the kernel.**  Every nonnegative periodic point of period `< 200` is
a known cycle member. -/
theorem atkinNoShortCycles : Literature.AtkinNoShortCycles := by
  intro n hn p hp hp200 hcyc
  have h := amusical_noNewCycles_199 n p hp (by omega) hcyc
  rwa [abs_of_nonneg hn] at h

/-- **Proved.**  The minimum `n ≥ 2` of a cycle is `≡ 2` or `4 (mod 6)`.  If `n` is odd then
`U n < n`; if `6 ∣ n` then `V n = 2n/3 < n`; both lie on the cycle. -/
theorem cycle_min_mod_six (n : ℤ) (P : ℕ) (hP : 0 < P) (hn : 2 ≤ n)
    (hcyc : amusical^[P] n = n) (hmin : ∀ j < P, n ≤ amusical^[j] n) :
    n % 6 = 2 ∨ n % 6 = 4 := by
  have hfwd : n ≤ amusical n := by
    by_cases h : P = 1
    · subst P
      simpa using hcyc.symm.le
    · simpa using hmin 1 (by omega)
  have hback : amusicalInv n = amusical^[P - 1] n := by
    change amusicalInv^[1] n = amusical^[P - 1] n
    rw [amusicalInv_iterate_eq_perm_pow, amusical_iterate_eq_perm_pow]
    have hcyc' : (amusicalPerm ^ (P : ℤ)) n = n := by
      simpa [amusical_iterate_eq_perm_pow] using hcyc
    calc
      (amusicalPerm ^ (-1 : ℤ)) n =
          (amusicalPerm ^ (-1 : ℤ)) ((amusicalPerm ^ (P : ℤ)) n) := by rw [hcyc']
      _ = (amusicalPerm ^ ((P : ℤ) - 1)) n := by
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        congr 2
      _ = (amusicalPerm ^ ((P - 1 : ℕ) : ℤ)) n := by
        congr 2
        omega
  have hbwd : n ≤ amusicalInv n := by
    rw [hback]
    exact hmin (P - 1) (by omega)
  have hrange : 0 ≤ n % 6 ∧ n % 6 < 6 :=
    ⟨Int.emod_nonneg n (by omega), Int.emod_lt_of_pos n (by omega)⟩
  rcases hrange with ⟨hrange0, hrange6⟩
  interval_cases hmod : n % 6
  · have h3 : n % 3 = 0 := by omega
    unfold amusicalInv at hbwd
    simp [h3] at hbwd
    omega
  · have h2 : n % 2 ≠ 0 := by omega
    unfold amusical at hfwd
    simp [h2] at hfwd
    split at hfwd <;> omega
  · exact Or.inl rfl
  · have h2 : n % 2 ≠ 0 := by omega
    unfold amusical at hfwd
    simp [h2] at hfwd
    split at hfwd <;> omega
  · exact Or.inr rfl
  · have h2 : n % 2 ≠ 0 := by omega
    unfold amusical at hfwd
    simp [h2] at hfwd
    split at hfwd <;> omega

end CollatzMoonshot.Amusical
