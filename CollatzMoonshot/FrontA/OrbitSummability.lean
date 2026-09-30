/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.FrontA.OrbitPacking

/-!
# Summability of reciprocals along a divergent orbit

Second step of `RESEARCH-2026-09-22-packing-shadow.md`.  The packing bound of
`OrbitPacking.lean` is summed over dyadic shells to give a *uniform* bound on
`∑ 1/x` over any finite set of distinct values of an iterate-separated set, and
hence along a hypothetical divergent orbit.

Shells are taken in steps of five (`[2^(5t), 2^(5t+5))`), because `3·(5t+5)/5`
is exactly `3t+3`: the whole shell sits inside the single aligned block
`[0, 2^(5t+5))`, so no union of blocks is needed, and the resulting bound is
geometric in `t` with rational ratios `27/32` and `243/256`.
-/

namespace CollatzMoonshot.FrontA.OrbitPacking

open CollatzMoonshot CollatzMoonshot.FrontB

/-! ## Divergent orbits are iterate-separated -/

/-- The value set of the accelerated orbit of `n`. -/
def orbitSet (n : ℕ) : Set ℕ := {x | ∃ i, x = tstep^[i] n}

/-- An accelerated-orbit repeat rules out divergence. -/
theorem not_diverges_of_tstep_repeat {n i j : ℕ} (hn : 1 ≤ n) (hij : i < j)
    (h : tstep^[i] n = tstep^[j] n) : ¬ Diverges n := by
  have hx1 : 1 ≤ tstep^[i] n := tstep_iterate_pos hn i
  have hrep : tstep^[j - i] (tstep^[i] n) = tstep^[i] n := by
    rw [← Function.iterate_add_apply, show j - i + i = j from by omega]
    exact h.symm
  obtain ⟨L, hL, hLmono⟩ := exists_step_count (j - i) (tstep^[i] n)
  have hL1 : 1 ≤ L := le_trans (by omega) (hLmono hx1)
  have hfix : step^[L] (tstep^[i] n) = tstep^[i] n := by rw [← hL, hrep]
  have hxnd : ¬ Diverges (tstep^[i] n) :=
    not_diverges_of_repeat (i := 0) (j := L) (by omega) (by simpa using hfix.symm)
  obtain ⟨K, hK, _⟩ := exists_step_count i n
  rw [hK] at hxnd
  exact fun hdiv => hxnd (diverges_iterate_iff.mpr hdiv)

/-- A divergent orbit never repeats a value: the time index is recoverable. -/
theorem tstep_time_injective {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) {i j : ℕ}
    (h : tstep^[i] n = tstep^[j] n) : i = j := by
  by_contra hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact not_diverges_of_tstep_repeat hn hlt h hd
  · exact not_diverges_of_tstep_repeat hn (by omega : j < i) h.symm hd

/-- **A divergent orbit is iterate-separated**, so the packing bound applies to it. -/
theorem iterateSeparated_orbitSet {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) :
    IterateSeparated (orbitSet n) := by
  intro m x hx y hy hxy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have h1 : tstep^[m + i] n = tstep^[m + j] n := by
    rw [Function.iterate_add_apply, Function.iterate_add_apply]
    exact hxy
  have := tstep_time_injective hn hd h1
  have hij : i = j := by omega
  rw [hij]

/-! ## The shell bound -/

/-- The packing bound for the aligned block `[0, 2^(5t+5))`. -/
def packNat (t : ℕ) : ℕ := (5 * t + 6) * 3 ^ (3 * t + 3) + 3 ^ (5 * t + 5) / 2 ^ (3 * t + 4)

variable {S : Set ℕ}

theorem shell_card_le (hS : IterateSeparated S) (t : ℕ) (B : Finset ℕ)
    (hBS : ∀ x ∈ B, x ∈ S) (hB : ∀ x ∈ B, x < 2 ^ (5 * t + 5)) : B.card ≤ packNat t := by
  have h := block_card_le hS (5 * t + 5) 0 B hBS (fun x hx => ⟨by simp, by simpa using hB x hx⟩)
  have hdiv : 3 * (5 * t + 5) / 5 = 3 * t + 3 := by omega
  rw [hdiv, show 5 * t + 5 + 1 = 5 * t + 6 from by omega,
    show 3 * t + 3 + 1 = 3 * t + 4 from by omega] at h
  exact h

/-- The real geometric envelope of the shell bound, divided by the shell floor `2^(5t)`. -/
noncomputable def packReal (t : ℕ) : ℝ :=
  27 * (5 * t + 6) * (27 / 32 : ℝ) ^ t + (243 / 16 : ℝ) * (243 / 256 : ℝ) ^ t

theorem packReal_nonneg (t : ℕ) : 0 ≤ packReal t := by
  unfold packReal
  positivity

theorem packNat_div_le (t : ℕ) : (packNat t : ℝ) / 2 ^ (5 * t) ≤ packReal t := by
  have hcast : (packNat t : ℝ)
      ≤ (5 * t + 6) * 3 ^ (3 * t + 3) + (3 : ℝ) ^ (5 * t + 5) / 2 ^ (3 * t + 4) := by
    have hd : (((3 ^ (5 * t + 5) / 2 ^ (3 * t + 4) : ℕ) : ℝ))
        ≤ (3 : ℝ) ^ (5 * t + 5) / 2 ^ (3 * t + 4) := by
      refine le_trans (Nat.cast_div_le (α := ℝ)) (le_of_eq ?_)
      push_cast
      ring
    unfold packNat
    push_cast
    linarith [hd]
  have hpos : (0 : ℝ) < 2 ^ (5 * t) := by positivity
  rw [div_le_iff₀ hpos]
  have e1 : (3 : ℝ) ^ (3 * t + 3) = 27 * (27 : ℝ) ^ t := by
    rw [pow_add, pow_mul]; norm_num [mul_comm]
  have e2 : (3 : ℝ) ^ (5 * t + 5) = 243 * (243 : ℝ) ^ t := by
    rw [pow_add, pow_mul]; norm_num [mul_comm]
  have e3 : (2 : ℝ) ^ (3 * t + 4) = 16 * (8 : ℝ) ^ t := by
    rw [pow_add, pow_mul]; norm_num [mul_comm]
  have e4 : (2 : ℝ) ^ (5 * t) = (32 : ℝ) ^ t := by rw [pow_mul]; norm_num
  have h256 : (256 : ℝ) ^ t = (32 : ℝ) ^ t * (8 : ℝ) ^ t := by rw [← mul_pow]; norm_num
  have hb : (0 : ℝ) < (32 : ℝ) ^ t := by positivity
  have he : (0 : ℝ) < (8 : ℝ) ^ t := by positivity
  have key : packReal t * 2 ^ (5 * t)
      = (5 * (t : ℝ) + 6) * 3 ^ (3 * t + 3) + (3 : ℝ) ^ (5 * t + 5) / 2 ^ (3 * t + 4) := by
    unfold packReal
    rw [e1, e2, e3, e4, div_pow, div_pow, h256]
    field_simp
  exact le_trans hcast (le_of_eq key.symm)

theorem summable_packReal : Summable packReal := by
  have h1 : Summable (fun t : ℕ => 27 * (5 * (t : ℝ) + 6) * (27 / 32 : ℝ) ^ t) := by
    have hg : Summable (fun t : ℕ => (t : ℝ) * (27 / 32 : ℝ) ^ t) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (k := 1)
        (r := (27 / 32 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
    have hc : Summable (fun t : ℕ => (27 / 32 : ℝ) ^ t) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have := (hg.mul_left (135 : ℝ)).add (hc.mul_left (162 : ℝ))
    refine this.congr ?_
    intro t; ring
  have h2 : Summable (fun t : ℕ => (243 / 16 : ℝ) * (243 / 256 : ℝ) ^ t) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact h1.add h2


/-! ## The uniform reciprocal bound -/

/-- The absolute constant bounding every partial reciprocal sum. -/
noncomputable def recipBound : ℝ := ∑' t : ℕ, packReal t

/-- **Uniform reciprocal bound.**  Every finite set of positive values of an
iterate-separated set has reciprocal sum at most `recipBound`, an absolute constant. -/
theorem sum_inv_le (hS : IterateSeparated S) (V : Finset ℕ)
    (hVS : ∀ x ∈ V, x ∈ S) (hV1 : ∀ x ∈ V, 1 ≤ x) :
    ∑ x ∈ V, (1 : ℝ) / x ≤ recipBound := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, ∀ x ∈ V, Nat.log 2 x / 5 < T :=
    ⟨V.sup (fun x => Nat.log 2 x / 5) + 1, fun x hx => Nat.lt_succ_of_le (Finset.le_sup (f := fun x => Nat.log 2 x / 5) hx)⟩
  have hmaps : ∀ x ∈ V, Nat.log 2 x / 5 ∈ Finset.range T :=
    fun x hx => Finset.mem_range.mpr (hT x hx)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => (1 : ℝ) / x)]
  have hfib : ∀ t ∈ Finset.range T,
      ∑ x ∈ V.filter (fun x => Nat.log 2 x / 5 = t), (1 : ℝ) / x ≤ packReal t := by
    intro t _
    have hshell : ∀ x ∈ V.filter (fun x => Nat.log 2 x / 5 = t),
        2 ^ (5 * t) ≤ x ∧ x < 2 ^ (5 * t + 5) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hx1 : 1 ≤ x := hV1 x hx.1
      have hne : x ≠ 0 := by omega
      have hlow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hne
      have hhigh : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
      have hmod : Nat.log 2 x = 5 * (Nat.log 2 x / 5) + Nat.log 2 x % 5 :=
        (Nat.div_add_mod _ _).symm
      have hlt5 : Nat.log 2 x % 5 < 5 := Nat.mod_lt _ (by norm_num)
      rw [hx.2] at hmod
      constructor
      · exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlow
      · exact lt_of_lt_of_le hhigh (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hcard : (V.filter (fun x => Nat.log 2 x / 5 = t)).card ≤ packNat t := by
      refine shell_card_le hS t _ (fun x hx => hVS x (Finset.mem_filter.mp hx).1) ?_
      intro x hx
      exact (hshell x hx).2
    have hbound : ∀ x ∈ V.filter (fun x => Nat.log 2 x / 5 = t),
        (1 : ℝ) / x ≤ 1 / 2 ^ (5 * t) := by
      intro x hx
      have h1 := (hshell x hx).1
      have hpos : (0 : ℝ) < 2 ^ (5 * t) := by positivity
      refine one_div_le_one_div_of_le hpos ?_
      exact_mod_cast h1
    calc ∑ x ∈ V.filter (fun x => Nat.log 2 x / 5 = t), (1 : ℝ) / x
        ≤ (V.filter (fun x => Nat.log 2 x / 5 = t)).card • ((1 : ℝ) / 2 ^ (5 * t)) :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = ((V.filter (fun x => Nat.log 2 x / 5 = t)).card : ℝ) / 2 ^ (5 * t) := by
          rw [nsmul_eq_mul]; ring
      _ ≤ (packNat t : ℝ) / 2 ^ (5 * t) := by
          gcongr
      _ ≤ packReal t := packNat_div_le t
  refine le_trans (Finset.sum_le_sum hfib) ?_
  exact summable_packReal.sum_le_tsum _ (fun t _ => packReal_nonneg t)


/-- Time-indexed reciprocal sums along a divergent orbit are uniformly bounded. -/
theorem sum_inv_orbit_le {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 : ℝ) / (tstep^[j] n : ℝ) ≤ recipBound := by
  classical
  have hinj : ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k,
      tstep^[a] n = tstep^[b] n → a = b := fun a _ b _ h => tstep_time_injective hn hd h
  have himg : ∑ j ∈ Finset.range k, (1 : ℝ) / (tstep^[j] n : ℝ)
      = ∑ x ∈ (Finset.range k).image (fun j => tstep^[j] n), (1 : ℝ) / (x : ℝ) :=
    (Finset.sum_image (f := fun x : ℕ => (1 : ℝ) / (x : ℝ)) hinj).symm
  rw [himg]
  refine sum_inv_le (iterateSeparated_orbitSet hn hd) _ ?_ ?_
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact ⟨j, rfl⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact tstep_iterate_pos hn j

/-! ## The bounded multiplicative `+1` correction -/

/-- The parity trace grows by appending the parity of the current orbit value. -/
theorem traceWord_succ_append (n k : ℕ) :
    traceWord n (k + 1) = traceWord n k ++ [decide (tstep^[k] n % 2 = 1)] := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hL : traceWord n (k + 1 + 1) = decide (n % 2 = 1) :: traceWord (tstep n) (k + 1) := rfl
    have hR : traceWord n (k + 1) = decide (n % 2 = 1) :: traceWord (tstep n) k := rfl
    rw [hL, hR, ih (tstep n), Function.iterate_succ_apply]
    rfl

theorem ones_traceWord_append (n k : ℕ) :
    ones (traceWord n (k + 1))
      = ones (traceWord n k) + (if tstep^[k] n % 2 = 1 then 1 else 0) := by
  rw [traceWord_succ_append]
  by_cases h : tstep^[k] n % 2 = 1
  · simp [h]
  · simp [h]

/-- **The bounded correction.**  Along any orbit, the exact iterate identity is
dominated by the homogeneous term times the exponential of a third of the running
reciprocal sum: `2^k · y_k ≤ 3^(r_k) · n · exp(S_k/3)`.  The `+1` in `3n+1`
contributes only the multiplicative factor `1 + 1/(3y_j)` at each odd step. -/
theorem two_pow_mul_iterate_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    (2 : ℝ) ^ k * (tstep^[k] n : ℝ)
      ≤ 3 ^ ones (traceWord n k) * (n : ℝ)
          * Real.exp ((∑ j ∈ Finset.range k, (1 : ℝ) / (tstep^[j] n : ℝ)) / 3) := by
  induction k with
  | zero => simp [traceWord]
  | succ k ih =>
    set y := tstep^[k] n with hy
    have hy1 : 1 ≤ y := tstep_iterate_pos hn k
    have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    have hyR0 : (0 : ℝ) < (y : ℝ) := by linarith
    set S := ∑ j ∈ Finset.range k, (1 : ℝ) / (tstep^[j] n : ℝ) with hS
    have hSsucc : ∑ j ∈ Finset.range (k + 1), (1 : ℝ) / (tstep^[j] n : ℝ)
        = S + 1 / (y : ℝ) := by rw [hS, Finset.sum_range_succ]
    have hZ0 : (0 : ℝ) ≤ 3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3) := by positivity
    have hnext : tstep^[k + 1] n = tstep y := Function.iterate_succ_apply' tstep k n
    by_cases hpar : y % 2 = 1
    · have h2 : 2 * tstep y = 3 * y + 1 := by unfold tstep; split <;> omega
      have h2R : (tstep y : ℝ) = (3 * (y : ℝ) + 1) / 2 := by
        have h : (2 : ℝ) * (tstep y : ℝ) = 3 * (y : ℝ) + 1 := by exact_mod_cast h2
        linarith
      have hones : ones (traceWord n (k + 1)) = ones (traceWord n k) + 1 := by
        rw [ones_traceWord_append]
        simp [← hy, hpar]
      have hexp : (1 : ℝ) + 1 / (3 * (y : ℝ)) ≤ Real.exp (1 / (3 * (y : ℝ))) := by
        have h := Real.add_one_le_exp (1 / (3 * (y : ℝ)))
        linarith
      have hsplit : Real.exp ((S + 1 / (y : ℝ)) / 3)
          = Real.exp (S / 3) * Real.exp (1 / (3 * (y : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
      rw [hnext, hones, hSsucc, h2R, hsplit]
      have hkey : (2 : ℝ) ^ (k + 1) * ((3 * (y : ℝ) + 1) / 2)
          = ((2 : ℝ) ^ k * (y : ℝ)) * (3 + 1 / (y : ℝ)) := by
        field_simp
        ring
      have hRHS : (3 : ℝ) ^ (ones (traceWord n k) + 1) * (n : ℝ)
            * (Real.exp (S / 3) * Real.exp (1 / (3 * (y : ℝ))))
          = 3 * (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3))
            * Real.exp (1 / (3 * (y : ℝ))) := by
        rw [pow_succ]; ring
      rw [hkey, hRHS]
      have hfac : (0 : ℝ) ≤ 3 + 1 / (y : ℝ) := by positivity
      have h1 : ((2 : ℝ) ^ k * (y : ℝ)) * (3 + 1 / (y : ℝ))
          ≤ (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3)) * (3 + 1 / (y : ℝ)) :=
        mul_le_mul_of_nonneg_right ih hfac
      have h2' : (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3)) * (3 + 1 / (y : ℝ))
          = 3 * (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3))
            * (1 + 1 / (3 * (y : ℝ))) := by
        field_simp
      have h3 : 3 * (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3))
            * (1 + 1 / (3 * (y : ℝ)))
          ≤ 3 * (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3))
            * Real.exp (1 / (3 * (y : ℝ))) := by
        have hz : (0 : ℝ) ≤ 3 * (3 ^ ones (traceWord n k) * (n : ℝ) * Real.exp (S / 3)) := by
          linarith
        exact mul_le_mul_of_nonneg_left hexp hz
      linarith [h1, h3, h2'.le, h2'.ge]
    · have h2 : 2 * tstep y = y := by unfold tstep; split <;> omega
      have h2R : (tstep y : ℝ) = (y : ℝ) / 2 := by
        have h : (2 : ℝ) * (tstep y : ℝ) = (y : ℝ) := by exact_mod_cast h2
        linarith
      have hones : ones (traceWord n (k + 1)) = ones (traceWord n k) := by
        rw [ones_traceWord_append]
        simp [← hy, hpar]
      rw [hnext, hones, hSsucc, h2R]
      have hkey : (2 : ℝ) ^ (k + 1) * ((y : ℝ) / 2) = (2 : ℝ) ^ k * (y : ℝ) := by
        rw [pow_succ]; ring
      rw [hkey]
      refine le_trans ih ?_
      have hmono : Real.exp (S / 3) ≤ Real.exp ((S + 1 / (y : ℝ)) / 3) := by
        apply Real.exp_le_exp.mpr
        have hq : (0 : ℝ) < 1 / (y : ℝ) := by positivity
        linarith
      have hpos : (0 : ℝ) ≤ 3 ^ ones (traceWord n k) * (n : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hmono hpos


/-- **The homogeneous coefficient dominates the orbit.**  On a divergent orbit the
correction factor is bounded by the absolute constant `exp (recipBound/3)`, so the
homogeneous coefficient `3^(r_k)/2^k` is at least `y_k` divided by a fixed constant. -/
theorem iterate_le_coefficient {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) (k : ℕ) :
    (tstep^[k] n : ℝ)
      ≤ (3 : ℝ) ^ ones (traceWord n k) / 2 ^ k * ((n : ℝ) * Real.exp (recipBound / 3)) := by
  have h := two_pow_mul_iterate_le n hn k
  have hs := sum_inv_orbit_le hn hd k
  have hmono : Real.exp ((∑ j ∈ Finset.range k, (1 : ℝ) / (tstep^[j] n : ℝ)) / 3)
      ≤ Real.exp (recipBound / 3) := Real.exp_le_exp.mpr (by linarith)
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ ones (traceWord n k) * (n : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpow]
  nlinarith [h, mul_le_mul_of_nonneg_left hmono hnn]

end CollatzMoonshot.FrontA.OrbitPacking
