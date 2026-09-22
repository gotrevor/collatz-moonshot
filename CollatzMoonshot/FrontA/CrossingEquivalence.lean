/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.OrbitSummability
import CollatzMoonshot.FrontA.FirstCrossing

/-!
# `CrossingExists` is exactly the divergence front

Final step of `RESEARCH-2026-09-22-packing-shadow.md`: the existing predicate
`FrontA.FirstCrossing.CrossingExists` (every start `n ≥ 2` has a finite index `m`
with `3^(ones (traceWord n m)) < 2^m`) is *equivalent* to the existing
`NoDivergentOrbit`.

Neither direction assumes `StoppingCorrect`, `NoNontrivialCycle`, or any
verification range; positive nontrivial cycles, if they exist, satisfy
`CrossingExists` (the reverse implication produces the crossing *from* the cycle).
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB CollatzMoonshot.FrontA
open CollatzMoonshot.FrontA.OrbitPacking

/-! ## Odd-step counts add along the orbit -/

/-- The odd-step count of a length-`k+t` trace splits at time `k`. -/
theorem ones_traceWord_add (n k t : ℕ) :
    ones (traceWord n (k + t))
      = ones (traceWord n k) + ones (traceWord (tstep^[k] n) t) := by
  induction t with
  | zero => simp [traceWord]
  | succ t ih =>
    have h1 : ones (traceWord n (k + t + 1))
        = ones (traceWord n (k + t)) + (if tstep^[k + t] n % 2 = 1 then 1 else 0) :=
      ones_traceWord_append n (k + t)
    have h2 : ones (traceWord (tstep^[k] n) (t + 1))
        = ones (traceWord (tstep^[k] n) t)
          + (if tstep^[t] (tstep^[k] n) % 2 = 1 then 1 else 0) :=
      ones_traceWord_append _ t
    have h3 : tstep^[t] (tstep^[k] n) = tstep^[k + t] n := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    rw [show k + (t + 1) = k + t + 1 from by omega, h1, ih, h2, h3]
    omega

/-! ## A divergent orbit has arbitrarily late ballot-forever tails -/

/-- The accelerated version of `exists_floor_of_diverges`. -/
theorem exists_floor_tstep {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) (N : ℕ) :
    ∃ K, ∀ k, K ≤ k → N ≤ tstep^[k] n := by
  obtain ⟨K, hK⟩ := exists_floor_of_diverges hd N
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨K', hK', hmono⟩ := exists_step_count k n
  rw [hK']
  exact hK K' (le_trans hk (hmono hn))

/-- **Arbitrarily late tail minima of the homogeneous coefficient.**  On a divergent
orbit `3^(r_k)/2^k` tends to infinity, so it attains a minimum on every index tail. -/
theorem exists_tail_min {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) (j : ℕ) :
    ∃ k, j ≤ k ∧ ∀ t : ℕ,
      (3 : ℝ) ^ ones (traceWord n k) / 2 ^ k
        ≤ (3 : ℝ) ^ ones (traceWord n (k + t)) / 2 ^ (k + t) := by
  classical
  set b : ℕ → ℝ := fun k => (3 : ℝ) ^ ones (traceWord n k) / 2 ^ k with hbdef
  set C : ℝ := (n : ℝ) * Real.exp (recipBound / 3) with hCdef
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hC : 0 < C := by rw [hCdef]; positivity
  have hlow : ∀ k, (tstep^[k] n : ℝ) ≤ b k * C := fun k => iterate_le_coefficient hn hd k
  obtain ⟨M, hM⟩ := exists_nat_gt (b j * C)
  obtain ⟨K, hK⟩ := exists_floor_tstep hn hd M
  set K' := max K j with hK'def
  have hjK' : j ≤ K' := le_max_right _ _
  obtain ⟨k₀, hk₀mem, hk₀min⟩ :=
    Finset.exists_min_image (Finset.Icc j K') b ⟨j, by simp [hjK']⟩
  have hk₀j : j ≤ k₀ := (Finset.mem_Icc.mp hk₀mem).1
  have hjmem : j ∈ Finset.Icc j K' := by simp [hjK']
  refine ⟨k₀, hk₀j, fun t => ?_⟩
  by_cases hle : k₀ + t ≤ K'
  · exact hk₀min _ (Finset.mem_Icc.mpr ⟨by omega, hle⟩)
  · have hlt : K' < k₀ + t := by omega
    have hfloor : M ≤ tstep^[k₀ + t] n := hK _ (by omega)
    have h1 : (M : ℝ) ≤ (tstep^[k₀ + t] n : ℝ) := by exact_mod_cast hfloor
    have h2 : (tstep^[k₀ + t] n : ℝ) ≤ b (k₀ + t) * C := hlow _
    have h3 : b j * C < b (k₀ + t) * C := by linarith
    have h4 : b j < b (k₀ + t) := lt_of_mul_lt_mul_right (by linarith) hC.le
    have h5 : b k₀ ≤ b j := hk₀min _ hjmem
    linarith

/-- **The ballot-forever tail.**  Every divergent orbit contains a value `x ≥ 2`
whose coefficient never crosses: `2^m ≤ 3^(ones (traceWord x m))` for all `m`. -/
theorem exists_ballot_forever {n : ℕ} (hn : 1 ≤ n) (hd : Diverges n) (j : ℕ) :
    ∃ k, j ≤ k ∧ 2 ≤ tstep^[k] n ∧
      ∀ m, 2 ^ m ≤ 3 ^ ones (traceWord (tstep^[k] n) m) := by
  obtain ⟨k, hjk, hmin⟩ := exists_tail_min hn hd j
  refine ⟨k, hjk, ?_, ?_⟩
  · have h1 : 1 ≤ tstep^[k] n := tstep_iterate_pos hn k
    rcases lt_or_ge (tstep^[k] n) 2 with hlt | hge
    · exfalso
      have hone : tstep^[k] n = 1 := by omega
      have h2 : tstep^[2 + k] n = 1 := by
        rw [Function.iterate_add_apply, hone]
        decide
      have := tstep_time_injective hn hd (h2.trans hone.symm)
      omega
    · exact hge
  · intro m
    have h := hmin m
    have hsplit : ones (traceWord n (k + m))
        = ones (traceWord n k) + ones (traceWord (tstep^[k] n) m) := ones_traceWord_add n k m
    rw [hsplit, pow_add, pow_add] at h
    have h3 : (0 : ℝ) < (3 : ℝ) ^ ones (traceWord n k) := by positivity
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have h3m : (0 : ℝ) < (3 : ℝ) ^ ones (traceWord (tstep^[k] n) m) := by positivity
    have key : (2 : ℝ) ^ m ≤ (3 : ℝ) ^ ones (traceWord (tstep^[k] n) m) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
      nlinarith [h, mul_pos h3 h2k, h2m, h3m]
    exact_mod_cast key

/-- **Forward implication.**  A finite coefficient crossing at every start rules out
divergence. -/
theorem noDivergentOrbit_of_crossingExists (h : CrossingExists) : NoDivergentOrbit := by
  intro n hn hd
  obtain ⟨k, _, hx2, hball⟩ := exists_ballot_forever hn hd 0
  obtain ⟨m, hm⟩ := h _ hx2
  have := hball m
  omega


/-! ## The reverse implication: a bounded orbit manufactures its own crossing -/

/-- A non-divergent positive orbit repeats a value under the accelerated map. -/
theorem exists_tstep_repeat_of_not_diverges {n : ℕ} (_hn : 1 ≤ n) (h : ¬ Diverges n) :
    ∃ i j, i < j ∧ tstep^[i] n = tstep^[j] n := by
  classical
  rw [Diverges] at h
  simp only [not_forall, not_exists, not_le] at h
  obtain ⟨M, hM⟩ := h
  have hbound : ∀ k, tstep^[k] n < M := by
    intro k
    obtain ⟨K, hK, _⟩ := exists_step_count k n
    rw [hK]
    exact hM K
  have hmaps : ∀ k ∈ Finset.range (M + 1), tstep^[k] n ∈ Finset.range M :=
    fun k _ => Finset.mem_range.mpr (hbound k)
  have hcard : (Finset.range M).card < (Finset.range (M + 1)).card := by simp
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact ⟨a, b, hlt, heq⟩
  · exact ⟨b, a, by omega, heq.symm⟩

/-- **Every positive accelerated cycle is coefficient-subcritical.**  Some step of a
positive cycle is odd, so the `+1` contributes a positive numerator and the
homogeneous coefficient around the period is strictly below one. -/
theorem pow_ones_lt_of_cycle {x p : ℕ} (hx : 1 ≤ x) (hp : 1 ≤ p) (hcyc : tstep^[p] x = x) :
    3 ^ ones (traceWord x p) < 2 ^ p := by
  have hid := tstep_iterate_identity p x
  rw [hcyc] at hid
  rcases Nat.eq_zero_or_pos (numer (traceWord x p)) with hz | hpos
  · exfalso
    rw [hz] at hid
    have hid' : 2 ^ p * x = 3 ^ ones (traceWord x p) * x := by omega
    have hxx : (2 : ℕ) ^ p = 3 ^ ones (traceWord x p) :=
      Nat.eq_of_mul_eq_mul_right (by omega) hid'
    have he : 2 ^ p % 2 = 0 := by
      have hdvd : (2 : ℕ) ∣ 2 ^ p := dvd_pow_self 2 (by omega)
      omega
    have ho : 3 ^ ones (traceWord x p) % 2 = 1 := by simp [Nat.pow_mod]
    omega
  · have hlt : 3 ^ ones (traceWord x p) * x < 2 ^ p * x := by omega
    exact lt_of_mul_lt_mul_right hlt (by omega)

/-- The odd-step count over `s` full periods is `s` times the period's count. -/
theorem ones_traceWord_period {x p : ℕ} (hcyc : tstep^[p] x = x) (s : ℕ) :
    ones (traceWord x (s * p)) = s * ones (traceWord x p) := by
  induction s with
  | zero => simp [traceWord]
  | succ s ih =>
    have hfix : tstep^[s * p] x = x := by
      rw [Nat.mul_comm, Function.iterate_mul]
      exact Function.iterate_fixed hcyc s
    have h := ones_traceWord_add x (s * p) p
    rw [hfix] at h
    rw [show (s + 1) * p = s * p + p from by ring, h, ih]
    ring

/-- **Reverse implication.**  If no positive orbit diverges, every start `n ≥ 2` has a
finite coefficient crossing.  The crossing comes from the cycle the orbit falls into:
its period coefficient is `< 1`, so repeating the period drives the prefix coefficient
below one regardless of the preperiod.  No cycle exclusion is used. -/
theorem crossingExists_of_noDivergentOrbit (h : NoDivergentOrbit) : CrossingExists := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨i, j, hij, heq⟩ := exists_tstep_repeat_of_not_diverges hn1 (h n hn1)
  set x := tstep^[i] n with hxdef
  have hx1 : 1 ≤ x := tstep_iterate_pos hn1 i
  have hcyc : tstep^[j - i] x = x := by
    rw [hxdef, ← Function.iterate_add_apply, show j - i + i = j from by omega]
    exact heq.symm
  set p := j - i with hpdef
  have hp : 1 ≤ p := by omega
  have hsub : 3 ^ ones (traceWord x p) < 2 ^ p := pow_ones_lt_of_cycle hx1 hp hcyc
  set a := ones (traceWord x p) with hadef
  set r := ones (traceWord n i) with hrdef
  -- pick a number of periods driving the coefficient below one
  have hrho : ((3 : ℝ) ^ a) / 2 ^ p < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hsub
  have hrho0 : (0 : ℝ) ≤ (3 : ℝ) ^ a / 2 ^ p := by positivity
  have heps : (0 : ℝ) < (2 : ℝ) ^ i / 3 ^ r := by positivity
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one heps hrho
  refine ⟨i + s * p, ?_⟩
  have hones : ones (traceWord n (i + s * p)) = r + s * a := by
    rw [ones_traceWord_add n i (s * p), ← hxdef, ones_traceWord_period hcyc s, hrdef, hadef]
  rw [hones]
  have hkey : (3 : ℝ) ^ (r + s * a) < (2 : ℝ) ^ (i + s * p) := by
    have hexp : ((3 : ℝ) ^ a / 2 ^ p) ^ s = (3 : ℝ) ^ (s * a) / 2 ^ (s * p) := by
      rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a s, Nat.mul_comm p s]
    rw [hexp, div_lt_div_iff₀ (by positivity) (by positivity)] at hs
    rw [pow_add, pow_add]
    nlinarith [hs, pow_pos (show (0:ℝ) < 3 by norm_num) r,
      pow_pos (show (0:ℝ) < 2 by norm_num) i,
      pow_pos (show (0:ℝ) < 3 by norm_num) (s * a),
      pow_pos (show (0:ℝ) < 2 by norm_num) (s * p)]
  exact_mod_cast hkey

/-- **`CrossingExists` is exactly the divergence front.**  Equivalent to the existing
`NoDivergentOrbit`, with no appeal to `StoppingCorrect`, no cycle exclusion, and no
verification range.  Positive nontrivial cycles, if any exist, satisfy both sides. -/
theorem crossingExists_iff_noDivergentOrbit : CrossingExists ↔ NoDivergentOrbit :=
  ⟨noDivergentOrbit_of_crossingExists, crossingExists_of_noDivergentOrbit⟩

/-!
## Audit surface

The three headline declarations of this chain, with their transitive assumptions.
Real `#print axioms` output at the time of writing: each reports exactly the
classical trio `[propext, Classical.choice, Quot.sound]` - no project axiom, no
`native_decide`, no `sorry`.
-/

section Audit

open CollatzMoonshot.FrontA.OrbitPacking

/-- info: 'CollatzMoonshot.FrontA.OrbitPacking.block_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_card_le

/-- info: 'CollatzMoonshot.FrontA.OrbitPacking.sum_inv_orbit_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_inv_orbit_le

/-- info: 'CollatzMoonshot.FrontA.FirstCrossing.crossingExists_iff_noDivergentOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms crossingExists_iff_noDivergentOrbit

end Audit

end CollatzMoonshot.FrontA.FirstCrossing
