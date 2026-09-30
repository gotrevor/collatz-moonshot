/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.CubicCarry

/-! The hard cubic auxiliary has both a positive finite coalescence class and
arbitrarily long finite-depth nonmeeting classes.  All claims concern the
actual accelerated map `tstep`. -/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

open CollatzMoonshot.FrontB

def branchQ (t : ℕ) : ℕ := 105 + 2048 * t
def hardParam (t : ℕ) : ℕ := 240 + 1024 * t

/-! ### Local step lemmas

`CubicCarry` keeps its step lemmas private, so the two parity forms of a
single accelerated step are re-established here. -/

/-- One accelerated step halves an even number. -/
private theorem two_tstep_even {u : ℕ} (hu : u % 2 = 0) : 2 * tstep u = u := by
  simp only [tstep, hu, if_true]
  omega

/-- One accelerated step from an even number, in offset form. -/
private theorem tstep_double' (u : ℕ) : tstep (2 * u) = u := by
  have h := two_tstep_even (u := 2 * u) (by omega)
  omega

/-- One accelerated step from an odd number, pinned by `3*u + 1 = 2*v`. -/
private theorem tstep_odd_val {u v : ℕ} (hu : u % 2 = 1) (h : 3 * u + 1 = 2 * v) :
    tstep u = v := by
  have h2 := two_tstep_odd hu
  omega

/-! ### The reusable cylinder offset -/

/-- A full parity cylinder of depth `k` has an exact affine endpoint with
positive odd multiplier.  This is the shared helper for both directions. -/
theorem tstep_iterate_pow_two_offset (k x d : ℕ) :
    tstep^[k] (x + 2 ^ k * d) =
      tstep^[k] x + 3 ^ ones (traceWord x k) * d := by
  induction k generalizing x d with
  | zero => simp [traceWord]
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hpow : (2 : ℕ) ^ (m + 1) * d = 2 * (2 ^ m * d) := by ring
    rcases Nat.even_or_odd x with he | ho
    · have hx : x % 2 = 0 := Nat.even_iff.mp he
      have hy : (x + 2 ^ (m + 1) * d) % 2 = 0 := by omega
      have e1 := two_tstep_even hx
      have e2 := two_tstep_even hy
      have hstep : tstep (x + 2 ^ (m + 1) * d) = tstep x + 2 ^ m * d := by omega
      have ht : traceWord x (m + 1) = false :: traceWord (tstep x) m := by
        simp [traceWord, hx]
      rw [hstep, ih, ht]
      simp only [ones]
    · have hx : x % 2 = 1 := Nat.odd_iff.mp ho
      have hy : (x + 2 ^ (m + 1) * d) % 2 = 1 := by omega
      have e1 := two_tstep_odd hx
      have e2 := two_tstep_odd hy
      have hstep0 : tstep (x + 2 ^ (m + 1) * d) = tstep x + 3 * (2 ^ m * d) := by
        omega
      have hstep : tstep (x + 2 ^ (m + 1) * d) = tstep x + 2 ^ m * (3 * d) := by
        rw [hstep0]; ring
      have ht : traceWord x (m + 1) = true :: traceWord (tstep x) m := by
        simp [traceWord, hx]
      rw [hstep, ih, ht]
      simp only [ones]
      ring

/-! ### The `1 ↔ 2` base orbit -/

private theorem trace_one_two (m : ℕ) :
    traceWord 1 (m + 2) = true :: false :: traceWord 1 m := by
  simp [traceWord]

private theorem one_orbit_pair (j : ℕ) :
    tstep^[2 * j] 1 = 1 ∧ ones (traceWord 1 (2 * j)) = j ∧
      tstep^[2 * j + 1] 1 = 2 ∧ ones (traceWord 1 (2 * j + 1)) = j + 1 := by
  induction j with
  | zero => exact ⟨by decide, by decide, by decide, by decide⟩
  | succ i ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have hit : tstep^[2] 1 = 1 := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 2 by ring, Function.iterate_add_apply, hit, h0]
    · rw [show 2 * (i + 1) = 2 * i + 2 by ring, trace_one_two]
      simp only [ones]
      omega
    · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, Function.iterate_add_apply,
        hit, h2]
    · rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring, trace_one_two]
      simp only [ones]
      omega

private theorem one_orbit (j : ℕ) :
    tstep^[j] 1 ≤ 2 ∧ ones (traceWord 1 j) = (j + 1) / 2 := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨i, hi⟩ := he
    obtain ⟨h0, h1, _, _⟩ := one_orbit_pair i
    have hj : j = 2 * i := by omega
    subst hj
    exact ⟨by rw [h0]; norm_num, by rw [h1]; omega⟩
  · obtain ⟨i, hi⟩ := ho
    obtain ⟨_, _, h2, h3⟩ := one_orbit_pair i
    have hj : j = 2 * i + 1 := by omega
    subst hj
    exact ⟨by rw [h2], by rw [h3]; omega⟩

/-- A depth-`K` cylinder around the `1↔2` orbit stays within twice its
initial value through that depth. -/
theorem near_one_cycle_le_double (K u j : ℕ) (hj : j ≤ K) :
    tstep^[j] (1 + 2 ^ K * u) ≤ 2 * (1 + 2 ^ K * u) := by
  obtain ⟨hle, hones⟩ := one_orbit j
  have hsplit : (1 : ℕ) + 2 ^ K * u = 1 + 2 ^ j * (2 ^ (K - j) * u) := by
    rw [← mul_assoc, ← pow_add, show j + (K - j) = K by omega]
  rw [hsplit, tstep_iterate_pow_two_offset, hones]
  -- the multiplier `3 ^ ((j+1)/2)` is at most `2 ^ (j+1)`
  have hA : (3 : ℕ) ^ ((j + 1) / 2) ≤ 2 ^ (j + 1) := by
    calc (3 : ℕ) ^ ((j + 1) / 2) ≤ 4 ^ ((j + 1) / 2) :=
          Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * ((j + 1) / 2)) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkey : 3 ^ ((j + 1) / 2) * 2 ^ (K - j) ≤ 2 ^ (K + 1) := by
    calc 3 ^ ((j + 1) / 2) * 2 ^ (K - j) ≤ 2 ^ (j + 1) * 2 ^ (K - j) :=
          Nat.mul_le_mul hA (le_refl _)
      _ = 2 ^ (j + 1 + (K - j)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 3 ^ ((j + 1) / 2) * (2 ^ (K - j) * u) ≤ 2 ^ (K + 1) * u := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul hkey (le_refl _)
  have hpow : (2 : ℕ) ^ (K + 1) * u = 2 * (2 ^ K * u) := by rw [pow_succ]; ring
  omega

/-! ### The positive eleven-step coalescence class -/

/-- The two affine families coalesce after eleven actual shortcut steps.
The common endpoint is stated exactly, not just as an equality. -/
theorem branchQ_eleven (t : ℕ) :
    tstep^[11] (branchQ t) = 38 + 729 * t ∧
    tstep^[11] (27 * branchQ t + 2) = 38 + 729 * t := by
  have hA : tstep^[11] (105 : ℕ) = 38 := by decide
  have hAo : ones (traceWord 105 11) = 6 := by decide
  have hB : tstep^[11] (2837 : ℕ) = 38 := by decide
  have hBo : ones (traceWord 2837 11) = 3 := by decide
  constructor
  · have h : branchQ t = 105 + 2 ^ 11 * t := by simp only [branchQ]; norm_num
    rw [h, tstep_iterate_pow_two_offset, hA, hAo]
    ring
  · have h : 27 * branchQ t + 2 = 2837 + 2 ^ 11 * (27 * t) := by
      simp only [branchQ]; ring
    rw [h, tstep_iterate_pow_two_offset, hB, hBo]
    ring

/-! ### The seventh actual step of the hard family -/

/-- The seventh actual step of the hard family is the competing `q₁` head. -/
theorem cubic_seventh (s : ℕ) :
    tstep^[7] (cubicN s) = 27 * cubicQ1 s + 2 := by
  rw [show (7 : ℕ) = 6 + 1 by rfl, Function.iterate_succ_apply', cubic_carry_sixth]
  exact tstep_odd_val (by simp only [cubicQ1]; omega) (by ring)

/-! ### The eighteen-versus-eleven bridge -/

private theorem q1_hardParam (t : ℕ) :
    cubicQ1 (hardParam t) = branchQ (322446787 + 1372031325 * t) := by
  simp only [cubicQ1, hardParam, branchQ]; ring

/-- On this parameter slice, the original start meets its auxiliary orbit
after eighteen steps versus eleven steps. -/
theorem hardParam_eighteen_meets_q1 (t : ℕ) :
    tstep^[18] (cubicN (hardParam t)) =
      tstep^[11] (cubicQ1 (hardParam t)) := by
  rw [show (18 : ℕ) = 11 + 7 by rfl, Function.iterate_add_apply, cubic_seventh,
    q1_hardParam]
  exact ((branchQ_eleven _).2).trans ((branchQ_eleven _).1).symm

/-- The coalescence gives actual descent on the positive parameter slice. -/
theorem hardParam_descends_at_eighteen (t : ℕ) :
    tstep^[18] (cubicN (hardParam t)) < cubicN (hardParam t) := by
  rw [hardParam_eighteen_meets_q1, q1_hardParam, (branchQ_eleven _).1]
  simp only [cubicN, hardParam]
  omega

/-! ### The hard-shadow ordered separation

The six-term affine prefix of `cubicN` is recomputed locally (the
`CubicCarry` copies are private), then an odd-run induction covers the
remaining depth. -/

private theorem pre1 (s : ℕ) : tstep (cubicN s) = 38314322795 + 58540003200 * s :=
  tstep_odd_val (by simp only [cubicN]; omega) (by simp only [cubicN]; ring)

private theorem pre2 (s : ℕ) :
    tstep (38314322795 + 58540003200 * s) = 57471484193 + 87810004800 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem pre3 (s : ℕ) :
    tstep (57471484193 + 87810004800 * s) = 86207226290 + 131715007200 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem pre4 (s : ℕ) :
    tstep (86207226290 + 131715007200 * s) = 43103613145 + 65857503600 * s := by
  rw [show 86207226290 + 131715007200 * s = 2 * (43103613145 + 65857503600 * s) by ring]
  exact tstep_double' _

private theorem pre5 (s : ℕ) :
    tstep (43103613145 + 65857503600 * s) = 64655419718 + 98786255400 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem pre6 (s : ℕ) :
    tstep (64655419718 + 98786255400 * s) = 32327709859 + 49393127700 * s := by
  rw [show 64655419718 + 98786255400 * s = 2 * (32327709859 + 49393127700 * s) by ring]
  exact tstep_double' _

/-- Every one of the first six actual iterates of `cubicN` is at least the
start: the prefix has not descended. -/
private theorem prefix_ge (s : ℕ) : ∀ i ≤ 6, cubicN s ≤ tstep^[i] (cubicN s) := by
  intro i hi
  interval_cases i
  · simp
  · show cubicN s ≤ tstep (cubicN s)
    rw [pre1]; simp only [cubicN]; omega
  · show cubicN s ≤ tstep (tstep (cubicN s))
    rw [pre1, pre2]; simp only [cubicN]; omega
  · show cubicN s ≤ tstep (tstep (tstep (cubicN s)))
    rw [pre1, pre2, pre3]; simp only [cubicN]; omega
  · show cubicN s ≤ tstep (tstep (tstep (tstep (cubicN s))))
    rw [pre1, pre2, pre3, pre4]; simp only [cubicN]; omega
  · show cubicN s ≤ tstep (tstep (tstep (tstep (tstep (cubicN s)))))
    rw [pre1, pre2, pre3, pre4, pre5]; simp only [cubicN]; omega
  · show cubicN s ≤ tstep (tstep (tstep (tstep (tstep (tstep (cubicN s))))))
    rw [pre1, pre2, pre3, pre4, pre5, pre6]; simp only [cubicN]; omega

/-- An odd run: if `p + 1` carries `r + m + 3` powers of two then the first
`r` accelerated steps from `p` are all odd shortcut steps, and the exact
value of the `r`-th one is pinned. -/
private theorem odd_run :
    ∀ (r m u p : ℕ), p + 1 = 2 ^ (r + m + 3) * u →
      tstep^[r] p + 1 = 3 ^ r * 2 ^ (m + 3) * u := by
  intro r
  induction r with
  | zero => intro m u p h; simpa using h
  | succ i ih =>
    intro m u p h
    have hpow : (2 : ℕ) ^ (i + 1 + m + 3) * u = 2 * (2 ^ (i + m + 3) * u) := by
      rw [show i + 1 + m + 3 = (i + m + 3) + 1 by ring, pow_succ]; ring
    have hodd : p % 2 = 1 := by omega
    have e := two_tstep_odd hodd
    have hnext0 : tstep p + 1 = 3 * (2 ^ (i + m + 3) * u) := by omega
    have hnext : tstep p + 1 = 2 ^ (i + m + 3) * (3 * u) := by rw [hnext0]; ring
    rw [Function.iterate_succ_apply, ih m (3 * u) (tstep p) hnext]
    ring


/-! Small-context arithmetic helpers for the auxiliary side.  They are stated
for abstract `q, n, U`, which keeps `omega` away from the eleven-digit
progression coefficients: those enter only through the two `ring` identities
`128*q = 9*n+1` and `2*(9*q+1) = cubicP s + 1`. -/

/-- The exact affine tie between the auxiliary label and the original start. -/
private theorem q1_cubicN_link (s : ℕ) : 128 * cubicQ1 s = 9 * cubicN s + 1 := by
  simp only [cubicQ1, cubicN]; ring

/-- `cubicP s + 1` is exactly twice `9*q + 1`. -/
private theorem cubicP_succ (s : ℕ) : 2 * (9 * cubicQ1 s + 1) = cubicP s + 1 := by
  simp only [cubicP, cubicQ1]; ring

/-- `q ≡ 3 (mod 4)`, and twice the near-cycle point is already below the
original start.  The strict inequality is `47 < 175*q`, valid for `q ≥ 1`. -/
private theorem aux_arith (q n U : ℕ) (hw : 9 * q + 1 = 4 * U)
    (hqn : 128 * q = 9 * n + 1) : q % 4 = 3 ∧ 2 * (1 + U) < n := by
  omega

/-- The two opening auxiliary values are already below the original start. -/
private theorem aux_one (q n U : ℕ) (hw : 9 * q + 1 = 4 * U)
    (hqn : 128 * q = 9 * n + 1) : q < n ∧ tstep q < n := by
  obtain ⟨hq4, hb⟩ := aux_arith q n U hw hqn
  have e1 := two_tstep_odd (u := q) (by omega)
  exact ⟨by omega, by omega⟩

/-- `q ≡ 3 (mod 4)` makes the first two auxiliary steps both odd shortcut
steps, landing exactly on the near-cycle point `1 + 2^K*u`. -/
private theorem aux_two (q U : ℕ) (hw : 9 * q + 1 = 4 * U) :
    tstep^[2] q = 1 + U := by
  have hq4 : q % 4 = 3 := by omega
  have e1 := two_tstep_odd (u := q) (by omega)
  have ho1 : tstep q % 2 = 1 := by omega
  have e2 := two_tstep_odd ho1
  show tstep (tstep q) = _
  omega

/-- For every fixed depth there is a hard-family parameter whose original
orbit has not descended while its auxiliary orbit stays below the original
start throughout that depth. -/
theorem cubicN_q1_ordered_separation :
    ∀ K : ℕ, ∃ s : ℕ,
      (∀ i ≤ K, cubicN s ≤ tstep^[i] (cubicN s)) ∧
      (∀ j ≤ K, tstep^[j] (cubicQ1 s) < cubicN s) := by
  intro K
  obtain ⟨s, c, hc⟩ := cubic_peel_growth_divisibility (K + 1)
  refine ⟨s, ?_, ?_⟩
  · -- the original orbit does not descend through depth `K`
    have h6 : tstep^[6] (cubicN s) = 32327709859 + 49393127700 * s := by
      show tstep (tstep (tstep (tstep (tstep (tstep (cubicN s)))))) = _
      rw [pre1, pre2, pre3, pre4, pre5, pre6]
    have hP : tstep^[6] (cubicN s) + 1 = 2 ^ (K + 3) * c := by
      rw [h6]
      simp only [cubicP] at hc
      rw [show K + 3 = K + 1 + 2 by ring]
      omega
    intro i hi
    rcases Nat.lt_or_ge i 7 with hsmall | hbig
    · exact prefix_ge s i (by omega)
    · obtain ⟨r, hr⟩ : ∃ r, i = r + 6 := ⟨i - 6, by omega⟩
      subst hr
      have hrK : r ≤ K := by omega
      have hrun := odd_run r (K - r) c (tstep^[6] (cubicN s))
        (by rw [show r + (K - r) + 3 = K + 3 by omega]; exact hP)
      have hge : 2 ^ (K + 3) * c ≤ 3 ^ r * 2 ^ (K - r + 3) * c := by
        have h1 : (2 : ℕ) ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by norm_num) _
        have h2 : (2 : ℕ) ^ (K + 3) = 2 ^ r * 2 ^ (K - r + 3) := by
          rw [← pow_add]; congr 1; omega
        rw [h2]
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 (le_refl _)) (le_refl _)
      have hstep : tstep^[6] (cubicN s) ≤ tstep^[r] (tstep^[6] (cubicN s)) := by omega
      rw [Function.iterate_add_apply]
      exact le_trans (prefix_ge s 6 le_rfl) hstep
  · -- the auxiliary orbit stays below the original start through depth `K`
    obtain ⟨U, hU⟩ : ∃ U : ℕ, 2 ^ K * c = U := ⟨_, rfl⟩
    have e2 : (2 : ℕ) ^ (K + 1 + 2) * c = 2 * (4 * (2 ^ K * c)) := by
      rw [show K + 1 + 2 = 3 + K by ring, pow_add]; ring
    have key : 2 * (9 * cubicQ1 s + 1) = 2 * (4 * U) := by
      rw [cubicP_succ, hc, e2, hU]
    have hw : 9 * cubicQ1 s + 1 = 4 * U :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) key
    have hqn := q1_cubicN_link s
    obtain ⟨hq4, hbound⟩ := aux_arith (cubicQ1 s) (cubicN s) U hw hqn
    have h2q := aux_two (cubicQ1 s) U hw
    intro j hj
    rcases j with _ | _ | j'
    · exact (aux_one (cubicQ1 s) (cubicN s) U hw hqn).1
    · exact (aux_one (cubicQ1 s) (cubicN s) U hw hqn).2
    · have hjK : j' ≤ K := by omega
      have hnear := near_one_cycle_le_double K c j' hjK
      rw [hU] at hnear
      clear hU hc e2 key hqn hw
      rw [show j' + 1 + 1 = j' + 2 from rfl, Function.iterate_add_apply, h2q]
      omega

/-- The ordered separation excludes every bounded pairwise meeting between
the two actual orbits, even when the two time indices differ. -/
theorem cubicN_q1_no_bounded_pairwise_meeting :
    ∀ K : ℕ, ∃ s : ℕ, ∀ i ≤ K, ∀ j ≤ K,
      tstep^[i] (cubicN s) ≠ tstep^[j] (cubicQ1 s) := by
  intro K
  obtain ⟨s, hA, hB⟩ := cubicN_q1_ordered_separation K
  refine ⟨s, fun i hi j hj => ?_⟩
  have h1 := hA i hi
  have h2 := hB j hj
  omega

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

