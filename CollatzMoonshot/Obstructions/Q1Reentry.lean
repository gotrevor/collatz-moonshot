import CollatzMoonshot.Obstructions.Q1Coalescence

/-! Q1 exit and reset obstructions.  All claims concern the actual accelerated
map `tstep`: direct canonical re-entry fails at the exit, a completed target
run can expand its proposed parameter, and resetting to the normalized pair
charges a fourth power of ordinary numerical size. -/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

open CollatzMoonshot.FrontB

def oddExitA (r u : ℕ) : ℕ := 36 * 9 ^ r * u - 1
def oddExitB (r u : ℕ) : ℕ := (9 * 3 ^ r * u + 7) / 2
def phaseWeight (a b : ℕ) : ℕ := (a + 1) * (b - 1) ^ 3

/-! ### Local step lemmas

The step lemmas of the imported modules are private, so the two parity forms
of a single accelerated step are re-established here. -/

/-- One accelerated step halves an even number. -/
private theorem two_tstep_even' {u : ℕ} (hu : u % 2 = 0) : 2 * tstep u = u := by
  simp only [tstep, hu, if_true]
  omega

/-- One accelerated step from an even number, in doubled form. -/
private theorem tstep_double'' (u : ℕ) : tstep (2 * u) = u := by
  have h := two_tstep_even' (u := 2 * u) (by omega)
  omega

/-- One accelerated step from an odd number, pinned by `3*u + 1 = 2*v`. -/
private theorem tstep_odd_val' {u v : ℕ} (hu : u % 2 = 1) (h : 3 * u + 1 = 2 * v) :
    tstep u = v := by
  have h2 := two_tstep_odd hu
  omega

/-- A full run of `k` halvings is an actual orbit segment. -/
private theorem tstep_iterate_two_pow (k x : ℕ) : tstep^[k] (2 ^ k * x) = x := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have h : (2 : ℕ) ^ (m + 1) * x = 2 * (2 ^ m * x) := by ring
    rw [h, tstep_double'', ih]

/-! ### Arithmetic cores of the exit -/

private theorem stepsA_core {P : ℕ} (hP : 0 < P) (hodd : P % 2 = 1) :
    tstep^[2] (16 * P - 1) = 36 * P - 1 := by
  have s1 : tstep (16 * P - 1) = 24 * P - 1 :=
    tstep_odd_val' (by omega) (by omega)
  have s2 : tstep (24 * P - 1) = 36 * P - 1 :=
    tstep_odd_val' (by omega) (by omega)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, s1, s2]

private theorem stepsB_core {N : ℕ} (hN : 0 < N) (hodd : N % 2 = 1) :
    tstep^[2] (1 + 2 * N) = (9 * N + 7) / 2 := by
  have s1 : tstep (1 + 2 * N) = 3 * N + 2 :=
    tstep_odd_val' (by omega) (by omega)
  have s2 : tstep (3 * N + 2) = (9 * N + 7) / 2 :=
    tstep_odd_val' (by omega) (by omega)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, s1, s2]

private theorem stepsTarget_core (P : ℕ) :
    tstep^[2] (36 * P - 1) = 81 * P - 1 := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · norm_num [tstep]
  have s1 : tstep (36 * P - 1) = 54 * P - 1 :=
    tstep_odd_val' (by omega) (by omega)
  have s2 : tstep (54 * P - 1) = 81 * P - 1 :=
    tstep_odd_val' (by omega) (by omega)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, s1, s2]

/-! ### Shared numeric facts -/

private theorem pow3_pos (r : ℕ) : 0 < (3 : ℕ) ^ r := pow_pos (by norm_num) r
private theorem pow9_pos (r : ℕ) : 0 < (9 : ℕ) ^ r := pow_pos (by norm_num) r

private theorem pow9_eq (r : ℕ) : (9 : ℕ) ^ r = 3 ^ r * 3 ^ r := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, mul_pow]

private theorem pow9_mod_two (r : ℕ) : (9 : ℕ) ^ r % 2 = 1 := by
  rw [Nat.pow_mod]; simp

private theorem pow3_mod_two (r : ℕ) : (3 : ℕ) ^ r % 2 = 1 := by
  rw [Nat.pow_mod]; simp

private theorem pow9_mod_four (r : ℕ) : (9 : ℕ) ^ r % 4 = 1 := by
  rw [Nat.pow_mod]; simp

private theorem pow_target (r : ℕ) : (3 : ℕ) ^ (2 * r + 4) = 81 * 9 ^ r := by
  rw [pow_add, pow_mul]; norm_num [mul_comm]

/-! ### The frozen targets -/

/-- The two actual odd exit steps on both frontiers. -/
theorem odd_exit_actual_steps (r u : ℕ) (hu : 0 < u) (ho : u % 2 = 1) :
    tstep^[2] (16 * 9 ^ r * u - 1) = oddExitA r u ∧
    tstep^[2] (1 + 2 * 3 ^ r * u) = oddExitB r u := by
  have hQpos : 0 < 9 ^ r * u := Nat.mul_pos (pow9_pos r) hu
  have hQodd : (9 ^ r * u) % 2 = 1 := by
    rw [Nat.mul_mod, pow9_mod_two, ho]
  have hNpos : 0 < 3 ^ r * u := Nat.mul_pos (pow3_pos r) hu
  have hNodd : (3 ^ r * u) % 2 = 1 := by
    rw [Nat.mul_mod, pow3_mod_two, ho]
  have e1 : 16 * 9 ^ r * u = 16 * (9 ^ r * u) := by ring
  have e2 : 36 * 9 ^ r * u = 36 * (9 ^ r * u) := by ring
  have e3 : 1 + 2 * 3 ^ r * u = 1 + 2 * (3 ^ r * u) := by ring
  have e4 : 9 * 3 ^ r * u = 9 * (3 ^ r * u) := by ring
  simp only [oddExitA, oddExitB, e1, e2, e3, e4]
  exact ⟨stepsA_core hQpos hQodd, stepsB_core hNpos hNodd⟩

/-- The offset created by the exit is retained exactly. -/
theorem odd_exit_affine (r u : ℕ) (hu : 0 < u) (ho : u % 2 = 1) :
    2 * (oddExitA r u + 1) =
      (8 * 3 ^ r) * (2 * oddExitB r u - 7) := by
  have hNodd : (3 ^ r * u) % 2 = 1 := by
    rw [Nat.mul_mod, pow3_mod_two, ho]
  have hQpos : 0 < 36 * 9 ^ r * u :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (pow9_pos r)) hu
  have hB : 2 * oddExitB r u = 9 * (3 ^ r * u) + 7 := by
    have e4 : 9 * 3 ^ r * u = 9 * (3 ^ r * u) := by ring
    simp only [oddExitB, e4]
    omega
  have hA : oddExitA r u + 1 = 36 * 9 ^ r * u := by
    simp only [oddExitA]; omega
  rw [hA, hB, show 9 * (3 ^ r * u) + 7 - 7 = 9 * (3 ^ r * u) by omega, pow9_eq]
  ring

/-- No choice of canonical multiplier restores the old state at this exit. -/
theorem odd_exit_no_canonical_reentry (r u : ℕ) (hu : 0 < u)
    (ho : u % 2 = 1) :
    ¬ ∃ j : ℕ, oddExitA r u + 1 =
      8 * 3 ^ j * (oddExitB r u - 1) := by
  have hNodd : (3 ^ r * u) % 2 = 1 := by
    rw [Nat.mul_mod, pow3_mod_two, ho]
  have hNpos : 0 < 3 ^ r * u := Nat.mul_pos (pow3_pos r) hu
  have hapos := pow3_pos r
  have hQpos : 0 < 36 * 9 ^ r * u :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (pow9_pos r)) hu
  have hZpos : 0 < 3 ^ r * 3 ^ r * u := Nat.mul_pos (Nat.mul_pos hapos hapos) hu
  have hZ : (3 : ℕ) ^ r ≤ 3 ^ r * 3 ^ r * u := by
    calc (3 : ℕ) ^ r = 3 ^ r * 1 * 1 := by ring
      _ ≤ 3 ^ r * 3 ^ r * u := Nat.mul_le_mul (Nat.mul_le_mul_left _ hapos) hu
  have hA : oddExitA r u + 1 = 36 * (3 ^ r * 3 ^ r * u) := by
    simp only [oddExitA]
    rw [pow9_eq] at hQpos
    have : 36 * (3 ^ r * 3 ^ r) * u = 36 * (3 ^ r * 3 ^ r * u) := by ring
    rw [pow9_eq]
    omega
  -- the auxiliary offset
  have hB : 2 * (oddExitB r u - 1) = 9 * (3 ^ r * u) + 5 := by
    have e4 : 9 * 3 ^ r * u = 9 * (3 ^ r * u) := by ring
    simp only [oddExitB, e4]
    omega
  have hCpos : 0 < oddExitB r u - 1 := by omega
  -- the two strict comparisons with the canonical multiplier `8 * 3 ^ r`
  have key : 2 * (8 * 3 ^ r * (oddExitB r u - 1))
      = 72 * (3 ^ r * 3 ^ r * u) + 40 * 3 ^ r := by
    rw [show 2 * (8 * 3 ^ r * (oddExitB r u - 1))
          = 8 * 3 ^ r * (2 * (oddExitB r u - 1)) by ring, hB]
    ring
  have hlow : oddExitA r u + 1 < 8 * 3 ^ r * (oddExitB r u - 1) := by
    rw [hA]; omega
  have hhigh : 8 * 3 ^ r * (oddExitB r u - 1) < 3 * (oddExitA r u + 1) := by
    rw [hA]; omega
  rintro ⟨j, hj⟩
  have hjr : (3 : ℕ) ^ j < 3 ^ r := by
    have h1 : 8 * 3 ^ j * (oddExitB r u - 1) < 8 * 3 ^ r * (oddExitB r u - 1) := by
      rw [← hj]; exact hlow
    by_contra hcon
    push_neg at hcon
    have : 8 * 3 ^ r * (oddExitB r u - 1) ≤ 8 * 3 ^ j * (oddExitB r u - 1) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcon)
    omega
  have hjlt : j < r := by
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hjr
  have hstep : (3 : ℕ) ^ (j + 1) ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hjlt
  have : 3 * (oddExitA r u + 1) = 8 * 3 ^ (j + 1) * (oddExitB r u - 1) := by
    rw [hj, pow_succ]; ring
  have hle : 8 * 3 ^ (j + 1) * (oddExitB r u - 1) ≤ 8 * 3 ^ r * (oddExitB r u - 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hstep)
  omega

/-- The target has two forced odd steps after this exit. -/
theorem odd_exit_target_two (r u : ℕ) (hu : 0 < u) :
    tstep^[2] (oddExitA r u) = 3 ^ (2 * r + 4) * u - 1 := by
  have e2 : 36 * 9 ^ r * u = 36 * (9 ^ r * u) := by ring
  have e5 : 3 ^ (2 * r + 4) * u = 81 * (9 ^ r * u) := by
    rw [pow_target]; ring
  simp only [oddExitA, e2, e5]
  exact stepsTarget_core _

/-- A specified halving run is an actual orbit segment. -/
theorem odd_exit_target_halvings (r u k x : ℕ) (hu : 0 < u)
    (hx : 3 ^ (2 * r + 4) * u - 1 = 2 ^ k * x) :
    tstep^[2 + k] (oddExitA r u) = x := by
  rw [Nat.add_comm, Function.iterate_add_apply, odd_exit_target_two r u hu, hx,
    tstep_iterate_two_pow]

/-- One halving is a uniform expansion of the proposed odd-unit parameter. -/
theorem odd_exit_one_halving_expands (r u : ℕ) (hu : 0 < u)
    (ho : u % 4 = 3) :
    tstep^[3] (oddExitA r u) = (3 ^ (2 * r + 4) * u - 1) / 2 ∧
    u < tstep^[3] (oddExitA r u) := by
  have hQ4 : (9 ^ r * u) % 4 = 3 := by
    rw [Nat.mul_mod, pow9_mod_four, ho]
  have hQpos : 0 < 9 ^ r * u := Nat.mul_pos (pow9_pos r) hu
  have hQge : u ≤ 9 ^ r * u := Nat.le_mul_of_pos_left u (pow9_pos r)
  have e5 : 3 ^ (2 * r + 4) * u = 81 * (9 ^ r * u) := by rw [pow_target]; ring
  have hstep : tstep^[3] (oddExitA r u) = (3 ^ (2 * r + 4) * u - 1) / 2 := by
    rw [Function.iterate_succ_apply' tstep 2, odd_exit_target_two r u hu]
    have heven : (3 ^ (2 * r + 4) * u - 1) % 2 = 0 := by rw [e5]; omega
    have := two_tstep_even' heven
    omega
  refine ⟨hstep, ?_⟩
  rw [hstep, e5]
  omega

/-- A fresh normalized pair charges a fourth power of its size. -/
theorem phaseWeight_normalized (d : ℕ) (hd : 0 < d) :
    phaseWeight (8 * d - 1) (d + 1) = 8 * d ^ 4 := by
  simp only [phaseWeight, Nat.add_sub_cancel]
  rw [show 8 * d - 1 + 1 = 8 * d by omega]
  ring

/-- Returning to the normalized state with lower weight is exactly numerical
descent of its parameter; shrinking the auxiliary before reset is insufficient. -/
theorem canonical_reset_rank_iff (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    phaseWeight (8 * d - 1) (d + 1) <
      phaseWeight (8 * e - 1) (e + 1) ↔ d < e := by
  rw [phaseWeight_normalized d hd, phaseWeight_normalized e he]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have : e ^ 4 ≤ d ^ 4 := Nat.pow_le_pow_left hcon 4
    omega
  · intro h
    have : d ^ 4 < e ^ 4 := Nat.pow_lt_pow_left h (by norm_num)
    omega

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
