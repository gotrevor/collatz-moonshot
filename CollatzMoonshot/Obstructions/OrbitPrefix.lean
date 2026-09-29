import CollatzMoonshot.Obstructions.PositiveApproximation

/-!
# A dyadic ray with an arbitrary finite orbit prefix

This module proves the coefficient identity needed for the sharp anchored
operator constant.  The prefix is counted with multiplicity, so the identity
does not assume that the orbit is injective or misses the dyadic ray.

The proof is elementary and purely algebraic:

* `transfer_pointCoeff`: the transfer of a point mass at `u` is the point mass
  at `tstep u`, for every `u` and every positive coefficient index.  This is
  the rational-coefficient shadow of the two-element shortcut fibre.
* `rayCoeff_two_mul` / `rayCoeff_odd_pre`: the two transfer preimages of the
  dyadic ray `{2^h * n}`.  The even preimage reproduces the ray plus the single
  extra point `2 * v = n`; the odd preimage is odd, so it meets the ray only at
  its base.  Together these give `transfer_rayCoeff_eq`, which says the ray is
  fixed by `transfer` up to the single point mass at `tstep n`.  No parity
  assumption on the base `n` is used.
* The prefix sum then telescopes (`telescope_sub`), the two copies of
  `pointCoeff (tstep n) v` cancel, and only the endpoint `tstep^[L] n` survives.

Nothing here is an independent Collatz estimate: it is a finite algebraic
identity valid for every positive base, including even bases and `n = 1`,
and with repeated orbit points counted with multiplicity.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

open CollatzMoonshot.FrontB

/-- The coefficient of a point mass at `u`. -/
def pointCoeff (u v : ℕ) : ℚ := if v = u then 1 else 0

/-- `D_n` plus the orbit points at times `1, ..., L-1`, with multiplicity. -/
def orbitPrefixCoeff (n L v : ℕ) : ℚ :=
  rayCoeff n v +
    ∑ j ∈ Finset.Ico 1 L, pointCoeff ((tstep^[j]) n) v

/-! ## The point-mass transfer law -/

lemma tstep_eq (w : ℕ) : tstep w = if w % 2 = 0 then w / 2 else (3 * w + 1) / 2 := rfl

/-- `transfer` moves a point mass forward one shortcut step.  No positivity of
`u` is needed; only the coefficient index must be positive. -/
lemma transfer_pointCoeff (u v : ℕ) (hv : 0 < v) :
    transfer (pointCoeff u) v = pointCoeff (tstep u) v := by
  unfold transfer pointCoeff
  by_cases h3 : v % 3 = 2
  · rw [if_pos h3]
    have hc : 3 * ((2 * v - 1) / 3) = 2 * v - 1 := by omega
    by_cases h1 : 2 * v = u
    · have hne : (2 * v - 1) / 3 ≠ u := by omega
      have ht : tstep u = v := by rw [tstep_eq, if_pos (by omega)]; omega
      rw [if_pos h1, if_neg hne, ht, if_pos rfl]; ring
    · by_cases h2 : (2 * v - 1) / 3 = u
      · have ht : tstep u = v := by rw [tstep_eq, if_neg (by omega)]; omega
        rw [if_neg h1, if_pos h2, ht, if_pos rfl]; ring
      · have hne : ¬ (v = tstep u) := by rw [tstep_eq]; split <;> omega
        rw [if_neg h1, if_neg h2, if_neg hne]; ring
  · rw [if_neg h3]
    by_cases h1 : 2 * v = u
    · have ht : tstep u = v := by rw [tstep_eq, if_pos (by omega)]; omega
      rw [if_pos h1, ht, if_pos rfl]; ring
    · have hne : ¬ (v = tstep u) := by rw [tstep_eq]; split <;> omega
      rw [if_neg h1, if_neg hne]; ring

/-! ## The two transfer preimages of a dyadic ray -/

/-- The even preimage of the ray `{2^h * n}` is the ray plus the point `n/2`. -/
lemma rayCoeff_two_mul (n v : ℕ) (hn : 0 < n) :
    rayCoeff n (2 * v) = rayCoeff n v + pointCoeff n (2 * v) := by
  unfold pointCoeff
  by_cases hb : 2 * v = n
  · rw [if_pos hb, rayCoeff_eq_one hn ⟨0, by simp [hb]⟩]
    rw [rayCoeff_eq_zero (by
      rintro ⟨j, hj⟩
      have hle : n ≤ 2 ^ j * n := Nat.le_mul_of_pos_left n (by positivity)
      omega)]
    ring
  · have key : (∃ j, 2 * v = 2 ^ j * n) ↔ (∃ j, v = 2 ^ j * n) := by
      constructor
      · rintro ⟨j, hj⟩
        cases j with
        | zero => simp only [pow_zero, one_mul] at hj; exact absurd hj hb
        | succ k =>
            refine ⟨k, ?_⟩
            have : 2 * v = 2 * (2 ^ k * n) := by rw [hj, pow_succ]; ring
            omega
      · rintro ⟨j, hj⟩; exact ⟨j + 1, by rw [pow_succ, hj]; ring⟩
    rw [if_neg hb]
    by_cases hr : ∃ j, v = 2 ^ j * n
    · rw [rayCoeff_eq_one hn (key.2 hr), rayCoeff_eq_one hn hr]; ring
    · rw [rayCoeff_eq_zero (fun h => hr (key.1 h)), rayCoeff_eq_zero hr]; ring

/-- The odd preimage is odd, so it meets the ray only at the base `n`. -/
lemma rayCoeff_odd_pre (n v : ℕ) (hn : 0 < n) (h3 : v % 3 = 2) :
    rayCoeff n ((2 * v - 1) / 3) = pointCoeff n ((2 * v - 1) / 3) := by
  have hodd : ((2 * v - 1) / 3) % 2 = 1 := by omega
  unfold pointCoeff
  by_cases he : (2 * v - 1) / 3 = n
  · rw [if_pos he, rayCoeff_eq_one hn ⟨0, by simp [he]⟩]
  · rw [if_neg he]
    refine rayCoeff_eq_zero ?_
    rintro ⟨j, hj⟩
    cases j with
    | zero => simp only [pow_zero, one_mul] at hj; exact he hj
    | succ k =>
        have : (2 * v - 1) / 3 = 2 * (2 ^ k * n) := by rw [hj, pow_succ]; ring
        omega

/-- The dyadic ray through any positive base is fixed by `transfer` up to the
single point mass at `tstep n`.  The base may be even, and for `n = 1` the new
image at `2` already lies on the ray; the identity is unaffected. -/
lemma transfer_rayCoeff_eq (n v : ℕ) (hn : 0 < n) (hv : 0 < v) :
    transfer (rayCoeff n) v = rayCoeff n v + pointCoeff (tstep n) v := by
  have e1 : transfer (rayCoeff n) v = rayCoeff n v + transfer (pointCoeff n) v := by
    unfold transfer
    rw [rayCoeff_two_mul n v hn]
    by_cases h3 : v % 3 = 2
    · rw [if_pos h3, if_pos h3, rayCoeff_odd_pre n v hn h3]; ring
    · rw [if_neg h3, if_neg h3]; ring
  rw [e1, transfer_pointCoeff n v hv]

/-! ## The finite prefix -/

/-- `transfer` distributes over the ray-plus-prefix decomposition. -/
lemma transfer_orbitPrefixCoeff (n L v : ℕ) :
    transfer (orbitPrefixCoeff n L) v
      = transfer (rayCoeff n) v
        + ∑ j ∈ Finset.Ico 1 L, transfer (pointCoeff ((tstep^[j]) n)) v := by
  unfold transfer orbitPrefixCoeff
  by_cases h3 : v % 3 = 2
  · simp only [if_pos h3, Finset.sum_add_distrib]; ring
  · simp only [if_neg h3, add_zero]

lemma telescope_sub (g : ℕ → ℚ) (L : ℕ) (hL : 1 ≤ L) :
    ∑ j ∈ Finset.Ico 1 L, (g (j + 1) - g j) = g L - g 1 := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

/-! ## The frozen statement -/

/-- The entire ray and prefix have one-point transfer defect at time `L`.
No nonperiodicity or 0/1 coefficient premise belongs in this theorem. -/
theorem orbitPrefix_defect (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (v : ℕ) (hv : 0 < v) :
    transfer (orbitPrefixCoeff n L) v - orbitPrefixCoeff n L v =
      pointCoeff ((tstep^[L]) n) v := by
  have hstep : ∀ j : ℕ, transfer (pointCoeff ((tstep^[j]) n)) v
      = pointCoeff ((tstep^[(j + 1)]) n) v := by
    intro j
    rw [transfer_pointCoeff _ v hv, Function.iterate_succ_apply']
  have hsum : (∑ j ∈ Finset.Ico 1 L, transfer (pointCoeff ((tstep^[j]) n)) v)
      = ∑ j ∈ Finset.Ico 1 L, pointCoeff ((tstep^[(j + 1)]) n) v :=
    Finset.sum_congr rfl (fun j _ => hstep j)
  have htel : (∑ j ∈ Finset.Ico 1 L, pointCoeff ((tstep^[(j + 1)]) n) v)
      - ∑ j ∈ Finset.Ico 1 L, pointCoeff ((tstep^[j]) n) v
      = pointCoeff ((tstep^[L]) n) v - pointCoeff ((tstep^[1]) n) v := by
    rw [← Finset.sum_sub_distrib]
    exact telescope_sub (fun j => pointCoeff ((tstep^[j]) n) v) L hL
  have h1 : pointCoeff ((tstep^[1]) n) v = pointCoeff (tstep n) v := by
    rw [Function.iterate_one]
  rw [transfer_orbitPrefixCoeff, hsum, transfer_rayCoeff_eq n v hn hv]
  unfold orbitPrefixCoeff
  rw [h1] at htel
  linarith [htel]

/-! ## Finite controls -/

-- `L = 1` reduces to the ray formula; here the even base `n = 8` has its
-- defect at `tstep 8 = 4`.
example : transfer (orbitPrefixCoeff 8 1) 4 - orbitPrefixCoeff 8 1 4 = 1 := by
  have := orbitPrefix_defect 8 1 (by norm_num) (by norm_num) 4 (by norm_num)
  rw [this]; decide

-- The odd base `n = 3`, `L = 2`: `tstep 3 = 5`, `tstep 5 = 8`.
example : transfer (orbitPrefixCoeff 3 2) 8 - orbitPrefixCoeff 3 2 8 = 1 := by
  have := orbitPrefix_defect 3 2 (by norm_num) (by norm_num) 8 (by norm_num)
  rw [this]; decide

-- `n = 1`, `L = 3` exercises both repetition and ray overlap: the orbit is
-- `1, 2, 1, 2`, the coefficient at `2` occurs on the ray *and* in the prefix,
-- yet the defect is still a single point mass at `tstep^[3] 1 = 2`.
example : transfer (orbitPrefixCoeff 1 3) 2 - orbitPrefixCoeff 1 3 2 = 1 := by
  have := orbitPrefix_defect 1 3 (by norm_num) (by norm_num) 2 (by norm_num)
  rw [this]; decide

-- Trust-base audit: no `sorry`, no new axiom.
/-- info: 'CollatzMoonshot.Obstructions.ArithmeticLifts.orbitPrefix_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms orbitPrefix_defect

end CollatzMoonshot.Obstructions.ArithmeticLifts
