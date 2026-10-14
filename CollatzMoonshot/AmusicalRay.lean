/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalPowers

/-!
# Forward survivors on a ray: the powers of `2`

The 2026-10-14 "rayfs" agent asked whether one explicit ray holds infinitely many forward
survivors (research §34).  No ray is settled, but the question reduces to the powers of `2`.

**`not_fwdSurvivor_of_odd`.**  Odd `y > 1` has `U y < y`, so an odd ray (`5ᵏ`, …) holds no
forward survivor past its first member.

**`threeSmooth_fwdSurvivor_infinite_iff`.**  On a staircase `2^(s−b) 3^b y` the forward survivors
form an initial segment (`staircase_fwdSurvivor_iff`), so infinitely many `3`-smooth forward
survivors is the same as infinitely many forward survivors among the `2ˢ` (Ray(2)).

**`pow_two_drop_bound` (Theorem DE).**  `U y + 1 ≥ ¾ (y + 1)` on every branch, so after the climb
`2ˢ m ↦ 3ˢ m` the orbit needs `t > s · log(3/2)/log(4/3) ≈ 1.41 s` further steps to return below
`2ˢ m`.  It must consume every binary digit of `3ˢ m` first: Ray(2) is a pure late-drop question.

**`infinitelyManyOrbits_of_pow_two_orbitMin` (M2).**  Infinitely many powers of `2` that are orbit
minima give Klamkin (a).  Measured backward-survivor rate of `2ˢ`: `0.3576` (predicted `0.3553`).

**`ConjP2`.**  Every `2ˢ` is a forward survivor (BELIEVED 90%; `s ≤ 3000` pass a walk proxy, and
the Haar model expects `0.78` failures).  A single `Π⁰₁` sentence that implies Ray(2).
-/

namespace CollatzMoonshot.Amusical

/-- **Proved.**  `U` lowers every odd number above `1`. -/
theorem amusical_lt_of_odd {y : ℤ} (h1 : 1 < y) (h : Odd y) : amusical y < y := by
  obtain ⟨k, rfl⟩ := h
  unfold amusical; split_ifs <;> omega

/-- **Proved.**  An odd number above `1` is not a forward survivor. -/
theorem not_fwdSurvivor_of_odd {y : ℤ} (h1 : 1 < y) (h : Odd y) : ¬ FwdSurvivor y := by
  intro hf
  have := hf 1 le_rfl
  rw [Function.iterate_one] at this
  exact absurd (amusical_lt_of_odd h1 h) (not_lt.mpr this)

/-- **Proved (Lemma IS).**  A staircase point below the top survives iff it lies at or below the
top's forward orbit. -/
theorem staircase_fwdSurvivor_iff {y : ℤ} (hy : 0 < y) {s b : ℕ} (hb : b < s) :
    FwdSurvivor (2 ^ (s - b) * 3 ^ b * y) ↔
      ∀ t : ℕ, 2 ^ (s - b) * 3 ^ b * y ≤ amusical^[t] (3 ^ s * y) := by
  have htop : amusical^[s - b] (2 ^ (s - b) * 3 ^ b * y) = 3 ^ s * y := by
    rw [amusical_iterate_staircase y (s - b) b (s - b) le_rfl, Nat.sub_self, pow_zero, one_mul,
      show b + (s - b) = s by omega]
  constructor
  · intro hf t
    have := hf (t + (s - b)) (by omega)
    rwa [Function.iterate_add_apply, htop] at this
  · intro h
    refine staircase_fwdSurvivor hy (s - b) b ?_
    rw [show s - b + b = s by omega]
    exact h

/-- **Proved (Corollary H).**  Infinitely many `3`-smooth forward survivors iff infinitely many
powers of `2` are forward survivors. -/
theorem threeSmooth_fwdSurvivor_infinite_iff :
    {n : ℕ | (∃ a b : ℕ, n = 2 ^ a * 3 ^ b) ∧ FwdSurvivor (n : ℤ)}.Infinite ↔
      {s : ℕ | FwdSurvivor ((2 : ℤ) ^ s)}.Infinite := by
  -- a `3`-smooth forward survivor `2^a 3^b` makes `2^(a+b)` one
  have key : ∀ a b : ℕ, FwdSurvivor ((2 : ℤ) ^ a * 3 ^ b) → FwdSurvivor ((2 : ℤ) ^ (a + b)) := by
    intro a b hf
    have hall : ∀ t : ℕ, (2 : ℤ) ^ a * 3 ^ b ≤ amusical^[t] (3 ^ (a + b)) := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · intro t
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp
        · simpa using hf t ht
      · have := (staircase_fwdSurvivor_iff (y := 1) one_pos
          (show b < a + b by omega)).mp (by simpa [show a + b - b = a by omega] using hf)
        simpa [show a + b - b = a by omega] using this
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simpa using hf
    have h23 : (2 : ℤ) ^ b ≤ 3 ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
    have hle : (2 : ℤ) ^ (a + b) ≤ 2 ^ a * 3 ^ b := by
      rw [pow_add]; exact mul_le_mul_of_nonneg_left h23 (by positivity)
    have := (staircase_fwdSurvivor_iff (y := 1) one_pos (show 0 < a + b from hpos)).mpr
      (fun t => by simpa using hle.trans (hall t))
    simpa using this
  constructor
  · intro hS
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    apply hS
    refine (Set.finite_Iic (3 ^ M)).subset ?_
    rintro n ⟨⟨a, b, rfl⟩, hn⟩
    push_cast at hn
    have hab : a + b ≤ M := hM (key a b hn)
    show 2 ^ a * 3 ^ b ≤ 3 ^ M
    calc 2 ^ a * 3 ^ b ≤ 3 ^ a * 3 ^ b :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) a)
      _ = 3 ^ (a + b) := (pow_add 3 a b).symm
      _ ≤ 3 ^ M := Nat.pow_le_pow_right (by norm_num) hab
  · intro h
    have hinj : Function.Injective fun s : ℕ => 2 ^ s := Nat.pow_right_injective le_rfl
    refine (h.image hinj.injOn).mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨⟨s, 0, by simp⟩, by push_cast; exact hs⟩

/-- **Proved.**  Each step of `U` on `y ≥ 0` keeps `U y + 1 ≥ ¾ (y + 1)`. -/
theorem amusical_iterate_add_one_ge (t : ℕ) {y : ℤ} (hy : 0 ≤ y) :
    3 ^ t * (y + 1) ≤ 4 ^ t * (amusical^[t] y + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hz : 0 ≤ amusical^[t] y := by
        clear ih
        induction t with
        | zero => exact hy
        | succ k ihk => rw [Function.iterate_succ_apply']; exact amusical_nonneg ihk
      have hstep : 3 * (amusical^[t] y + 1) ≤ 4 * (amusical (amusical^[t] y) + 1) := by
        generalize amusical^[t] y = z at hz
        unfold amusical; split_ifs <;> omega
      rw [Function.iterate_succ_apply', pow_succ, pow_succ]
      have h4 : (0 : ℤ) ≤ 4 ^ t := by positivity
      nlinarith

/-- **Proved (Theorem DE).**  After the climb `2ˢ m ↦ 3ˢ m`, `t` more steps lose at most a factor
`(4/3)^t`. -/
theorem pow_two_drop_bound (s t : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    3 ^ t * (3 ^ s * m + 1) ≤ 4 ^ t * (amusical^[s + t] (2 ^ s * m) + 1) := by
  have hc : amusical^[s] (2 ^ s * m) = 3 ^ s * m := by
    have := amusical_iterate_staircase m s 0 s le_rfl
    simpa using this
  rw [add_comm s t, Function.iterate_add_apply, hc]
  exact amusical_iterate_add_one_ge t (by positivity)

/-- **Proved (M2).**  Infinitely many powers of `2` that are orbit minima imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_pow_two_orbitMin
    (h : {s : ℕ | IsOrbitMin ((2 : ℤ) ^ s)}.Infinite) : AmusicalInfinitelyManyOrbits := by
  apply amusicalInfinitelyManyOrbits_of_minima
  have hinj : Function.Injective fun s : ℕ => (2 : ℤ) ^ s :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 2)).injective
  refine (h.image hinj.injOn).mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨by positivity, hs⟩

/-- **Open (Conjecture P2, BELIEVED 90%).**  Every power of `2` is a forward survivor. -/
def ConjP2 : Prop :=
  ∀ s t : ℕ, (2 : ℤ) ^ s ≤ amusical^[t] (2 ^ s)

/-- **Proved.**  Conjecture P2 gives Ray(2). -/
theorem ray_two_of_conjP2 (h : ConjP2) : {s : ℕ | FwdSurvivor ((2 : ℤ) ^ s)}.Infinite := by
  have : {s : ℕ | FwdSurvivor ((2 : ℤ) ^ s)} = Set.univ :=
    Set.eq_univ_of_forall fun s t _ => h s t
  rw [this]
  exact Set.infinite_univ

end CollatzMoonshot.Amusical
