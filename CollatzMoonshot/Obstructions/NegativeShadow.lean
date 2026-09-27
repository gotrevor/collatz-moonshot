import Mathlib
import CollatzMoonshot.FrontB.Dictionary

/-!
# Negative rational shadow potentials

Faithful targets for RESEARCH-2026-09-27-negative-shadow.md.  The finite
catalog uses the existing FrontB word numerator and odd-step count.
The two general obstructions are unfinished until their proofs are supplied.
Keep the definitions and headline statements fixed during the bounded task.
-/

namespace CollatzMoonshot.Obstructions.NegativeShadow

open CollatzMoonshot.FrontB

/-- The reduced fraction `-a/b` is at most -1 and has odd denominator. -/
def Admissible (a b : ℕ) : Prop :=
  0 < b ∧ b ≤ a ∧ Odd b ∧ Nat.Coprime a b

/-- The exact potential used by the Python probe, valued in the rationals. -/
def score (n a b : ℕ) : ℚ :=
  ((b * n + a : ℕ) : ℚ) * (2 : ℚ) ^ padicValNat 2 (b * n + a) / (a : ℚ) ^ 2

def scoreValues (n : ℕ) : Set ℚ :=
  {x | ∃ a b : ℕ, Admissible a b ∧ x = score n a b}

def weightedScore (n a b : ℕ) : ℚ := (b : ℚ) * score n a b

/-- Rational shortcut Collatz map; on odd-denominator rationals numerator
parity is rational parity.  No floor or real-valued parity convention. -/
def rationalStep (x : ℚ) : ℚ :=
  if x.num % 2 = 0 then x / 2 else (3 * x + 1) / 2

def witnessA (p : ℕ) : ℕ := 2 * 4 ^ p - 3 ^ p
def witnessB (p : ℕ) : ℕ := 3 ^ p
def witnessRef (p : ℕ) : ℚ := -(witnessA p : ℚ) / (witnessB p : ℚ)

def words : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (words k).flatMap fun w => [false :: w, true :: w]

/-- Finite list, with harmless duplicates, of the reduced negative rational
periodic references represented by words of length at most depth. -/
def catalog (depth : ℕ) : List (ℕ × ℕ) :=
  ((List.range (depth + 1)).flatMap words).flatMap fun w =>
    if 2 ^ w.length < 3 ^ ones w then
      let a := numer w
      let b := 3 ^ ones w - 2 ^ w.length
      let g := Nat.gcd a b
      [(a / g, b / g)]
    else []

def catalogMax (depth n : ℕ) : ℚ :=
  (catalog depth).foldl (fun acc ab => max acc (score n ab.1 ab.2)) 0

/- Hand-computed anchors, also present in the external Python CLI suite. -/
theorem score_three_neg_one : score 3 1 1 = 16 := by native_decide
theorem score_nine_neg_five_thirds : score 9 5 3 = 1024 / 25 := by native_decide
theorem score_fourteen_neg_two : score 14 2 1 = 64 := by native_decide
theorem rational_step_neg_five_thirds : rationalStep (-5 / 3) = -2 := by native_decide
theorem word_numerator_anchor : numer [true, true, false] = 5 := by decide
theorem witness_anchor : witnessA 2 = 23 ∧ witnessB 2 = 9 := by decide

/-- A concrete refutation of the depth-10 catalog, not of every larger catalog. -/
theorem catalog_ten_six : catalogMax 10 6 = 7 := by native_decide
theorem catalog_ten_three : catalogMax 10 3 = 16 := by native_decide
theorem catalog_ten_increases : catalogMax 10 6 < catalogMax 10 (tstep 6) := by
  norm_num [tstep, catalog_ten_six, catalog_ten_three]

/-- Upper bound independent of any Collatz convergence assumption. -/
theorem score_le_square (n a b : ℕ) (hn : 0 < n) (hab : Admissible a b) :
    score n a b ≤ ((n : ℚ) + 1) ^ 2 := by
  obtain ⟨hb, hba, _, _⟩ := hab
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hq0 : 0 < b * n + a := by omega
  have hpow : 2 ^ padicValNat 2 (b * n + a) ≤ b * n + a :=
    Nat.le_of_dvd hq0 pow_padicValNat_dvd
  have hqle : b * n + a ≤ a * (n + 1) := by
    have : b * n ≤ a * n := Nat.mul_le_mul_right n hba
    have : a * (n + 1) = a * n + a := by ring
    omega
  have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hqQ : (0 : ℚ) < ((b * n + a : ℕ) : ℚ) := by exact_mod_cast hq0
  have hpowQ : (2 : ℚ) ^ padicValNat 2 (b * n + a) ≤ ((b * n + a : ℕ) : ℚ) := by
    calc (2 : ℚ) ^ padicValNat 2 (b * n + a)
        = ((2 ^ padicValNat 2 (b * n + a) : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((b * n + a : ℕ) : ℚ) := by exact_mod_cast hpow
  have hqleQ : ((b * n + a : ℕ) : ℚ) ≤ (a : ℚ) * ((n : ℚ) + 1) := by
    have := (Nat.cast_le (α := ℚ)).2 hqle
    push_cast at this ⊢
    linarith
  rw [score, div_le_iff₀ (by positivity)]
  have hmul : ((b * n + a : ℕ) : ℚ) * (2 : ℚ) ^ padicValNat 2 (b * n + a)
      ≤ ((b * n + a : ℕ) : ℚ) * ((b * n + a : ℕ) : ℚ) := by
    exact mul_le_mul_of_nonneg_left hpowQ hqQ.le
  have hsq : ((b * n + a : ℕ) : ℚ) * ((b * n + a : ℕ) : ℚ)
      ≤ ((n : ℚ) + 1) ^ 2 * (a : ℚ) ^ 2 := by
    have hn1 : (0 : ℚ) ≤ (n : ℚ) + 1 := by positivity
    nlinarith [hqleQ, hqQ.le, haQ.le]
  linarith

/-- Evaluating the score when the shifted numerator is an exact power of two. -/
theorem score_of_pow (n a b k : ℕ) (h : b * n + a = 2 ^ k) :
    score n a b = ((2 : ℚ) ^ k) ^ 2 / (a : ℚ) ^ 2 := by
  unfold score
  rw [h, padicValNat.prime_pow]
  push_cast
  ring

/-- Sharpness construction.  For every `n ≥ 1` and every target `M` there is an
admissible pair with `b ≥ M`, `a = b + d` for a small remainder `d`, and
`b * n + a` an exact power of two. -/
theorem exists_dyadic_ref (n M : ℕ) (hn : 0 < n) :
    ∃ a b d k : ℕ, Admissible a b ∧ M ≤ b ∧ d < 2 * (n + 1) ∧ a = b + d ∧
      b * n + a = 2 ^ k := by
  have hc0 : 0 < n + 1 := by omega
  set k := (M + 2) * (n + 1) with hkdef
  set Q := 2 ^ k with hQdef
  have hQge : (M + 2) * (n + 1) ≤ Q := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  set m := Q / (n + 1) with hmdef
  have hmge : M + 2 ≤ m := (Nat.le_div_iff_mul_le hc0).2 hQge
  set b := 2 * ((m - 1) / 2) + 1 with hbdef
  have hbm : b ≤ m := by omega
  have hbm' : m ≤ b + 1 := by omega
  have hbM : M ≤ b := by omega
  have hb1 : 0 < b := by omega
  have hbc : b * (n + 1) ≤ Q :=
    le_trans (Nat.mul_le_mul_right (n + 1) hbm) (Nat.div_mul_le_self Q (n + 1))
  refine ⟨b + (Q - b * (n + 1)), b, Q - b * (n + 1), k, ?_, hbM, ?_, rfl, ?_⟩
  · -- admissibility
    refine ⟨hb1, Nat.le_add_right _ _, ⟨(m - 1) / 2, by omega⟩, ?_⟩
    have hsum : b * n + (b + (Q - b * (n + 1))) = 2 ^ k := by
      have : b * (n + 1) = b * n + b := by ring
      omega
    have h2b : ¬ (2 ∣ b) := by omega
    have hcb : Nat.Coprime b (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2b).symm
    have hga : Nat.gcd (b + (Q - b * (n + 1))) b ∣ 2 ^ k := by
      rw [← hsum]
      exact Nat.dvd_add ((Nat.gcd_dvd_right _ b).mul_right n) (Nat.gcd_dvd_left _ b)
    have hgb : Nat.gcd (b + (Q - b * (n + 1))) b ∣ b := Nat.gcd_dvd_right _ b
    exact Nat.eq_one_of_dvd_coprimes hcb hgb hga
  · -- remainder bound
    have hmod : m * (n + 1) + Q % (n + 1) = Q := by
      rw [hmdef, Nat.mul_comm]
      exact Nat.div_add_mod Q (n + 1)
    have hr : Q % (n + 1) < n + 1 := Nat.mod_lt _ hc0
    have h1 : m * (n + 1) ≤ b * (n + 1) + (n + 1) := by
      calc m * (n + 1) ≤ (b + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) hbm'
        _ = b * (n + 1) + (n + 1) := by ring
    omega
  · have : b * (n + 1) = b * n + b := by ring
    omega

/-- The elementary inequality behind sharpness: once `B` is large enough relative
to a target `y` strictly below `C^2`, the exact score `P^2/A^2` exceeds `y`. -/
theorem score_sharp_arith {y B C D A P : ℚ} (hy : 0 < y) (hC : 0 < C) (hB : 1 ≤ B)
    (hD0 : 0 ≤ D) (hD : D < 2 * C) (hA : A = B + D) (hP : B * C + D = P)
    (hbig : 4 * y * C + 4 * y * C ^ 2 < B * (C ^ 2 - y)) : y * A ^ 2 < P ^ 2 := by
  have hB0 : (0 : ℚ) < B := by linarith
  have e1 : B * (4 * y * C + 4 * y * C ^ 2) < B * (B * (C ^ 2 - y)) :=
    mul_lt_mul_of_pos_left hbig hB0
  have hpc : (0 : ℚ) ≤ 4 * y * C ^ 2 := by positivity
  have e2 : 4 * y * C ^ 2 * 1 ≤ 4 * y * C ^ 2 * B := mul_le_mul_of_nonneg_left hB hpc
  have e3 : y * B ^ 2 + 4 * y * C * B + 4 * y * C ^ 2 < B ^ 2 * C ^ 2 := by linarith [e1, e2]
  have f1 : B * D < B * (2 * C) := mul_lt_mul_of_pos_left hD hB0
  have f2 : (0 : ℚ) < (2 * C - D) * (2 * C + D) := mul_pos (by linarith) (by linarith)
  have e4 : A ^ 2 < B ^ 2 + 4 * B * C + 4 * C ^ 2 := by
    rw [hA]; linarith [f1, f2]
  have e5 : y * A ^ 2 < y * (B ^ 2 + 4 * B * C + 4 * C ^ 2) := mul_lt_mul_of_pos_left e4 hy
  have g1 : (0 : ℚ) ≤ B * C * D := by positivity
  have e6 : B ^ 2 * C ^ 2 ≤ P ^ 2 := by
    rw [← hP]; linarith [g1, sq_nonneg D]
  linarith [e3, e5, e6]

/-- Main first obstruction: the all-rational envelope is exactly elementary. -/
theorem scoreValues_isLUB (n : ℕ) (hn : 0 < n) :
    IsLUB (scoreValues n) (((n : ℚ) + 1) ^ 2) := by
  constructor
  · rintro x ⟨a, b, hab, rfl⟩
    exact score_le_square n a b hn hab
  · intro y hy
    by_contra hcon
    rw [not_le] at hcon
    have hcpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    rcases le_or_gt y 0 with hy0 | hy0
    · have hmem : score n 1 1 ∈ scoreValues n :=
        ⟨1, 1, ⟨Nat.one_pos, le_refl 1, odd_one, Nat.coprime_one_left 1⟩, rfl⟩
      have hle := hy hmem
      have hnum : (0 : ℚ) < ((1 * n + 1 : ℕ) : ℚ) := by
        have : 0 < 1 * n + 1 := by omega
        exact_mod_cast this
      have hpos : 0 < score n 1 1 := by
        unfold score
        apply div_pos (mul_pos hnum (by positivity))
        norm_num
      linarith
    · obtain ⟨N, hN⟩ := exists_nat_gt
        ((4 * y * ((n : ℚ) + 1) + 4 * y * ((n : ℚ) + 1) ^ 2) / (((n : ℚ) + 1) ^ 2 - y))
      have heps : (0 : ℚ) < ((n : ℚ) + 1) ^ 2 - y := by linarith
      have hNe : 4 * y * ((n : ℚ) + 1) + 4 * y * ((n : ℚ) + 1) ^ 2
          < (N : ℚ) * (((n : ℚ) + 1) ^ 2 - y) := by
        rw [div_lt_iff₀ heps] at hN
        linarith
      obtain ⟨a, b, d, k, hab, hbN, hdlt, hadd, hsum⟩ := exists_dyadic_ref n N hn
      have hbpos : 0 < b := hab.1
      have hapos : 0 < a := lt_of_lt_of_le hab.1 hab.2.1
      have haQ0 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast hapos
      have hbQ1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hbpos
      have hbQN : (N : ℚ) ≤ (b : ℚ) := by exact_mod_cast hbN
      have hdQ0 : (0 : ℚ) ≤ (d : ℚ) := by positivity
      have hdQ : (d : ℚ) < 2 * ((n : ℚ) + 1) := by
        have := (Nat.cast_lt (α := ℚ)).2 hdlt
        push_cast at this
        linarith
      have haQ : (a : ℚ) = (b : ℚ) + (d : ℚ) := by exact_mod_cast hadd
      have hsumQ : (b : ℚ) * ((n : ℚ) + 1) + (d : ℚ) = (2 : ℚ) ^ k := by
        have h : b * (n + 1) + d = 2 ^ k := by
          have : b * (n + 1) = b * n + b := by ring
          omega
        have h2 : ((b * (n + 1) + d : ℕ) : ℚ) = ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast h
        push_cast at h2
        linarith
      have hle := hy (⟨a, b, hab, rfl⟩ : score n a b ∈ scoreValues n)
      rw [score_of_pow n a b k hsum, div_le_iff₀ (by positivity)] at hle
      have hstep1 : (N : ℚ) * (((n : ℚ) + 1) ^ 2 - y) ≤ (b : ℚ) * (((n : ℚ) + 1) ^ 2 - y) :=
        mul_le_mul_of_nonneg_right hbQN heps.le
      exact absurd hle (not_le.2 (score_sharp_arith hy0 hcpos hbQ1 hdQ0 hdQ haQ hsumQ
        (lt_of_lt_of_le hNe hstep1)))

/-- No choice of these exact envelope values is nonincreasing above 1. -/
theorem envelope_not_nonincreasing :
    ¬ ∃ V : ℕ → ℚ,
      (∀ n, 0 < n → IsLUB (scoreValues n) (V n)) ∧
      (∀ n, 1 < n → V (tstep n) ≤ V n) := by
  rintro ⟨V, hlub, hmono⟩
  have h3 : V 3 = 16 := by
    have h := (hlub 3 (by norm_num)).unique (scoreValues_isLUB 3 (by norm_num))
    rw [h]; norm_num
  have h5 : V 5 = 36 := by
    have h := (hlub 5 (by norm_num)).unique (scoreValues_isLUB 5 (by norm_num))
    rw [h]; norm_num
  have hm := hmono 3 (by norm_num)
  rw [show tstep 3 = 5 from by decide, h3, h5] at hm
  norm_num at hm

theorem witnessB_pos (p : ℕ) : 0 < witnessB p := pow_pos (by norm_num) p

theorem witness_three_le_four (p : ℕ) : 3 ^ p ≤ 4 ^ p := Nat.pow_le_pow_left (by norm_num) p

theorem witnessA_pos (p : ℕ) : 0 < witnessA p := by
  have h := witness_three_le_four p
  have h3 : 0 < 3 ^ p := pow_pos (by norm_num) p
  unfold witnessA
  omega

/-- `b + a = 2^(2p+1)`: the sum is an exact power of two. -/
theorem witness_sum (p : ℕ) : witnessB p + witnessA p = 2 ^ (2 * p + 1) := by
  have h := witness_three_le_four p
  have hpow : 2 ^ (2 * p + 1) = 2 * 4 ^ p := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  unfold witnessA witnessB
  omega

theorem witnessB_le_witnessA (p : ℕ) : witnessB p ≤ witnessA p := by
  have h := witness_three_le_four p
  have h3 : 0 < 3 ^ p := pow_pos (by norm_num) p
  unfold witnessA witnessB
  omega

theorem witnessB_odd (p : ℕ) : Odd (witnessB p) := by
  unfold witnessB
  exact Odd.pow (by decide)

theorem witness_coprime (p : ℕ) : Nat.Coprime (witnessA p) (witnessB p) := by
  have hnd : ¬ (3 ∣ witnessA p) := by
    intro hd
    have hs := witness_sum p
    have h3p : (3 : ℕ) ∣ 3 ^ p ∨ p = 0 := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exact Or.inr h
      · exact Or.inl (dvd_pow_self 3 (by omega))
    rcases h3p with h3p | h0
    · have hd2 : (3 : ℕ) ∣ 2 ^ (2 * p + 1) := by
        have hB : (3 : ℕ) ∣ witnessB p := by unfold witnessB; exact h3p
        omega
      have hp3 : Nat.Prime 3 := by norm_num
      have := Nat.Prime.dvd_of_dvd_pow hp3 hd2
      omega
    · subst h0
      unfold witnessA at hd
      norm_num at hd
  have hcop3 : Nat.Coprime 3 (witnessA p) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hnd
  unfold witnessB
  exact Nat.Coprime.pow_right p hcop3.symm

/-- The unboundedness witnesses are valid primitive references. -/
theorem witness_admissible (p : ℕ) : Admissible (witnessA p) (witnessB p) :=
  ⟨witnessB_pos p, witnessB_le_witnessA p, witnessB_odd p, witness_coprime p⟩

theorem witnessA_odd (p : ℕ) : witnessA p % 2 = 1 := by
  have h := witness_three_le_four p
  have h3 : 3 ^ p % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
  unfold witnessA
  omega

theorem witnessA_cast (p : ℕ) : (witnessA p : ℚ) = 2 * 4 ^ p - 3 ^ p := by
  have h : 3 ^ p ≤ 2 * 4 ^ p := by have := witness_three_le_four p; omega
  unfold witnessA
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem witnessB_cast (p : ℕ) : (witnessB p : ℚ) = 3 ^ p := by
  unfold witnessB; push_cast; ring

theorem witnessB_ne_zero (p : ℕ) : ((witnessB p : ℚ)) ≠ 0 := by
  have := witnessB_pos p
  positivity

/-- The reference is already in lowest terms, so its numerator is `-(A p)`. -/
theorem witnessRef_num (p : ℕ) : (witnessRef p).num = -(witnessA p : ℤ) := by
  have hB : (0 : ℤ) < (witnessB p : ℤ) := by exact_mod_cast witnessB_pos p
  have hcop : Nat.Coprime (-(witnessA p : ℤ)).natAbs ((witnessB p : ℤ)).natAbs := by
    simpa using witness_coprime p
  have h : witnessRef p = ((-(witnessA p : ℤ) : ℤ) : ℚ) / (((witnessB p : ℤ)) : ℚ) := by
    unfold witnessRef; push_cast; ring
  rw [h]
  exact Rat.num_div_eq_of_coprime hB hcop

/-- Doubling keeps the fraction reduced, because the denominator is odd. -/
theorem witnessRef_double_num (p : ℕ) :
    (2 * witnessRef p).num = -(2 * witnessA p : ℤ) := by
  have hB : (0 : ℤ) < (witnessB p : ℤ) := by exact_mod_cast witnessB_pos p
  have hodd : Nat.Coprime 2 (witnessB p) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
      have h3 : witnessB p % 2 = 1 := Nat.odd_iff.1 (witnessB_odd p)
      omega)
  have hcop : Nat.Coprime (-(2 * witnessA p : ℤ)).natAbs ((witnessB p : ℤ)).natAbs := by
    simpa [Int.natAbs_mul] using Nat.Coprime.mul_left hodd (witness_coprime p)
  have h : 2 * witnessRef p = ((-(2 * witnessA p : ℤ) : ℤ) : ℚ) / (((witnessB p : ℤ)) : ℚ) := by
    unfold witnessRef; push_cast; ring
  rw [h]
  exact Rat.num_div_eq_of_coprime hB hcop

/-- One odd step takes the level-`p+1` reference to twice the level-`p` reference. -/
theorem witness_step_odd (p : ℕ) :
    rationalStep (witnessRef (p + 1)) = 2 * witnessRef p := by
  have hnum : (witnessRef (p + 1)).num % 2 ≠ 0 := by
    have := witnessA_odd (p + 1)
    rw [witnessRef_num]
    omega
  unfold rationalStep
  rw [if_neg hnum]
  unfold witnessRef
  rw [witnessA_cast, witnessB_cast, witnessA_cast, witnessB_cast]
  have h3 : (3 : ℚ) ^ p ≠ 0 := by positivity
  field_simp
  ring

/-- The following even step removes the doubling. -/
theorem witness_step_even (p : ℕ) :
    rationalStep (2 * witnessRef p) = witnessRef p := by
  have hnum : (2 * witnessRef p).num % 2 = 0 := by
    rw [witnessRef_double_num]
    omega
  unfold rationalStep
  rw [if_pos hnum]
  ring

/-- Bridge to the actual inverse basin, including the rational parity test. -/
theorem witness_reaches_neg_one (p : ℕ) :
    (rationalStep^[2 * p]) (witnessRef p) = -1 := by
  induction p with
  | zero =>
      norm_num [witnessRef, witnessA, witnessB]
  | succ p ih =>
      have hstep : rationalStep^[2] (witnessRef (p + 1)) = witnessRef p := by
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
        rw [witness_step_odd, witness_step_even]
      have hsplit : 2 * (p + 1) = 2 * p + 2 := by ring
      rw [hsplit, Function.iterate_add_apply, hstep, ih]

/-- Explicit lower bound; the strict inequality is true even at p=0. -/
theorem witness_weighted_closed (p : ℕ) :
    weightedScore 1 (witnessA p) (witnessB p)
      = (3 : ℚ) ^ p * ((2 : ℚ) ^ (2 * p + 1)) ^ 2 / (witnessA p : ℚ) ^ 2 := by
  have hA : (0 : ℚ) < (witnessA p : ℚ) := by exact_mod_cast witnessA_pos p
  have hsum : witnessB p * 1 + witnessA p = 2 ^ (2 * p + 1) := by
    rw [Nat.mul_one]; exact witness_sum p
  unfold weightedScore score
  rw [hsum, padicValNat.prime_pow]
  have hB : ((witnessB p : ℕ) : ℚ) = (3 : ℚ) ^ p := by
    unfold witnessB; push_cast; ring
  rw [hB]
  push_cast
  ring

theorem witness_weighted_gt (p : ℕ) :
    (3 : ℚ) ^ p < weightedScore 1 (witnessA p) (witnessB p) := by
  have hA : (0 : ℚ) < (witnessA p : ℚ) := by exact_mod_cast witnessA_pos p
  have hlt : (witnessA p : ℚ) < (2 : ℚ) ^ (2 * p + 1) := by
    have h3 : 0 < 3 ^ p := pow_pos (by norm_num) p
    have : witnessA p < 2 ^ (2 * p + 1) := by
      have := witness_sum p
      have hb : 0 < witnessB p := witnessB_pos p
      omega
    calc (witnessA p : ℚ) < ((2 ^ (2 * p + 1) : ℕ) : ℚ) := by exact_mod_cast this
      _ = (2 : ℚ) ^ (2 * p + 1) := by push_cast; ring
  have h3p : (0 : ℚ) < (3 : ℚ) ^ p := by positivity
  have hsq : (witnessA p : ℚ) ^ 2 < ((2 : ℚ) ^ (2 * p + 1)) ^ 2 := by nlinarith
  rw [witness_weighted_closed, lt_div_iff₀ (by positivity)]
  exact mul_lt_mul_of_pos_left hsq h3p

/-- Main second obstruction: unboundedness at the known positive cycle. -/
theorem weighted_witnesses_unbounded :
    ¬ BddAbove (Set.range fun p : ℕ => weightedScore 1 (witnessA p) (witnessB p)) := by
  rintro ⟨y, hy⟩
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt (y : ℚ) (by norm_num : (1 : ℚ) < 3)
  have hmem : weightedScore 1 (witnessA p) (witnessB p)
      ∈ Set.range fun p : ℕ => weightedScore 1 (witnessA p) (witnessB p) := ⟨p, rfl⟩
  have := hy hmem
  have := witness_weighted_gt p
  linarith

/-- Same obstruction stated over the actual negative inverse basin of -1. -/
theorem inverse_basin_scores_unbounded :
    ¬ BddAbove {x : ℚ | ∃ a b : ℕ, Admissible a b ∧
      (∃ k : ℕ, (rationalStep^[k]) (-(a : ℚ) / (b : ℚ)) = -1) ∧
      x = weightedScore 1 a b} := by
  intro hbdd
  refine weighted_witnesses_unbounded (hbdd.mono ?_)
  rintro x ⟨p, rfl⟩
  exact ⟨witnessA p, witnessB p, witness_admissible p,
    ⟨2 * p, witness_reaches_neg_one p⟩, rfl⟩

end CollatzMoonshot.Obstructions.NegativeShadow
