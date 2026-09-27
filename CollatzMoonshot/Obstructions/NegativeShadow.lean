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

/-- Main first obstruction: the all-rational envelope is exactly elementary. -/
theorem scoreValues_isLUB (n : ℕ) (hn : 0 < n) :
    IsLUB (scoreValues n) (((n : ℚ) + 1) ^ 2) := by
  sorry

/-- No choice of these exact envelope values is nonincreasing above 1. -/
theorem envelope_not_nonincreasing :
    ¬ ∃ V : ℕ → ℚ,
      (∀ n, 0 < n → IsLUB (scoreValues n) (V n)) ∧
      (∀ n, 1 < n → V (tstep n) ≤ V n) := by
  sorry

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
    · have : (3 : ℕ) ∣ 2 ^ (2 * p + 1) := by
        have : witnessB p + witnessA p = 2 ^ (2 * p + 1) := hs
        have hB : (3 : ℕ) ∣ witnessB p := by unfold witnessB; exact h3p
        omega
      have hp3 : Nat.Prime 3 := by norm_num
      have := (Nat.Prime.dvd_of_dvd_pow hp3 this)
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

/-- Bridge to the actual inverse basin, including the rational parity test. -/
theorem witness_reaches_neg_one (p : ℕ) :
    (rationalStep^[2 * p]) (witnessRef p) = -1 := by
  sorry

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
  sorry

end CollatzMoonshot.Obstructions.NegativeShadow
