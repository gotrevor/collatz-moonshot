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
  sorry

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

/-- The unboundedness witnesses are valid primitive references. -/
theorem witness_admissible (p : ℕ) : Admissible (witnessA p) (witnessB p) := by
  sorry

/-- Bridge to the actual inverse basin, including the rational parity test. -/
theorem witness_reaches_neg_one (p : ℕ) :
    (rationalStep^[2 * p]) (witnessRef p) = -1 := by
  sorry

/-- Explicit lower bound; the strict inequality is true even at p=0. -/
theorem witness_weighted_gt (p : ℕ) :
    (3 : ℚ) ^ p < weightedScore 1 (witnessA p) (witnessB p) := by
  sorry

/-- Main second obstruction: unboundedness at the known positive cycle. -/
theorem weighted_witnesses_unbounded :
    ¬ BddAbove (Set.range fun p : ℕ => weightedScore 1 (witnessA p) (witnessB p)) := by
  sorry

/-- Same obstruction stated over the actual negative inverse basin of -1. -/
theorem inverse_basin_scores_unbounded :
    ¬ BddAbove {x : ℚ | ∃ a b : ℕ, Admissible a b ∧
      (∃ k : ℕ, (rationalStep^[k]) (-(a : ℚ) / (b : ℚ)) = -1) ∧
      x = weightedScore 1 a b} := by
  sorry

end CollatzMoonshot.Obstructions.NegativeShadow
