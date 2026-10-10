/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

namespace CollatzMoonshot.Benchmark.ArcCarryCompatibility

/-- The integer successor before reduction modulo the memory period. -/
def carryNext (r J : ℤ) : ℤ := (3 * r - r % 2) / 2 + J

/-- Equal low two residue bits give equal next parities exactly when the move floors
have equal parity.  Thus comparing delay labels numerically is unnecessary. -/
theorem next_parity_eq_iff_floor_parity_eq (r s J K : ℤ)
    (hrs : r % 4 = s % 4) :
    carryNext r J % 2 = carryNext s K % 2 ↔ J % 2 = K % 2 := by
  unfold carryNext
  omega

/-- At memory at least three, the two possible next residues have the same low two bits. -/
theorem child_lifts_agree_mod_four (k : ℕ) (hk : 3 ≤ k) (r : ℤ) :
    (r + 2 ^ (k - 1)) % 4 = r % 4 := by
  have he : k - 1 = 2 + (k - 3) := by omega
  rw [he, pow_add]
  norm_num

/-- A faithful translation of a delay strategy must satisfy this test: if its two
top-bit children are represented by the two residue lifts, and prescribe the same
following parity, their chosen move floors must have equal parity.  Either matching
of the two children is permitted.  This is a necessary local condition on a specified
translation, not an exclusion of alternative strategies or encodings using more states. -/
theorem sibling_floors_must_agree (k : ℕ) (hk : 3 ≤ k) (r J K : ℤ)
    (hp : carryNext r J % 2 = carryNext (r + 2 ^ (k - 1)) K % 2) :
    J % 2 = K % 2 := by
  exact (next_parity_eq_iff_floor_parity_eq r (r + 2 ^ (k - 1)) J K
    (child_lifts_agree_mod_four k hk r).symm).mp hp

/-- Opposite floor parities at the sibling states obstruct that faithful translation. -/
theorem opposite_sibling_floors_obstruct (k : ℕ) (hk : 3 ≤ k) (r J K : ℤ)
    (hJK : J % 2 ≠ K % 2) :
    carryNext r J % 2 ≠ carryNext (r + 2 ^ (k - 1)) K % 2 := by
  intro hp
  exact hJK (sibling_floors_must_agree k hk r J K hp)

/-- The k>=3 restriction matters: at k=2, changing the residue lift can cancel an odd
floor change.  This is a hand-computed positive control for the obstruction's scope. -/
theorem two_bit_control : carryNext 0 0 % 2 = carryNext 2 1 % 2 := by decide

/-- A rational open interval of starts on which a witness supplies a particular floor. -/
structure FloorPiece where
  word : ℕ
  floor : ℤ
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def floorParitiesAt (pieces : List FloorPiece) (w : ℕ) (a : ℚ) : List ℤ :=
  (pieces.filter fun p => p.word == w && decide (p.lo < a ∧ a < p.hi)).map
    fun p => p.floor % 2

def siblingConflictAt (k : ℕ) (pieces : List FloorPiece) (w : ℕ) (a : ℚ) : Bool :=
  let left := floorParitiesAt pieces w a
  let right := floorParitiesAt pieces (w + 2 ^ (k - 1)) a
  !left.isEmpty && !right.isEmpty && !(left.any fun j => right.contains j)

/-- Exact finite diagnostic: inspect a midpoint between every consecutive distinct
cover endpoint.  The floor options are constant within each such open interval.
Boundary starts and translation over more than one step are outside this diagnostic. -/
def witnessHasSiblingConflict (k : ℕ) (pieces : List FloorPiece) : Bool :=
  (List.range (2 ^ (k - 1))).any fun w =>
    let relevant := pieces.filter fun p => p.word == w || p.word == w + 2 ^ (k - 1)
    let cuts := (relevant.flatMap fun p => [p.lo, p.hi]).mergeSort (fun a b => a ≤ b)
    (cuts.zip cuts.tail).any fun xy =>
      decide (xy.1 < xy.2) && siblingConflictAt k pieces w ((xy.1 + xy.2) / 2)

/-- Hand-computed positive control: at a=3/8, the siblings force opposite floors. -/
theorem sibling_test_positive : witnessHasSiblingConflict 3
    [⟨0, 0, 0, 1⟩, ⟨4, 1, 1/4, 3/4⟩] = true := by native_decide

/-- Adding an even-floor option removes the conflict everywhere. -/
theorem sibling_test_alternative : witnessHasSiblingConflict 3
    [⟨0, 0, 0, 1⟩, ⟨4, 1, 1/4, 3/4⟩, ⟨4, 2, 1/4, 3/4⟩] = false := by native_decide

theorem start_tenth_forces_floor_zero (u : ℝ) (hu : (1 : ℝ) / 10 ≤ u)
    (hw : u + 2 * (31 / 100 : ℝ) / 3 ≤ 1 / 10 + 31 / 100) :
    ⌊3 * u / 2⌋ = 0 := by
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num <;> linarith

theorem start_seventeen_twentyfifths_forces_floor_one (u : ℝ)
    (hu : (17 : ℝ) / 25 ≤ u)
    (hw : u + 2 * (31 / 100 : ℝ) / 3 ≤ 17 / 25 + 31 / 100) :
    ⌊3 * u / 2⌋ = 1 := by
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num <;> linarith

/-- Necessary condition for a fraction-independent encoding of delay word zero:
its assigned residue fixes A, and its fixed two child words fix the successor base B.
We retain only the window-fit condition, allowing more moves than the actual arc game. -/
def FixedChildBaseRealization (h A B : ℕ) (P : Set ℝ) : Prop :=
  ∀ a ∈ P, ∃ u : ℝ, a ≤ u ∧ u + 2 * (31 / 100 : ℝ) / 3 ≤ a + 31 / 100 ∧
    (A + ⌊3 * u / 2⌋.toNat) % h = B

/-- Two starts in the same delay word rule out every fixed choice of residue and child
base.  The surviving possibility is an encoding that also depends on position. -/
theorem two_starts_preclude_fixed_child_base (h A B : ℕ) (hh : 2 ≤ h) (P : Set ℝ)
    (hlo : (1 : ℝ) / 10 ∈ P) (hhi : (17 : ℝ) / 25 ∈ P) :
    ¬ FixedChildBaseRealization h A B P := by
  intro hP
  obtain ⟨u, hu, hw, hb0⟩ := hP _ hlo
  obtain ⟨v, hv, hvw, hb1⟩ := hP _ hhi
  rw [start_tenth_forces_floor_zero u hu hw] at hb0
  rw [start_seventeen_twentyfifths_forces_floor_one v hv hvw] at hb1
  norm_num at hb0 hb1
  have hlt : A % h < h := Nat.mod_lt A (by omega)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < h by omega)] at hb1
  by_cases hs : A % h + 1 < h
  · rw [Nat.mod_eq_of_lt hs] at hb1
    omega
  · have he : A % h + 1 = h := by omega
    rw [he, Nat.mod_self] at hb1
    omega

/-- Control: with just the low start, a fixed-base assignment exists. -/
theorem single_start_fixed_base_control :
    FixedChildBaseRealization 32 0 0 {((1 : ℝ) / 10)} := by
  intro a ha
  have ha' : a = (1 : ℝ) / 10 := ha
  subst a
  refine ⟨1 / 10, le_rfl, by norm_num, ?_⟩
  norm_num

end CollatzMoonshot.Benchmark.ArcCarryCompatibility
