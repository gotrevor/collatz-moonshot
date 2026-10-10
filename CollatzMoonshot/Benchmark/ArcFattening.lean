/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcTrap

namespace CollatzMoonshot.Benchmark.ArcFattening

/-- Real-coordinate version of the two-child game.  The finite-memory interpretation uses
a set periodic with period 2^k and child displacement h = 2^(k-1).  Equivalence with
ArcTrap.KRelaxedStrategy, including normalization across integers, is not proved here. -/
def LiftedStrategy (s t l h : ℝ) (P : Set ℝ) : Prop :=
  0 < l ∧ ∀ x ∈ P, ∃ v : ℝ, x ≤ v ∧ v + 2 * l / 3 ≤ x + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ v ∧ v + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b : ℕ, b < 2 → 3 * v / 2 + b * h ∈ P

/-- Increase window width by e, shift centers accordingly, and allow a start interval
of radius e/6 around each shifted old start. -/
def fatten (e : ℝ) (P : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ P, ∃ z : ℝ, |z| ≤ e / 6 ∧ y = x - e / 2 + z}

/-- Widening the arc by e/3 at each end makes every real-coordinate strategy robust.
The selected move v-e/3 lands exactly at the center of each fattened successor fiber.
This changes the parameters; it does not establish liveness at the original arc. -/
theorem LiftedStrategy.fatten {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    LiftedStrategy (s - e / 3) (t + 2 * e / 3) (l + e) h (fatten e P) := by
  refine ⟨by linarith [hP.1], ?_⟩
  rintro y ⟨x, hx, z, hz, rfl⟩
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨v, hv1, hv2, ⟨j, hj1, hj2⟩, hv⟩ := hP.2 x hx
  refine ⟨v - e / 3, by linarith, by linarith,
    ⟨j, by linarith, by linarith⟩, ?_⟩
  intro b hb
  exact ⟨3 * v / 2 + b * h, hv b hb, 0, by simp; positivity, by ring⟩

/-- A live fattened strategy has an interval of starts whenever e>0. -/
theorem fatten_contains_interval {e x : ℝ} {P : Set ℝ} (hx : x ∈ P) :
    Set.Icc (x - 2 * e / 3) (x - e / 3) ⊆ fatten e P := by
  intro y hy
  refine ⟨x, hx, y - x + e / 2, ?_, by ring⟩
  rw [abs_le]
  constructor <;> linarith [hy.1, hy.2]

/-- Fattening preserves translation invariance, so the period required by a finite-memory
encoding is not lost.  The separate encoding equivalence is still needed. -/
theorem fatten_translation {e M : ℝ} {P : Set ℝ}
    (hP : ∀ x ∈ P, x + M ∈ P) :
    ∀ y ∈ fatten e P, y + M ∈ fatten e P := by
  rintro y ⟨x, hx, z, hz, rfl⟩
  exact ⟨x + M, hP x hx, z, hz, by ring⟩

/-- A smaller fattening whose starts and successor landings admit uniform move margins. -/
def fattenCore (e : ℝ) (P : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ P, ∃ z : ℝ, |z| ≤ e / 12 ∧ y = x - e / 2 + z}

/-- Robust interface for a future rounded-solver inclusion proof.  Every core start has
an entire interval of legal moves of radius e/24.  Each child is within e/16 of a core
center, leaving e/48 before the core boundary at radius e/12.  For e>0 these margins
are strictly positive.  Neither residue encoding nor lattice rounding is asserted here. -/
theorem LiftedStrategy.robust_fatten {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    ∀ y ∈ fattenCore e P, ∃ v : ℝ, ∀ q : ℝ, |q| ≤ e / 24 →
      y ≤ v + q ∧ v + q + 2 * (l + e) / 3 ≤ y + (l + e) ∧
      (∃ j : ℤ, (j : ℝ) + (s - e / 2) ≤ v + q ∧
        v + q + 2 * (l + e) / 3 ≤ j + (s - e / 2) + (t + e)) ∧
      ∀ b : ℕ, b < 2 → ∃ x ∈ P,
        |3 * (v + q) / 2 + b * h - (x - e / 2)| ≤ e / 16 := by
  rintro y ⟨x, hx, z, hz, rfl⟩
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨v, hv1, hv2, ⟨j, hj1, hj2⟩, hv⟩ := hP.2 x hx
  refine ⟨v - e / 3, ?_⟩
  intro q hq
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  refine ⟨by linarith, by linarith, ⟨j, by linarith, by linarith⟩, ?_⟩
  intro b hb
  refine ⟨3 * v / 2 + b * h, hv b hb, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- In particular, the core itself is a strategy on the widened arc. -/
theorem LiftedStrategy.fattenCore {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    LiftedStrategy (s - e / 2) (t + e) (l + e) h (fattenCore e P) := by
  refine ⟨by linarith [hP.1], ?_⟩
  intro y hy
  obtain ⟨v, hv⟩ := hP.robust_fatten he y hy
  obtain ⟨hv1, hv2, hj, hb⟩ := hv 0 (by simp; positivity)
  simp only [add_zero] at hv1 hv2 hj hb
  refine ⟨v, hv1, hv2, hj, ?_⟩
  intro b hb'
  obtain ⟨x, hx, hdist⟩ := hb b hb'
  exact ⟨x, hx, 3 * v / 2 + b * h - (x - e / 2), by linarith, by ring⟩

/-- Read the integer residue of a physical start using Euclidean remainder, also for
negative starts. -/
noncomputable def residue (k : ℕ) (x : ℝ) : ℕ := (⌊x⌋ % (2 ^ k : ℤ)).toNat

/-- Integer-coordinate decomposition behind the residue bridge, valid also at negative m. -/
theorem physical_child_decomposition (m : ℤ) (u : ℝ) :
    3 * ((m : ℝ) + u) / 2 =
      (3 * u / 2 + ((m % 2 : ℤ) : ℝ) / 2) + (((3 * m - m % 2) / 2 : ℤ) : ℝ) := by
  have hm : 2 * ((3 * m - m % 2) / 2) = 3 * m - m % 2 := by omega
  have hmr : (2 : ℝ) * (((3 * m - m % 2) / 2 : ℤ) : ℝ) =
      3 * (m : ℝ) - ((m % 2 : ℤ) : ℝ) := by exact_mod_cast hm
  linarith

/-- Physical and normalized moves have the same successor fractional coordinate. -/
theorem physical_child_fract (m : ℤ) (u : ℝ) :
    Int.fract (3 * ((m : ℝ) + u) / 2) =
      Int.fract (3 * u / 2 + ((m % 2 : ℤ) : ℝ) / 2) := by
  rw [physical_child_decomposition, Int.fract_add_intCast]

/-- The physical successor floor is the sum used in the residue transition. -/
theorem physical_child_floor (m : ℤ) (u : ℝ) :
    ⌊3 * ((m : ℝ) + u) / 2⌋ =
      ⌊3 * u / 2 + ((m % 2 : ℤ) : ℝ) / 2⌋ + (3 * m - m % 2) / 2 := by
  rw [physical_child_decomposition, Int.floor_add_intCast]

/-- Changing the integer representative by 2*h*q changes its successor integer carry
by 3*h*q.  This is the arithmetic underlying the two-lift permutation. -/
theorem integer_carry_shift (m h q : ℤ) :
    (3 * (m + 2 * h * q) - (m + 2 * h * q) % 2) / 2 =
      (3 * m - m % 2) / 2 + 3 * h * q := by
  have hp : (m + 2 * h * q) % 2 = m % 2 := by
    simp [Int.add_emod, Int.mul_emod]
  rw [hp]
  rw [show 3 * (m + 2 * h * q) - m % 2 =
    (3 * m - m % 2) + (3 * h * q) * 2 by ring]
  exact Int.add_mul_ediv_right _ _ (by decide)

/-- In particular the successor base modulo h is independent of the integer representative. -/
theorem integer_carry_shift_mod (m h q : ℤ) :
    ((3 * (m + 2 * h * q) - (m + 2 * h * q) % 2) / 2) % h =
      ((3 * m - m % 2) / 2) % h := by
  rw [integer_carry_shift]
  simp [Int.add_emod, Int.mul_emod]

/-- The two residues spaced by h are precisely the two lifts of the base modulo h. -/
theorem residue_pair_lifts (A h : ℤ) (hh : 0 < h) :
    ({A % (2 * h), (A + h) % (2 * h)} : Set ℤ) = {A % h, A % h + h} := by
  let z := A % (2 * h)
  have hz0 : 0 ≤ z := Int.emod_nonneg _ (by omega)
  have hz2 : z < 2 * h := Int.emod_lt_of_pos _ (by omega)
  have hzmod : z % h = A % h := Int.emod_emod_of_dvd A ⟨2, by ring⟩
  have hshift : (A + h) % (2 * h) = (z + h) % (2 * h) := by
    simp only [Int.add_emod, z, Int.emod_emod]
  rcases lt_or_ge z h with hzh | hzh
  · have hb : A % h = z := by rw [← hzmod, Int.emod_eq_of_lt hz0 hzh]
    have hc : (A + h) % (2 * h) = z + h := by
      rw [hshift, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hb, hc]
  · have hb : A % h = z - h := by
      calc
        A % h = z % h := hzmod.symm
        _ = ((z - h) + h) % h := by congr 1 <;> ring
        _ = (z - h) % h := by simp
        _ = z - h := Int.emod_eq_of_lt (by omega) (by omega)
    have hc : (A + h) % (2 * h) = z - h := by
      rw [hshift, show z + h = (z - h) + 2 * h by ring, Int.add_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hb, hc, sub_add_cancel]
    exact Set.pair_comm _ _

/-- Shared bridge interface: the physical children are the two lifts of the canonical
residue's successor base, as an unordered pair.  Taking h=2^(k-1) gives the memory game. -/
theorem children_are_lifts (m J h : ℤ) (hh : 0 < h) :
    let r := m % (2 * h)
    let base := ((3 * r - r % 2) / 2 + J) % h
    ({((3 * m - m % 2) / 2 + J) % (2 * h),
      ((3 * m - m % 2) / 2 + J + h) % (2 * h)} : Set ℤ) = {base, base + h} := by
  dsimp only
  have he : m % (2 * h) + 2 * h * (m / (2 * h)) = m :=
    Int.emod_add_mul_ediv _ _
  have hc := integer_carry_shift_mod (m % (2 * h)) h (m / (2 * h))
  rw [he] at hc
  have hb : ((3 * m - m % 2) / 2 + J) % h =
      ((3 * (m % (2 * h)) - m % (2 * h) % 2) / 2 + J) % h := by
    simp only [Int.add_emod, Int.emod_emod, hc]
  rw [residue_pair_lifts _ h hh, hb]

/-- Periodic real-coordinate realization of a family of fractional start sets. -/
def physicalize (k : ℕ) (P : ℕ → Set ℝ) : Set ℝ :=
  {x | Int.fract x ∈ P (residue k x)}

/-- Project a physical strategy to integer residues and fractional starts. -/
def residualize (k : ℕ) (P : Set ℝ) (r : ℕ) : Set ℝ :=
  {a | ∃ x ∈ P, residue k x = r ∧ Int.fract x = a}

/-- The physical realization is invariant under any integer multiple of its memory period. -/
theorem physicalize_shift (k : ℕ) (P : ℕ → Set ℝ) (x : ℝ) (q : ℤ) :
    x + (((2 ^ k : ℤ) * q : ℤ) : ℝ) ∈ physicalize k P ↔ x ∈ physicalize k P := by
  simp only [physicalize, Set.mem_setOf_eq, residue]
  rw [Int.fract_add_intCast, Int.floor_add_intCast]
  simp [Int.add_emod, Int.mul_emod]

/-- Every physical point projects to a valid memory residue. -/
theorem residue_lt (k : ℕ) (x : ℝ) : residue k x < 2 ^ k := by
  have hm : 0 ≤ ⌊x⌋ % (2 ^ k : ℤ) := Int.emod_nonneg _ (by positivity)
  unfold residue
  rw [Int.toNat_lt hm]
  exact_mod_cast Int.emod_lt_of_pos ⌊x⌋ (show (0 : ℤ) < 2 ^ k by positivity)

/-- Projection satisfies the fractional-domain restriction required by KRelaxedStrategy. -/
theorem residualize_subset (k : ℕ) (P : Set ℝ) (r : ℕ) :
    residualize k P r ⊆ Set.Ico 0 1 := by
  rintro a ⟨x, hx, hr, rfl⟩
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- A live physical set stays live after projecting to memory residues. -/
theorem residualize_live {k : ℕ} {P : Set ℝ} (hne : P.Nonempty) :
    ∃ r < 2 ^ k, (residualize k P r).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨residue k x, residue_lt k x, Int.fract x, x, hx, rfl, rfl⟩

/-- A valid fractional start embeds at its canonical integer representative. -/
theorem mem_physicalize_of_mem {k r : ℕ} {P : ℕ → Set ℝ} {a : ℝ}
    (hr : r < 2 ^ k) (ha : a ∈ P r) (ha01 : a ∈ Set.Ico 0 1) :
    (r : ℝ) + a ∈ physicalize k P := by
  have hfloor : ⌊(r : ℝ) + a⌋ = (r : ℤ) := by
    rw [show (r : ℝ) = ((r : ℤ) : ℝ) by simp, Int.floor_intCast_add,
      Int.floor_eq_zero_iff.mpr ha01, add_zero]
  have hfract : Int.fract ((r : ℝ) + a) = a := by
    rw [add_comm, show (r : ℝ) = ((r : ℤ) : ℝ) by simp,
      Int.fract_add_intCast, Int.fract_eq_self.mpr ha01]
  have hres : residue k ((r : ℝ) + a) = r := by
    simp only [residue, hfloor]
    norm_cast
    simp [Nat.mod_eq_of_lt hr]
  change Int.fract ((r : ℝ) + a) ∈ P (residue k ((r : ℝ) + a))
  simpa only [hfract, hres] using ha

/-- A live family of valid fractional starts has a live physical realization. -/
theorem physicalize_live {k : ℕ} {P : ℕ → Set ℝ}
    (hP : ∀ r, P r ⊆ Set.Ico 0 1) (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    (physicalize k P).Nonempty := by
  obtain ⟨r, hr, a, ha⟩ := hne
  exact ⟨(r : ℝ) + a, mem_physicalize_of_mem hr ha (hP r ha)⟩

/-- Open bridge, reviewed by Opus on 2026-10-10; confidence 92%, not a theorem.
The key arithmetic is that replacing m by m+2^k*q adds 3*2^(k-1)*q to floor(3m/2),
so the two children are permuted modulo 2^k.  k>=1 is essential. -/
def KToLiftedBridge : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k →
    ArcTrap.KRelaxedStrategy s t l k P →
    LiftedStrategy s t l (2 ^ (k - 1)) (physicalize k P)

/-- Open converse bridge; confidence 92%, not a theorem.  No periodicity assumption
is proposed: each physical witness supplies a move and both projected children. -/
def LiftedToKBridge : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : Set ℝ), 1 ≤ k →
    LiftedStrategy s t l (2 ^ (k - 1)) P →
    ArcTrap.KRelaxedStrategy s t l k (residualize k P)

end CollatzMoonshot.Benchmark.ArcFattening
