/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.ArithmeticLifts

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

open CollatzMoonshot.FrontB

/-- Equality of products of two odd-edge generators, after cancellation of
the common leading term.  Positivity and oddness are separate hypotheses. -/
def pairRel (a b c d : ℤ) : Prop :=
  (3 * (a + b) + 1) * c * d = a * b * (3 * (c + d) + 1)

private theorem smaller_factor_bound (D A c d M : ℤ)
    (hD : 0 < D) (hc : 0 < c) (hcd : c ≤ d)
    (h : D * c * d = 3 * A * (c + d) + A)
    (hm : 3 * A ≤ D * M) (hmq : 6 * A * M + A < D * M ^ 2) : c < M := by
  by_contra hn
  have hMc : M ≤ c := by omega
  have hdc : 0 ≤ d - c := by omega
  have hfac : 0 ≤ D * c - 3 * A := by nlinarith
  have hprod := mul_nonneg hdc hfac
  have hdiff : 0 ≤ c - M := by omega
  have hfac2 : 0 ≤ D * c + D * M - 6 * A := by nlinarith
  have hprod2 := mul_nonneg hdiff hfac2
  nlinarith

/-- Every unordered two-factor replacement involving 7 in the two displayed
triples fixes that pair.  This quantifies over all positive integer labels,
not over a bounded experimental search. -/
theorem pair_seven_frozen (v c d : ℤ)
    (hv : v = 53 ∨ v = 65 ∨ v = 133 ∨ v = 247)
    (hc : 0 < c) (hcd : c ≤ d) (h : pairRel 7 v c d) : c = 7 ∧ d = v := by
  have hvpos : 0 < v := by rcases hv with h | h | h | h <;> omega
  have heq : (3 * v + 22) * c * d = 21 * v * (c + d) + 7 * v := by
    unfold pairRel at h
    nlinarith [h]
  have hb : c < 15 := smaller_factor_bound (3 * v + 22) (7 * v) c d 15
    (by omega) hc hcd (by nlinarith [heq]) (by nlinarith) (by nlinarith)
  rcases hv with rfl | rfl | rfl | rfl <;>
    interval_cases c <;> norm_num at heq ⊢ <;> omega

/-- The only positive odd sorted pairs with product r_65*r_133 are (53,247)
and (65,133).  Together with pair_seven_frozen this closes the two-state
quadratic component containing {7,65,133}. -/
theorem high_pair_fiber (c d : ℤ) (hc : 0 < c) (hcd : c ≤ d)
    (hcodd : c % 2 = 1) (hdodd : d % 2 = 1)
    (h : 17 * c * d = 741 * (c + d) + 247) :
    (c = 53 ∧ d = 247) ∨ (c = 65 ∧ d = 133) := by
  have hb : c < 88 := smaller_factor_bound 17 247 c d 88
    (by norm_num) hc hcd (by nlinarith [h]) (by norm_num) (by norm_num)
  interval_cases c <;> norm_num at h ⊢ <;> omega

theorem high_pair_equations (c d : ℤ) :
    (pairRel 65 133 c d ↔ 17 * c * d = 741 * (c + d) + 247) ∧
    (pairRel 53 247 c d ↔ 17 * c * d = 741 * (c + d) + 247) := by
  unfold pairRel
  constructor <;> constructor <;> intro h <;> nlinarith

theorem short_units_and_cubic_exchange :
    certificateValue 3 [19,25,29,55,83] = 1 ∧
    certificateValue 5 [5,7,7,11,17,55,65,83] = 1 ∧
    certificateValue 0 [35,53] = certificateValue 0 [25,133] ∧
    certificateValue 0 [7,65,133] = certificateValue 0 [13,19,29] ∧
    certificateValue 0 [7,65,133] = (247 : ℚ) / 880 ∧
    certificateValue 6 [7,11,17,13,5] = 7 ∧ (tstep^[11]) 7 = 1 := by
  native_decide

/-- The unit-count vectors (3,5) and (5,8) span the full integer lattice.
This removes every additive count-only invariant, without claiming that
the corresponding substitutions are available at every nonnegative state. -/
theorem unit_count_lattice (t k : ℤ) :
    3 * (-8 * t + 5 * k) + 5 * (5 * t - 3 * k) = t ∧
    5 * (-8 * t + 5 * k) + 8 * (5 * t - 3 * k) = k := by
  constructor <;> ring

/-- The interval 5/8 <= r_u < 2/3 leaves just this possible short odd unit
count after removing r_1.  The remaining triple case is excluded separately
in the paper argument; this theorem asserts only the exact count reduction. -/
theorem short_odd_unit_count_reduction :
    ∀ t ∈ Finset.range 13, ∀ k ∈ Finset.range 13,
      0 < k → t + k < 13 → (t + k) % 2 = 1 →
      (2 : ℚ)^t * (5/8 : ℚ)^k ≤ 1 →
      1 < (2 : ℚ)^t * (2/3 : ℚ)^k → t = 2 ∧ k = 3 := by
  native_decide


abbrev Triple := ℤ × ℤ × ℤ

def sortTriple (a b c : ℤ) : Triple :=
  (min (min a b) c, max (min a b) (min (max a b) c), max (max a b) c)

/-- The coordinate held fixed, followed by the two coordinates replaced. -/
def pairSlot (s : Triple) (i : Fin 3) : Triple :=
  match i.val with
  | 0 => (s.1, s.2.1, s.2.2)
  | 1 => (s.2.1, s.1, s.2.2)
  | _ => (s.2.2, s.1, s.2.1)

/-- An arbitrary positive-odd two-factor substitution, sorted afterwards.
There is no bound on replacement labels or on the number of substitutions. -/
def QuadraticStep (s t : Triple) : Prop :=
  ∃ (i : Fin 3) (c d : ℤ), 0 < c ∧ c ≤ d ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
    pairRel (pairSlot s i).2.1 (pairSlot s i).2.2 c d ∧
    t = sortTriple (pairSlot s i).1 c d

inductive QuadraticReach : Triple → Triple → Prop where
  | refl (s) : QuadraticReach s s
  | tail {s t u} : QuadraticReach s t → QuadraticStep t u → QuadraticReach s u

theorem cubic_component_closed {s t : Triple}
    (hs : s = (7,65,133) ∨ s = (7,53,247)) (h : QuadraticStep s t) :
    t = (7,65,133) ∨ t = (7,53,247) := by
  obtain ⟨i,c,d,hc,hcd,hco,hdo,hp,rfl⟩ := h
  rcases hs with rfl | rfl
  · fin_cases i
    · have heq := (high_pair_equations c d).1.mp hp
      rcases high_pair_fiber c d hc hcd hco hdo heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        norm_num [pairSlot, sortTriple]
    · obtain ⟨rfl,rfl⟩ := pair_seven_frozen 133 c d (by omega) hc hcd hp
      norm_num [pairSlot, sortTriple]
    · obtain ⟨rfl,rfl⟩ := pair_seven_frozen 65 c d (by omega) hc hcd hp
      norm_num [pairSlot, sortTriple]
  · fin_cases i
    · have heq := (high_pair_equations c d).2.mp hp
      rcases high_pair_fiber c d hc hcd hco hdo heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        norm_num [pairSlot, sortTriple]
    · obtain ⟨rfl,rfl⟩ := pair_seven_frozen 247 c d (by omega) hc hcd hp
      norm_num [pairSlot, sortTriple]
    · obtain ⟨rfl,rfl⟩ := pair_seven_frozen 53 c d (by omega) hc hcd hp
      norm_num [pairSlot, sortTriple]

theorem cubic_component_reachable {s t : Triple} (h : QuadraticReach s t)
    (hs : s = (7,65,133) ∨ s = (7,53,247)) :
    t = (7,65,133) ∨ t = (7,53,247) := by
  induction h with
  | refl => exact hs
  | tail h step ih => exact cubic_component_closed ih step

/-- A true neutral cubic exchange cannot be synthesized by any finite
sequence of two-odd-factor exchanges, regardless of intermediate height. -/
theorem cubic_exchange_not_quadratic :
    ¬ QuadraticReach (7,65,133) (13,19,29) := by
  intro h
  have hc := cubic_component_reachable h (Or.inl rfl)
  norm_num at hc

end CollatzMoonshot.Obstructions.ArithmeticLifts
