import CollatzMoonshot.FrontA.ParityReconstruction
import CollatzMoonshot.FrontA.Paradoxical
import CollatzMoonshot.Descent

/-! First coefficient crossing: a stronger remainder bound and explicit open inputs.
No coefficient stopping-time conjecture or crossing-existence theorem is assumed.
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- Every proper prefix has coefficient at least one. -/
def PrefixSupercritical (v : List Bool) : Prop :=
  ∀ u w : List Bool, v = u ++ w → w ≠ [] → 2 ^ u.length ≤ 3 ^ ones u

/-- A first-crossing numerator obeys the stronger factor-three bound.
The proof only needs the proper-prefix condition, not final subcriticality. -/
theorem three_mul_numer_le (v : List Bool) (hp : PrefixSupercritical v) :
    3 * numer v ≤ ones v * 3 ^ ones v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    have hpre : PrefixSupercritical v := by
      intro u w heq hw
      apply hp u (w ++ [b])
      · simp [heq, List.append_assoc]
      · simp
    have hbound := ih hpre
    have hlast : 2 ^ v.length ≤ 3 ^ ones v := hp v [b] rfl (by simp)
    cases b
    · simpa [numer_append_false] using hbound
    · simp only [numer_append_true, ones_append_true, pow_succ]
      nlinarith

/-- The actual first coefficient crossing; all quantifiers concern the same orbit. -/
def At (n m : ℕ) : Prop :=
  0 < m ∧ (∀ j < m, 2 ^ j ≤ 3 ^ ones (traceWord n j)) ∧
    3 ^ ones (traceWord n m) < 2 ^ m

theorem take_traceWord (n m j : ℕ) (hj : j ≤ m) :
    (traceWord n m).take j = traceWord n j := by
  induction j generalizing n m with
  | zero => simp [traceWord]
  | succ j ih =>
    cases m with
    | zero => omega
    | succ m => simpa [traceWord] using ih (tstep n) m (by omega)

theorem prefix_supercritical_trace {n m : ℕ}
    (hp : ∀ j < m, 2 ^ j ≤ 3 ^ ones (traceWord n j)) :
    PrefixSupercritical (traceWord n m) := by
  intro u w heq hw
  have hwlen : 0 < w.length := List.length_pos_iff_ne_nil.mpr hw
  have hlen : m = u.length + w.length := by
    simpa using congrArg List.length heq
  have hu : traceWord n u.length = u := by
    rw [← take_traceWord n m u.length (by omega), heq]
    simp
  simpa [hu] using hp u.length (by omega)

theorem numerator_bound {n m : ℕ} (h : At n m) :
    3 * numer (traceWord n m) ≤
      ones (traceWord n m) * 3 ^ ones (traceWord n m) :=
  three_mul_numer_le _ (prefix_supercritical_trace h.2.1)

/-- A failed descent at the first crossing forces an explicit small-start bound.
The subtraction is in naturals; final subcriticality makes it exact. -/
theorem small_start_of_not_descending {n m : ℕ} (h : At n m)
    (hsurv : n ≤ tstep^[m] n) :
    3 * (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤
      ones (traceWord n m) * 3 ^ ones (traceWord n m) := by
  have hid := tstep_iterate_identity m n
  have hprod := Nat.mul_le_mul_left (2 ^ m) hsurv
  have hsub := h.2.2
  have hnum : (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤
      numer (traceWord n m) := by
    have hsplit : 2 ^ m = (2 ^ m - 3 ^ ones (traceWord n m)) +
        3 ^ ones (traceWord n m) := by omega
    rw [hid, hsplit] at hprod
    nlinarith
  have hb := numerator_bound h
  nlinarith

/-- Open: finite coefficient crossing at every positive nontrivial start. -/
def CrossingExists : Prop := ∀ n, 2 ≤ n →
  ∃ m, 3 ^ ones (traceWord n m) < 2 ^ m

/-- Open: the coefficient-stopping-time conjecture, in finite-crossing form. -/
def StoppingCorrect : Prop := ∀ n m, 2 ≤ n → At n m → tstep^[m] n < n

theorem exists_first_crossing {n : ℕ}
    (h : ∃ m, 3 ^ ones (traceWord n m) < 2 ^ m) : ∃ m, At n m := by
  refine ⟨Nat.find h, ?_⟩
  have hs := Nat.find_spec h
  refine ⟨?_, ?_, hs⟩
  · by_contra hz
    have heq : Nat.find h = 0 := by omega
    simp [heq, traceWord] at hs
  · intro j hj
    exact Nat.le_of_not_gt (Nat.find_min h hj)

theorem conjecture_of_stoppingCorrect_and_crossingExists
    (hc : StoppingCorrect) (he : CrossingExists) : Conjecture := by
  apply conjecture_of_descent
  intro n hn
  obtain ⟨m, hm⟩ := exists_first_crossing (he n hn)
  obtain ⟨k, hk, _⟩ := exists_step_count m n
  exact ⟨k, hk ▸ hc n m hn hm⟩

end CollatzMoonshot.FrontA.FirstCrossing
