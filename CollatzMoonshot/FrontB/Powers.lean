/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontB.Words

/-!
# Word powers, and the degeneracy they expose 🧨

A parity word traversed `j` times - the concatenation `wpow v j = v ++ v ++ ⋯ ++ v` -
encodes **the same rational cycle** as `v`: the value `numer v / den v` is invariant
under powering (`numer_wpow_mul_den`), so integrality and triviality transfer both ways
(`integerCycle_wpow_iff`, `isTrivial_wpow_iff`), while

* the circuit count **telescopes**: `circuits (wpow v j) = j * circuits v`, and
* the denominator **explodes**: `j ≤ den (wpow v j)` once `1 ≤ den v`.

Consequence (drawn in `Threads.lean`): one nontrivial integral word manufactures
nontrivial integral words of arbitrarily large circuit count and denominator.  Any
board statement of the shape "∃ bound over *all* nontrivial integral words" is therefore
**equivalent to Front B itself** - no reduction at all.  The honest targets quantify over
`Primitive` words (not a proper power), and every nonempty word decomposes over one
(`exists_primitive_root`), which is what the repaired wiring in `Threads.lean` runs on.

Probed numerically before proving (exhaustive `k ≤ 8` plus random long words), including
the negative mirror: powers of the `−17` cycle's word `[t,t,t,t,f,t,t,t,f,f,f]` keep
`den ∣ numer` while `circuits` telescopes `2, 4, 6, …` - the mechanism is sign-blind.
-/

namespace CollatzMoonshot.FrontB

/-! ## The power of a word -/

/-- `v` concatenated with itself `j` times: the cycle traversed `j` times. -/
def wpow (v : List Bool) : ℕ → List Bool
  | 0 => []
  | j + 1 => v ++ wpow v j

@[simp] theorem wpow_zero (v : List Bool) : wpow v 0 = [] := rfl

theorem wpow_succ (v : List Bool) (j : ℕ) : wpow v (j + 1) = v ++ wpow v j := rfl

@[simp] theorem wpow_one (v : List Bool) : wpow v 1 = v := by
  simp [wpow]

@[simp] theorem wpow_nil : ∀ j, wpow ([] : List Bool) j = []
  | 0 => rfl
  | j + 1 => by simp [wpow, wpow_nil j]

theorem wpow_add (v : List Bool) (m n : ℕ) :
    wpow v (m + n) = wpow v m ++ wpow v n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, wpow_succ, wpow_succ, ih, List.append_assoc]

theorem wpow_wpow (v : List Bool) (i j : ℕ) : wpow (wpow v i) j = wpow v (i * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [wpow_succ, ih, show i * (j + 1) = i + i * j by ring, wpow_add]

@[simp] theorem length_wpow (v : List Bool) (j : ℕ) :
    (wpow v j).length = j * v.length := by
  induction j with
  | zero => simp
  | succ j ih => rw [wpow_succ, List.length_append, ih]; ring

theorem wpow_ne_nil {v : List Bool} (hv : v ≠ []) {j : ℕ} (hj : 1 ≤ j) :
    wpow v j ≠ [] := by
  have h1 : 0 < v.length := List.length_pos_iff.mpr hv
  have : 0 < (wpow v j).length := by rw [length_wpow]; exact Nat.mul_pos hj h1
  exact List.length_pos_iff.mp this

/-! ## `ones`, `numer`, `den` of appends and powers -/

theorem ones_append (u w : List Bool) : ones (u ++ w) = ones u + ones w := by
  induction u with
  | nil => simp [ones]
  | cons b t ih =>
    cases b
    · simp [ones, ih]
    · simp [ones, ih]
      omega

@[simp] theorem ones_wpow (v : List Bool) (j : ℕ) : ones (wpow v j) = j * ones v := by
  induction j with
  | zero => simp
  | succ j ih => rw [wpow_succ, ones_append, ih]; ring

/-- The append formula: appending `w` shifts every one of `u` past all of `w`'s positions
(the `2 ^ u.length` weight on `numer w`) and under all of `w`'s ones (the `3 ^ ones w`
weight on `numer u`). -/
theorem numer_append (u w : List Bool) :
    numer (u ++ w) = 3 ^ ones w * numer u + 2 ^ u.length * numer w := by
  induction u with
  | nil => simp [numer]
  | cons b t ih =>
    cases b <;>
      simp only [List.cons_append, numer, ih, ones_append, List.length_cons,
        pow_succ, pow_add] <;> ring

/-- `den` of a power, in the form the algebra wants: with `A = 2 ^ |v|` and
`B = 3 ^ ones v`, powering sends `A - B` to `A^j - B^j`. -/
theorem den_wpow (v : List Bool) (j : ℕ) :
    den (wpow v j) = ((2 : ℤ) ^ v.length) ^ j - ((3 : ℤ) ^ ones v) ^ j := by
  simp only [den, length_wpow, ones_wpow]
  rw [Nat.mul_comm j v.length, Nat.mul_comm j (ones v), pow_mul, pow_mul]

/-- **The value identity**: powering preserves the cycle's rational value
`numer v / den v`, in fraction-free form.  The whole degeneracy flows from this. -/
theorem numer_wpow_mul_den (v : List Bool) (j : ℕ) :
    (numer (wpow v j) : ℤ) * den v = (numer v : ℤ) * den (wpow v j) := by
  induction j with
  | zero => simp [den]
  | succ j ih =>
    have hn : (numer (wpow v (j + 1)) : ℤ) =
        ((3 : ℤ) ^ ones v) ^ j * numer v + (2 : ℤ) ^ v.length * numer (wpow v j) := by
      rw [wpow_succ, numer_append]
      push_cast
      rw [ones_wpow, Nat.mul_comm j (ones v), pow_mul]
    have hdv : den v = (2 : ℤ) ^ v.length - (3 : ℤ) ^ ones v := rfl
    rw [hn, den_wpow, hdv]
    rw [den_wpow, hdv] at ih
    linear_combination (2 : ℤ) ^ v.length * ih

/-! ## Positivity and nonvanishing of `den` under powers -/

theorem den_pos_iff_lt {v : List Bool} :
    0 < den v ↔ (3 : ℤ) ^ ones v < (2 : ℤ) ^ v.length := by
  simp only [den]
  exact sub_pos

theorem den_wpow_pos {v : List Bool} (hd : 0 < den v) {j : ℕ} (hj : 1 ≤ j) :
    0 < den (wpow v j) := by
  rw [den_wpow]
  have hAB := den_pos_iff_lt.mp hd
  have h3 : (0 : ℤ) ≤ 3 ^ ones v := by positivity
  have := pow_lt_pow_left₀ hAB h3 (Nat.one_le_iff_ne_zero.mp hj)
  linarith

theorem den_pos_of_den_wpow_pos {v : List Bool} {j : ℕ}
    (hd : 0 < den (wpow v j)) : 0 < den v := by
  by_contra h
  push Not at h
  have hle : (2 : ℤ) ^ v.length ≤ (3 : ℤ) ^ ones v := by
    simp only [den] at h; linarith
  have h2 : (0 : ℤ) ≤ 2 ^ v.length := by positivity
  have := pow_le_pow_left₀ h2 hle j
  rw [den_wpow] at hd
  linarith

theorem den_wpow_ne_zero {v : List Bool} (hd : den v ≠ 0) (j : ℕ) :
    den (wpow v j) ≠ 0 ∨ j = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact Or.inr rfl
  refine Or.inl ?_
  rw [den_wpow]
  have hj' : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj
  have h2 : (0 : ℤ) ≤ 2 ^ v.length := by positivity
  have h3 : (0 : ℤ) ≤ 3 ^ ones v := by positivity
  rcases lt_trichotomy ((2 : ℤ) ^ v.length) ((3 : ℤ) ^ ones v) with h | h | h
  · have := pow_lt_pow_left₀ h h2 hj'
    intro hzero; linarith
  · exact absurd (by simp only [den]; exact sub_eq_zero_of_eq h) hd
  · have := pow_lt_pow_left₀ h h3 hj'
    intro hzero; linarith

/-- The denominator of a power **explodes**: `j ≤ den (wpow v j)` once `1 ≤ den v`.
(Step: `A^(j+1) − B^(j+1) = A·(A^j − B^j) + B^j·(A − B)`, and each summand helps.) -/
theorem le_den_wpow {v : List Bool} (hd : 1 ≤ den v) (j : ℕ) :
    (j : ℤ) ≤ den (wpow v j) := by
  have hdv : den v = (2 : ℤ) ^ v.length - (3 : ℤ) ^ ones v := rfl
  have hA : (1 : ℤ) ≤ 2 ^ v.length := one_le_pow₀ (by norm_num)
  have hB : (1 : ℤ) ≤ 3 ^ ones v := one_le_pow₀ (by norm_num)
  induction j with
  | zero => simp [den]
  | succ j ih =>
    have hBj : (1 : ℤ) ≤ (3 ^ ones v : ℤ) ^ j := one_le_pow₀ hB
    have hstep : den (wpow v (j + 1)) =
        (2 : ℤ) ^ v.length * den (wpow v j) + ((3 : ℤ) ^ ones v) ^ j * den v := by
      rw [den_wpow, den_wpow, hdv]; ring
    have hnonneg : (0 : ℤ) ≤ den (wpow v j) := le_trans (by positivity) ih
    have h1 : den (wpow v j) ≤ (2 : ℤ) ^ v.length * den (wpow v j) :=
      le_mul_of_one_le_left hnonneg hA
    have h2 : (1 : ℤ) ≤ ((3 : ℤ) ^ ones v) ^ j * den v := by nlinarith [hBj, hd]
    push_cast
    linarith

/-! ## Transfer: integrality and triviality are power-invariant -/

/-- The engine for both transfers: the member value `c` is the same on `v` and on any
power of `v` (both denominators nonzero). -/
theorem value_eq_iff {v : List Bool} {j : ℕ} (c : ℤ)
    (hdv : den v ≠ 0) (hdw : den (wpow v j) ≠ 0) :
    (numer (wpow v j) : ℤ) = c * den (wpow v j) ↔ (numer v : ℤ) = c * den v := by
  have hkey := numer_wpow_mul_den v j
  constructor
  · intro h
    rw [h] at hkey
    -- c * D_j * D₁ = W * D_j  →  cancel D_j
    have : (c * den v) * den (wpow v j) = (numer v : ℤ) * den (wpow v j) := by
      linear_combination hkey
    exact (mul_right_cancel₀ hdw this).symm
  · intro h
    rw [h] at hkey
    -- n_j * D₁ = c * D₁ * D_j  →  cancel D₁
    have : (numer (wpow v j) : ℤ) * den v = (c * den (wpow v j)) * den v := by
      linear_combination hkey
    exact mul_right_cancel₀ hdv this

theorem integerCycle_wpow_iff {v : List Bool} {j : ℕ} (hj : 1 ≤ j) :
    IntegerCycle (wpow v j) ↔ IntegerCycle v := by
  constructor
  · rintro ⟨hne, hx, hd, hdvd⟩
    have hv : v ≠ [] := by rintro rfl; simp at hne
    have hdv : 0 < den v := den_pos_of_den_wpow_pos hd
    have hx' : 1 ≤ ones v := by
      rcases Nat.eq_zero_or_pos (ones v) with h0 | h0
      · rw [ones_wpow, h0, Nat.mul_zero] at hx
        omega
      · exact h0
    refine ⟨hv, hx', hdv, ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    have := (value_eq_iff c (ne_of_gt hdv) (ne_of_gt hd)).mp (by rw [hc]; ring)
    exact ⟨c, by rw [this]; ring⟩
  · rintro ⟨hne, hx, hd, hdvd⟩
    refine ⟨wpow_ne_nil hne hj, ?_, den_wpow_pos hd hj, ?_⟩
    · rw [ones_wpow]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · obtain ⟨c, hc⟩ := hdvd
      have hdw : 0 < den (wpow v j) := den_wpow_pos hd hj
      have := (value_eq_iff c (ne_of_gt hd) (ne_of_gt hdw)).mpr (by rw [hc]; ring)
      exact ⟨c, by rw [this]; ring⟩

theorem isTrivial_wpow_iff {v : List Bool} (hdv : den v ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    IsTrivial (wpow v j) ↔ IsTrivial v := by
  have hdw : den (wpow v j) ≠ 0 := by
    rcases den_wpow_ne_zero hdv j with h | h
    · exact h
    · omega
  have e1 : ∀ w : List Bool, ((numer w : ℤ) = den w) ↔ ((numer w : ℤ) = 1 * den w) := by
    intro w; rw [one_mul]
  unfold IsTrivial
  rw [e1 v, e1 (wpow v j)]
  exact or_congr (value_eq_iff 1 hdv hdw) (value_eq_iff 2 hdv hdw)

/-! ## The circuit count telescopes -/

/-- The cyclic adjacency pairs of a word, linearized: `cpairs z f` pairs each letter with
its successor, the last letter with the sentinel `f`.  With `f := head z` this is exactly
`z.zip (rot z)`. -/
def cpairs : List Bool → Bool → List (Bool × Bool)
  | [], _ => []
  | [a], f => [(a, f)]
  | a :: b :: t, f => (a, b) :: cpairs (b :: t) f

theorem zip_tail_sentinel (f : Bool) :
    ∀ z : List Bool, z ≠ [] → z.zip (z.tail ++ [f]) = cpairs z f
  | [], h => absurd rfl h
  | [a], _ => rfl
  | a :: b :: t, _ => by
    have ih := zip_tail_sentinel f (b :: t) (by simp)
    simp only [List.tail_cons] at ih ⊢
    rw [List.cons_append, List.zip_cons_cons, ih, cpairs]

theorem zip_rot_eq_cpairs (b : Bool) (t : List Bool) :
    (b :: t).zip (rot (b :: t)) = cpairs (b :: t) b := by
  have h : rot (b :: t) = (b :: t).tail ++ [b] := rfl
  rw [h, zip_tail_sentinel b (b :: t) (by simp)]

theorem cpairs_append (c : Bool) (s : List Bool) (f : Bool) :
    ∀ u : List Bool, cpairs (u ++ c :: s) f = cpairs u c ++ cpairs (c :: s) f
  | [] => by simp [cpairs]
  | [a] => by simp [cpairs]
  | a :: b :: t => by
    have ih := cpairs_append c s f (b :: t)
    simp only [List.cons_append] at ih ⊢
    rw [cpairs, ih, cpairs, List.cons_append]

/-- `circuits` through the linearized pairs, sentinel = head. -/
theorem circuits_cons (b : Bool) (t : List Bool) :
    circuits (b :: t) = ((cpairs (b :: t) b).countP fun q => q.1 && !q.2) := by
  simp only [circuits]
  rw [zip_rot_eq_cpairs]

/-- **The telescope**: traversing the cycle `j` times crosses each falling edge `j`
times. -/
theorem circuits_wpow (b : Bool) (t : List Bool) :
    ∀ j : ℕ, circuits (wpow (b :: t) j) = j * circuits (b :: t)
  | 0 => by simp [circuits, rot]
  | 1 => by simp
  | j + 2 => by
    have ih := circuits_wpow b t (j + 1)
    have hshape : wpow (b :: t) (j + 2) = (b :: t) ++ (b :: (t ++ wpow (b :: t) j)) := by
      rw [wpow_succ, wpow_succ]
      simp
    have hshape' : wpow (b :: t) (j + 1) = b :: (t ++ wpow (b :: t) j) := by
      rw [wpow_succ, List.cons_append]
    rw [hshape, show ((b :: t) ++ (b :: (t ++ wpow (b :: t) j))) =
      b :: (t ++ (b :: (t ++ wpow (b :: t) j))) from rfl, circuits_cons,
      show (b :: (t ++ (b :: (t ++ wpow (b :: t) j)))) =
        ((b :: t) ++ (b :: (t ++ wpow (b :: t) j))) from rfl,
      cpairs_append, List.countP_append, ← circuits_cons, ← circuits_cons,
      ← hshape', ih]
    ring

/-! ## A nontrivial integral word has a falling edge -/

theorem ones_eq_countP (v : List Bool) : ones v = v.countP id := by
  induction v with
  | nil => rfl
  | cons b t ih => cases b <;> simp [ones, ih]

theorem countP_fst_zip_rot (v : List Bool) :
    ((v.zip (rot v)).countP fun q => q.1) = ones v := by
  have h : (v.zip (rot v)).map Prod.fst = v :=
    List.map_fst_zip (by simp)
  have h2 := List.countP_map (p := id) (f := Prod.fst (β := Bool)) (l := v.zip (rot v))
  rw [h] at h2
  rw [ones_eq_countP, h2]
  rfl

theorem countP_snd_zip_rot (v : List Bool) :
    ((v.zip (rot v)).countP fun q => q.2) = ones v := by
  have h : (v.zip (rot v)).map Prod.snd = rot v :=
    List.map_snd_zip (by simp)
  have h2 := List.countP_map (p := id) (f := Prod.snd (α := Bool)) (l := v.zip (rot v))
  rw [h] at h2
  rw [← ones_rot v, ones_eq_countP, h2]
  rfl

/-- Around a cycle, rises equal falls: pointwise `[q.1] − [q.2] = [q.1 ∧ ¬q.2] − [¬q.1 ∧ q.2]`. -/
theorem countP_balance (l : List (Bool × Bool)) :
    (l.countP fun q => q.1) + (l.countP fun q => !q.1 && q.2) =
    (l.countP fun q => q.2) + (l.countP fun q => q.1 && !q.2) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, b⟩ := q
    cases a <;> cases b <;> simp <;> omega

/-- The falling-edge count equals the rising-edge count on any cyclic word. -/
theorem countP_ft_eq_circuits (v : List Bool) :
    ((v.zip (rot v)).countP fun q => !q.1 && q.2) = circuits v := by
  have hb := countP_balance (v.zip (rot v))
  rw [countP_fst_zip_rot, countP_snd_zip_rot] at hb
  simp only [circuits]
  omega

/-- A word containing both letters has two unequal cyclic neighbours. -/
theorem exists_ne_cpair :
    ∀ (z : List Bool) (f : Bool), true ∈ z → false ∈ z →
      ∃ q ∈ cpairs z f, q.1 ≠ q.2
  | [], _, ht, _ => absurd ht (by simp)
  | [a], _, ht, hf => by
    simp only [List.mem_singleton] at ht hf
    rw [← ht] at hf
    exact absurd hf (by simp)
  | a :: b :: t, f, ht, hf => by
    by_cases hab : a = b
    · subst hab
      have ht' : true ∈ a :: t := by
        simp only [List.mem_cons] at ht ⊢
        tauto
      have hf' : false ∈ a :: t := by
        simp only [List.mem_cons] at hf ⊢
        tauto
      obtain ⟨q, hq, hne⟩ := exists_ne_cpair (a :: t) f ht' hf'
      refine ⟨q, ?_, hne⟩
      show q ∈ (a, a) :: cpairs (a :: t) f
      exact List.mem_cons_of_mem _ hq
    · refine ⟨(a, b), ?_, by simpa using hab⟩
      show (a, b) ∈ (a, b) :: cpairs (b :: t) f
      simp

theorem true_mem_of_ones_pos {v : List Bool} (h : 1 ≤ ones v) : true ∈ v := by
  induction v with
  | nil => simp [ones] at h
  | cons b t ih =>
    cases b
    · simp only [ones] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp

theorem false_mem_or_ones_eq_length (v : List Bool) :
    false ∈ v ∨ ones v = v.length := by
  induction v with
  | nil => exact Or.inr rfl
  | cons b t ih =>
    cases b
    · exact Or.inl (by simp)
    · rcases ih with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (by simp [ones, h])

theorem false_mem_of_den_pos {v : List Bool} (hd : 0 < den v) : false ∈ v := by
  rcases false_mem_or_ones_eq_length v with h | h
  · exact h
  · exfalso
    have h23 : (2 : ℤ) ^ v.length ≤ 3 ^ v.length :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) v.length
    simp only [den] at hd
    rw [h] at hd
    linarith

/-- **A nontrivial integral cycle has at least one circuit** - so powering genuinely
inflates the count. -/
theorem circuits_pos_of_integerCycle {v : List Bool} (h : IntegerCycle v) :
    1 ≤ circuits v := by
  obtain ⟨hne, hx, hd, -⟩ := h
  have ht := true_mem_of_ones_pos hx
  have hf := false_mem_of_den_pos hd
  obtain ⟨b, t, rfl⟩ : ∃ b t, v = b :: t := by
    cases v with
    | nil => exact absurd rfl hne
    | cons b t => exact ⟨b, t, rfl⟩
  obtain ⟨⟨qa, qb⟩, hqmem, hqne⟩ := exists_ne_cpair (b :: t) b ht hf
  rw [← zip_rot_eq_cpairs] at hqmem
  cases qa <;> cases qb
  · exact absurd rfl hqne
  · -- rising edge (false, true): convert via rises = falls
    have hpos : 0 < ((b :: t).zip (rot (b :: t))).countP fun q => !q.1 && q.2 :=
      List.countP_pos_iff.mpr ⟨(false, true), hqmem, by simp⟩
    rw [countP_ft_eq_circuits] at hpos
    omega
  · -- falling edge (true, false): a circuit directly
    have hpos : 0 < circuits (b :: t) := by
      simp only [circuits]
      exact List.countP_pos_iff.mpr ⟨(true, false), hqmem, by simp⟩
    omega
  · exact absurd rfl hqne

/-! ## Primitive words and the decomposition -/

/-- A word is **primitive** when it is nonempty and not a proper power `wpow u j`,
`j ≥ 2`, of any word.  Genuine cycles - traversed once - are primitive words; a
non-primitive integral word is a shorter cycle walked several times, which is why every
honest "boundedly many …" statement on the board quantifies over primitive words only. -/
def Primitive (v : List Bool) : Prop :=
  v ≠ [] ∧ ∀ u j, 2 ≤ j → v ≠ wpow u j

/-- Every nonempty word is a power of a primitive word. -/
theorem exists_primitive_root (v : List Bool) (hv : v ≠ []) :
    ∃ u j, Primitive u ∧ 1 ≤ j ∧ v = wpow u j := by
  by_cases hp : ∀ u j, 2 ≤ j → v ≠ wpow u j
  · exact ⟨v, 1, ⟨hv, hp⟩, le_refl 1, (wpow_one v).symm⟩
  · push Not at hp
    obtain ⟨u, j, hj, huv⟩ := hp
    have hu : u ≠ [] := by
      rintro rfl
      rw [wpow_nil] at huv
      exact hv huv
    have hul : 1 ≤ u.length := List.length_pos_iff.mpr hu
    have hlt : u.length < v.length := by
      have hlen : v.length = j * u.length := by rw [huv, length_wpow]
      nlinarith
    obtain ⟨w, i, hw, hi, hui⟩ := exists_primitive_root u hu
    refine ⟨w, i * j, hw, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · rw [huv, hui, wpow_wpow]
termination_by v.length
decreasing_by exact hlt

/-! ## A positive cycle cannot be all-growth

The archimedean shadow of `0 < den`: a positive integer cycle word has strictly more
"halving mass" than "tripling mass", so its odd-step frequency is strictly below
`log 2 / log 3`.  This is the exact sense in which every positive cycle — trivial or not —
has odd frequency below the drift ceiling (the Route A1 strength audit's `3^a < 2^b`), stated
inside the Front B word convention so no cross-map bridge is needed. -/

/-- `0 < den v` unpacked: `3^(ones v) < 2^(v.length)` over `ℤ`. -/
theorem cycle_three_pow_lt_two_pow {v : List Bool} (h : 0 < den v) :
    (3 : ℤ) ^ ones v < 2 ^ v.length := by
  have : (0 : ℤ) < 2 ^ v.length - 3 ^ ones v := h
  linarith

/-- The logarithmic form: `ones · log 3 < length · log 2` for a positive cycle word. -/
theorem cycle_ones_log_lt {v : List Bool} (h : 0 < den v) :
    (ones v : ℝ) * Real.log 3 < (v.length : ℝ) * Real.log 2 := by
  have hlt : (3 : ℝ) ^ ones v < 2 ^ v.length := by
    have h3 : ((3 : ℤ) ^ ones v : ℝ) < ((2 : ℤ) ^ v.length : ℝ) := by
      exact_mod_cast cycle_three_pow_lt_two_pow h
    push_cast at h3; exact h3
  have hlog := Real.log_lt_log (by positivity) hlt
  rwa [Real.log_pow, Real.log_pow] at hlog

/-- **The odd-step frequency of a positive cycle is below `log 2 / log 3`.**  This is the
archimedean ceiling every positive integer cycle respects, `Compression`-independent. -/
theorem cycle_ones_freq_lt {v : List Bool} (h : 0 < den v) (hne : v ≠ []) :
    (ones v : ℝ) / v.length < Real.log 2 / Real.log 3 := by
  have hlen : (0 : ℝ) < v.length := by
    have := List.length_pos_iff_ne_nil.mpr hne; exact_mod_cast this
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ hlen hlog3]
  have := cycle_ones_log_lt h
  linarith

end CollatzMoonshot.FrontB
