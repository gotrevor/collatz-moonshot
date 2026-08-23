/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Conjecture
import CollatzMoonshot.FrontB.Words
import CollatzMoonshot.FrontB.Threads

/-!
# The dictionary: `NoNontrivialCycle` (on `ℕ`) ↔ `FrontB` (on words)

The Halbeisen-Hungerbühler / Bernstein-Lagarias correspondence.  Landing this bridge
retroactively upgrades every `FrontB/` theorem to a genuine Collatz statement (see the
warning in `FrontB/Threads.lean`, now discharged).

## Structure

The word convention in `Words.lean` (`den v = 2^|v| − 3^(ones v)`) matches the
**accelerated** (Syracuse-style) map `tstep` - every step halves once, odd steps also
multiply by 3 - not the un-accelerated `step` of `Basic.lean`.  So the bridge has two
layers:

1. **orbit ↔ word** (`tstep`-cycles ↔ words).  The engine is the exact iterate identity
   `tstep_iterate_identity`:
   `2^m · tstep^[m] n = 3^(ones v) · n + numer v` for `v = traceWord n m`,
   an unconditional statement over `ℕ` proved by one induction - no cycle hypothesis, no
   rotation bookkeeping.  On a cycle it specializes instantly to the member identity
   `n · den v = numer v`.  Sanity anchors, hand-checked:
   `n = 1`, `v = [true, false]`: `den = 1`, `numer = 1` ✓;
   `n = 2`, `v = [false, true]`: `den = 1`, `numer = 2` ✓.
   (Orientation: the FIRST letter of the trace is the parity of `n` itself.)
   For the converse, `realize_iterate` walks an integral word back into an orbit; there the
   rotation identities `two_mul_numer_rot_false/true` are the per-step engine.
2. **`step` ↔ `tstep`** (un-accelerated ↔ accelerated cycles): `walk` chases a `step`-cycle
   with `tstep`-steps, advancing 1 (even member) or 2 (odd member) positions; the only way
   to miss a member is to be its odd predecessor's `3n+1` intermediate.  The trivial
   `tstep`-cycle `{1, 2}` corresponds to the trivial `step`-cycle `{1, 2, 4}`.

## Note on `IsTrivial` (2026-08-23)

The original `IsTrivial v := numer v = den v` ("member is 1") made `FrontB` refutably
false: `[false, true]` - the trivial cycle rooted at `2` - is an `IntegerCycle` with
`numer = 2 ≠ 1 = den`.  `IsTrivial` now reads member `∈ {1, 2}`, which is exactly the
membership of the trivial accelerated cycle.  With that fix both directions below are
theorems.
-/

namespace CollatzMoonshot.FrontB

open CollatzMoonshot

/-! ## Layer 1: the accelerated map and its parity trace -/

/-- The accelerated (Syracuse-style) Collatz map: every application halves once.
This is the map whose cycles the words of `Words.lean` encode. -/
def tstep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

@[simp] theorem tstep_one : tstep 1 = 2 := by decide

@[simp] theorem tstep_two : tstep 2 = 1 := by decide

theorem tstep_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ tstep n := by
  unfold tstep; split <;> omega

/-- One accelerated step from an even number is one plain step. -/
theorem tstep_eq_step {n : ℕ} (h : n % 2 = 0) : tstep n = step n := by
  simp [tstep, step, h]

/-- One accelerated step from an odd number is two plain steps (`3n+1` is even). -/
theorem tstep_eq_step_step {n : ℕ} (h : n % 2 = 1) : tstep n = step (step n) := by
  have h0 : ¬ n % 2 = 0 := by omega
  have h1 : (3 * n + 1) % 2 = 0 := by omega
  simp [tstep, step, h0, h1]

/-- The parity trace of the first `m` accelerated steps from `n`:
the first letter is the parity of `n` itself. -/
def traceWord (n : ℕ) : ℕ → List Bool
  | 0 => []
  | m + 1 => (n % 2 = 1) :: traceWord (tstep n) m

@[simp] theorem traceWord_length (n m : ℕ) : (traceWord n m).length = m := by
  induction m generalizing n with
  | zero => rfl
  | succ k ih => simp [traceWord, ih]

/-- **The iterate identity**, the engine of Layer 1: unconditionally,
`2^m · tstep^[m] n = 3^(ones v) · n + numer v` where `v` is the parity trace.
Proved by one induction along the orbit; specializing to a cycle gives the member
identity for free. -/
theorem tstep_iterate_identity (m n : ℕ) :
    2 ^ m * tstep^[m] n =
      3 ^ ones (traceWord n m) * n + numer (traceWord n m) := by
  induction m generalizing n with
  | zero => simp [traceWord]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.even_or_odd n with he | ho
    · have hpar : n % 2 = 0 := Nat.even_iff.mp he
      have ht : traceWord n (k + 1) = false :: traceWord (tstep n) k := by
        simp [traceWord, hpar]
      have h2 : 2 * tstep n = n := by unfold tstep; split <;> omega
      rw [ht]
      simp only [ones, numer]
      calc 2 ^ (k + 1) * tstep^[k] (tstep n)
          = 2 * (2 ^ k * tstep^[k] (tstep n)) := by ring
        _ = 2 * (3 ^ ones (traceWord (tstep n) k) * tstep n
              + numer (traceWord (tstep n) k)) := by rw [ih]
        _ = 3 ^ ones (traceWord (tstep n) k) * (2 * tstep n)
              + 2 * numer (traceWord (tstep n) k) := by ring
        _ = _ := by rw [h2]
    · have hpar : n % 2 = 1 := Nat.odd_iff.mp ho
      have ht : traceWord n (k + 1) = true :: traceWord (tstep n) k := by
        simp [traceWord, hpar]
      have h2 : 2 * tstep n = 3 * n + 1 := by
        unfold tstep; split <;> omega
      rw [ht]
      simp only [ones, numer]
      calc 2 ^ (k + 1) * tstep^[k] (tstep n)
          = 2 * (2 ^ k * tstep^[k] (tstep n)) := by ring
        _ = 2 * (3 ^ ones (traceWord (tstep n) k) * tstep n
              + numer (traceWord (tstep n) k)) := by rw [ih]
        _ = 3 ^ ones (traceWord (tstep n) k) * (2 * tstep n)
              + 2 * numer (traceWord (tstep n) k) := by ring
        _ = 3 ^ ones (traceWord (tstep n) k) * (3 * n + 1)
              + 2 * numer (traceWord (tstep n) k) := by rw [h2]
        _ = _ := by ring

/-- **The member identity**: if the accelerated orbit returns to `n` after `m > 0`
steps, the parity trace is a word `v` with `(n : ℤ) * den v = numer v`. -/
theorem member_identity {n m : ℕ} (_hn : 1 ≤ n) (_hm : 0 < m)
    (hcyc : tstep^[m] n = n) :
    (n : ℤ) * den (traceWord n m) = (numer (traceWord n m) : ℤ) := by
  have h := tstep_iterate_identity m n
  rw [hcyc] at h
  have hz : (2 : ℤ) ^ m * n =
      3 ^ ones (traceWord n m) * n + numer (traceWord n m) := by exact_mod_cast h
  simp only [den, traceWord_length]
  linear_combination hz

/-- A word with no odd step has numerator zero. -/
theorem numer_eq_zero_of_ones_eq_zero {v : List Bool} (hx : ones v = 0) :
    numer v = 0 := by
  induction v with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simp only [ones] at hx
      simp [numer, ih hx]
    · simp only [ones] at hx
      omega

/-- A word with an odd step has positive numerator. -/
theorem numer_pos {v : List Bool} (hx : 1 ≤ ones v) : 0 < numer v := by
  induction v with
  | nil => simp [ones] at hx
  | cons b t ih =>
    cases b
    · simp only [ones] at hx
      have := ih hx
      simp only [numer]
      omega
    · have h3 : 0 < 3 ^ ones t := Nat.pow_pos (by norm_num)
      simp only [numer]
      omega

/-- A nontrivial accelerated cycle has an odd member, so its trace has a `true`.
(An all-halving cycle would strictly decrease.) -/
theorem ones_pos_of_cycle {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (hcyc : tstep^[m] n = n) : 1 ≤ ones (traceWord n m) := by
  by_contra h
  have hx : ones (traceWord n m) = 0 := by omega
  have hid := tstep_iterate_identity m n
  rw [hcyc, hx, numer_eq_zero_of_ones_eq_zero hx, pow_zero, one_mul, add_zero] at hid
  have h2 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  nlinarith

/-- The trace of an accelerated cycle is an `IntegerCycle`: nonempty, has an odd step,
positive denominator, and the divisibility - all falling out of `member_identity`. -/
theorem integerCycle_traceWord {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (hcyc : tstep^[m] n = n) : IntegerCycle (traceWord n m) := by
  have hone := ones_pos_of_cycle hn hm hcyc
  have hid := member_identity hn hm hcyc
  have hne : traceWord n m ≠ [] := by
    intro h
    have := traceWord_length n m
    rw [h] at this
    simp at this
    omega
  have hden_ne : den (traceWord n m) ≠ 0 := by
    intro h
    exact not_two_dvd_den hne (h ▸ dvd_zero 2)
  have hnum_nonneg : (0 : ℤ) ≤ (numer (traceWord n m) : ℤ) := Int.natCast_nonneg _
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hden_pos : 0 < den (traceWord n m) := by
    rcases lt_trichotomy (den (traceWord n m)) 0 with h | h | h
    · nlinarith
    · exact absurd h hden_ne
    · exact h
  exact ⟨hne, hone, hden_pos, ⟨(n : ℤ), by rw [← hid]; ring⟩⟩

/-! ## Layer 2: un-accelerated ↔ accelerated cycles -/

/-- **The walk lemma.**  Chasing the plain orbit with accelerated steps: after some
number of `tstep`s we either land exactly on `step^[d] u`, or position `d` is the
`3n+1`-intermediate of an odd member (its predecessor `step^[d−1] u` is odd) and we
land one past it.  The bound `d ≤ 2j` (resp. `d + 1 ≤ 2j`) guarantees the walk is
genuinely moving, which later forces the accelerated period to be positive. -/
theorem walk (d : ℕ) : ∀ u : ℕ,
    (∃ j, d ≤ 2 * j ∧ tstep^[j] u = step^[d] u) ∨
    (1 ≤ d ∧ (step^[d - 1] u) % 2 = 1 ∧
      ∃ j, d + 1 ≤ 2 * j ∧ tstep^[j] u = step^[d + 1] u) := by
  induction d with
  | zero => intro u; exact Or.inl ⟨0, by omega, rfl⟩
  | succ k ih =>
    intro u
    rcases ih u with ⟨j, hj, hhit⟩ | ⟨hk1, hodd, j, hj, hover⟩
    · by_cases hpar : (step^[k] u) % 2 = 0
      · left
        refine ⟨j + 1, by omega, ?_⟩
        calc tstep^[j + 1] u = tstep (tstep^[j] u) := Function.iterate_succ_apply' _ _ _
          _ = tstep (step^[k] u) := by rw [hhit]
          _ = step (step^[k] u) := tstep_eq_step hpar
          _ = step^[k + 1] u := (Function.iterate_succ_apply' _ _ _).symm
      · right
        refine ⟨by omega, by simpa using (by omega : (step^[k] u) % 2 = 1), j + 1,
          by omega, ?_⟩
        calc tstep^[j + 1] u = tstep (tstep^[j] u) := Function.iterate_succ_apply' _ _ _
          _ = tstep (step^[k] u) := by rw [hhit]
          _ = step (step (step^[k] u)) := tstep_eq_step_step (by omega)
          _ = step (step^[k + 1] u) := by rw [Function.iterate_succ_apply' step k u]
          _ = step^[k + 1 + 1] u := (Function.iterate_succ_apply' _ _ _).symm
    · left
      exact ⟨j, by omega, hover⟩

/-- A `step`-cycle through `n ≥ 1` yields an accelerated cycle through a related
member: either `n` itself is `tstep`-periodic, or `n` is the `3n'+1`-intermediate of an
odd `tstep`-periodic member `n'`. -/
theorem tstep_cycle_of_step_cycle {n : ℕ} (hn : 1 ≤ n) (hc : OnCycle n) :
    ∃ n' p, 1 ≤ n' ∧ 0 < p ∧ tstep^[p] n' = n' ∧
      (n = n' ∨ (n' % 2 = 1 ∧ n = 3 * n' + 1)) := by
  obtain ⟨m, hm, hcyc⟩ := hc
  rcases walk m n with ⟨j, hj, hhit⟩ | ⟨hm1, hodd, j, hj, hover⟩
  · exact ⟨n, j, hn, by omega, by rw [hhit, hcyc], Or.inl rfl⟩
  · -- `n` is the intermediate of the odd cycle member `w := step^[m-1] n`.
    set w := step^[m - 1] n with hw
    have hwpos : 1 ≤ w := iterate_step_pos hn _
    have hstepw : step w = n := by
      have h1 : step^[m - 1 + 1] n = n := by rw [show m - 1 + 1 = m by omega, hcyc]
      rw [Function.iterate_succ_apply'] at h1
      rw [hw]
      exact h1
    have hn3 : n = 3 * w + 1 := by
      have hsw : step w = 3 * w + 1 := by
        simp only [step]
        rw [if_neg (by omega)]
      rw [hstepw] at hsw
      exact hsw
    have hwcyc : step^[m] w = w := by
      rw [hw, ← Function.iterate_add_apply, show m + (m - 1) = (m - 1) + m by omega,
        Function.iterate_add_apply, hcyc]
    rcases walk m w with ⟨i, hi, hwhit⟩ | ⟨_, hodd2, i, hi, hwover⟩
    · exact ⟨w, i, hwpos, by omega, by rw [hwhit, hwcyc], Or.inr ⟨hodd, hn3⟩⟩
    · -- `w` itself an intermediate: then `w = 3·(odd)+1` is even, contradicting `w` odd.
      exfalso
      have hpre : step (step^[m - 1] w) = w := by
        have h1 : step^[m - 1 + 1] w = w := by rw [show m - 1 + 1 = m by omega, hwcyc]
        rw [Function.iterate_succ_apply'] at h1
        exact h1
      have hsx : step (step^[m - 1] w) = 3 * step^[m - 1] w + 1 := by
        simp only [step]
        rw [if_neg (by omega)]
      rw [hpre] at hsx
      omega

/-- Accelerated iterates are plain iterates: `tstep^[p] n = step^[K] n` for some
`K ≥ p`.  This is how a `tstep`-cycle expands to a `step`-cycle. -/
theorem step_iterate_of_tstep_iterate (p : ℕ) : ∀ n : ℕ,
    ∃ K, p ≤ K ∧ tstep^[p] n = step^[K] n := by
  induction p with
  | zero => exact fun n => ⟨0, le_refl _, rfl⟩
  | succ q ih =>
    intro n
    obtain ⟨K, hK, hEq⟩ := ih (tstep n)
    rcases Nat.even_or_odd n with he | ho
    · have hpar : n % 2 = 0 := Nat.even_iff.mp he
      refine ⟨K + 1, by omega, ?_⟩
      calc tstep^[q + 1] n = tstep^[q] (tstep n) := Function.iterate_succ_apply _ _ _
        _ = step^[K] (tstep n) := hEq
        _ = step^[K] (step n) := by rw [tstep_eq_step hpar]
        _ = step^[K + 1] n := (Function.iterate_succ_apply _ _ _).symm
    · have hpar : n % 2 = 1 := Nat.odd_iff.mp ho
      refine ⟨K + 2, by omega, ?_⟩
      calc tstep^[q + 1] n = tstep^[q] (tstep n) := Function.iterate_succ_apply _ _ _
        _ = step^[K] (tstep n) := hEq
        _ = step^[K] (step (step n)) := by rw [tstep_eq_step_step hpar]
        _ = step^[K + 1] (step n) := (Function.iterate_succ_apply _ _ _).symm
        _ = step^[K + 2] n := (Function.iterate_succ_apply _ _ _).symm

/-- The accelerated orbit of `2` is the two-cycle `{2, 1}`. -/
theorem tstep_iterate_two (p : ℕ) : tstep^[p] 2 = 2 ∨ tstep^[p] 2 = 1 := by
  induction p with
  | zero => exact Or.inl rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h] <;> simp

/-- `4` is not `tstep`-periodic: its accelerated orbit falls into `{2, 1}` and never
returns. -/
theorem four_not_tstep_periodic {p : ℕ} (hp : 0 < p) : tstep^[p] 4 ≠ 4 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Function.iterate_succ_apply, show tstep 4 = 2 by decide]
  rcases tstep_iterate_two q with h | h <;> omega

/-- If the accelerated cycle through `n'` is trivial (member `1` or `2`), the plain
member `n` it came from is among `{1, 2, 4}`. -/
theorem step_member_trivial {n n' : ℕ} (h12 : n' = 1 ∨ n' = 2)
    (hrel : n = n' ∨ (n' % 2 = 1 ∧ n = 3 * n' + 1)) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  rcases h12 with rfl | rfl <;> rcases hrel with rfl | ⟨hodd, rfl⟩ <;> omega

/-- Under `FrontB`, every accelerated cycle member is `1` or `2`: its trace is an
`IntegerCycle`, so `IsTrivial` pins the member via the member identity. -/
theorem tstep_cycle_member_trivial (h : FrontB) {n' p : ℕ} (hn' : 1 ≤ n')
    (hp : 0 < p) (hcyc : tstep^[p] n' = n') : n' = 1 ∨ n' = 2 := by
  have hic := integerCycle_traceWord hn' hp hcyc
  have hid := member_identity hn' hp hcyc
  have hden := hic.2.2.1
  rcases h _ hic with h1 | h2
  · left
    have hcancel : (n' : ℤ) * den (traceWord n' p) = 1 * den (traceWord n' p) := by
      rw [one_mul, hid, h1]
    have := mul_right_cancel₀ (ne_of_gt hden) hcancel
    exact_mod_cast this
  · right
    have hcancel : (n' : ℤ) * den (traceWord n' p) = 2 * den (traceWord n' p) := by
      rw [hid, h2]
    have := mul_right_cancel₀ (ne_of_gt hden) hcancel
    exact_mod_cast this

/-! ## The realization walk (for the converse) -/

/-- `rot` is `List.rotate 1`. -/
theorem rot_eq_rotate (v : List Bool) : rot v = v.rotate 1 := by
  cases v with
  | nil => rfl
  | cons b t => rw [List.rotate_cons_succ, List.rotate_zero]; rfl

theorem rot_iterate (k : ℕ) (v : List Bool) : rot^[k] v = v.rotate k := by
  induction k with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, rot_eq_rotate, List.rotate_rotate]

/-- Rotating a word once per letter returns it. -/
theorem rot_iterate_length (v : List Bool) : rot^[v.length] v = v := by
  rw [rot_iterate, List.rotate_length]

/-- One realization step, even case: if `n · den v = numer v` and `v` starts with
`false`, then `n` is even and `tstep n` realizes the rotated word. -/
theorem realize_head_false {t : List Bool} {n : ℕ}
    (hid : (n : ℤ) * den (false :: t) = numer (false :: t)) :
    n % 2 = 0 ∧ (tstep n : ℤ) * den (false :: t) = numer (rot (false :: t)) := by
  have hkey : (2 : ℤ) * (numer (rot (false :: t)) : ℤ) = (numer (false :: t) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (two_mul_numer_rot_false t)
  have hodd_den : ¬ (2 : ℤ) ∣ den (false :: t) := not_two_dvd_den (by simp)
  have h2n : (2 : ℤ) ∣ (n : ℤ) := by
    have hdvd : (2 : ℤ) ∣ (n : ℤ) * den (false :: t) := by
      rw [hid, ← hkey]; exact Dvd.intro _ rfl
    rcases Int.prime_two.dvd_mul.mp hdvd with h | h
    · exact h
    · exact absurd h hodd_den
  have hpar : n % 2 = 0 := by
    have : (2 : ℕ) ∣ n := by exact_mod_cast h2n
    omega
  refine ⟨hpar, ?_⟩
  have htn : 2 * tstep n = n := by unfold tstep; split <;> omega
  have h2 : (2 : ℤ) * ((tstep n : ℤ) * den (false :: t)) =
      2 * (numer (rot (false :: t)) : ℤ) := by
    rw [hkey, ← hid]
    have : (2 : ℤ) * (tstep n : ℤ) = (n : ℤ) := by exact_mod_cast htn
    linear_combination den (false :: t) * this
  exact mul_left_cancel₀ (by norm_num) h2

/-- The numerator of a `true`-headed word is odd. -/
theorem numer_true_odd (t : List Bool) : numer (true :: t) % 2 = 1 := by
  have h3 : 3 ^ ones t % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  simp only [numer]
  omega

/-- One realization step, odd case: if `n · den v = numer v` and `v` starts with
`true`, then `n` is odd and `tstep n` realizes the rotated word. -/
theorem realize_head_true {t : List Bool} {n : ℕ}
    (hid : (n : ℤ) * den (true :: t) = numer (true :: t)) :
    n % 2 = 1 ∧ (tstep n : ℤ) * den (true :: t) = numer (rot (true :: t)) := by
  have hkey := two_mul_numer_rot_true t
  have hodd_den : ¬ (2 : ℤ) ∣ den (true :: t) := not_two_dvd_den (by simp)
  have hpar : n % 2 = 1 := by
    by_contra h
    have hn2 : (2 : ℕ) ∣ n := by omega
    have : (2 : ℤ) ∣ (numer (true :: t) : ℤ) := by
      rw [← hid]
      exact Dvd.dvd.mul_right (by exact_mod_cast hn2) _
    have : (2 : ℕ) ∣ numer (true :: t) := by exact_mod_cast this
    have := numer_true_odd t
    omega
  refine ⟨hpar, ?_⟩
  have htn : 2 * tstep n = 3 * n + 1 := by unfold tstep; split <;> omega
  have h2 : (2 : ℤ) * ((tstep n : ℤ) * den (true :: t)) =
      2 * (numer (rot (true :: t)) : ℤ) := by
    rw [hkey, ← hid]
    have hz : (2 : ℤ) * (tstep n : ℤ) = 3 * (n : ℤ) + 1 := by exact_mod_cast htn
    linear_combination den (true :: t) * hz
  exact mul_left_cancel₀ (by norm_num) h2

/-- **The realization walk**: an integral word is walked by `tstep`, one rotation per
step. -/
theorem realize_iterate (k : ℕ) : ∀ (v : List Bool), v ≠ [] → ∀ n : ℕ,
    (n : ℤ) * den v = numer v → (tstep^[k] n : ℤ) * den v = numer (rot^[k] v) := by
  induction k with
  | zero => intro v _ n hid; simpa using hid
  | succ i ih =>
    intro v hv n hid
    have hstep : (tstep n : ℤ) * den v = numer (rot v) := by
      cases v with
      | nil => exact absurd rfl hv
      | cons b t =>
        cases b
        · exact (realize_head_false hid).2
        · exact (realize_head_true hid).2
    have hrotne : rot v ≠ [] := by
      intro h
      have := length_rot v
      rw [h] at this
      simp at this
      exact hv (List.length_eq_zero_iff.mp this.symm)
    have := ih (rot v) hrotne (tstep n) (by rw [den_rot]; exact hstep)
    rw [den_rot] at this
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact this

/-! ## Headlines - FROZEN statements 🧊 -/

/-- **HEADLINE (frozen).**  The word-level Front B implies the `ℕ`-level one: if every
integral positive word-cycle is trivial, then every Collatz cycle is the trivial one.
This is the direction that upgrades every `FrontB/` theorem to a Collatz statement. -/
theorem noNontrivialCycle_of_frontB (h : FrontB) : NoNontrivialCycle := by
  intro n hn hc
  obtain ⟨n', p, hn', hp, hcyc, hrel⟩ := tstep_cycle_of_step_cycle hn hc
  exact step_member_trivial (tstep_cycle_member_trivial h hn' hp hcyc) hrel

/-- The converse: an `IntegerCycle` word is realized by an actual accelerated
`ℕ`-cycle (its member is `numer v / den v`; the orbit follows the word), which expands
to a `step`-cycle; `NoNontrivialCycle` then forces triviality of the word. -/
theorem frontB_of_noNontrivialCycle (h : NoNontrivialCycle) : FrontB := by
  rintro v ⟨hne, hx, hden, hdvd⟩
  obtain ⟨c, hc⟩ := hdvd
  have hnum : 0 < numer v := numer_pos hx
  have hnumz : (0 : ℤ) < (numer v : ℤ) := by exact_mod_cast hnum
  have hcpos : 0 < c := by
    have h0 : 0 < den v * c := hc ▸ hnumz
    rcases lt_trichotomy 0 c with hlt | heq | hgt
    · exact hlt
    · rw [← heq, mul_zero] at h0; exact absurd h0 (lt_irrefl 0)
    · nlinarith
  obtain ⟨n, hnc⟩ : ∃ n : ℕ, (n : ℤ) = c := ⟨c.toNat, Int.toNat_of_nonneg hcpos.le⟩
  have hn1 : 1 ≤ n := by omega
  have hid : (n : ℤ) * den v = numer v := by rw [hnc, hc]; ring
  have hlenpos : 0 < v.length := List.length_pos_of_ne_nil hne
  have hper : tstep^[v.length] n = n := by
    have h1 := realize_iterate v.length v hne n hid
    rw [rot_iterate_length] at h1
    have hcancel := mul_right_cancel₀ (ne_of_gt hden) (h1.trans hid.symm)
    exact_mod_cast hcancel
  obtain ⟨K, hK, hEq⟩ := step_iterate_of_tstep_iterate v.length n
  have honc : OnCycle n := ⟨K, by omega, by rw [← hEq, hper]⟩
  rcases h n hn1 honc with rfl | rfl | rfl
  · left; rw [← hid]; push_cast; ring
  · right; rw [← hid]; push_cast; ring
  · exact absurd hper (four_not_tstep_periodic hlenpos)

/-- **HEADLINE (frozen).**  The dictionary. -/
theorem noNontrivialCycle_iff_frontB : NoNontrivialCycle ↔ FrontB :=
  ⟨frontB_of_noNontrivialCycle, noNontrivialCycle_of_frontB⟩

end CollatzMoonshot.FrontB
