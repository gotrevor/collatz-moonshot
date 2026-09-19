import CollatzMoonshot.FrontA.FirstCrossing
import CollatzMoonshot.FrontB.OneCircuit

/-! # First crossing: the overshoot, and stopping-time correctness on one-run words

At a first crossing `v` (length `m`, `a` odd letters, `D = 2^m - 3^a > 0`) a start `n`
that does not descend has overshoot `E = tstep^[m] n - n` with

    D · n + 2^m · E = numer v      and      3 · E < a   (for a ≥ 1).

So `numer v ≡ 3^a · E (mod D)`: a stopping-time failure is a *near-cycle*, and `E = 0` is
exactly the cycle case.  On a one-run word `1^a 0^b` the overshoot is below one, so a
non-descending start closes the one-circuit cycle, and the repository's own effective
separation (`sep_two_three`, Rhin-lite) excludes it.  That separation also discharges the
`SteinerOneCircuit` hypothesis of `OneCircuit.lean` (Steiner 1977).

No stopping-time or crossing-existence assumption is used anywhere in this file. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- The trace of `a + b` steps is the trace of `a` steps followed by the trace of `b`
steps from the `a`-th iterate. -/
theorem traceWord_add (n a b : ℕ) :
    traceWord n (a + b) = traceWord n a ++ traceWord (tstep^[a] n) b := by
  induction a generalizing n with
  | zero => simp [traceWord]
  | succ a ih =>
    rw [Nat.succ_add]
    simp [traceWord, ih (tstep n), Function.iterate_succ_apply]

theorem ones_replicate_false' (b : ℕ) : ones (List.replicate b false) = 0 := by
  induction b with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ones, ih]

/-! ### The overshoot at a first crossing -/

/-- **Exact overshoot identity.**  If the start survives its first crossing, then
`D · n + 2^m · (y − n) = numer v` with `D = 2^m − 3^a`, `y = tstep^[m] n`. -/
theorem overshoot_identity {n m : ℕ} (h : At n m) (hsurv : n ≤ tstep^[m] n) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n
      + 2 ^ m * (tstep^[m] n - n) = numer (traceWord n m) := by
  have hid := tstep_iterate_identity m n
  have hsub := h.2.2
  obtain ⟨E, hE⟩ : ∃ E, tstep^[m] n = n + E := ⟨_, (Nat.add_sub_cancel' hsurv).symm⟩
  obtain ⟨D, hD⟩ : ∃ D, 2 ^ m = D + 3 ^ ones (traceWord n m) :=
    ⟨_, (Nat.sub_add_cancel hsub.le).symm⟩
  rw [hE, Nat.add_sub_cancel_left, hD, Nat.add_sub_cancel]
  rw [hD, hE] at hid
  nlinarith [hid]

/-- **The overshoot is below `a/3`.**  A surviving start at a first crossing with at least
one odd step lands strictly less than `a/3` above itself. -/
theorem three_mul_overshoot_lt {n m : ℕ} (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (ha : 1 ≤ ones (traceWord n m)) :
    3 * (tstep^[m] n - n) < ones (traceWord n m) := by
  have hid := overshoot_identity h hsurv
  have hb := numerator_bound h
  have hsub := h.2.2
  have h1 : 2 ^ m * (3 * (tstep^[m] n - n)) ≤ ones (traceWord n m) * 3 ^ ones (traceWord n m) := by
    nlinarith [hid, hb]
  have h2 : ones (traceWord n m) * 3 ^ ones (traceWord n m)
      < ones (traceWord n m) * 2 ^ m := Nat.mul_lt_mul_of_pos_left hsub (by omega)
  have h3 : 2 ^ m * (3 * (tstep^[m] n - n)) < 2 ^ m * ones (traceWord n m) := by
    rw [mul_comm (2 ^ m) (ones _)]; exact lt_of_le_of_lt h1 h2
  exact Nat.lt_of_mul_lt_mul_left h3

/-! ### Steiner's inequality from the effective separation -/

/-- **Steiner's inequality.**  For `a ≥ 2` and `3^a < 2^(a+b)`, the gap `2^(a+b) − 3^a` is
at least `2^b`.  Off the near-critical window this is trivial; on it, `sep_two_three`
(the Rhin-lite separation) handles `a ≥ 6` and the four remaining `a` are finite. -/
theorem two_pow_le_gap (a b : ℕ) (ha : 2 ≤ a) (h1 : 3 ^ a < 2 ^ (a + b)) :
    2 ^ b ≤ 2 ^ (a + b) - 3 ^ a := by
  have hZ : 2 ^ b ≤ 2 ^ (a + b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : 2 ^ (a + b) = 2 * 2 ^ (a + b - 1) := by
    rw [← pow_succ']; congr 1; omega
  rcases le_or_gt (2 * 3 ^ a) (2 ^ (a + b)) with hbig | hwin
  · omega
  · rcases le_or_gt 6 a with h6 | h5
    · have hsep := sep_two_three a (a + b) h6 h1 hwin
      by_contra hlt
      push Not at hlt
      have hcube : (2 ^ (a + b) - 3 ^ a) ^ 3 * 2 ^ a < (2 ^ b) ^ 3 * 2 ^ a :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hlt (by norm_num)) (by positivity)
      have hlow : (2 ^ (a + b - 1)) ^ 3 ≤ 3 ^ (3 * a) := by
        rw [pow_mul']
        exact Nat.pow_le_pow_left (by omega) 3
      have hchain : (2 ^ (a + b - 1)) ^ 3 < (2 ^ b) ^ 3 * 2 ^ a :=
        lt_of_le_of_lt (hlow.trans hsep) hcube
      rw [← pow_mul, ← pow_mul, ← pow_add] at hchain
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hchain
      omega
    · have hb : b ≤ 6 := by
        have h35 : 3 ^ a ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (a + b) < 2 ^ 9 := by
          calc 2 ^ (a + b) < 2 * 3 ^ a := hwin
            _ ≤ 2 * 3 ^ 5 := by omega
            _ < 2 ^ 9 := by norm_num
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
        omega
      interval_cases a <;> interval_cases b <;> (revert h1 hwin; norm_num)

/-- **Steiner's theorem (1977), discharged.**  The `SteinerOneCircuit` hypothesis of
`OneCircuit.lean` follows from `two_pow_le_gap`: a divisor of `2^b − 1` is below `2^b`. -/
theorem steinerOneCircuit : SteinerOneCircuit := by
  intro a b ha hb hpos hdvd
  rw [den_oneCircuitWord] at hpos hdvd
  have h1 : 3 ^ a < 2 ^ (a + b) := by
    have : (3 : ℤ) ^ a < 2 ^ (a + b) := by linarith
    exact_mod_cast this
  have hgap := two_pow_le_gap a b ha h1
  have hgapZ : (2 : ℤ) ^ b ≤ 2 ^ (a + b) - 3 ^ a := by
    have : ((2 ^ b : ℕ) : ℤ) ≤ ((2 ^ (a + b) - 3 ^ a : ℕ) : ℤ) := by exact_mod_cast hgap
    rw [Nat.cast_sub h1.le] at this
    push_cast at this
    exact this
  have hone : (1 : ℤ) < 2 ^ b := by
    have : 1 < 2 ^ b := Nat.one_lt_two_pow (by omega)
    exact_mod_cast this
  have hle : (2 : ℤ) ^ (a + b) - 3 ^ a ≤ 2 ^ b - 1 := Int.le_of_dvd (by linarith) hdvd
  linarith

/-! ### Stopping-time correctness on one-run words -/

/-- **One-run stopping-time correctness.**  A start `n ≥ 2` whose first crossing is the
one-run word `1^a 0^b` descends there.  Proof: the prefix `1^a` forces `n + 1 = 2^a s` and
`tstep^[a] n + 1 = 3^a s`; the suffix `0^b` gives `2^b · tstep^[m] n = tstep^[a] n`; a
non-descent then reads `(2^(a+b) − 3^a) · s + 1 ≤ 2^b`, against Steiner's inequality
(`a ≥ 2`) or the elementary `a = 1` case, which only admits `n = 1`. -/
theorem descends_of_oneRun {n m a b : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hw : traceWord n m = oneCircuitWord a b) : tstep^[m] n < n := by
  have hm : m = a + b := by
    have := congrArg List.length hw; simpa using this
  subst hm
  have hones : ones (traceWord n (a + b)) = a := by rw [hw]; simp
  have hsub : 3 ^ a < 2 ^ (a + b) := by have := h.2.2; rwa [hones] at this
  have hid := tstep_iterate_identity (a + b) n
  rw [hw, numer_oneCircuitWord, ones_oneCircuitWord] at hid
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- all-even word: `2^b · y = n` with `b ≥ 1`
    simp at hid hsub ⊢
    have hb2 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hy1 : 1 ≤ tstep^[b] n := by
      by_contra h0; push Not at h0
      have : tstep^[b] n = 0 := by omega
      rw [this] at hid; omega
    have : 2 * tstep^[b] n ≤ 2 ^ b * tstep^[b] n :=
      Nat.mul_le_mul_right _ hb2
    omega
  · have hb : 1 ≤ b := by
      by_contra hb0; push Not at hb0
      have hb0' : b = 0 := by omega
      subst hb0'
      have : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
      simp at hsub; omega
    rw [traceWord_add] at hw
    have hlen1 : (traceWord n a).length = (List.replicate a true).length := by simp
    obtain ⟨hpre, hsuf⟩ := List.append_inj hw hlen1
    -- prefix `1^a`
    have hidp := tstep_iterate_identity a n
    rw [hpre, ones_replicate_true] at hidp
    have hnum : numer (List.replicate a true) = 3 ^ a - 2 ^ a := by
      have := numer_oneCircuitWord a 0; simpa [oneCircuitWord] using this
    rw [hnum] at hidp
    have h23 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
    have hidp' : 2 ^ a * (tstep^[a] n + 1) = 3 ^ a * (n + 1) := by
      rw [mul_add, mul_add, hidp]; omega
    have hdvd : 2 ^ a ∣ n + 1 := by
      have hcop : Nat.Coprime (2 ^ a) (3 ^ a) := Nat.Coprime.pow _ _ (by decide)
      exact hcop.dvd_of_dvd_mul_left ⟨_, hidp'.symm⟩
    obtain ⟨s, hs⟩ := hdvd
    have hx : tstep^[a] n + 1 = 3 ^ a * s := by
      have : 2 ^ a * (tstep^[a] n + 1) = 2 ^ a * (3 ^ a * s) := by
        rw [hidp', hs]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    have hs1 : 1 ≤ s := by
      by_contra h0; push Not at h0
      have : s = 0 := by omega
      rw [this] at hs; omega
    -- suffix `0^b`
    have hids := tstep_iterate_identity b (tstep^[a] n)
    rw [hsuf, ones_replicate_false', numer_eq_zero_of_ones_eq_zero (ones_replicate_false' b)]
      at hids
    simp only [pow_zero, one_mul, add_zero] at hids
    have hy : tstep^[a + b] n = tstep^[b] (tstep^[a] n) := by
      rw [add_comm, Function.iterate_add_apply]
    rw [hy]
    -- the non-descent inequality
    by_contra hsurv
    push Not at hsurv
    have e2 : 2 ^ b * n ≤ tstep^[a] n := by
      rw [← hids]; exact Nat.mul_le_mul_left _ hsurv
    have e1 : 2 ^ b * n + 2 ^ b = 2 ^ (a + b) * s := by
      rw [pow_add, mul_comm (2 ^ a) (2 ^ b), mul_assoc, ← hs]; ring
    have key : 2 ^ (a + b) * s + 1 ≤ 3 ^ a * s + 2 ^ b := by omega
    obtain ⟨D, hD⟩ : ∃ D, 2 ^ (a + b) = D + 3 ^ a := ⟨_, (Nat.sub_add_cancel hsub.le).symm⟩
    have key2 : D * s + 1 ≤ 2 ^ b := by
      rw [hD, add_mul] at key; omega
    have hDs : D ≤ D * s := Nat.le_mul_of_pos_right _ hs1
    rcases le_or_gt 2 a with ha2 | ha1
    · have := two_pow_le_gap a b ha2 hsub
      omega
    · have ha1' : a = 1 := by omega
      subst ha1'
      have h2b : 2 ^ (1 + b) = 2 * 2 ^ b := by rw [pow_add]; ring
      have hb2 : 2 ≤ 2 ^ b := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      have hD1 : D = 1 := by omega
      rw [hD1, one_mul] at key2
      simp at hs
      omega

/-- The one-run instance of `StoppingCorrect`: every start at least `2` whose first
crossing is a one-run word descends at that crossing. -/
theorem stoppingCorrect_oneRun : ∀ n m, 2 ≤ n → At n m →
    (∃ a b, traceWord n m = oneCircuitWord a b) → tstep^[m] n < n := by
  rintro n m hn h ⟨a, b, hw⟩
  exact descends_of_oneRun hn h hw

end CollatzMoonshot.FrontA.FirstCrossing
