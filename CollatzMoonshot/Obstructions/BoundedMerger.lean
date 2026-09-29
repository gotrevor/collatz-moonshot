import CollatzMoonshot.Obstructions.Q1Coalescence

/-! A bounded merger to any smaller positive seed cannot cover all starts.
The two time bounds are independent; the seed is unrestricted below n. -/
namespace CollatzMoonshot.Obstructions.BoundedMerger
open CollatzMoonshot.FrontB

/-! ## Word arithmetic

The affine numerator of a length-`k` parity word `v` with `p = ones v` odd letters
satisfies `2 ^ k * tstep^[k] x = 3 ^ p * x + numer v` (`tstep_iterate_identity`).
The combined constant `g v = 2 ^ v.length + numer v` is what the geometry needs; it
starts at `1`, and prepending a letter either doubles it (`false`) or doubles it and
adds `3 ^ (ones of the tail)` (`true`).  Both bounds below are one induction. -/

private theorem ones_le_length (v : List Bool) : ones v ≤ v.length := by
  induction v with
  | nil => simp
  | cons a t ih => cases a <;> simp [ones] <;> omega

/-- `3 ^ p ≤ 2 ^ k + numer v`: the constant never drops below the odd-step product. -/
private theorem le_g (v : List Bool) : 3 ^ ones v ≤ 2 ^ v.length + numer v := by
  induction v with
  | nil => simp
  | cons a t ih =>
    cases a
    · simpa [ones, numer, pow_succ] using le_trans ih (by omega)
    · have : (3 : ℕ) ^ ones t ≤ 2 ^ t.length + numer t := ih
      simp only [ones, numer, List.length_cons, pow_succ]
      calc (3 : ℕ) ^ ones t * 3 = 2 * 3 ^ ones t + 3 ^ ones t := by ring
        _ ≤ 2 * (2 ^ t.length + numer t) + 3 ^ ones t := by omega
        _ = 2 ^ t.length * 2 + (2 * numer t + 3 ^ ones t) := by ring

/-- `2 ^ k + numer v ≤ 2 ^ (k - p) * 3 ^ p`: the constant is at most one doubling per
even letter above the odd-step product. -/
private theorem g_le (v : List Bool) :
    2 ^ v.length + numer v ≤ 2 ^ (v.length - ones v) * 3 ^ ones v := by
  induction v with
  | nil => simp
  | cons a t ih =>
    have hol := ones_le_length t
    cases a
    · have hlen : (false :: t).length - ones (false :: t) = (t.length - ones t) + 1 := by
        simp [ones]; omega
      have hlen2 : t.length + 1 - ones t = (t.length - ones t) + 1 := by omega
      simp only [ones, numer, List.length_cons, hlen2, pow_succ]
      calc 2 ^ t.length * 2 + 2 * numer t = 2 * (2 ^ t.length + numer t) := by ring
        _ ≤ 2 * (2 ^ (t.length - ones t) * 3 ^ ones t) := by omega
        _ = 2 ^ (t.length - ones t) * 2 * 3 ^ ones t := by ring
    · have hlen : (true :: t).length - ones (true :: t) = t.length - ones t := by
        simp [ones]
      have hpos : (1 : ℕ) ≤ 2 ^ (t.length - ones t) := Nat.one_le_two_pow
      have hstep : (3 : ℕ) ^ ones t ≤ 2 ^ (t.length - ones t) * 3 ^ ones t :=
        Nat.le_mul_of_pos_left _ hpos
      have hlen2 : t.length + 1 - (ones t + 1) = t.length - ones t := by omega
      simp only [ones, numer, List.length_cons, hlen2, pow_succ]
      calc 2 ^ t.length * 2 + (2 * numer t + 3 ^ ones t)
          = 2 * (2 ^ t.length + numer t) + 3 ^ ones t := by ring
        _ ≤ 2 * (2 ^ (t.length - ones t) * 3 ^ ones t)
              + 2 ^ (t.length - ones t) * 3 ^ ones t := by omega
        _ = 2 ^ (t.length - ones t) * (3 ^ ones t * 3) := by ring

private theorem ones_append (u v : List Bool) : ones (u ++ v) = ones u + ones v := by
  induction u with
  | nil => simp
  | cons a t ih =>
    cases a
    · simp [ones, ih]
    · simp only [ones, List.cons_append, ih]; omega

/-- The parity trace splits along an iterate: the first `d` letters are read at `x`,
the remaining `i` letters at `tstep^[d] x`. -/
private theorem traceWord_add (d : ℕ) : ∀ (i x : ℕ),
    traceWord x (d + i) = traceWord x d ++ traceWord (tstep^[d] x) i := by
  induction d with
  | zero => intro i x; simp [traceWord]
  | succ k ih =>
    intro i x
    have hsucc : k + 1 + i = (k + i) + 1 := by omega
    rw [hsucc]
    -- both sides peel the same first letter
    by_cases hpar : x % 2 = 1
    · simp only [traceWord, hpar]
      rw [ih i (tstep x)]
      simp [Function.iterate_succ_apply]
    · have h0 : ¬ (x % 2 = 1) := hpar
      simp only [traceWord, h0]
      rw [ih i (tstep x)]
      simp [Function.iterate_succ_apply]

/-! ## The scaled strict growth bound

This replaces the paper's signed orbit.  Whenever `x < C * 2 ^ d`, the shortcut orbit
of `x` stays strictly below `C * 3 ^ p` after `d` steps, where `p` counts the odd steps
actually taken.  An even step halves the budget exactly; an odd step trades a factor `2`
for a factor `3`, which is exactly the slack the final contradiction consumes. -/
private theorem tstep_iterate_lt : ∀ (d C x : ℕ), 0 < x → 0 < C → x < C * 2 ^ d →
    tstep^[d] x < C * 3 ^ ones (traceWord x d) := by
  intro d
  induction d with
  | zero => intro C x _ _ h; simpa [traceWord] using h
  | succ k ih =>
    intro C x hx hC h
    obtain ⟨B, hB⟩ : ∃ B, C * 2 ^ k = B := ⟨_, rfl⟩
    have hBx : C * 2 ^ (k + 1) = B * 2 := by rw [← hB, pow_succ]; ring
    have hB0 : 0 < B := by
      have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      rw [← hB]; exact Nat.mul_pos hC (by omega)
    rcases Nat.even_or_odd x with he | ho
    · have hpar : x % 2 = 0 := Nat.even_iff.mp he
      have hnot : ¬ (x % 2 = 1) := by omega
      have ht : traceWord x (k + 1) = false :: traceWord (tstep x) k := by
        simp [traceWord, hnot]
      have h2 : 2 * tstep x = x := by unfold tstep; split <;> omega
      have hx' : 0 < tstep x := by omega
      have hlt : tstep x < C * 2 ^ k := by rw [hB]; omega
      have key := ih C (tstep x) hx' hC hlt
      rw [ht, Function.iterate_succ_apply]
      simpa [ones] using key
    · have hpar : x % 2 = 1 := Nat.odd_iff.mp ho
      have ht : traceWord x (k + 1) = true :: traceWord (tstep x) k := by
        simp [traceWord, hpar]
      have h2 : 2 * tstep x = 3 * x + 1 := by unfold tstep; split <;> omega
      have hx' : 0 < tstep x := by omega
      have hB3 : 3 * C * 2 ^ k = 3 * B := by rw [← hB]; ring
      have hlt : tstep x < (3 * C) * 2 ^ k := by rw [hB3]; omega
      have key := ih (3 * C) (tstep x) hx' (by omega) hlt
      rw [ht, Function.iterate_succ_apply]
      simp only [ones, pow_succ]
      calc tstep^[k] (tstep x) < 3 * C * 3 ^ ones (traceWord (tstep x) k) := key
        _ = C * (3 ^ ones (traceWord (tstep x) k) * 3) := by ring

/-! ## The two positive-orbit growth facts -/

/-- Every shortcut step contracts `x + 1` by at least the factor `2/3`. -/
private theorem tstep_iterate_le (m : ℕ) : ∀ x : ℕ,
    2 ^ m * (tstep^[m] x + 1) ≤ 3 ^ m * (x + 1) := by
  induction m with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have hone : 2 * (tstep x + 1) ≤ 3 * (x + 1) := by unfold tstep; split <;> omega
    have key := ih (tstep x)
    rw [Function.iterate_succ_apply, pow_succ, pow_succ]
    calc 2 ^ k * 2 * (tstep^[k] (tstep x) + 1)
        = 2 * (2 ^ k * (tstep^[k] (tstep x) + 1)) := by ring
      _ ≤ 2 * (3 ^ k * (tstep x + 1)) := by omega
      _ = 3 ^ k * (2 * (tstep x + 1)) := by ring
      _ ≤ 3 ^ k * (3 * (x + 1)) := Nat.mul_le_mul_left _ hone
      _ = 3 ^ k * 3 * (x + 1) := by ring

/-- On the `2`-adic cylinder `2 ^ i ∣ n + 1` the first `i` shortcut steps are all odd,
so `x + 1` grows by exactly `3/2` each step. -/
private theorem odd_run (i : ℕ) : ∀ n : ℕ, 2 ^ i ∣ n + 1 →
    2 ^ i * (tstep^[i] n + 1) = 3 ^ i * (n + 1) := by
  induction i with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hdvd
    obtain ⟨s, hs⟩ := hdvd
    have hpk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hs2 : n + 1 = 2 * (2 ^ k * s) := by rw [hs, pow_succ]; ring
    have hpar : n % 2 = 1 := by omega
    have h2 : 2 * tstep n = 3 * n + 1 := by unfold tstep; split <;> omega
    have hdvd' : 2 ^ k ∣ tstep n + 1 := by
      refine ⟨3 * s, ?_⟩
      have hg : (2 : ℕ) ^ k * (3 * s) = 3 * (2 ^ k * s) := by ring
      omega
    have key := ih (tstep n) hdvd'
    rw [Function.iterate_succ_apply, pow_succ, pow_succ]
    calc 2 ^ k * 2 * (tstep^[k] (tstep n) + 1)
        = 2 * (2 ^ k * (tstep^[k] (tstep n) + 1)) := by ring
      _ = 2 * (3 ^ k * (tstep n + 1)) := by rw [key]
      _ = 3 ^ k * (2 * tstep n + 2) := by ring
      _ = 3 ^ k * 3 * (n + 1) := by rw [h2]; ring

/-! ## The main separation -/

/-- Explicit simultaneous 2-adic and 3-adic cylinders defeat every smaller seed. -/
theorem crt_no_bounded_smaller_merge (K n : ℕ)
    (hn : 6 ^ K ≤ n) (h2 : 2 ^ K ∣ n + 1) (h3 : 3 ^ K ∣ n) :
    ∀ b : ℕ, 0 < b → b < n →
      ∀ i : ℕ, i ≤ K → ∀ j : ℕ, j ≤ K →
        tstep^[i] n ≠ tstep^[j] b := by
  intro b hb hbn i hi j hj heq
  have h6 : (1 : ℕ) ≤ 6 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hn0 : 0 < n := lt_of_lt_of_le h6 hn
  -- the all-odd run on `n`
  have hnrun : 2 ^ i * (tstep^[i] n + 1) = 3 ^ i * (n + 1) :=
    odd_run i n (dvd_trans (pow_dvd_pow 2 hi) h2)
  -- step 1: the merge depth on `b` must strictly exceed the depth on `n`
  have hji : i < j := by
    by_contra hcon
    have hjle : j ≤ i := by omega
    have hup : 2 ^ j * (tstep^[j] b + 1) ≤ 3 ^ j * (b + 1) := tstep_iterate_le j b
    rw [← heq] at hup
    -- 3 ^ i * (n+1) = 2 ^ (i-j) * (2 ^ j * (tstep^[i] n + 1)) ≤ 2 ^ (i-j) * 3 ^ j * (b+1)
    have hsplit : (2 : ℕ) ^ i = 2 ^ (i - j) * 2 ^ j := by
      rw [← pow_add]; congr 1; omega
    have hchain : 3 ^ i * (n + 1) ≤ 2 ^ (i - j) * 3 ^ j * (b + 1) := by
      calc (3 : ℕ) ^ i * (n + 1) = 2 ^ (i - j) * (2 ^ j * (tstep^[i] n + 1)) := by
            rw [← hnrun, hsplit]; ring
        _ ≤ 2 ^ (i - j) * (3 ^ j * (b + 1)) := Nat.mul_le_mul_left _ hup
        _ = 2 ^ (i - j) * 3 ^ j * (b + 1) := by ring
    have h23 : (2 : ℕ) ^ (i - j) ≤ 3 ^ (i - j) := Nat.pow_le_pow_left (by norm_num) _
    have hfold : (2 : ℕ) ^ (i - j) * 3 ^ j ≤ 3 ^ i := by
      calc (2 : ℕ) ^ (i - j) * 3 ^ j ≤ 3 ^ (i - j) * 3 ^ j :=
            Nat.mul_le_mul_right _ h23
        _ = 3 ^ i := by rw [← pow_add]; congr 1; omega
    have : (3 : ℕ) ^ i * (n + 1) ≤ 3 ^ i * (b + 1) :=
      le_trans hchain (Nat.mul_le_mul_right _ hfold)
    have h3p : (0 : ℕ) < 3 ^ i := Nat.pow_pos (by norm_num)
    have := Nat.le_of_mul_le_mul_left this h3p
    omega
  set d := j - i with hd
  have hd0 : 0 < d := by omega
  have hjd : j = d + i := by omega
  -- step 2: the affine relation of the length-`j` word on `b`
  set v := traceWord b j with hv
  set p := ones v with hp
  set gw := 2 ^ j + numer v with hgw
  have hvlen : v.length = j := by rw [hv]; exact traceWord_length b j
  have hpj : p ≤ j := by rw [hp, ← hvlen]; exact ones_le_length v
  have hid : 2 ^ j * tstep^[j] b = 3 ^ p * b + numer v := by
    rw [hv, hp]; exact tstep_iterate_identity j b
  have hsplit2 : (2 : ℕ) ^ j = 2 ^ d * 2 ^ i := by rw [← pow_add, hjd]
  -- `2 ^ i * tstep^[i] n = 3 ^ i * n + 3 ^ i - 2 ^ i`, kept additive
  have hni : 2 ^ i * tstep^[i] n + 2 ^ i = 3 ^ i * n + 3 ^ i := by
    have : 2 ^ i * (tstep^[i] n + 1) = 3 ^ i * (n + 1) := hnrun
    ring_nf at this ⊢; omega
  -- the master equation `3 ^ p * b + gw = 2 ^ d * 3 ^ i * n + 2 ^ d * 3 ^ i`
  have master : 3 ^ p * b + gw = 2 ^ d * 3 ^ i * n + 2 ^ d * 3 ^ i := by
    have e1 : 3 ^ p * b + numer v = 2 ^ d * (2 ^ i * tstep^[i] n) := by
      rw [← hid, ← heq, hsplit2]; ring
    have e2 : 2 ^ d * (2 ^ i * tstep^[i] n) + 2 ^ d * 2 ^ i
        = 2 ^ d * 3 ^ i * n + 2 ^ d * 3 ^ i := by
      calc 2 ^ d * (2 ^ i * tstep^[i] n) + 2 ^ d * 2 ^ i
          = 2 ^ d * (2 ^ i * tstep^[i] n + 2 ^ i) := by ring
        _ = 2 ^ d * (3 ^ i * n + 3 ^ i) := by rw [hni]
        _ = 2 ^ d * 3 ^ i * n + 2 ^ d * 3 ^ i := by ring
    have e3 : (2 : ℕ) ^ d * 2 ^ i = 2 ^ j := hsplit2.symm
    rw [hgw]; omega
  -- the constant bounds
  have hglow : 3 ^ p ≤ gw := by rw [hgw, hp, ← hvlen]; exact le_g v
  have hghigh : gw ≤ 2 ^ (j - p) * 3 ^ p := by
    rw [hgw, hp, ← hvlen]; exact g_le v
  have hgsmall : gw ≤ 6 ^ K := by
    have hb1 : (2 : ℕ) ^ (j - p) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb2 : (3 : ℕ) ^ p ≤ 3 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc gw ≤ 2 ^ (j - p) * 3 ^ p := hghigh
      _ ≤ 2 ^ K * 3 ^ K := Nat.mul_le_mul hb1 hb2
      _ = 6 ^ K := by rw [← Nat.mul_pow]
  -- step 3: trichotomy on the slope `2 ^ d * 3 ^ i` versus `3 ^ p`
  rcases lt_trichotomy (2 ^ d * 3 ^ i) (3 ^ p) with hcase | hcase | hcase
  · -- contracting slope: the genuine case
    have hpi : i < p := by
      by_contra hcon
      have : (3 : ℕ) ^ p ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2d : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
      have h3i : (0 : ℕ) < 3 ^ i := Nat.pow_pos (by norm_num)
      have : (3 : ℕ) ^ i ≤ 2 ^ d * 3 ^ i := Nat.le_mul_of_pos_left _ (by omega)
      omega
    set q := p - i with hq
    have hq0 : 0 < q := by omega
    have hpq : p = q + i := by omega
    have hqK : q ≤ K := by omega
    -- `N = n / 3 ^ q`
    have h3q : 3 ^ q ∣ n := dvd_trans (pow_dvd_pow 3 hqK) h3
    obtain ⟨N, hN⟩ := h3q
    have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h] at hN; omega
      · exact h
    -- `3 ^ p * b + gw = 3 ^ p * (2 ^ d * N) + 2 ^ d * 3 ^ i`
    have master' : 3 ^ p * b + gw = 3 ^ p * (2 ^ d * N) + 2 ^ d * 3 ^ i := by
      have : (2 : ℕ) ^ d * 3 ^ i * n = 3 ^ p * (2 ^ d * N) := by
        rw [hN, hpq, pow_add]; ring
      rw [master, this]
    have h3pp : (0 : ℕ) < 3 ^ p := Nat.pow_pos (by norm_num)
    have hblt : b < 2 ^ d * N := by
      by_contra hcon
      have hge : 2 ^ d * N ≤ b := by omega
      have : 3 ^ p * (2 ^ d * N) ≤ 3 ^ p * b := Nat.mul_le_mul_left _ hge
      omega
    -- step 4: split the word at depth `d`
    -- step 4: split the length-`j` word at depth `d`
    set y := tstep^[d] b with hy
    set v1 := traceWord b d with hv1
    set v2 := traceWord y i with hv2
    have hvsplit : v = v1 ++ v2 := by
      rw [hv, hv1, hv2, hy, hjd]; exact traceWord_add d i b
    set p0 := ones v1 with hp0
    set a' := ones v2 with ha'
    have hpsum : p = p0 + a' := by rw [hp, hvsplit, hp0, ha']; exact ones_append v1 v2
    have hv2len : v2.length = i := by rw [hv2]; exact traceWord_length y i
    have ha'i : a' ≤ i := by rw [ha', ← hv2len]; exact ones_le_length v2
    set a := p0 - q with ha
    have hai : a' = i - a := by omega
    have hp0aq : p0 = a + q := by omega
    -- the growth bound replaces the paper's signed orbit
    have hylt : y < N * 3 ^ p0 := by
      have hblt' : b < N * 2 ^ d := by rw [Nat.mul_comm]; exact hblt
      rw [hy, hp0, hv1]; exact tstep_iterate_lt d N b hb hN0 hblt' 
    have hyn : N * 3 ^ p0 = 3 ^ a * n := by rw [hp0aq, hN, pow_add]; ring
    have hylt' : y + 1 ≤ 3 ^ a * n := by omega
    -- the tail affine relation, with the common `3 ^ i * n` cancelled
    have htail : 2 ^ i * tstep^[i] y = 3 ^ a' * y + numer v2 := by
      rw [hv2, ha']; exact tstep_iterate_identity i y
    have hmeet : tstep^[i] y = tstep^[i] n := by
      have hjy : tstep^[i] y = tstep^[j] b := by
        rw [hy, ← Function.iterate_add_apply]; congr 1; omega
      rw [hjy, ← heq]
    have hkey : 3 ^ (i - a) * y + (2 ^ i + numer v2) = 3 ^ i * n + 3 ^ i := by
      rw [hai, hmeet] at htail; omega
    -- the tail constant bound
    have hg2 : 2 ^ i + numer v2 ≤ 2 ^ a * 3 ^ (i - a) := by
      have hgg := g_le v2
      rw [hv2len, ← ha', hai] at hgg
      have hia : i - (i - a) = a := by omega
      rwa [hia] at hgg
    have hE : (1 : ℕ) ≤ 3 ^ (i - a) := Nat.one_le_pow _ _ (by norm_num)
    have hEa : 3 ^ (i - a) * 3 ^ a = 3 ^ i := by rw [← pow_add]; congr 1; omega
    have hmul : 3 ^ (i - a) * y + 3 ^ (i - a) ≤ 3 ^ i * n := by
      calc 3 ^ (i - a) * y + 3 ^ (i - a) = 3 ^ (i - a) * (y + 1) := by ring
        _ ≤ 3 ^ (i - a) * (3 ^ a * n) := Nat.mul_le_mul_left _ hylt'
        _ = 3 ^ i * n := by rw [← mul_assoc, hEa]
    have h23a : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) _
    have hshrink : 2 ^ a * 3 ^ (i - a) ≤ 3 ^ a * 3 ^ (i - a) :=
      Nat.mul_le_mul_right _ h23a
    have h3i : 3 ^ a * 3 ^ (i - a) = 3 ^ i := by rw [mul_comm]; exact hEa
    have hcontra : 3 ^ i + 3 ^ (i - a) ≤ 3 ^ i :=
      calc 3 ^ i + 3 ^ (i - a) ≤ 2 ^ i + numer v2 := by omega
        _ ≤ 2 ^ a * 3 ^ (i - a) := hg2
        _ ≤ 3 ^ a * 3 ^ (i - a) := hshrink
        _ = 3 ^ i := h3i
    omega
  · -- `2 ^ d * 3 ^ i = 3 ^ p` is impossible: the left side is even, the right is odd
    have heven : (2 : ℕ) ∣ 2 ^ d * 3 ^ i :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [hcase] at heven
    have : ¬ (2 : ℕ) ∣ 3 ^ p := by
      intro hdd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdd
      omega
    exact this heven
  · -- expanding slope forces `b > n`
    have hdelta : 3 ^ p + 1 ≤ 2 ^ d * 3 ^ i := by omega
    have h3i : (0 : ℕ) < 3 ^ i := Nat.pow_pos (by norm_num)
    have hbig : 3 ^ p * n + n ≤ 2 ^ d * 3 ^ i * n :=
      calc 3 ^ p * n + n = (3 ^ p + 1) * n := by ring
        _ ≤ 2 ^ d * 3 ^ i * n := Nat.mul_le_mul_right _ hdelta
    have h3pp : (0 : ℕ) < 3 ^ p := Nat.pow_pos (by norm_num)
    have : 3 ^ p * n < 3 ^ p * b := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega

/-- Arbitrarily large starts evade all smaller seeds at any prescribed depth. -/
theorem arbitrarily_large_no_bounded_smaller_merge (K M : ℕ) :
    ∃ n : ℕ, M < n ∧
      ∀ b : ℕ, 0 < b → b < n →
        ∀ i : ℕ, i ≤ K → ∀ j : ℕ, j ≤ K →
          tstep^[i] n ≠ tstep^[j] b := by
  have hcop : Nat.Coprime (3 ^ K) (2 ^ K) := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨n0, hA, hB⟩ := Nat.chineseRemainder hcop 0 (2 ^ K - 1)
  have h2K : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_two_pow
  have h6K : (1 : ℕ) ≤ 6 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have h6eq : (6 : ℕ) ^ K = 2 ^ K * 3 ^ K := by
    rw [← Nat.mul_pow]
  have h30 : 3 ^ K ∣ n0 := (Nat.modEq_zero_iff_dvd).mp hA
  have h20 : 2 ^ K ∣ n0 + 1 := by
    have hmod : n0 % 2 ^ K = 2 ^ K - 1 := by
      have := hB
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨t, ht⟩ : ∃ t, n0 = 2 ^ K * t + n0 % 2 ^ K :=
      ⟨n0 / 2 ^ K, (Nat.div_add_mod n0 (2 ^ K)).symm⟩
    exact ⟨t + 1, by rw [ht, hmod]; ring_nf; omega⟩
  refine ⟨n0 + 6 ^ K * (M + 1), ?_, ?_⟩
  · have : M + 1 ≤ 6 ^ K * (M + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · refine crt_no_bounded_smaller_merge K _ ?_ ?_ ?_
    · have : 6 ^ K * 1 ≤ 6 ^ K * (M + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · have hd2 : 2 ^ K ∣ 6 ^ K * (M + 1) :=
        Dvd.dvd.mul_right ⟨3 ^ K, h6eq⟩ _
      obtain ⟨u, hu⟩ := h20
      obtain ⟨w, hw⟩ := hd2
      have hdist : (2 : ℕ) ^ K * (u + w) = 2 ^ K * u + 2 ^ K * w := by ring
      exact ⟨u + w, by omega⟩
    · have hd3 : 3 ^ K ∣ 6 ^ K * (M + 1) :=
        Dvd.dvd.mul_right ⟨2 ^ K, by rw [h6eq]; ring⟩ _
      exact Nat.dvd_add h30 hd3

/-! ## Non-vacuity anchors

The hypotheses are satisfiable and the conclusion has content: the kickoff's hand
controls `K = 1, n = 9` and `K = 2, n = 63` sit in the cylinder, and a direct decision
procedure confirms that no smaller positive seed meets them within the stated depths.
The countercontrol `n = 31` (outside the K = 3 cylinder, since `27 ∤ 31`) does admit the
smaller seed `27` at depths `0` and `3`, so the cylinder hypotheses are doing work. -/

example : 6 ^ 1 ≤ 9 ∧ 2 ^ 1 ∣ 9 + 1 ∧ 3 ^ 1 ∣ 9 := by decide

example : ∀ b < 9, 0 < b → ∀ i ≤ 1, ∀ j ≤ 1, tstep^[i] 9 ≠ tstep^[j] b := by decide

example : 6 ^ 2 ≤ 63 ∧ 2 ^ 2 ∣ 63 + 1 ∧ 3 ^ 2 ∣ 63 := by decide

example : ∀ b < 63, 0 < b → ∀ i ≤ 2, ∀ j ≤ 2, tstep^[i] 63 ≠ tstep^[j] b := by decide

/-- The countercontrol: `31` fails the ternary divisibility at `K = 3` and does merge with
the smaller seed `27`, at depths `0` and `3`. -/
example : tstep^[0] 31 = tstep^[3] 27 := by decide

end CollatzMoonshot.Obstructions.BoundedMerger
