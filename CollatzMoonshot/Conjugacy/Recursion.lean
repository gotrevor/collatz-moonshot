/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.Ladder

/-!
# The bias recursion and Terras at depth `j`

Two exact identities for the first beyond-Terras letter, both corollaries of the lift identity
`tstep_iterate_add_mul_two_pow`.

* **The mod-3 recursion** (`bias_succ`): `bias (m+1) = 2 · bias m − 2 · biasClass m c`, where
  `biasClass m c` is the bias restricted to starts `y ≡ c (mod 3)` and `c = (2 − 2^m) mod 3`.
  Splitting `range (2^(m+1))` into evens and odds, the even half is `bias m` on the nose
  (`tstep (2s) = s`), and the odd half is the bias of `tstep^[m]` over the starts `3s + 2 < 3 · 2^m`;
  three blocks of length `2^m`, each a residue class mod 3 of the base start, with signs
  `+, −, +` by the lift identity.
* **Parity** (`bias_mod_four`): `bias j ≡ 2 (mod 4)` for `j ≥ 1`, because the class in the
  recursion has odd size (`(4^e − 1)/3` and `(2 · 4^e + 1)/3` are odd).  So the first
  beyond-Terras letter is never exactly balanced (`bias_ne_zero`), and `BiasDecays` cannot be
  witnessed by an exact zero.
* **Terras at depth `j`** (`depth_count`): over `(j+i)`-bit starts, the `j`-th iterate is
  equidistributed mod `2^i`: each residue is hit exactly `2^j` times.  The lift identity with
  `c = 2^i` is the induction step.  Its antisymmetric reading `depth_antisymm` says the two
  lifts of a residue mod `2^i` to residues mod `2^(i+1)` split the `2^j` hits between them.
* **Windows** (`bias_window`): over every aligned window `[c · 2^j, (c+1) · 2^j)` the sign sum is
  `(−1)^c · bias j`: the bias is a constant of the level, not a small-numbers effect.
* **The decay conjecture, exactly** (`biasDecays_iff_classFluct`): `BiasDecays` holds iff the signed
  mass of the leaking class `leakClass m` is asymptotically one third of `bias m`, at the scale
  `2^m`.  The recursion in the normalised variable `x m = bias m / 2^m` reads
  `x (m+1) = (2/3) · x m − y m`, a contraction with forcing `y`; `x → 0` iff `y → 0`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Elementary helpers -/

/-- `tstep` halves an even number. -/
theorem tstep_two_mul (s : ℕ) : tstep (2 * s) = s := by
  unfold tstep; split_ifs <;> omega

/-- `tstep (2s + 1) = 3s + 2`. -/
theorem tstep_two_mul_add_one (s : ℕ) : tstep (2 * s + 1) = 3 * s + 2 := by
  unfold tstep; split_ifs <;> omega

/-- A sum over `range (2n)` folded into even and odd terms. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n), g r = ∑ s ∈ Finset.range n, (g (2 * s) + g (2 * s + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      add_assoc]

theorem two_pow_mod_three (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- The sign of the `j`-th iterate flips under `+ 2^j` (because `3^a` is odd). -/
theorem sign_add_two_pow (j r : ℕ) :
    (if tstep^[j] (r + 2 ^ j) % 2 = 0 then (1 : ℤ) else -1)
      = -(if tstep^[j] r % 2 = 0 then (1 : ℤ) else -1) := by
  rw [tstep_iterate_add_two_pow]
  have h3 := three_pow_mod_two (oddCount r j)
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h
  · have : (tstep^[j] r + 3 ^ oddCount r j) % 2 = 1 := by omega
    simp [h, this]
  · have : (tstep^[j] r + 3 ^ oddCount r j) % 2 = 0 := by omega
    simp [h, this]

/-- The sign of the `j`-th iterate is unchanged under `+ 2 · 2^j`. -/
theorem sign_add_two_mul_two_pow (j r : ℕ) :
    (if tstep^[j] (r + 2 * 2 ^ j) % 2 = 0 then (1 : ℤ) else -1)
      = (if tstep^[j] r % 2 = 0 then (1 : ℤ) else -1) := by
  rw [tstep_iterate_add_mul_two_pow]
  have : (tstep^[j] r + 2 * 3 ^ oddCount r j) % 2 = tstep^[j] r % 2 := by omega
  rw [this]

/-! ## The bias on a residue class mod 3 -/

/-- The bias restricted to one residue class mod 3 of the start:
`biasClass k c = ∑_{y < 2^k, y ≡ c (3)} (−1)^(tstep^[k] y)`. -/
def biasClass (k c : ℕ) : ℤ :=
  ∑ y ∈ (Finset.range (2 ^ k)).filter (fun y => y % 3 = c),
    (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1)

/-- The three classes add up to the bias. -/
theorem biasClass_add (k : ℕ) : biasClass k 0 + biasClass k 1 + biasClass k 2 = bias k := by
  unfold biasClass bias
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.range (2 ^ k)) (t := Finset.range 3)
    (g := fun y => y % 3) (fun y _ => Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    (fun y => (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1))
  rw [← h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-! ## The mod-3 recursion -/

theorem bias_succ_check_0 : bias 1 = 2 * bias 0 - 2 * biasClass 0 ((2 + 2 * (2 ^ 0 % 3)) % 3) := by
  decide
theorem bias_succ_check_1 : bias 2 = 2 * bias 1 - 2 * biasClass 1 ((2 + 2 * (2 ^ 1 % 3)) % 3) := by
  decide
theorem bias_succ_check_2 : bias 3 = 2 * bias 2 - 2 * biasClass 2 ((2 + 2 * (2 ^ 2 % 3)) % 3) := by
  decide
theorem bias_succ_check_3 : bias 4 = 2 * bias 3 - 2 * biasClass 3 ((2 + 2 * (2 ^ 3 % 3)) % 3) := by
  decide
theorem bias_succ_check_4 : bias 5 = 2 * bias 4 - 2 * biasClass 4 ((2 + 2 * (2 ^ 4 % 3)) % 3) := by
  decide
theorem bias_succ_check_5 : bias 6 = 2 * bias 5 - 2 * biasClass 5 ((2 + 2 * (2 ^ 5 % 3)) % 3) := by
  decide

/-- The odd half of `bias (m+1)`, reindexed by the odd starts `3s + 2 < 3 · 2^m`. -/
theorem bias_odd_half_reindex (m : ℕ) :
    ∑ s ∈ Finset.range (2 ^ m), (if tstep^[m] (3 * s + 2) % 2 = 0 then (1 : ℤ) else -1)
      = ∑ y ∈ Finset.range (3 * 2 ^ m),
          (if y % 3 = 2 then (if tstep^[m] y % 2 = 0 then (1 : ℤ) else -1) else 0) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun s => 3 * s + 2) (fun y => y / 3)
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢; omega
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_range] at hy; omega
  · intro s _; rfl

/-- **The mod-3 recursion.**  `bias (m+1) = 2 · bias m − 2 · biasClass m c` with
`c = (2 − 2^m) mod 3 = (2 + 2 · (2^m mod 3)) mod 3`.  The even starts `2s` contribute `bias m`
exactly; the odd starts `2s + 1` go to `3s + 2`, and as `s` runs over `range (2^m)` these run over
the starts `y < 3 · 2^m` with `y ≡ 2 (mod 3)`, three blocks of length `2^m` with signs `+, −, +`
by the lift identity, i.e. `biasClass m 2 − biasClass m c + biasClass m c'` where `{2, c, c'}`
are the three residues; by `biasClass_add` this is `bias m − 2 · biasClass m c`.  Checked by
`decide` for `m ≤ 5` (`bias_succ_check_0` … `bias_succ_check_5`). -/
theorem bias_succ (m : ℕ) :
    bias (m + 1) = 2 * bias m - 2 * biasClass m ((2 + 2 * (2 ^ m % 3)) % 3) := by
  -- the even/odd split
  have hsplit : bias (m + 1) = bias m +
      ∑ s ∈ Finset.range (2 ^ m), (if tstep^[m] (3 * s + 2) % 2 = 0 then (1 : ℤ) else -1) := by
    unfold bias
    rw [pow_succ, mul_comm, sum_range_two_mul, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun s _ => by rw [Function.iterate_succ_apply, tstep_two_mul]
    · exact Finset.sum_congr rfl fun s _ => by
        rw [Function.iterate_succ_apply, tstep_two_mul_add_one]
  -- the three blocks of the odd half
  have hthree : 3 * 2 ^ m = 2 ^ m + 2 ^ m + 2 ^ m := by ring
  have hB1 : ∑ y ∈ Finset.range (2 ^ m),
      (if y % 3 = 2 then (if tstep^[m] y % 2 = 0 then (1 : ℤ) else -1) else 0) = biasClass m 2 := by
    rw [biasClass, Finset.sum_filter]
  have hB2 : ∑ y ∈ Finset.range (2 ^ m),
      (if (2 ^ m + y) % 3 = 2 then (if tstep^[m] (2 ^ m + y) % 2 = 0 then (1 : ℤ) else -1) else 0)
        = -biasClass m ((2 + 2 * (2 ^ m % 3)) % 3) := by
    rw [biasClass, Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : (2 ^ m + y) % 3 = 2 ↔ y % 3 = (2 + 2 * (2 ^ m % 3)) % 3 := by omega
    rw [add_comm (2 ^ m) y, sign_add_two_pow, add_comm y (2 ^ m)]
    simp only [hc]
    split_ifs <;> simp
  have hB3 : ∑ y ∈ Finset.range (2 ^ m),
      (if (2 ^ m + 2 ^ m + y) % 3 = 2 then
        (if tstep^[m] (2 ^ m + 2 ^ m + y) % 2 = 0 then (1 : ℤ) else -1) else 0)
        = biasClass m ((2 + 2 ^ m % 3) % 3) := by
    rw [biasClass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : (2 ^ m + 2 ^ m + y) % 3 = 2 ↔ y % 3 = (2 + 2 ^ m % 3) % 3 := by omega
    have e : 2 ^ m + 2 ^ m + y = y + 2 * 2 ^ m := by ring
    rw [e, sign_add_two_mul_two_pow, ← e]
    simp only [hc]
  rw [hsplit, bias_odd_half_reindex, hthree, Finset.sum_range_add, Finset.sum_range_add, hB1, hB2,
    hB3]
  have hadd := biasClass_add m
  rcases two_pow_mod_three m with h | h <;> rw [h] <;> norm_num <;> linarith

/-! ## Parity: the bias is `2 mod 4` -/

/-- The number of `y < n` with `y ≡ c (mod 3)`, for `c < 3`. -/
theorem card_filter_mod_three (n c : ℕ) (hc : c < 3) :
    ((Finset.range n).filter (fun y => y % 3 = c)).card = (n + 2 - c) / 3 := by
  induction n with
  | zero => simp; omega
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

/-- `biasClass k c ≡ #{y < 2^k : y ≡ c (3)} (mod 2)`: each term is `±1`. -/
theorem biasClass_mod_two_eq_card (k c : ℕ) :
    biasClass k c % 2 = (((Finset.range (2 ^ k)).filter (fun y => y % 3 = c)).card : ℤ) % 2 := by
  unfold biasClass
  rw [Finset.sum_int_mod]
  have : ∀ y ∈ (Finset.range (2 ^ k)).filter (fun y => y % 3 = c),
      (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1) % 2 = 1 := by
    intro y _; split_ifs <;> decide
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The class size in the recursion is odd for `m ≥ 1`: `(2^m + 2 − c) / 3` with
`c = (2 + 2 · (2^m mod 3)) mod 3`, i.e. `(4^e − 1)/3` or `(2 · 4^e + 1)/3`. -/
theorem class_size_odd (m : ℕ) (hm : 1 ≤ m) :
    ((2 ^ m + 2 - (2 + 2 * (2 ^ m % 3)) % 3) / 3) % 2 = 1 := by
  rcases m with _ | _ | m
  · omega
  · decide
  · have e : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
    rw [e]
    rcases two_pow_mod_three m with h | h <;> omega

theorem biasClass_odd (m : ℕ) (hm : 1 ≤ m) :
    biasClass m ((2 + 2 * (2 ^ m % 3)) % 3) % 2 = 1 := by
  rw [biasClass_mod_two_eq_card, card_filter_mod_three _ _ (Nat.mod_lt _ (by norm_num))]
  have := class_size_odd m hm
  omega

/-- **The bias is `2 mod 4`.**  For `j ≥ 1`, `bias j ≡ 2 (mod 4)`: by `bias_succ`,
`bias (m+1) = 2 · (bias m − biasClass m c)`, and the bracket is odd because `bias m` is even and
the class has odd size (`class_size_odd`).  In particular the first beyond-Terras letter is never
exactly balanced (`bias_ne_zero`): the correlation `bias j / 2^j` is never `0`, so `BiasDecays` is
a genuine limit statement, not witnessed by an exact zero at any level.  Numerics (2026-10-21):
`bias j % 4 = 2` for every computed `j ≤ 31`. -/
theorem bias_mod_four (j : ℕ) (hj : 1 ≤ j) : bias j % 4 = 2 := by
  induction j with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [bias_one]; rfl
    · have h1 := ih hm
      have h2 := biasClass_odd m hm
      rw [bias_succ]
      omega

/-- The first beyond-Terras letter is never exactly balanced. -/
theorem bias_ne_zero (j : ℕ) (hj : 1 ≤ j) : bias j ≠ 0 := by
  have := bias_mod_four j hj
  omega

/-! ## Terras at depth `j` -/

/-- A residue mod `2P` is a residue mod `P` together with the bit `(y / P) % 2`. -/
theorem mod_two_mul_eq_iff (P y c : ℕ) :
    y % (2 * P) = c ↔ y % P = c % P ∧ y / P % 2 = c / P := by
  constructor
  · rintro rfl
    refine ⟨(Nat.mod_mod_of_dvd y (dvd_mul_left P 2)).symm, ?_⟩
    rw [mul_comm, Nat.mod_mul_right_div_self]
  · rintro ⟨h1, h2⟩
    rw [mul_comm, Nat.mod_mul, h1, h2, Nat.mod_add_div]

/-- The indicator bookkeeping of the induction step: for `P > 0`, `o` odd and `c < 2P`, exactly
one of `y`, `y + P · o` is `≡ c (mod 2P)` when `y ≡ c (mod P)`, and neither is otherwise. -/
theorem indicator_add_eq {P y c o : ℕ} (hP : 0 < P) (ho : o % 2 = 1) (hc : c < 2 * P) :
    (if y % (2 * P) = c then 1 else 0) + (if (y + P * o) % (2 * P) = c then 1 else 0)
      = if y % P = c % P then 1 else 0 := by
  have h1 : (y + P * o) % (2 * P) = (y + P) % (2 * P) := by
    have e : y + P * o = (y + P) + (2 * P) * (o / 2) := by
      have := Nat.div_add_mod o 2
      rw [ho] at this
      calc y + P * o = y + P * (2 * (o / 2) + 1) := by rw [this]
        _ = (y + P) + (2 * P) * (o / 2) := by ring
    rw [e, Nat.add_mul_mod_self_left]
  rw [h1]
  simp only [mod_two_mul_eq_iff, Nat.add_mod_right, Nat.add_div_right _ hP]
  have hd : c / P < 2 := (Nat.div_lt_iff_lt_mul hP).2 (by linarith)
  generalize c / P = d at *
  generalize y / P = q at *
  split_ifs <;> omega

/-- **Terras at depth `j`.**  Over the `(j+i)`-bit starts, the `j`-th iterate is equidistributed
mod `2^i`: each residue `c < 2^i` is hit exactly `2^j` times.  Induction on `i`: the lift identity
with `c = 2^i` says `tstep^[j] (r + 2^(j+i)) = tstep^[j] r + 2^i · 3^a`, and since `3^a` is odd
exactly one of the two lifts of `r` lands on each residue mod `2^(i+1)` above a given residue
mod `2^i`. -/
theorem depth_count (j i c : ℕ) (hc : c < 2 ^ i) :
    ((Finset.range (2 ^ (j + i))).filter (fun r => tstep^[j] r % 2 ^ i = c)).card = 2 ^ j := by
  induction i generalizing c with
  | zero =>
    have : c = 0 := by simpa using hc
    subst this
    have hall : (Finset.range (2 ^ (j + 0))).filter (fun r => tstep^[j] r % 2 ^ 0 = 0)
        = Finset.range (2 ^ j) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Nat.add_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, Nat.mod_one _⟩⟩
    rw [hall, Finset.card_range]
  | succ i ih =>
    have hP : 0 < 2 ^ i := by positivity
    have key : ∀ r, ((if tstep^[j] r % 2 ^ (i + 1) = c then 1 else 0) +
        (if tstep^[j] (2 ^ (j + i) + r) % 2 ^ (i + 1) = c then 1 else 0) : ℕ)
          = if tstep^[j] r % 2 ^ i = c % 2 ^ i then 1 else 0 := by
      intro r
      have e : 2 ^ (j + i) + r = r + 2 ^ i * 2 ^ j := by ring
      rw [e, tstep_iterate_add_mul_two_pow, pow_succ']
      exact indicator_add_eq hP (three_pow_mod_two _) (by rw [← pow_succ']; exact hc)
    have e2 : 2 ^ (j + (i + 1)) = 2 ^ (j + i) + 2 ^ (j + i) := by ring
    rw [Finset.card_filter, e2, Finset.sum_range_add, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun r _ => key r, ← Finset.card_filter]
    exact ih (c % 2 ^ i) (Nat.mod_lt _ hP)

/-- A residue mod `2^i` is exactly one of its two lifts mod `2^(i+1)`. -/
theorem mod_two_pow_eq_iff_or {i y c : ℕ} (hc : c < 2 ^ i) :
    y % 2 ^ i = c ↔ y % 2 ^ (i + 1) = c ∨ y % 2 ^ (i + 1) = c + 2 ^ i := by
  have hP : 0 < 2 ^ i := by positivity
  simp only [pow_succ', mod_two_mul_eq_iff, Nat.add_mod_right, Nat.add_div_right _ hP,
    Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc]
  omega

/-- **Antisymmetry at depth `j`.**  The two lifts of a residue `c < 2^i` to residues mod
`2^(i+1)` share the `2^j` hits of `depth_count`. -/
theorem depth_antisymm (j i c : ℕ) (hc : c < 2 ^ i) :
    ((Finset.range (2 ^ (j + i))).filter (fun r => tstep^[j] r % 2 ^ (i + 1) = c)).card +
      ((Finset.range (2 ^ (j + i))).filter
        (fun r => tstep^[j] r % 2 ^ (i + 1) = c + 2 ^ i)).card = 2 ^ j := by
  rw [← depth_count j i c hc, ← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · exact congrArg Finset.card (Finset.filter_congr fun r _ => (mod_two_pow_eq_iff_or hc).symm)
  · rw [Finset.disjoint_filter]
    intro r _ h1 h2
    have : 0 < 2 ^ i := by positivity
    omega

/-! ## Two readings of the bias -/

/-- The bias as a count: `bias j = 2 · #{r < 2^j : tstep^[j] r even} − 2^j`. -/
theorem bias_eq_two_mul_card_sub (j : ℕ) :
    bias j = 2 * (((Finset.range (2 ^ j)).filter (fun r => tstep^[j] r % 2 = 0)).card : ℤ)
      - 2 ^ j := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 ^ j)) (fun r => tstep^[j] r % 2 = 0)
  rw [Finset.card_range] at h
  have h' : ((((Finset.range (2 ^ j)).filter (fun r => tstep^[j] r % 2 = 0)).card : ℤ) +
      (((Finset.range (2 ^ j)).filter (fun r => ¬ tstep^[j] r % 2 = 0)).card : ℤ)) = 2 ^ j := by
    exact_mod_cast h
  unfold bias
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  linarith

/-- **Windows.**  Over every aligned window `[c · 2^j, (c+1) · 2^j)` the sign sum is
`(−1)^c · bias j`: reindexing `r = r₀ + c · 2^j`, the lift identity gives
`tstep^[j] r = tstep^[j] r₀ + c · 3^a`, whose parity flips exactly when `c` is odd.  The bias is
a constant of the level, not a small-numbers effect. -/
theorem bias_window (j c : ℕ) :
    ∑ r ∈ Finset.Ico (c * 2 ^ j) ((c + 1) * 2 ^ j),
      (if tstep^[j] r % 2 = 0 then (1 : ℤ) else -1) = (-1) ^ c * bias j := by
  have e : (c + 1) * 2 ^ j = c * 2 ^ j + 2 ^ j := by ring
  rw [e, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, bias, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [add_comm (c * 2 ^ j) r, tstep_iterate_add_mul_two_pow]
  have hpar : (c * 3 ^ oddCount r j) % 2 = c % 2 := by
    rw [Nat.mul_mod, three_pow_mod_two, mul_one, Nat.mod_mod]
  rcases Nat.even_or_odd c with hc | hc
  · have hc2 := Nat.even_iff.1 hc
    have : (tstep^[j] r + c * 3 ^ oddCount r j) % 2 = tstep^[j] r % 2 := by omega
    rw [this, hc.neg_one_pow, one_mul]
  · have hc2 := Nat.odd_iff.1 hc
    have : (tstep^[j] r + c * 3 ^ oddCount r j) % 2 = (tstep^[j] r + 1) % 2 := by omega
    rw [this, hc.neg_one_pow]
    rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h
    · have : (tstep^[j] r + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (tstep^[j] r + 1) % 2 = 0 := by omega
      simp [h, this]

/-! ## The decay conjecture through the recursion -/

/-- The residue class of the start mod 3 that leaks in `bias_succ`: `c_{m+1} = (2 − 2^m) mod 3`, so
`bias (m+1) = 2 · bias m − 2 · biasClass m (leakClass m)`.  It alternates `0, 1, 0, 1, …` from
`m = 1` (`leakClass 0 = 1`). -/
def leakClass (m : ℕ) : ℕ := (2 + 2 * (2 ^ m % 3)) % 3

theorem bias_succ_leakClass (m : ℕ) :
    bias (m + 1) = 2 * bias m - 2 * biasClass m (leakClass m) :=
  bias_succ m

/-- The recursion in the normalised variable `x m = bias m / 2^m`:
`x (m+1) = (2/3) · x m − y m`, where `y m = (biasClass m (leakClass m) − bias m / 3) / 2^m` is the
excess of the leaking class over one third of the total, at the scale of the level. -/
theorem bias_div_succ (m : ℕ) :
    (bias (m + 1) : ℝ) / 2 ^ (m + 1) = 2 / 3 * ((bias m : ℝ) / 2 ^ m)
      - ((biasClass m (leakClass m) : ℝ) - (bias m : ℝ) / 3) / 2 ^ m := by
  rw [bias_succ_leakClass]
  push_cast
  have h : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_succ]
  field_simp
  ring

/-- A contraction with vanishing forcing converges to `0`: if `|x (m+1)| ≤ r · |x m| + |y m|` with
`0 ≤ r < 1` and `y → 0`, then `x → 0`.  (For `ε > 0` pick `M` with `|y m| < (1 − r) ε/2` beyond
`M`; then `|x (M+k)| ≤ r^k |x M| + ε/2` by induction, and `r^k → 0`.) -/
theorem tendsto_zero_of_contraction {x y : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ m, |x (m + 1)| ≤ r * |x m| + |y m|) (hy : Tendsto y atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hy ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := hy ((1 - r) * (ε / 2)) (mul_pos (sub_pos.2 hr1) (half_pos hε))
  have hbound : ∀ k, |x (M + k)| ≤ r ^ k * |x M| + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h1 := hrec (M + k)
      have h2 := hM (M + k) (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      rw [← Nat.add_assoc]
      calc |x (M + k + 1)| ≤ r * |x (M + k)| + |y (M + k)| := h1
        _ ≤ r * (r ^ k * |x M| + ε / 2) + (1 - r) * (ε / 2) :=
            add_le_add (mul_le_mul_of_nonneg_left ih hr0) h2.le
        _ = r ^ (k + 1) * |x M| + ε / 2 := by ring
  have hpow : Tendsto (fun k : ℕ => r ^ k * |x M|) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const |x M|
    simpa only [zero_mul] using this
  rw [Metric.tendsto_atTop] at hpow
  obtain ⟨K, hK⟩ := hpow (ε / 2) (half_pos hε)
  refine ⟨M + K, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hb := hbound (n - M)
  have hk := hK (n - M) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (abs_nonneg _))] at hk
  have e : M + (n - M) = n := by omega
  rw [e] at hb
  linarith

/-- **The decay conjecture is a 3-adic equidistribution statement.**  `b_j → 0` iff the signed
mass of the residue class `leakClass m` of the start mod 3 is asymptotically one third of the
total, at the scale of the level: `BiasDecays` is exactly the equidistribution of the first
beyond-Terras parity across the three classes of the start mod 3.

Proof: `bias_div_succ` reads `x (m+1) = (2/3) x m − y m` for `x m = bias m / 2^m` and
`y m = (biasClass m (leakClass m) − bias m / 3) / 2^m`.  If `x → 0` then `y m = (2/3) x m − x (m+1)
→ 0`; if `y → 0` then `|x (m+1)| ≤ (2/3) |x m| + |y m|` is a contraction with vanishing forcing
(`tendsto_zero_of_contraction`), so `x → 0`.

**The AR(1) reading.**  In normalised units `b̃_m = bias m / 2^(m/2)` the recursion is
`b̃_{m+1} = (4/3)/√2 · b̃_m + η_{m+1}` with `(4/3)/√2 = 0.943`, so the sign has a memory of about
17 levels for every map in the family.  Numerics (2026-10-21): the innovations `η` over
`j = 10..31` have mean `+0.14` and sd `0.33`; under the zero-mean null, the `22` consecutive
positive values of `bias` have probability `0.40`, so `BiasPositive` is not yet evidence of a
mechanism. -/
theorem biasDecays_iff_classFluct :
    BiasDecays ↔
      Tendsto (fun m => ((biasClass m (leakClass m) : ℝ) - (bias m : ℝ) / 3) / 2 ^ m) atTop
        (𝓝 0) := by
  unfold BiasDecays
  constructor
  · intro hx
    have h1 : Tendsto (fun m => 2 / 3 * ((bias m : ℝ) / 2 ^ m) - (bias (m + 1) : ℝ) / 2 ^ (m + 1))
        atTop (𝓝 0) := by
      have := (hx.const_mul (2 / 3)).sub ((tendsto_add_atTop_iff_nat 1).2 hx)
      simpa only [mul_zero, sub_zero] using this
    exact h1.congr fun m => by rw [bias_div_succ]; ring
  · intro hy
    refine tendsto_zero_of_contraction (r := 2 / 3) (by norm_num) (by norm_num) (fun m => ?_) hy
    show |(bias (m + 1) : ℝ) / 2 ^ (m + 1)| ≤ _
    rw [bias_div_succ]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]

end CollatzMoonshot.Conjugacy
