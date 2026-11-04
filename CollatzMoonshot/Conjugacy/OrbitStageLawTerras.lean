/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitStageLawPull

/-!
# The stage word law: exponential moments over blocks

Terras in product form (`sum_mul_shift`): if `G` sees only `r mod 2^s` and `h` only `x mod 2^L`, then

    ∑_(r < 2^(s+L)) G(r) h(T^s r) = (∑_(r < 2^s) G r) (∑_(x < 2^L) h x),

because `T^s (r + 2^s c) = T^s r + 3^a c` and `c ↦ b + 3^a c` permutes the residues mod `2^L`.  Iterated
over `q` blocks it gives the exponential moment of `blkCnt` (`sum_pow_blkCnt`), and Chernoff
(`card_ge_le_of_mgf`) gives the tails `SufTail` and `OddTail`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Terras in product form -/

theorem sum_range_mul_eq (f : ℕ → ℝ) (a : ℕ) : ∀ m, ∑ r ∈ Finset.range (a * m), f r =
    ∑ c ∈ Finset.range m, ∑ r ∈ Finset.range a, f (r + a * c)
  | 0 => by simp
  | m + 1 => by
    rw [mul_add, mul_one, Finset.sum_range_add, sum_range_mul_eq f a m, Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by rw [add_comm]

/-- `c ↦ b + 3^a c` permutes the residues mod `2^L`. -/
theorem sum_affine_mod (h : ℕ → ℝ) {L : ℕ} (hh : ∀ x, h x = h (x % 2 ^ L)) (b a : ℕ) :
    ∑ c ∈ Finset.range (2 ^ L), h (b + c * 3 ^ a) = ∑ x ∈ Finset.range (2 ^ L), h x := by
  set g : ℕ → ℕ := fun c => (b + c * 3 ^ a) % 2 ^ L
  have hinj : Set.InjOn g (Finset.range (2 ^ L)) := by
    intro c hc c' hc' he
    have hc1 := Finset.mem_range.mp hc
    have hc2 := Finset.mem_range.mp hc'
    have h1 : b + c * 3 ^ a ≡ b + c' * 3 ^ a [MOD 2 ^ L] := he
    have h2 : c * 3 ^ a ≡ c' * 3 ^ a [MOD 2 ^ L] := Nat.ModEq.add_left_cancel' b h1
    have hcop : Nat.gcd (2 ^ L) (3 ^ a) = 1 :=
      Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)
    have h3 := Nat.ModEq.cancel_right_of_coprime hcop h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at h3
  have himg : (Finset.range (2 ^ L)).image g = Finset.range (2 ^ L) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ c ∈ Finset.range (2 ^ L), h (b + c * 3 ^ a) = ∑ c ∈ Finset.range (2 ^ L), h (g c) :=
        Finset.sum_congr rfl fun c _ => hh _
    _ = ∑ x ∈ (Finset.range (2 ^ L)).image g, h x := (Finset.sum_image hinj).symm
    _ = ∑ x ∈ Finset.range (2 ^ L), h x := by rw [himg]

/-- **Terras in product form.** -/
theorem sum_mul_shift {s L : ℕ} (G h : ℕ → ℝ) (hG : ∀ r, G r = G (r % 2 ^ s))
    (hh : ∀ x, h x = h (x % 2 ^ L)) :
    ∑ r ∈ Finset.range (2 ^ (s + L)), G r * h (tstep^[s] r) =
      (∑ r ∈ Finset.range (2 ^ s), G r) * ∑ x ∈ Finset.range (2 ^ L), h x := by
  rw [pow_add, sum_range_mul_eq, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  have hGc : ∀ c, G (r + 2 ^ s * c) = G r := fun c => by
    rw [hG, hG r, mul_comm, Nat.add_mul_mod_self_right]
  have hT : ∀ c, tstep^[s] (r + 2 ^ s * c) = tstep^[s] r + c * 3 ^ oddCount r s := fun c => by
    rw [mul_comm]; exact tstep_iterate_add_mul_two_pow s r c
  simp only [hGc, hT]
  rw [← Finset.mul_sum, sum_affine_mod h hh]

/-- A function of `x mod 2^m` is a function of `r mod 2^(m + n)` after `T^i`, when `i + m ≤ N`. -/
theorem iterate_mod_eq {i m N : ℕ} (h : i + m ≤ N) (r : ℕ) :
    tstep^[i] (r % 2 ^ N) % 2 ^ m = tstep^[i] r % 2 ^ m := by
  conv_rhs => rw [← Nat.mod_add_div r (2 ^ N)]
  rw [show r % 2 ^ N + 2 ^ N * (r / 2 ^ N) = r % 2 ^ N + (r / 2 ^ N * 2 ^ (N - i)) * 2 ^ i by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]; ring]
  rw [tstep_iterate_add_mul_two_pow]
  rw [show r / 2 ^ N * 2 ^ (N - i) * 3 ^ oddCount (r % 2 ^ N) i =
    (r / 2 ^ N * 2 ^ (N - i - m) * 3 ^ oddCount (r % 2 ^ N) i) * 2 ^ m by
    have e : 2 ^ (N - i) = 2 ^ (N - i - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
    rw [e]; ring]
  rw [Nat.add_mul_mod_self_right]

/-! ## Exponential moments -/

theorem blkCnt_zero (P : ℕ → Prop) [DecidablePred P] (L o r : ℕ) : blkCnt P L o 0 r = 0 := by
  simp [blkCnt]

theorem blkCnt_succ (P : ℕ → Prop) [DecidablePred P] (L o q r : ℕ) :
    blkCnt P L o (q + 1) r = blkCnt P L o q r + if P (tstep^[o + q * L] r) then 1 else 0 := by
  unfold blkCnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hP
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- `blkCnt` over `q` blocks sees only `r mod 2^(o + q L)`. -/
theorem blkCnt_mod (P : ℕ → Prop) [DecidablePred P] {L : ℕ} (hP : ∀ x, P x ↔ P (x % 2 ^ L))
    (o q r : ℕ) : blkCnt P L o q (r % 2 ^ (o + q * L)) = blkCnt P L o q r := by
  unfold blkCnt
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hP, hP (tstep^[o + j * L] r), iterate_mod_eq]
  nlinarith

/-- The weight of one block. -/
noncomputable def blkW (P : ℕ → Prop) [DecidablePred P] (lam : ℝ) (x : ℕ) : ℝ :=
  if P x then lam else 1

/-- **The exponential moment of `blkCnt`.** -/
theorem sum_pow_blkCnt (P : ℕ → Prop) [DecidablePred P] {L : ℕ} (hP : ∀ x, P x ↔ P (x % 2 ^ L))
    (lam : ℝ) (o : ℕ) : ∀ q : ℕ, ∑ r ∈ Finset.range (2 ^ (o + q * L)), lam ^ blkCnt P L o q r =
      2 ^ o * (∑ x ∈ Finset.range (2 ^ L), blkW P lam x) ^ q
  | 0 => by simp [blkCnt_zero]
  | q + 1 => by
    have hG : ∀ r, lam ^ blkCnt P L o q r = lam ^ blkCnt P L o q (r % 2 ^ (o + q * L)) :=
      fun r => by rw [blkCnt_mod P hP]
    have hh : ∀ x, blkW P lam x = blkW P lam (x % 2 ^ L) := fun x => by
      unfold blkW; rw [if_congr (hP x) rfl rfl]
    have e : ∀ r, lam ^ blkCnt P L o (q + 1) r =
        lam ^ blkCnt P L o q r * blkW P lam (tstep^[o + q * L] r) := fun r => by
      rw [blkCnt_succ, pow_add]; unfold blkW; split_ifs <;> simp
    rw [show o + (q + 1) * L = (o + q * L) + L by ring]
    simp only [e]
    rw [sum_mul_shift _ _ hG hh, sum_pow_blkCnt P hP lam o q, pow_succ]
    ring

/-- The weight of one block, summed: `(2^L − c) + c λ`, `c` the number of residues in `P`. -/
theorem sum_blkW (P : ℕ → Prop) [DecidablePred P] (lam : ℝ) (L : ℕ) :
    ∑ x ∈ Finset.range (2 ^ L), blkW P lam x =
      (2 ^ L : ℝ) + (((Finset.range (2 ^ L)).filter P).card : ℝ) * (lam - 1) := by
  unfold blkW
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ L)) P
  rw [Finset.card_range] at this
  have h' : ((((Finset.range (2 ^ L)).filter P).card + ((Finset.range (2 ^ L)).filter
      fun a => ¬ P a).card : ℕ) : ℝ) = (2 ^ L : ℕ) := by rw [this]
  push_cast at h'
  linarith

/-- Over `r < 2^s`, `s ≥ o + q L`. -/
theorem sum_pow_blkCnt_le (P : ℕ → Prop) [DecidablePred P] {L : ℕ} (hP : ∀ x, P x ↔ P (x % 2 ^ L))
    {lam : ℝ} (o q s : ℕ) (hs : o + q * L ≤ s) :
    ∑ r ∈ Finset.range (2 ^ s), lam ^ blkCnt P L o q r =
      2 ^ s * (1 + (((Finset.range (2 ^ L)).filter P).card : ℝ) / 2 ^ L * (lam - 1)) ^ q := by
  have hG : ∀ r, lam ^ blkCnt P L o q r = lam ^ blkCnt P L o q (r % 2 ^ (o + q * L)) :=
    fun r => by rw [blkCnt_mod P hP]
  have h1 := sum_mul_shift (s := o + q * L) (L := s - (o + q * L)) (fun r => lam ^ blkCnt P L o q r)
    (fun _ => 1) hG (fun _ => rfl)
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  rw [Nat.add_sub_cancel' hs] at h1
  rw [h1, sum_pow_blkCnt P hP lam o q, sum_blkW]
  have hL : (2 : ℝ) ^ L ≠ 0 := by positivity
  set c : ℝ := (((Finset.range (2 ^ L)).filter P).card : ℝ)
  rw [show (2 : ℝ) ^ L + c * (lam - 1) = 2 ^ L * (1 + c / 2 ^ L * (lam - 1)) by
    field_simp]
  rw [mul_pow, ← pow_mul]
  have : (2 : ℝ) ^ s = 2 ^ (s - (o + q * L)) * (2 ^ o * 2 ^ (L * q)) := by
    rw [← pow_add, ← pow_add, mul_comm L q]; congr 1; omega
  rw [this]; push_cast; ring

/-! ## Chernoff -/

/-- **Chernoff, upper tail.**  From the exponential moment at `λ = 1 + η`. -/
theorem card_ge_le_of_mgf (S : Finset ℕ) (Y : ℕ → ℕ) {N₀ p η : ℝ} (q : ℕ) (hp : 0 ≤ p)
    (hη : 0 < η) (hM : ∑ r ∈ S, (1 + η) ^ Y r ≤ N₀ * (1 + p * η) ^ q) :
    ((S.filter fun r => (p + η) * q ≤ Y r).card : ℝ) ≤
      N₀ * Real.exp (-(q * η ^ 2 * (1 - p) / (1 + η))) := by
  set E := S.filter fun r => (p + η) * q ≤ Y r
  set l := Real.log (1 + η)
  have h1η : 0 < 1 + η := by linarith
  have hl : η / (1 + η) ≤ l := by
    have := Real.one_sub_inv_le_log_of_pos h1η
    rw [show 1 - (1 + η)⁻¹ = η / (1 + η) by field_simp; ring] at this
    exact this
  have hpow : ∀ r, (1 + η) ^ Y r = Real.exp (Y r * l) := fun r => by
    rw [Real.exp_nat_mul, Real.exp_log h1η]
  have hE : (E.card : ℝ) * Real.exp ((p + η) * q * l) ≤ ∑ r ∈ S, (1 + η) ^ Y r := by
    calc (E.card : ℝ) * Real.exp ((p + η) * q * l) = ∑ _r ∈ E, Real.exp ((p + η) * q * l) := by
          simp
      _ ≤ ∑ r ∈ E, (1 + η) ^ Y r := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [hpow]
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hr).2 ?_)
          exact le_trans (by positivity) hl
      _ ≤ ∑ r ∈ S, (1 + η) ^ Y r :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun r _ _ => by positivity
  have hq : (1 + p * η) ^ q ≤ Real.exp (q * (p * η)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (p * η)]) q
  have hN₀ : 0 ≤ N₀ := by
    by_contra hneg
    push Not at hneg
    have : 0 ≤ ∑ r ∈ S, (1 + η) ^ Y r := Finset.sum_nonneg fun r _ => by positivity
    have : 0 < (1 + p * η) ^ q := by positivity
    nlinarith
  have hexp : Real.exp ((p + η) * q * l) > 0 := Real.exp_pos _
  have key : (E.card : ℝ) ≤ N₀ * Real.exp (q * (p * η)) / Real.exp ((p + η) * q * l) := by
    rw [le_div_iff₀ hexp]
    exact le_trans hE (le_trans hM (mul_le_mul_of_nonneg_left hq hN₀))
  refine le_trans key ?_
  rw [mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN₀
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have : (p + η) * (η / (1 + η)) ≤ (p + η) * l := mul_le_mul_of_nonneg_left hl (by linarith)
  have e : q * (p * η) - (p + η) * q * (η / (1 + η)) = -(q * η ^ 2 * (1 - p) / (1 + η)) := by
    field_simp; ring
  nlinarith

/-! ## The two tails -/

theorem blkCnt_add_not (P : ℕ → Prop) [DecidablePred P] (L o q r : ℕ) :
    blkCnt P L o q r + blkCnt (fun x => ¬ P x) L o q r = q := by
  unfold blkCnt
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

/-- The odd letters at positions `o, …, o + q − 1` are a `blkCnt`. -/
theorem oddCount_add_eq (r o : ℕ) : ∀ q : ℕ,
    oddCount r (o + q) = oddCount r o + blkCnt (fun x => x % 2 = 1) 1 o q r
  | 0 => by simp [blkCnt_zero]
  | q + 1 => by
    rw [← add_assoc, oddCount_succ', oddCount_add_eq r o q, blkCnt_succ, mul_one]
    ring

theorem odd_periodic : ∀ x : ℕ, x % 2 = 1 ↔ x % 2 ^ 1 % 2 = 1 := fun x => by
  rw [pow_one, Nat.mod_mod]

theorem not_odd_periodic : ∀ x : ℕ, ¬ x % 2 = 1 ↔ ¬ x % 2 ^ 1 % 2 = 1 := fun x => by
  rw [pow_one, Nat.mod_mod]

/-- The exponential moment of the odd (or even) letters of a window. -/
theorem sum_pow_odd_le (P : ℕ → Prop) [DecidablePred P] (hP : ∀ x, P x ↔ P (x % 2 ^ 1))
    (hc : ((Finset.range (2 ^ 1)).filter P).card = 1) {η : ℝ} (o q k : ℕ) (hs : o + q ≤ k) :
    ∑ r ∈ Finset.range (2 ^ k), (1 + η) ^ blkCnt P 1 o q r ≤ 2 ^ k * (1 + 1 / 2 * η) ^ q := by
  rw [sum_pow_blkCnt_le P hP o q k (by simpa using hs), hc]
  norm_num

open Classical in
/-- **`SufTail`**, with `τ = exp(−1/220)`. -/
theorem sufTail_holds' : SufTail := by
  refine ⟨Real.exp (-(1 / 220)), Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num), fun k ℓ₀ => ?_⟩
  set P : ℕ → Prop := fun x => x % 2 = 1
  set Ev : ℕ → Finset ℕ := fun i => (Finset.range (2 ^ k)).filter fun r =>
    (1 / 2 + 1 / 10 : ℝ) * ((k - i : ℕ) : ℝ) ≤ blkCnt P 1 i (k - i) r
  have hsub : (Finset.range (2 ^ k)).filter (fun r => ¬ SufGood ℓ₀ k r) ⊆
      ((Finset.range (k + 1)).filter fun i => i + ℓ₀ ≤ k).biUnion Ev := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    unfold SufGood at hr2
    push Not at hr2
    obtain ⟨i, hi, hbad⟩ := hr2
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩,
      Finset.mem_filter.mpr ⟨hr1, ?_⟩⟩
    have he : oddCount r (i + (k - i)) = oddCount r i + blkCnt P 1 i (k - i) r :=
      oddCount_add_eq r i (k - i)
    rw [show i + (k - i) = k by omega] at he
    have h5 : 3 * (k - i) ≤ 5 * blkCnt P 1 i (k - i) r := by
      have : oddCount r k - oddCount r i = blkCnt P 1 i (k - i) r := by omega
      omega
    have h5' : (3 : ℝ) * ((k - i : ℕ) : ℝ) ≤ 5 * (blkCnt P 1 i (k - i) r : ℝ) := by exact_mod_cast h5
    linarith
  have hEv : ∀ i ∈ (Finset.range (k + 1)).filter (fun i => i + ℓ₀ ≤ k),
      ((Ev i).card : ℝ) ≤ 2 ^ k * Real.exp (-(1 / 220)) ^ ℓ₀ := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hM := sum_pow_odd_le P odd_periodic (by decide) (η := 1 / 10) i (k - i) k (by omega)
    have h := card_ge_le_of_mgf (Finset.range (2 ^ k)) (fun r => blkCnt P 1 i (k - i) r)
      (k - i) (by norm_num) (by norm_num) hM
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : (ℓ₀ : ℝ) ≤ ((k - i : ℕ) : ℝ) := by exact_mod_cast (by omega : ℓ₀ ≤ k - i)
    have e : (((k - i : ℕ) : ℝ) * (1 / 10) ^ 2 * (1 - 1 / 2) / (1 + 1 / 10) : ℝ) =
      ((k - i : ℕ) : ℝ) / 220 := by ring
    rw [e]
    linarith
  calc (((Finset.range (2 ^ k)).filter (fun r => ¬ SufGood ℓ₀ k r)).card : ℝ)
      ≤ ((((Finset.range (k + 1)).filter fun i => i + ℓ₀ ≤ k).biUnion Ev).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ (Finset.range (k + 1)).filter (fun i => i + ℓ₀ ≤ k), ((Ev i).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ (Finset.range (k + 1)).filter (fun i => i + ℓ₀ ≤ k),
          2 ^ k * Real.exp (-(1 / 220)) ^ ℓ₀ := Finset.sum_le_sum hEv
    _ ≤ (k + 1) * 2 ^ k * Real.exp (-(1 / 220)) ^ ℓ₀ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : ((Finset.range (k + 1)).filter fun i => i + ℓ₀ ≤ k).card ≤ k + 1 :=
          le_trans (Finset.card_filter_le _ _) (by simp)
        exact_mod_cast this

open Classical in
/-- **`OddTail`**, with `τ = exp(−γ²/(2(1 + γ)))`. -/
theorem oddTail_holds' : OddTail := by
  intro γ hγ
  set c := γ ^ 2 * (1 - 1 / 2) / (1 + γ)
  have hc : 0 < c := by positivity
  refine ⟨Real.exp (-c), (Real.exp_pos _).le, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), fun k => ?_⟩
  set P : ℕ → Prop := fun x => ¬ x % 2 = 1
  have hsub : (Finset.range (2 ^ k)).filter (fun r => ¬ OddLow γ k r) ⊆
      (Finset.range (2 ^ k)).filter fun r => (1 / 2 + γ) * (k : ℝ) ≤ blkCnt P 1 0 k r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨hr1, ?_⟩
    unfold OddLow at hr2
    push Not at hr2
    have he := oddCount_add_eq r 0 k
    rw [zero_add, oddCount_zero, zero_add] at he
    have hsum : blkCnt (fun x => x % 2 = 1) 1 0 k r + blkCnt P 1 0 k r = k :=
      blkCnt_add_not (fun x => x % 2 = 1) 1 0 k r
    have : ((blkCnt (fun x => x % 2 = 1) 1 0 k r : ℕ) : ℝ) + (blkCnt P 1 0 k r : ℝ) = k := by
      exact_mod_cast hsum
    rw [← he] at this
    linarith
  have hM := sum_pow_odd_le P not_odd_periodic (by decide) (η := γ) 0 k k (by omega)
  have h := card_ge_le_of_mgf (Finset.range (2 ^ k)) (fun r => blkCnt P 1 0 k r) k
    (by norm_num) hγ hM
  calc (((Finset.range (2 ^ k)).filter (fun r => ¬ OddLow γ k r)).card : ℝ)
      ≤ (((Finset.range (2 ^ k)).filter fun r =>
          (1 / 2 + γ) * (k : ℝ) ≤ blkCnt P 1 0 k r).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 ^ k * Real.exp (-(k * γ ^ 2 * (1 - 1 / 2) / (1 + γ))) := h
    _ = 2 ^ k * Real.exp (-c) ^ k := by
        rw [← Real.exp_nat_mul]; congr 2; simp only [c]; ring

end CollatzMoonshot.Conjugacy
