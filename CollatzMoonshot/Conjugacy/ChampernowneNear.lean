/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneOne

/-!
# Short-interval mixing at bounded offsets

`ShortIntervalMixing C` asks for all offsets `t ∈ [k, C k)` and every initial segment of stage `k`.
This file separates two things that hypothesis mixes together.

* **Segments are not the obstruction.**  Starting from a block `[α 2^b, (α + 1) 2^b)` only shifts
  the iterate: `T^b (r + α 2^b) = T^b r + α 3^s`, `s` the odd count of `r`
  (`tstep_iterate_add_mul_two_pow`).  So `BlockWordsUniform`, uniformity of `T^b n mod 2^K` over
  each fixed block, gives every segment, at offsets within a fixed distance of `k`
  (`shortIntervalMixingNear_of_blockWordsUniform`).
* **Distance from `k` is.**  Over `n < 2^k`, the letters at `t ≥ k` are determined by the `k` bits
  of `n`, so a slice law over `r < 2^t` sees those `n` only as a `2^(k−t)` fraction of its mass.
  By that count, a character bound of size `j^(−A)` reaches about `t − k = O(log k)`
  (`ShortIntervalMixingLog`), which is a heuristic and not a proved limit.  `ShortIntervalMixing C` for `C ≥ 2` needs `t − k ≍ k`, so nothing here
  bears on normality of `𝒞_C` for `C ≥ 2`: the bounded offsets are `O(1 / k)` of each word.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The starts in block `α` (`n = r + α 2^b`, `r < 2^b`) whose `b`-th iterate is `c mod 2^K`. -/
def blockCount (b α K c : ℕ) : ℕ :=
  ((Finset.range (2 ^ b)).filter fun r => tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c).card

/-- **Node.**  Over each fixed block, `T^b n mod 2^K` is uniform as `b → ∞`.  At `α = 0` this is
`BeyondWordsUniform`.  Confidence 90%: on each central slice `a` the shift `α 3^a` is a constant, and
the slice-wise bound behind `BeyondWordsUniform` is uniform in the residue.

Evidence (`experiments/conjugacy/segment_reach.py`, exhaustive, `L = 1`, supremum over `m`): at
`t = k + 1, k + 2, k + 4` the error falls from `0.0112, 0.0078, 0.0122` at `k = 14` to `0.0004, 0.0003,
0.0006` at `k = 24`, against `0.0001` for a random walk of the same length. -/
def BlockWordsUniform : Prop :=
  ∀ α K c : ℕ, c < 2 ^ K →
    Tendsto (fun b : ℕ => (blockCount b α K c : ℝ) / 2 ^ b) atTop (𝓝 (1 / 2 ^ K))

/-- `ShortIntervalMixing`, restricted to offsets within `g` of the bit length. -/
def ShortIntervalMixingNear (g : ℕ) : Prop :=
  ∀ (L : ℕ) (p : Fin L → Bool) (δ : ℝ), 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ,
    m ≤ 2 ^ (k - 1) → ∀ t : ℕ, k ≤ t → t + L ≤ k + g →
      |(((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
          fun n => ∀ s : Fin L, accWord n (t + s) = p s).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
        δ * 2 ^ (k - 1)

/-- **Node.**  `ShortIntervalMixing`, restricted to offsets within `A log₂ k` of the bit length, for
every `A`.  This is the reach of a character bound `j^(−A)` for every `A`.  Confidence 75%. -/
def ShortIntervalMixingLog : Prop :=
  ∀ (A L : ℕ) (p : Fin L → Bool) (δ : ℝ), 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ,
    m ≤ 2 ^ (k - 1) → ∀ t : ℕ, k ≤ t → t + L ≤ k + A * Nat.size k →
      |(((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
          fun n => ∀ s : Fin L, accWord n (t + s) = p s).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
        δ * 2 ^ (k - 1)

/-- Letter `b + e` of `n` is letter `e` of `T^b n`. -/
theorem accWord_add_eq (n b e : ℕ) : accWord n (b + e) = accWord (tstep^[b] n) e := by
  simp only [accWord]
  rw [add_comm, Function.iterate_add_apply]

/-- The window at `b + e` of `n` is the window at `e` of `T^b n`. -/
private theorem windowMatch_add_iff (g : ℕ → Bool) (L b e n : ℕ) :
    WindowMatch g L (b + e) n ↔ WindowMatch g L e (tstep^[b] n) := by
  unfold WindowMatch
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  rw [add_assoc, accWord_add_eq]

/-- The window at `b + e` over a block, counted through the residues of `T^b n mod 2^(e+L)`:
exactly `2^e` residues match (`card_windowMatch`). -/
theorem card_block_window_eq (g : ℕ → Bool) (L b e α : ℕ) :
    (((Finset.range (2 ^ b)).filter fun r => WindowMatch g L (b + e) (r + α * 2 ^ b)).card) =
      ∑ c ∈ (Finset.range (2 ^ (e + L))).filter (WindowMatch g L e), blockCount b α (e + L) c := by
  have hmod : ∀ y, WindowMatch g L e (y % 2 ^ (e + L)) ↔ WindowMatch g L e y := fun y =>
    iff_of_eq ((windowMatch_periodic g L e).map_mod_nat y)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun r => tstep^[b] (r + α * 2 ^ b) % 2 ^ (e + L))
    (t := (Finset.range (2 ^ (e + L))).filter (WindowMatch g L e))]
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hcW := (Finset.mem_filter.mp hc).2
    unfold blockCount
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hr, _⟩, hrc⟩
      exact ⟨hr, hrc⟩
    · rintro ⟨hr, hrc⟩
      refine ⟨⟨hr, ?_⟩, hrc⟩
      rw [windowMatch_add_iff, ← hmod, hrc]
      exact hcW
  · intro r hr
    have hrW := (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mod_lt _ (by positivity)), ?_⟩)
    rw [hmod]
    exact (windowMatch_add_iff g L b e _).mp hrW

/-- **One block.**  Uniform in the finitely many `e ≤ E`, `α < A`: over a block the window count is
`2^b / 2^L` up to `η 2^b`. -/
theorem eventually_abs_block_window_le (h : BlockWordsUniform) (g : ℕ → Bool) (L E A : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ b in atTop, ∀ e ≤ E, ∀ α < A,
      |(((Finset.range (2 ^ b)).filter fun r => WindowMatch g L (b + e) (r + α * 2 ^ b)).card : ℝ) -
          (2 : ℝ) ^ b / 2 ^ L| ≤ η * 2 ^ b := by
  have hε : 0 < η / 2 ^ E := by positivity
  have hall : ∀ᶠ b : ℕ in atTop, ∀ e ∈ Finset.range (E + 1), ∀ α ∈ Finset.range A,
      ∀ c ∈ Finset.range (2 ^ (e + L)),
        |(blockCount b α (e + L) c : ℝ) / 2 ^ b - 1 / 2 ^ (e + L)| < η / 2 ^ E := by
    rw [Filter.eventually_all_finset]
    intro e _
    rw [Filter.eventually_all_finset]
    intro α _
    rw [Filter.eventually_all_finset]
    intro c hc
    have := (Metric.tendsto_nhds.mp (h α (e + L) c (Finset.mem_range.mp hc))) _ hε
    simpa only [Real.dist_eq] using this
  filter_upwards [hall] with b hb e he α hα
  have hb' := hb e (Finset.mem_range.mpr (by omega)) α (Finset.mem_range.mpr hα)
  rw [card_block_window_eq]
  set R := (Finset.range (2 ^ (e + L))).filter (WindowMatch g L e) with hR
  have hRcard : R.card = 2 ^ e := card_windowMatch g L e
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hmain : (2 : ℝ) ^ b / 2 ^ L = ∑ _c ∈ R, (2 : ℝ) ^ b / 2 ^ (e + L) := by
    rw [Finset.sum_const, hRcard, nsmul_eq_mul, pow_add]
    push_cast
    field_simp
  rw [hmain]
  push_cast
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ c ∈ R, |(blockCount b α (e + L) c : ℝ) - (2 : ℝ) ^ b / 2 ^ (e + L)| ≤
      η / 2 ^ E * 2 ^ b := by
    intro c hc
    have hc' := hb' c (Finset.mem_filter.mp hc).1
    have heq : (blockCount b α (e + L) c : ℝ) - (2 : ℝ) ^ b / 2 ^ (e + L) =
        ((blockCount b α (e + L) c : ℝ) / 2 ^ b - 1 / 2 ^ (e + L)) * 2 ^ b := by
      field_simp
    rw [heq, abs_mul, abs_of_pos h2b]
    exact mul_le_mul_of_nonneg_right hc'.le h2b.le
  calc |∑ c ∈ R, ((blockCount b α (e + L) c : ℝ) - (2 : ℝ) ^ b / 2 ^ (e + L))|
      ≤ ∑ c ∈ R, |(blockCount b α (e + L) c : ℝ) - (2 : ℝ) ^ b / 2 ^ (e + L)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ R, η / 2 ^ E * 2 ^ b := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ e * (η / 2 ^ E * 2 ^ b) := by
        rw [Finset.sum_const, hRcard, nsmul_eq_mul]; push_cast; rfl
    _ ≤ η * 2 ^ b := by
        have h2e : (2 : ℝ) ^ e ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) he
        have h2E : (0 : ℝ) < 2 ^ E := by positivity
        have : (2 : ℝ) ^ e * (η / 2 ^ E * 2 ^ b) = (2 : ℝ) ^ e / 2 ^ E * (η * 2 ^ b) := by ring
        rw [this]
        have hle : (2 : ℝ) ^ e / 2 ^ E ≤ 1 := (div_le_one h2E).mpr h2e
        have hnn : 0 ≤ η * (2 : ℝ) ^ b := by positivity
        nlinarith

/-- Interval counts add (the public restatement of a private lemma of `ChampernowneOne`). -/
private theorem card_filter_Ico_add' (P : ℕ → Prop) [DecidablePred P] (a b c : ℕ) :
    ((Finset.Ico a (a + b + c)).filter P).card =
      ((Finset.Ico a (a + b)).filter P).card + ((Finset.Ico (a + b) (a + b + c)).filter P).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a b) (Nat.le_add_right (a + b) c),
    Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- A filter over `[A, A + N)` is the shifted filter over `range N`. -/
private theorem card_filter_Ico_eq_range (P : ℕ → Prop) [DecidablePred P] (A N : ℕ) :
    ((Finset.Ico A (A + N)).filter P).card = ((Finset.range N).filter fun r => P (r + A)).card := by
  refine Finset.card_nbij' (fun n => n - A) (fun r => r + A) ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    have hI := Finset.mem_Ico.mp hn'.1
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by show n - A < N; omega), ?_⟩)
    show P (n - A + A)
    rw [Nat.sub_add_cancel hI.1]
    exact hn'.2
  · intro r hr
    have hr' := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
    have hI := Finset.mem_range.mp hr'.1
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (by show A ≤ r + A ∧ r + A < A + N; omega), hr'.2⟩)
  · intro n hn
    have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    have hI := Finset.mem_Ico.mp hn'.1
    exact Nat.sub_add_cancel hI.1
  · intro r _
    show r + A - A = r
    omega

/-- `q` consecutive blocks, each within `ε` of `B`, are within `q ε` of `q B`. -/
private theorem abs_blocks_le (P : ℕ → Prop) [DecidablePred P] (N a : ℕ) (B ε : ℝ) (q : ℕ)
    (hblock : ∀ i < q,
      |(((Finset.range N).filter fun r => P (r + (a + i) * N)).card : ℝ) - B| ≤ ε) :
    |(((Finset.Ico (a * N) (a * N + q * N)).filter P).card : ℝ) - q * B| ≤ q * ε := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit := card_filter_Ico_add' P (a * N) (q * N) N
    have hlast := card_filter_Ico_eq_range P (a * N + q * N) N
    have hA : a * N + q * N = (a + q) * N := by ring
    rw [hA] at hlast
    rw [← hA] at hlast
    have hb := hblock q (Nat.lt_succ_self q)
    have hb' : |(((Finset.Ico (a * N + q * N) (a * N + q * N + N)).filter P).card : ℝ) - B| ≤ ε := by
      rw [hlast]
      simpa only [hA] using hb
    have hih := ih fun i hi => hblock i (Nat.lt_succ_of_lt hi)
    have heq : a * N + (q + 1) * N = a * N + q * N + N := by ring
    rw [heq, hsplit]
    push_cast
    rw [abs_le] at hb' hih ⊢
    constructor <;> nlinarith [hb'.1, hb'.2, hih.1, hih.2]

/-- **A segment is blocks plus a remainder.**  Cutting `[α₀ 2^b, α₀ 2^b + m)` into `q = m / 2^b`
blocks: if each block is within `η 2^b`, the window count is within `(q η + 2) 2^b` of `m / 2^L`. -/
theorem abs_segment_window_le (g : ℕ → Bool) (L t b α₀ m : ℕ) (η : ℝ)
    (hblock : ∀ i < m / 2 ^ b,
      |(((Finset.range (2 ^ b)).filter
          fun r => WindowMatch g L t (r + (α₀ + i) * 2 ^ b)).card : ℝ) - (2 : ℝ) ^ b / 2 ^ L| ≤
        η * 2 ^ b) :
    |(((Finset.Ico (α₀ * 2 ^ b) (α₀ * 2 ^ b + m)).filter (WindowMatch g L t)).card : ℝ) -
        (m : ℝ) / 2 ^ L| ≤ (((m / 2 ^ b : ℕ) : ℝ) * η + 2) * 2 ^ b := by
  have hNpos : 0 < 2 ^ b := by positivity
  have hdec : (m / 2 ^ b) * 2 ^ b + m % 2 ^ b = m := Nat.div_add_mod' m (2 ^ b)
  have hs : m % 2 ^ b < 2 ^ b := Nat.mod_lt _ hNpos
  set q := m / 2 ^ b with hq
  set s := m % 2 ^ b with hsdef
  have hb := abs_blocks_le (WindowMatch g L t) (2 ^ b) α₀ ((2 : ℝ) ^ b / 2 ^ L) (η * 2 ^ b) q
    (by simpa using hblock)
  have hsplit := card_filter_Ico_add' (WindowMatch g L t) (α₀ * 2 ^ b) (q * 2 ^ b) s
  have hm : α₀ * 2 ^ b + q * 2 ^ b + s = α₀ * 2 ^ b + m := by omega
  rw [hm] at hsplit
  rw [hsplit]
  have hrem : ((Finset.Ico (α₀ * 2 ^ b + q * 2 ^ b) (α₀ * 2 ^ b + m)).filter
      (WindowMatch g L t)).card ≤ s := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Ico]
    omega
  set u := ((Finset.Ico (α₀ * 2 ^ b + q * 2 ^ b) (α₀ * 2 ^ b + m)).filter
      (WindowMatch g L t)).card
  have huR : (u : ℝ) ≤ s := by exact_mod_cast hrem
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hsR : (s : ℝ) ≤ 2 ^ b := by exact_mod_cast hs.le
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hmR : (m : ℝ) = q * 2 ^ b + s := by exact_mod_cast hdec.symm
  have hL1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  have hsL0 : 0 ≤ (s : ℝ) / 2 ^ L := by positivity
  have hsL : (s : ℝ) / 2 ^ L ≤ s := div_le_self hs0 hL1
  have hdiv : (m : ℝ) / 2 ^ L = q * ((2 : ℝ) ^ b / 2 ^ L) + (s : ℝ) / 2 ^ L := by
    rw [hmR]; ring
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  rw [hdiv]
  push_cast
  rw [abs_le] at hb ⊢
  have hexp : ((q : ℝ) * η + 2) * 2 ^ b = q * (η * 2 ^ b) + 2 * 2 ^ b := by ring
  rw [hexp]
  constructor <;> linarith [hb.1, hb.2]

/-- **Bounded offsets: every segment mixes.**  Take `b = k − h` with `2^(3−h) ≤ δ`, so that a
stage is `2^(h−1)` blocks, and `t = b + e` with `e ≤ h + g`.  One block is `eventually_abs_block_window_le`
with `η = δ / 2^(h+1)`, a segment is `abs_segment_window_le`. -/
theorem shortIntervalMixingNear_of_blockWordsUniform (h : BlockWordsUniform) (g : ℕ) :
    ShortIntervalMixingNear g := by
  intro L p δ hδ
  set G : ℕ → Bool := fun s => if h : s < L then p ⟨s, h⟩ else false with hG
  -- `h₀ + 1` plays the role of `h`, which keeps `h ≥ 1` and `h - 1` out of the arithmetic.
  obtain ⟨h₀, hh₀⟩ := pow_unbounded_of_one_lt (8 / δ) (one_lt_two : (1 : ℝ) < 2)
  have h8 : 8 ≤ δ * 2 ^ (h₀ + 1) := by
    have h1 : (2 : ℝ) ^ h₀ ≤ 2 ^ (h₀ + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    have h2 : 8 < 2 ^ h₀ * δ := (div_lt_iff₀ hδ).mp hh₀
    nlinarith
  set η : ℝ := δ / 2 ^ (h₀ + 2) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (eventually_abs_block_window_le h G L (h₀ + 1 + g) (2 ^ (h₀ + 1)) η hηpos)
  refine ⟨B + h₀ + 1, fun k hk m hm t ht htL => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + (h₀ + 1) := ⟨k - (h₀ + 1), by omega⟩
  have hbB : B ≤ b := by omega
  obtain ⟨e, rfl⟩ : ∃ e, t = b + e := ⟨t - b, by omega⟩
  have he : e ≤ h₀ + 1 + g := by omega
  have hk1 : b + (h₀ + 1) - 1 = b + h₀ := by omega
  rw [hk1] at hm ⊢
  have hstart : (2 : ℕ) ^ (b + h₀) = 2 ^ h₀ * 2 ^ b := by rw [pow_add]; ring
  have hq : m / 2 ^ b ≤ 2 ^ h₀ := by
    apply Nat.div_le_of_le_mul
    rw [hstart] at hm
    linarith [Nat.mul_comm (2 ^ h₀) (2 ^ b)]
  have hf : (Finset.Ico (2 ^ (b + h₀)) (2 ^ (b + h₀) + m)).filter
        (fun n => ∀ s : Fin L, accWord n (b + e + s) = p s) =
      (Finset.Ico (2 ^ h₀ * 2 ^ b) (2 ^ h₀ * 2 ^ b + m)).filter (WindowMatch G L (b + e)) := by
    rw [hstart]
    apply Finset.filter_congr
    intro n _
    simp only [WindowMatch, Fin.forall_iff, hG]
    refine forall_congr' fun s => forall_congr' fun hs => ?_
    simp [hs]
  rw [hf]
  have hseg := abs_segment_window_le G L (b + e) b (2 ^ h₀) m η (fun i hi => by
    refine hB b hbB e he (2 ^ h₀ + i) ?_
    have : i < 2 ^ h₀ := lt_of_lt_of_le hi hq
    rw [pow_succ]; omega)
  refine hseg.trans ?_
  have hqR : ((m / 2 ^ b : ℕ) : ℝ) ≤ 2 ^ h₀ := by exact_mod_cast hq
  have h2h : (0 : ℝ) < 2 ^ h₀ := by positivity
  have hηeq : (2 : ℝ) ^ h₀ * η = δ / 4 := by
    rw [hη, pow_add]; field_simp; norm_num
  have hqη : ((m / 2 ^ b : ℕ) : ℝ) * η ≤ δ / 4 := by
    rw [← hηeq]; exact mul_le_mul_of_nonneg_right hqR hηpos.le
  have hx1 : δ ≤ δ * 2 ^ h₀ := le_mul_of_one_le_right hδ.le (one_le_pow₀ (by norm_num))
  have hx4 : 4 ≤ δ * 2 ^ h₀ := by
    rw [pow_succ] at h8; linarith
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hfin : ((m / 2 ^ b : ℕ) : ℝ) * η + 2 ≤ δ * 2 ^ h₀ := by linarith
  calc (((m / 2 ^ b : ℕ) : ℝ) * η + 2) * 2 ^ b ≤ δ * 2 ^ h₀ * 2 ^ b :=
        mul_le_mul_of_nonneg_right hfin h2b.le
    _ = δ * 2 ^ (b + h₀) := by rw [pow_add]; ring

end CollatzMoonshot.Conjugacy
