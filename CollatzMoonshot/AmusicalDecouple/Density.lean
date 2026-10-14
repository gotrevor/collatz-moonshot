/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Densities of eventually periodic sets, and CRT decoupling

Helpers for `CollatzMoonshot/AmusicalDecouple.lean` (Lemma D).  `cnt S X` is definitionally the
`countBelow S X` of that file.

* `tendsto_cnt_div_of_evPer`: an eventually `p`-periodic set has a density, its block count over
  `p`.
* `tendsto_cnt_inter_of_coprime`: eventually periodic sets with coprime periods are independent
  (CRT).
* `tendsto_of_sandwich`: a two-parameter squeeze.
* `tendsto_cnt_inter_iInter`: an eventually `2`-power-periodic set is independent of the
  intersection of a `3`-power-periodic family (step (i) of Lemma D).
-/

namespace CollatzMoonshot.Amusical.Decouple

open Filter Topology

open Classical in
/-- The number of elements of `S` below `X` (definitionally `countBelow`). -/
noncomputable def cnt (S : Set ℕ) (X : ℕ) : ℕ :=
  ((Finset.range X).filter fun n => n ∈ S).card

open Classical in
theorem cnt_succ (S : Set ℕ) (X : ℕ) :
    cnt S (X + 1) = cnt S X + if X ∈ S then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

theorem cnt_zero (S : Set ℕ) : cnt S 0 = 0 := by
  simp [cnt]

theorem cnt_le_cnt {S T : Set ℕ} (h : S ⊆ T) (X : ℕ) : cnt S X ≤ cnt T X := by
  induction X with
  | zero => simp [cnt_zero]
  | succ X ih =>
      rw [cnt_succ, cnt_succ]
      by_cases hS : X ∈ S
      · simp [hS, h hS]; omega
      · by_cases hT : X ∈ T <;> simp [hS, hT] <;> omega

theorem cnt_mono_right (S : Set ℕ) {X Y : ℕ} (h : X ≤ Y) : cnt S X ≤ cnt S Y := by
  induction Y, h using Nat.le_induction with
  | base => exact le_rfl
  | succ Y _ ih =>
      rw [cnt_succ]
      omega

theorem cnt_le (S : Set ℕ) (X : ℕ) : cnt S X ≤ X := by
  induction X with
  | zero => simp [cnt_zero]
  | succ X ih =>
      rw [cnt_succ]
      split_ifs <;> omega

theorem cnt_compl_add (S : Set ℕ) (X : ℕ) : cnt Sᶜ X + cnt S X = X := by
  induction X with
  | zero => simp [cnt_zero]
  | succ X ih =>
      rw [cnt_succ, cnt_succ]
      by_cases hS : X ∈ S
      · have : X ∉ Sᶜ := fun h => h hS
        simp [hS, this]; omega
      · have : X ∈ Sᶜ := hS
        simp [hS, this]; omega

theorem cnt_inter_add_diff (S T : Set ℕ) (X : ℕ) :
    cnt (S ∩ T) X + cnt (S \ T) X = cnt S X := by
  induction X with
  | zero => simp [cnt_zero]
  | succ X ih =>
      rw [cnt_succ, cnt_succ, cnt_succ]
      by_cases hS : X ∈ S <;> by_cases hT : X ∈ T <;> simp [hS, hT] <;> omega

theorem cnt_union_le (S T : Set ℕ) (X : ℕ) : cnt (S ∪ T) X ≤ cnt S X + cnt T X := by
  induction X with
  | zero => simp [cnt_zero]
  | succ X ih =>
      rw [cnt_succ, cnt_succ, cnt_succ]
      by_cases hS : X ∈ S <;> by_cases hT : X ∈ T <;> simp [hS, hT] <;> omega

open Classical in
theorem cnt_add (S : Set ℕ) (M k : ℕ) :
    cnt S (M + k) = cnt S M + ((Finset.range k).filter fun i => M + i ∈ S).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← add_assoc, cnt_succ, ih, Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · rfl

/-! ## Eventually periodic sets -/

/-- `S` is `p`-periodic from `N` on. -/
def EvPer (S : Set ℕ) (p N : ℕ) : Prop :=
  ∀ n, N ≤ n → (n ∈ S ↔ n + p ∈ S)

theorem EvPer.mono {S : Set ℕ} {p N N' : ℕ} (h : EvPer S p N) (hN : N ≤ N') : EvPer S p N' :=
  fun n hn => h n (hN.trans hn)

theorem EvPer.add_mul {S : Set ℕ} {p N : ℕ} (h : EvPer S p N) (k : ℕ) {n : ℕ} (hn : N ≤ n) :
    n + k * p ∈ S ↔ n ∈ S := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [add_one_mul, ← add_assoc, ← h _ (by omega), ih]

theorem EvPer.mul {S : Set ℕ} {p N : ℕ} (h : EvPer S p N) (k : ℕ) : EvPer S (k * p) N :=
  fun _ hn => (h.add_mul k hn).symm

theorem EvPer.compl {S : Set ℕ} {p N : ℕ} (h : EvPer S p N) : EvPer Sᶜ p N :=
  fun n hn => not_congr (h n hn)

theorem EvPer.inter {S T : Set ℕ} {p q N : ℕ} (hS : EvPer S p N) (hT : EvPer T q N) :
    EvPer (S ∩ T) (p * q) N := by
  intro n hn
  have h1 := hS.mul q n hn
  have h2 := hT.mul p n hn
  rw [mul_comm q p] at h1
  rw [Set.mem_inter_iff, Set.mem_inter_iff, h1, h2]

open Classical in
/-- The number of elements of `S` in the block `[M, M + p)`. -/
noncomputable def blockCnt (S : Set ℕ) (M p : ℕ) : ℕ :=
  ((Finset.range p).filter fun i => M + i ∈ S).card

open Classical in
theorem blockCnt_le (S : Set ℕ) (M p : ℕ) : blockCnt S M p ≤ p := by
  unfold blockCnt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem cnt_add_period {S : Set ℕ} {p N : ℕ} (h : EvPer S p N) {X : ℕ} (hX : N ≤ X) :
    cnt S (X + p) = cnt S X + blockCnt S N p := by
  induction X, hX using Nat.le_induction with
  | base => exact cnt_add S N p
  | succ X hX ih =>
      rw [show X + 1 + p = X + p + 1 by omega, cnt_succ, cnt_succ, ih]
      have hiff := h X hX
      by_cases hS : X ∈ S
      · simp [hS, hiff.1 hS]; omega
      · have : X + p ∉ S := fun h' => hS (hiff.2 h')
        simp [hS, this]

theorem cnt_add_mul_period {S : Set ℕ} {p N : ℕ} (h : EvPer S p N) {X : ℕ} (hX : N ≤ X)
    (k : ℕ) : cnt S (X + k * p) = cnt S X + k * blockCnt S N p := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [add_one_mul, ← add_assoc, cnt_add_period h (by omega), ih, add_one_mul]
      ring

/-- A bounded error against a linear function gives a density. -/
theorem tendsto_div_of_abs_sub_le {f : ℕ → ℝ} {γ K : ℝ} (N : ℕ)
    (h : ∀ X, N ≤ X → |f X - γ * X| ≤ K) :
    Tendsto (fun X : ℕ => f X / X) atTop (𝓝 γ) := by
  have h0 : Tendsto (fun X : ℕ => (f X - γ * X) / X) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat K)
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with X hX hX1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hXpos]
    exact div_le_div_of_nonneg_right (h X hX) hXpos.le
  have h1 := h0.const_add γ
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX1
  have hXpos : (X : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **An eventually periodic set has a density**: its block count over the period. -/
theorem tendsto_cnt_div_of_evPer {S : Set ℕ} {p N : ℕ} (hp : 0 < p) (h : EvPer S p N) :
    Tendsto (fun X : ℕ => (cnt S X : ℝ) / X) atTop (𝓝 ((blockCnt S N p : ℝ) / p)) := by
  set c := blockCnt S N p with hc
  refine tendsto_div_of_abs_sub_le (K := (N + p) + (c / p) * (N + p)) N ?_
  intro X hX
  set r := (X - N) % p
  set k := (X - N) / p
  have hXeq : X = (N + r) + k * p := by
    have := Nat.mod_add_div (X - N) p
    simp only [r, k]
    rw [mul_comm]
    omega
  have hr : r < p := Nat.mod_lt _ hp
  have hcnt := cnt_add_mul_period h (X := N + r) (by omega) k
  rw [← hXeq] at hcnt
  have hle : cnt S (N + r) ≤ N + r := cnt_le S (N + r)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hXR : (X : ℝ) = (N + r : ℕ) + k * p := by exact_mod_cast hXeq
  have hkey : (cnt S X : ℝ) - c / p * X = (cnt S (N + r) : ℝ) - c / p * (N + r : ℕ) := by
    rw [hcnt, hXR]
    push_cast
    field_simp
    ring
  rw [hkey]
  have hcp : (0 : ℝ) ≤ c / p := by positivity
  have hle' : (cnt S (N + r) : ℝ) ≤ N + p := by
    have : cnt S (N + r) ≤ N + p := by omega
    exact_mod_cast this
  have hNr : ((N + r : ℕ) : ℝ) ≤ N + p := by
    have : N + r ≤ N + p := by omega
    exact_mod_cast this
  have h1 : c / p * ((N + r : ℕ) : ℝ) ≤ c / p * (N + p) := mul_le_mul_of_nonneg_left hNr hcp
  have h2 : (0 : ℝ) ≤ c / p * ((N + r : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ cnt S (N + r) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **CRT block count.**  Over a block of length `p q` with coprime `p, q`, membership in a
`p`-periodic and a `q`-periodic set are independent. -/
theorem blockCnt_inter_of_coprime {P Q : Set ℕ} {p q M : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hP : EvPer P p M) (hQ : EvPer Q q M) :
    blockCnt (P ∩ Q) M (p * q) = blockCnt P M p * blockCnt Q M q := by
  classical
  have hPj : ∀ j, M + j ∈ P ↔ M + j % p ∈ P := by
    intro j
    have := hP.add_mul (j / p) (n := M + j % p) (by omega)
    rw [← this]
    have := Nat.mod_add_div j p
    rw [show M + j % p + j / p * p = M + j by rw [mul_comm]; omega]
  have hQj : ∀ j, M + j ∈ Q ↔ M + j % q ∈ Q := by
    intro j
    have := hQ.add_mul (j / q) (n := M + j % q) (by omega)
    rw [← this]
    have := Nat.mod_add_div j q
    rw [show M + j % q + j / q * q = M + j by rw [mul_comm]; omega]
  unfold blockCnt
  rw [← Finset.card_product]
  refine Finset.card_bij (fun j _ => (j % p, j % q)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff] at hj
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ hp, (hPj j).1 hj.2.1⟩, ⟨Nat.mod_lt _ hq, (hQj j).1 hj.2.2⟩⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
    simp only [Prod.mk.injEq] at heq
    have hmod : j₁ ≡ j₂ [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hpq).1 ⟨heq.1, heq.2⟩
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt hj₁.1, Nat.mod_eq_of_lt hj₂.1] at hmod
  · rintro ⟨s, t⟩ hst
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hst
    obtain ⟨⟨hs, hsP⟩, ⟨ht, htQ⟩⟩ := hst
    let k := Nat.chineseRemainder hpq s t
    have hk1 : k.val % p = s := by
      rw [k.prop.1]; exact Nat.mod_eq_of_lt hs
    have hk2 : k.val % q = t := by
      rw [k.prop.2]; exact Nat.mod_eq_of_lt ht
    refine ⟨k.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff]
      refine ⟨Nat.chineseRemainder_lt_mul hpq s t hp.ne' hq.ne', ?_, ?_⟩
      · rw [hPj, hk1]; exact hsP
      · rw [hQj, hk2]; exact htQ
    · simp [hk1, hk2]

/-- **CRT independence.**  Eventually periodic sets with coprime periods are independent. -/
theorem tendsto_cnt_inter_of_coprime {P Q : Set ℕ} {p q N : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hP : EvPer P p N) (hQ : EvPer Q q N) {dP dQ : ℝ}
    (hdP : Tendsto (fun X : ℕ => (cnt P X : ℝ) / X) atTop (𝓝 dP))
    (hdQ : Tendsto (fun X : ℕ => (cnt Q X : ℝ) / X) atTop (𝓝 dQ)) :
    Tendsto (fun X : ℕ => (cnt (P ∩ Q) X : ℝ) / X) atTop (𝓝 (dP * dQ)) := by
  have eP := tendsto_nhds_unique hdP (tendsto_cnt_div_of_evPer hp hP)
  have eQ := tendsto_nhds_unique hdQ (tendsto_cnt_div_of_evPer hq hQ)
  have h := tendsto_cnt_div_of_evPer (Nat.mul_pos hp hq) (hP.inter hQ)
  rw [blockCnt_inter_of_coprime hp hq hpq hP hQ] at h
  rw [eP, eQ]
  convert h using 2
  push_cast
  field_simp

/-! ## The squeeze and Lemma D -/

/-- A two-parameter squeeze: `f` is trapped between `h L` and `g L`, whose limits `H L`, `G L`
both tend to `γ`. -/
theorem tendsto_of_sandwich {f : ℕ → ℝ} {γ : ℝ} {g h : ℕ → ℕ → ℝ} {G H : ℕ → ℝ}
    (hg : ∀ L, Tendsto (g L) atTop (𝓝 (G L))) (hh : ∀ L, Tendsto (h L) atTop (𝓝 (H L)))
    (hG : Tendsto G atTop (𝓝 γ)) (hH : Tendsto H atTop (𝓝 γ))
    (hfg : ∀ L X, f X ≤ g L X) (hhf : ∀ L X, h L X ≤ f X) :
    Tendsto f atTop (𝓝 γ) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨L, hL⟩ := (hH.eventually (lt_mem_nhds ha)).exists
    filter_upwards [(hh L).eventually (lt_mem_nhds hL)] with X hX
    exact hX.trans_le (hhf L X)
  · intro b hb
    obtain ⟨L, hL⟩ := (hG.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hg L).eventually (gt_mem_nhds hL)] with X hX
    exact (hfg L X).trans_lt hX

theorem cnt_div_le {S T : Set ℕ} (h : S ⊆ T) (X : ℕ) : (cnt S X : ℝ) / X ≤ (cnt T X : ℝ) / X :=
  div_le_div_of_nonneg_right (by exact_mod_cast cnt_le_cnt h X) (by positivity)

theorem tendsto_cnt_compl {S : Set ℕ} {d : ℝ}
    (h : Tendsto (fun X : ℕ => (cnt S X : ℝ) / X) atTop (𝓝 d)) :
    Tendsto (fun X : ℕ => (cnt Sᶜ X : ℝ) / X) atTop (𝓝 (1 - d)) := by
  refine (h.const_sub 1).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hXR : (X : ℝ) ≠ 0 := by positivity
  have hc := cnt_compl_add S X
  have hcR : (cnt Sᶜ X : ℝ) + cnt S X = X := by exact_mod_cast hc
  field_simp
  linarith

/-- **Step (i) of Lemma D.**  An eventually `2`-power-periodic set `P` of density `d` meets
`⋂ B_L` in density `d β`. -/
theorem tendsto_cnt_inter_iInter {P : Set ℕ} {a N : ℕ} (hP : EvPer P (2 ^ a) N) {d : ℝ}
    (hdP : Tendsto (fun X : ℕ => (cnt P X : ℝ) / X) atTop (𝓝 d))
    {B : ℕ → Set ℕ} (pB : ∀ L, ∃ b N : ℕ, EvPer (B L) (3 ^ b) N) {b : ℕ → ℝ} {β : ℝ}
    (hBL : ∀ L, Tendsto (fun X : ℕ => (cnt (B L) X : ℝ) / X) atTop (𝓝 (b L)))
    (hb : Tendsto b atTop (𝓝 β))
    (hB : Tendsto (fun X : ℕ => (cnt (⋂ L, B L) X : ℝ) / X) atTop (𝓝 β)) :
    Tendsto (fun X : ℕ => (cnt (P ∩ ⋂ L, B L) X : ℝ) / X) atTop (𝓝 (d * β)) := by
  have hind : ∀ (Q : Set ℕ) {e : ℝ}, EvPer Q (2 ^ a) N →
      Tendsto (fun X : ℕ => (cnt Q X : ℝ) / X) atTop (𝓝 e) →
      ∀ L, Tendsto (fun X : ℕ => (cnt (Q ∩ B L) X : ℝ) / X) atTop (𝓝 (e * b L)) := by
    intro Q e hQ he L
    obtain ⟨k, N', hN'⟩ := pB L
    exact tendsto_cnt_inter_of_coprime (by positivity) (by positivity)
      (Nat.Coprime.pow _ _ (by norm_num)) (hQ.mono (le_max_left N N'))
      (hN'.mono (le_max_right N N')) he (hBL L)
  refine tendsto_of_sandwich (g := fun L X => (cnt (P ∩ B L) X : ℝ) / X)
    (h := fun L X => ((cnt (⋂ L, B L) X : ℝ) - cnt (Pᶜ ∩ B L) X) / X)
    (G := fun L => d * b L) (H := fun L => β - (1 - d) * b L)
    (hind P hP hdP) ?_ (tendsto_const_nhds.mul hb) ?_ ?_ ?_
  · intro L
    have := hB.sub (hind Pᶜ hP.compl (tendsto_cnt_compl hdP) L)
    simpa only [sub_div] using this
  · have := tendsto_const_nhds (x := β) |>.sub ((tendsto_const_nhds (x := 1 - d)).mul hb)
    convert this using 2
    ring
  · intro L X
    exact cnt_div_le (Set.inter_subset_inter_right _ (Set.iInter_subset _ L)) X
  · intro L X
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 := cnt_inter_add_diff (⋂ L, B L) P X
    have h2 : cnt ((⋂ L, B L) \ P) X ≤ cnt (Pᶜ ∩ B L) X := by
      apply cnt_le_cnt
      intro n hn
      exact ⟨hn.2, Set.mem_iInter.1 hn.1 L⟩
    rw [Set.inter_comm] at h1
    have h1R : (cnt (P ∩ ⋂ L, B L) X : ℝ) + cnt ((⋂ L, B L) \ P) X = cnt (⋂ L, B L) X := by
      exact_mod_cast h1
    have h2R : (cnt ((⋂ L, B L) \ P) X : ℝ) ≤ cnt (Pᶜ ∩ B L) X := by exact_mod_cast h2
    linarith

/-- **Lemma D**, phrased with `cnt` and `EvPer`. -/
theorem tendsto_cnt_iInter_inter {A B : ℕ → Set ℕ}
    (pA : ∀ L, ∃ a N : ℕ, EvPer (A L) (2 ^ a) N) (pB : ∀ L, ∃ b N : ℕ, EvPer (B L) (3 ^ b) N)
    {a b : ℕ → ℝ} {α β : ℝ}
    (hAL : ∀ L, Tendsto (fun X : ℕ => (cnt (A L) X : ℝ) / X) atTop (𝓝 (a L)))
    (hBL : ∀ L, Tendsto (fun X : ℕ => (cnt (B L) X : ℝ) / X) atTop (𝓝 (b L)))
    (ha : Tendsto a atTop (𝓝 α)) (hb : Tendsto b atTop (𝓝 β))
    (hA : Tendsto (fun X : ℕ => (cnt (⋂ L, A L) X : ℝ) / X) atTop (𝓝 α))
    (hB : Tendsto (fun X : ℕ => (cnt (⋂ L, B L) X : ℝ) / X) atTop (𝓝 β)) :
    Tendsto (fun X : ℕ => (cnt ((⋂ L, A L) ∩ ⋂ L, B L) X : ℝ) / X) atTop (𝓝 (α * β)) := by
  have hstep : ∀ L, Tendsto (fun X : ℕ => (cnt (A L ∩ ⋂ L, B L) X : ℝ) / X) atTop
      (𝓝 (a L * β)) := by
    intro L
    obtain ⟨k, N, hN⟩ := pA L
    exact tendsto_cnt_inter_iInter hN (hAL L) pB hBL hb hB
  refine tendsto_of_sandwich (g := fun L X => (cnt (A L ∩ ⋂ L, B L) X : ℝ) / X)
    (h := fun L X => ((cnt (A L ∩ ⋂ L, B L) X : ℝ) - (cnt (A L) X - cnt (⋂ L, A L) X)) / X)
    (G := fun L => a L * β) (H := fun L => a L * β - (a L - α))
    hstep ?_ (ha.mul_const β) ?_ ?_ ?_
  · intro L
    have := (hstep L).sub ((hAL L).sub hA)
    simpa only [sub_div] using this
  · have := (ha.mul_const β).sub (ha.sub (tendsto_const_nhds (x := α)))
    convert this using 2
    ring
  · intro L X
    exact cnt_div_le (Set.inter_subset_inter_left _ (Set.iInter_subset _ L)) X
  · intro L X
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsub : (⋂ L, A L) ⊆ A L := Set.iInter_subset _ L
    have h1 := cnt_inter_add_diff (A L) (⋂ L, A L) X
    rw [Set.inter_eq_right.2 hsub] at h1
    have h2 : cnt (A L ∩ ⋂ L, B L) X ≤
        cnt ((⋂ L, A L) ∩ ⋂ L, B L) X + cnt (A L \ ⋂ L, A L) X := by
      refine (cnt_le_cnt ?_ X).trans (cnt_union_le _ _ X)
      intro n hn
      by_cases hA' : n ∈ ⋂ L, A L
      · exact Or.inl ⟨hA', hn.2⟩
      · exact Or.inr ⟨hn.1, hA'⟩
    have h1R : (cnt (⋂ L, A L) X : ℝ) + cnt (A L \ ⋂ L, A L) X = cnt (A L) X := by
      exact_mod_cast h1
    have h2R : (cnt (A L ∩ ⋂ L, B L) X : ℝ) ≤
        cnt ((⋂ L, A L) ∩ ⋂ L, B L) X + cnt (A L \ ⋂ L, A L) X := by exact_mod_cast h2
    linarith

end CollatzMoonshot.Amusical.Decouple
