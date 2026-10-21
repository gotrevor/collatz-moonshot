/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Champernowne

/-!
# Bridges between the Champernowne hypotheses

`Champernowne.lean` reads the normality of `𝒞_C` through two hypotheses on the parity words of
the `k`-bit integers: `ShortIntervalMixing C` (the letters at every beyond-Terras position
`t ∈ [k, Ck − L]` are jointly uniform over the stage, error `o(2^k)`) and `EarlyArrival C` (a
fixed fraction `ρ` of the stage has reached `1` by step `r k`, `r < C`).  This module proves
the edge between them: **they exclude each other** (`not_shortIntervalMixing_of_earlyArrival`).
An orbit that has reached `1` emits the cycle tail `1010…` (`accWord_of_reaches_one`), so its
block of length `L` at any position past the arrival is one of the two alternating patterns
(`block_eq_altPattern`), and the `2^L − 2` non-alternating patterns together miss the whole
arrived fraction: a deficit of `ρ − 2^(1−L)` of the stage, which the `o(2^k)` error of mixing
cannot absorb.

Together with `not_normal_of_earlyArrival` this is the `C > C*` side of the threshold of
`Champernowne.lean`: above the stopping-time constant, early arrival (which the stochastic model
predicts) rules out both normality of `𝒞_C` and the mixing hypothesis.  `earlyArrival_mono`
says the early-arrival regime is upward closed in `C`.

* `tstep_iterate_one`, `accWord_of_reaches_one`: the cycle `1 → 2 → 1` and its parity tail.
* `le_two_pow_mul_tstep_iterate`, `le_of_reaches_one`: `n ≤ 2^s · tstep^[s] n`, so a `k`-bit
  start needs `k − 1` steps to reach `1`.  This is what lets the headline take every `C`: for
  `C ≤ 1` it makes `EarlyArrival C` itself false.
* `altPattern`, `block`, `block_mem_altPatterns`, `card_compl_altPatterns`: the alternating
  patterns, the block map, and the count `2^L − 2` of non-alternating patterns.
* `not_shortIntervalMixing_of_earlyArrival`: the headline.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## The cycle `1 → 2 → 1` and its parity tail -/

theorem tstep_one : tstep 1 = 2 := by decide

theorem tstep_two : tstep 2 = 1 := by decide

/-- The orbit of `1` is the cycle `1, 2, 1, 2, …`. -/
theorem tstep_iterate_one (i : ℕ) : tstep^[i] 1 = if i % 2 = 0 then 1 else 2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h' : (i + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (i + 1) % 2 = 0 := by omega
      simp [h, h']

/-- **The tail of an arrived orbit.**  Once `tstep^[s] n = 1`, the letters from position `s` on
alternate `1, 0, 1, 0, …`. -/
theorem accWord_of_reaches_one {n s : ℕ} (hs : tstep^[s] n = 1) (i : ℕ) :
    accWord n (s + i) = decide (i % 2 = 0) := by
  simp only [accWord]
  rw [add_comm, Function.iterate_add_apply, hs, tstep_iterate_one]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-! ## A `k`-bit start needs `k − 1` steps -/

/-- One shortcut step at most halves. -/
theorem le_two_mul_tstep (n : ℕ) : n ≤ 2 * tstep n := by
  unfold tstep; split_ifs <;> omega

/-- `n ≤ 2^s · tstep^[s] n`: in `s` steps the orbit cannot drop below `n / 2^s`. -/
theorem le_two_pow_mul_tstep_iterate (s : ℕ) : ∀ n, n ≤ 2 ^ s * tstep^[s] n := by
  induction s with
  | zero => intro n; simp
  | succ s ih =>
    intro n
    rw [Function.iterate_succ_apply, pow_succ, mul_comm (2 ^ s) 2, mul_assoc]
    exact (le_two_mul_tstep n).trans (Nat.mul_le_mul_left 2 (ih (tstep n)))

/-- A start `≥ 2^(k-1)` that has reached `1` by step `s` has `k − 1 ≤ s`. -/
theorem le_of_reaches_one {n k s : ℕ} (hn : 2 ^ (k - 1) ≤ n) (hs : tstep^[s] n = 1) :
    k - 1 ≤ s := by
  have h := le_two_pow_mul_tstep_iterate s n
  rw [hs, mul_one] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hn.trans h)

/-! ## Alternating patterns and blocks -/

/-- The alternating pattern of length `L` and phase `d`: `altPattern L d s = decide ((d + s) % 2 = 0)`.
Phase `0` reads `1010…`, phase `1` reads `0101…`; only the phase mod `2` matters. -/
def altPattern (L d : ℕ) : Fin L → Bool := fun s => decide ((d + s) % 2 = 0)

theorem altPattern_mod_two (L d : ℕ) : altPattern L d = altPattern L (d % 2) := by
  funext s; simp only [altPattern, decide_eq_decide]; omega

/-- The two alternating patterns of a length `L ≥ 1` are distinct. -/
theorem altPattern_zero_ne_one {L : ℕ} (hL : 1 ≤ L) : altPattern L 0 ≠ altPattern L 1 := by
  intro h
  have := congrFun h ⟨0, hL⟩
  simp [altPattern] at this

/-- The block of length `L` read at position `t` of the parity word of `n`. -/
def block (L t n : ℕ) : Fin L → Bool := fun s => accWord n (t + s)

/-- **An arrived orbit shows only alternating blocks.**  If `tstep^[s] n = 1` and `s ≤ t`, the
block at `t` is the alternating pattern of phase `t − s`. -/
theorem block_eq_altPattern {n s t : ℕ} (hs : tstep^[s] n = 1) (hst : s ≤ t) (L : ℕ) :
    block L t n = altPattern L (t - s) := by
  funext j
  simp only [block, altPattern]
  have e : t + (j : ℕ) = s + (t - s + j) := by omega
  rw [e, accWord_of_reaches_one hs]

/-- The block of an arrived orbit lies in the two-element set of alternating patterns. -/
theorem block_mem_altPatterns {n s t : ℕ} (hs : tstep^[s] n = 1) (hst : s ≤ t) (L : ℕ) :
    block L t n ∈ ({altPattern L 0, altPattern L 1} : Finset (Fin L → Bool)) := by
  rw [block_eq_altPattern hs hst, altPattern_mod_two L (t - s)]
  rcases Nat.mod_two_eq_zero_or_one (t - s) with h | h <;> simp [h]

/-- There are `2^L − 2` non-alternating patterns of length `L ≥ 1`. -/
theorem card_compl_altPatterns {L : ℕ} (hL : 1 ≤ L) :
    (({altPattern L 0, altPattern L 1} : Finset (Fin L → Bool))ᶜ).card = 2 ^ L - 2 := by
  rw [Finset.card_compl, Finset.card_pair (altPattern_zero_ne_one hL), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-! ## The bridges -/

/-- Early arrival is upward closed in `C`: the rate `r < C` stays below any `C' ≥ C`. -/
theorem earlyArrival_mono {C C' : ℕ} (h : C ≤ C') : EarlyArrival C → EarlyArrival C' := by
  rintro ⟨r, ρ, hr, hρ, hev⟩
  exact ⟨r, ρ, hr.trans_le (by exact_mod_cast h), hρ, hev⟩

/-- **Edge: early arrival at the cycle contradicts short-interval mixing.**  Orbits that have
reached `1` emit `1010…`, so they never show a non-alternating block; if a fixed fraction `ρ`
of the `k`-bit integers has arrived by step `r·k < C·k`, the non-alternating blocks of length
`L` at a beyond-range position are under-represented by `ρ − 2^(1−L)`, which no `o(2^k)` error
absorbs.  Together with `not_normal_of_earlyArrival` (Champernowne.lean) this is the `C > C*`
side of the threshold: above the stopping-time constant neither `𝒞_C` normal nor the mixing
hypothesis can hold if early arrival holds.

Proof.  Take `L` with `4 < ρ 2^L`, `δ = ρ / (4 · 2^L)`, and `k` large enough for mixing at every
pattern, for `L + 2 ≤ (C − r) k`, and for the arrival bound.  The position is
`T = ⌈r k⌉₊ + 1`: every arrival time `s` has `s ≤ T`, and `k − 1 ≤ s` (`le_of_reaches_one`),
so `k ≤ T` and `T + L ≤ C k`.  Summing the mixing lower bound `M / 2^L − δ M` over the
`2^L − 2` non-alternating patterns (fibres of the block map,
`Finset.sum_card_fiberwise_eq_card_filter`) counts the `n` in the stage whose block at `T` is
non-alternating; none of the `≥ ρ M` arrivers is among them (`block_mem_altPatterns`), so the
count is `≤ (1 − ρ) M`.  Dividing by `M`: `(2^L − 2)(4 − ρ) ≤ 4 · 2^L (1 − ρ)`, i.e.
`3 ρ 2^L + 2 ρ ≤ 8`, against `ρ 2^L > 4`. -/
theorem not_shortIntervalMixing_of_earlyArrival (C : ℕ) (h : EarlyArrival C) :
    ¬ ShortIntervalMixing C := by
  classical
  intro hmix
  obtain ⟨r, ρ, hrC, hρ, hev⟩ := h
  -- The block length: `4 < ρ 2^L`, i.e. `2^(1−L) < ρ / 2`.
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt (4 / ρ) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = L₀ + 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by omega
  have hP : 4 < ρ * 2 ^ L := by
    have : (4 : ℝ) / ρ < 2 ^ L :=
      hL₀.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
    rwa [div_lt_iff₀ hρ, mul_comm] at this
  have hPpos : (0 : ℝ) < 2 ^ L := by positivity
  -- The error tolerance.
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ρ / (4 * 2 ^ L) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- Mixing for every pattern at once, eventually in `k`.
  have hmix' : ∀ᶠ k : ℕ in atTop, ∀ p : Fin L → Bool, ∀ m : ℕ, m ≤ 2 ^ (k - 1) →
      ∀ t : ℕ, k ≤ t → t + L ≤ C * k →
        |(((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
            fun n => ∀ s : Fin L, accWord n (t + s) = p s).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
          δ * 2 ^ (k - 1) := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_atTop]
    exact hmix L p δ hδpos
  -- Room beyond the arrival: eventually `L + 2 ≤ (C − r) k`.
  have hCr : 0 < (C : ℝ) - r := by linarith
  have hbig : ∀ᶠ k : ℕ in atTop, (L : ℝ) + 2 ≤ ((C : ℝ) - r) * k := by
    obtain ⟨K₁, hK₁⟩ := exists_nat_ge (((L : ℝ) + 2) / ((C : ℝ) - r))
    rw [Filter.eventually_atTop]
    refine ⟨K₁, fun k hk => ?_⟩
    have hk' : (K₁ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ hCr] at hK₁
    have := mul_le_mul_of_nonneg_right hk' hCr.le
    linarith
  obtain ⟨k, hk_ev, hk_mix, hk_big, hk1⟩ :=
    (hev.and (hmix'.and (hbig.and (eventually_ge_atTop 1)))).exists
  -- The stage `[M, 2M)`, `M = 2^(k-1)`, and its arrivers `A`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ (k - 1) := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMR : (M : ℝ) = 2 ^ (k - 1) := by simp [hM]
  have hMRpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hM2 : 2 ^ k = M + M := by
    rw [hM, ← two_mul, ← pow_succ', Nat.sub_add_cancel hk1]
  rw [← hM] at hk_mix
  rw [← hM, hM2, ← hMR] at hk_ev
  obtain ⟨stage, hstage⟩ : ∃ stage : Finset ℕ, stage = Finset.Ico M (M + M) := ⟨_, rfl⟩
  have hstage_card : stage.card = M := by rw [hstage, Nat.card_Ico]; omega
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ,
      A = stage.filter (fun n => ∃ s : ℕ, (s : ℝ) ≤ r * k ∧ tstep^[s] n = 1) := ⟨_, rfl⟩
  have hAsub : A ⊆ stage := by rw [hA]; exact Finset.filter_subset _ _
  have hAle : A.card ≤ M := hstage_card ▸ Finset.card_le_card hAsub
  have hAset : {n : ℕ | M ≤ n ∧ n < M + M ∧ ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1} = ↑A := by
    ext n
    rw [hA, hstage]
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, and_assoc]
  rw [hAset, Set.ncard_coe_finset] at hk_ev
  -- Some arriver exists, so `k − 1 ≤ r k`, which puts `T = ⌈r k⌉₊ + 1` in the window.
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hk_ev
  obtain ⟨n₀, hn₀⟩ : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  rw [hA, Finset.mem_filter, hstage, Finset.mem_Ico] at hn₀
  obtain ⟨⟨hn₀M, -⟩, s₀, hs₀r, hs₀⟩ := hn₀
  have hk_s₀ : k - 1 ≤ s₀ := le_of_reaches_one (k := k) (hM ▸ hn₀M) hs₀
  have hrk : (k : ℝ) - 1 ≤ r * k := by
    have h1 : ((k - 1 : ℕ) : ℝ) ≤ s₀ := by exact_mod_cast hk_s₀
    rw [Nat.cast_sub hk1] at h1
    push_cast at h1
    linarith
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hrk0 : 0 ≤ r * k := by linarith
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈r * k⌉₊ + 1 := ⟨_, rfl⟩
  have hTR : (T : ℝ) = ⌈r * k⌉₊ + 1 := by rw [hT]; push_cast; ring
  have hkT : k ≤ T := by
    have : (k : ℝ) ≤ T := by rw [hTR]; linarith [Nat.le_ceil (r * k)]
    exact_mod_cast this
  have hTL : T + L ≤ C * k := by
    have h1 : (⌈r * k⌉₊ : ℝ) < r * k + 1 := Nat.ceil_lt_add_one hrk0
    have : ((T + L : ℕ) : ℝ) ≤ ((C * k : ℕ) : ℝ) := by push_cast; rw [hTR]; linarith
    exact_mod_cast this
  have hsT : ∀ s : ℕ, (s : ℝ) ≤ r * k → s ≤ T := by
    intro s hs
    have : (s : ℝ) ≤ T := by rw [hTR]; linarith [Nat.le_ceil (r * k)]
    exact_mod_cast this
  -- The non-alternating patterns `N` and the fibres of the block map at `T`.
  obtain ⟨N, hN⟩ : ∃ N : Finset (Fin L → Bool),
      N = ({altPattern L 0, altPattern L 1} : Finset (Fin L → Bool))ᶜ := ⟨_, rfl⟩
  have hNcard : (N.card : ℝ) = 2 ^ L - 2 := by
    have h2 : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
    rw [hN, card_compl_altPatterns hL1, Nat.cast_sub h2]
    push_cast
    ring
  have hfib : ∀ p : Fin L → Bool, stage.filter (fun n => block L T n = p) =
      stage.filter (fun n => ∀ s : Fin L, accWord n (T + s) = p s) :=
    fun p => Finset.filter_congr fun n _ => by simp only [block, funext_iff]
  -- Mixing from below, pattern by pattern.
  have hlow : ∀ p ∈ N,
      (M : ℝ) / 2 ^ L - δ * M ≤ ((stage.filter (fun n => block L T n = p)).card : ℝ) := by
    intro p _
    have := hk_mix p M le_rfl T hkT hTL
    rw [← hMR, ← hstage, ← hfib p, abs_le] at this
    linarith [this.1]
  have hsum : (N.card : ℝ) * ((M : ℝ) / 2 ^ L - δ * M) ≤
      ∑ p ∈ N, ((stage.filter (fun n => block L T n = p)).card : ℝ) := by
    have := Finset.card_nsmul_le_sum N
      (fun p => ((stage.filter (fun n => block L T n = p)).card : ℝ)) _ hlow
    simpa [nsmul_eq_mul] using this
  have hX : ∑ p ∈ N, ((stage.filter (fun n => block L T n = p)).card : ℝ) =
      ((stage.filter (fun n => block L T n ∈ N)).card : ℝ) := by
    rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
  -- No arriver has a non-alternating block.
  have hXsub : stage.filter (fun n => block L T n ∈ N) ⊆ stage \ A := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_sdiff]
    refine ⟨hn.1, fun hnA => ?_⟩
    rw [hA, Finset.mem_filter] at hnA
    obtain ⟨-, s, hsr, hs⟩ := hnA
    have hmem := block_mem_altPatterns hs (hsT s hsr) L
    have hn2 := hn.2
    rw [hN, Finset.mem_compl] at hn2
    exact hn2 hmem
  have hcardX : ((stage.filter (fun n => block L T n ∈ N)).card : ℝ) ≤ (M : ℝ) - A.card := by
    have h1 := Finset.card_le_card hXsub
    rw [Finset.card_sdiff_of_subset hAsub, hstage_card] at h1
    have : ((stage.filter (fun n => block L T n ∈ N)).card : ℝ) ≤ ((M - A.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    rwa [Nat.cast_sub hAle] at this
  -- Assemble: `(2^L − 2)(M / 2^L − δ M) ≤ (1 − ρ) M`.
  have key : ((2 : ℝ) ^ L - 2) * ((M : ℝ) / 2 ^ L - δ * M) ≤ (M : ℝ) - ρ * M := by
    calc ((2 : ℝ) ^ L - 2) * ((M : ℝ) / 2 ^ L - δ * M)
        = (N.card : ℝ) * ((M : ℝ) / 2 ^ L - δ * M) := by rw [hNcard]
      _ ≤ ∑ p ∈ N, ((stage.filter (fun n => block L T n = p)).card : ℝ) := hsum
      _ = ((stage.filter (fun n => block L T n ∈ N)).card : ℝ) := hX
      _ ≤ (M : ℝ) - A.card := hcardX
      _ ≤ (M : ℝ) - ρ * M := by linarith
  -- Divide by `M > 0`, then clear `4 · 2^L`.
  have key' : ((2 : ℝ) ^ L - 2) * (1 / 2 ^ L - δ) ≤ 1 - ρ := by
    have e1 : ((2 : ℝ) ^ L - 2) * ((M : ℝ) / 2 ^ L - δ * M) =
        (M : ℝ) * (((2 : ℝ) ^ L - 2) * (1 / 2 ^ L - δ)) := by ring
    have e2 : (M : ℝ) - ρ * M = (M : ℝ) * (1 - ρ) := by ring
    rw [e1, e2] at key
    exact le_of_mul_le_mul_left key hMRpos
  have hδ' : 1 / (2 : ℝ) ^ L - δ = (4 - ρ) / (4 * 2 ^ L) := by
    rw [hδ]; field_simp
  rw [hδ', mul_div_assoc', div_le_iff₀ (by positivity)] at key'
  nlinarith [hP, hρ]

end CollatzMoonshot.Conjugacy
