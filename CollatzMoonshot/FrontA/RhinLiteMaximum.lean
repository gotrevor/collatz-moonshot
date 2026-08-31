/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteInterval

/-!
# Global maximum bound for the Rhin-lite kernel

This closes the analytic maximum step: the square of the normalized signed kernel attains its
maximum on `[2,4]`; a nonzero maximizer is interior, and logarithmic differentiation places it in
one of the seven already-certified critical brackets.
-/

namespace CollatzMoonshot.FrontA

open Set Polynomial

/-- The signed normalized Rhin-lite kernel. -/
noncomputable def rhinLiteKernel (x : ℝ) : ℝ :=
  rhinLiteFactor1 x ^ rhinLiteW1 *
    rhinLiteFactor2 x ^ rhinLiteW2 *
    rhinLiteFactor3 x ^ rhinLiteW3 *
    rhinLiteFactor4 x ^ rhinLiteW4 *
    rhinLiteFactor5 x ^ rhinLiteW5 *
    rhinLiteFactor6 x ^ rhinLiteW6 / x ^ rhinLiteScale

/-- Squaring removes the nondifferentiability of absolute value at factor zeros. -/
noncomputable def rhinLiteKernelSq (x : ℝ) : ℝ := rhinLiteKernel x ^ 2

/-- The logarithm of the squared kernel, used only where all factors are nonzero. -/
noncomputable def rhinLiteLogSq (x : ℝ) : ℝ :=
  (rhinLiteW1 : ℝ) * Real.log (rhinLiteFactor1 x ^ 2) +
    (rhinLiteW2 : ℝ) * Real.log (rhinLiteFactor2 x ^ 2) +
    (rhinLiteW3 : ℝ) * Real.log (rhinLiteFactor3 x ^ 2) +
    (rhinLiteW4 : ℝ) * Real.log (rhinLiteFactor4 x ^ 2) +
    (rhinLiteW5 : ℝ) * Real.log (rhinLiteFactor5 x ^ 2) +
    (rhinLiteW6 : ℝ) * Real.log (rhinLiteFactor6 x ^ 2) -
    (2 * (rhinLiteScale : ℝ)) * Real.log x

lemma rhinLiteKernelSq_continuousOn : ContinuousOn rhinLiteKernelSq (Icc (2 : ℝ) 4) := by
  unfold rhinLiteKernelSq rhinLiteKernel rhinLiteFactor1 rhinLiteFactor2 rhinLiteFactor3
    rhinLiteFactor4 rhinLiteFactor5 rhinLiteFactor6
  apply ContinuousOn.pow
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact pow_ne_zero _ (by linarith [hx.1])

lemma rhinLiteKernelSq_nonneg (x : ℝ) : 0 ≤ rhinLiteKernelSq x := by
  exact sq_nonneg _

lemma rhinLiteKernelSq_two : rhinLiteKernelSq 2 = 0 := by
  norm_num [rhinLiteKernelSq, rhinLiteKernel, rhinLiteFactor1, rhinLiteFactor2,
    rhinLiteFactor3, rhinLiteFactor4, rhinLiteFactor5, rhinLiteFactor6, rhinLiteW2]

lemma rhinLiteKernelSq_four : rhinLiteKernelSq 4 = 0 := by
  norm_num [rhinLiteKernelSq, rhinLiteKernel, rhinLiteFactor1, rhinLiteFactor2,
    rhinLiteFactor3, rhinLiteFactor4, rhinLiteFactor5, rhinLiteFactor6, rhinLiteW3]

lemma rhinLiteKernelSq_five_halves_pos : 0 < rhinLiteKernelSq (5 / 2 : ℝ) := by
  rw [rhinLiteKernelSq, sq_pos_iff]
  norm_num [rhinLiteKernel, rhinLiteFactor1, rhinLiteFactor2, rhinLiteFactor3,
    rhinLiteFactor4, rhinLiteFactor5, rhinLiteFactor6]

lemma rhinLiteKernelSq_three : rhinLiteKernelSq 3 = 0 := by
  norm_num [rhinLiteKernelSq, rhinLiteKernel, rhinLiteFactor1, rhinLiteFactor2,
    rhinLiteFactor3, rhinLiteFactor4, rhinLiteFactor5, rhinLiteFactor6, rhinLiteW1]

lemma rhinLiteKernelSq_seven_halves_pos : 0 < rhinLiteKernelSq (7 / 2 : ℝ) := by
  rw [rhinLiteKernelSq, sq_pos_iff]
  norm_num [rhinLiteKernel, rhinLiteFactor1, rhinLiteFactor2, rhinLiteFactor3,
    rhinLiteFactor4, rhinLiteFactor5, rhinLiteFactor6]

lemma hasDerivAt_rhinLiteLogSq (x : ℝ)
    (hx : x ≠ 0)
    (h1 : rhinLiteFactor1 x ≠ 0) (h2 : rhinLiteFactor2 x ≠ 0)
    (h3 : rhinLiteFactor3 x ≠ 0) (h4 : rhinLiteFactor4 x ≠ 0)
    (h5 : rhinLiteFactor5 x ≠ 0) (h6 : rhinLiteFactor6 x ≠ 0) :
    HasDerivAt rhinLiteLogSq
      (2 * (705 / rhinLiteFactor1 x + 551 / rhinLiteFactor2 x +
        449 / rhinLiteFactor3 x + 545 / rhinLiteFactor4 x +
        39 * (34 * x - 102) / rhinLiteFactor5 x +
        54 * (38 * x - 108) / rhinLiteFactor6 x - 1000 / x)) x := by
  have hf1 : HasDerivAt rhinLiteFactor1 1 x := by
    change HasDerivAt (fun y : ℝ => y - 3) 1 x
    exact HasDerivAt.sub_const 3 (hasDerivAt_id x)
  have hf2 : HasDerivAt rhinLiteFactor2 1 x := by
    change HasDerivAt (fun y : ℝ => y - 2) 1 x
    exact HasDerivAt.sub_const 2 (hasDerivAt_id x)
  have hf3 : HasDerivAt rhinLiteFactor3 1 x := by
    change HasDerivAt (fun y : ℝ => y - 4) 1 x
    exact HasDerivAt.sub_const 4 (hasDerivAt_id x)
  have hf4 : HasDerivAt rhinLiteFactor4 5 x := by
    change HasDerivAt (fun y : ℝ => 5 * y - 12) 5 x
    simpa only [id_eq, mul_one] using
      (HasDerivAt.sub_const 12 ((hasDerivAt_id x).const_mul 5))
  have hf5 : HasDerivAt rhinLiteFactor5 (34 * x - 102) x := by
    change HasDerivAt (fun y : ℝ => 17 * y ^ 2 - 102 * y + 144) (34 * x - 102) x
    convert HasDerivAt.add_const 144 ((((hasDerivAt_id x).pow 2).const_mul 17).sub
      ((hasDerivAt_id x).const_mul 102)) using 1
    all_goals try rfl
    all_goals simp only [id_eq, Nat.cast_ofNat, mul_one]
    all_goals first | rfl | ring
  have hf6 : HasDerivAt rhinLiteFactor6 (38 * x - 108) x := by
    change HasDerivAt (fun y : ℝ => 19 * y ^ 2 - 108 * y + 144) (38 * x - 108) x
    convert HasDerivAt.add_const 144 ((((hasDerivAt_id x).pow 2).const_mul 19).sub
      ((hasDerivAt_id x).const_mul 108)) using 1
    all_goals try rfl
    all_goals simp only [id_eq, Nat.cast_ofNat, mul_one]
    all_goals first | rfl | ring
  have hl1 := (hf1.pow 2).log (pow_ne_zero 2 h1)
  have hl2 := (hf2.pow 2).log (pow_ne_zero 2 h2)
  have hl3 := (hf3.pow 2).log (pow_ne_zero 2 h3)
  have hl4 := (hf4.pow 2).log (pow_ne_zero 2 h4)
  have hl5 := (hf5.pow 2).log (pow_ne_zero 2 h5)
  have hl6 := (hf6.pow 2).log (pow_ne_zero 2 h6)
  have hlx := (hasDerivAt_id x).log hx
  have H := ((((((hl1.const_mul (rhinLiteW1 : ℝ)).add (hl2.const_mul (rhinLiteW2 : ℝ))).add
    (hl3.const_mul (rhinLiteW3 : ℝ))).add (hl4.const_mul (rhinLiteW4 : ℝ))).add
    (hl5.const_mul (rhinLiteW5 : ℝ))).add (hl6.const_mul (rhinLiteW6 : ℝ))).sub
    (hlx.const_mul (2 * (rhinLiteScale : ℝ)))
  convert H using 1
  all_goals try { with_reducible_and_instances rfl }
  · funext y
    simp only [rhinLiteLogSq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, id_eq]
  · norm_num [rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6,
      rhinLiteScale, Pi.pow_apply, id_eq]
    field_simp [h1, h2, h3, h4, h5, h6, hx]
    ring

lemma rhinLiteCriticalReal_eval_eq_zero_of_logDeriv_eq_zero (x : ℝ)
    (hx : x ≠ 0)
    (h1 : rhinLiteFactor1 x ≠ 0) (h2 : rhinLiteFactor2 x ≠ 0)
    (h3 : rhinLiteFactor3 x ≠ 0) (h4 : rhinLiteFactor4 x ≠ 0)
    (h5 : rhinLiteFactor5 x ≠ 0) (h6 : rhinLiteFactor6 x ≠ 0)
    (hd : 2 * (705 / rhinLiteFactor1 x + 551 / rhinLiteFactor2 x +
        449 / rhinLiteFactor3 x + 545 / rhinLiteFactor4 x +
        39 * (34 * x - 102) / rhinLiteFactor5 x +
        54 * (38 * x - 108) / rhinLiteFactor6 x - 1000 / x) = 0) :
    rhinLiteCriticalReal.eval x = 0 := by
  rw [rhinLiteCriticalReal_eval]
  field_simp [h1, h2, h3, h4, h5, h6, hx] at hd
  simp only [rhinLiteFactor1, rhinLiteFactor2, rhinLiteFactor3, rhinLiteFactor4,
    rhinLiteFactor5, rhinLiteFactor6] at hd
  ring_nf at hd ⊢
  linarith

lemma exp_rhinLiteLogSq (x : ℝ) (hx : 0 < x)
    (h1 : rhinLiteFactor1 x ≠ 0) (h2 : rhinLiteFactor2 x ≠ 0)
    (h3 : rhinLiteFactor3 x ≠ 0) (h4 : rhinLiteFactor4 x ≠ 0)
    (h5 : rhinLiteFactor5 x ≠ 0) (h6 : rhinLiteFactor6 x ≠ 0) :
    Real.exp (rhinLiteLogSq x) = rhinLiteKernelSq x := by
  have hp1 : 0 < rhinLiteFactor1 x ^ 2 := (sq_pos_iff).2 h1
  have hp2 : 0 < rhinLiteFactor2 x ^ 2 := (sq_pos_iff).2 h2
  have hp3 : 0 < rhinLiteFactor3 x ^ 2 := (sq_pos_iff).2 h3
  have hp4 : 0 < rhinLiteFactor4 x ^ 2 := (sq_pos_iff).2 h4
  have hp5 : 0 < rhinLiteFactor5 x ^ 2 := (sq_pos_iff).2 h5
  have hp6 : 0 < rhinLiteFactor6 x ^ 2 := (sq_pos_iff).2 h6
  rw [rhinLiteLogSq, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add,
    Real.exp_add, Real.exp_add]
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_nat_mul]
  rw [show 2 * (rhinLiteScale : ℝ) * Real.log x =
      ((2 * rhinLiteScale : ℕ) : ℝ) * Real.log x by norm_num, Real.exp_nat_mul]
  rw [Real.exp_log hp1, Real.exp_log hp2, Real.exp_log hp3, Real.exp_log hp4,
    Real.exp_log hp5, Real.exp_log hp6, Real.exp_log hx]
  simp only [rhinLiteKernelSq, rhinLiteKernel]
  field_simp [ne_of_gt hx]
  ring

lemma abs_rhinLiteKernel_eq (x : ℝ) (hx : 0 < x) :
    |rhinLiteKernel x| = rhinLiteKernelAbs x / x ^ rhinLiteScale := by
  simp only [rhinLiteKernel, rhinLiteKernelAbs, abs_div, abs_mul, abs_pow, abs_of_pos hx]

set_option maxRecDepth 100000 in
/-- **Global base-block estimate.**  The seven local critical-point certificates control the
maximum of the normalized kernel on the whole base interval. -/
theorem rhinLiteKernelAbs_div_pow_le_on_Icc {x : ℝ} (hx : x ∈ Icc (2 : ℝ) 4) :
    rhinLiteKernelAbs x / x ^ rhinLiteScale ≤ (9 / 40 : ℝ) ^ rhinLiteScale := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (2 : ℝ) 4).Nonempty)
    rhinLiteKernelSq_continuousOn
  have hhalfmem : (5 / 2 : ℝ) ∈ Icc (2 : ℝ) 4 := by norm_num
  have hmpos : 0 < rhinLiteKernelSq m :=
    lt_of_lt_of_le rhinLiteKernelSq_five_halves_pos (hmax hhalfmem)
  have hkne : rhinLiteKernel m ≠ 0 := (sq_pos_iff.mp hmpos)
  have hm0 : m ≠ 0 := by linarith [hm.1]
  have h1 : rhinLiteFactor1 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW1]
  have h2 : rhinLiteFactor2 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW2]
  have h3 : rhinLiteFactor3 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW3]
  have h4 : rhinLiteFactor4 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW4]
  have h5 : rhinLiteFactor5 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW5]
  have h6 : rhinLiteFactor6 m ≠ 0 := by
    intro h
    apply hkne
    simp [rhinLiteKernel, h, rhinLiteW6]
  have hmne2 : m ≠ 2 := by
    intro h
    subst m
    rw [rhinLiteKernelSq_two] at hmpos
    linarith
  have hmne4 : m ≠ 4 := by
    intro h
    subst m
    rw [rhinLiteKernelSq_four] at hmpos
    linarith
  have hmopen : m ∈ Ioo (2 : ℝ) 4 := ⟨lt_of_le_of_ne hm.1 (Ne.symm hmne2),
    lt_of_le_of_ne hm.2 hmne4⟩
  have hopen1 : IsOpen {y : ℝ | rhinLiteFactor1 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor1; fun_prop)
  have hopen2 : IsOpen {y : ℝ | rhinLiteFactor2 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor2; fun_prop)
  have hopen3 : IsOpen {y : ℝ | rhinLiteFactor3 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor3; fun_prop)
  have hopen4 : IsOpen {y : ℝ | rhinLiteFactor4 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor4; fun_prop)
  have hopen5 : IsOpen {y : ℝ | rhinLiteFactor5 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor5; fun_prop)
  have hopen6 : IsOpen {y : ℝ | rhinLiteFactor6 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor6; fun_prop)
  have hlocal : IsLocalMax rhinLiteLogSq m := by
    filter_upwards [isOpen_Ioo.mem_nhds hmopen, hopen1.mem_nhds h1, hopen2.mem_nhds h2,
      hopen3.mem_nhds h3, hopen4.mem_nhds h4, hopen5.mem_nhds h5, hopen6.mem_nhds h6]
      with y hyI hy1 hy2 hy3 hy4 hy5 hy6
    have hypos : 0 < y := lt_trans (by norm_num) hyI.1
    have hycc : y ∈ Icc (2 : ℝ) 4 := ⟨hyI.1.le, hyI.2.le⟩
    apply Real.exp_le_exp.mp
    rw [exp_rhinLiteLogSq y hypos hy1 hy2 hy3 hy4 hy5 hy6,
      exp_rhinLiteLogSq m (lt_trans (by norm_num) hmopen.1) h1 h2 h3 h4 h5 h6]
    exact hmax hycc
  have hderiv : deriv rhinLiteLogSq m = 0 := hlocal.deriv_eq_zero
  have hformula := hasDerivAt_rhinLiteLogSq m hm0 h1 h2 h3 h4 h5 h6
  rw [hformula.deriv] at hderiv
  have hroot : rhinLiteCriticalReal.eval m = 0 :=
    rhinLiteCriticalReal_eval_eq_zero_of_logDeriv_eq_zero m hm0 h1 h2 h3 h4 h5 h6 hderiv
  obtain ⟨i, hmi⟩ := rhinLiteCriticalRoot_exhaustive_positive hm hroot
  have hmBound := rhinLiteKernelAbs_div_pow_le i hmi
  have hmpos' : 0 < m := lt_trans (by norm_num) hmopen.1
  have habsm : |rhinLiteKernel m| ≤ (9 / 40 : ℝ) ^ rhinLiteScale := by
    rw [abs_rhinLiteKernel_eq m hmpos']
    exact hmBound
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hsquares : |rhinLiteKernel x| ^ 2 ≤ |rhinLiteKernel m| ^ 2 := by
    simpa [rhinLiteKernelSq, sq_abs] using hmax hx
  rw [← abs_rhinLiteKernel_eq x hxpos]
  have htarget : 0 ≤ (9 / 40 : ℝ) ^ rhinLiteScale := pow_nonneg (by norm_num) _
  nlinarith [abs_nonneg (rhinLiteKernel x), abs_nonneg (rhinLiteKernel m),
    sq_nonneg (|rhinLiteKernel x| + |rhinLiteKernel m|)]

/-- Any critical bracket meeting `(3,4)` lies at `rootLeft ≥ 3`.  (Brackets 1–4 have
`rootRight < 3`; brackets 5–7 have `rootLeft ≥ 3.47`.)  Finite check. -/
theorem rhinLiteRootLeft_ge_three (i : Fin 7)
    (h : (3 : ℚ) < rhinLiteRootRight i.succ) : (3 : ℚ) ≤ rhinLiteRootLeft i.succ := by
  revert h; native_decide +revert

set_option maxRecDepth 100000 in
/-- **Tight `[3,4]` base-block estimate.**  On `[3,4]` the normalized kernel is bounded by the
strictly smaller `(2209/10000)^{scale}` — the `[3,4]` peak is `exp(2.7)` below it.  Same
compact-maximum/critical-bracket bridge as the global estimate, but the maximiser lands in a `[3,4]`
bracket (`rootLeft ≥ 3`), where the tight per-bracket certificate applies.  This is the isolated
interval-arithmetic node feeding the `I₂` per-step upper bound `rhinLiteI₂_peak_upper`. -/
theorem rhinLiteKernelAbs_div_pow_le_on_Icc34 {x : ℝ} (hx : x ∈ Icc (3 : ℝ) 4) :
    rhinLiteKernelAbs x / x ^ rhinLiteScale ≤ (2205 / 10000 : ℝ) ^ rhinLiteScale := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (3 : ℝ) 4).Nonempty)
    (rhinLiteKernelSq_continuousOn.mono (Icc_subset_Icc (by norm_num) le_rfl))
  have hm24 : m ∈ Icc (2 : ℝ) 4 := ⟨by linarith [hm.1], hm.2⟩
  have hhalfmem : (7 / 2 : ℝ) ∈ Icc (3 : ℝ) 4 := by norm_num
  have hmpos : 0 < rhinLiteKernelSq m :=
    lt_of_lt_of_le rhinLiteKernelSq_seven_halves_pos (hmax hhalfmem)
  have hkne : rhinLiteKernel m ≠ 0 := (sq_pos_iff.mp hmpos)
  have hm0 : m ≠ 0 := by linarith [hm.1]
  have h1 : rhinLiteFactor1 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW1]
  have h2 : rhinLiteFactor2 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW2]
  have h3 : rhinLiteFactor3 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW3]
  have h4 : rhinLiteFactor4 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW4]
  have h5 : rhinLiteFactor5 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW5]
  have h6 : rhinLiteFactor6 m ≠ 0 := by intro h; apply hkne; simp [rhinLiteKernel, h, rhinLiteW6]
  have hmne3 : m ≠ 3 := by
    intro h; subst m; rw [rhinLiteKernelSq_three] at hmpos; linarith
  have hmne4 : m ≠ 4 := by
    intro h; subst m; rw [rhinLiteKernelSq_four] at hmpos; linarith
  have hmopen : m ∈ Ioo (3 : ℝ) 4 := ⟨lt_of_le_of_ne hm.1 (Ne.symm hmne3),
    lt_of_le_of_ne hm.2 hmne4⟩
  have hopen1 : IsOpen {y : ℝ | rhinLiteFactor1 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor1; fun_prop)
  have hopen2 : IsOpen {y : ℝ | rhinLiteFactor2 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor2; fun_prop)
  have hopen3 : IsOpen {y : ℝ | rhinLiteFactor3 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor3; fun_prop)
  have hopen4 : IsOpen {y : ℝ | rhinLiteFactor4 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor4; fun_prop)
  have hopen5 : IsOpen {y : ℝ | rhinLiteFactor5 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor5; fun_prop)
  have hopen6 : IsOpen {y : ℝ | rhinLiteFactor6 y ≠ 0} :=
    isOpen_ne.preimage (by unfold rhinLiteFactor6; fun_prop)
  have hlocal : IsLocalMax rhinLiteLogSq m := by
    filter_upwards [isOpen_Ioo.mem_nhds hmopen, hopen1.mem_nhds h1, hopen2.mem_nhds h2,
      hopen3.mem_nhds h3, hopen4.mem_nhds h4, hopen5.mem_nhds h5, hopen6.mem_nhds h6]
      with y hyI hy1 hy2 hy3 hy4 hy5 hy6
    have hypos : 0 < y := lt_trans (by norm_num) hyI.1
    have hycc : y ∈ Icc (3 : ℝ) 4 := ⟨hyI.1.le, hyI.2.le⟩
    apply Real.exp_le_exp.mp
    rw [exp_rhinLiteLogSq y hypos hy1 hy2 hy3 hy4 hy5 hy6,
      exp_rhinLiteLogSq m (lt_trans (by norm_num) hmopen.1) h1 h2 h3 h4 h5 h6]
    exact hmax hycc
  have hderiv : deriv rhinLiteLogSq m = 0 := hlocal.deriv_eq_zero
  have hformula := hasDerivAt_rhinLiteLogSq m hm0 h1 h2 h3 h4 h5 h6
  rw [hformula.deriv] at hderiv
  have hroot : rhinLiteCriticalReal.eval m = 0 :=
    rhinLiteCriticalReal_eval_eq_zero_of_logDeriv_eq_zero m hm0 h1 h2 h3 h4 h5 h6 hderiv
  obtain ⟨i, hmi⟩ := rhinLiteCriticalRoot_exhaustive_positive hm24 hroot
  have hRR : (3 : ℚ) < rhinLiteRootRight i.succ := by
    have : (3 : ℝ) < (rhinLiteRootRight i.succ : ℝ) := lt_of_lt_of_le hmopen.1 hmi.2
    exact_mod_cast this
  have hi3 : (3 : ℚ) ≤ rhinLiteRootLeft i.succ := rhinLiteRootLeft_ge_three i hRR
  have hmBound := rhinLiteKernelAbs_div_pow_le_tight i hi3 hmi
  have hmpos' : 0 < m := lt_trans (by norm_num) hmopen.1
  have habsm : |rhinLiteKernel m| ≤ (2205 / 10000 : ℝ) ^ rhinLiteScale := by
    rw [abs_rhinLiteKernel_eq m hmpos']
    exact hmBound
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hsquares : |rhinLiteKernel x| ^ 2 ≤ |rhinLiteKernel m| ^ 2 := by
    simpa [rhinLiteKernelSq, sq_abs] using hmax hx
  rw [← abs_rhinLiteKernel_eq x hxpos]
  have htarget : 0 ≤ (2205 / 10000 : ℝ) ^ rhinLiteScale := pow_nonneg (by norm_num) _
  nlinarith [abs_nonneg (rhinLiteKernel x), abs_nonneg (rhinLiteKernel m),
    sq_nonneg (|rhinLiteKernel x| + |rhinLiteKernel m|)]

end CollatzMoonshot.FrontA
