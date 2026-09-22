import CollatzMoonshot.FrontA.FirstCrossingOneRun
import CollatzMoonshot.FrontB.Powers

/-! # First crossing: two exact facts the 2026-09-22 mechanism search leans on

* **Primitivity.**  A first-crossing word is never a proper power `u^j`, `j ≥ 2`: the
  prefix `u` is supercritical (`2^|u| ≤ 3^ones u`), so `2^m = (2^|u|)^j ≤ 3^(j·ones u) = 3^ones v`
  against the crossing.  Repetition of a word can therefore never produce a first-crossing
  survivor; the many-run survivors of the sibling map `5n+1` (start 5 entering the 13-cycle
  from below) are *eventually* periodic words `1·(1110000)^39`, not powers.

* **The overshoot is a residue.**  For a survivor, `overshoot_identity` reads
  `D·n + 2^m·E = numer v` with `D = 2^m − 3^K`; since `2^m ≡ 3^K (mod D)`,
  `3^K·E ≡ numer v (mod D)`.  Together with `3E < K` (`three_mul_overshoot_lt`) this says
  a stopping-time failure is exactly "`numer v · 3^{−K} mod D` lands in `[0, K/3)` with a
  quotient `≥ 2`", the single congruence every run-to-run admission equation reduces to.

No stopping-time or crossing-existence assumption is used. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- A first-crossing word is primitive. -/
theorem at_primitive {n m : ℕ} (h : At n m) : Primitive (traceWord n m) := by
  have hm : 0 < m := h.1
  refine ⟨?_, ?_⟩
  · intro hnil
    have hl := congrArg List.length hnil
    simp at hl
    omega
  · intro u j hj hv
    have hlen : m = j * u.length := by
      have := congrArg List.length hv
      simpa using this
    have hu : 0 < u.length := by
      rcases Nat.eq_zero_or_pos u.length with h0 | h0
      · rw [h0, mul_zero] at hlen
        omega
      · exact h0
    have hlt : u.length < m := by
      rw [hlen]
      nlinarith
    have hpre : traceWord n u.length = u := by
      rw [← take_traceWord n m u.length hlt.le, hv]
      rcases j with _ | j
      · omega
      · rw [wpow_succ, List.take_append_of_le_length le_rfl, List.take_length]
    have hsup : 2 ^ u.length ≤ 3 ^ ones u := by
      have := h.2.1 u.length hlt
      rwa [hpre] at this
    have hpow : 2 ^ m ≤ 3 ^ ones (traceWord n m) := by
      rw [hv, ones_wpow, hlen, pow_mul', pow_mul']
      exact Nat.pow_le_pow_left hsup j
    exact absurd h.2.2 (not_lt.mpr hpow)

/-- **The overshoot is the residue of the numerator.**  For a survivor of its first crossing,
`3^K · E ≡ numer v (mod 2^m − 3^K)` where `E = tstep^[m] n − n`. -/
theorem overshoot_modEq {n m : ℕ} (h : At n m) (hsurv : n ≤ tstep^[m] n) :
    3 ^ ones (traceWord n m) * (tstep^[m] n - n) ≡ numer (traceWord n m)
      [MOD 2 ^ m - 3 ^ ones (traceWord n m)] := by
  have hid := overshoot_identity h hsurv
  have hD : 3 ^ ones (traceWord n m) < 2 ^ m := h.2.2
  have key : 2 ^ m * (tstep^[m] n - n) =
      (2 ^ m - 3 ^ ones (traceWord n m)) * (tstep^[m] n - n) +
        3 ^ ones (traceWord n m) * (tstep^[m] n - n) := by
    rw [← add_mul, Nat.sub_add_cancel hD.le]
  have hN : numer (traceWord n m) =
      3 ^ ones (traceWord n m) * (tstep^[m] n - n) +
        (2 ^ m - 3 ^ ones (traceWord n m)) * (n + (tstep^[m] n - n)) := by
    rw [← hid, key]
    ring
  unfold Nat.ModEq
  rw [hN, Nat.add_mul_mod_self_left]

end CollatzMoonshot.FrontA.FirstCrossing
