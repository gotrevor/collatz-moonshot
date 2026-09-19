import CollatzMoonshot.FrontA.FirstCrossing

/-!
# Local residue transport across an adjacent letter swap

Bounded helper lap (attended override 2026-09-18 late).  Three results, all about
the *local* effect of swapping an adjacent `10` block for `01` inside a parity word:

* `numer_adjacent_swap` — the exact numerator gap created by one adjacent swap;
* `residue_adjacent_swap` — the induced congruence between the two starting values,
  suffix-independent and needing no first-crossing hypothesis;
* `numeratorAntitoneResidue_false` — the numerator does **not** order first-crossing
  starts antitonely, refuted by `x = 95`, `y = 175`, `m = 8`.

Nothing here proves the coefficient stopping-time conjecture; it is local transport.
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- **Adjacent-swap numerator law.**  Replacing the block `10` by `01` at position
`|u|` raises the numerator by exactly `2 ^ |u| · 3 ^ ones w`.  Both blocks carry one
odd step, so the suffix weight `3 ^ ones` of the tail is unchanged and only the
internal placement of the single one moves. -/
theorem numer_adjacent_swap (u w : List Bool) :
    numer (u ++ [false, true] ++ w) =
      numer (u ++ [true, false] ++ w) + 2 ^ u.length * 3 ^ ones w := by
  have hs1 : numer ([false, true] ++ w) = 4 * numer w + 2 * 3 ^ ones w := by
    simp [numer]; ring
  have hs2 : numer ([true, false] ++ w) = 4 * numer w + 3 ^ ones w := by
    simp [numer, ones]; ring
  have ho1 : ones ([false, true] ++ w) = ones w + 1 := by simp [ones]
  have ho2 : ones ([true, false] ++ w) = ones w + 1 := by simp [ones]
  rw [List.append_assoc u [false, true] w, List.append_assoc u [true, false] w,
    numer_append u ([false, true] ++ w), numer_append u ([true, false] ++ w),
    hs1, hs2, ho1, ho2]
  ring

/-- **Local residue transport.**  If two starts have length-`m` traces differing by a
single adjacent `10 ↦ 01` swap at position `|u|`, their values are tied modulo `2 ^ m`
by an affine relation depending only on the *prefix* `u` — the suffix `w` cancels.

Proof: subtract the two iterate identities mod `2 ^ m`, insert the numerator swap law,
and cancel the unit `3 ^ ones w`. -/
theorem residue_adjacent_swap {x y m : ℕ} (u w : List Bool)
    (hx : traceWord x m = u ++ [true, false] ++ w)
    (hy : traceWord y m = u ++ [false, true] ++ w) :
    3 ^ (ones u + 1) * y + 2 ^ u.length ≡ 3 ^ (ones u + 1) * x [MOD 2 ^ m] := by
  set N := numer (u ++ [true, false] ++ w) with hN
  have hoX : ones (u ++ [true, false] ++ w) = (ones u + 1) + ones w := by
    simp [ones_append, ones]; omega
  have hoY : ones (u ++ [false, true] ++ w) = (ones u + 1) + ones w := by
    simp [ones_append, ones]; omega
  -- The two iterate identities, read as congruences mod `2 ^ m`.
  have hA : 3 ^ ((ones u + 1) + ones w) * x + N ≡ 0 [MOD 2 ^ m] := by
    rw [hN, ← hoX, ← hx, ← tstep_iterate_identity m x]
    exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
  have hB : (3 ^ ((ones u + 1) + ones w) * y + 2 ^ u.length * 3 ^ ones w) + N ≡ 0
      [MOD 2 ^ m] := by
    have h0 : 3 ^ ones (traceWord y m) * y + numer (traceWord y m) ≡ 0 [MOD 2 ^ m] := by
      rw [← tstep_iterate_identity m y]
      exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
    rw [hy, hoY, numer_adjacent_swap u w, ← hN] at h0
    calc (3 ^ ((ones u + 1) + ones w) * y + 2 ^ u.length * 3 ^ ones w) + N
        = 3 ^ ((ones u + 1) + ones w) * y + (N + 2 ^ u.length * 3 ^ ones w) := by ring
      _ ≡ 0 [MOD 2 ^ m] := h0
  -- Cancel the common numerator, then the unit `3 ^ ones w`.
  have hcancel : 3 ^ ((ones u + 1) + ones w) * y + 2 ^ u.length * 3 ^ ones w ≡
      3 ^ ((ones u + 1) + ones w) * x [MOD 2 ^ m] :=
    Nat.ModEq.add_right_cancel' N (hB.trans hA.symm)
  have hfac : 3 ^ ones w * (3 ^ (ones u + 1) * y + 2 ^ u.length) ≡
      3 ^ ones w * (3 ^ (ones u + 1) * x) [MOD 2 ^ m] := by
    have e1 : 3 ^ ones w * (3 ^ (ones u + 1) * y + 2 ^ u.length)
        = 3 ^ ((ones u + 1) + ones w) * y + 2 ^ u.length * 3 ^ ones w := by
      rw [pow_add]; ring
    have e2 : 3 ^ ones w * (3 ^ (ones u + 1) * x)
        = 3 ^ ((ones u + 1) + ones w) * x := by rw [pow_add]; ring
    rw [e1, e2]; exact hcancel
  have hcop : Nat.Coprime (3 ^ ones w) (2 ^ m) := Nat.Coprime.pow _ _ (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hfac

/-- Would the first-crossing numerator order the starting values antitonely? -/
def NumeratorAntitoneResidue : Prop :=
  ∀ x y m : ℕ, 2 ≤ x → 2 ≤ y → x < 2 ^ m → y < 2 ^ m →
    At x m → At y m →
    numer (traceWord x m) ≤ numer (traceWord y m) → y ≤ x

/-- **No numerator antitonicity.**  `x = 95` and `y = 175` both first-cross at `m = 8`
with traces `11111000` and `11110100` — one adjacent swap apart — and numerators
`211 < 227`; yet `175 > 95`.  This refutes the proposed antitone ordering of
the starts; the swap law above itself gives a congruence, not an inequality. -/
theorem numeratorAntitoneResidue_false : ¬ NumeratorAntitoneResidue := by
  intro h
  have := h 95 175 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold At; decide) (by unfold At; decide) (by decide)
  omega

end CollatzMoonshot.FrontA.FirstCrossing
