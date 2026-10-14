/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReversal

/-!
# A Gaussian relative of the amusical permutation with infinitely many orbits

Found by the 2026-10-13 "relative" research agent; checked independently
(`scripts/amusical/gauss_check.py`: integral, injective and reversible on `|a|, |b| ≤ 60`, and a
perturbed constant fails).  Write `z = a + bi ∈ ℤ[i]` as a pair, `π = 2 + i`, `π̄ = 2 − i`.

* on `a + 2b ≡ 0 (mod 5)` (`z ≡ 0 mod π̄`):  `H z = 1 + π² z / π̄ = 1 + (2 + 11i) z / 5`;
* on `a + 7b ≡ 1 (mod 25)` (`z ≡ 1 mod π̄²`): `H z = π (z − 1) / π̄² = (2 + 11i)(z − 1) / 25`;
* on the other 19 classes `ρ mod π̄²`: `H z = (π² z + y_ρ i)/π̄² = ((−7 + 24i) z + y_ρ(−4 + 3i))/25`,
  `y_ρ ≡ 17ρ (mod 25)`, `|y_ρ| ≤ 12`.

Like `U` it multiplies by one prime of a split pair and divides by the other on every piece
(`π` and `π̄` here, `3` and `2` for `U`), so it is wild, has no residue-class cycles and finitely
many cycles of each length; its symbolic coding is a two-sided full shift (on `ℤ_π̄ × ℤ_π`), so
no residue-class union is a growth cone.  Unlike `U`, it is reversible:
`conj ∘ H ∘ conj = H⁻¹`, and `Fix(conj) = ℤ` is infinite, so `H` has infinitely many orbits
(`reversing_zpow_fixed`).  Theorem NR (`no_piecewiseAffine_reversor`) shows `U` admits no such
reversor: in rank one the unbalance sits on the non-swappable primes `2, 3`.

Both targets kernel-checked 2026-10-13 by the gauss treadmill (`HANDOFF-amusical-gauss.md`).
-/

namespace CollatzMoonshot.GaussianRelative

/-- The offset `y_ρ ≡ 17ρ (mod 25)` with `|y_ρ| ≤ 12`. -/
def yOf (r : ℤ) : ℤ := if 17 * r % 25 > 12 then 17 * r % 25 - 25 else 17 * r % 25

/-- The Gaussian relative `H` on `ℤ[i] ≅ ℤ × ℤ`. -/
def gaussH (z : ℤ × ℤ) : ℤ × ℤ :=
  if (z.1 + 2 * z.2) % 5 = 0 then
    (1 + (2 * z.1 - 11 * z.2) / 5, (11 * z.1 + 2 * z.2) / 5)
  else if (z.1 + 7 * z.2) % 25 = 1 then
    ((2 * (z.1 - 1) - 11 * z.2) / 25, (11 * (z.1 - 1) + 2 * z.2) / 25)
  else
    ((-7 * z.1 - 24 * z.2 - 4 * yOf ((z.1 + 7 * z.2) % 25)) / 25,
      (24 * z.1 - 7 * z.2 + 3 * yOf ((z.1 + 7 * z.2) % 25)) / 25)

/-- Complex conjugation on `ℤ × ℤ`. -/
def conj (z : ℤ × ℤ) : ℤ × ℤ := (z.1, -z.2)

set_option maxHeartbeats 2000000 in
/-- **Proved.**  `conj ∘ H ∘ conj ∘ H = id`, i.e. `conj ∘ H ∘ conj = H⁻¹` once `H` is a bijection. -/
theorem conj_gaussH_conj_gaussH (z : ℤ × ℤ) : conj (gaussH (conj (gaussH z))) = z := by
  rcases z with ⟨a, b⟩
  generalize hr : (a + 7 * b) % 25 = r
  have hr0 : 0 ≤ r := by rw [← hr]; omega
  have hr25 : r < 25 := by rw [← hr]; omega
  interval_cases r <;>
    simp only [conj, gaussH, yOf, hr] <;>
    split_ifs <;> norm_num at * <;> omega

/-- `H` is a bijection, with inverse `conj ∘ H ∘ conj`. -/
def gaussPerm : Equiv.Perm (ℤ × ℤ) where
  toFun := gaussH
  invFun := fun z => conj (gaussH (conj z))
  left_inv := conj_gaussH_conj_gaussH
  right_inv := fun z => by
    have h := conj_gaussH_conj_gaussH (conj z)
    have hc : ∀ w, conj (conj w) = w := fun w => by simp [conj]
    -- apply `conj` to `conj (H (conj (H (conj z)))) = conj z`
    have := congrArg conj h
    rw [hc, hc] at this
    exact this

/-- Conjugation as a permutation. -/
def conjPerm : Equiv.Perm (ℤ × ℤ) where
  toFun := conj
  invFun := conj
  left_inv := fun w => by simp [conj]
  right_inv := fun w => by simp [conj]

/-- A nonzero return time makes the full integer-power orbit finite. -/
private theorem zpow_orbit_finite_of_period {α : Type*} (σ : Equiv.Perm α) (x : α) {p : ℤ}
    (hp : p ≠ 0) (hperiod : (σ ^ p) x = x) :
    (Set.range fun k : ℤ => (σ ^ k) x).Finite := by
  let f : ℤ → α := fun k => (σ ^ k) x
  have hf : Function.Periodic f p := fun k => by
    dsimp [f]
    rw [zpow_add, Equiv.Perm.mul_apply, hperiod]
  rw [← hf.image_uIcc hp 0]
  exact Set.Finite.image _ (Set.finite_uIcc (0 : ℤ) (0 + p))

/-- **Proved.**  `H` has infinitely many orbits: each meets the real axis `Fix(conj) = ℤ × {0}`
in at most two points (`orbit_inter_fixedPoints_ncard_le_two`). -/
theorem gauss_infinitely_many_orbits :
    {O : Set (ℤ × ℤ) | ∃ z, O = Set.range fun k : ℤ => (gaussPerm ^ k) z}.Infinite := by
  let orbit (z : ℤ × ℤ) : Set (ℤ × ℤ) := Set.range fun k : ℤ => (gaussPerm ^ k) z
  let orbits : Set (Set (ℤ × ℤ)) := {O | ∃ z, O = orbit z}
  change orbits.Infinite
  by_contra hnot
  have horbits : orbits.Finite := by
    by_contra hfinite
    exact hnot hfinite
  let orbitOf (n : ℤ) : orbits := ⟨orbit (n, 0), ⟨(n, 0), rfl⟩⟩
  letI : Finite orbits := horbits
  obtain ⟨O, hfiber⟩ := Finite.exists_infinite_fiber orbitOf
  letI : Infinite (orbitOf ⁻¹' {O}) := hfiber
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩, hnm'⟩ := exists_pair_ne (orbitOf ⁻¹' {O})
  have hnm : n ≠ m := fun h => hnm' (Subtype.ext h)
  have hnO : orbitOf n = O := by simpa using hn
  have hmO : orbitOf m = O := by simpa using hm
  have horbit_eq : orbit (m, 0) = orbit (n, 0) := by
    exact congrArg Subtype.val (hmO.trans hnO.symm)
  have hm_mem : (m, 0) ∈ orbit (n, 0) := by
    rw [← horbit_eq]
    exact ⟨0, by simp⟩
  obtain ⟨k, hk⟩ := hm_mem
  change (gaussPerm ^ k) (n, 0) = (m, 0) at hk
  have hk0 : k ≠ 0 := by
    intro hzero
    subst k
    simp only [zpow_zero, Equiv.Perm.one_apply] at hk
    exact hnm (Prod.mk.inj hk).1
  have hι : conjPerm * conjPerm = 1 := by
    apply Equiv.ext
    intro z
    rcases z with ⟨a, b⟩
    simp [conjPerm, conj]
  have hrev : conjPerm * gaussPerm * conjPerm = gaussPerm⁻¹ := by
    apply Equiv.ext
    intro z
    rfl
  have hperiod : (gaussPerm ^ (2 * k)) (n, 0) = (n, 0) := by
    apply CollatzMoonshot.Amusical.reversing_zpow_fixed hι hrev
    · simp [conjPerm, conj]
    · rw [hk]
      simp [conjPerm, conj]
  have horbit_finite : (orbit (n, 0)).Finite := by
    exact zpow_orbit_finite_of_period gaussPerm (n, 0) (mul_ne_zero (by norm_num) hk0) hperiod
  have hfiber_set : (orbitOf ⁻¹' {O}).Infinite := Set.infinite_coe_iff.mp hfiber
  have himage_infinite : ((fun q : ℤ => (q, (0 : ℤ))) '' (orbitOf ⁻¹' {O})).Infinite :=
    hfiber_set.image (fun _ _ _ _ h => (Prod.mk.inj h).1)
  have himage_subset : (fun q : ℤ => (q, (0 : ℤ))) '' (orbitOf ⁻¹' {O}) ⊆ orbit (n, 0) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqO : orbitOf q = O := by simpa using hq
    have hqeq : orbit (q, 0) = orbit (n, 0) :=
      congrArg Subtype.val (hqO.trans hnO.symm)
    rw [← hqeq]
    exact ⟨0, by simp⟩
  exact (himage_infinite.mono himage_subset) horbit_finite

end CollatzMoonshot.GaussianRelative
