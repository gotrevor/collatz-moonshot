/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalStaircase

/-!
# Powers of `3`: staircases in one window separate orbits (Theorem P3)

The 2026-10-14 "lfsep" agent's Theorem P3 and Corollary P3′ (research §30).  Fix `y > 0` prime to
`6` and put `X = 2^L y`.  For `s < L` the orbit of `3^s y` contains the ratio-`3/2` staircase
`2^(s−b) 3^b y`, `0 ≤ b ≤ s` (`amusical_iterate_staircase`).  Its lowest point divisible by `3`
(`b = 1`) is `3 · 2^(s−1) y ≤ 3X/4`.  If the whole forward orbit of `3^s y` stays at or above
`3X/2`, the staircase has a point `n_s ∈ 3ℤ ∩ [X, 3X/2)`, which is a forward survivor by Lemma St
(`staircase_fwdSurvivor`).

**`powers_orbit_ne` (P3).**  Two such `s ≠ s'` lie on distinct orbits: `n_s ≠ n_s'` by unique
factorization (`y` prime to `6`), and Sep3 (`fwdSurvivor_three_not_mem_orbit`) separates forward
survivors divisible by `3` in one window.  Each such orbit is infinite
(`powers_not_periodic`, from `fwdSurvivor_three_not_periodic`).

**`infinitelyManyOrbits_of_powers` (P3, counting form).**  If for every `r` some `L` has more than
`r` such exponents, `U` has infinitely many orbits on `ℕ`.

**`infinitelyManyOrbits_of_powers_log` (P3′).**  With `η = 1/k`: if the exponents `s ≤ S` whose
orbit never returns below `3 · 2^(s + s/k + 1) y / 2` are not `O(log S)`, `U` has infinitely many
orbits.  Paper proof: cover `[1, S]` by `O(k log S)` blocks `[L_j, L_{j+1})` with
`L_{j+1} = L_j + L_j / (k + 1) + 1`; every exponent of a block is admissible for `L = L_{j+1}`, so
each block holds at most `r` of them.

This is a reduction, not progress on the count: one admissible `s` already exhibits an infinite
orbit, which is Conway's open question (§30).  Measured for `y = 1`, `s ≤ 3000`, `η = 0.01`: only
`s = 4, 5, 6, 7, 10` fail.
-/

namespace CollatzMoonshot.Amusical

/-- `s` is admissible for the window `[2^L y, 3 · 2^L y / 2)`: `s < L` and the forward orbit of
`3^s y` never drops below `3 · 2^L y / 2`. -/
def PowerAdmissible (y : ℤ) (L s : ℕ) : Prop :=
  s < L ∧ ∀ t : ℕ, 3 * (2 ^ L * y) ≤ 2 * amusical^[t] (3 ^ s * y)

/-- **Target.**  An admissible staircase has a point divisible by `3` in `[2^L y, 3 · 2^L y / 2)`
(`1 ≤ b ≤ s`; such a point is a forward survivor by `staircase_fwdSurvivor`). -/
theorem powerAdmissible_window_point {y : ℤ} (hy : 0 < y) {L s : ℕ}
    (h : PowerAdmissible y L s) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ s ∧ 2 ^ L * y ≤ 2 ^ (s - b) * 3 ^ b * y ∧
      2 * (2 ^ (s - b) * 3 ^ b * y) < 3 * (2 ^ L * y) := by
  classical
  obtain ⟨hsL, hall⟩ := h
  have h0 := hall 0
  rw [Function.iterate_zero, id] at h0
  have hXpos : (0 : ℤ) < 2 ^ L * y := by positivity
  have hP : ∃ b, b ≤ s ∧ 2 ^ L * y ≤ 2 ^ (s - b) * 3 ^ b * y :=
    ⟨s, le_rfl, by rw [Nat.sub_self, pow_zero, one_mul]; linarith⟩
  have hspec := Nat.find_spec hP
  have hmin : ∀ c < Nat.find hP, ¬ (c ≤ s ∧ 2 ^ L * y ≤ 2 ^ (s - c) * 3 ^ c * y) :=
    fun c hc => Nat.find_min hP hc
  obtain ⟨hbs, hXb⟩ := hspec
  have h2L1 : (2 : ℤ) ^ (s + 1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hsL
  obtain ⟨c, hc⟩ : ∃ c, Nat.find hP = c + 2 := by
    rcases hb : Nat.find hP with _ | _ | c
    · rw [hb, Nat.sub_zero, pow_zero, mul_one] at hXb
      have h2s : (0 : ℤ) < 2 ^ s * y := by positivity
      rw [pow_succ] at h2L1
      nlinarith
    · rw [hb] at hXb hbs
      obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
      rw [show a + 1 - (0 + 1) = a by omega, pow_one] at hXb
      have : (0 : ℤ) < 2 ^ a * y := by positivity
      rw [pow_succ, pow_succ] at h2L1
      nlinarith
    · exact ⟨c, rfl⟩
  rw [hc] at hbs hXb hmin
  have hlt := hmin (c + 1) (by omega)
  obtain ⟨a, rfl⟩ : ∃ a, s = a + (c + 2) := ⟨s - (c + 2), by omega⟩
  refine ⟨c + 2, by omega, hbs, hXb, ?_⟩
  rw [show a + (c + 2) - (c + 1) = a + 1 by omega] at hlt
  rw [show a + (c + 2) - (c + 2) = a by omega]
  have hlt' : 2 ^ (a + 1) * 3 ^ (c + 1) * y < 2 ^ L * y := by
    by_contra hge; exact hlt ⟨by omega, not_lt.mp hge⟩
  have : 2 * (2 ^ a * 3 ^ (c + 2) * y) = 3 * (2 ^ (a + 1) * 3 ^ (c + 1) * y) := by ring
  linarith

/-- `2^a 3^b` determines `a` and `b`. -/
theorem two_pow_mul_three_pow_inj {a b a' b' : ℕ} (h : 2 ^ a * 3 ^ b = 2 ^ a' * 3 ^ b') :
    a = a' ∧ b = b' := by
  have h2 := congrArg (fun m => m.factorization 2) h
  have h3 := congrArg (fun m => m.factorization 3) h
  have h32 : (Nat.factorization 3) 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have h23 : (Nat.factorization 2) 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_two.factorization_self,
    Nat.prime_three.factorization_self, h32, h23] at h2 h3
  exact ⟨h2, h3⟩

/-- The staircase point `2^(s−b) 3^b y` of `powerAdmissible_window_point` is a positive forward
survivor divisible by `3`, `s − b` steps below `3^s y`. -/
theorem powerAdmissible_survivor {y : ℤ} (hy : 0 < y) {L s : ℕ} (h : PowerAdmissible y L s) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ s ∧ 2 ^ L * y ≤ 2 ^ (s - b) * 3 ^ b * y ∧
      2 * (2 ^ (s - b) * 3 ^ b * y) < 3 * (2 ^ L * y) ∧ FwdSurvivor (2 ^ (s - b) * 3 ^ b * y) ∧
      3 ∣ 2 ^ (s - b) * 3 ^ b * y ∧ amusical^[s - b] (2 ^ (s - b) * 3 ^ b * y) = 3 ^ s * y := by
  obtain ⟨b, hb1, hbs, hlo, hhi⟩ := powerAdmissible_window_point hy h
  refine ⟨b, hb1, hbs, hlo, hhi, ?_, ?_, ?_⟩
  · apply staircase_fwdSurvivor hy
    intro t
    have := h.2 t
    rw [show s - b + b = s by omega]
    linarith
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    exact ⟨2 ^ (s - (c + 1)) * 3 ^ c * y, by ring⟩
  · rw [amusical_iterate_staircase y _ _ _ le_rfl, Nat.sub_self, pow_zero, one_mul,
      show b + (s - b) = s by omega]

theorem amusical_iterate_mem_amusicalOrbit (t : ℕ) (x : ℤ) : amusical^[t] x ∈ amusicalOrbit x :=
  ⟨t, amusicalPerm_pow_nat_apply t x⟩

/-- **Target (P3).**  Distinct admissible exponents give distinct orbits. -/
theorem powers_orbit_ne {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y) (hy3 : ¬ 3 ∣ y) {L s s' : ℕ}
    (hs : PowerAdmissible y L s) (hs' : PowerAdmissible y L s') (hne : s ≠ s') :
    3 ^ s' * y ∉ amusicalOrbit (3 ^ s * y) := by
  intro hmem
  obtain ⟨b, hb1, hbs, hlo, hhi, hfs, h3, hit⟩ := powerAdmissible_survivor hy hs
  obtain ⟨b', hb1', hbs', hlo', hhi', hfs', h3', hit'⟩ := powerAdmissible_survivor hy hs'
  set n := 2 ^ (s - b) * 3 ^ b * y with hn
  set n' := 2 ^ (s' - b') * 3 ^ b' * y with hn'
  have hO : amusicalOrbit (3 ^ s * y) = amusicalOrbit n :=
    amusicalOrbit_eq_of_mem (hit ▸ amusical_iterate_mem_amusicalOrbit _ n)
  have hO' : amusicalOrbit (3 ^ s' * y) = amusicalOrbit n' :=
    amusicalOrbit_eq_of_mem (hit' ▸ amusical_iterate_mem_amusicalOrbit _ n')
  have hsame : amusicalOrbit n' = amusicalOrbit n := by
    rw [← hO, ← hO', amusicalOrbit_eq_of_mem hmem]
  have hnn : n ≠ n' := by
    intro heq
    have hy0 : y ≠ 0 := hy.ne'
    have : ((2 ^ (s - b) * 3 ^ b : ℕ) : ℤ) = ((2 ^ (s' - b') * 3 ^ b' : ℕ) : ℤ) := by
      push_cast; exact mul_right_cancel₀ hy0 heq
    obtain ⟨h1, h2⟩ := two_pow_mul_three_pow_inj (Int.ofNat_inj.mp this)
    omega
  rcases lt_or_gt_of_ne hnn with hlt | hlt
  · exact fwdSurvivor_three_not_mem_orbit hfs hfs' hlo hlt hhi' h3'
      (hsame ▸ mem_amusicalOrbit_self n')
  · exact fwdSurvivor_three_not_mem_orbit hfs' hfs hlo' hlt hhi h3
      (hsame.symm ▸ mem_amusicalOrbit_self n)

/-- **Target.**  An admissible power lies on an infinite orbit. -/
theorem powers_not_periodic {y : ℤ} (hy : 0 < y) {L s : ℕ} (hs : PowerAdmissible y L s) :
    3 ^ s * y ∉ Function.periodicPts amusical := by
  rintro ⟨p, hp, hper⟩
  obtain ⟨b, hb1, hbs, hlo, hhi, hfs, h3, hit⟩ := powerAdmissible_survivor hy hs
  refine fwdSurvivor_three_not_periodic hfs h3 (by positivity) ⟨p, hp, ?_⟩
  apply (amusical_injective.iterate (s - b))
  show amusical^[s - b] (amusical^[p] _) = _
  rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hit]
  exact hper.eq

/-- **Target (P3, counting form).**  Unboundedly many admissible exponents for single windows
imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_powers {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y) (hy3 : ¬ 3 ∣ y)
    (h : ∀ r : ℕ, ∃ L : ℕ, ∃ T : Finset ℕ, r < T.card ∧ ∀ s ∈ T, PowerAdmissible y L s) :
    AmusicalInfinitelyManyOrbits := by
  intro hfin
  obtain ⟨L, T, hcard, hT⟩ := h hfin.toFinset.card
  have hmaps : ∀ s ∈ T, amusicalOrbit (3 ^ s * y) ∈ hfin.toFinset := by
    intro s _
    rw [Set.Finite.mem_toFinset]
    exact ⟨3 ^ s * y, by positivity, rfl⟩
  have hinj : Set.InjOn (fun s : ℕ => amusicalOrbit (3 ^ s * y)) T := by
    intro s hs s' hs' heq
    by_contra hne
    have heq' : amusicalOrbit (3 ^ s * y) = amusicalOrbit (3 ^ s' * y) := heq
    refine powers_orbit_ne hy hy2 hy3 (hT s hs) (hT s' hs') hne ?_
    rw [heq']
    exact mem_amusicalOrbit_self _
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  omega

/-- **Target (P3′).**  With `η = 1/k`: if the exponents `s ≤ S` whose orbit stays at or above
`3 · 2^(s + s/k + 1) y / 2` are not `O(log S)`, `U` has infinitely many orbits on `ℕ`. -/
theorem infinitelyManyOrbits_of_powers_log {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y)
    (hy3 : ¬ 3 ∣ y) (k : ℕ) (hk : 0 < k)
    (h : ∀ C : ℕ, ∃ S : ℕ, ∃ T : Finset ℕ, C * (Nat.log 2 S + 1) < T.card ∧
      ∀ s ∈ T, s ≤ S ∧ PowerAdmissible y (s + s / k + 1) s) :
    AmusicalInfinitelyManyOrbits := by
  sorry

end CollatzMoonshot.Amusical
