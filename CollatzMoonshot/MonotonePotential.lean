/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap

/-!
# Lemma P: orbit classification from a monotone potential

Research note `wythoff-solvable`, §1.  Let `σ` be a permutation of `ℤ` preserving `ℕ⁺`, `S` a
set of "up" points, `Φ` a `σ`-invariant set of exceptional points (in the applications `Φ = {1}`,
a fixed point, or `Φ = ∅`), and `T` a return bound.  Assume, on `ℕ⁺`:

* **(H1)** every `z ∉ S ∪ Φ` steps down: `σ z < z`;
* **(H2)** every `s ∈ S ∖ Φ` returns to `S` within `T` steps, and its first return
  `R(s) = σ^τ(s) s` is larger: `s < R(s)`.

**Lemma P.**  Every orbit through a positive point off `Φ` meets `S`, is infinite, and tends to
`∞` in both time directions (`permOrbit_infinite`, `tendsto_pow`, `tendsto_pow_neg`).  Its minimum
is its unique point of `S` whose `T` predecessors all lie off `S` (`isOrbitMin_iff`); equivalently
the minima off `Φ` are `(S ∖ Φ) ∖ R(S ∖ Φ)` (`isOrbitMin_iff_returnMap`).  Since `R` is injective
and `R(s) > s`, for every `X`

  `#{orbit minima ≤ X off Φ} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #((S ∖ Φ) ∩ [1, X])`

(`minCountOff_add_returnCount`).  When `Φ` consists of fixed points, they are exactly the finite
orbits in `ℕ⁺` (`permOrbit_finite_iff`) and each is its own minimum, adding `#(Φ ∩ [1, X])`
(`minCount_add_returnCount`; Theorem F's `1 + A − B` is the case `Φ = {1}`).

Paper proof (research note §1).  An orbit off `Φ` that avoids `S` strictly decreases forever in
`ℕ⁺` by (H1), impossible.  Along an orbit the `S`-visits satisfy `s < R(s) < R²(s) < ⋯`, and the
points strictly between `s` and `R(s)` lie off `S ∪ Φ`, so by (H1) they decrease to `R(s)`: each
exceeds `R(s)`.  Read backward the `S`-visits decrease in `ℕ⁺`, so there is a first one `y*`, and
before it every point lies off `S ∪ Φ`, increasing read backward.  Hence every point other than
`y*` exceeds `y*`, and both tails go to `∞`.  An `S`-point `y ≠ y*` has a last earlier `S`-visit
`s'` with `R(s') = y` at distance `τ(s') ≤ T`, so the `T`-predecessor test detects it.
-/

namespace CollatzMoonshot.MonotonePotential

open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology

/-- The hypotheses of Lemma P for a permutation `σ` of `ℤ`, an up-set `S`, an invariant
exceptional set `Φ`, and a return bound `T`. -/
structure Hyp (σ : Equiv.Perm ℤ) (S Φ : Set ℤ) (T : ℕ) : Prop where
  /-- `σ` preserves `ℕ⁺` (hence also `ℤ≤0`). -/
  pos_iff : ∀ n, 0 < σ n ↔ 0 < n
  /-- `Φ` is `σ`-invariant. -/
  mem_fix_iff : ∀ z, σ z ∈ Φ ↔ z ∈ Φ
  /-- (H1) Off `S ∪ Φ`, positive points step down. -/
  desc : ∀ z, 0 < z → z ∉ S → z ∉ Φ → σ z < z
  /-- (H2) A positive `s ∈ S ∖ Φ` first returns to `S` after `τ ≤ T` steps, to a larger
  value. -/
  ret : ∀ s, s ∈ S → 0 < s → s ∉ Φ → ∃ τ : ℕ, 1 ≤ τ ∧ τ ≤ T ∧ (σ ^ τ) s ∈ S ∧
    s < (σ ^ τ) s ∧ ∀ i : ℕ, 1 ≤ i → i < τ → (σ ^ i) s ∉ S

/-- `x` is the minimum of its two-sided orbit. -/
def IsOrbitMin (σ : Equiv.Perm ℤ) (x : ℤ) : Prop :=
  ∀ y ∈ permOrbit σ x, x ≤ y

open Classical in
/-- First-return time of `s` to `S` (`0` if `s` never returns). -/
noncomputable def returnTime (σ : Equiv.Perm ℤ) (S : Set ℤ) (s : ℤ) : ℕ :=
  if h : ∃ τ : ℕ, 0 < τ ∧ (σ ^ τ) s ∈ S then Nat.find h else 0

/-- The first-return map `R(s) = σ^τ(s) s`. -/
noncomputable def returnMap (σ : Equiv.Perm ℤ) (S : Set ℤ) (s : ℤ) : ℤ :=
  (σ ^ returnTime σ S s) s

open Classical in
/-- The number of orbit minima in `[1, X]`. -/
noncomputable def minCount (σ : Equiv.Perm ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => IsOrbitMin σ x).card

open Classical in
/-- The number of orbit minima in `[1, X]` off `Φ`. -/
noncomputable def minCountOff (σ : Equiv.Perm ℤ) (Φ : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => x ∉ Φ ∧ IsOrbitMin σ x).card

open Classical in
/-- `#(A ∩ [1, X])`. -/
noncomputable def setCount (A : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => x ∈ A).card

open Classical in
/-- `#{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X}`, which is `#(R(S ∖ Φ) ∩ [1, X])` since `R` is
injective with `R(s) > s`. -/
noncomputable def returnCount (σ : Equiv.Perm ℤ) (S Φ : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun s => s ∈ S ∧ s ∉ Φ ∧ returnMap σ S s ≤ X).card

section LemmaP

variable {σ : Equiv.Perm ℤ} {S Φ : Set ℤ} {T : ℕ}

/-! ### Orbit helpers -/

lemma mem_permOrbit_self (x : ℤ) : x ∈ permOrbit σ x := ⟨0, by simp⟩

lemma zpow_mem_permOrbit (x : ℤ) (t : ℤ) : (σ ^ t) x ∈ permOrbit σ x := ⟨t, rfl⟩

lemma pow_mem_permOrbit (x : ℤ) (n : ℕ) : (σ ^ n) x ∈ permOrbit σ x :=
  ⟨n, by simp only [zpow_natCast]⟩

lemma permOrbit_eq_of_mem {x y : ℤ} (h : y ∈ permOrbit σ x) : permOrbit σ y = permOrbit σ x := by
  obtain ⟨t, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s + t, by dsimp only; rw [zpow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s - t, ?_⟩
    dsimp only
    rw [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel]

/-- A property closed under `σ` and `σ⁻¹` holds on the whole orbit. -/
lemma permOrbit_induction (P : ℤ → Prop) {x : ℤ} (h0 : P x) (h1 : ∀ y, P y → P (σ y))
    (h2 : ∀ y, P y → P (σ.symm y)) : ∀ y ∈ permOrbit σ x, P y := by
  rintro y ⟨t, rfl⟩
  induction t using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    dsimp only at ih ⊢
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]; exact h1 _ ih
  | pred n ih =>
    dsimp only at ih ⊢
    rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
    exact h2 _ ih

lemma pow_pow_apply (a b : ℕ) (y : ℤ) : (σ ^ a) ((σ ^ b) y) = (σ ^ (a + b)) y := by
  rw [pow_add, Equiv.Perm.mul_apply]

lemma pow_zpow_neg (n : ℕ) (y : ℤ) : (σ ^ n) ((σ ^ (-(n : ℤ))) y) = y := by
  rw [← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero,
    Equiv.Perm.one_apply]

lemma pow_back (l m : ℕ) (hl : l ≤ m) (y : ℤ) :
    (σ ^ l) ((σ ^ (-(m : ℤ))) y) = (σ ^ (-((m - l : ℕ) : ℤ))) y := by
  rw [← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add,
    show (l : ℤ) + -(m : ℤ) = -((m - l : ℕ) : ℤ) by omega]

theorem Hyp.symm_pos (h : Hyp σ S Φ T) (y : ℤ) : 0 < σ.symm y ↔ 0 < y := by
  rw [← h.pos_iff, Equiv.apply_symm_apply]

theorem Hyp.symm_mem_fix (h : Hyp σ S Φ T) (y : ℤ) : σ.symm y ∈ Φ ↔ y ∈ Φ := by
  rw [← h.mem_fix_iff, Equiv.apply_symm_apply]

/-- **(ratified).**  Orbits of positive points stay positive.  Paper proof: `zpow` induction with
`pos_iff` in both directions. -/
theorem permOrbit_subset_pos (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) :
    permOrbit σ x ⊆ {y | 0 < y} := by
  intro y hy
  exact permOrbit_induction (fun y => 0 < y) hx (fun y hy => (h.pos_iff y).2 hy)
    (fun y hy => (h.symm_pos y).2 hy) y hy

/-- **(ratified).**  Orbits of points off `Φ` avoid `Φ` (`Φ` is invariant). -/
theorem permOrbit_subset_compl (h : Hyp σ S Φ T) {x : ℤ} (hx : x ∉ Φ) :
    permOrbit σ x ⊆ Φᶜ := by
  intro y hy
  exact permOrbit_induction (fun y => y ∉ Φ) hx (fun y hy => by rwa [h.mem_fix_iff])
    (fun y hy => by rwa [h.symm_mem_fix]) y hy

lemma zpow_pos' (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (t : ℤ) : 0 < (σ ^ t) x :=
  permOrbit_subset_pos h hx ⟨t, rfl⟩

lemma zpow_not_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : x ∉ Φ) (t : ℤ) : (σ ^ t) x ∉ Φ :=
  permOrbit_subset_compl h hx ⟨t, rfl⟩

lemma pow_pos' (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (n : ℕ) : 0 < (σ ^ n) x :=
  permOrbit_subset_pos h hx (pow_mem_permOrbit x n)

lemma pow_not_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : x ∉ Φ) (n : ℕ) : (σ ^ n) x ∉ Φ :=
  permOrbit_subset_compl h hx (pow_mem_permOrbit x n)

/-- Characterisation of the first-return time. -/
lemma returnTime_eq {u : ℤ} {n : ℕ} (hn : 0 < n) (hS : (σ ^ n) u ∈ S)
    (hmin : ∀ j : ℕ, 0 < j → j < n → (σ ^ j) u ∉ S) : returnTime σ S u = n := by
  classical
  have hex : ∃ τ : ℕ, 0 < τ ∧ (σ ^ τ) u ∈ S := ⟨n, hn, hS⟩
  unfold returnTime
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨⟨hn, hS⟩, fun j hj ⟨hj0, hjS⟩ => hmin j hj0 hj hjS⟩

/-- **(H1) iterated.**  A run of `d` points off `S` (starting at a positive `z ∉ Φ`) descends
by at least `d`. -/
lemma desc_chain (h : Hyp σ S Φ T) {z : ℤ} (hz : 0 < z) (hzΦ : z ∉ Φ) (d : ℕ)
    (hd : ∀ i : ℕ, i < d → (σ ^ i) z ∉ S) : (σ ^ d) z + d ≤ z := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih' := ih fun i hi => hd i (by omega)
    have hlt := h.desc ((σ ^ d) z) (pow_pos' h hz d) (hd d (by omega)) (pow_not_mem h hzΦ d)
    rw [pow_succ', Equiv.Perm.mul_apply]
    omega

/-- **(ratified).**  The first-return time is the `τ` of (H2): it lies in `[1, T]`, the return
lands in `S` above `s`, and the intermediate points are off `S`.  Paper proof: `Nat.find` is the
least positive `τ` with `σ^τ s ∈ S`; (H2)'s `τ` is such a `τ` with no smaller one. -/
theorem returnTime_spec (h : Hyp σ S Φ T) {s : ℤ} (hs : s ∈ S) (hs0 : 0 < s) (hsΦ : s ∉ Φ) :
    1 ≤ returnTime σ S s ∧ returnTime σ S s ≤ T ∧ returnMap σ S s ∈ S ∧
      s < returnMap σ S s ∧ ∀ i : ℕ, 1 ≤ i → i < returnTime σ S s → (σ ^ i) s ∉ S := by
  obtain ⟨τ, hτ1, hτT, hτS, hτlt, hτint⟩ := h.ret s hs hs0 hsΦ
  have hrt : returnTime σ S s = τ := returnTime_eq (by omega) hτS fun j hj0 hj => hτint j hj0 hj
  rw [returnMap, hrt]
  exact ⟨hτ1, hτT, hτS, hτlt, hτint⟩

/-- **(ratified).**  `R` stays positive and off `Φ`. -/
theorem returnMap_pos_not_mem (h : Hyp σ S Φ T) {s : ℤ} (hs : s ∈ S) (hs0 : 0 < s)
    (hsΦ : s ∉ Φ) : 0 < returnMap σ S s ∧ returnMap σ S s ∉ Φ := by
  exact ⟨pow_pos' h hs0 _, pow_not_mem h hsΦ _⟩

/-- **(ratified).**  `R` is injective on `(S ∖ Φ) ∩ ℕ⁺`.  Paper proof: if `R(s) = R(s') = y`
with `τ(s) < τ(s')`, then `s = σ^{τ(s') − τ(s)} s'` is an intermediate point of the first return
of `s'` (index in `[1, τ(s') − 1]`), yet `s ∈ S`: contradiction (`returnTime_spec`). -/
theorem returnMap_injOn (h : Hyp σ S Φ T) :
    Set.InjOn (returnMap σ S) {s | s ∈ S ∧ 0 < s ∧ s ∉ Φ} := by
  have key : ∀ s s', s ∈ S → 0 < s → s ∉ Φ → s' ∈ S → 0 < s' → s' ∉ Φ →
      returnTime σ S s ≤ returnTime σ S s' → returnMap σ S s = returnMap σ S s' → s = s' := by
    intro s s' hs hs0 hsΦ hs' hs0' hsΦ' hle heq
    have h1 := returnTime_spec h hs hs0 hsΦ
    have h2 := returnTime_spec h hs' hs0' hsΦ'
    unfold returnMap at heq
    have hs_eq : s = (σ ^ (returnTime σ S s' - returnTime σ S s)) s' := by
      apply (σ ^ returnTime σ S s).injective
      rw [pow_pow_apply, Nat.add_sub_cancel' hle]
      exact heq
    rcases Nat.eq_or_lt_of_le hle with hab | hab
    · rw [hab, Nat.sub_self, pow_zero] at hs_eq; exact hs_eq
    · rw [hs_eq] at hs
      exact absurd hs (h2.2.2.2.2 _ (by omega) (by omega))
  rintro s ⟨hs, hs0, hsΦ⟩ s' ⟨hs', hs0', hsΦ'⟩ heq
  rcases le_total (returnTime σ S s) (returnTime σ S s') with hle | hle
  · exact key s s' hs hs0 hsΦ hs' hs0' hsΦ' hle heq
  · exact (key s' s hs' hs0' hsΦ' hs hs0 hsΦ hle heq.symm).symm

/-- The forward orbit of a positive point off `Φ` meets `S`. -/
lemma exists_pow_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    ∃ n : ℕ, (σ ^ n) x ∈ S := by
  by_contra hne
  push Not at hne
  have := desc_chain h hx hxΦ x.toNat fun i _ => hne i
  have := pow_pos' h hx x.toNat
  omega

/-- **(ratified, Lemma P).**  An orbit through a positive point off `Φ` meets `S`. -/
theorem exists_mem_orbit_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    ∃ y ∈ permOrbit σ x, y ∈ S := by
  obtain ⟨n, hn⟩ := exists_pow_mem h hx hxΦ
  exact ⟨_, pow_mem_permOrbit x n, hn⟩

/-- After a positive `S`-point off `Φ`, every later point is strictly larger. -/
lemma lt_pow_of_mem (h : Hyp σ S Φ T) (i : ℕ) :
    ∀ {s : ℤ}, s ∈ S → 0 < s → s ∉ Φ → 1 ≤ i → s < (σ ^ i) s := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro s hs hs0 hsΦ hi
  obtain ⟨τ, hτ1, hτT, hτS, hτlt, hτint⟩ := h.ret s hs hs0 hsΦ
  rcases lt_trichotomy i τ with hlt | rfl | hgt
  · have := desc_chain h (pow_pos' h hs0 i) (pow_not_mem h hsΦ i) (τ - i) fun l hl => by
      rw [pow_pow_apply]; exact hτint (l + i) (by omega) (by omega)
    rw [pow_pow_apply, Nat.sub_add_cancel hlt.le] at this
    omega
  · exact hτlt
  · have := ih (i - τ) (by omega) hτS (pow_pos' h hs0 τ) (pow_not_mem h hsΦ τ) (by omega)
    rw [pow_pow_apply, Nat.sub_add_cancel hgt.le] at this
    omega

/-- After `k·T` steps from a positive `S`-point off `Φ`, the orbit has gained at least `k`. -/
lemma add_le_pow_of_mem (h : Hyp σ S Φ T) (k : ℕ) :
    ∀ {s : ℤ}, s ∈ S → 0 < s → s ∉ Φ → ∀ i : ℕ, k * T ≤ i → s + k ≤ (σ ^ i) s := by
  induction k with
  | zero =>
    intro s hs hs0 hsΦ i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have := lt_pow_of_mem h i hs hs0 hsΦ hi; omega
  | succ k ih =>
    intro s hs hs0 hsΦ i hi
    obtain ⟨τ, hτ1, hτT, hτS, hτlt, -⟩ := h.ret s hs hs0 hsΦ
    have hmul : (k + 1) * T = k * T + T := Nat.succ_mul k T
    have := ih hτS (pow_pos' h hs0 τ) (pow_not_mem h hsΦ τ) (i - τ) (by omega)
    rw [pow_pow_apply, Nat.sub_add_cancel (by omega)] at this
    omega

lemma tendsto_pow_aux (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    Tendsto (fun n : ℕ => (σ ^ n) x) atTop atTop := by
  obtain ⟨n0, hn0⟩ := exists_pow_mem h hx hxΦ
  rw [tendsto_atTop]
  intro b
  refine eventually_atTop.2 ⟨n0 + b.toNat * T, fun n hn => ?_⟩
  have := add_le_pow_of_mem h b.toNat hn0 (pow_pos' h hx n0) (pow_not_mem h hxΦ n0) (n - n0)
    (by omega)
  rw [pow_pow_apply, Nat.sub_add_cancel (by omega)] at this
  have := pow_pos' h hx n0
  omega

/-- Far enough back, the orbit avoids `S`. -/
lemma back_not_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) {n : ℕ}
    (hn : x.toNat * T ≤ n) : (σ ^ (-(n : ℤ))) x ∉ S := by
  intro hu
  have := add_le_pow_of_mem h x.toNat hu (zpow_pos' h hx _) (zpow_not_mem h hxΦ _) n hn
  rw [pow_zpow_neg] at this
  have := zpow_pos' h hx (-(n : ℤ))
  omega

/-- If the orbit avoids `S` strictly before time `−N`, it increases read backward from `−N`. -/
lemma back_ge (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) (N : ℕ)
    (hN : ∀ n : ℕ, N < n → (σ ^ (-(n : ℤ))) x ∉ S) (d : ℕ) :
    (σ ^ (-(N : ℤ))) x + d ≤ (σ ^ (-((N + d : ℕ) : ℤ))) x := by
  have := desc_chain h (zpow_pos' h hx _) (zpow_not_mem h hxΦ _) d
    (z := (σ ^ (-((N + d : ℕ) : ℤ))) x) fun i hi => by
      rw [pow_back i (N + d) (by omega)]; exact hN _ (by omega)
  rwa [pow_back d (N + d) (by omega), show N + d - d = N by omega] at this

/-- If the `T` predecessors of `x` are off `S`, then all its predecessors are. -/
lemma no_back_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ)
    (hT : ∀ i : ℕ, 1 ≤ i → i ≤ T → (σ ^ (-(i : ℤ))) x ∉ S) :
    ∀ n : ℕ, 0 < n → (σ ^ (-(n : ℤ))) x ∉ S := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hm0, hmS⟩ := Nat.find_spec hne
  have hmT : T < Nat.find hne := by
    by_contra hle
    push Not at hle
    exact hT _ hm0 hle hmS
  obtain ⟨τ, hτ1, hτT, hτS, -, -⟩ := h.ret _ hmS (zpow_pos' h hx _) (zpow_not_mem h hxΦ _)
  rw [pow_back τ _ (by omega)] at hτS
  exact Nat.find_min hne (show Nat.find hne - τ < Nat.find hne by omega) ⟨by omega, hτS⟩

/-- **(ratified, Lemma P).**  Such an orbit is infinite. -/
theorem permOrbit_infinite (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    (permOrbit σ x).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨b, hb⟩ => ?_
  obtain ⟨n, hn⟩ := ((tendsto_pow_aux h hx hxΦ).eventually_gt_atTop b).exists
  exact absurd (hb (pow_mem_permOrbit x n)) (not_le.2 hn)

/-- **(ratified).**  The orbit of a fixed point is a singleton (no `Hyp` needed). -/
theorem permOrbit_eq_singleton_of_fixed {x : ℤ} (hx : σ x = x) : permOrbit σ x = {x} := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx t
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mem_permOrbit_self y

/-- **(ratified, Lemma P (1)).**  When `Φ` consists of fixed points, the finite orbits through
`ℕ⁺` are exactly the points of `Φ`. -/
theorem permOrbit_finite_iff (h : Hyp σ S Φ T) (hfix : ∀ z ∈ Φ, σ z = z) {x : ℤ} (hx : 0 < x) :
    (permOrbit σ x).Finite ↔ x ∈ Φ := by
  constructor
  · intro hfin
    by_contra hxΦ
    exact permOrbit_infinite h hx hxΦ hfin
  · intro hxΦ
    rw [permOrbit_eq_singleton_of_fixed (hfix x hxΦ)]
    exact Set.finite_singleton x

/-- **(ratified, Lemma P (2), forward).**  The forward orbit tends to `∞`. -/
theorem tendsto_pow (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    Tendsto (fun n : ℕ => (σ ^ n) x) atTop atTop :=
  tendsto_pow_aux h hx hxΦ

/-- **(ratified, Lemma P (2), backward).**  The backward orbit tends to `∞`. -/
theorem tendsto_pow_neg (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    Tendsto (fun n : ℕ => (σ ^ (-(n : ℤ))) x) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  refine eventually_atTop.2 ⟨x.toNat * T + b.toNat, fun n hn => ?_⟩
  have := back_ge h hx hxΦ (x.toNat * T) (fun n hn => back_not_mem h hx hxΦ (by omega))
    (n - x.toNat * T)
  rw [show x.toNat * T + (n - x.toNat * T) = n by omega] at this
  have := zpow_pos' h hx (-((x.toNat * T : ℕ) : ℤ))
  omega

/-- **(ratified, Lemma P (3)).**  The orbit has a minimum. -/
theorem exists_isOrbitMin (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    ∃ y ∈ permOrbit σ x, IsOrbitMin σ y := by
  have hpos := permOrbit_subset_pos h hx
  classical
  have hex : ∃ n : ℕ, ∃ y ∈ permOrbit σ x, y = n :=
    ⟨x.toNat, x, mem_permOrbit_self x, by omega⟩
  obtain ⟨y, hy, hyn⟩ := Nat.find_spec hex
  refine ⟨y, hy, fun z hz => ?_⟩
  rw [permOrbit_eq_of_mem hy] at hz
  have hz0 : 0 < z := hpos hz
  have := Nat.find_min' hex ⟨z, hz, (Int.toNat_of_nonneg hz0.le).symm⟩
  omega

/-- **(ratified, Lemma P (3)).**  A positive `x ∉ Φ` is the minimum of its orbit iff `x ∈ S` and
its `T` predecessors are all off `S`. -/
theorem isOrbitMin_iff (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    IsOrbitMin σ x ↔
      x ∈ S ∧ ∀ i : ℕ, 1 ≤ i → i ≤ T → (σ ^ (-(i : ℤ))) x ∉ S := by
  constructor
  · intro hmin
    have hS : x ∈ S := by
      by_contra hS
      have h1 := h.desc x hx hS hxΦ
      have h2 := hmin _ (pow_mem_permOrbit x 1)
      rw [pow_one] at h2
      omega
    refine ⟨hS, fun i hi1 _ hu => ?_⟩
    have h1 := lt_pow_of_mem h i hu (zpow_pos' h hx _) (zpow_not_mem h hxΦ _) hi1
    rw [pow_zpow_neg] at h1
    have h2 := hmin _ (zpow_mem_permOrbit x (-(i : ℤ)))
    omega
  · rintro ⟨hS, hT⟩
    have hback := no_back_mem h hx hxΦ hT
    rintro y ⟨t, rfl⟩
    dsimp only
    rcases Int.eq_nat_or_neg t with ⟨n, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have := lt_pow_of_mem h n hS hx hxΦ hn
        rw [zpow_natCast]
        omega
    · have := back_ge h hx hxΦ 0 (fun n hn => hback n hn) n
      simp only [Nat.cast_zero, neg_zero, zpow_zero, Equiv.Perm.one_apply, zero_add] at this
      omega

/-- **(ratified, Lemma P (4)).**  The minima off `Φ` are `(S ∖ Φ) ∖ R(S ∖ Φ)`. -/
theorem isOrbitMin_iff_returnMap (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    IsOrbitMin σ x ↔
      x ∈ S ∧ ∀ s, s ∈ S → 0 < s → s ∉ Φ → returnMap σ S s ≠ x := by
  constructor
  · intro hmin
    have hS := ((isOrbitMin_iff h hx hxΦ).1 hmin).1
    refine ⟨hS, fun s hs hs0 hsΦ hR => ?_⟩
    have hlt := (returnTime_spec h hs hs0 hsΦ).2.2.2.1
    have hmem : s ∈ permOrbit σ x := by
      rw [← hR, returnMap, permOrbit_eq_of_mem (pow_mem_permOrbit s _)]
      exact mem_permOrbit_self s
    have := hmin s hmem
    omega
  · rintro ⟨hS, hR⟩
    refine (isOrbitMin_iff h hx hxΦ).2 ⟨hS, ?_⟩
    classical
    intro i hi1 _ hu
    have hne : ∃ n : ℕ, 0 < n ∧ (σ ^ (-(n : ℤ))) x ∈ S := ⟨i, hi1, hu⟩
    obtain ⟨hm0, hmS⟩ := Nat.find_spec hne
    have hrt : returnTime σ S ((σ ^ (-(Nat.find hne : ℤ))) x) = Nat.find hne := by
      apply returnTime_eq hm0
      · rw [pow_zpow_neg]; exact hS
      · intro j hj0 hjm hjS
        rw [pow_back j _ hjm.le] at hjS
        exact Nat.find_min hne (show Nat.find hne - j < Nat.find hne by omega) ⟨by omega, hjS⟩
    apply hR _ hmS (zpow_pos' h hx _) (zpow_not_mem h hxΦ _)
    rw [returnMap, hrt, pow_zpow_neg]

/-- **(ratified).**  A fixed point is the minimum of its orbit. -/
theorem isOrbitMin_of_fixed {x : ℤ} (hx : σ x = x) : IsOrbitMin σ x := by
  intro y hy
  rw [permOrbit_eq_singleton_of_fixed hx, Set.mem_singleton_iff] at hy
  rw [hy]

/-- **(ratified, Lemma P (4), exact count off `Φ`).**
`#{minima ≤ X off Φ} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #((S ∖ Φ) ∩ [1, X])`.
Paper proof: by `isOrbitMin_iff_returnMap` the minima in `[1, X]` off `Φ` are
`((S ∖ Φ) ∩ [1, X]) ∖ R(…)`; `R` maps `{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X}` injectively onto
`R(S ∖ Φ) ∩ [1, X]` (`R(s) ≤ X` forces `s < X`), a subset of `(S ∖ Φ) ∩ [1, X]`;
`Finset.card_sdiff`. -/
theorem minCountOff_add_returnCount (h : Hyp σ S Φ T) (X : ℕ) :
    minCountOff σ Φ X + returnCount σ S Φ X = setCount (S \ Φ) X := by
  classical
  have hinj : Set.InjOn (returnMap σ S)
      ↑((Finset.Icc (1 : ℤ) X).filter fun s => s ∈ S ∧ s ∉ Φ ∧ returnMap σ S s ≤ X) := by
    refine (returnMap_injOn h).mono fun s hs => ?_
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hs
    exact ⟨hs.2.1, by omega, hs.2.2.1⟩
  have hsub : ((Finset.Icc (1 : ℤ) X).filter fun s => s ∈ S ∧ s ∉ Φ ∧ returnMap σ S s ≤ X).image
      (returnMap σ S) ⊆ (Finset.Icc (1 : ℤ) X).filter fun x => x ∈ S \ Φ := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    obtain ⟨⟨hs1, hsX⟩, hsS, hsΦ, hR⟩ := hs
    obtain ⟨-, -, hRS, hlt, -⟩ := returnTime_spec h hsS (by omega) hsΦ
    have hRΦ := (returnMap_pos_not_mem h hsS (by omega) hsΦ).2
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_sdiff]
    exact ⟨⟨by omega, hR⟩, hRS, hRΦ⟩
  have hA : ((Finset.Icc (1 : ℤ) X).filter fun x => x ∉ Φ ∧ IsOrbitMin σ x) =
      ((Finset.Icc (1 : ℤ) X).filter fun x => x ∈ S \ Φ) \
        ((Finset.Icc (1 : ℤ) X).filter fun s => s ∈ S ∧ s ∉ Φ ∧ returnMap σ S s ≤ X).image
          (returnMap σ S) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, Finset.mem_Icc,
      Set.mem_sdiff]
    constructor
    · rintro ⟨hI, hxΦ, hmin⟩
      have hm := (isOrbitMin_iff_returnMap h (by omega) hxΦ).1 hmin
      refine ⟨⟨hI, hm.1, hxΦ⟩, ?_⟩
      rintro ⟨s, ⟨hsI, hsS, hsΦ, -⟩, hR⟩
      exact hm.2 s hsS (by omega) hsΦ hR
    · rintro ⟨⟨hI, hxS, hxΦ⟩, hnot⟩
      refine ⟨hI, hxΦ, (isOrbitMin_iff_returnMap h (by omega) hxΦ).2 ⟨hxS, ?_⟩⟩
      intro s hsS hs0 hsΦ hR
      have hlt := (returnTime_spec h hsS hs0 hsΦ).2.2.2.1
      exact hnot ⟨s, ⟨⟨by omega, by omega⟩, hsS, hsΦ, by omega⟩, hR⟩
  have key := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_image_of_injOn hinj, ← hA] at key
  unfold minCountOff returnCount setCount
  convert key using 2
  ext x
  simp only [Finset.mem_filter]

/-- **(ratified, Lemma P (4), exact count).**  When `Φ` consists of fixed points,
`#{minima ≤ X} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #(Φ ∩ [1, X]) + #((S ∖ Φ) ∩ [1, X])`.
The `#Φ` term is Theorem F's `+1`. -/
theorem minCount_add_returnCount (h : Hyp σ S Φ T) (hfix : ∀ z ∈ Φ, σ z = z) (X : ℕ) :
    minCount σ X + returnCount σ S Φ X = setCount Φ X + setCount (S \ Φ) X := by
  classical
  have hsplit : minCount σ X = setCount Φ X + minCountOff σ Φ X := by
    unfold minCount setCount minCountOff
    rw [← Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc (1 : ℤ) X).filter fun x => IsOrbitMin σ x) (fun x => x ∈ Φ),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hI, -, hxΦ⟩; exact ⟨hI, hxΦ⟩
      · rintro ⟨hI, hxΦ⟩; exact ⟨hI, isOrbitMin_of_fixed (hfix x hxΦ), hxΦ⟩
    · ext x
      simp only [Finset.mem_filter]
      tauto
  rw [hsplit, add_assoc, minCountOff_add_returnCount h X]

/-- **(ratified).**  Infinitely many positive minima off `Φ` give infinitely many infinite
orbits.  Paper proof: distinct minima lie on distinct orbits (two minima of one orbit are equal by
`le_antisymm`), each infinite by `permOrbit_infinite`. -/
theorem infinitelyManyInfiniteOrbits_of_minima (h : Hyp σ S Φ T)
    (hinf : {x : ℤ | 0 < x ∧ x ∉ Φ ∧ IsOrbitMin σ x}.Infinite) :
    InfinitelyManyInfiniteOrbits σ := by
  have hinj : Set.InjOn (permOrbit σ) {x : ℤ | 0 < x ∧ x ∉ Φ ∧ IsOrbitMin σ x} := by
    rintro x ⟨-, -, hx⟩ y ⟨-, -, hy⟩ hxy
    have h1 : y ∈ permOrbit σ x := by rw [hxy]; exact mem_permOrbit_self y
    have h2 : x ∈ permOrbit σ y := by rw [← hxy]; exact mem_permOrbit_self x
    exact le_antisymm (hx y h1) (hy x h2)
  refine (hinf.image hinj).mono ?_
  rintro _ ⟨x, ⟨hx0, hxΦ, -⟩, rfl⟩
  exact ⟨x, hx0.le, rfl, permOrbit_infinite h hx0 hxΦ⟩

end LemmaP

end CollatzMoonshot.MonotonePotential
