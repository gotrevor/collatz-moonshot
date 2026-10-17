/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Amusical
import CollatzMoonshot.WythoffRational

/-!
# Residue-transitivity of the rational Wythoff members (Theorem RT)

The residue digraph of `f : ℤ → ℤ` mod `M` has an edge `a → b` iff some `n ≡ a (mod M)` has
`f n ≡ b (mod M)` (`ResidueEdge`).  `f` is *residue-transitive* mod `M` if that digraph is strongly
connected (`ResidueTransitive`); equivalently, the only sets of residues closed under `f`
(`ResidueClosed`: `n mod M ∈ C → f n mod M ∈ C`) are `∅` and everything
(`residueTransitive_iff_closed`).  A closed proper set is exactly a *residue trap*: a union of
residue classes that `f` maps into itself, the input of `AmusicalTrap`'s trap theorem.

**Theorem RT** (research note `wythoff-transitive.md`, 2026-10-16).  Let `p ≥ 3`, `0 < q < p`,
`gcd(p, q) = 1`, `R = p − q`.  `W = W_{p/q±}` (`wythoff`) is residue-transitive mod every `M ≥ 1`,
except the *absorbing* members (`p` even, side `+`, `q = 1` or `R = 1`; Theorem T,
`parityClass_invariant_iff`), which are residue-transitive exactly at the odd `M`
(`residueTransitive_iff`).  `U = W_{3/1+}` (`amusical_eq_wythoff`), so `U` is residue-transitive
at every modulus (`amusical_residueTransitive`).  This is *stronger* than the existing
`amusical_pow_classUnion_invariant` (no union of classes with `U(S) = S`): it also excludes
`U(S) ⊊ S`, i.e. every periodic trap.  Consequence (`eventually_mem_or_not_mem_of_closed`): an
eventually-periodic set that `W` eventually maps into itself is eventually everything or
eventually empty, so the trap theorem has nothing to act on.

Proof shape (note §1-§3): the **window formula** (`wythoff_even_window`, `wythoff_odd_window`)
writes `W(2y) = (py − j)/q`, `W(2y − 1) = (py − j)/R` with `j` in a window of `q` (resp. `R`)
consecutive integers.  **Base** at moduli `2^e M₀`, `gcd(M₀, 2pqR) = 1`: (B0) `e = 0`
(`residueTransitive_base_coprime`; uniform law stationary, translation by `1/q`), (B1) `e ≥ 1`
for even `p` (`residueTransitive_base_two_pow`; stationary law `φ × uniform`, full support iff
non-absorbing).  **Lifts** one prime at a time: Lemma D (`2`, `4 ∣ p`), Lemma B (odd `ℓ ∣ p`, via
`W⁻¹`), Lemma A (odd `ℓ ∣ qR`, routed through parity), Lemma A₂ (`2`, `p` odd).

Sharpness: at `p = 2`, `W_{2/1−}` is the swap `2k ↔ 2k − 1`, not residue-transitive at any even
`M ≥ 4` (`two_minus_not_residueTransitive`).

Truth checks: `tmp/drafter-rt/check.py` (gitignored; brute-force SCC over a full period
`[0, 2qRM)`, subset enumeration for the trap form, teeth on every hypothesis that is not a proof
artifact).
-/

namespace CollatzMoonshot.WythoffResidue

open CollatzMoonshot.WythoffRational
open CollatzMoonshot.Amusical (amusical)

/-! ## A. Residue digraphs -/

section Digraph

/-- An edge `a → b` of the residue digraph of `f` mod `M`. -/
def ResidueEdge (f : ℤ → ℤ) (M : ℕ) (a b : ZMod M) : Prop :=
  ∃ n : ℤ, (n : ZMod M) = a ∧ (f n : ZMod M) = b

/-- `f` is residue-transitive mod `M`: its residue digraph is strongly connected. -/
def ResidueTransitive (f : ℤ → ℤ) (M : ℕ) : Prop :=
  ∀ a b : ZMod M, Relation.ReflTransGen (ResidueEdge f M) a b

/-- A set of residues mod `M` that `f` maps into itself (a *residue trap* when proper and
nonempty). -/
def ResidueClosed (f : ℤ → ℤ) (M : ℕ) (C : Set (ZMod M)) : Prop :=
  ∀ n : ℤ, (n : ZMod M) ∈ C → (f n : ZMod M) ∈ C

/-- **(ratified).**  Closed under `f` is closed under the edges of the residue digraph. -/
theorem residueClosed_iff_edge (f : ℤ → ℤ) (M : ℕ) (C : Set (ZMod M)) :
    ResidueClosed f M C ↔ ∀ a b, a ∈ C → ResidueEdge f M a b → b ∈ C := by
  constructor
  · rintro h a b ha ⟨n, rfl, rfl⟩
    exact h n ha
  · intro h n hn
    exact h _ _ hn ⟨n, rfl, rfl⟩

/-- **(ratified).**  The trap form: residue-transitive iff the only closed sets are `∅` and
everything.  (The set reachable from a vertex is closed.) -/
theorem residueTransitive_iff_closed (f : ℤ → ℤ) (M : ℕ) :
    ResidueTransitive f M ↔ ∀ C : Set (ZMod M), ResidueClosed f M C → C = ∅ ∨ C = Set.univ := by
  constructor
  · intro h C hC
    rw [residueClosed_iff_edge] at hC
    by_cases hne : C.Nonempty
    · obtain ⟨a, ha⟩ := hne
      right
      refine Set.eq_univ_of_forall fun b => ?_
      induction h a b with
      | refl => exact ha
      | tail _ hbc ih => exact hC _ _ ih hbc
    · left; exact Set.not_nonempty_iff_eq_empty.mp hne
  · intro h a b
    have hC : ResidueClosed f M {x | Relation.ReflTransGen (ResidueEdge f M) a x} := by
      rw [residueClosed_iff_edge]
      intro x y hx hxy
      exact Relation.ReflTransGen.tail hx hxy
    rcases h _ hC with h0 | h1
    · have : a ∈ ({x | Relation.ReflTransGen (ResidueEdge f M) a x} : Set (ZMod M)) :=
        Relation.ReflTransGen.refl
      rw [h0] at this
      exact absurd this (Set.notMem_empty a)
    · have : b ∈ ({x | Relation.ReflTransGen (ResidueEdge f M) a x} : Set (ZMod M)) := by
        rw [h1]; trivial
      exact this

/-- **(ratified).**  The residue digraph of `σ⁻¹` is the reversal of that of `σ`, so the two are
residue-transitive together. -/
theorem residueTransitive_symm_iff (σ : Equiv.Perm ℤ) (M : ℕ) :
    ResidueTransitive σ.symm M ↔ ResidueTransitive σ M := by
  have hswap : ResidueEdge σ.symm M = Function.swap (ResidueEdge σ M) := by
    funext a b
    apply propext
    constructor
    · rintro ⟨n, rfl, rfl⟩
      exact ⟨σ.symm n, rfl, by simp⟩
    · rintro ⟨n, rfl, rfl⟩
      exact ⟨σ n, rfl, by simp⟩
  unfold ResidueTransitive
  rw [hswap]
  constructor
  · intro h a b; exact Relation.reflTransGen_swap.mp (h b a)
  · intro h a b; exact Relation.reflTransGen_swap.mpr (h b a)

/-- **(ratified).**  Every map is residue-transitive mod `1`. -/
theorem residueTransitive_one (f : ℤ → ℤ) : ResidueTransitive f 1 := by
  intro a b
  rw [Subsingleton.elim a b]

end Digraph

/-! ## B. The window formula -/

section Window

variable (s : Side) {p q : ℕ}

/-- Left end of the even-branch window: `J_E = [0, q − 1]` on `+`, `[1, q]` on `−`. -/
def evenLo : Side → ℤ
  | .plus => 0
  | .minus => 1

/-- Left end of the odd-branch window: `J_O = [1, R]` on `+`, `[0, R − 1]` on `−`. -/
def oddLo : Side → ℤ
  | .plus => 1
  | .minus => 0

/-- **(ratified).**  Even-branch window formula: for `j` in the window `J_E`,
`q · W(2y) = py − j` iff `j ≡ py (mod q)`.  Paper proof: `⌊x/q⌋ = (x − x mod q)/q`, and
`⌈x/q⌉ − 1 = (x − j)/q` with `j ∈ [1, q]`, `j ≡ x`. -/
theorem wythoff_even_window (hq : 0 < q) (y j : ℤ) (hj : evenLo s ≤ j ∧ j < evenLo s + q) :
    wythoff s p q (2 * y) * q = p * y - j ↔ (q : ℤ) ∣ p * y - j := by
  sorry

/-- **(ratified).**  Odd-branch window formula: for `j` in the window `J_O`,
`R · W(2y − 1) = py − j` iff `j ≡ py (mod R)`. -/
theorem wythoff_odd_window (hqp : q < p) (y j : ℤ)
    (hj : oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) :
    wythoff s p q (2 * y - 1) * ((p : ℤ) - q) = p * y - j ↔ ((p : ℤ) - q) ∣ p * y - j := by
  sorry

/-- **(ratified).**  The even window contains an element `≡ py (mod q)`. -/
theorem exists_even_window (hq : 0 < q) (y : ℤ) :
    ∃ j, (evenLo s ≤ j ∧ j < evenLo s + q) ∧ (q : ℤ) ∣ p * y - j := by
  sorry

/-- **(ratified).**  The odd window contains an element `≡ py (mod R)`. -/
theorem exists_odd_window (hqp : q < p) (y : ℤ) :
    ∃ j, (oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) ∧ ((p : ℤ) - q) ∣ p * y - j := by
  sorry

end Window

/-! ## C. Odd `p`, and `U` -/

section OddP

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  `U = W_{3/1+}`: `2k ↦ 3k`, `2k − 1 ↦ ⌈3k/2⌉ − 1`. -/
theorem amusical_eq_wythoff : amusical = wythoff .plus 3 1 := by
  funext n
  simp only [amusical, wythoff, Nat.cast_ofNat, Nat.cast_one, Int.ediv_one]
  rw [show ((3 : ℤ) - 1) = 2 by norm_num]
  split_ifs <;> omega

/-- **(ratified).**  **(B0)** Base at moduli coprime to `2pqR`, any `p ≥ 3`, both sides,
absorbing members included.  Paper proof: note §2 (B0). -/
theorem residueTransitive_base_coprime (hp3 : 3 ≤ p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M₀ : ℕ} (hM₀ : Nat.Coprime M₀ (2 * p * q * (p - q))) :
    ResidueTransitive (wythoff s p q) M₀ := by
  sorry

/-- **(ratified).**  **Lemma B** (odd primes of `p`): lift `M' → ℓ^e M'` for an odd prime
`ℓ ∣ p`, `ℓ ∤ M'`; `W⁻¹` expands `ℓ`-adically.  Paper proof: note §3 Lemma B. -/
theorem residueTransitive_lift_dvd_p (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p) {M' : ℕ} (hM' : 0 < M')
    (hℓM : ¬ ℓ ∣ M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (ℓ ^ e * M') := by
  sorry

/-- **(ratified).**  **Lemma A** (odd primes of `qR`): lift `M' → ℓ^e M'` for an odd prime
`ℓ ∣ qR`, `ℓ ∤ M'`; `W` expands `ℓ`-adically on one branch, routed through parity.  Paper proof:
note §3 Lemma A. -/
theorem residueTransitive_lift_dvd_qR (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓqR : ℓ ∣ q * (p - q)) {M' : ℕ} (hM' : 0 < M')
    (hℓM : ¬ ℓ ∣ M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (ℓ ^ e * M') := by
  sorry

/-- **(ratified).**  **Lemma A₂** (`p` odd, the prime `2`): every piece `a + 2Qℤ ↦ c + pℤ`
drops the `2`-level.  Paper proof: note §3 Lemma A₂. -/
theorem residueTransitive_lift_two_of_odd (hp : Odd p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M' : ℕ} (hM' : Odd M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (2 ^ e * M') := by
  sorry

/-- **(ratified).**  **Theorem RT, odd `p`.**  `W_{p/q±}` is residue-transitive mod every
`M ≥ 1`.  Paper proof: (B0) mod `M₀`, then Lemma A₂, Lemma B, Lemma A one prime at a time. -/
theorem residueTransitive_of_odd (hp : Odd p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M : ℕ} (hM : 0 < M) : ResidueTransitive (wythoff s p q) M := by
  sorry

/-- **(ratified).**  `U` is residue-transitive mod every `M ≥ 1`: no union of residue classes is
a proper nonempty trap for `U`. -/
theorem amusical_residueTransitive {M : ℕ} (hM : 0 < M) : ResidueTransitive amusical M := by
  rw [amusical_eq_wythoff]
  exact residueTransitive_of_odd .plus ⟨1, rfl⟩ (by norm_num) one_pos (by norm_num) hM

/-- **(ratified).**  **No eventually-periodic trap.**  If `W` is residue-transitive mod `M`, and
`C ⊆ ℤ` is eventually `M`-periodic and eventually mapped into itself by `W`, then `C` eventually
contains everything or eventually nothing.  Paper proof: let `C̃` be the residues of the large
elements of `C`.  Each edge `a → b` is realized along `n + 2qRMk`, `k → ∞`, with `W n → ∞`; so
`C̃` is `ResidueClosed`, hence `∅` or everything. -/
theorem eventually_mem_or_not_mem_of_closed (hq : 0 < q) (hqp : q < p) {M : ℕ} (hM : 0 < M)
    (hRT : ResidueTransitive (wythoff s p q) M) {C : Set ℤ}
    (hper : ∀ᶠ n in (Filter.atTop : Filter ℤ), (n ∈ C ↔ n + M ∈ C))
    (hfwd : ∀ᶠ n in (Filter.atTop : Filter ℤ), n ∈ C → wythoff s p q n ∈ C) :
    (∀ᶠ n in (Filter.atTop : Filter ℤ), n ∈ C) ∨ (∀ᶠ n in (Filter.atTop : Filter ℤ), n ∉ C) := by
  sorry

/-- **(ratified).**  For `U`: an eventually-periodic set eventually mapped into itself by `U`
is eventually everything or eventually empty.  (Finite cycles are the only trap-free exceptions
in `ℕ⁺`: `C` itself may be a finite union of cycles, or the complement of one.) -/
theorem amusical_eventually_mem_or_not_mem {M : ℕ} (hM : 0 < M) {C : Set ℤ}
    (hper : ∀ᶠ n in (Filter.atTop : Filter ℤ), (n ∈ C ↔ n + M ∈ C))
    (hfwd : ∀ᶠ n in (Filter.atTop : Filter ℤ), n ∈ C → amusical n ∈ C) :
    (∀ᶠ n in (Filter.atTop : Filter ℤ), n ∈ C) ∨ (∀ᶠ n in (Filter.atTop : Filter ℤ), n ∉ C) := by
  rw [amusical_eq_wythoff] at hfwd
  exact eventually_mem_or_not_mem_of_closed .plus one_pos (by norm_num) hM
    (residueTransitive_of_odd .plus ⟨1, rfl⟩ (by norm_num) one_pos (by norm_num) hM) hper hfwd

end OddP

/-! ## D. Even `p`: the full Theorem RT -/

section EvenP

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  **(B1)** Base at `2^e M₀` for even `p ≥ 4`, non-absorbing, when
`p ≡ 2 (mod 4)` or `e = 1`.  (The disjunct is a proof artifact: for `4 ∣ p`, `e ≥ 2`, Lemma D
supplies the case.)  Paper proof: note §2 (B1). -/
theorem residueTransitive_base_two_pow (hp : Even p) (hp4 : 4 ≤ p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) (hna : ¬ (s = .plus ∧ (q = 1 ∨ p - q = 1))) {e M₀ : ℕ}
    (he : 1 ≤ e) (h4 : p % 4 = 2 ∨ e = 1) (hM₀ : Nat.Coprime M₀ (2 * p * q * (p - q))) :
    ResidueTransitive (wythoff s p q) (2 ^ e * M₀) := by
  sorry

/-- **(ratified).**  **Lemma D** (`4 ∣ p`, the prime `2`): lift `2M₀ → 2^e M₀`; `W⁻¹` expands
`2`-adically by `2^{v₂(p) − 1}`.  Paper proof: note §2 Lemma D. -/
theorem residueTransitive_lift_two_of_four_dvd (h4 : 4 ∣ p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) {M₀ : ℕ} (hM₀ : Nat.Coprime M₀ (2 * p * q * (p - q)))
    (h : ResidueTransitive (wythoff s p q) (2 * M₀)) {e : ℕ} (he : 1 ≤ e) :
    ResidueTransitive (wythoff s p q) (2 ^ e * M₀) := by
  sorry

/-- **(ratified).**  **Theorem RT, even `p`, non-absorbing.**  Residue-transitive mod every
`M ≥ 1`.  Paper proof: (B0)/(B1)/Lemma D at `2^e M₀`, then Lemma B, Lemma A. -/
theorem residueTransitive_of_even_nonabsorbing (hp : Even p) (hp4 : 4 ≤ p)
    (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (hna : ¬ (s = .plus ∧ (q = 1 ∨ p - q = 1))) {M : ℕ} (hM : 0 < M) :
    ResidueTransitive (wythoff s p q) M := by
  sorry

/-- **(ratified).**  Every member with `p ≥ 3` is residue-transitive at every odd `M`
(absorbing members included: (B0), Lemma B and Lemma A at odd `M'` never use the parity chain). -/
theorem residueTransitive_of_odd_modulus (hp3 : 3 ≤ p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M : ℕ} (hM : Odd M) : ResidueTransitive (wythoff s p q) M := by
  sorry

/-- **(ratified).**  Absorbing members are not residue-transitive at any even `M`: the absorbing
parity class is closed (Theorem T, `parityClass_invariant_iff`).  Holds at `p = 2` too. -/
theorem not_residueTransitive_of_absorbing_even (hp : Even p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) (habs : s = .plus ∧ (q = 1 ∨ p - q = 1)) {M : ℕ}
    (hM0 : 0 < M) (hM : Even M) : ¬ ResidueTransitive (wythoff s p q) M := by
  sorry

/-- **(ratified).**  **Theorem RT, absorbing members.**  For even `p ≥ 4`, side `+`, `q = 1` or
`R = 1`: residue-transitive mod `M` iff `M` is odd. -/
theorem residueTransitive_absorbing_iff (hp : Even p) (hp4 : 4 ≤ p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) (habs : s = .plus ∧ (q = 1 ∨ p - q = 1)) {M : ℕ}
    (hM : 0 < M) : ResidueTransitive (wythoff s p q) M ↔ Odd M := by
  constructor
  · intro h
    rcases Nat.even_or_odd M with hM2 | hM2
    · exact absurd h (not_residueTransitive_of_absorbing_even s hp hcop hq hqp habs hM hM2)
    · exact hM2
  · intro hM2
    exact residueTransitive_of_odd_modulus s (by omega) hcop hq hqp hM2

/-- **(ratified).**  **Theorem RT.**  For `p ≥ 3`, `0 < q < p`, `gcd(p, q) = 1`, `W_{p/q±}` is
residue-transitive mod `M ≥ 1` iff the member is not absorbing or `M` is odd. -/
theorem residueTransitive_iff (hp3 : 3 ≤ p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M : ℕ} (hM : 0 < M) :
    ResidueTransitive (wythoff s p q) M ↔
      ¬ (Even p ∧ s = .plus ∧ (q = 1 ∨ p - q = 1)) ∨ Odd M := by
  rcases Nat.even_or_odd p with hp | hp
  · have hp4 : 4 ≤ p := by obtain ⟨k, rfl⟩ := hp; omega
    by_cases habs : s = .plus ∧ (q = 1 ∨ p - q = 1)
    · rw [residueTransitive_absorbing_iff s hp hp4 hcop hq hqp habs hM]
      simp [hp, habs]
    · simp only [hp, true_and, habs, not_false_eq_true, true_or, iff_true]
      exact residueTransitive_of_even_nonabsorbing s hp hp4 hcop hq hqp habs hM
  · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr hp
    simp only [hne, false_and, not_false_eq_true, true_or, iff_true]
    exact residueTransitive_of_odd s hp hcop hq hqp hM

/-- **(ratified).**  Sharpness at `p = 2`: `W_{2/1−}` is the swap `2k ↔ 2k − 1`, and the pair
`{1, 2}` is a closed proper set mod every even `M ≥ 4`. -/
theorem two_minus_not_residueTransitive {M : ℕ} (hM4 : 4 ≤ M) (hM : Even M) :
    ¬ ResidueTransitive (wythoff .minus 2 1) M := by
  sorry

end EvenP

end CollatzMoonshot.WythoffResidue
