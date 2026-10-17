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

Formal route.  Every lift is one instance of `ClassIn.drop`: a closed set containing a full
class mod `K₁` contains the class of the image mod `K₂` when `f` is affine from `K₁`-steps to
`K₂`-steps with a multiplier coprime to `M / K₂` (`W(n + 2Qm) = W n + pm`, `wythoffInv_add_piece`).
Levels are classes mod `ℓ^j M'`; no valuations are needed.  (B0) is a translation argument
(`residueTransitive_of_translate`), and (B1) replaces the circulation by counting
(`exists_preimage_of_counting`): the even and odd parts of a closed set inject into each other, so
every window map is onto its parity part, and two adjacent window indices translate by `1/Q`.

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

/-- Floor division recovers `t − j` exactly when `d ∣ t − j`, for `j ∈ [0, d)`. -/
theorem ediv_mul_eq_sub_iff {t j d : ℤ} (hd : 0 < d) (hj : 0 ≤ j ∧ j < d) :
    t / d * d = t - j ↔ d ∣ t - j := by
  constructor
  · intro h; exact ⟨t / d, by linarith⟩
  · rintro ⟨c, hc⟩
    rw [(ediv_eq_iff hd).2 ⟨by linarith, by linarith⟩]
    linarith

/-- **(ratified).**  Even-branch window formula: for `j` in the window `J_E`,
`q · W(2y) = py − j` iff `j ≡ py (mod q)`.  Paper proof: `⌊x/q⌋ = (x − x mod q)/q`, and
`⌈x/q⌉ − 1 = (x − j)/q` with `j ∈ [1, q]`, `j ≡ x`. -/
theorem wythoff_even_window (hq : 0 < q) (y j : ℤ) (hj : evenLo s ≤ j ∧ j < evenLo s + q) :
    wythoff s p q (2 * y) * q = p * y - j ↔ (q : ℤ) ∣ p * y - j := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  cases s
  · rw [wythoff_plus_even, mul_comm y]
    exact ediv_mul_eq_sub_iff hq' (by simpa [evenLo] using hj)
  · rw [wythoff_minus_even, mul_comm y,
      show (p : ℤ) * y - j = p * y - 1 - (j - 1) by ring]
    exact ediv_mul_eq_sub_iff hq' (by simp [evenLo] at hj; omega)

/-- **(ratified).**  Odd-branch window formula: for `j` in the window `J_O`,
`R · W(2y − 1) = py − j` iff `j ≡ py (mod R)`. -/
theorem wythoff_odd_window (hqp : q < p) (y j : ℤ)
    (hj : oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) :
    wythoff s p q (2 * y - 1) * ((p : ℤ) - q) = p * y - j ↔ ((p : ℤ) - q) ∣ p * y - j := by
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  cases s
  · rw [wythoff_plus_odd, mul_comm y,
      show (p : ℤ) * y - j = p * y - 1 - (j - 1) by ring]
    exact ediv_mul_eq_sub_iff hR (by simp [oddLo] at hj; omega)
  · rw [wythoff_minus_odd, mul_comm y]
    exact ediv_mul_eq_sub_iff hR (by simpa [oddLo] using hj)

/-- **(ratified).**  The even window contains an element `≡ py (mod q)`. -/
theorem exists_even_window (hq : 0 < q) (y : ℤ) :
    ∃ j, (evenLo s ≤ j ∧ j < evenLo s + q) ∧ (q : ℤ) ∣ p * y - j := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  refine ⟨evenLo s + (p * y - evenLo s) % q, ⟨?_, ?_⟩, ?_⟩
  · have := Int.emod_nonneg (p * y - evenLo s) hq'.ne'; omega
  · have := Int.emod_lt_of_pos (p * y - evenLo s) hq'; omega
  · exact ⟨(p * y - evenLo s) / q, by
      have := Int.mul_ediv_add_emod (p * y - evenLo s) q; linarith⟩

/-- **(ratified).**  The odd window contains an element `≡ py (mod R)`. -/
theorem exists_odd_window (hqp : q < p) (y : ℤ) :
    ∃ j, (oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) ∧ ((p : ℤ) - q) ∣ p * y - j := by
  have hR : (0 : ℤ) < (p : ℤ) - q := by omega
  refine ⟨oddLo s + (p * y - oddLo s) % ((p : ℤ) - q), ⟨?_, ?_⟩, ?_⟩
  · have := Int.emod_nonneg (p * y - oddLo s) hR.ne'; omega
  · have := Int.emod_lt_of_pos (p * y - oddLo s) hR; omega
  · exact ⟨(p * y - oddLo s) / ((p : ℤ) - q), by
      have := Int.mul_ediv_add_emod (p * y - oddLo s) ((p : ℤ) - q); linarith⟩

end Window

/-! ## Class-drop machinery

A closed set that contains a whole residue class mod `K₁` contains the class of the image mod
`K₂` whenever `f` is affine from steps of `K₁` to steps of `K₂` with a multiplier coprime to
`M / K₂` (`ClassIn.drop`).  The same lemma, with `K₁ = K₂ = M'`, transports full fibers over
`ZMod M'` along the edges mod `M'`; with `K₁ = ℓ^{j+1} M'`, `K₂ = ℓ^j M'` it drops the level by
one.  Every lift (A₂, B, A, D) is an instance. -/

section Machinery

variable {M : ℕ}

/-- `C` contains the whole class of `x` mod `K` (read in `ZMod M`). -/
def ClassIn (C : Set (ZMod M)) (K x : ℤ) : Prop :=
  ∀ t : ℤ, ((x + K * t : ℤ) : ZMod M) ∈ C

theorem ClassIn.shift {C : Set (ZMod M)} {K x : ℤ} (h : ClassIn C K x) (k : ℤ) :
    ClassIn C K (x + K * k) := fun t => by
  have := h (k + t)
  rwa [show x + K * (k + t) = x + K * k + K * t by ring] at this

theorem ClassIn.of_dvd {C : Set (ZMod M)} {K x x' : ℤ} (h : ClassIn C K x) (hd : K ∣ x' - x) :
    ClassIn C K x' := by
  obtain ⟨k, hk⟩ := hd
  rw [show x' = x + K * k by linarith]
  exact h.shift k

theorem ClassIn.mem {C : Set (ZMod M)} {K x : ℤ} (h : ClassIn C K x) : ((x : ℤ) : ZMod M) ∈ C := by
  simpa using h 0

/-- Coverage: `K · (B · v)` hits every multiple of `K` mod `M = K N` when `B` is coprime to
`N`. -/
theorem exists_cover {K B N : ℤ} (hKN : (M : ℤ) = K * N) (hB : IsCoprime B N) (t : ℤ) :
    ∃ v, ((K * (B * v) : ℤ) : ZMod M) = ((K * t : ℤ) : ZMod M) := by
  obtain ⟨a, b, hab⟩ := hB
  refine ⟨a * t, (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨b * t, ?_⟩⟩
  rw [hKN]
  linear_combination (-(K * t)) * hab

/-- **The drop lemma.** -/
theorem ClassIn.drop {f : ℤ → ℤ} {C : Set (ZMod M)} (hC : ResidueClosed f M C)
    {K₁ K₂ A B N x : ℤ} (hx : ClassIn C K₁ x)
    (hf : ∀ v, f (x + K₁ * (A * v)) = f x + K₂ * (B * v))
    (hKN : (M : ℤ) = K₂ * N) (hB : IsCoprime B N) : ClassIn C K₂ (f x) := by
  intro t
  obtain ⟨v, hv⟩ := exists_cover hKN hB t
  have := hC _ (hx (A * v))
  rwa [hf, Int.cast_add, hv, ← Int.cast_add] at this

/-- A point of `C` is a class mod `M`. -/
theorem classIn_self {C : Set (ZMod M)} {a : ZMod M} (ha : a ∈ C) : ClassIn C M (a.cast : ℤ) :=
  fun t => by simpa using ha

/-- Descent through the levels `ℓ^j M'`: if every class mod `ℓ^{j+1} M'` in `C` yields a class
mod `ℓ^j M'` in `C`, a nonempty `C` contains a class mod `M'`. -/
theorem exists_classIn_of_step {C : Set (ZMod M)} {ℓ M' : ℤ} {e : ℕ}
    (hM : (M : ℤ) = ℓ ^ e * M')
    (hstep : ∀ j, j < e → ∀ x, ClassIn C (ℓ ^ (j + 1) * M') x → ∃ x', ClassIn C (ℓ ^ j * M') x')
    (hne : C.Nonempty) : ∃ x, ClassIn C M' x := by
  obtain ⟨a, ha⟩ := hne
  suffices h : ∀ i, i ≤ e → ∃ x, ClassIn C (ℓ ^ (e - i) * M') x by simpa using h e le_rfl
  intro i
  induction i with
  | zero => intro _; exact ⟨_, by rw [Nat.sub_zero, ← hM]; exact classIn_self ha⟩
  | succ i ih =>
    intro hi
    obtain ⟨x, hx⟩ := ih (by omega)
    exact hstep (e - (i + 1)) (by omega) x (by rwa [show e - (i + 1) + 1 = e - i by omega])

/-- **The lift.**  If `f` is residue-transitive mod `M'`, carries full classes mod `M'` to full
classes mod `M'`, and every nonempty closed set mod `M` contains a full class mod `M'`, then `f`
is residue-transitive mod `M`. -/
theorem residueTransitive_of_classIn {f : ℤ → ℤ} {M' : ℕ} (hT : ResidueTransitive f M')
    (hfib : ∀ C : Set (ZMod M), ResidueClosed f M C → ∀ n, ClassIn C M' n → ClassIn C M' (f n))
    (hdrop : ∀ C : Set (ZMod M), ResidueClosed f M C → C.Nonempty → ∃ x, ClassIn C M' x) :
    ResidueTransitive f M := by
  rw [residueTransitive_iff_closed]
  intro C hC
  by_cases hne : C.Nonempty
  · right
    obtain ⟨x, hx⟩ := hdrop C hC hne
    let T : Set (ZMod M') := {b | ∃ z : ℤ, (z : ZMod M') = b ∧ ClassIn C M' z}
    have hTc : ResidueClosed f M' T := by
      rintro n ⟨z, hz, hzC⟩
      exact ⟨f n, rfl, hfib C hC n (hzC.of_dvd ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hz))⟩
    have hxT : (x : ZMod M') ∈ T := ⟨x, rfl, hx⟩
    rcases (residueTransitive_iff_closed f M').1 hT T hTc with h0 | h1
    · rw [h0] at hxT; exact absurd hxT (Set.notMem_empty _)
    · refine Set.eq_univ_of_forall fun a => ?_
      have haT : (((a.cast : ℤ) : ZMod M') ∈ T) := by rw [h1]; trivial
      obtain ⟨z, hz, hzC⟩ := haT
      have := (hzC.of_dvd ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hz)).mem
      simpa using this
  · left; exact Set.not_nonempty_iff_eq_empty.mp hne

end Machinery

/-! ## Pieces of `W` and `W⁻¹` -/

section PiecesInv

variable (s : Side) {p q : ℕ}

/-- The branch divisor of `n`: `q` on evens, `R = p − q` on odds. -/
def branchQ (p q : ℕ) (n : ℤ) : ℤ := if n % 2 = 0 then (q : ℤ) else (p : ℤ) - q

theorem wythoff_add_piece (hq : 0 < q) (hqp : q < p) (n m : ℤ) :
    wythoff s p q (n + 2 * branchQ p q n * m) = wythoff s p q n + p * m := by
  unfold branchQ
  split_ifs with h
  · exact wythoff_add_even s hq h m
  · exact wythoff_add_odd s hqp (by omega) m

/-- `W⁻¹(m + py) = W⁻¹ m + 2Qy` (the pieces `c + pℤ ↦ a + 2Qℤ`). -/
theorem wythoffInv_add_piece (hq : 0 < q) (hqp : q < p) (m y : ℤ) :
    wythoffInv s p q (m + p * y) =
      wythoffInv s p q m + 2 * branchQ p q (wythoffInv s p q m) * y := by
  have hm : wythoff s p q (wythoffInv s p q m) = m := wythoff_wythoffInv s hq hqp m
  rw [← wythoffInv_wythoff s hq hqp (wythoffInv s p q m + 2 * branchQ p q _ * y),
    wythoff_add_piece s hq hqp, hm]

theorem branchQ_pos (hq : 0 < q) (hqp : q < p) (n : ℤ) : 0 < branchQ p q n := by
  unfold branchQ; split_ifs <;> omega

/-- Every odd prime power coprime to `q` and `R` is coprime to the branch divisor. -/
theorem isCoprime_branchQ {a : ℤ} (hq : IsCoprime a q) (hR : IsCoprime a ((p : ℤ) - q))
    (n : ℤ) : IsCoprime a (branchQ p q n) := by
  unfold branchQ; split_ifs <;> assumption

end PiecesInv

/-! ## Edge realization and the translation argument (bases B0, B1) -/

section Edges

variable (s : Side) {p q : ℕ}

/-- Every `j` of the even window is realized along `y + Lℤ` when `gcd(pL, q) = 1`. -/
theorem exists_even_rep (hq : 0 < q) {L : ℤ} (hL : IsCoprime ((p : ℤ) * L) q) (y j : ℤ)
    (hj : evenLo s ≤ j ∧ j < evenLo s + q) :
    ∃ t, wythoff s p q (2 * (y + L * t)) * q = p * (y + L * t) - j := by
  obtain ⟨a, b, hab⟩ := hL
  refine ⟨a * (j - p * y), (wythoff_even_window s hq _ j hj).2 ⟨(p * y - j) * b, ?_⟩⟩
  linear_combination (j - p * y) * hab

/-- Every `j` of the odd window is realized along `y + Lℤ` when `gcd(pL, R) = 1`. -/
theorem exists_odd_rep (hqp : q < p) {L : ℤ} (hL : IsCoprime ((p : ℤ) * L) ((p : ℤ) - q))
    (y j : ℤ) (hj : oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) :
    ∃ t, wythoff s p q (2 * (y + L * t) - 1) * ((p : ℤ) - q) = p * (y + L * t) - j := by
  obtain ⟨a, b, hab⟩ := hL
  refine ⟨a * (j - p * y), (wythoff_odd_window s hqp _ j hj).2 ⟨(p * y - j) * b, ?_⟩⟩
  linear_combination (j - p * y) * hab

variable {M : ℕ}

/-- Even edge: `2y → z` mod `M` whenever `z q = py − j`, `j` in the even window. -/
theorem residueEdge_even (hq : 0 < q) {L : ℤ} (hL : IsCoprime ((p : ℤ) * L) q)
    (hL2 : (M : ℤ) ∣ 2 * L) (hpL : (M : ℤ) ∣ p * L) (hqu : IsUnit (q : ZMod M)) (y j : ℤ)
    (hj : evenLo s ≤ j ∧ j < evenLo s + q) (z : ZMod M) (hz : z * q = p * y - j) :
    ResidueEdge (wythoff s p q) M ((2 * y : ℤ) : ZMod M) z := by
  obtain ⟨t, ht⟩ := exists_even_rep s hq hL y j hj
  obtain ⟨c, hc⟩ := hL2
  obtain ⟨d, hd⟩ := hpL
  refine ⟨2 * (y + L * t), ?_, ?_⟩
  · rw [show 2 * (y + L * t) = 2 * y + 2 * L * t by ring, hc]; simp
  · apply hqu.mul_right_cancel
    have := congrArg (fun w : ℤ => (w : ZMod M)) ht
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast] at this
    rw [this, hz, mul_add, ← mul_assoc, show ((p : ZMod M) * (L : ZMod M)) = ((p * L : ℤ) : ZMod M)
      by push_cast; ring, hd]
    simp

/-- Odd edge: `2y − 1 → z` mod `M` whenever `z R = py − j`, `j` in the odd window. -/
theorem residueEdge_odd (hqp : q < p) {L : ℤ} (hL : IsCoprime ((p : ℤ) * L) ((p : ℤ) - q))
    (hL2 : (M : ℤ) ∣ 2 * L) (hpL : (M : ℤ) ∣ p * L) (hRu : IsUnit ((p : ZMod M) - q))
    (y j : ℤ) (hj : oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)) (z : ZMod M)
    (hz : z * ((p : ZMod M) - q) = p * y - j) :
    ResidueEdge (wythoff s p q) M ((2 * y - 1 : ℤ) : ZMod M) z := by
  obtain ⟨t, ht⟩ := exists_odd_rep s hqp hL y j hj
  obtain ⟨c, hc⟩ := hL2
  obtain ⟨d, hd⟩ := hpL
  refine ⟨2 * (y + L * t) - 1, ?_, ?_⟩
  · rw [show 2 * (y + L * t) - 1 = 2 * y - 1 + 2 * L * t by ring, hc]; simp
  · apply hRu.mul_right_cancel
    have := congrArg (fun w : ℤ => (w : ZMod M)) ht
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast] at this
    rw [this, hz, mul_add, ← mul_assoc,
      show ((p : ZMod M) * (L : ZMod M)) = ((p * L : ℤ) : ZMod M) by push_cast; ring, hd]
    simp

end Edges

section Translate

variable {M : ℕ}

theorem affine_injective {R : Type*} [CommRing R] (a b : Rˣ) (c : R) :
    Function.Injective (fun x : R => (↑a * x - c) * ↑b) := by
  intro x x' h
  have h' : (↑a * x - c) * ↑b * ↑b⁻¹ = (↑a * x' - c) * ↑b * ↑b⁻¹ := by
    simp only at h; rw [h]
  rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one, mul_one, sub_left_inj] at h'
  exact a.isUnit.mul_left_cancel h'

/-- **The translation argument.**  If the residue digraph of `f` mod `M` contains the graph of an
injective `g` and of `g − u` for a unit `u`, then `f` is residue-transitive mod `M`: a closed `C`
is mapped onto itself by `g`, so `z ∈ C ⇒ z − u ∈ C`, and `u` generates `ZMod M`. -/
theorem residueTransitive_of_translate [NeZero M] {f : ℤ → ℤ} (g : ZMod M → ZMod M)
    (hg : Function.Injective g) (u : ZMod M) (hu : IsUnit u)
    (h1 : ∀ x, ResidueEdge f M x (g x)) (h2 : ∀ x, ResidueEdge f M x (g x - u)) :
    ResidueTransitive f M := by
  rw [residueTransitive_iff_closed]
  intro C hC
  rw [residueClosed_iff_edge] at hC
  by_cases hne : C.Nonempty
  · right
    obtain ⟨a, ha⟩ := hne
    have hmaps : Set.MapsTo g C C := fun x hx => hC _ _ hx (h1 x)
    have hbij := (Set.toFinite C).injOn_iff_bijOn_of_mapsTo hmaps |>.1 hg.injOn
    have hstep : ∀ z ∈ C, z - u ∈ C := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hz
      exact hC _ _ hx (h2 x)
    have hk : ∀ k : ℕ, a - k * u ∈ C := by
      intro k
      induction k with
      | zero => simpa using ha
      | succ k ih => have := hstep _ ih; rwa [Nat.cast_succ, add_mul, one_mul, ← sub_sub]
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨v, rfl⟩ := hu
    have := hk ((a - b) * ↑v⁻¹).val
    rwa [ZMod.natCast_zmod_val, mul_assoc, Units.inv_mul, mul_one, sub_sub_cancel] at this
  · left; exact Set.not_nonempty_iff_eq_empty.mp hne

end Translate

/-! ## Lift helpers -/

section LiftHelpers

variable (s : Side) {p q : ℕ}

theorem isCoprime_of_odd {a : ℤ} (ha : Odd a) : IsCoprime a 2 := by
  obtain ⟨k, rfl⟩ := ha; exact ⟨1, -k, by ring⟩

/-- Chinese remainder in the form used for routing: `n + a t` can be moved into any class
mod `b`. -/
theorem exists_crt {a b : ℤ} (hab : IsCoprime a b) (n z : ℤ) : ∃ t, b ∣ n + a * t - z := by
  obtain ⟨u, v, huv⟩ := hab
  exact ⟨u * (z - n), ⟨(n - z) * v, by linear_combination (z - n) * huv⟩⟩

/-- `W` along a scaled piece step. -/
theorem wythoff_add_scaled (hq : 0 < q) (hqp : q < p) (n K v : ℤ) :
    wythoff s p q (n + 2 * K * (branchQ p q n * v)) = wythoff s p q n + K * (p * v) := by
  rw [show n + 2 * K * (branchQ p q n * v) = n + 2 * branchQ p q n * (K * v) by ring,
    wythoff_add_piece s hq hqp]
  ring

/-- `W⁻¹` along a scaled piece step. -/
theorem wythoffInv_add_scaled (hq : 0 < q) (hqp : q < p) (m K v : ℤ) :
    wythoffInv s p q (m + p * (K * v)) =
      wythoffInv s p q m + K * (2 * branchQ p q (wythoffInv s p q m) * v) := by
  rw [wythoffInv_add_piece s hq hqp]; ring

theorem coe_wythoffPerm (hq : 0 < q) (hqp : q < p) :
    ⇑(wythoffPerm s hq hqp) = wythoff s p q := rfl

theorem coe_wythoffPerm_symm (hq : 0 < q) (hqp : q < p) :
    ⇑(wythoffPerm s hq hqp).symm = wythoffInv s p q := rfl

/-- Transitivity transfers between `W` and `W⁻¹`. -/
theorem residueTransitive_inv_iff (hq : 0 < q) (hqp : q < p) (M : ℕ) :
    ResidueTransitive (wythoffInv s p q) M ↔ ResidueTransitive (wythoff s p q) M := by
  rw [← coe_wythoffPerm_symm s hq hqp, ← coe_wythoffPerm s hq hqp]
  exact residueTransitive_symm_iff _ M

/-- An odd prime power is coprime to the modulus part it does not divide. -/
theorem isCoprime_pow_of_prime {ℓ M' : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M') (k : ℕ) :
    IsCoprime ((ℓ : ℤ) ^ k) M' :=
  (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)).pow_left

theorem pow_mul_split (ℓ M' : ℤ) {j e : ℕ} (hj : j ≤ e) :
    ℓ ^ e * M' = ℓ ^ j * M' * ℓ ^ (e - j) := by
  rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hj]

theorem odd_intCast {p : ℕ} (hp : Odd p) : Odd (p : ℤ) := by
  obtain ⟨k, rfl⟩ := hp; exact ⟨k, by push_cast; ring⟩

/-- An odd prime `ℓ ∣ p` is coprime to `2`, `q` and `R`, hence to every `2Q`. -/
theorem isCoprime_two_branchQ_of_dvd_p (hcop : Nat.Coprime p q) (hqp : q < p) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p) (n : ℤ) :
    IsCoprime (2 * branchQ p q n) (ℓ : ℤ) := by
  have h2 : IsCoprime (2 : ℤ) ℓ := by
    have := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Nat.prime_two hℓ).2 hℓ2.symm)
    simpa using this
  have hq : IsCoprime (ℓ : ℤ) q :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hℓp hcop)
  have hR : IsCoprime (ℓ : ℤ) ((p : ℤ) - q) := by
    have := Nat.isCoprime_iff_coprime.2
      (Nat.Coprime.coprime_dvd_left hℓp ((Nat.coprime_self_sub_right hqp.le).2 hcop))
    rwa [Nat.cast_sub hqp.le] at this
  exact h2.mul_left (isCoprime_branchQ hq hR n).symm

/-- For even `p`, both branch divisors are odd. -/
theorem isCoprime_branchQ_two (hp : Even p) (hcop : Nat.Coprime p q) (hqp : q < p) (n : ℤ) :
    IsCoprime (branchQ p q n) 2 := by
  have hq2 := odd_of_even_coprime hp hcop
  obtain ⟨r, hr⟩ := hp
  apply isCoprime_of_odd
  unfold branchQ
  split_ifs
  · exact ⟨(q / 2 : ℕ), by omega⟩
  · exact ⟨((p - q) / 2 : ℕ), by omega⟩

end LiftHelpers

/-! ## Assembly (H5) -/

section Assembly

/-- **Assembly.**  Strong induction on `M`: while some prime `ℓ ∣ M` admits a lift, split
`M = ℓ^e M'` with `ℓ ∤ M'` and recurse on `M' < M`; otherwise `M` is a base modulus.  `S`
(closed under divisors) restricts the moduli, e.g. to odd ones. -/
theorem residueTransitive_of_lifts {f : ℤ → ℤ} (S : ℕ → Prop) (hS : ∀ M d, S M → d ∣ M → S d)
    (good : ℕ → Prop)
    (hlift : ∀ ℓ M', ℓ.Prime → good ℓ → 0 < M' → ¬ ℓ ∣ M' → S M' →
      ResidueTransitive f M' → ∀ e, ResidueTransitive f (ℓ ^ e * M'))
    (hbase : ∀ M, 0 < M → S M → (∀ ℓ, ℓ.Prime → ℓ ∣ M → ¬ good ℓ) → ResidueTransitive f M) :
    ∀ M, 0 < M → S M → ResidueTransitive f M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM hSM
    by_cases hex : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ M ∧ good ℓ
    · obtain ⟨ℓ, hℓ, hℓM, hg⟩ := hex
      obtain ⟨e, M', hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' ℓ hℓ.ne_one
      have hM'pos : 0 < M' := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
      have he : e ≠ 0 := by rintro rfl; simp at hℓM; exact hndvd hℓM
      have hlt : M' < ℓ ^ e * M' := by
        have := Nat.one_lt_pow he hℓ.one_lt; nlinarith
      have hSM' := hS _ _ hSM (dvd_mul_left M' (ℓ ^ e))
      exact hlift ℓ M' hℓ hg hM'pos hndvd hSM' (ih M' hlt hM'pos hSM') e
    · exact hbase M hM hSM (fun ℓ hℓ hd hg => hex ⟨ℓ, hℓ, hd, hg⟩)

/-- A modulus none of whose primes is `2` or divides `pqR` is coprime to `2pqR`. -/
theorem coprime_of_primes {p q M : ℕ}
    (h : ∀ ℓ, ℓ.Prime → ℓ ∣ M → ¬ (ℓ = 2 ∨ ℓ ∣ p ∨ ℓ ∣ q * (p - q))) :
    Nat.Coprime M (2 * p * q * (p - q)) := by
  refine Nat.coprime_of_dvd fun k hk hkM hkd => h k hk hkM ?_
  rcases (Nat.Prime.dvd_mul hk).1 hkd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hk).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hk).1 h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 h3)
      · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (dvd_mul_of_dvd_left h2 _))
  · exact Or.inr (Or.inr (dvd_mul_of_dvd_right h1 _))

end Assembly

/-! ## The counting step of (B1) -/

section Counting

/-- **Counting.**  Two parity classes, and for each parity `β` a family of maps `H β j`
(`j ∈ J β`), injective on parity `β`, sending the `β`-part of `C` into the `j`-part of `C`.
If `J 0` has an odd index and `J 1` an even one, the two parts of `C` have the same size, so each
`H β j` maps the `β`-part of `C` *onto* the `j`-part of `C`. -/
theorem exists_preimage_of_counting {X : Type*} [Finite X] (φ : X → ZMod 2) (C : Set X)
    (H : ZMod 2 → ℤ → X → X) (J : ZMod 2 → Set ℤ)
    (hmaps : ∀ β j, j ∈ J β → ∀ x ∈ C, φ x = β → H β j x ∈ C ∧ φ (H β j x) = j)
    (hinj : ∀ β j, j ∈ J β → Set.InjOn (H β j) {x | φ x = β})
    (h01 : ∃ j ∈ J 0, (j : ZMod 2) = 1) (h10 : ∃ j ∈ J 1, (j : ZMod 2) = 0)
    (β : ZMod 2) (j : ℤ) (hj : j ∈ J β) (z : X) (hz : z ∈ C) (hzj : φ z = j) :
    ∃ x ∈ C, φ x = β ∧ H β j x = z := by
  let S : ZMod 2 → Set X := fun b => {x | x ∈ C ∧ φ x = b}
  have hle : ∀ b j, j ∈ J b → (S b).ncard ≤ (S (j : ZMod 2)).ncard := fun b j hj =>
    Set.ncard_le_ncard_of_injOn (H b j) (fun x hx => hmaps b j hj x hx.1 hx.2)
      ((hinj b j hj).mono fun x hx => hx.2)
  obtain ⟨j0, hj0, hj01⟩ := h01
  obtain ⟨j1, hj1, hj10⟩ := h10
  have heq : (S 0).ncard = (S 1).ncard :=
    le_antisymm (hj01 ▸ hle 0 j0 hj0) (hj10 ▸ hle 1 j1 hj1)
  have hall : ∀ b b', (S b).ncard = (S b').ncard := by
    intro b b'
    rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases b' with rfl | rfl
    · rfl
    · exact heq
    · exact heq.symm
    · rfl
  have himg : H β j '' S β = S j := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩; exact hmaps β j hj x hx.1 hx.2
    · rw [Set.InjOn.ncard_image ((hinj β j hj).mono fun x hx => hx.2)]; exact (hall _ _).le
  have hzS : z ∈ S j := ⟨hz, hzj⟩
  rw [← himg] at hzS
  obtain ⟨x, hx, rfl⟩ := hzS
  exact ⟨x, hx.1, hx.2, rfl⟩

/-- A set closed under subtracting a unit is empty or everything. -/
theorem eq_univ_of_sub_mem {M : ℕ} [NeZero M] {C : Set (ZMod M)} {u : ZMod M} (hu : IsUnit u)
    {a : ZMod M} (ha : a ∈ C) (hstep : ∀ z ∈ C, z - u ∈ C) : C = Set.univ := by
  have hk : ∀ k : ℕ, a - k * u ∈ C := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih => have := hstep _ ih; rwa [Nat.cast_succ, add_mul, one_mul, ← sub_sub]
  refine Set.eq_univ_of_forall fun b => ?_
  obtain ⟨v, rfl⟩ := hu
  have := hk ((a - b) * ↑v⁻¹).val
  rwa [ZMod.natCast_zmod_val, mul_assoc, Units.inv_mul, mul_one, sub_sub_cancel] at this

end Counting

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
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    have h1 := Nat.coprime_zero_left _ |>.1 hM₀
    have : 1 ≤ q * (p - q) := Nat.mul_pos hq (by omega)
    have : 2 * 3 ≤ 2 * p * (q * (p - q)) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp3) this; simpa using this
    rw [← mul_assoc] at this; omega
  have : NeZero M₀ := ⟨hM0⟩
  have hcd : ∀ d, d ∣ 2 * p * q * (p - q) → Nat.Coprime d M₀ := fun d hd =>
    (hM₀.coprime_dvd_right hd).symm
  have h2 := hcd 2 ⟨p * q * (p - q), by ring⟩
  have hqM := hcd q ⟨2 * p * (p - q), by ring⟩
  have hRM := hcd (p - q) ⟨2 * p * q, by ring⟩
  have hRc : ((p - q : ℕ) : ℤ) = (p : ℤ) - q := by omega
  let u2 := ZMod.unitOfCoprime 2 h2
  let uq := ZMod.unitOfCoprime q hqM
  let uR := ZMod.unitOfCoprime (p - q) hRM
  have hu2 : (u2 : ZMod M₀) = 2 := by simp [u2]
  have huq : (uq : ZMod M₀) = q := by simp [uq]
  have huR : (uR : ZMod M₀) = (p : ZMod M₀) - q := by simp [uR, Nat.cast_sub hqp.le]
  have hLq : IsCoprime ((p : ℤ) * (M₀ : ℤ)) q := by
    rw [← Nat.cast_mul]; exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left hcop hqM.symm)
  have hLR : IsCoprime ((p : ℤ) * M₀) ((p : ℤ) - q) := by
    rw [← Nat.cast_mul, ← hRc]
    exact Nat.isCoprime_iff_coprime.2
      (Nat.Coprime.mul_left ((Nat.coprime_self_sub_right hqp.le).2 hcop) hRM.symm)
  have hL2 : (M₀ : ℤ) ∣ 2 * M₀ := dvd_mul_left _ _
  have hpL : (M₀ : ℤ) ∣ p * M₀ := dvd_mul_left _ _
  -- `y := x / 2`
  have hy : ∀ x : ZMod M₀, (((2 * ((x * ↑u2⁻¹ : ZMod M₀).cast : ℤ)) : ℤ) : ZMod M₀) = x := by
    intro x
    rw [Int.cast_mul, ZMod.intCast_zmod_cast, Int.cast_ofNat, ← hu2, mul_left_comm,
      Units.mul_inv, mul_one]
  have hy' : ∀ x : ZMod M₀,
      (((2 * ((x * ↑u2⁻¹ + ↑u2⁻¹ : ZMod M₀).cast : ℤ) - 1 : ℤ)) : ZMod M₀) = x := by
    intro x
    rw [Int.cast_sub, Int.cast_mul, ZMod.intCast_zmod_cast, Int.cast_ofNat, Int.cast_one, ← hu2,
      mul_add, mul_left_comm, Units.mul_inv, mul_one, add_sub_cancel_right]
  let up := ZMod.unitOfCoprime p (hcd p ⟨2 * q * (p - q), by ring⟩)
  have hup : (up : ZMod M₀) = p := by simp [up]
  rcases (show 2 ≤ q ∨ 2 ≤ p - q by omega) with hq2 | hR2
  · -- even branch: `x ↦ (p x / 2 − j) / q`
    have edge : ∀ x : ZMod M₀, ∀ j : ℤ, evenLo s ≤ j ∧ j < evenLo s + q →
        ResidueEdge (wythoff s p q) M₀ x ((↑(up * u2⁻¹) * x - j) * ↑uq⁻¹) := by
      intro x j hj
      have := residueEdge_even s hq hLq hL2 hpL (by rw [← huq]; exact uq.isUnit)
        ((x * ↑u2⁻¹ : ZMod M₀).cast) j hj ((↑(up * u2⁻¹) * x - j) * ↑uq⁻¹)
        (by rw [ZMod.intCast_zmod_cast, ← huq, mul_assoc _ (↑uq⁻¹ : ZMod M₀), Units.inv_mul,
          mul_one, Units.val_mul, hup]; ring)
      rwa [hy] at this
    refine residueTransitive_of_translate _ (affine_injective (up * u2⁻¹) uq⁻¹ (evenLo s))
      (↑uq⁻¹) (Units.isUnit _) (fun x => edge x _ ⟨le_rfl, by omega⟩) (fun x => ?_)
    have := edge x (evenLo s + 1) ⟨by omega, by omega⟩
    convert this using 1; push_cast; ring
  · -- odd branch: `x ↦ (p (x + 1) / 2 − j) / R`
    have edge : ∀ x : ZMod M₀, ∀ j : ℤ, oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q) →
        ResidueEdge (wythoff s p q) M₀ x
          ((↑(up * u2⁻¹) * x - (j - ↑(up * u2⁻¹))) * ↑uR⁻¹) := by
      intro x j hj
      have := residueEdge_odd s hqp hLR hL2 hpL (by rw [← huR]; exact uR.isUnit)
        ((x * ↑u2⁻¹ + ↑u2⁻¹ : ZMod M₀).cast) j hj
        ((↑(up * u2⁻¹) * x - (j - ↑(up * u2⁻¹))) * ↑uR⁻¹)
        (by rw [ZMod.intCast_zmod_cast, ← huR, mul_assoc _ (↑uR⁻¹ : ZMod M₀), Units.inv_mul,
          mul_one, Units.val_mul, hup]; ring)
      rwa [hy'] at this
    refine residueTransitive_of_translate _
      (affine_injective (up * u2⁻¹) uR⁻¹ (oddLo s - ↑(up * u2⁻¹)))
      (↑uR⁻¹) (Units.isUnit _) (fun x => edge x _ ⟨le_rfl, by omega⟩) (fun x => ?_)
    have := edge x (oddLo s + 1) ⟨by omega, by omega⟩
    convert this using 1; push_cast; ring

/-- **(ratified).**  **Lemma B** (odd primes of `p`): lift `M' → ℓ^e M'` for an odd prime
`ℓ ∣ p`, `ℓ ∤ M'`; `W⁻¹` expands `ℓ`-adically.  Paper proof: note §3 Lemma B. -/
theorem residueTransitive_lift_dvd_p (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p) {M' : ℕ} (hM' : 0 < M')
    (hℓM : ¬ ℓ ∣ M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (ℓ ^ e * M') := by
  have hQ := isCoprime_two_branchQ_of_dvd_p hcop hqp hℓ hℓ2 hℓp
  obtain ⟨p₁, hp₁⟩ := hℓp
  rw [← residueTransitive_inv_iff s hq hqp]
  refine residueTransitive_of_classIn ((residueTransitive_inv_iff s hq hqp M').2 h)
    (fun C hC n hn => ?_) (fun C hC hne => ?_)
  · refine hn.drop hC (A := p) (B := 2 * branchQ p q (wythoffInv s p q n)) (N := ℓ ^ e)
      (fun v => ?_) (by push_cast; ring) (hQ _).pow_right
    rw [show n + (M' : ℤ) * (p * v) = n + p * (M' * v) by ring]
    exact wythoffInv_add_scaled s hq hqp n M' v
  · refine exists_classIn_of_step (ℓ := ℓ) (e := e) (by push_cast; ring)
      (fun j hj x hx => ⟨_, hx.drop hC (A := p₁) (B := 2 * branchQ p q (wythoffInv s p q x))
        (N := ℓ ^ (e - j)) (fun v => ?_) (by push_cast; exact pow_mul_split _ _ hj.le)
        (hQ _).pow_right⟩) hne
    rw [show x + (ℓ : ℤ) ^ (j + 1) * M' * (p₁ * v) = x + p * (ℓ ^ j * M' * v) by
      rw [hp₁]; push_cast; ring]
    exact wythoffInv_add_scaled s hq hqp x _ v

/-- **Lemma A, parametrized by the dropping parity `ε`.**  The `ε`-branch divisor is divisible
by `ℓ` (those pieces drop the `ℓ`-level), the other is coprime to `ℓ` (those pieces keep it).
A class with no `ε`-point is routed, at constant level, along a path mod `M'` to the residue
`ε`, whose classes always contain an `ε`-point. -/
theorem residueTransitive_lift_branch (hq : 0 < q) (hqp : q < p) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓp : IsCoprime (ℓ : ℤ) p) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hdrop : ∀ n, n % 2 = ε → (ℓ : ℤ) ∣ branchQ p q n)
    (hkeep : ∀ n, n % 2 ≠ ε → IsCoprime (ℓ : ℤ) (branchQ p q n))
    {M' : ℕ} (hℓM : ¬ ℓ ∣ M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (ℓ ^ e * M') := by
  have hpℓ : ∀ k : ℕ, IsCoprime (p : ℤ) ((ℓ : ℤ) ^ k) := fun k => hℓp.symm.pow_right
  have hℓM' : ∀ k : ℕ, IsCoprime ((ℓ : ℤ) ^ k) M' := isCoprime_pow_of_prime hℓ hℓM
  have hℓodd : Odd (ℓ : ℤ) := odd_intCast (hℓ.odd_of_ne_two hℓ2)
  have h2ℓ : ∀ k : ℕ, IsCoprime (2 : ℤ) ((ℓ : ℤ) ^ k) := fun k =>
    (isCoprime_of_odd hℓodd).symm.pow_right
  refine residueTransitive_of_classIn h (fun C hC n hn => ?_) (fun C hC hne => ?_)
  · refine hn.drop hC (A := 2 * branchQ p q n) (B := p) (N := ℓ ^ e) (fun v => ?_)
      (by push_cast; ring) (hpℓ e)
    rw [show n + (M' : ℤ) * (2 * branchQ p q n * v) = n + 2 * M' * (branchQ p q n * v) by ring]
    exact wythoff_add_scaled s hq hqp n M' v
  refine exists_classIn_of_step (ℓ := ℓ) (e := e) (by push_cast; ring) (fun j hj x hx => ?_) hne
  have hKN : ((ℓ ^ e * M' : ℕ) : ℤ) = (ℓ : ℤ) ^ j * M' * ℓ ^ (e - j) := by
    push_cast; exact pow_mul_split _ _ hj.le
  have hKN' : ((ℓ ^ e * M' : ℕ) : ℤ) = (ℓ : ℤ) ^ (j + 1) * M' * ℓ ^ (e - (j + 1)) := by
    push_cast; exact pow_mul_split _ _ hj
  -- a class containing an `ε`-point drops a level
  have hdropC : ∀ z, ClassIn C ((ℓ : ℤ) ^ (j + 1) * M') z → z % 2 = ε →
      ∃ x', ClassIn C ((ℓ : ℤ) ^ j * M') x' := by
    intro z hz hzε
    obtain ⟨Q₁, hQ₁⟩ := hdrop z hzε
    refine ⟨_, hz.drop hC (A := 2 * Q₁) (B := p) (N := ℓ ^ (e - j)) (fun v => ?_) hKN (hpℓ _)⟩
    rw [show z + (ℓ : ℤ) ^ (j + 1) * M' * (2 * Q₁ * v) =
      z + 2 * ((ℓ : ℤ) ^ j * M') * (branchQ p q z * v) by rw [hQ₁]; ring]
    exact wythoff_add_scaled s hq hqp z _ v
  by_contra hcon
  have hno : ∀ z, ClassIn C ((ℓ : ℤ) ^ (j + 1) * M') z → z % 2 ≠ ε := fun z hz hzε =>
    hcon (hdropC z hz hzε)
  let T : Set (ZMod M') := {b | ∃ z : ℤ, (z : ZMod M') = b ∧ ClassIn C ((ℓ : ℤ) ^ (j + 1) * M') z}
  have hTc : ResidueClosed (wythoff s p q) M' T := by
    rintro n ⟨z, hz, hzC⟩
    have hMz : (M' : ℤ) ∣ n - z := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hz
    by_cases hn : n % 2 = ε
    · exfalso
      obtain ⟨t, ht⟩ := exists_crt ((h2ℓ (j + 1)).mul_left (hℓM' (j + 1)).symm) n z
      have hK : (ℓ : ℤ) ^ (j + 1) * M' ∣ n + 2 * M' * t - z := (hℓM' (j + 1)).mul_dvd ht (by
        rw [show n + 2 * (M' : ℤ) * t - z = (n - z) + M' * (2 * t) by ring]
        exact hMz.add (dvd_mul_right _ _))
      refine hno _ (hzC.of_dvd hK) ?_
      rw [show n + 2 * (M' : ℤ) * t = n + 2 * (M' * t) by ring]; omega
    · have hQk := hkeep n hn
      have hcop' : IsCoprime (2 * branchQ p q n * M') ((ℓ : ℤ) ^ (j + 1)) :=
        ((h2ℓ _).mul_left hQk.symm.pow_right).mul_left (hℓM' _).symm
      obtain ⟨t, ht⟩ := exists_crt hcop' n z
      set n' := n + 2 * branchQ p q n * M' * t with hn'
      have hK : (ℓ : ℤ) ^ (j + 1) * M' ∣ n' - z := (hℓM' (j + 1)).mul_dvd ht (by
        rw [show n' - z = (n - z) + M' * (2 * branchQ p q n * t) by rw [hn']; ring]
        exact hMz.add (dvd_mul_right _ _))
      have hn'C := hzC.of_dvd hK
      have hpar : n' % 2 = n % 2 := by
        rw [hn', show 2 * branchQ p q n * M' * t = 2 * (branchQ p q n * M' * t) by ring]; omega
      have hQeq : branchQ p q n' = branchQ p q n := by unfold branchQ; rw [hpar]
      have hkeepC : ClassIn C ((ℓ : ℤ) ^ (j + 1) * M') (wythoff s p q n') := by
        refine hn'C.drop hC (A := 2 * branchQ p q n') (B := p) (N := ℓ ^ (e - (j + 1)))
          (fun v => ?_) hKN' (hpℓ _)
        rw [show n' + (ℓ : ℤ) ^ (j + 1) * M' * (2 * branchQ p q n' * v) =
          n' + 2 * ((ℓ : ℤ) ^ (j + 1) * M') * (branchQ p q n' * v) by ring]
        exact wythoff_add_scaled s hq hqp n' _ v
      refine ⟨wythoff s p q n', (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨-(p * t), ?_⟩,
        hkeepC⟩
      rw [hn', show n + 2 * branchQ p q n * M' * t = n + 2 * branchQ p q n * (M' * t) by ring,
        wythoff_add_piece s hq hqp]
      ring
  have hxT : (x : ZMod M') ∈ T := ⟨x, rfl, hx⟩
  rcases (residueTransitive_iff_closed _ M').1 h T hTc with h0 | h1
  · rw [h0] at hxT; exact hxT
  · obtain ⟨z, hz, hzC⟩ : ((ε : ℤ) : ZMod M') ∈ T := by rw [h1]; trivial
    have hMz : (M' : ℤ) ∣ z - ε := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hz
      rw [← dvd_neg, neg_sub] at this; exact this
    refine hno (z + (ℓ : ℤ) ^ (j + 1) * M' * (z - ε)) (hzC.shift _) ?_
    have h2 : (2 : ℤ) ∣ (z - ε) * (1 + (ℓ : ℤ) ^ (j + 1) * M') := by
      rcases Int.even_or_odd (M' : ℤ) with hev | hod
      · exact (hev.two_dvd.trans hMz).mul_right _
      · obtain ⟨k, hk⟩ := (hℓodd.pow (n := j + 1)).mul hod
        exact (show (2 : ℤ) ∣ 1 + (ℓ : ℤ) ^ (j + 1) * M' from ⟨k + 1, by rw [hk]; ring⟩).mul_left _
    rw [show (z - ε) * (1 + (ℓ : ℤ) ^ (j + 1) * M') =
      z - ε + (ℓ : ℤ) ^ (j + 1) * M' * (z - ε) by ring] at h2
    omega

/-- **(ratified).**  **Lemma A** (odd primes of `qR`): lift `M' → ℓ^e M'` for an odd prime
`ℓ ∣ qR`, `ℓ ∤ M'`; `W` expands `ℓ`-adically on one branch, routed through parity.  Paper proof:
note §3 Lemma A. -/
theorem residueTransitive_lift_dvd_qR (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓqR : ℓ ∣ q * (p - q)) {M' : ℕ} (hM' : 0 < M')
    (hℓM : ¬ ℓ ∣ M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (ℓ ^ e * M') := by
  have hqR : Nat.Coprime q (p - q) := (Nat.coprime_sub_self_right hqp.le).2 hcop.symm
  have hpR : Nat.Coprime p (p - q) := (Nat.coprime_self_sub_right hqp.le).2 hcop
  have hRc : ((p - q : ℕ) : ℤ) = (p : ℤ) - q := by omega
  rcases (Nat.Prime.dvd_mul hℓ).1 hℓqR with hℓq | hℓR
  · refine residueTransitive_lift_branch s hq hqp hℓ hℓ2
      (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hℓq hcop.symm)) (ε := 0)
      (Or.inl rfl) (fun n hn => ?_) (fun n hn => ?_) hℓM h e
    · unfold branchQ; rw [if_pos hn]; exact_mod_cast hℓq
    · unfold branchQ; rw [if_neg hn, ← hRc]
      exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hℓq hqR)
  · refine residueTransitive_lift_branch s hq hqp hℓ hℓ2
      (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hℓR hpR.symm)) (ε := 1)
      (Or.inr rfl) (fun n hn => ?_) (fun n hn => ?_) hℓM h e
    · unfold branchQ; rw [if_neg (by omega), ← hRc]; exact_mod_cast hℓR
    · unfold branchQ; rw [if_pos (by omega)]
      exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hℓR hqR.symm)

/-- **(ratified).**  **Lemma A₂** (`p` odd, the prime `2`): every piece `a + 2Qℤ ↦ c + pℤ`
drops the `2`-level.  Paper proof: note §3 Lemma A₂. -/
theorem residueTransitive_lift_two_of_odd (hp : Odd p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M' : ℕ} (hM' : Odd M') (h : ResidueTransitive (wythoff s p q) M') (e : ℕ) :
    ResidueTransitive (wythoff s p q) (2 ^ e * M') := by
  have hp2 : IsCoprime (p : ℤ) 2 := isCoprime_of_odd (odd_intCast hp)
  refine residueTransitive_of_classIn h (fun C hC n hn => ?_) (fun C hC hne => ?_)
  · refine hn.drop hC (A := 2 * branchQ p q n) (B := p) (N := 2 ^ e) (fun v => ?_)
      (by push_cast; ring) hp2.pow_right
    rw [show n + (M' : ℤ) * (2 * branchQ p q n * v) = n + 2 * M' * (branchQ p q n * v) by ring]
    exact wythoff_add_scaled s hq hqp n M' v
  · refine exists_classIn_of_step (ℓ := 2) (e := e) (by push_cast; ring)
      (fun j hj x hx => ⟨_, hx.drop hC (A := branchQ p q x) (B := p) (N := 2 ^ (e - j))
        (fun v => ?_) (by push_cast; exact pow_mul_split _ _ hj.le) hp2.pow_right⟩) hne
    rw [show x + (2 : ℤ) ^ (j + 1) * M' * (branchQ p q x * v) =
      x + 2 * (2 ^ j * M') * (branchQ p q x * v) by ring]
    exact wythoff_add_scaled s hq hqp x _ v

/-- **(ratified).**  **Theorem RT, odd `p`.**  `W_{p/q±}` is residue-transitive mod every
`M ≥ 1`.  Paper proof: (B0) mod `M₀`, then Lemma A₂, Lemma B, Lemma A one prime at a time. -/
theorem residueTransitive_of_odd (hp : Odd p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M : ℕ} (hM : 0 < M) : ResidueTransitive (wythoff s p q) M := by
  have hp3 : 3 ≤ p := by obtain ⟨k, rfl⟩ := hp; omega
  refine residueTransitive_of_lifts (fun _ => True) (fun _ _ _ _ => trivial)
    (fun ℓ => ℓ = 2 ∨ ℓ ∣ p ∨ ℓ ∣ q * (p - q)) ?_ ?_ M hM trivial
  · rintro ℓ M' hℓ hg hM' hℓM - hT e
    by_cases h2 : ℓ = 2
    · subst h2
      exact residueTransitive_lift_two_of_odd s hp hcop hq hqp
        (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hℓM)) hT e
    · rcases hg.resolve_left h2 with hℓp | hℓqR
      · exact residueTransitive_lift_dvd_p s hcop hq hqp hℓ h2 hℓp hM' hℓM hT e
      · exact residueTransitive_lift_dvd_qR s hcop hq hqp hℓ h2 hℓqR hM' hℓM hT e
  · intro M _ _ hgood
    exact residueTransitive_base_coprime s hp3 hcop hq hqp (coprime_of_primes hgood)

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
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hper
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hfwd
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  -- membership is `M`-periodic beyond `N₁`
  have hstep : ∀ k : ℕ, ∀ m, N₁ ≤ m → (m ∈ C ↔ m + M * k ∈ C) := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      rw [ih m hm, hN₁ (m + M * k) (by nlinarith)]
      push_cast; ring_nf
  have hperiod : ∀ m n, N₁ ≤ m → N₁ ≤ n → (M : ℤ) ∣ n - m → (m ∈ C ↔ n ∈ C) := by
    have key : ∀ m n, N₁ ≤ m → m ≤ n → (M : ℤ) ∣ n - m → (m ∈ C ↔ n ∈ C) := by
      rintro m n hm hmn ⟨k, hk⟩
      have hk0 : 0 ≤ k := by
        by_contra h; push Not at h; nlinarith
      rw [hstep k.toNat m hm, Int.toNat_of_nonneg hk0, show m + M * k = n by linarith]
    intro m n hm hn hd
    rcases le_total m n with h | h
    · exact key m n hm h hd
    · exact (key n m hn h (by rw [← dvd_neg, neg_sub]; exact hd)).symm
  set N := max N₁ N₂
  let D : Set (ZMod M) := {a | ∃ n : ℤ, N ≤ n ∧ (n : ZMod M) = a ∧ n ∈ C}
  have hD : ResidueClosed (wythoff s p q) M D := by
    rintro n ⟨m, hm, hmn, hmC⟩
    set k : ℤ := |N - n| + |N - wythoff s p q n| with hk
    have hk0 : 0 ≤ k := by positivity
    have hQ := branchQ_pos hq hqp n
    set n' := n + 2 * branchQ p q n * (M * k) with hn'
    have hW : wythoff s p q n' = wythoff s p q n + M * (p * k) := by
      rw [hn', wythoff_add_piece s hq hqp]; ring
    have hn'N : N ≤ n' := by
      have h1 : k ≤ (M : ℤ) * k := le_mul_of_one_le_left hk0 (by omega)
      have : k ≤ 2 * branchQ p q n * (M * k) :=
        h1.trans (le_mul_of_one_le_left (by linarith) (by linarith))
      have := le_abs_self (N - n); have := abs_nonneg (N - wythoff s p q n); linarith
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have hWN : N ≤ wythoff s p q n' := by
      have h1 : k ≤ (p : ℤ) * k := le_mul_of_one_le_left hk0 hp1
      have : k ≤ M * (p * k) := h1.trans (le_mul_of_one_le_left (by linarith) (by omega))
      have := le_abs_self (N - wythoff s p q n); have := abs_nonneg (N - n); linarith
    have hn'C : n' ∈ C := by
      refine (hperiod m n' (le_trans (le_max_left _ _) hm) (le_trans (le_max_left _ _) hn'N)
        ?_).1 hmC
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmn
      rw [show n' - m = (n - m) + M * (2 * branchQ p q n * k) by rw [hn']; ring]
      exact this.add (dvd_mul_right _ _)
    refine ⟨wythoff s p q n', hWN, ?_, hN₂ n' (le_trans (le_max_right _ _) hn'N) hn'C⟩
    rw [hW]; simp
  rcases (residueTransitive_iff_closed _ M).1 hRT D hD with h0 | h1
  · right
    refine Filter.eventually_atTop.2 ⟨N, fun n hn hnC => ?_⟩
    have : (n : ZMod M) ∈ D := ⟨n, hn, rfl, hnC⟩
    rw [h0] at this; exact this
  · left
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    obtain ⟨m, hm, hmn, hmC⟩ : (n : ZMod M) ∈ D := by rw [h1]; trivial
    exact (hperiod m n (le_trans (le_max_left _ _) hm) (le_trans (le_max_left _ _) hn)
      ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmn)).1 hmC

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
  obtain ⟨p', hp'⟩ : ∃ p', p = 2 * p' := ⟨p / 2, by obtain ⟨r, hr⟩ := hp; omega⟩
  have hq2 : q % 2 = 1 := odd_of_even_coprime hp hcop
  have hR2 : (p - q) % 2 = 1 := by omega
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    have h1 := Nat.coprime_zero_left _ |>.1 hM₀
    have : 1 ≤ q * (p - q) := Nat.mul_pos hq (by omega)
    have : 2 * 3 ≤ 2 * p * (q * (p - q)) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (show 3 ≤ p by omega)) this; simpa using this
    rw [← mul_assoc] at this; omega
  have hcd : ∀ d, d ∣ 2 * p * q * (p - q) → Nat.Coprime d M₀ := fun d hd =>
    (hM₀.coprime_dvd_right hd).symm
  set L := 2 ^ (e - 1) * M₀ with hLdef
  have hML : 2 ^ e * M₀ = 2 * L := by
    rw [hLdef, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
  rw [hML]
  have : NeZero (2 * L) := ⟨by rw [← hML]; positivity⟩
  have hodd2 : ∀ {d : ℕ}, d % 2 = 1 → Nat.Coprime d 2 := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.2 (by omega)).symm
  have hcopL : ∀ {d : ℕ}, d % 2 = 1 → d ∣ 2 * p * q * (p - q) → Nat.Coprime d L := fun hd hdd =>
    Nat.Coprime.mul_right ((hodd2 hd).pow_right _) (hcd _ hdd)
  have hqL := hcopL hq2 ⟨2 * p * (p - q), by ring⟩
  have hRL := hcopL hR2 ⟨2 * p * q, by ring⟩
  have hcopM : ∀ {d : ℕ}, d % 2 = 1 → Nat.Coprime d L → Nat.Coprime d (2 * L) := fun hd h =>
    Nat.Coprime.mul_right (hodd2 hd) h
  let uq := ZMod.unitOfCoprime q (hcopM hq2 hqL)
  let uR := ZMod.unitOfCoprime (p - q) (hcopM hR2 hRL)
  have huq : (uq : ZMod (2 * L)) = q := by simp [uq]
  have huR : (uR : ZMod (2 * L)) = (p : ZMod (2 * L)) - q := by simp [uR, Nat.cast_sub hqp.le]
  have hRc : ((p - q : ℕ) : ℤ) = (p : ℤ) - q := by omega
  have hLq : IsCoprime ((p : ℤ) * (L : ℤ)) q := by
    rw [← Nat.cast_mul]; exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left hcop hqL.symm)
  have hLR : IsCoprime ((p : ℤ) * L) ((p : ℤ) - q) := by
    rw [← Nat.cast_mul, ← hRc]
    exact Nat.isCoprime_iff_coprime.2
      (Nat.Coprime.mul_left ((Nat.coprime_self_sub_right hqp.le).2 hcop) hRL.symm)
  have hL2 : ((2 * L : ℕ) : ℤ) ∣ 2 * L := by push_cast; exact dvd_rfl
  have hpL : ((2 * L : ℕ) : ℤ) ∣ p * L := ⟨p', by rw [hp']; push_cast; ring⟩
  -- `p'` is coprime to `L` (here `p ≡ 2 (mod 4)` or `e = 1` is used)
  have hp'L : IsCoprime (p' : ℤ) L := by
    have hp'M : Nat.Coprime p' M₀ := hcd p' ⟨4 * q * (p - q), by rw [hp']; ring⟩
    refine Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_right ?_ hp'M)
    rcases h4 with h4 | rfl
    · exact (hodd2 (by omega)).pow_right _
    · simp
  have h2M : 2 ∣ 2 * L := dvd_mul_right 2 L
  let φ := ZMod.castHom h2M (ZMod 2)
  have hφ : ∀ n : ℤ, φ (n : ZMod (2 * L)) = (n : ZMod 2) := fun n => by simp [φ]
  have hφx : ∀ x : ZMod (2 * L), φ x = ((x.cast : ℤ) : ZMod 2) := fun x => by
    rw [← hφ, ZMod.intCast_zmod_cast]
  -- injectivity on a parity class
  have hcancel : ∀ d : ZMod (2 * L), φ d = 0 → (p' : ZMod (2 * L)) * d = 0 → d = 0 := by
    intro d hd0 hpd
    set D : ℤ := d.cast with hD
    have hDd : (D : ZMod (2 * L)) = d := ZMod.intCast_zmod_cast d
    rw [hφx, intCast_zmod2_eq_zero_iff] at hd0
    obtain ⟨k, hk⟩ : ∃ k, D = 2 * k := ⟨D / 2, by omega⟩
    rw [← hDd, ← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at hpd
    obtain ⟨c, hc⟩ := hpd
    have hLk : (L : ℤ) ∣ p' * k := ⟨c, by push_cast at hc; rw [hk] at hc; linarith⟩
    obtain ⟨c', hc'⟩ := hp'L.symm.dvd_of_dvd_mul_left hLk
    rw [← hDd, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c', by rw [hk, hc']; push_cast; ring⟩
  have hφq : φ (↑uq⁻¹ : ZMod (2 * L)) = 1 := by
    have := congrArg φ (Units.inv_mul uq)
    rwa [map_mul, map_one, huq, map_natCast, ZMod.natCast_eq_one_iff_odd.2 (Nat.odd_iff.2 hq2),
      mul_one] at this
  have hφR : φ (↑uR⁻¹ : ZMod (2 * L)) = 1 := by
    have := congrArg φ (Units.inv_mul uR)
    have huR' : (uR : ZMod (2 * L)) = ((p - q : ℕ) : ZMod (2 * L)) := by simp [uR]
    rwa [map_mul, map_one, huR', map_natCast,
      ZMod.natCast_eq_one_iff_odd.2 (Nat.odd_iff.2 hR2), mul_one] at this
  -- the edges `x → (p' x − j) / q` (even `x`) and `x → (p' (x + 1) − j) / R` (odd `x`)
  have edgeE : ∀ x : ZMod (2 * L), φ x = 0 → ∀ j : ℤ, evenLo s ≤ j ∧ j < evenLo s + q →
      ResidueEdge (wythoff s p q) (2 * L) x ((p' * x - j) * ↑uq⁻¹) := by
    intro x hx j hj
    have hDx : ((x.cast : ℤ) : ZMod (2 * L)) = x := ZMod.intCast_zmod_cast x
    rw [hφx, intCast_zmod2_eq_zero_iff] at hx
    have hy : ((2 * ((x.cast : ℤ) / 2) : ℤ) : ZMod (2 * L)) = x := by
      rw [show 2 * ((x.cast : ℤ) / 2) = x.cast by omega, hDx]
    have := residueEdge_even s hq hLq hL2 hpL (by rw [← huq]; exact uq.isUnit)
      ((x.cast : ℤ) / 2) j hj ((p' * x - j) * ↑uq⁻¹) (by
        rw [← huq, mul_assoc, Units.inv_mul, mul_one]
        conv_lhs => rw [← hy]
        rw [hp']; push_cast; ring)
    rwa [hy] at this
  have edgeO : ∀ x : ZMod (2 * L), φ x = 1 → ∀ j : ℤ,
      oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q) →
      ResidueEdge (wythoff s p q) (2 * L) x ((p' * (x + 1) - j) * ↑uR⁻¹) := by
    intro x hx j hj
    have hDx : ((x.cast : ℤ) : ZMod (2 * L)) = x := ZMod.intCast_zmod_cast x
    rw [hφx, intCast_zmod2_eq_one_iff] at hx
    have hy : ((2 * (((x.cast : ℤ) + 1) / 2) - 1 : ℤ) : ZMod (2 * L)) = x := by
      rw [show 2 * (((x.cast : ℤ) + 1) / 2) - 1 = x.cast by omega, hDx]
    have := residueEdge_odd s hqp hLR hL2 hpL (by rw [← huR]; exact uR.isUnit)
      (((x.cast : ℤ) + 1) / 2) j hj ((p' * (x + 1) - j) * ↑uR⁻¹) (by
        rw [← huR, mul_assoc, Units.inv_mul, mul_one]
        conv_lhs => rw [← hy]
        rw [hp']; push_cast; ring)
    rwa [hy] at this
  let H : ZMod 2 → ℤ → ZMod (2 * L) → ZMod (2 * L) := fun β j x =>
    if β = 0 then (p' * x - j) * ↑uq⁻¹ else (p' * (x + 1) - j) * ↑uR⁻¹
  let J : ZMod 2 → Set ℤ := fun β => if β = 0 then {j | evenLo s ≤ j ∧ j < evenLo s + q}
    else {j | oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q)}
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hH0 : ∀ j x, H 0 j x = (p' * x - j) * ↑uq⁻¹ := fun j x => if_pos rfl
  have hH1 : ∀ j x, H 1 j x = (p' * (x + 1) - j) * ↑uR⁻¹ := fun j x => if_neg h10
  have hJ0 : ∀ j, j ∈ J 0 ↔ evenLo s ≤ j ∧ j < evenLo s + q := fun j => by
    simp only [J, if_pos rfl]; rfl
  have hJ1 : ∀ j, j ∈ J 1 ↔ oddLo s ≤ j ∧ j < oddLo s + ((p : ℤ) - q) := fun j => by
    simp only [J, if_neg h10]; rfl
  rw [residueTransitive_iff_closed]
  intro C hC
  rw [residueClosed_iff_edge] at hC
  have hmaps : ∀ β j, j ∈ J β → ∀ x ∈ C, φ x = β → H β j x ∈ C ∧ φ (H β j x) = j := by
    intro β j hj x hxC hxβ
    rcases zmod2_cases β with rfl | rfl
    · rw [hJ0] at hj
      rw [hH0]
      refine ⟨hC _ _ hxC (edgeE x hxβ j hj), ?_⟩
      rw [map_mul, map_sub, map_mul, map_natCast, map_intCast, hxβ, hφq]
      simp [ZMod.neg_eq_self_mod_two]
    · rw [hJ1] at hj
      rw [hH1]
      refine ⟨hC _ _ hxC (edgeO x hxβ j hj), ?_⟩
      rw [map_mul, map_sub, map_mul, map_natCast, map_intCast, map_add, map_one, hxβ, hφR,
        show (1 + 1 : ZMod 2) = 0 by decide]
      simp [ZMod.neg_eq_self_mod_two]
  have hinj : ∀ β j, j ∈ J β → Set.InjOn (H β j) {x | φ x = β} := by
    intro β j _ x hx x' hx' heq
    have hsub : φ (x - x') = 0 := by
      rw [map_sub]; rw [show φ x = β from hx, show φ x' = β from hx', sub_self]
    rw [← sub_eq_zero]
    refine hcancel _ hsub ?_
    rcases zmod2_cases β with rfl | rfl
    · rw [hH0, hH0] at heq
      have := sub_left_injective ((Units.mul_left_inj uq⁻¹).1 heq)
      rw [mul_sub, this, sub_self]
    · rw [hH1, hH1] at heq
      have := sub_left_injective ((Units.mul_left_inj uR⁻¹).1 heq)
      rw [mul_add, mul_add] at this
      rw [mul_sub, add_right_cancel this, sub_self]
  have hq1 : s = .plus → 2 ≤ q := fun h => by have := hna; simp [h] at this; omega
  have hR1 : s = .plus → 2 ≤ p - q := fun h => by have := hna; simp [h] at this; omega
  have hJ01 : ∃ j ∈ J 0, (j : ZMod 2) = 1 := ⟨1, (hJ0 1).2 (by
    cases s
    · have := hq1 rfl; simp [evenLo]; omega
    · simp [evenLo]; omega), by simp⟩
  have hJ10 : ∃ j ∈ J 1, (j : ZMod 2) = 0 := by
    cases s
    · exact ⟨2, (hJ1 2).2 (by have := hR1 rfl; simp [oddLo]; omega), by decide⟩
    · exact ⟨0, (hJ1 0).2 (by simp [oddLo]; omega), by simp⟩
  by_cases hne : C.Nonempty
  · right
    obtain ⟨a, ha⟩ := hne
    have hpick : ∀ (lo : ℤ) (π : ZMod 2), ∃ k : ℤ, 0 ≤ k ∧ k ≤ 1 ∧ ((lo + k : ℤ) : ZMod 2) = π :=
      fun lo π => ⟨((π - (lo : ZMod 2)).val : ℤ), by positivity,
        by have := ZMod.val_lt (π - (lo : ZMod 2)); omega,
        by push_cast; rw [ZMod.natCast_zmod_val]; ring⟩
    rcases (show 3 ≤ q ∨ 3 ≤ p - q by omega) with hq3 | hR3
    · refine eq_univ_of_sub_mem (u := ↑uq⁻¹) (Units.isUnit _) ha fun z hz => ?_
      obtain ⟨k, hk0, hk1, hk⟩ := hpick (evenLo s) (φ z)
      obtain ⟨x, hxC, hx0, hxz⟩ := exists_preimage_of_counting φ C H J hmaps hinj hJ01 hJ10 0
        (evenLo s + k) ((hJ0 _).2 ⟨by omega, by omega⟩) z hz hk.symm
      have := hC _ _ hxC (edgeE x hx0 (evenLo s + k + 1) ⟨by omega, by omega⟩)
      convert this using 1
      rw [← hxz, hH0]; push_cast; ring
    · refine eq_univ_of_sub_mem (u := ↑uR⁻¹) (Units.isUnit _) ha fun z hz => ?_
      obtain ⟨k, hk0, hk1, hk⟩ := hpick (oddLo s) (φ z)
      obtain ⟨x, hxC, hx0, hxz⟩ := exists_preimage_of_counting φ C H J hmaps hinj hJ01 hJ10 1
        (oddLo s + k) ((hJ1 _).2 ⟨by omega, by omega⟩) z hz hk.symm
      have := hC _ _ hxC (edgeO x hx0 (oddLo s + k + 1) ⟨by omega, by omega⟩)
      convert this using 1
      rw [← hxz, hH1]; push_cast; ring
  · left; exact Set.not_nonempty_iff_eq_empty.mp hne

/-- **(ratified).**  **Lemma D** (`4 ∣ p`, the prime `2`): lift `2M₀ → 2^e M₀`; `W⁻¹` expands
`2`-adically by `2^{v₂(p) − 1}`.  Paper proof: note §2 Lemma D. -/
theorem residueTransitive_lift_two_of_four_dvd (h4 : 4 ∣ p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) {M₀ : ℕ} (hM₀ : Nat.Coprime M₀ (2 * p * q * (p - q)))
    (h : ResidueTransitive (wythoff s p q) (2 * M₀)) {e : ℕ} (he : 1 ≤ e) :
    ResidueTransitive (wythoff s p q) (2 ^ e * M₀) := by
  have hQ := isCoprime_branchQ_two (even_iff_two_dvd.2 (dvd_trans ⟨2, rfl⟩ h4)) hcop hqp
  obtain ⟨p₄, hp₄⟩ := h4
  rw [← residueTransitive_inv_iff s hq hqp]
  have hM : ((2 ^ e * M₀ : ℕ) : ℤ) = 2 ^ (e - 1) * (2 * M₀ : ℕ) := by
    push_cast
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel he]
  refine residueTransitive_of_classIn ((residueTransitive_inv_iff s hq hqp _).2 h)
    (fun C hC n hn => ?_) (fun C hC hne => ?_)
  · refine hn.drop hC (A := 2 * p₄) (B := branchQ p q (wythoffInv s p q n)) (N := 2 ^ (e - 1))
      (fun v => ?_) (by rw [hM]; push_cast; ring) (hQ _).pow_right
    rw [show n + ((2 * M₀ : ℕ) : ℤ) * (2 * p₄ * v) = n + p * (M₀ * v) by rw [hp₄]; push_cast; ring,
      wythoffInv_add_scaled s hq hqp]
    push_cast; ring
  · refine exists_classIn_of_step (ℓ := 2) (e := e - 1) hM
      (fun j hj x hx => ⟨_, hx.drop hC (A := p₄) (B := branchQ p q (wythoffInv s p q x))
        (N := 2 ^ (e - 1 - j)) (fun v => ?_) (by rw [hM]; exact pow_mul_split _ _ hj.le)
        (hQ _).pow_right⟩) hne
    rw [show x + (2 : ℤ) ^ (j + 1) * ((2 * M₀ : ℕ) : ℤ) * (p₄ * v) = x + p * (2 ^ j * M₀ * v) by
      rw [hp₄]; push_cast; ring, wythoffInv_add_scaled s hq hqp]
    push_cast; ring

/-- **(ratified).**  **Theorem RT, even `p`, non-absorbing.**  Residue-transitive mod every
`M ≥ 1`.  Paper proof: (B0)/(B1)/Lemma D at `2^e M₀`, then Lemma B, Lemma A. -/
theorem residueTransitive_of_even_nonabsorbing (hp : Even p) (hp4 : 4 ≤ p)
    (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (hna : ¬ (s = .plus ∧ (q = 1 ∨ p - q = 1))) {M : ℕ} (hM : 0 < M) :
    ResidueTransitive (wythoff s p q) M := by
  refine residueTransitive_of_lifts (fun _ => True) (fun _ _ _ _ => trivial)
    (fun ℓ => ℓ ≠ 2 ∧ (ℓ ∣ p ∨ ℓ ∣ q * (p - q))) ?_ ?_ M hM trivial
  · rintro ℓ M' hℓ ⟨h2, hg⟩ hM' hℓM - hT e
    rcases hg with hℓp | hℓqR
    · exact residueTransitive_lift_dvd_p s hcop hq hqp hℓ h2 hℓp hM' hℓM hT e
    · exact residueTransitive_lift_dvd_qR s hcop hq hqp hℓ h2 hℓqR hM' hℓM hT e
  · intro M hM _ hgood
    obtain ⟨e, M₀, hM₀2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' 2 (by norm_num)
    have hM₀ : Nat.Coprime M₀ (2 * p * q * (p - q)) := coprime_of_primes fun ℓ hℓ hd => by
      have h2 : ℓ ≠ 2 := by rintro rfl; exact hM₀2 hd
      rintro (h | h)
      · exact h2 h
      · exact hgood ℓ hℓ (dvd_mul_of_dvd_right hd _) ⟨h2, h⟩
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; rw [pow_zero, one_mul]
      exact residueTransitive_base_coprime s (by omega) hcop hq hqp hM₀
    rcases (show p % 4 = 2 ∨ 4 ∣ p by obtain ⟨r, hr⟩ := hp; omega) with h4 | h4
    · exact residueTransitive_base_two_pow s hp hp4 hcop hq hqp hna he (Or.inl h4) hM₀
    · refine residueTransitive_lift_two_of_four_dvd s h4 hcop hq hqp hM₀ ?_ he
      have := residueTransitive_base_two_pow s hp hp4 hcop hq hqp hna le_rfl (Or.inr rfl) hM₀
      rwa [pow_one] at this

/-- **(ratified).**  Every member with `p ≥ 3` is residue-transitive at every odd `M`
(absorbing members included: (B0), Lemma B and Lemma A at odd `M'` never use the parity chain). -/
theorem residueTransitive_of_odd_modulus (hp3 : 3 ≤ p) (hcop : Nat.Coprime p q) (hq : 0 < q)
    (hqp : q < p) {M : ℕ} (hM : Odd M) : ResidueTransitive (wythoff s p q) M := by
  refine residueTransitive_of_lifts Odd (fun _ _ hM hd => Odd.of_dvd_nat hM hd)
    (fun ℓ => ℓ ≠ 2 ∧ (ℓ ∣ p ∨ ℓ ∣ q * (p - q))) ?_ ?_ M (by obtain ⟨k, rfl⟩ := hM; omega) hM
  · rintro ℓ M' hℓ ⟨h2, hg⟩ hM' hℓM - hT e
    rcases hg with hℓp | hℓqR
    · exact residueTransitive_lift_dvd_p s hcop hq hqp hℓ h2 hℓp hM' hℓM hT e
    · exact residueTransitive_lift_dvd_qR s hcop hq hqp hℓ h2 hℓqR hM' hℓM hT e
  · intro M _ hMo hgood
    refine residueTransitive_base_coprime s hp3 hcop hq hqp (coprime_of_primes fun ℓ hℓ hd => ?_)
    have h2 : ℓ ≠ 2 := by
      rintro rfl; exact (Nat.not_even_iff_odd.2 hMo) (even_iff_two_dvd.2 hd)
    rintro (h | h)
    · exact h2 h
    · exact hgood ℓ hℓ hd ⟨h2, h⟩

/-- **(ratified).**  Absorbing members are not residue-transitive at any even `M`: the absorbing
parity class is closed (Theorem T, `parityClass_invariant_iff`).  Holds at `p = 2` too. -/
theorem not_residueTransitive_of_absorbing_even (hp : Even p) (hcop : Nat.Coprime p q)
    (hq : 0 < q) (hqp : q < p) (habs : s = .plus ∧ (q = 1 ∨ p - q = 1)) {M : ℕ}
    (hM0 : 0 < M) (hM : Even M) : ¬ ResidueTransitive (wythoff s p q) M := by
  obtain ⟨e, he⟩ := (parityClass_invariant_iff s hcop hq hqp).2 ⟨hp, habs⟩
  have h2 : 2 ∣ M := even_iff_two_dvd.1 hM
  let φ := ZMod.castHom h2 (ZMod 2)
  have hφ : ∀ n : ℤ, φ (n : ZMod M) = (n : ZMod 2) := fun n => by simp [φ]
  let C : Set (ZMod M) := {a | φ a = e}
  have hC : ResidueClosed (wythoff s p q) M C := fun n hn => by
    simp only [C, Set.mem_ofPred_eq, hφ] at hn ⊢; exact he n hn
  intro hT
  rcases (residueTransitive_iff_closed _ M).1 hT C hC with h0 | h1
  · have : (((e.val : ℤ) : ZMod M)) ∈ C := by
      simp only [C, Set.mem_ofPred_eq, hφ]; simp
    rw [h0] at this; exact this
  · have : (((e.val + 1 : ℤ) : ZMod M)) ∈ C := by rw [h1]; trivial
    simp only [C, Set.mem_ofPred_eq, hφ] at this
    push_cast at this
    rw [ZMod.natCast_zmod_val] at this
    revert this; generalize e = e'; revert e'; decide

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
  have h2 : (2 : ℤ) ∣ M := by exact_mod_cast even_iff_two_dvd.1 hM
  have hWe : ∀ n : ℤ, n % 2 = 0 → wythoff .minus 2 1 n = n - 1 := fun n hn => by
    simp only [wythoff, hn, if_true, Nat.cast_ofNat, Nat.cast_one, Int.ediv_one]; omega
  have hWo : ∀ n : ℤ, n % 2 = 1 → wythoff .minus 2 1 n = n + 1 := fun n hn => by
    simp only [wythoff, hn, Nat.cast_ofNat, Nat.cast_one]; norm_num; omega
  have hpar : ∀ (n c : ℤ), (n : ZMod M) = (c : ZMod M) → n % 2 = c % 2 := fun n c h => by
    have := h2.trans ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h); omega
  let C : Set (ZMod M) := {1, 2}
  have hC : ResidueClosed (wythoff .minus 2 1) M C := by
    intro n hn
    rcases hn with hn | hn
    · have h1 := hpar n 1 (by simpa using hn)
      rw [hWo n (by omega)]; right; push_cast; rw [hn]; norm_num
    · have h1 := hpar n 2 (by simpa using hn)
      rw [hWe n (by omega)]; left; push_cast; rw [hn]; norm_num
  intro hT
  have h0C : (0 : ZMod M) ∉ C := by
    rintro (h | h)
    · have := (ZMod.natCast_eq_zero_iff 1 M).1 (by simpa using h.symm)
      have := Nat.le_of_dvd one_pos this; omega
    · have := (ZMod.natCast_eq_zero_iff 2 M).1 (by simpa using h.symm)
      have := Nat.le_of_dvd two_pos this; omega
  rcases (residueTransitive_iff_closed _ M).1 hT C hC with h0 | h1
  · have : (1 : ZMod M) ∈ C := Or.inl rfl
    rw [h0] at this; exact this
  · exact h0C (by rw [h1]; trivial)

end EvenP

end CollatzMoonshot.WythoffResidue
