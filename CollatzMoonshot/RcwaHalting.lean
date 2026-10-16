/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaSameOrbit
import CollatzMoonshot.CounterMachineUniversal

/-!
# Halting is undecidable for valid reversible 2-counter machines; Theorem C hypothesis-free

The upper half: `CounterMachine.UndecidableCM` (one fixed deterministic `k`-counter machine `U`
with an undecidable halting problem) gives `RcwaSameOrbit.HaltingUndecidable`, so the same-orbit
part of Theorem C needs no hypothesis (`not_computable_sameCycle'`).  The chain is
`U ↦ histWrap U ↦ godel (histWrap U) ↦ double (godel (histWrap U))`, research note
`undec-lemma` (Lemmas H, G, M, D) after Morita, *Theory of Reversible Computing* (2017) §9.2,
and Kari–Ollinger (MFCS 2008).  Every all-configuration property (garbage included) is proved,
not only the runs from encoded inputs that Morita's lemmas cover.

1. **Lemma M for counter machines.**  `LapsMixed M B`: every closed rule walk off the boundary
   states `B` changes some counter down and some counter up.  Then an infinite backward chain
   visits `B` infinitely often, so the reverse is mortal as soon as boundary-to-boundary macro
   steps have no infinite backward chain (`revMortal_of_macro`, from `RcwaMachine`).
2. **History (Lemma H; Morita Lemma 9.3, every step recorded).**  `histWrap U lab` runs `U` on the
   counters `val i`, guarded by `work = 0` at each boundary state `bnd s`, and after the step by
   rule `ρ` replaces `hist` by `K · hist + lab ρ` (a transfer `hist → work`, then a wheel of `K`
   states).  Merges are separated by a re-test, so it is reversible in Morita's syntactic sense,
   and `hist` grows along every macro step, so its reverse is mortal on all configurations.
3. **Gödel compile (Lemma G; Morita Lemma 9.7 with a `x ≥ 1` guard).**  `godel B p N` keeps
   `J · ∏ p i ^ v i` in counter `0` and uses counter `1` as scratch.  Each state of `B` is a
   boundary `ent q` guarded by `x ≥ 1, y = 0`; moves are multiply/divide loops, tests are a
   division wheel plus a restore wheel per target.  Faithful on every guarded boundary
   configuration (junk `J` rides along), reversible, and every loop is a mixed lap.
4. **Doubling (Lemma D; Kari–Ollinger Thm 3).**  `double rs e` runs `R` forward on the layer
   `(q, true)`, the inverse quadruples backward on `(q, false)`, and turns around on every
   zero-pattern where `R` is stuck.  For deterministic reversible `R` with mortal reverse it is
   `Valid` with `pair (q, b) = (q, !b)`.
5. **Assembly.**  `exists_valid_machine`, then `haltingUndecidable` and
   `not_computable_sameCycle'`.
-/

namespace CollatzMoonshot.RcwaHalting

open CollatzMoonshot.CounterMachine
open CollatzMoonshot.RcwaSameOrbit (Test Move Rule Machine step IsSource IsSink Halts
  Deterministic Reversible HaltingUndecidable RcwaTable not_computable_sameCycle)

/-! ## 1. Lemma M for counter machines -/

section LemmaM

variable {Q ι : Type*}

/-- **(S1).**  Every closed walk `ρ 0, …, ρ (m - 1)` (`m ≥ 1`) of rules whose sources are off `B`
has a lap vector with a negative and a positive entry. -/
def LapsMixed [DecidableEq ι] (M : CM Q ι) (B : Set Q) : Prop :=
  ∀ (ρ : ℕ → Quad Q ι) (m : ℕ), 0 < m → (∀ i, i < m → ρ i ∈ M) →
    (∀ i, i < m → (ρ i).src ∉ B) → (∀ i, i + 1 < m → (ρ i).dst = (ρ (i + 1)).src) →
    (ρ (m - 1)).dst = (ρ 0).src →
    (∃ j, ∑ i ∈ Finset.range m, (ρ i).op.delta j < 0) ∧
      (∃ j, 0 < ∑ i ∈ Finset.range m, (ρ i).op.delta j)

/-- Dickson's lemma for finitely many counters. -/
theorem wellQuasiOrderedLE_pi [Finite ι] : WellQuasiOrderedLE (ι → ℕ) :=
  Pi.wellQuasiOrderedLE

/-- An operation changes each counter by its `delta`. -/
theorem Op.act_delta [DecidableEq ι] {o : Op ι} {v w : ι → ℕ} (h : o.Act v w) (j : ι) :
    (w j : ℤ) = v j + o.delta j := by
  cases o with
  | test i b => obtain ⟨-, rfl⟩ := h; simp [Op.delta]
  | dec i =>
    obtain ⟨-, h1, h2⟩ := h
    by_cases hj : j = i
    · subst hj; simp [Op.delta]; omega
    · simp [Op.delta, hj, h2 j hj]
  | inc i =>
    obtain ⟨h1, h2⟩ := h
    by_cases hj : j = i
    · subst hj; simp [Op.delta, h1]
    · simp [Op.delta, hj, h2 j hj]
  | nop => cases h; simp [Op.delta]

/-- (S1) gives the backward loop condition of `RcwaMachine`'s Lemma M. -/
theorem lapNotDown_of_lapsMixed [DecidableEq ι] {M : CM Q ι} {B : Set Q}
    (hlap : LapsMixed M B) : RcwaMachine.LapNotDown B M.Step := by
  intro x m n hmn hrun hq hle
  have hex : ∀ j, ∃ ρ : Quad Q ι, j < n - m → ρ ∈ M ∧ (x (m + j)).1 = ρ.src ∧
      (x (m + j + 1)).1 = ρ.dst ∧ ρ.op.Act (x (m + j)).2 (x (m + j + 1)).2 := by
    intro j
    by_cases hj : j < n - m
    · obtain ⟨ρ, hρ, h1, h2, h3⟩ := hrun.1 (m + j) (by omega) (by omega)
      exact ⟨ρ, fun _ => ⟨hρ, h1, h2, h3⟩⟩
    · exact ⟨⟨(x m).1, .nop, (x m).1⟩, fun h => absurd h hj⟩
  choose ρ hρ using hex
  have hsum : ∀ j k, k ≤ n - m → ∑ i ∈ Finset.range k, (ρ i).op.delta j =
      ((x (m + k)).2 j : ℤ) - (x m).2 j := by
    intro j k
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      have := Op.act_delta (hρ k (by omega)).2.2.2 j
      rw [Finset.sum_range_succ, ih (by omega), show m + (k + 1) = m + k + 1 by omega]
      omega
  obtain ⟨-, j, hj⟩ := hlap ρ (n - m) (by omega) (fun i hi => (hρ i hi).1)
    (fun i hi => by rw [← (hρ i hi).2.1]; exact hrun.2 _ (by omega) (by omega))
    (fun i hi => by
      rw [← (hρ i (by omega)).2.2.1, ← (hρ (i + 1) hi).2.1, Nat.add_assoc])
    (by
      rw [← (hρ _ (by omega)).2.2.1, ← (hρ 0 (by omega)).2.1,
        show m + (n - m - 1) + 1 = n by omega, Nat.add_zero, hq])
  rw [hsum j _ le_rfl, show m + (n - m) = n by omega] at hj
  have : (x n).2 j ≤ (x m).2 j := hle j
  omega

/-- **Lemma M, reverse.**  Under (S1), the reverse is mortal if the macro map on boundary
configurations has no infinite backward chain. -/
theorem revMortal_of_macro [Finite Q] [Finite ι] [DecidableEq ι] {M : CM Q ι} {B : Set Q}
    (hlap : LapsMixed M B)
    (hmac : ¬ ∃ b : ℕ → Cfg Q ι, ∀ n, RcwaMachine.MacroStep B M.Step (b (n + 1)) (b n)) :
    M.RevMortal := by
  have := wellQuasiOrderedLE_pi (ι := ι)
  exact fun h => hmac
    ((RcwaMachine.reverse_immortal_iff_macro B M.Step (lapNotDown_of_lapsMixed hlap)).1 h)

/-- A macro step is a nonempty run. -/
theorem macroStep_transGen {M : CM Q ι} {B : Set Q} {b b' : Cfg Q ι}
    (h : RcwaMachine.MacroStep B M.Step b b') : Relation.TransGen M.Step b b' := by
  obtain ⟨-, -, x, n, hn, rfl, rfl, hstep, -⟩ := h
  have key : ∀ k, k < n → Relation.TransGen M.Step (x 0) (x (k + 1)) := by
    intro k
    induction k with
    | zero => intro h; exact .single (hstep 0 h)
    | succ k ih => intro h; exact .tail (ih (by omega)) (hstep _ h)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact key k (by omega)

/-- Under determinism a boundary configuration has at most one macro successor. -/
theorem macroStep_functional {M : CM Q ι} (hM : M.Det) {B : Set Q} {b b₁ b₂ : Cfg Q ι}
    (h₁ : RcwaMachine.MacroStep B M.Step b b₁) (h₂ : RcwaMachine.MacroStep B M.Step b b₂) :
    b₁ = b₂ := by
  obtain ⟨-, hb₁, x, n, hn, hx0, rfl, hx, hxoff⟩ := h₁
  obtain ⟨-, hb₂, y, n', hn', hy0, rfl, hy, hyoff⟩ := h₂
  have heq : ∀ i, i ≤ n → i ≤ n' → x i = y i := by
    intro i
    induction i with
    | zero => intros; rw [hx0, hy0]
    | succ i ih =>
      intro h1 h2
      exact CM.step_functional hM (hx i (by omega))
        (by rw [ih (by omega) (by omega)]; exact hy i (by omega))
  rcases lt_trichotomy n n' with h | rfl | h
  · exact absurd (heq n le_rfl h.le ▸ hb₁) (hyoff n hn h)
  · exact heq n le_rfl le_rfl
  · exact absurd ((heq n' h.le le_rfl).symm ▸ hb₂) (hxoff n' hn' h)

end LemmaM

/-! ## 2. The history wrapper (Lemma H) -/

/-- The counters of the history wrapper: the simulated counters, the history, scratch. -/
inductive HCtr (ι : Type*) where
  | val (i : ι)
  | hist
  | work
  deriving DecidableEq, Fintype

/-- The states of the history wrapper.  `bnd s` is the boundary (guard `work = 0`), `act s`
performs `U`'s operation, `pre ρ`, `tr ρ`, `tr₁ ρ`, `tr₂ ρ`, `tr₃ ρ` move `hist` into `work`,
and `wh s j`, `wa s j`, `wb s`, `wc s`, `wd s` are the wheel into the target `s`. -/
inductive HState (Q ι : Type*) (K : ℕ) where
  | bnd (s : Q)
  | act (s : Q)
  | pre (ρ : Quad Q ι)
  | tr (ρ : Quad Q ι)
  | tr₁ (ρ : Quad Q ι)
  | tr₂ (ρ : Quad Q ι)
  | tr₃ (ρ : Quad Q ι)
  | wh (s : Q) (j : Fin K)
  | wa (s : Q) (j : Fin K)
  | wb (s : Q)
  | wc (s : Q)
  | wd (s : Q)
  deriving DecidableEq, Fintype

section History

variable {Q ι : Type*} {K : ℕ}

/-- The rules of the history wrapper, generated by the rules `ρ` of `U` (the wheel of a target
`s` by every rule into `s`).  Entering `wh s (lab ρ)` with `hist = 0`, `work = w`, the wheel
ends at `bnd s` with `hist = K · w + lab ρ`, `work = 0`. -/
inductive HRule (U : CM Q ι) (lab : Quad Q ι → Fin K) : Quad (HState Q ι K) (HCtr ι) → Prop
  | guard {ρ} : ρ ∈ U → HRule U lab ⟨.bnd ρ.src, .test .work false, .act ρ.src⟩
  | op {ρ} : ρ ∈ U → HRule U lab ⟨.act ρ.src, ρ.op.map .val, .pre ρ⟩
  | pre {ρ} : ρ ∈ U → HRule U lab ⟨.pre ρ, .test .work false, .tr ρ⟩
  | trZ {ρ} : ρ ∈ U → HRule U lab ⟨.tr ρ, .test .hist false, .wh ρ.dst (lab ρ)⟩
  | trP {ρ} : ρ ∈ U → HRule U lab ⟨.tr ρ, .test .hist true, .tr₁ ρ⟩
  | tr₁ {ρ} : ρ ∈ U → HRule U lab ⟨.tr₁ ρ, .dec .hist, .tr₂ ρ⟩
  | tr₂ {ρ} : ρ ∈ U → HRule U lab ⟨.tr₂ ρ, .inc .work, .tr₃ ρ⟩
  | tr₃ {ρ} : ρ ∈ U → HRule U lab ⟨.tr₃ ρ, .test .work true, .tr ρ⟩
  | whInc {ρ} (j : Fin K) : ρ ∈ U → 1 ≤ j.val →
      HRule U lab ⟨.wh ρ.dst j, .inc .hist, .wa ρ.dst j⟩
  | waP {ρ} (j j' : Fin K) : ρ ∈ U → j'.val + 1 = j.val →
      HRule U lab ⟨.wa ρ.dst j, .test .hist true, .wh ρ.dst j'⟩
  | whZ {ρ} (j : Fin K) : ρ ∈ U → j.val = 0 →
      HRule U lab ⟨.wh ρ.dst j, .test .work false, .bnd ρ.dst⟩
  | whP {ρ} (j : Fin K) : ρ ∈ U → j.val = 0 →
      HRule U lab ⟨.wh ρ.dst j, .test .work true, .wb ρ.dst⟩
  | wb {ρ} : ρ ∈ U → HRule U lab ⟨.wb ρ.dst, .dec .work, .wc ρ.dst⟩
  | wc {ρ} : ρ ∈ U → HRule U lab ⟨.wc ρ.dst, .inc .hist, .wd ρ.dst⟩
  | wd {ρ} (t : Fin K) : ρ ∈ U → t.val + 1 = K →
      HRule U lab ⟨.wd ρ.dst, .test .hist true, .wh ρ.dst t⟩

/-- The history wrapper of `U` with rule labels `lab`. -/
def histWrap (U : CM Q ι) (lab : Quad Q ι → Fin K) : CM (HState Q ι K) (HCtr ι) :=
  {ρ | HRule U lab ρ}

/-- The wrapper's counters: `v` on `val`, history `h`, `work = 0`. -/
def hcfg (v : ι → ℕ) (h : ℕ) : HCtr ι → ℕ
  | .val i => v i
  | .hist => h
  | .work => 0

variable {U : CM Q ι} {lab : Quad Q ι → Fin K}

/-- The wrapper is deterministic. -/
theorem histWrap_det (hU : U.Det) : (histWrap U lab).Det := by
  sorry

/-- The wrapper is reversible: every merge is a pair of tests (`tr ρ` on `work`, `wh s j` on
`hist`). -/
theorem histWrap_rev (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    (hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ') : (histWrap U lab).Rev := by
  sorry

/-- No rule enters `bnd q₀` when no rule of `U` enters `q₀`. -/
theorem histWrap_normalAt {q₀ : Q} (hU : U.NormalAt q₀) : (histWrap U lab).NormalAt (.bnd q₀) := by
  sorry

/-- **(S1) for the wrapper.**  The only loops off the boundary are the transfer (lap
`hist − 1, work + 1`) and the wheel (lap `work − 1, hist + K`). -/
theorem histWrap_lapsMixed [DecidableEq ι] : LapsMixed (histWrap U lab) (Set.range HState.bnd) := by
  sorry

/-- **The macro step.**  A step of `U` by `ρ` is one macro step of the wrapper, with history
`K · h + lab ρ`. -/
theorem histWrap_macro {ρ : Quad Q ι} (hρ : ρ ∈ U) {v v' : ι → ℕ} (hact : ρ.op.Act v v')
    (h : ℕ) :
    RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step
      (.bnd ρ.src, hcfg v h) (.bnd ρ.dst, hcfg v' (K * h + (lab ρ).val)) := by
  sorry

/-- A halting ID of `U` gives a halting run of the wrapper. -/
theorem histWrap_halts_of_stuck {s : Q} {v : ι → ℕ} (hs : U.Stuck (s, v)) (h : ℕ) :
    (histWrap U lab).Halts (.bnd s, hcfg v h) := by
  sorry

/-- Every macro step, from any boundary configuration (garbage included), raises `hist`. -/
theorem histWrap_macro_hist (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    {b b' : Cfg (HState Q ι K) (HCtr ι)}
    (hm : RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step b b') :
    b.2 .hist < b'.2 .hist := by
  sorry

/-- **Lemma H.**  The wrapper's reverse is mortal, on all configurations. -/
theorem histWrap_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι]
    (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val) : (histWrap U lab).RevMortal := by
  sorry

/-- The wrapper halts from `bnd q` with counters `v` and empty history iff `U` halts. -/
theorem histWrap_halts_iff (hU : U.Det) (q : Q) (v : ι → ℕ) :
    (histWrap U lab).Halts (.bnd q, hcfg v 0) ↔ U.Halts (q, v) := by
  sorry

end History

/-! ## 3. The Gödel compile to two counters (Lemma G) -/

/-- The states of the Gödel compile.  `ent q` is the boundary of `B`'s state `q`, `grd q` follows
the `x ≥ 1` guard; `a₁ … a₄` move `x` into `y`, `b₁ b₂ b₃`, `mul q j`, `dv q j` multiply or divide
back; `w₁ q j`, `w₂ q j` divide by `p` with remainder `j`; `r₁ s j`, `r₂ s j` restore into the
target `s`. -/
inductive GState (Q : Type*) (N : ℕ) where
  | ent (q : Q)
  | grd (q : Q)
  | a₁ (q : Q)
  | a₂ (q : Q)
  | a₃ (q : Q)
  | a₄ (q : Q)
  | b₁ (q : Q)
  | b₂ (q : Q)
  | b₃ (q : Q)
  | mul (q : Q) (j : Fin (N + 1))
  | dv (q : Q) (j : Fin (N + 1))
  | w₁ (q : Q) (j : Fin (N + 1))
  | w₂ (q : Q) (j : Fin (N + 1))
  | r₁ (s : Q) (j : Fin (N + 1))
  | r₂ (s : Q) (j : Fin (N + 1))
  deriving DecidableEq, Fintype

section Godel

variable {Q ι : Type*} {N : ℕ}

/-- `q` leaves by an increment or a decrement of counter `i` into `q'`. -/
def MoveRule (B : CM Q ι) (q : Q) (i : ι) (q' : Q) : Prop :=
  ⟨q, .inc i, q'⟩ ∈ B ∨ ⟨q, .dec i, q'⟩ ∈ B

/-- The rules of the Gödel compile (counter `0` is `x = J · ∏ p i ^ v i`, counter `1` is `y`). -/
inductive GRule (B : CM Q ι) (p : ι → ℕ) (N : ℕ) : Quad (GState Q N) (Fin 2) → Prop
  | guard (q : Q) : GRule B p N ⟨.ent q, .test 0 true, .grd q⟩
  | nop {q q'} : ⟨q, .nop, q'⟩ ∈ B → GRule B p N ⟨.grd q, .test 1 false, .ent q'⟩
  | aIn {q i q'} : MoveRule B q i q' → GRule B p N ⟨.grd q, .test 1 false, .a₁ q⟩
  | a₁Z {q i q'} : MoveRule B q i q' → GRule B p N ⟨.a₁ q, .test 0 false, .b₁ q⟩
  | a₁P {q i q'} : MoveRule B q i q' → GRule B p N ⟨.a₁ q, .test 0 true, .a₂ q⟩
  | a₂ {q i q'} : MoveRule B q i q' → GRule B p N ⟨.a₂ q, .dec 0, .a₃ q⟩
  | a₃ {q i q'} : MoveRule B q i q' → GRule B p N ⟨.a₃ q, .inc 1, .a₄ q⟩
  | a₄ {q i q'} : MoveRule B q i q' → GRule B p N ⟨.a₄ q, .test 1 true, .a₁ q⟩
  | b₁Z {q i q'} : MoveRule B q i q' → GRule B p N ⟨.b₁ q, .test 1 false, .ent q'⟩
  | b₃ {q i q'} : MoveRule B q i q' → GRule B p N ⟨.b₃ q, .test 0 true, .b₁ q⟩
  | mulIn {q i q'} : ⟨q, .inc i, q'⟩ ∈ B → GRule B p N ⟨.b₁ q, .test 1 true, .b₂ q⟩
  | mulB₂ {q i q'} (j : Fin (N + 1)) : ⟨q, .inc i, q'⟩ ∈ B → j.val = 1 →
      GRule B p N ⟨.b₂ q, .dec 1, .mul q j⟩
  | mulStep {q i q'} (j j' : Fin (N + 1)) : ⟨q, .inc i, q'⟩ ∈ B → 1 ≤ j.val → j.val < p i →
      j'.val = j.val + 1 → GRule B p N ⟨.mul q j, .inc 0, .mul q j'⟩
  | mulLast {q i q'} (j : Fin (N + 1)) : ⟨q, .inc i, q'⟩ ∈ B → j.val = p i →
      GRule B p N ⟨.mul q j, .inc 0, .b₃ q⟩
  | dvIn {q i q'} (j : Fin (N + 1)) : ⟨q, .dec i, q'⟩ ∈ B → j.val = 1 →
      GRule B p N ⟨.b₁ q, .test 1 true, .dv q j⟩
  | dvStep {q i q'} (j j' : Fin (N + 1)) : ⟨q, .dec i, q'⟩ ∈ B → 1 ≤ j.val → j.val < p i →
      j'.val = j.val + 1 → GRule B p N ⟨.dv q j, .dec 1, .dv q j'⟩
  | dvLast {q i q'} (j : Fin (N + 1)) : ⟨q, .dec i, q'⟩ ∈ B → j.val = p i →
      GRule B p N ⟨.dv q j, .dec 1, .b₂ q⟩
  | dvB₂ {q i q'} : ⟨q, .dec i, q'⟩ ∈ B → GRule B p N ⟨.b₂ q, .inc 0, .b₃ q⟩
  | wIn {q i b q'} (j : Fin (N + 1)) : ⟨q, .test i b, q'⟩ ∈ B → j.val = 0 →
      GRule B p N ⟨.grd q, .test 1 false, .w₁ q j⟩
  | wP {q i b q'} (j : Fin (N + 1)) : ⟨q, .test i b, q'⟩ ∈ B → j.val < p i →
      GRule B p N ⟨.w₁ q j, .test 0 true, .w₂ q j⟩
  | wDec {q i b q'} (j j' : Fin (N + 1)) : ⟨q, .test i b, q'⟩ ∈ B → j.val < p i →
      j'.val = j.val + 1 → GRule B p N ⟨.w₂ q j, .dec 0, .w₁ q j'⟩
  | wInc {q i b q'} (j : Fin (N + 1)) : ⟨q, .test i b, q'⟩ ∈ B → j.val = p i →
      GRule B p N ⟨.w₁ q j, .inc 1, .w₂ q j⟩
  | wBack {q i b q'} (j j' : Fin (N + 1)) : ⟨q, .test i b, q'⟩ ∈ B → j.val = p i →
      j'.val = 0 → GRule B p N ⟨.w₂ q j, .test 1 true, .w₁ q j'⟩
  | exitP {q i q'} (j : Fin (N + 1)) : ⟨q, .test i true, q'⟩ ∈ B → j.val = 0 →
      GRule B p N ⟨.w₁ q j, .test 0 false, .r₁ q' j⟩
  | exitZ {q i q'} (j : Fin (N + 1)) : ⟨q, .test i false, q'⟩ ∈ B → 1 ≤ j.val → j.val < p i →
      GRule B p N ⟨.w₁ q j, .test 0 false, .r₁ q' j⟩
  | rZ {q i b s} (j : Fin (N + 1)) : ⟨q, .test i b, s⟩ ∈ B → j.val = 0 →
      GRule B p N ⟨.r₁ s j, .test 1 false, .ent s⟩
  | rP {q i b s} (j : Fin (N + 1)) : ⟨q, .test i b, s⟩ ∈ B → j.val = 0 →
      GRule B p N ⟨.r₁ s j, .test 1 true, .r₂ s j⟩
  | rDec {q i b s} (j j' : Fin (N + 1)) : ⟨q, .test i b, s⟩ ∈ B → j.val = 0 → j'.val = p i →
      GRule B p N ⟨.r₂ s j, .dec 1, .r₁ s j'⟩
  | rInc {q i b s} (j : Fin (N + 1)) : ⟨q, .test i b, s⟩ ∈ B → 1 ≤ j.val → j.val ≤ p i →
      GRule B p N ⟨.r₁ s j, .inc 0, .r₂ s j⟩
  | rBack {q i b s} (j j' : Fin (N + 1)) : ⟨q, .test i b, s⟩ ∈ B → 1 ≤ j.val → j.val ≤ p i →
      j'.val + 1 = j.val → GRule B p N ⟨.r₂ s j, .test 0 true, .r₁ s j'⟩

/-- The Gödel compile of `B` with primes `p` (all `≤ N`). -/
def godel (B : CM Q ι) (p : ι → ℕ) (N : ℕ) : CM (GState Q N) (Fin 2) :=
  {ρ | GRule B p N ρ}

/-- The two counters encoding `v` with junk `J`: `(J · ∏ p i ^ v i, 0)`. -/
def genc [Fintype ι] (p : ι → ℕ) (J : ℕ) (v : ι → ℕ) : Fin 2 → ℕ :=
  ![J * ∏ i, p i ^ v i, 0]

/-- Distinct primes, all at most `N`. -/
structure PrimeData (p : ι → ℕ) (N : ℕ) : Prop where
  prime : ∀ i, (p i).Prime
  inj : Function.Injective p
  le : ∀ i, p i ≤ N

variable {B : CM Q ι} {p : ι → ℕ}

/-- An encoding determines its junk and its counters (unique factorization). -/
theorem genc_inj [Fintype ι] (hp : PrimeData p N) {J J' : ℕ} {v v' : ι → ℕ} (hJ : 0 < J)
    (hJ' : 0 < J') (hJp : ∀ i, ¬ p i ∣ J) (hJp' : ∀ i, ¬ p i ∣ J')
    (h : genc p J v = genc p J' v') : J = J' ∧ v = v' := by
  sorry

/-- The compile is deterministic. -/
theorem godel_det (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) : (godel B p N).Det := by
  sorry

/-- The compile is reversible. -/
theorem godel_rev (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) : (godel B p N).Rev := by
  sorry

/-- No rule enters `ent q₀` when no rule of `B` enters `q₀`. -/
theorem godel_normalAt {q₀ : Q} (hB : B.NormalAt q₀) : (godel B p N).NormalAt (.ent q₀) := by
  sorry

/-- **(S1) for the compile.**  Every loop off the boundary is one wheel or transfer, with lap
`(−1, +1)`, `(+p, −1)`, `(+1, −p)`, `(−p, +1)` or `(+p, −1)`. -/
theorem godel_lapsMixed (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) :
    LapsMixed (godel B p N) (Set.range GState.ent) := by
  sorry

/-- **Faithfulness.**  On a configuration encoding `v` with junk `J` coprime to every `p i`, a
step of `B` is one macro step of the compile. -/
theorem godel_macro [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) {J : ℕ} (hJ : 0 < J)
    (hJp : ∀ i, ¬ p i ∣ J) {q q' : Q} {v v' : ι → ℕ} (hstep : B.Step (q, v) (q', v')) :
    RcwaMachine.MacroStep (Set.range GState.ent) (godel B p N).Step
      (.ent q, genc p J v) (.ent q', genc p J v') := by
  sorry

/-- A halting ID of `B` gives a halting run of the compile. -/
theorem godel_halts_of_stuck [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) {J : ℕ}
    (hJ : 0 < J) (hJp : ∀ i, ¬ p i ∣ J) {q : Q} {v : ι → ℕ} (hs : B.Stuck (q, v)) :
    (godel B p N).Halts (.ent q, genc p J v) := by
  sorry

/-- **Soundness on garbage.**  Every macro step, from any configuration, starts at a guarded
boundary configuration (`x ≥ 1`, `y = 0`, an encoding with some junk) and is a step of `B`. -/
theorem godel_macro_sound [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N)
    {b b' : Cfg (GState Q N) (Fin 2)}
    (h : RcwaMachine.MacroStep (Set.range GState.ent) (godel B p N).Step b b') :
    ∃ (q q' : Q) (v v' : ι → ℕ) (J : ℕ), 0 < J ∧ (∀ i, ¬ p i ∣ J) ∧
      b = (.ent q, genc p J v) ∧ b' = (.ent q', genc p J v') ∧ B.Step (q, v) (q', v') := by
  sorry

/-- **Lemma G.**  The compile's reverse is mortal, on all configurations, if `B`'s is. -/
theorem godel_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] (hB : B.Det) (hB' : B.Rev)
    (hp : PrimeData p N) (hmort : B.RevMortal) : (godel B p N).RevMortal := by
  sorry

/-- The compile halts from an encoding (junk `1`) iff `B` halts. -/
theorem godel_halts_iff [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) (q : Q)
    (v : ι → ℕ) :
    (godel B p N).Halts (.ent q, genc p 1 v) ↔ B.Halts (q, v) := by
  sorry

end Godel

/-! ## 4. The forward/backward doubling (Lemma D) -/

section Double

variable {Q : Type*}

/-- The guarded-rule test for a Morita test symbol. -/
def testOf (b : Bool) : Test :=
  if b then .pos else .zero

/-- A two-counter quadruple as a guarded rule, states numbered by `n`. -/
def toRule (n : Q → ℕ) (ρ : Quad Q (Fin 2)) : Rule :=
  match ρ.op with
  | .test i b => ⟨n ρ.src, if i = 0 then testOf b else .any, if i = 1 then testOf b else .any,
      .zero, .zero, n ρ.dst⟩
  | .dec i => ⟨n ρ.src, .any, .any, if i = 0 then .minus else .zero,
      if i = 1 then .minus else .zero, n ρ.dst⟩
  | .inc i => ⟨n ρ.src, .any, .any, if i = 0 then .plus else .zero,
      if i = 1 then .plus else .zero, n ρ.dst⟩
  | .nop => ⟨n ρ.src, .any, .any, .zero, .zero, n ρ.dst⟩

/-- A two-counter operation applies on the zero-pattern `(b₀, b₁)` (`true` = positive). -/
def opFiresPat : Op (Fin 2) → Bool → Bool → Bool
  | .test i b, b₀, b₁ => (if i = 0 then b₀ else b₁) == b
  | .dec i, b₀, b₁ => if i = 0 then b₀ else b₁
  | .inc _, _, _ => true
  | .nop, _, _ => true

/-- The turnarounds at `q`: `(q, +) → (q, −)` with no move, on each zero-pattern where no rule
of `rs` from `q` applies. -/
def turnRules [DecidableEq Q] (rs : List (Quad Q (Fin 2))) (nPlus nMinus : Q → ℕ) (q : Q) :
    List Rule :=
  [(false, false), (false, true), (true, false), (true, true)].filterMap fun bb =>
    if rs.any (fun ρ => decide (ρ.src = q) && opFiresPat ρ.op bb.1 bb.2) then none
    else some ⟨nPlus q, testOf bb.1, testOf bb.2, .zero, .zero, nMinus q⟩

/-- **The doubling.**  States `e (q, true)` run the rules `rs` forward, states `e (q, false)` the
inverse quadruples, with a turnaround on every stuck zero-pattern; `pair` swaps the layers. -/
def double [DecidableEq Q] {K : ℕ} (rs : List (Quad Q (Fin 2))) (e : Q × Bool ≃ Fin K) :
    Machine where
  K := K
  rules := rs.map (toRule fun q => (e (q, true)).val) ++
    rs.map (fun ρ => toRule (fun q => (e (q, false)).val) ρ.inv) ++
    ((List.finRange K).filterMap fun n => if (e.symm n).2 then some (e.symm n).1 else none).flatMap
      (turnRules rs (fun q => (e (q, true)).val) (fun q => (e (q, false)).val))
  pair := (List.finRange K).map fun n => (e ((e.symm n).1, !(e.symm n).2)).val

/-- A two-counter configuration in layer `b`, as a guarded-rule configuration. -/
def dcfg {K : ℕ} (e : Q × Bool ≃ Fin K) (b : Bool) (c : Cfg Q (Fin 2)) : RcwaSameOrbit.Cfg :=
  ((e (c.1, b)).val, c.2 0, c.2 1)

variable [DecidableEq Q] {K : ℕ} {R : CM Q (Fin 2)} {rs : List (Quad Q (Fin 2))}
  (e : Q × Bool ≃ Fin K)

/-- The doubling is deterministic on all configurations. -/
theorem double_deterministic (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev) :
    Deterministic (double rs e).rules := by
  sorry

/-- The doubling is reversible on all configurations. -/
theorem double_reversible (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev) :
    Reversible (double rs e).rules := by
  sorry

/-- Forward layer: a step of `R`. -/
theorem double_step_fwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    step (double rs e).rules (dcfg e true c) = some (dcfg e true d) := by
  sorry

/-- Turnaround at a halting ID of `R`. -/
theorem double_step_turn (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (h : R.Stuck c) :
    step (double rs e).rules (dcfg e true c) = some (dcfg e false c) := by
  sorry

/-- Backward layer: a step of `R` undone. -/
theorem double_step_bwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    step (double rs e).rules (dcfg e false d) = some (dcfg e false c) := by
  sorry

/-- The sinks of the backward layer are the sources of `R`. -/
theorem double_isSink_bwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (c : Cfg Q (Fin 2)) : IsSink (double rs e).rules (dcfg e false c) ↔ R.IsSource c := by
  sorry

/-- The forward copy of a source of `R` is a source. -/
theorem double_isSource (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (hc : R.IsSource c) : IsSource (double rs e).rules (dcfg e true c) := by
  sorry

/-- **Lemma D.**  The doubling of a deterministic reversible machine with mortal reverse is
`Valid`. -/
theorem double_valid (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (hmort : R.RevMortal) : (double rs e).Valid := by
  sorry

/-- From the forward copy of a source of `R`, the doubling halts iff `R` halts. -/
theorem double_halts_iff (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (hc : R.IsSource c) :
    Halts (double rs e).rules (dcfg e true c) ↔ R.Halts c := by
  sorry

end Double

/-! ## 5. Assembly -/

/-- The encoding of the wrapper's input: `v = Pi.single i₀ n`, empty history. -/
theorem genc_hcfg_single {ι : Type*} [Fintype ι] [DecidableEq ι] (p : HCtr ι → ℕ) (i₀ : ι)
    (n : ℕ) : genc p 1 (hcfg (Pi.single i₀ n) 0) = ![p (.val i₀) ^ n, 0] := by
  sorry

/-- **The compiled machine.**  A deterministic `U` in normal form at `q₀` gives a valid machine
with a source state `s₀ < K` and a prime `P` such that halting from `(s₀, P ^ n, 0)` is halting
of `U` from `q₀` with `n` in counter `i₀`. -/
theorem exists_valid_machine {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι] {U : CM Q ι}
    {q₀ : Q} (hU : U.Det) (hq₀ : U.NormalAt q₀) (i₀ : ι) :
    ∃ (M : Machine) (s₀ P : ℕ), M.Valid ∧ s₀ < M.K ∧ ∀ n : ℕ,
      IsSource M.rules (s₀, P ^ n, 0) ∧
        (Halts M.rules (s₀, P ^ n, 0) ↔ U.Halts (q₀, Pi.single i₀ n)) := by
  sorry

/-- **The upper half.**  `UndecidableCM` gives `HaltingUndecidable`. -/
theorem haltingUndecidable_of_undecidableCM (h : UndecidableCM) : HaltingUndecidable := by
  sorry

/-- **Halting is undecidable** for valid machines in `RcwaSameOrbit`'s format, from Mathlib's
halting problem. -/
theorem haltingUndecidable : HaltingUndecidable :=
  haltingUndecidable_of_undecidableCM CounterMachineUniversal.undecidableCM

/-- **Theorem C, same-orbit part, hypothesis-free.**  Same-orbit is undecidable on exact tables
with bijective evaluation, i.e. on RCWA permutations of `ℤ` with all slopes in `2^ℤ 3^ℤ`. -/
theorem not_computable_sameCycle' :
    ¬ ∃ g : RcwaTable × ℤ × ℤ → Bool, Computable g ∧
      ∀ (T : RcwaTable) (a b : ℤ), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g (T, a, b) = true ↔ Equiv.Perm.SameCycle (Equiv.ofBijective T.eval hb) a b) :=
  not_computable_sameCycle haltingUndecidable

end CollatzMoonshot.RcwaHalting
