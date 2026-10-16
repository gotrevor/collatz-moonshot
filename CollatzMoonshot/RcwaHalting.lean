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
  Deterministic Reversible HaltingUndecidable RcwaTable not_computable_sameCycle run)

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

section Chain
variable {Q V : Type*}

/-- A run of `Step` from `c` to `m` whose targets avoid `B`, then one step into `B`, is a macro
step. -/
theorem macroStep_of_chain {B : Set Q} {Step : Q × V → Q × V → Prop} {c m d : Q × V}
    (hc : c.1 ∈ B) (hcm : Relation.ReflTransGen (fun a b => Step a b ∧ b.1 ∉ B) c m)
    (hmd : Step m d) (hd : d.1 ∈ B) : RcwaMachine.MacroStep B Step c d := by
  have key : ∀ m, Relation.ReflTransGen (fun a b => Step a b ∧ b.1 ∉ B) c m →
      ∃ (x : ℕ → Q × V) (n : ℕ), x 0 = c ∧ x n = m ∧ (∀ i, i < n → Step (x i) (x (i + 1))) ∧
        ∀ i, 0 < i → i ≤ n → (x i).1 ∉ B := by
    intro m h
    induction h with
    | refl => exact ⟨fun _ => c, 0, rfl, rfl, fun i hi => absurd hi (by omega),
        fun i h1 h2 => absurd h2 (by omega)⟩
    | tail _ hst ih =>
      obtain ⟨x, n, h0, hn, hs, hoff⟩ := ih
      rename_i b e _
      refine ⟨fun i => if i ≤ n then x i else e, n + 1, by simp [h0], by simp, fun i hi => ?_,
        fun i h1 h2 => ?_⟩
      · by_cases hin : i + 1 ≤ n
        · simp only [show i ≤ n by omega, hin, if_true]; exact hs i (by omega)
        · simp only [show i ≤ n by omega, hin, if_true, if_false]
          rw [show i = n by omega, hn]; exact hst.1
      · by_cases hin : i ≤ n
        · simp only [hin, if_true]; exact hoff i h1 hin
        · simp only [hin, if_false]; exact hst.2
  obtain ⟨x, n, h0, hn, hs, hoff⟩ := key m hcm
  refine ⟨hc, hd, fun i => if i ≤ n then x i else d, n + 1, by omega, by simp [h0], by simp,
    fun i hi => ?_, fun i h1 h2 => ?_⟩
  · by_cases hin : i + 1 ≤ n
    · simp only [show i ≤ n by omega, hin, if_true]; exact hs i (by omega)
    · simp only [show i ≤ n by omega, hin, if_true, if_false]
      rw [show i = n by omega, hn]; exact hmd
  · simp only [show i ≤ n by omega, if_true]; exact hoff i h1 (by omega)

/-- Along a closed walk every potential telescopes to `0`. -/
theorem walk_sum_zero {X : Type*} (f : X → ℤ) (src dst : ℕ → X) {m : ℕ} (hm : 0 < m)
    (hchain : ∀ i, i + 1 < m → dst i = src (i + 1)) (hclose : dst (m - 1) = src 0) :
    ∑ i ∈ Finset.range m, (f (dst i) - f (src i)) = 0 := by
  have : ∀ i ∈ Finset.range m, f (dst i) - f (src i) =
      f (src ((i + 1) % m)) - f (src (i % m)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mod_eq_of_lt hi]
    by_cases h : i + 1 < m
    · rw [Nat.mod_eq_of_lt h, hchain i h]
    · rw [show i + 1 = m by omega, Nat.mod_self, ← hclose, show i = m - 1 by omega]
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i => f (src (i % m))), Nat.mod_self,
    Nat.zero_mod, sub_self]

end Chain

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

/-- The wrapper's counters `v`, `hist = h`, `work = w`. -/
def hc3 (v : ι → ℕ) (h w : ℕ) : HCtr ι → ℕ
  | .val i => v i
  | .hist => h
  | .work => w

theorem hcfg_eq (v : ι → ℕ) (h : ℕ) : hcfg v h = hc3 v h 0 := funext fun c => by cases c <;> rfl

/-- One step off the boundary. -/
def HOff (U : CM Q ι) (lab : Quad Q ι → Fin K) (c d : Cfg (HState Q ι K) (HCtr ι)) : Prop :=
  (histWrap U lab).Step c d ∧ d.1 ∉ Set.range HState.bnd

theorem hoff_of {r : Quad (HState Q ι K) (HCtr ι)} (hr : HRule U lab r)
    {s t : HState Q ι K} {w w' : HCtr ι → ℕ} (hs : s = r.src) (hd : t = r.dst)
    (ha : r.op.Act w w') (hB : t ∉ Set.range HState.bnd) : HOff U lab (s, w) (t, w') :=
  ⟨⟨r, hr, hs, hd, ha⟩, hB⟩

theorem act_dec_hist (v : ι → ℕ) (h w : ℕ) :
    (Op.dec (HCtr.hist (ι := ι))).Act (hc3 v (h + 1) w) (hc3 v h w) :=
  ⟨by simp [hc3], by simp [hc3], fun j hj => by cases j <;> simp_all [hc3]⟩

theorem act_inc_hist (v : ι → ℕ) (h w : ℕ) :
    (Op.inc (HCtr.hist (ι := ι))).Act (hc3 v h w) (hc3 v (h + 1) w) :=
  ⟨by simp [hc3], fun j hj => by cases j <;> simp_all [hc3]⟩

theorem act_dec_work (v : ι → ℕ) (h w : ℕ) :
    (Op.dec (HCtr.work (ι := ι))).Act (hc3 v h (w + 1)) (hc3 v h w) :=
  ⟨by simp [hc3], by simp [hc3], fun j hj => by cases j <;> simp_all [hc3]⟩

theorem act_inc_work (v : ι → ℕ) (h w : ℕ) :
    (Op.inc (HCtr.work (ι := ι))).Act (hc3 v h w) (hc3 v h (w + 1)) :=
  ⟨by simp [hc3], fun j hj => by cases j <;> simp_all [hc3]⟩

theorem act_test (c : HCtr ι) (b : Bool) {w : HCtr ι → ℕ} (hb : decide (0 < w c) = b) :
    (Op.test c b).Act w w := ⟨hb, rfl⟩

theorem act_map {o : Op ι} {v v' : ι → ℕ} (h : o.Act v v') (x w : ℕ) :
    (o.map HCtr.val).Act (hc3 v x w) (hc3 v' x w) := by
  cases o with
  | test i b => obtain ⟨h1, rfl⟩ := h; exact ⟨h1, rfl⟩
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, fun j hj => ?_⟩
    cases j with
    | val k => exact h3 k (fun e => hj (by rw [e]))
    | hist => rfl
    | work => rfl
  | inc i =>
    obtain ⟨h1, h3⟩ := h
    refine ⟨h1, fun j hj => ?_⟩
    cases j with
    | val k => exact h3 k (fun e => hj (by rw [e]))
    | hist => rfl
    | work => rfl
  | nop => cases h; rfl

/-- A relabelled operation acts on the `val` counters and fixes `hist` and `work`. -/
theorem map_act_inv {o : Op ι} {w w' : HCtr ι → ℕ} (h : (o.map HCtr.val).Act w w') :
    o.Act (fun i => w (.val i)) (fun i => w' (.val i)) ∧ w' .hist = w .hist ∧
      w' .work = w .work := by
  cases o with
  | test i b => obtain ⟨h1, rfl⟩ := h; exact ⟨⟨h1, rfl⟩, rfl, rfl⟩
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, h2, fun j hj => h3 _ (fun e => hj (HCtr.val.inj e))⟩, h3 _ (by simp),
      h3 _ (by simp)⟩
  | inc i =>
    obtain ⟨h1, h3⟩ := h
    exact ⟨⟨h1, fun j hj => h3 _ (fun e => hj (HCtr.val.inj e))⟩, h3 _ (by simp),
      h3 _ (by simp)⟩
  | nop => cases h; exact ⟨rfl, rfl, rfl⟩

/-- The transfer loop moves `hist` into `work`. -/
theorem hw_transfer {ρ : Quad Q ι} (hρ : ρ ∈ U) (v : ι → ℕ) (t : ℕ) : ∀ a b,
    Relation.ReflTransGen (HOff U lab) (.tr ρ, hc3 v (a + t) b) (.tr ρ, hc3 v a (b + t)) := by
  induction t with
  | zero => intro a b; exact .refl
  | succ t ih =>
    intro a b
    refine .head (hoff_of (.trP hρ) rfl rfl (act_test _ _ (by simp [hc3])) (by simp)) ?_
    refine .head (hoff_of (.tr₁ hρ) rfl rfl
      (by rw [← Nat.add_assoc]; exact act_dec_hist v _ b) (by simp)) ?_
    refine .head (hoff_of (.tr₂ hρ) rfl rfl (act_inc_work v _ b) (by simp)) ?_
    refine .head (hoff_of (.tr₃ hρ) rfl rfl (act_test _ _ (by simp [hc3])) (by simp)) ?_
    rw [show b + (t + 1) = b + 1 + t by omega]
    exact ih a (b + 1)

/-- The wheel descent `wh j → wh 0` adds `j` to `hist`. -/
theorem hw_descent {ρ : Quad Q ι} (hρ : ρ ∈ U) (v : ι → ℕ) (w : ℕ) (j : ℕ) : ∀ x (hj : j < K),
    Relation.ReflTransGen (HOff U lab) (.wh ρ.dst ⟨j, hj⟩, hc3 v x w)
      (.wh ρ.dst ⟨0, by omega⟩, hc3 v (x + j) w) := by
  induction j with
  | zero => intro x hj; exact .refl
  | succ j ih =>
    intro x hj
    refine .head (hoff_of (.whInc ⟨j + 1, hj⟩ hρ (by simp)) rfl rfl (act_inc_hist v x w)
      (by simp)) ?_
    refine .head (hoff_of (.waP ⟨j + 1, hj⟩ ⟨j, by omega⟩ hρ rfl) rfl rfl
      (act_test _ _ (by simp [hc3])) (by simp)) ?_
    rw [show x + (j + 1) = x + 1 + j by omega]
    exact ih (x + 1) (by omega)

/-- One lap of the wheel moves a unit of `work` into `K` units of `hist`. -/
theorem hw_laps {ρ : Quad Q ι} (hρ : ρ ∈ U) (v : ι → ℕ) (hK : 0 < K) (w : ℕ) : ∀ x,
    Relation.ReflTransGen (HOff U lab) (.wh ρ.dst ⟨0, hK⟩, hc3 v x w)
      (.wh ρ.dst ⟨0, hK⟩, hc3 v (x + K * w) 0) := by
  induction w with
  | zero => intro x; exact .refl
  | succ w ih =>
    intro x
    refine .head (hoff_of (.whP ⟨0, hK⟩ hρ rfl) rfl rfl (act_test _ _ (by simp [hc3]))
      (by simp)) ?_
    refine .head (hoff_of (.wb hρ) rfl rfl (act_dec_work v x w) (by simp)) ?_
    refine .head (hoff_of (.wc hρ) rfl rfl (act_inc_hist v x w) (by simp)) ?_
    refine .head (hoff_of (.wd ⟨K - 1, by omega⟩ hρ (by simp; omega)) rfl rfl
      (act_test _ _ (by simp [hc3])) (by simp)) ?_
    refine (hw_descent hρ v w (K - 1) (x + 1) (by omega)).trans ?_
    rw [show x + K * (w + 1) = x + 1 + (K - 1) + K * w by
      rw [Nat.mul_succ]; omega]
    exact ih _

/-- The wrapper is deterministic. -/
theorem histWrap_det (hU : U.Det) : (histWrap U lab).Det := by
  rintro r₁ h₁ r₂ h₂ hne hsrc
  cases h₁ <;> cases h₂ <;> simp only [HState.bnd.injEq, HState.act.injEq, HState.pre.injEq,
    HState.tr.injEq, HState.tr₁.injEq, HState.tr₂.injEq, HState.tr₃.injEq, HState.wh.injEq,
    HState.wa.injEq, HState.wb.injEq, HState.wc.injEq, HState.wd.injEq, reduceCtorEq] at hsrc
  case op.op ρ₁ hρ₁ ρ₂ hρ₂ =>
    obtain ⟨i, b, b', h1, h2, hb⟩ := hU _ hρ₁ _ hρ₂ (fun e => hne (by subst e; rfl)) hsrc
    exact ⟨.val i, b, b', by simp [h1, Op.map], by simp [h2, Op.map], hb⟩
  case waP.waP ρ₁ j₁ j₁' hρ₁ hj₁ ρ₂ j₂ j₂' hρ₂ hj₂ =>
    obtain ⟨h1, rfl⟩ := hsrc
    exact absurd (by rw [h1, Fin.ext (show j₁'.val = j₂'.val by omega)]) hne
  case wd.wd ρ₁ t₁ hρ₁ ht₁ ρ₂ t₂ hρ₂ ht₂ =>
    exact absurd (by rw [hsrc, Fin.ext (show t₁.val = t₂.val by omega)]) hne
  all_goals simp_all

/-- The wrapper is reversible: every merge is a pair of tests (`tr ρ` on `work`, `wh s j` on
`hist`). -/
theorem histWrap_rev (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    (hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ') : (histWrap U lab).Rev := by
  rintro r₁ h₁ r₂ h₂ hne hdst
  cases h₁ <;> cases h₂ <;> simp only [HState.bnd.injEq, HState.act.injEq, HState.pre.injEq,
    HState.tr.injEq, HState.tr₁.injEq, HState.tr₂.injEq, HState.tr₃.injEq, HState.wh.injEq,
    HState.wa.injEq, HState.wb.injEq, HState.wc.injEq, HState.wd.injEq, reduceCtorEq] at hdst
  case trZ.trZ ρ₁ hρ₁ ρ₂ hρ₂ =>
    obtain rfl := hinj _ hρ₁ _ hρ₂ hdst.2
    exact absurd rfl hne
  case waP.waP ρ₁ j₁ j₁' hρ₁ hj₁ ρ₂ j₂ j₂' hρ₂ hj₂ =>
    obtain ⟨h1, rfl⟩ := hdst
    exact absurd (by rw [h1, Fin.ext (show j₁.val = j₂.val by omega)]) hne
  case waP.wd ρ₁ j₁ j₁' hρ₁ hj₁ ρ₂ t hρ₂ ht =>
    obtain ⟨-, rfl⟩ := hdst
    exact absurd j₁.isLt (by omega)
  case wd.waP ρ₁ t hρ₁ ht ρ₂ j₁ j₁' hρ₂ hj₁ =>
    obtain ⟨-, rfl⟩ := hdst
    exact absurd j₁.isLt (by omega)
  case whZ.whZ ρ₁ j₁ hρ₁ hj₁ ρ₂ j₂ hρ₂ hj₂ =>
    exact absurd (by rw [hdst, Fin.ext (show j₁.val = j₂.val by omega)]) hne
  case whP.whP ρ₁ j₁ hρ₁ hj₁ ρ₂ j₂ hρ₂ hj₂ =>
    exact absurd (by rw [hdst, Fin.ext (show j₁.val = j₂.val by omega)]) hne
  all_goals simp_all

/-- No rule enters `bnd q₀` when no rule of `U` enters `q₀`. -/
theorem histWrap_normalAt {q₀ : Q} (hU : U.NormalAt q₀) : (histWrap U lab).NormalAt (.bnd q₀) := by
  intro r hr h
  cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h
  rename_i ρ _ hρ _
  exact hU ρ hρ h

/-- Rank of a wrapper state: rules off the boundary never lower it. -/
def hrank : HState Q ι K → ℕ
  | .bnd _ => 4
  | .act _ => 0
  | .pre _ => 1
  | .tr _ | .tr₁ _ | .tr₂ _ | .tr₃ _ => 2
  | .wh _ _ | .wa _ _ | .wb _ | .wc _ | .wd _ => 3

/-- Transfer potential for `hist` (`4 δ = Δ − 1`). -/
def tF : HState Q ι K → ℤ
  | .tr₁ _ => 1
  | .tr₂ _ => -2
  | .tr₃ _ => -1
  | _ => 0

/-- Transfer potential for `hist + work`. -/
def tH : HState Q ι K → ℤ
  | .tr₂ _ => -1
  | _ => 0

/-- Wheel potential for `work` (`(2K + 2) δ = Δ − 1`). -/
def wF : HState Q ι K → ℤ
  | .wh _ j => 2 * K - 2 * j.val
  | .wa _ j => 2 * K - 2 * j.val + 1
  | .wb _ => 2 * K + 1
  | .wd _ => 1
  | _ => 0

/-- Wheel potential for `hist + K · work`. -/
def wH : HState Q ι K → ℤ
  | .wh _ j => -j.val
  | .wa _ j => 1 - j.val
  | .wc _ => -K
  | .wd _ => 1 - K
  | _ => 0

/-- Wheel potential when `K = 0`. -/
def wZ : HState Q ι K → ℤ
  | .wc _ => 1
  | .wd _ => 2
  | _ => 0

theorem hrule_rank [DecidableEq ι] {r : Quad (HState Q ι K) (HCtr ι)} (hr : HRule U lab r)
    (hs : r.src ∉ Set.range HState.bnd) (hd : r.dst ∉ Set.range HState.bnd) :
    hrank r.src ≤ hrank r.dst ∧ (hrank r.src = hrank r.dst →
      (hrank r.src = 2 ∧ 4 * r.op.delta .hist = tF r.dst - tF r.src - 1 ∧
        r.op.delta .work + r.op.delta .hist = tH r.dst - tH r.src) ∨
      (hrank r.src = 3 ∧ (2 * K + 2) * r.op.delta .work = wF r.dst - wF r.src - 1 ∧
        r.op.delta .hist + K * r.op.delta .work = wH r.dst - wH r.src ∧
        (0 < K ∨ wZ r.dst - wZ r.src = 1))) := by
  cases hr <;> simp_all [hrank, tF, tH, wF, wH, wZ, Op.delta, Op.map]
  all_goals omega

/-- **(S1) for the wrapper.**  The only loops off the boundary are the transfer (lap
`hist − 1, work + 1`) and the wheel (lap `work − 1, hist + K`). -/
theorem histWrap_lapsMixed [DecidableEq ι] : LapsMixed (histWrap U lab) (Set.range HState.bnd) := by
  intro ρ m hm hmem hoff hchain hclose
  have hdoff : ∀ i, i < m → (ρ i).dst ∉ Set.range HState.bnd := by
    intro i hi
    by_cases h : i + 1 < m
    · rw [hchain i h]; exact hoff _ h
    · rw [show i = m - 1 by omega, hclose]; exact hoff 0 hm
  have key := fun i (hi : i < m) => hrule_rank (hmem i hi) (hoff i hi) (hdoff i hi)
  -- the rank is constant along the walk
  have hmono : ∀ j, j < m → ∀ i, i ≤ j → hrank (ρ i).src ≤ hrank (ρ j).src := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [show i = 0 by omega]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans
          ((key j (by omega)).1.trans (le_of_eq (by rw [hchain j hj])))
      · rw [show i = j + 1 by omega]
  have hconst : ∀ i, i < m → hrank (ρ i).src = hrank (ρ 0).src ∧
      hrank (ρ i).dst = hrank (ρ 0).src := by
    intro i hi
    have h0 := hmono i hi 0 (Nat.zero_le _)
    have h1 := (key i hi).1
    have h2 : hrank (ρ i).dst ≤ hrank (ρ 0).src := by
      by_cases h : i + 1 < m
      · rw [hchain i h]
        calc hrank (ρ (i + 1)).src ≤ hrank (ρ (m - 1)).src := hmono _ (by omega) _ (by omega)
          _ ≤ hrank (ρ (m - 1)).dst := (key _ (by omega)).1
          _ = _ := by rw [hclose]
      · rw [show i = m - 1 by omega, hclose]
    omega
  have hid := fun i (hi : i < m) =>
    (key i hi).2 ((hconst i hi).1.trans (hconst i hi).2.symm)
  have hsum := fun (f : HState Q ι K → ℤ) =>
    walk_sum_zero f (fun i => (ρ i).src) (fun i => (ρ i).dst) hm hchain hclose
  rcases hid 0 hm with ⟨h2, -⟩ | ⟨h3, -⟩
  · -- the transfer: `hist` down, `work` up
    have hi2 : ∀ i, i < m → hrank (ρ i).src = 2 := fun i hi => (hconst i hi).1.trans h2
    have e1 : ∑ i ∈ Finset.range m, 4 * (ρ i).op.delta .hist =
        ∑ i ∈ Finset.range m, ((tF (ρ i).dst - tF (ρ i).src) - 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rcases hid i hi with ⟨-, h, -⟩ | ⟨h, -⟩
      · rw [h]
      · have := hi2 i hi; omega
    have e2 : ∑ i ∈ Finset.range m, ((ρ i).op.delta .work + (ρ i).op.delta .hist) =
        ∑ i ∈ Finset.range m, (tH (ρ i).dst - tH (ρ i).src) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rcases hid i hi with ⟨-, -, h⟩ | ⟨h, -⟩
      · exact h
      · have := hi2 i hi; omega
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range]
      at e1
    rw [Finset.sum_add_distrib, hsum] at e2
    simp only [nsmul_eq_mul, mul_one] at e1
    have : (0 : ℤ) < m := by exact_mod_cast hm
    exact ⟨⟨.hist, by linarith⟩, ⟨.work, by linarith⟩⟩
  · -- the wheel: `work` down, `hist` up
    have hi3 : ∀ i, i < m → hrank (ρ i).src = 3 := fun i hi => (hconst i hi).1.trans h3
    have hw := fun i (hi : i < m) => (hid i hi).resolve_left (fun h => by
      have := hi3 i hi; omega)
    have e1 : ∑ i ∈ Finset.range m, (2 * (K : ℤ) + 2) * (ρ i).op.delta .work =
        ∑ i ∈ Finset.range m, ((wF (ρ i).dst - wF (ρ i).src) - 1) :=
      Finset.sum_congr rfl fun i hi => (hw i (Finset.mem_range.1 hi)).2.1
    have e2 : ∑ i ∈ Finset.range m, ((ρ i).op.delta .hist + K * (ρ i).op.delta .work) =
        ∑ i ∈ Finset.range m, (wH (ρ i).dst - wH (ρ i).src) :=
      Finset.sum_congr rfl fun i hi => (hw i (Finset.mem_range.1 hi)).2.2.1
    have hK : 0 < K := by
      by_contra hK
      have e3 : ∑ i ∈ Finset.range m, (wZ (ρ i).dst - wZ (ρ i).src) =
          ∑ i ∈ Finset.range m, (1 : ℤ) :=
        Finset.sum_congr rfl fun i hi =>
          (hw i (Finset.mem_range.1 hi)).2.2.2.resolve_left hK
      rw [hsum, Finset.sum_const, Finset.card_range] at e3
      simp at e3; omega
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range]
      at e1
    rw [Finset.sum_add_distrib, hsum, ← Finset.mul_sum] at e2
    simp only [nsmul_eq_mul, mul_one] at e1
    have : (0 : ℤ) < m := by exact_mod_cast hm
    have hK' : (0 : ℤ) < K := by exact_mod_cast hK
    have hwk : ∑ i ∈ Finset.range m, (ρ i).op.delta .work < 0 := by nlinarith
    exact ⟨⟨.work, hwk⟩, ⟨.hist, by nlinarith⟩⟩

/-- **The macro step.**  A step of `U` by `ρ` is one macro step of the wrapper, with history
`K · h + lab ρ`. -/
theorem histWrap_macro {ρ : Quad Q ι} (hρ : ρ ∈ U) {v v' : ι → ℕ} (hact : ρ.op.Act v v')
    (h : ℕ) :
    RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step
      (.bnd ρ.src, hcfg v h) (.bnd ρ.dst, hcfg v' (K * h + (lab ρ).val)) := by
  have hK : 0 < K := (lab ρ).pos
  rw [hcfg_eq, hcfg_eq, Nat.add_comm]
  have hchain : Relation.ReflTransGen (HOff U lab) (HState.bnd ρ.src, hc3 v h 0)
      (HState.wh ρ.dst ⟨0, hK⟩, hc3 v' ((lab ρ).val + K * h) 0) := by
    refine .head (hoff_of (.guard hρ) rfl rfl (act_test _ _ (by simp [hc3])) (by simp)) ?_
    refine .head (hoff_of (.op hρ) rfl rfl (act_map hact h 0) (by simp)) ?_
    refine .head (hoff_of (.pre hρ) rfl rfl (act_test _ _ (by simp [hc3])) (by simp)) ?_
    have h1 := hw_transfer (lab := lab) hρ v' h 0 0
    simp only [Nat.zero_add] at h1
    refine h1.trans ?_
    refine .head (hoff_of (.trZ hρ) rfl rfl (act_test _ _ (by simp [hc3])) (by simp)) ?_
    have h2 := hw_descent (lab := lab) hρ v' h (lab ρ).val 0 (lab ρ).isLt
    simp only [Nat.zero_add, Fin.eta] at h2
    exact h2.trans (hw_laps hρ v' hK h _)
  exact macroStep_of_chain (by simp) hchain
    ⟨_, .whZ ⟨0, hK⟩ hρ rfl, rfl, rfl, act_test _ _ (by simp [hc3])⟩ (by simp)

/-- A halting ID of `U` gives a halting run of the wrapper. -/
theorem histWrap_halts_of_stuck {s : Q} {v : ι → ℕ} (hs : U.Stuck (s, v)) (h : ℕ) :
    (histWrap U lab).Halts (.bnd s, hcfg v h) := by
  by_cases hex : ∃ ρ ∈ U, ρ.src = s
  · obtain ⟨ρ, hρ, rfl⟩ := hex
    refine ⟨(.act ρ.src, hcfg v h),
      .single ⟨_, .guard hρ, rfl, rfl, act_test _ _ (by simp [hcfg])⟩, ?_⟩
    rintro d ⟨r, hr, h1, -, h3⟩
    cases hr <;> simp only [HState.act.injEq, reduceCtorEq] at h1
    rename_i ρ' hρ'
    exact hs (ρ'.dst, fun i => d.2 (.val i)) ⟨ρ', hρ', h1, rfl, (map_act_inv h3).1⟩
  · refine ⟨_, .refl, ?_⟩
    rintro d ⟨r, hr, h1, -, -⟩
    cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h1
    exact hex ⟨_, ‹_›, h1.symm⟩

/-- Every macro step, from any boundary configuration (garbage included), raises `hist`. -/
theorem histWrap_macro_hist (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    {b b' : Cfg (HState Q ι K) (HCtr ι)}
    (hm : RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step b b') :
    b.2 .hist < b'.2 .hist := by
  have hm₀ := hm
  obtain ⟨hb, hb', x, n, hn, hx0, hxn, hstep, hoff⟩ := hm
  obtain ⟨s, hs⟩ := hb
  -- the first step is the guard
  obtain ⟨r, hr, h1, h2, h3⟩ := hstep 0 hn
  rw [hx0, ← hs] at h1
  cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h1
  rename_i ρ hρ
  obtain ⟨hw, hx1⟩ := h3
  rw [hx0] at hw hx1
  simp only [decide_eq_false_iff_not, not_lt, Nat.le_zero] at hw
  -- the second step is `op ρ'`
  have hn2 : 1 < n := by
    by_contra hc
    obtain rfl : n = 1 := by omega
    obtain ⟨t, ht⟩ := hb'
    rw [← hxn, h2] at ht
    cases ht
  obtain ⟨r', hr', h1', h2', h3'⟩ := hstep 1 hn2
  rw [h2] at h1'
  cases hr' <;> simp only [HState.act.injEq, reduceCtorEq] at h1'
  rename_i ρ' hρ'
  rw [hx1] at h3'
  obtain ⟨hact, -, -⟩ := map_act_inv h3'
  have hbeq : b = (.bnd ρ'.src, hcfg (fun i => b.2 (.val i)) (b.2 .hist)) := by
    refine Prod.ext (by rw [← hs, h1, h1']) (funext fun c => ?_)
    cases c <;> simp [hcfg, hw]
  have hmac := histWrap_macro (lab := lab) hρ' hact (b.2 .hist)
  rw [← hbeq] at hmac
  have := macroStep_functional (histWrap_det hU) hm₀ hmac
  rw [this]
  have hK : 0 < K := (lab ρ').pos
  have := hlab ρ' hρ'
  simp only [hcfg]
  have := Nat.le_mul_of_pos_left (b.2 .hist) hK
  omega

/-- **Lemma H.**  The wrapper's reverse is mortal, on all configurations. -/
theorem histWrap_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι]
    (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val) : (histWrap U lab).RevMortal := by
  refine revMortal_of_macro histWrap_lapsMixed ?_
  rintro ⟨b, hb⟩
  have : ∀ n, (b n).2 .hist + n ≤ (b 0).2 .hist := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := histWrap_macro_hist hU hlab (hb n); omega
  have := this ((b 0).2 .hist + 1)
  omega

/-- The wrapper halts from `bnd q` with counters `v` and empty history iff `U` halts. -/
theorem histWrap_halts_iff (hU : U.Det) (q : Q) (v : ι → ℕ) :
    (histWrap U lab).Halts (.bnd q, hcfg v 0) ↔ U.Halts (q, v) := by
  refine CM.halts_iff_of_sim (histWrap_det hU)
    (fun c c' => ∃ h, c' = (.bnd c.1, hcfg c.2 h)) ?_ ?_ ⟨0, rfl⟩
  · rintro c d c' ⟨ρ, hρ, h1, h2, h3⟩ ⟨h, rfl⟩
    refine ⟨(.bnd d.1, hcfg d.2 (K * h + (lab ρ).val)), ?_, _, rfl⟩
    rw [h1, h2]
    exact macroStep_transGen (histWrap_macro hρ h3 h)
  · rintro ⟨q, v⟩ c' hs ⟨h, rfl⟩
    exact histWrap_halts_of_stuck hs h

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

theorem testOf_ok (b : Bool) (a : ℕ) : (testOf b).ok a = (decide (0 < a) == b) := by
  cases b <;> by_cases ha : 0 < a <;> simp [testOf, Test.ok, ha] <;> omega

theorem fin2_ext {v w : Fin 2 → ℕ} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  ext j; fin_cases j <;> assumption

/-- An operation fires on `v` iff its pattern test passes. -/
theorem exists_act_iff (o : Op (Fin 2)) (v : Fin 2 → ℕ) :
    (∃ w, o.Act v w) ↔ opFiresPat o (decide (0 < v 0)) (decide (0 < v 1)) = true := by
  cases o with
  | test i bb =>
    fin_cases i <;> cases bb <;> simp [Op.Act, opFiresPat]
  | dec i =>
    simp only [Op.Act, opFiresPat]
    constructor
    · rintro ⟨w, h, -⟩; fin_cases i <;> simpa using h
    · intro h
      refine ⟨Function.update v i (v i - 1), ?_, ?_, fun j hj => by simp [hj]⟩ <;>
        fin_cases i <;> simp_all <;> omega
  | inc i =>
    simp only [Op.Act, opFiresPat, iff_true]
    exact ⟨Function.update v i (v i + 1), by simp, fun j hj => by simp [hj]⟩
  | nop => simp [Op.Act, opFiresPat]

/-- When the operation acts, the guarded rule fires and lands on the result. -/
theorem toRule_of_act (n : Q → ℕ) {ρ : Quad Q (Fin 2)} {v w : Fin 2 → ℕ}
    (h : ρ.op.Act v w) :
    (toRule n ρ).Fires (n ρ.src, v 0, v 1) ∧
      (toRule n ρ).target (n ρ.src, v 0, v 1) = (n ρ.dst, w 0, w 1) := by
  obtain ⟨src, op, dst⟩ := ρ
  cases op with
  | test i bb =>
    obtain ⟨h1, rfl⟩ := h
    fin_cases i <;> cases bb <;>
      simp_all [toRule, Rule.Fires, Rule.target, testOf, Test.ok, Move.val] <;> omega
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    fin_cases i
    · have := h3 1 (by decide)
      simp at h1 h2 this
      simp [toRule, Rule.Fires, Rule.target, Move.val, Test.ok, this]; omega
    · have := h3 0 (by decide)
      simp at h1 h2 this
      simp [toRule, Rule.Fires, Rule.target, Move.val, Test.ok, this]; omega
  | inc i =>
    obtain ⟨h1, h3⟩ := h
    fin_cases i
    · have := h3 1 (by decide)
      simp at h1 this
      simp [toRule, Rule.Fires, Rule.target, Move.val, Test.ok, this, h1]; omega
    · have := h3 0 (by decide)
      simp at h1 this
      simp [toRule, Rule.Fires, Rule.target, Move.val, Test.ok, this, h1]; omega
  | nop =>
    cases h
    simp [toRule, Rule.Fires, Rule.target, Move.val, Test.ok]

/-- A guarded rule from a quadruple fires only at its source, where the operation acts. -/
theorem act_of_toRule {n : Q → ℕ} {ρ : Quad Q (Fin 2)} {s : ℕ} {v : Fin 2 → ℕ}
    (h : (toRule n ρ).Fires (s, v 0, v 1)) : s = n ρ.src ∧ ∃ w, ρ.op.Act v w := by
  rw [exists_act_iff]
  obtain ⟨src, op, dst⟩ := ρ
  cases op with
  | test i bb =>
    fin_cases i <;> cases bb <;>
      simp_all [toRule, Rule.Fires, testOf, Test.ok, Move.val, opFiresPat] <;> omega
  | dec i =>
    fin_cases i <;> simp_all [toRule, Rule.Fires, Test.ok, Move.val, opFiresPat] <;> omega
  | inc i =>
    fin_cases i <;> simp_all [toRule, Rule.Fires, Test.ok, Move.val, opFiresPat]
  | nop => simp_all [toRule, Rule.Fires, Test.ok, Move.val, opFiresPat]

theorem toRule_src (n : Q → ℕ) (ρ : Quad Q (Fin 2)) : (toRule n ρ).src = n ρ.src := by
  obtain ⟨_, o, _⟩ := ρ; cases o <;> rfl

theorem toRule_dst (n : Q → ℕ) (ρ : Quad Q (Fin 2)) : (toRule n ρ).dst = n ρ.dst := by
  obtain ⟨_, o, _⟩ := ρ; cases o <;> rfl

theorem run_succ (R : List Rule) (n : ℕ) (c : RcwaSameOrbit.Cfg) :
    run R (n + 1) c = (run R n c).bind (step R) :=
  Function.iterate_succ_apply' _ _ _

theorem run_succ_of_step {R : List Rule} {c d : RcwaSameOrbit.Cfg} (h : step R c = some d)
    (n : ℕ) : run R (n + 1) c = run R n d := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_succ_of_sink {R : List Rule} {c : RcwaSameOrbit.Cfg} (h : IsSink R c)
    (n : ℕ) : run R (n + 1) c = none := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some]
  rw [show step R c = none from h]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem halts_of_step {R : List Rule} {c d : RcwaSameOrbit.Cfg} (h : step R c = some d)
    (hd : Halts R d) : Halts R c := by
  obtain ⟨n, f, hn, hf⟩ := hd
  exact ⟨n + 1, f, by rw [run_succ_of_step h]; exact hn, hf⟩

variable [DecidableEq Q] {K : ℕ} {R : CM Q (Fin 2)} {rs : List (Quad Q (Fin 2))}
  (e : Q × Bool ≃ Fin K)

theorem mem_double {ρ' : Rule} : ρ' ∈ (double rs e).rules ↔
    (∃ ρ ∈ rs, toRule (fun q => (e (q, true)).val) ρ = ρ') ∨
    (∃ ρ ∈ rs, toRule (fun q => (e (q, false)).val) ρ.inv = ρ') ∨
    ∃ q, ρ' ∈ turnRules rs (fun q => (e (q, true)).val) (fun q => (e (q, false)).val) q := by
  simp only [double, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filterMap,
    List.mem_finRange, true_and, or_assoc]
  refine or_congr_right (or_congr_right ⟨?_, ?_⟩)
  · rintro ⟨q, ⟨n, hn⟩, h⟩
    exact ⟨q, h⟩
  · rintro ⟨q, h⟩
    exact ⟨q, ⟨e (q, true), by simp⟩, h⟩

omit [DecidableEq Q] in
theorem dcfg_inj {b b' : Bool} {c c' : Cfg Q (Fin 2)} (h : dcfg e b c = dcfg e b' c') :
    b = b' ∧ c = c' := by
  simp only [dcfg, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have := e.injective (Fin.ext h1)
  simp only [Prod.mk.injEq] at this
  exact ⟨this.2, Prod.ext this.1 (fin2_ext h2 h3)⟩

theorem mem_turnRules {nP nM : Q → ℕ} {q : Q} {ρ' : Rule} :
    ρ' ∈ turnRules rs nP nM q ↔ ∃ b₀ b₁ : Bool,
      (∀ ρ ∈ rs, ρ.src = q → opFiresPat ρ.op b₀ b₁ = false) ∧
        ρ' = ⟨nP q, testOf b₀, testOf b₁, .zero, .zero, nM q⟩ := by
  simp only [turnRules, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨bb, hbb, h⟩
    split_ifs at h with hany
    refine ⟨bb.1, bb.2, fun ρ hρ hq => ?_, (Option.some.inj h).symm⟩
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_exists,
      not_and] at hany
    simpa using hany ρ hρ hq
  · rintro ⟨b₀, b₁, hno, rfl⟩
    refine ⟨(b₀, b₁), by cases b₀ <;> cases b₁ <;> simp, ?_⟩
    rw [if_neg]
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro ρ hρ hq
    simp [hno ρ hρ hq]


omit [DecidableEq Q] in
theorem testOf_ok_iff (b : Bool) (a : ℕ) : (testOf b).ok a = true ↔ decide (0 < a) = b := by
  rw [testOf_ok]; simp

/-- Every firing of the doubling is a forward step, a turnaround at a halting ID, or a backward
step. -/
theorem fires_cases (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) {ρ' : Rule} (hρ' : ρ' ∈ (double rs e).rules)
    {x : RcwaSameOrbit.Cfg} (hf : ρ'.Fires x) :
    (∃ c d, R.Step c d ∧ x = dcfg e true c ∧ ρ'.target x = dcfg e true d) ∨
    (∃ c, R.Stuck c ∧ x = dcfg e true c ∧ ρ'.target x = dcfg e false c) ∨
    (∃ c d, R.Step c d ∧ x = dcfg e false d ∧ ρ'.target x = dcfg e false c) := by
  obtain ⟨s, a, b⟩ := x
  rcases (mem_double e).1 hρ' with ⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩ | ⟨q, hq⟩
  · obtain ⟨rfl, w, hw⟩ := act_of_toRule (v := ![a, b]) hf
    exact .inl ⟨(ρ.src, ![a, b]), (ρ.dst, w), ⟨ρ, (hrs ρ).1 hρ, rfl, rfl, hw⟩, rfl,
      (toRule_of_act _ hw).2⟩
  · obtain ⟨rfl, w, hw⟩ := act_of_toRule (v := ![a, b]) hf
    have hw' : ρ.op.Act w ![a, b] := Op.act_inv.1 hw
    exact .inr (.inr ⟨(ρ.src, w), (ρ.dst, ![a, b]), ⟨ρ, (hrs ρ).1 hρ, rfl, rfl, hw'⟩, rfl,
      (toRule_of_act _ hw).2⟩)
  · obtain ⟨b₀, b₁, hno, rfl⟩ := (mem_turnRules).1 hq
    obtain ⟨h1, h2, h3, -, -⟩ := hf
    simp only at h1
    rw [testOf_ok_iff] at h2 h3
    refine .inr (.inl ⟨(q, ![a, b]), ?_, by rw [h1]; rfl, ?_⟩)
    · rintro d ⟨ρ, hρ, hs, -, hact⟩
      have := (exists_act_iff ρ.op ![a, b]).1 ⟨_, hact⟩
      have h2' : decide (0 < ![a, b] 0) = b₀ := h2
      have h3' : decide (0 < ![a, b] 1) = b₁ := h3
      rw [h2', h3', hno ρ ((hrs ρ).2 hρ) hs.symm] at this
      exact Bool.false_ne_true this
    · simp [Rule.target, Move.val, dcfg]

theorem double_fwd_fires (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    ∃ ρ' ∈ (double rs e).rules, ρ'.Fires (dcfg e true c) ∧
      ρ'.target (dcfg e true c) = dcfg e true d := by
  obtain ⟨ρ, hρ, h1, h2, h3⟩ := h
  obtain ⟨hf, ht⟩ := toRule_of_act (fun q => (e (q, true)).val) h3
  refine ⟨_, (mem_double e).2 (.inl ⟨ρ, (hrs ρ).2 hρ, rfl⟩), ?_, ?_⟩
  · simpa [dcfg, h1] using hf
  · simpa [dcfg, h1, h2] using ht

theorem double_bwd_fires (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    ∃ ρ' ∈ (double rs e).rules, ρ'.Fires (dcfg e false d) ∧
      ρ'.target (dcfg e false d) = dcfg e false c := by
  obtain ⟨ρ, hρ, h1, h2, h3⟩ := h
  obtain ⟨hf, ht⟩ := toRule_of_act (ρ := ρ.inv) (fun q => (e (q, false)).val) (Op.act_inv.2 h3)
  refine ⟨_, (mem_double e).2 (.inr (.inl ⟨ρ, (hrs ρ).2 hρ, rfl⟩)), ?_, ?_⟩
  · simpa [dcfg, h2, Quad.inv] using hf
  · simpa [dcfg, h1, h2, Quad.inv] using ht

theorem double_turn_fires (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) {c : Cfg Q (Fin 2)} (h : R.Stuck c) :
    ∃ ρ' ∈ (double rs e).rules, ρ'.Fires (dcfg e true c) ∧
      ρ'.target (dcfg e true c) = dcfg e false c := by
  obtain ⟨q, v⟩ := c
  have hno : ∀ ρ ∈ rs, ρ.src = q →
      opFiresPat ρ.op (decide (0 < v 0)) (decide (0 < v 1)) = false := by
    intro ρ hρ hq
    by_contra hc
    obtain ⟨w, hw⟩ := (exists_act_iff ρ.op v).2 (by simpa using hc)
    exact h (ρ.dst, w) ⟨ρ, (hrs ρ).1 hρ, hq.symm, rfl, hw⟩
  refine ⟨_, (mem_double e).2 (.inr (.inr ⟨q, (mem_turnRules).2 ⟨_, _, hno, rfl⟩⟩)), ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [testOf_ok_iff, Move.val, dcfg]
  · simp [Rule.target, Move.val, dcfg]

/-- The doubling is deterministic on all configurations. -/
theorem double_deterministic (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev) :
    Deterministic (double rs e).rules := by
  intro ρ hρ ρ' hρ' x hf hf'
  rcases fires_cases e hrs hρ hf with ⟨c, d, hs, rfl, ht⟩ | ⟨c, hs, rfl, ht⟩ |
      ⟨c, d, hs, rfl, ht⟩ <;>
    rcases fires_cases e hrs hρ' hf' with ⟨c', d', hs', hx, ht'⟩ | ⟨c', hs', hx, ht'⟩ |
      ⟨c', d', hs', hx, ht'⟩ <;>
    obtain ⟨hb, rfl⟩ := dcfg_inj e hx <;>
    first
    | exact absurd hb (by decide)
    | exact absurd hs (hs' _)
    | exact absurd hs' (hs _)
    | rw [ht, ht', CM.step_functional hdet hs hs']
    | rw [ht, ht', CM.step_injective hrev hs hs']
    | rw [ht, ht']

/-- The doubling is reversible on all configurations. -/
theorem double_reversible (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev) :
    Reversible (double rs e).rules := by
  intro ρ hρ ρ' hρ' x x' hf hf' heq
  rcases fires_cases e hrs hρ hf with ⟨c, d, hs, rfl, ht⟩ | ⟨c, hs, rfl, ht⟩ |
      ⟨c, d, hs, rfl, ht⟩ <;>
    rcases fires_cases e hrs hρ' hf' with ⟨c', d', hs', rfl, ht'⟩ | ⟨c', hs', rfl, ht'⟩ |
      ⟨c', d', hs', rfl, ht'⟩ <;>
    rw [ht, ht'] at heq <;>
    obtain ⟨hb, rfl⟩ := dcfg_inj e heq <;>
    first
    | exact absurd hb (by decide)
    | exact absurd hs (hs' _)
    | exact absurd hs' (hs _)
    | rw [CM.step_functional hdet hs hs']
    | rw [CM.step_injective hrev hs hs']
    | rfl

/-- Forward layer: a step of `R`. -/
theorem double_step_fwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    step (double rs e).rules (dcfg e true c) = some (dcfg e true d) := by
  obtain ⟨ρ, hρ, hf, ht⟩ := double_fwd_fires e hrs h
  rw [RcwaSameOrbit.step_eq_of_fires (double_deterministic e hrs hdet hrev) hρ hf, ht]

/-- Turnaround at a halting ID of `R`. -/
theorem double_step_turn (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (h : R.Stuck c) :
    step (double rs e).rules (dcfg e true c) = some (dcfg e false c) := by
  obtain ⟨ρ, hρ, hf, ht⟩ := double_turn_fires e hrs h
  rw [RcwaSameOrbit.step_eq_of_fires (double_deterministic e hrs hdet hrev) hρ hf, ht]

/-- Backward layer: a step of `R` undone. -/
theorem double_step_bwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c d : Cfg Q (Fin 2)} (h : R.Step c d) :
    step (double rs e).rules (dcfg e false d) = some (dcfg e false c) := by
  obtain ⟨ρ, hρ, hf, ht⟩ := double_bwd_fires e hrs h
  rw [RcwaSameOrbit.step_eq_of_fires (double_deterministic e hrs hdet hrev) hρ hf, ht]

/-- Every step of the doubling, classified. -/
theorem double_step_cases (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) {x y : RcwaSameOrbit.Cfg}
    (h : step (double rs e).rules x = some y) :
    (∃ c d, R.Step c d ∧ x = dcfg e true c ∧ y = dcfg e true d) ∨
    (∃ c, R.Stuck c ∧ x = dcfg e true c ∧ y = dcfg e false c) ∨
    (∃ c d, R.Step c d ∧ x = dcfg e false d ∧ y = dcfg e false c) := by
  obtain ⟨ρ, hρ, hf, rfl⟩ := RcwaSameOrbit.exists_rule_of_step h
  exact fires_cases e hrs hρ hf

/-- The sinks of the backward layer are the sources of `R`. -/
theorem double_isSink_bwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (c : Cfg Q (Fin 2)) : IsSink (double rs e).rules (dcfg e false c) ↔ R.IsSource c := by
  constructor
  · intro hs d hd
    have := double_step_bwd e hrs hdet hrev hd
    rw [IsSink] at hs
    rw [hs] at this
    cases this
  · intro hc
    rw [IsSink, Option.eq_none_iff_forall_ne_some]
    intro y hy
    rcases double_step_cases e hrs hy with ⟨c', d, hs, hx, -⟩ | ⟨c', hs, hx, -⟩ |
        ⟨c', d, hs, hx, -⟩ <;> obtain ⟨hb, rfl⟩ := dcfg_inj e hx
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · exact hc _ hs

/-- The forward copy of a source of `R` is a source. -/
theorem double_isSource (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (hc : R.IsSource c) : IsSource (double rs e).rules (dcfg e true c) := by
  intro x hx
  rcases double_step_cases e hrs hx with ⟨c', d, hs, -, hy⟩ | ⟨c', hs, -, hy⟩ |
      ⟨c', d, hs, -, hy⟩ <;> obtain ⟨hb, rfl⟩ := dcfg_inj e hy
  · exact hc _ hs
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)

theorem exists_dcfg {x : RcwaSameOrbit.Cfg} (hx : x.1 < K) :
    ∃ b c, x = dcfg e b (c : Cfg Q (Fin 2)) := by
  obtain ⟨s, a₁, a₂⟩ := x
  refine ⟨(e.symm ⟨s, hx⟩).2, ((e.symm ⟨s, hx⟩).1, ![a₁, a₂]), ?_⟩
  simp [dcfg]

theorem double_src_dst_lt {ρ' : Rule} (hρ' : ρ' ∈ (double rs e).rules) :
    ρ'.src < K ∧ ρ'.dst < K := by
  rcases (mem_double e).1 hρ' with ⟨ρ, -, rfl⟩ | ⟨ρ, -, rfl⟩ | ⟨q, hq⟩
  · simp [toRule_src, toRule_dst]
  · simp [toRule_src, toRule_dst]
  · obtain ⟨b₀, b₁, -, rfl⟩ := (mem_turnRules).1 hq
    simp

theorem double_step_lt {x y : RcwaSameOrbit.Cfg}
    (h : step (double rs e).rules x = some y) : x.1 < K ∧ y.1 < K := by
  obtain ⟨ρ, hρ, hf, rfl⟩ := RcwaSameOrbit.exists_rule_of_step h
  rw [hf.1]
  exact ⟨(double_src_dst_lt e hρ).1, (double_src_dst_lt e hρ).2⟩

theorem double_not_isSink_fwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (c : Cfg Q (Fin 2)) : ¬ IsSink (double rs e).rules (dcfg e true c) := by
  intro hs
  rw [IsSink] at hs
  by_cases h : ∃ d, R.Step c d
  · obtain ⟨d, hd⟩ := h
    rw [double_step_fwd e hrs hdet hrev hd] at hs; cases hs
  · rw [double_step_turn e hrs hdet hrev (fun d hd => h ⟨d, hd⟩)] at hs; cases hs

theorem double_not_isSource_bwd (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (c : Cfg Q (Fin 2)) : ¬ IsSource (double rs e).rules (dcfg e false c) := by
  intro hs
  by_cases h : ∃ d, R.Step c d
  · obtain ⟨d, hd⟩ := h
    exact hs _ (double_step_bwd e hrs hdet hrev hd)
  · exact hs _ (double_step_turn e hrs hdet hrev (fun d hd => h ⟨d, hd⟩))

theorem isSource_of_double (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (hc : IsSource (double rs e).rules (dcfg e true c)) : R.IsSource c :=
  fun d hd => hc _ (double_step_fwd e hrs hdet hrev hd)

theorem double_pairFn (q : Q) (b : Bool) :
    (double rs e).pairFn (e (q, b)).val = (e (q, !b)).val := by
  simp [Machine.pairFn, double, List.getD_eq_getElem?_getD]

theorem double_pairFn_of_le {s : ℕ} (hs : K ≤ s) : (double rs e).pairFn s = s := by
  simp [Machine.pairFn, double, List.getD_eq_getElem?_getD, hs]

/-- The run invariant from the forward copy of a source `x`. -/
def DInv (R : CM Q (Fin 2)) (x : Cfg Q (Fin 2)) (y : RcwaSameOrbit.Cfg) : Prop :=
  (∃ z, y = dcfg e true z ∧ R.Reaches x z) ∨
    (∃ z, y = dcfg e false z ∧ R.Reaches x z ∧ R.Halts x)

theorem dInv_step (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hrev : R.Rev) {x : Cfg Q (Fin 2)}
    (hx : R.IsSource x) {y y' : RcwaSameOrbit.Cfg} (hy : DInv e R x y)
    (h : step (double rs e).rules y = some y') : DInv e R x y' := by
  rcases double_step_cases e hrs h with ⟨c, d, hs, rfl, rfl⟩ | ⟨c, hs, rfl, rfl⟩ |
      ⟨c, d, hs, rfl, rfl⟩ <;>
    rcases hy with ⟨z, hz, hr⟩ | ⟨z, hz, hr, hh⟩ <;> obtain ⟨hb, rfl⟩ := dcfg_inj e hz
  · exact .inl ⟨d, rfl, hr.tail hs⟩
  · exact absurd hb (by decide)
  · exact .inr ⟨c, rfl, hr, c, hr, hs⟩
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · refine .inr ⟨c, rfl, ?_, hh⟩
    rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨w, hw, hwz⟩
    · exact absurd hs (hx _)
    · rwa [CM.step_injective hrev hwz hs] at hw

theorem dInv_run (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hrev : R.Rev) {x : Cfg Q (Fin 2)}
    (hx : R.IsSource x) (n : ℕ) {y : RcwaSameOrbit.Cfg}
    (h : run (double rs e).rules n (dcfg e true x) = some y) : DInv e R x y := by
  induction n generalizing y with
  | zero => cases h; exact .inl ⟨x, rfl, .refl⟩
  | succ n ih =>
    rw [run_succ] at h
    cases hn : run (double rs e).rules n (dcfg e true x) with
    | none => rw [hn] at h; cases h
    | some z =>
      rw [hn, Option.bind_some] at h
      exact dInv_step e hrs hrev hx (ih hn) h

/-- **Lemma D.**  The doubling of a deterministic reversible machine with mortal reverse is
`Valid`. -/
theorem double_valid (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    (hmort : R.RevMortal) : (double rs e).Valid := by
  have hlen : (double rs e).pair.length = K := by simp [double]
  refine ⟨⟨fun ρ hρ => (double_src_dst_lt e hρ).1, fun ρ hρ => (double_src_dst_lt e hρ).2, ?_⟩,
    double_reversible e hrs hdet hrev, ?_, ?_, ?_⟩
  · -- `pair` is a permutation
    let σ : Equiv.Perm (Fin K) := e.symm.trans ((Equiv.prodCongr (Equiv.refl Q)
      (Equiv.boolNot)).trans e)
    have : (double rs e).pair = ((List.finRange K).map σ).map Fin.val := by
      simp only [double, List.map_map]
      exact List.map_congr_left fun a _ => rfl
    rw [this, ← List.map_coe_finRange_eq_range]
    exact (Equiv.Perm.map_finRange_perm σ).map _
  · -- sinks pair with sources
    rintro ⟨s, a₁, a₂⟩
    by_cases hs : s < K
    · obtain ⟨b, c, hc⟩ := exists_dcfg e (x := (s, a₁, a₂)) hs
      rw [hc]
      simp only [dcfg]
      rw [double_pairFn]
      cases b
      · exact (double_isSink_bwd e hrs hdet hrev c).trans
          ⟨double_isSource e hrs hdet hrev, isSource_of_double e hrs hdet hrev⟩
      · exact iff_of_false (double_not_isSink_fwd e hrs hdet hrev c)
          (double_not_isSource_bwd e hrs hdet hrev c)
    · push Not at hs
      simp only [double_pairFn_of_le e hs]
      refine iff_of_true ?_ fun y hy => ?_
      · rw [IsSink, Option.eq_none_iff_forall_ne_some]
        intro y hy
        have := (double_step_lt e hy).1
        simp at this; omega
      · have := (double_step_lt e hy).2
        simp at this; omega
  · -- no bi-infinite run
    intro g hg
    have hlt : ∀ i, (g i).1 < K := fun i => (double_step_lt e (hg i)).1
    by_cases hF : ∃ i x, g i = dcfg e false x
    · obtain ⟨i₀, x₀, hx₀⟩ := hF
      have hall : ∀ n : ℕ, ∃ x, g (i₀ + n) = dcfg e false x := by
        intro n
        induction n with
        | zero => exact ⟨x₀, by simpa using hx₀⟩
        | succ n ih =>
          obtain ⟨x, hx⟩ := ih
          have := hg (i₀ + n)
          rw [hx] at this
          rcases double_step_cases e hrs this with ⟨c, d, -, hz, -⟩ | ⟨c, -, hz, -⟩ |
              ⟨c, d, -, -, hy⟩
          · exact absurd (dcfg_inj e hz).1 (by decide)
          · exact absurd (dcfg_inj e hz).1 (by decide)
          · exact ⟨c, by push_cast; rw [← add_assoc]; exact hy⟩
      choose y hy using hall
      refine hmort ⟨y, fun n => ?_⟩
      have := hg (i₀ + n)
      rw [hy n, show i₀ + ↑n + 1 = i₀ + ↑(n + 1) by push_cast; ring, hy (n + 1)] at this
      rcases double_step_cases e hrs this with ⟨c, d, -, hz, -⟩ | ⟨c, -, hz, -⟩ |
          ⟨c, d, hs, hz, hz'⟩
      · exact absurd (dcfg_inj e hz).1 (by decide)
      · exact absurd (dcfg_inj e hz).1 (by decide)
      · rwa [(dcfg_inj e hz).2, (dcfg_inj e hz').2]
    · push Not at hF
      have hall : ∀ i, ∃ c d, R.Step c d ∧ g i = dcfg e true c ∧ g (i + 1) = dcfg e true d := by
        intro i
        rcases double_step_cases e hrs (hg i) with h | ⟨c, -, -, hz⟩ | ⟨c, d, -, hz, -⟩
        · exact h
        · exact absurd hz (hF _ c)
        · exact absurd hz (hF _ d)
      choose c d hs hc hd using hall
      refine hmort ⟨fun n => c (-n), fun n => ?_⟩
      have h1 := hs (-(n + 1 : ℕ))
      have h2 := hd (-(n + 1 : ℕ))
      rw [show -((n + 1 : ℕ) : ℤ) + 1 = -n by push_cast; ring, hc] at h2
      rw [← (dcfg_inj e h2).2] at h1
      exact h1
  · -- end to start
    rintro ⟨s, a₁, a₂⟩ d n hsrc hrun hsink
    by_cases hs : s < K
    · obtain ⟨b, x, hx⟩ := exists_dcfg e (x := (s, a₁, a₂)) hs
      rw [hx] at hsrc hrun ⊢
      cases b
      · exact absurd hsrc (double_not_isSource_bwd e hrs hdet hrev x)
      · have hxs := isSource_of_double e hrs hdet hrev hsrc
        rcases dInv_run e hrs hrev hxs n hrun with ⟨z, rfl, -⟩ | ⟨z, rfl, hr, -⟩
        · exact absurd hsink (double_not_isSink_fwd e hrs hdet hrev z)
        · have hz := (double_isSink_bwd e hrs hdet hrev z).1 hsink
          obtain rfl : z = x := by
            rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨w, -, hwz⟩
            · rfl
            · exact absurd hwz (hz _)
          simp only [dcfg]
          rw [double_pairFn]
          rfl
    · push Not at hs
      have hsk : IsSink (double rs e).rules (s, a₁, a₂) := by
        rw [IsSink, Option.eq_none_iff_forall_ne_some]
        intro y hy
        have := (double_step_lt e hy).1
        simp at this; omega
      cases n with
      | zero =>
        cases hrun
        simp [double_pairFn_of_le e hs]
      | succ n => rw [run_succ_of_sink hsk] at hrun; cases hrun

/-- From the forward copy of a source of `R`, the doubling halts iff `R` halts. -/
theorem double_halts_iff (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R) (hdet : R.Det) (hrev : R.Rev)
    {c : Cfg Q (Fin 2)} (hc : R.IsSource c) :
    Halts (double rs e).rules (dcfg e true c) ↔ R.Halts c := by
  constructor
  · rintro ⟨n, d, hrun, hsink⟩
    rcases dInv_run e hrs hrev hc n hrun with ⟨z, rfl, -⟩ | ⟨z, rfl, -, hh⟩
    · exact absurd hsink (double_not_isSink_fwd e hrs hdet hrev z)
    · exact hh
  · rintro ⟨d, hr, hd⟩
    have hback : ∀ y, R.Reaches c y → Halts (double rs e).rules (dcfg e false y) := by
      intro y hy
      induction hy with
      | refl => exact ⟨0, _, rfl, (double_isSink_bwd e hrs hdet hrev c).2 hc⟩
      | tail _ hs ih => exact halts_of_step (double_step_bwd e hrs hdet hrev hs) ih
    have hd' : Halts (double rs e).rules (dcfg e true d) :=
      halts_of_step (double_step_turn e hrs hdet hrev hd) (hback d hr)
    clear hback hc
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact hd'
    | head hs _ ih => exact halts_of_step (double_step_fwd e hrs hdet hrev hs) ih

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
