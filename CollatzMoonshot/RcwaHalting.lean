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

/-- `p i` divides an encoding exactly when `v i ≥ 1`. -/
theorem dvd_enc_iff [Fintype ι] (hp : PrimeData p N) {J : ℕ} (hJp : ∀ i, ¬ p i ∣ J)
    (v : ι → ℕ) (i : ι) : p i ∣ J * ∏ k, p k ^ v k ↔ 1 ≤ v i := by
  have hpi := hp.prime i
  rw [hpi.dvd_mul, or_iff_right (hJp i), (Nat.prime_iff.1 hpi).dvd_finsetProd_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    rcases Nat.eq_zero_or_pos (v k) with h0 | h0
    · rw [h0, pow_zero] at hk
      exact absurd (Nat.le_of_dvd one_pos hk) (by have := hpi.two_le; omega)
    · obtain rfl := hp.inj ((Nat.prime_dvd_prime_iff_eq hpi (hp.prime k)).1
        (hpi.dvd_of_dvd_pow hk))
      exact h0
  · intro h
    exact ⟨i, Finset.mem_univ _, dvd_pow_self _ (by omega)⟩

/-- Products of prime powers with exponents agreeing off `i`. -/
theorem prod_pow_split [Fintype ι] [DecidableEq ι] {v v' : ι → ℕ} {i : ι}
    (h : ∀ k, k ≠ i → v' k = v k) :
    ∏ k, p k ^ v' k = p i ^ v' i * ∏ k ∈ Finset.univ.erase i, p k ^ v k := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by rw [h k (Finset.ne_of_mem_erase hk)]

theorem enc_inc [Fintype ι] {v v' : ι → ℕ} {i : ι} (h : (Op.inc i).Act v v') (J : ℕ) :
    J * ∏ k, p k ^ v' k = p i * (J * ∏ k, p k ^ v k) := by
  classical
  obtain ⟨h1, h2⟩ := h
  rw [prod_pow_split h2, prod_pow_split (v' := v) (fun _ _ => rfl), h1, pow_succ]
  ring

theorem enc_dec [Fintype ι] {v v' : ι → ℕ} {i : ι} (h : (Op.dec i).Act v v') (J : ℕ) :
    J * ∏ k, p k ^ v k = p i * (J * ∏ k, p k ^ v' k) := by
  classical
  obtain ⟨-, h1, h2⟩ := h
  rw [prod_pow_split (fun k hk => (h2 k hk).symm), prod_pow_split (v' := v') (fun _ _ => rfl),
    ← h1, pow_succ]
  ring

theorem enc_pos [Fintype ι] (hp : PrimeData p N) {J : ℕ} (hJ : 0 < J) (v : ι → ℕ) :
    0 < J * ∏ k, p k ^ v k :=
  Nat.mul_pos hJ (Finset.prod_pos fun k _ => pow_pos (hp.prime k).pos _)

/-- An encoding determines its junk and its counters (unique factorization). -/
theorem genc_inj [Fintype ι] (hp : PrimeData p N) {J J' : ℕ} {v v' : ι → ℕ} (hJ : 0 < J)
    (hJ' : 0 < J') (hJp : ∀ i, ¬ p i ∣ J) (hJp' : ∀ i, ¬ p i ∣ J')
    (h : genc p J v = genc p J' v') : J = J' ∧ v = v' := by
  have h0 : J * ∏ k, p k ^ v k = J' * ∏ k, p k ^ v' k := congrFun h 0
  have hf : ∀ (J : ℕ) (v : ι → ℕ), 0 < J → (∀ i, ¬ p i ∣ J) → ∀ i,
      (J * ∏ k, p k ^ v k).factorization (p i) = v i := by
    intro J v hJ hJp i
    classical
    rw [Nat.factorization_mul hJ.ne' (Finset.prod_pos fun k _ => pow_pos (hp.prime k).pos _).ne',
      Nat.factorization_prod fun k _ => (pow_pos (hp.prime k).pos _).ne']
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.factorization_eq_zero_of_not_dvd (hJp i), zero_add,
      Finset.sum_eq_single i (fun k _ hk => by
        rw [(hp.prime k).factorization, Finsupp.single_apply, if_neg (fun e => hk (hp.inj e)),
          mul_zero]) (by simp), (hp.prime i).factorization_self, mul_one]
  have hv : v = v' := funext fun i => by rw [← hf J v hJ hJp i, h0, hf J' v' hJ' hJp' i]
  subst hv
  refine ⟨Nat.eq_of_mul_eq_mul_right (Finset.prod_pos fun k _ => pow_pos (hp.prime k).pos _) h0,
    rfl⟩

/-- Two test rules from one state test one counter. -/
theorem det_test_counter (hB : B.Det) {q q₁ q₂ : Q} {i i' : ι} {b b' : Bool}
    (h₁ : ⟨q, .test i b, q₁⟩ ∈ B) (h₂ : ⟨q, .test i' b', q₂⟩ ∈ B) : i = i' := by
  by_cases he : (⟨q, .test i b, q₁⟩ : Quad Q ι) = ⟨q, .test i' b', q₂⟩
  · simp only [Quad.mk.injEq, Op.test.injEq] at he; exact he.2.1.1
  · obtain ⟨j, c, c', h1, h2, -⟩ := hB _ h₁ _ h₂ he rfl
    simp only [Op.test.injEq] at h1 h2
    rw [h1.1, h2.1]

/-- Two test rules from one state with the same symbol coincide. -/
theorem det_test_dst (hB : B.Det) {q q₁ q₂ : Q} {i i' : ι} {b : Bool}
    (h₁ : ⟨q, .test i b, q₁⟩ ∈ B) (h₂ : ⟨q, .test i' b, q₂⟩ ∈ B) : i = i' ∧ q₁ = q₂ := by
  by_cases he : (⟨q, .test i b, q₁⟩ : Quad Q ι) = ⟨q, .test i' b, q₂⟩
  · simp only [Quad.mk.injEq, Op.test.injEq] at he; exact ⟨he.2.1.1, he.2.2⟩
  · obtain ⟨j, c, c', h1, h2, hc⟩ := hB _ h₁ _ h₂ he rfl
    simp only [Op.test.injEq] at h1 h2
    exact absurd (h1.2.symm.trans h2.2) hc

/-- A non-test rule is the only rule from its state. -/
theorem det_nontest (hB : B.Det) {q q₁ q₂ : Q} {o o' : Op ι}
    (h₁ : ⟨q, o, q₁⟩ ∈ B) (h₂ : ⟨q, o', q₂⟩ ∈ B) (ho : ∀ i b, o ≠ .test i b) :
    o = o' ∧ q₁ = q₂ := by
  by_cases he : (⟨q, o, q₁⟩ : Quad Q ι) = ⟨q, o', q₂⟩
  · simp only [Quad.mk.injEq] at he; exact ⟨he.2.1, he.2.2⟩
  · obtain ⟨j, c, c', h1, -, -⟩ := hB _ h₁ _ h₂ he rfl
    exact absurd h1 (ho _ _)

/-- Two test rules into one state test one counter. -/
theorem rev_test_counter (hB : B.Rev) {s q₁ q₂ : Q} {i i' : ι} {b b' : Bool}
    (h₁ : ⟨q₁, .test i b, s⟩ ∈ B) (h₂ : ⟨q₂, .test i' b', s⟩ ∈ B) : i = i' := by
  by_cases he : (⟨q₁, .test i b, s⟩ : Quad Q ι) = ⟨q₂, .test i' b', s⟩
  · simp only [Quad.mk.injEq, Op.test.injEq] at he; exact he.2.1.1
  · obtain ⟨j, c, c', h1, h2, -⟩ := hB _ h₁ _ h₂ he rfl
    simp only [Op.test.injEq] at h1 h2
    rw [h1.1, h2.1]

/-- A non-test rule is the only rule into its state. -/
theorem rev_nontest (hB : B.Rev) {s q₁ q₂ : Q} {o o' : Op ι}
    (h₁ : ⟨q₁, o, s⟩ ∈ B) (h₂ : ⟨q₂, o', s⟩ ∈ B) (ho : ∀ i b, o ≠ .test i b) :
    o = o' ∧ q₁ = q₂ := by
  by_cases he : (⟨q₁, o, s⟩ : Quad Q ι) = ⟨q₂, o', s⟩
  · simp only [Quad.mk.injEq] at he; exact ⟨he.2.1, he.1⟩
  · obtain ⟨j, c, c', h1, -, -⟩ := hB _ h₁ _ h₂ he rfl
    exact absurd h1 (ho _ _)

/-- Two test rules into one state with the same symbol coincide. -/
theorem rev_test_src (hB : B.Rev) {s q₁ q₂ : Q} {i i' : ι} {b : Bool}
    (h₁ : ⟨q₁, .test i b, s⟩ ∈ B) (h₂ : ⟨q₂, .test i' b, s⟩ ∈ B) : i = i' ∧ q₁ = q₂ := by
  by_cases he : (⟨q₁, .test i b, s⟩ : Quad Q ι) = ⟨q₂, .test i' b, s⟩
  · simp only [Quad.mk.injEq, Op.test.injEq] at he; exact ⟨he.2.1.1, he.1⟩
  · obtain ⟨j, c, c', h1, h2, hc⟩ := hB _ h₁ _ h₂ he rfl
    simp only [Op.test.injEq] at h1 h2
    exact absurd (h1.2.symm.trans h2.2) hc

/-- The compile is deterministic. -/
theorem godel_det (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) : (godel B p N).Det := by
  rintro r₁ h₁ r₂ h₂ hne hsrc
  cases h₁ <;> cases h₂ <;> simp only [GState.ent.injEq, GState.grd.injEq, GState.a₁.injEq,
    GState.a₂.injEq, GState.a₃.injEq, GState.a₄.injEq, GState.b₁.injEq, GState.b₂.injEq,
    GState.b₃.injEq, GState.mul.injEq, GState.dv.injEq, GState.w₁.injEq, GState.w₂.injEq,
    GState.r₁.injEq, GState.r₂.injEq, reduceCtorEq] at hsrc
  all_goals try (simp_all; done)
  case nop.nop q₁ q₁' h₁ q₂ q₂' h₂ =>
    subst hsrc
    obtain rfl := (det_nontest hB h₁ h₂ (by simp)).2
    exact absurd rfl hne
  case nop.aIn q₁ q₁' h₁ q₂ i q₂' h₂ =>
    subst hsrc
    rcases h₂ with h₂ | h₂ <;> exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case nop.wIn q₁ q₁' h₁ q₂ i b q₂' j h₂ hj =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case aIn.nop q₂ i q₂' h₂ q₁ q₁' h₁ =>
    subst hsrc
    rcases h₂ with h₂ | h₂ <;> exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case aIn.wIn q₁ i q₁' h₁ q₂ i' b q₂' j h₂ hj =>
    subst hsrc
    rcases h₁ with h₁ | h₁ <;> exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case b₁Z.b₁Z q₁ i q₁' h₁ q₂ i' q₂' h₂ =>
    subst hsrc
    obtain rfl : q₁' = q₂' := by
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
        exact (det_nontest hB h₁ h₂ (by simp)).2
    exact absurd rfl hne
  case mulIn.dvIn q₁ i q₁' h₁ q₂ i' q₂' j h₂ hj =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case mulB₂.mulB₂ q₁ i q₁' j h₁ hj q₂ i' q₂' j' h₂ hj' =>
    subst hsrc
    obtain rfl : j = j' := Fin.ext (by omega)
    exact absurd rfl hne
  case mulB₂.dvB₂ q₁ i q₁' j h₁ hj q₂ i' q₂' h₂ =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case mulStep.mulStep q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : j₁' = j₂' := Fin.ext (by omega)
    exact absurd rfl hne
  case mulStep.mulLast q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    omega
  case mulLast.mulStep q₂ i' q₂' j₂ h₂ c₁ q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    omega
  case dvIn.mulIn q₂ i' q₂' j h₂ hj q₁ i q₁' h₁ =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case dvIn.dvIn q₁ i q₁' j h₁ hj q₂ i' q₂' j' h₂ hj' =>
    subst hsrc
    obtain rfl : j = j' := Fin.ext (by omega)
    exact absurd rfl hne
  case dvStep.dvStep q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : j₁' = j₂' := Fin.ext (by omega)
    exact absurd rfl hne
  case dvStep.dvLast q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    omega
  case dvLast.dvStep q₂ i' q₂' j₂ h₂ c₁ q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    omega
  case dvB₂.mulB₂ q₂ i' q₂' h₂ q₁ i q₁' j h₁ hj =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case wIn.nop q₂ i b q₂' j h₂ hj q₁ q₁' h₁ =>
    subst hsrc
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case wIn.aIn q₂ i' b q₂' j h₂ hj q₁ i q₁' h₁ =>
    subst hsrc
    rcases h₁ with h₁ | h₁ <;> exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case wP.wInc q₁ i b q₁' j h₁ a₁ q₂ i' b' q₂' j' h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wDec.wDec q₁ i b q₁' j₁ j₁' h₁ a₁ a₂ q₂ i' b' q₂' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : j₁' = j₂' := Fin.ext (by omega)
    exact absurd rfl hne
  case wDec.wBack q₁ i b q₁' j₁ j₁' h₁ a₁ a₂ q₂ i' b' q₂' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wInc.wP q₂ i' b' q₂' j' h₂ c₁ q₁ i b q₁' j h₁ a₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wInc.exitP q₁ i b q₁' j h₁ a₁ q₂ i' q₂' j' h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    have := (hp.prime i).two_le
    omega
  case wInc.exitZ q₁ i b q₁' j h₁ a₁ q₂ i' q₂' j' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wBack.wDec q₂ i' b' q₂' j₂ j₂' h₂ c₁ c₂ q₁ i b q₁' j₁ j₁' h₁ a₁ a₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case exitP.wInc q₂ i' q₂' j' h₂ c₁ q₁ i b q₁' j h₁ a₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    have := (hp.prime i).two_le
    omega
  case exitP.exitP q₁ i q₁' j h₁ a₁ q₂ i' q₂' j' h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain ⟨rfl, rfl⟩ := det_test_dst hB h₁ h₂
    exact absurd rfl hne
  case exitZ.wInc q₂ i' q₂' j' h₂ c₁ c₂ q₁ i b q₁' j h₁ a₁ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case exitZ.exitZ q₁ i q₁' j h₁ a₁ a₂ q₂ i' q₂' j' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain ⟨rfl, rfl⟩ := det_test_dst hB h₁ h₂
    exact absurd rfl hne
  case rDec.rDec q₁ i b s j j₁' h₁ a₁ a₂ q₂ i' b' s' j' j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl := rev_test_counter hB' h₁ h₂
    obtain rfl : j₁' = j₂' := Fin.ext (by omega)
    exact absurd rfl hne
  case rBack.rBack q₁ i b s j j₁' h₁ a₁ a₂ a₃ q₂ i' b' s' j' j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hsrc
    obtain rfl : j₁' = j₂' := Fin.ext (by omega)
    exact absurd rfl hne

/-- The compile is reversible. -/
theorem godel_rev (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) : (godel B p N).Rev := by
  rintro r₁ h₁ r₂ h₂ hne hdst
  cases h₁ <;> cases h₂ <;> simp only [GState.ent.injEq, GState.grd.injEq, GState.a₁.injEq,
    GState.a₂.injEq, GState.a₃.injEq, GState.a₄.injEq, GState.b₁.injEq, GState.b₂.injEq,
    GState.b₃.injEq, GState.mul.injEq, GState.dv.injEq, GState.w₁.injEq, GState.w₂.injEq,
    GState.r₁.injEq, GState.r₂.injEq, reduceCtorEq] at hdst
  all_goals try (simp_all; done)
  case nop.nop q₁ s h₁ q₂ s' h₂ =>
    subst hdst
    obtain rfl := (rev_nontest hB' h₁ h₂ (by simp)).2
    exact absurd rfl hne
  case nop.b₁Z q₁ s h₁ q₂ i s' h₂ =>
    subst hdst
    rcases h₂ with h₂ | h₂ <;> exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case nop.rZ q₁ s h₁ q₂ i b s' j h₂ hj =>
    subst hdst
    exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case b₁Z.nop q₂ i s' h₂ q₁ s h₁ =>
    subst hdst
    rcases h₂ with h₂ | h₂ <;> exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case b₁Z.b₁Z q₁ i s h₁ q₂ i' s' h₂ =>
    subst hdst
    obtain rfl : q₁ = q₂ := by
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
        exact (rev_nontest hB' h₁ h₂ (by simp)).2
    exact absurd rfl hne
  case b₁Z.rZ q₁ i s h₁ q₂ i' b s' j h₂ hj =>
    subst hdst
    rcases h₁ with h₁ | h₁ <;> exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case rZ.nop q₂ i b s' j h₂ hj q₁ s h₁ =>
    subst hdst
    exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case rZ.b₁Z q₂ i' b s' j h₂ hj q₁ i s h₁ =>
    subst hdst
    rcases h₁ with h₁ | h₁ <;> exact absurd (rev_nontest hB' h₁ h₂ (by simp)).1 (by simp)
  case mulIn.dvLast q₁ i q₁' h₁ q₂ i' q₂' j h₂ hj =>
    subst hdst
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case dvLast.mulIn q₂ i' q₂' j h₂ hj q₁ i q₁' h₁ =>
    subst hdst
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case mulLast.dvB₂ q₁ i q₁' j h₁ hj q₂ i' q₂' h₂ =>
    subst hdst
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case dvB₂.mulLast q₂ i' q₂' h₂ q₁ i q₁' j h₁ hj =>
    subst hdst
    exact absurd (det_nontest hB h₁ h₂ (by simp)).1 (by simp)
  case mulStep.mulStep q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case dvStep.dvStep q₁ i q₁' j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' q₂' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case mulLast.mulLast q₁ i q₁' j₁ h₁ a₁ q₂ i' q₂' j₂ h₂ c₁ =>
    subst hdst
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case dvLast.dvLast q₁ i q₁' j₁ h₁ a₁ q₂ i' q₂' j₂ h₂ c₁ =>
    subst hdst
    obtain rfl : i = i' := by simpa using (det_nontest hB h₁ h₂ (by simp)).1
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case wP.wInc q₁ i b q₁' j h₁ a₁ q₂ i' b' q₂' j' h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wInc.wP q₂ i' b' q₂' j' h₂ c₁ q₁ i b q₁' j h₁ a₁ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := det_test_counter hB h₁ h₂
    omega
  case wDec.wDec q₁ i b q₁' j₁ j₁' h₁ a₁ a₂ q₂ i' b' q₂' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case wBack.wBack q₁ i b q₁' j₁ j₁' h₁ a₁ a₂ q₂ i' b' q₂' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := det_test_counter hB h₁ h₂
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne
  case exitP.exitP q₁ i s j₁ h₁ a₁ q₂ i' s' j₂ h₂ c₁ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain ⟨rfl, rfl⟩ := rev_test_src hB' h₁ h₂
    exact absurd rfl hne
  case exitZ.exitZ q₁ i s j₁ h₁ a₁ a₂ q₂ i' s' j₂ h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain ⟨rfl, rfl⟩ := rev_test_src hB' h₁ h₂
    exact absurd rfl hne
  case exitP.rDec q₁ i s j₁ h₁ a₁ q₂ i' b s' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    have := (hp.prime i').two_le
    omega
  case rDec.exitP q₂ i' b s' j₂ j₂' h₂ c₁ c₂ q₁ i s j₁ h₁ a₁ =>
    obtain ⟨rfl, rfl⟩ := hdst
    have := (hp.prime i').two_le
    omega
  case exitZ.rDec q₁ i s j₁ h₁ a₁ a₂ q₂ i' b s' j₂ j₂' h₂ c₁ c₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := rev_test_counter hB' h₁ h₂
    omega
  case rDec.exitZ q₂ i' b s' j₂ j₂' h₂ c₁ c₂ q₁ i s j₁ h₁ a₁ a₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := rev_test_counter hB' h₁ h₂
    omega
  case rDec.rBack q₁ i b s j₁ j₁' h₁ a₁ a₂ q₂ i' b' s' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := rev_test_counter hB' h₁ h₂
    omega
  case rBack.rDec q₂ i' b' s' j₂ j₂' h₂ c₁ c₂ c₃ q₁ i b s j₁ j₁' h₁ a₁ a₂ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl := rev_test_counter hB' h₁ h₂
    omega
  case rBack.rBack q₁ i b s j₁ j₁' h₁ a₁ a₂ a₃ q₂ i' b' s' j₂ j₂' h₂ c₁ c₂ c₃ =>
    obtain ⟨rfl, rfl⟩ := hdst
    obtain rfl : j₁ = j₂ := Fin.ext (by omega)
    exact absurd rfl hne

/-- No rule enters `ent q₀` when no rule of `B` enters `q₀`. -/
theorem godel_normalAt {q₀ : Q} (hB : B.NormalAt q₀) : (godel B p N).NormalAt (.ent q₀) := by
  intro r hr h
  cases hr <;> simp only [GState.ent.injEq, reduceCtorEq] at h
  · exact hB _ ‹_› h
  · rename_i hm; rcases hm with hm | hm <;> exact hB _ hm h
  · exact hB _ ‹_› h

/-- Rank of a compile state: rules off the boundary never lower it. -/
def grank : GState Q N → ℕ
  | .ent _ => 5
  | .grd _ => 0
  | .a₁ _ | .a₂ _ | .a₃ _ | .a₄ _ => 1
  | .b₁ _ | .b₂ _ | .b₃ _ | .mul _ _ | .dv _ _ => 2
  | .w₁ _ _ | .w₂ _ _ => 3
  | .r₁ _ _ | .r₂ _ _ => 4

/-- The counter a family's laps lower (`x` on odd ranks, `y` on even ones). -/
def gdn (k : ℕ) : Fin 2 := if k % 2 = 1 then 0 else 1

/-- The counter a family's laps raise. -/
def gup (k : ℕ) : Fin 2 := if k % 2 = 1 then 1 else 0

open Classical in
/-- Every rule but a decrement of `gdn` raises `gD`. -/
noncomputable def gD (B : CM Q ι) : GState Q N → ℤ
  | .a₁ _ => 2
  | .a₂ _ => 3
  | .a₄ _ => 1
  | .b₂ q => if ∃ i q', (⟨q, .inc i, q'⟩ : Quad Q ι) ∈ B then 1 else -5
  | .b₃ _ => -1
  | .mul _ j => (j.val : ℤ) - (N + 3)
  | .dv _ _ => 1
  | .w₁ _ j => if j.val = 0 then 10 else 0
  | .w₂ _ j => if j.val = 0 then 11 else 1
  | .r₁ _ j => -2 * j.val
  | .r₂ _ j => if j.val = 0 then 1 else -2 * j.val + 1
  | _ => 0

open Classical in
/-- Every rule but an increment of `gup` raises `gI`. -/
noncomputable def gI (B : CM Q ι) (p : ι → ℕ) : GState Q N → ℤ
  | .a₁ _ => 1
  | .a₂ _ => 2
  | .a₃ _ => 3
  | .b₂ q => if ∃ i q', (⟨q, .dec i, q'⟩ : Quad Q ι) ∈ B then N + 5 else 1
  | .b₃ _ => -1
  | .mul _ _ => 2
  | .dv _ j => j.val
  | .w₁ _ j => 2 * j.val
  | .w₂ q j => if ∃ i b q', (⟨q, .test i b, q'⟩ : Quad Q ι) ∈ B ∧ j.val = p i then -1
      else 2 * j.val + 1
  | .r₁ _ j => if j.val = 0 then 0 else 2
  | .r₂ _ j => if j.val = 0 then 1 else -10
  | _ => 0

theorem grule_lap (hB : B.Det) (hp : PrimeData p N) {r : Quad (GState Q N) (Fin 2)}
    (hr : GRule B p N r) (hs : r.src ∉ Set.range GState.ent)
    (hd : r.dst ∉ Set.range GState.ent) :
    grank r.src ≤ grank r.dst ∧ (grank r.src = grank r.dst →
      r.op.delta (gdn (grank r.src)) ≤ 0 ∧ 0 ≤ r.op.delta (gup (grank r.src)) ∧
      (r.op = .dec (gdn (grank r.src)) ∨ gD (N := N) B r.src < gD B r.dst) ∧
      (r.op = .inc (gup (grank r.src)) ∨ gI (N := N) B p r.src < gI B p r.dst)) := by
  cases hr <;> simp [grank, gD, gI, gdn, gup, Op.delta] at hs hd ⊢
  all_goals try omega
  case mulIn q i q' h =>
    rw [if_pos, if_neg]
    · omega
    · rintro ⟨i', q'', h'⟩; exact absurd (det_nontest hB h h' (by simp)).1 (by simp)
    · exact ⟨i, q', h⟩
  case mulB₂ q i q' j h hj =>
    rw [if_neg]
    rintro ⟨i', q'', h'⟩; exact absurd (det_nontest hB h h' (by simp)).1 (by simp)
  case dvLast q i q' j h hj =>
    rw [if_pos]
    · have := hp.le i; omega
    · exact ⟨i, q', h⟩
  case dvB₂ q i q' h =>
    rw [if_neg]
    · omega
    · rintro ⟨i', q'', h'⟩; exact absurd (det_nontest hB h h' (by simp)).1 (by simp)
  case wP q i b q' j h hj =>
    have hc : ¬ ∃ i' b' q'', (⟨q, .test i' b', q''⟩ : Quad Q ι) ∈ B ∧ j.val = p i' := by
      rintro ⟨i', b', q'', h', hj'⟩; obtain rfl := det_test_counter hB h h'; omega
    rw [if_neg hc]
    simp only [Fin.ext_iff, Fin.val_zero]
    refine ⟨by split_ifs <;> omega, by omega⟩
  case wBack q i b q' j j' h hj hj' =>
    have hc : ∃ i' b' q'', (⟨q, .test i' b', q''⟩ : Quad Q ι) ∈ B ∧ j.val = p i' :=
      ⟨i, b, q', h, hj⟩
    rw [if_pos hc]
    have := (hp.prime i).two_le
    simp only [Fin.ext_iff, Fin.val_zero]
    refine ⟨by split_ifs <;> omega, by omega⟩
  all_goals
    simp only [Fin.ext_iff, Fin.val_zero, Fin.lt_def] at *
    try have := (hp.prime ‹ι›).two_le
    (try split_ifs) <;> omega

/-- A potential that every non-`P` step of a closed walk raises forces a `P` step. -/
theorem walk_exists {X : Type*} (f : X → ℤ) (src dst : ℕ → X) {m : ℕ} (hm : 0 < m)
    (hchain : ∀ i, i + 1 < m → dst i = src (i + 1)) (hclose : dst (m - 1) = src 0)
    (P : ℕ → Prop) (h : ∀ i, i < m → P i ∨ f (src i) < f (dst i)) : ∃ i, i < m ∧ P i := by
  by_contra hne
  push Not at hne
  have h0 := walk_sum_zero f src dst hm hchain hclose
  have : 0 < ∑ i ∈ Finset.range m, (f (dst i) - f (src i)) :=
    Finset.sum_pos (fun i hi => by
      have := (h i (Finset.mem_range.1 hi)).resolve_left (hne i (Finset.mem_range.1 hi))
      omega) ⟨0, Finset.mem_range.2 hm⟩
  omega

/-- **(S1) for the compile.**  Every loop off the boundary is one wheel or transfer, with lap
`(−1, +1)`, `(+p, −1)`, `(+1, −p)`, `(−p, +1)` or `(+p, −1)`. -/
theorem godel_lapsMixed (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) :
    LapsMixed (godel B p N) (Set.range GState.ent) := by
  intro ρ m hm hmem hoff hchain hclose
  have hdoff : ∀ i, i < m → (ρ i).dst ∉ Set.range GState.ent := by
    intro i hi
    by_cases h : i + 1 < m
    · rw [hchain i h]; exact hoff _ h
    · rw [show i = m - 1 by omega, hclose]; exact hoff 0 hm
  have key := fun i (hi : i < m) => grule_lap hB hp (hmem i hi) (hoff i hi) (hdoff i hi)
  -- the rank is constant along the walk
  have hmono : ∀ j, j < m → ∀ i, i ≤ j → grank (ρ i).src ≤ grank (ρ j).src := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [show i = 0 by omega]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans
          ((key j (by omega)).1.trans (le_of_eq (by rw [hchain j hj])))
      · rw [show i = j + 1 by omega]
  have hconst : ∀ i, i < m → grank (ρ i).src = grank (ρ 0).src ∧
      grank (ρ i).dst = grank (ρ 0).src := by
    intro i hi
    have h0 := hmono i hi 0 (Nat.zero_le _)
    have h1 := (key i hi).1
    have h2 : grank (ρ i).dst ≤ grank (ρ 0).src := by
      by_cases h : i + 1 < m
      · rw [hchain i h]
        calc grank (ρ (i + 1)).src ≤ grank (ρ (m - 1)).src := hmono _ (by omega) _ (by omega)
          _ ≤ grank (ρ (m - 1)).dst := (key _ (by omega)).1
          _ = _ := by rw [hclose]
      · rw [show i = m - 1 by omega, hclose]
    omega
  set k := grank (ρ 0).src
  have hid : ∀ i, i < m → _ := fun i hi => by
    have := (key i hi).2 ((hconst i hi).1.trans (hconst i hi).2.symm)
    rw [(hconst i hi).1] at this
    exact this
  obtain ⟨i₁, hi₁, h₁⟩ := walk_exists (gD (N := N) B) (fun i => (ρ i).src) (fun i => (ρ i).dst)
    hm hchain hclose (fun i => (ρ i).op = .dec (gdn k)) fun i hi => (hid i hi).2.2.1
  obtain ⟨i₂, hi₂, h₂⟩ := walk_exists (gI (N := N) B p) (fun i => (ρ i).src)
    (fun i => (ρ i).dst) hm hchain hclose (fun i => (ρ i).op = .inc (gup k))
    fun i hi => (hid i hi).2.2.2
  refine ⟨⟨gdn k, ?_⟩, ⟨gup k, ?_⟩⟩
  · calc ∑ i ∈ Finset.range m, (ρ i).op.delta (gdn k)
        < ∑ i ∈ Finset.range m, (0 : ℤ) :=
          Finset.sum_lt_sum (fun i hi => (hid i (Finset.mem_range.1 hi)).1)
            ⟨i₁, Finset.mem_range.2 hi₁, by rw [h₁]; simp [Op.delta]⟩
      _ = 0 := by simp
  · calc (0 : ℤ) = ∑ i ∈ Finset.range m, (0 : ℤ) := by simp
      _ < ∑ i ∈ Finset.range m, (ρ i).op.delta (gup k) :=
          Finset.sum_lt_sum (fun i hi => (hid i (Finset.mem_range.1 hi)).2.1)
            ⟨i₂, Finset.mem_range.2 hi₂, by rw [h₂]; simp [Op.delta]⟩

/-- Two counters `x`, `y`. -/
def gc (x y : ℕ) : Fin 2 → ℕ := ![x, y]

theorem gc_ext (w : Fin 2 → ℕ) : w = gc (w 0) (w 1) := funext fun j => by fin_cases j <;> rfl

theorem act_t0 {x y : ℕ} {b : Bool} (h : decide (0 < x) = b) :
    (Op.test (0 : Fin 2) b).Act (gc x y) (gc x y) := ⟨h, rfl⟩

theorem act_t1 {x y : ℕ} {b : Bool} (h : decide (0 < y) = b) :
    (Op.test (1 : Fin 2) b).Act (gc x y) (gc x y) := ⟨h, rfl⟩

theorem act_dec0 (x y : ℕ) : (Op.dec (0 : Fin 2)).Act (gc (x + 1) y) (gc x y) :=
  ⟨Nat.succ_pos x, rfl, fun j hj => by fin_cases j; exact absurd rfl hj; rfl⟩

theorem act_dec1 (x y : ℕ) : (Op.dec (1 : Fin 2)).Act (gc x (y + 1)) (gc x y) :=
  ⟨Nat.succ_pos y, rfl, fun j hj => by fin_cases j; rfl; exact absurd rfl hj⟩

theorem act_inc0 (x y : ℕ) : (Op.inc (0 : Fin 2)).Act (gc x y) (gc (x + 1) y) :=
  ⟨rfl, fun j hj => by fin_cases j; exact absurd rfl hj; rfl⟩

theorem act_inc1 (x y : ℕ) : (Op.inc (1 : Fin 2)).Act (gc x y) (gc x (y + 1)) :=
  ⟨rfl, fun j hj => by fin_cases j; rfl; exact absurd rfl hj⟩

/-- One step off the boundary. -/
def GOff (B : CM Q ι) (p : ι → ℕ) (N : ℕ) (c d : Cfg (GState Q N) (Fin 2)) : Prop :=
  (godel B p N).Step c d ∧ d.1 ∉ Set.range GState.ent

theorem goff_of {r : Quad (GState Q N) (Fin 2)} (hr : GRule B p N r)
    {s t : GState Q N} {w w' : Fin 2 → ℕ} (hs : s = r.src) (hd : t = r.dst)
    (ha : r.op.Act w w') (hB : t ∉ Set.range GState.ent) : GOff B p N (s, w) (t, w') :=
  ⟨⟨r, hr, hs, hd, ha⟩, hB⟩

local notation "RT" => Relation.ReflTransGen (GOff B p N)

/-- Transfer `x → y`. -/
theorem g_transfer {q : Q} {i : ι} {q' : Q} (hm : MoveRule B q i q') (t : ℕ) : ∀ x y,
    RT (.a₁ q, gc (x + t) y) (.a₁ q, gc x (y + t)) := by
  induction t with
  | zero => intro x y; exact .refl
  | succ t ih =>
    intro x y
    refine .head (goff_of (.a₁P hm) rfl rfl (act_t0 (decide_eq_true (by omega))) (by simp)) ?_
    refine .head (goff_of (.a₂ hm) rfl rfl (act_dec0 _ _) (by simp)) ?_
    refine .head (goff_of (.a₃ hm) rfl rfl (act_inc1 _ _) (by simp)) ?_
    refine .head (goff_of (.a₄ hm) rfl rfl (act_t1 (decide_eq_true (by omega))) (by simp)) ?_
    rw [show y + (t + 1) = y + 1 + t by omega]
    exact ih x (y + 1)

/-- The multiply chain `mul j → b₃`. -/
theorem g_mulChain (hp : PrimeData p N) {q : Q} {i : ι} {q' : Q} (hm : ⟨q, .inc i, q'⟩ ∈ B)
    (y : ℕ) : ∀ k x (hj : p i - k < N + 1), 1 ≤ p i - k → k < p i →
    RT (.mul q ⟨p i - k, hj⟩, gc x y) (.b₃ q, gc (x + k + 1) y) := by
  intro k
  induction k with
  | zero =>
    intro x hj h1 h2
    exact .single (goff_of (.mulLast _ hm (by simp)) rfl rfl (act_inc0 _ _) (by simp))
  | succ k ih =>
    intro x hj h1 h2
    refine .head (goff_of (.mulStep _ ⟨p i - k, by have := hp.le i; omega⟩ hm h1 (by simp; omega)
      (by simp; omega)) rfl rfl (act_inc0 _ _) (by simp)) ?_
    rw [show x + (k + 1) + 1 = x + 1 + k + 1 by omega]
    exact ih _ _ (by omega) (by omega)

/-- Multiply loop: `(x, y) → (x + p · y, 0)` at `b₁`. -/
theorem g_mul (hp : PrimeData p N) {q : Q} {i : ι} {q' : Q} (hm : ⟨q, .inc i, q'⟩ ∈ B)
    (t : ℕ) : ∀ x, RT (.b₁ q, gc x t) (.b₁ q, gc (x + p i * t) 0) := by
  have hpi := (hp.prime i).two_le
  have hle := hp.le i
  induction t with
  | zero => intro x; exact .refl
  | succ t ih =>
    intro x
    refine .head (goff_of (.mulIn hm) rfl rfl (act_t1 (decide_eq_true (by omega))) (by simp)) ?_
    refine .head (goff_of (.mulB₂ ⟨1, by omega⟩ hm rfl) rfl rfl (act_dec1 _ _) (by simp)) ?_
    have hc := g_mulChain hp hm t (p i - 1) x (by omega) (by omega) (by omega)
    simp only [show p i - (p i - 1) = 1 by omega] at hc
    refine hc.trans ?_
    refine .head (goff_of (.b₃ (.inl hm)) rfl rfl (act_t0 (decide_eq_true (by omega)))
      (by simp)) ?_
    rw [show x + p i * (t + 1) = x + (p i - 1) + 1 + p i * t by
      rw [Nat.mul_succ]; omega]
    exact ih _

/-- The divide chain: `dv j → dv (j + m)` takes `m` from `y`. -/
theorem g_dvChain (hp : PrimeData p N) {q : Q} {i : ι} {q' : Q} (hm : ⟨q, .dec i, q'⟩ ∈ B)
    (x y : ℕ) (m : ℕ) : ∀ j (hj : j < N + 1), 1 ≤ j → (hjm : j + m ≤ p i) →
    RT (.dv q ⟨j, hj⟩, gc x (y + m)) (.dv q ⟨j + m, by have := hp.le i; omega⟩, gc x y) := by
  induction m with
  | zero => intro j hj _ _; exact .refl
  | succ m ih =>
    intro j hj h1 h2
    refine .head (goff_of (.dvStep ⟨j, hj⟩ ⟨j + 1, by have := hp.le i; omega⟩ hm h1
      (by simp; omega) rfl) rfl rfl
      (by rw [show y + (m + 1) = y + m + 1 by omega]; exact act_dec1 _ _) (by simp)) ?_
    have := ih (j + 1) (by have := hp.le i; omega) (by omega) (by omega)
    simp only [show j + 1 + m = j + (m + 1) by omega] at this
    exact this

/-- Divide loop with remainder: `(x, p · t + r) → (x + t, r)` at `b₁`. -/
theorem g_dv (hp : PrimeData p N) {q : Q} {i : ι} {q' : Q} (hm : ⟨q, .dec i, q'⟩ ∈ B)
    (r t : ℕ) : ∀ x, RT (.b₁ q, gc x (p i * t + r)) (.b₁ q, gc (x + t) r) := by
  have hpi := (hp.prime i).two_le
  have hle := hp.le i
  induction t with
  | zero => intro x; simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exact .refl
  | succ t ih =>
    intro x
    refine .head (goff_of (.dvIn ⟨1, by omega⟩ hm rfl) rfl rfl
      (act_t1 (decide_eq_true (by rw [Nat.mul_succ]; omega))) (by simp)) ?_
    have hc := g_dvChain hp hm x (p i * t + r + 1) (p i - 1) 1 (by omega) le_rfl (by omega)
    simp only [show 1 + (p i - 1) = p i by omega,
      show p i * t + r + 1 + (p i - 1) = p i * (t + 1) + r by rw [Nat.mul_succ]; omega] at hc
    refine hc.trans ?_
    refine .head (goff_of (.dvLast _ hm rfl) rfl rfl (act_dec1 _ _) (by simp)) ?_
    refine .head (goff_of (.dvB₂ hm) rfl rfl (act_inc0 _ _) (by simp)) ?_
    refine .head (goff_of (.b₃ (.inr hm)) rfl rfl (act_t0 (decide_eq_true (by omega)))
      (by simp)) ?_
    rw [show x + (t + 1) = x + 1 + t by omega]
    exact ih _

/-- The division wheel, inner part: `w₁ j → w₁ (j + m)` takes `m` from `x`. -/
theorem g_wChain (hp : PrimeData p N) {q : Q} {i : ι} {b : Bool} {q' : Q}
    (hm : ⟨q, .test i b, q'⟩ ∈ B) (x y m : ℕ) : ∀ j (hj : j < N + 1), (hjm : j + m ≤ p i) →
    RT (.w₁ q ⟨j, hj⟩, gc (x + m) y) (.w₁ q ⟨j + m, by have := hp.le i; omega⟩, gc x y) := by
  induction m with
  | zero => intro j hj _; exact .refl
  | succ m ih =>
    intro j hj h2
    refine .head (goff_of (.wP ⟨j, hj⟩ hm (by simp; omega)) rfl rfl
      (act_t0 (decide_eq_true (by omega))) (by simp)) ?_
    refine .head (goff_of (.wDec ⟨j, hj⟩ ⟨j + 1, by have := hp.le i; omega⟩ hm (by simp; omega)
      rfl) rfl rfl
      (by rw [show x + (m + 1) = x + m + 1 by omega]; exact act_dec0 _ _) (by simp)) ?_
    have := ih (j + 1) (by have := hp.le i; omega) (by omega)
    simp only [show j + 1 + m = j + (m + 1) by omega] at this
    exact this

/-- Division wheel laps: `(x + p · t, y) → (x, y + t)` at `w₁ 0`. -/
theorem g_w (hp : PrimeData p N) {q : Q} {i : ι} {b : Bool} {q' : Q}
    (hm : ⟨q, .test i b, q'⟩ ∈ B) (x t : ℕ) : ∀ y,
    RT (.w₁ q ⟨0, by omega⟩, gc (x + p i * t) y) (.w₁ q ⟨0, by omega⟩, gc x (y + t)) := by
  have hpi := (hp.prime i).two_le
  have hle := hp.le i
  induction t with
  | zero => intro y; exact .refl
  | succ t ih =>
    intro y
    have hc := g_wChain hp hm (x + p i * t) y (p i) 0 (by omega) (by omega)
    simp only [Nat.zero_add] at hc
    rw [show x + p i * (t + 1) = x + p i * t + p i by ring]
    refine hc.trans ?_
    refine .head (goff_of (.wInc _ hm rfl) rfl rfl (act_inc1 _ _) (by simp)) ?_
    refine .head (goff_of (.wBack _ ⟨0, by omega⟩ hm rfl rfl) rfl rfl
      (act_t1 (decide_eq_true (by omega))) (by simp)) ?_
    rw [show y + (t + 1) = y + 1 + t by omega]
    exact ih _

/-- Restore descent: `r₁ j → r₁ 0` adds `j` to `x`. -/
theorem g_rDesc {q : Q} {i : ι} {b : Bool} {s : Q}
    (hm : ⟨q, .test i b, s⟩ ∈ B) (y j : ℕ) : ∀ x (hj : j < N + 1), j ≤ p i →
    RT (.r₁ s ⟨j, hj⟩, gc x y) (.r₁ s ⟨0, by omega⟩, gc (x + j) y) := by
  induction j with
  | zero => intro x hj _; exact .refl
  | succ j ih =>
    intro x hj h2
    refine .head (goff_of (.rInc ⟨j + 1, hj⟩ hm (by simp) h2) rfl rfl (act_inc0 _ _)
      (by simp)) ?_
    refine .head (goff_of (.rBack ⟨j + 1, hj⟩ ⟨j, by omega⟩ hm (by simp) h2 rfl) rfl rfl
      (act_t0 (decide_eq_true (by omega))) (by simp)) ?_
    rw [show x + (j + 1) = x + 1 + j by omega]
    exact ih _ _ (by omega)

/-- Restore laps: `(x, t) → (x + p · t, 0)` at `r₁ 0`. -/
theorem g_r (hp : PrimeData p N) {q : Q} {i : ι} {b : Bool} {s : Q}
    (hm : ⟨q, .test i b, s⟩ ∈ B) (t : ℕ) : ∀ x,
    RT (.r₁ s ⟨0, by omega⟩, gc x t) (.r₁ s ⟨0, by omega⟩, gc (x + p i * t) 0) := by
  have hpi := (hp.prime i).two_le
  have hle := hp.le i
  induction t with
  | zero => intro x; exact .refl
  | succ t ih =>
    intro x
    refine .head (goff_of (.rP _ hm rfl) rfl rfl (act_t1 (decide_eq_true (by omega)))
      (by simp)) ?_
    refine .head (goff_of (.rDec _ ⟨p i, by omega⟩ hm rfl rfl) rfl rfl (act_dec1 _ _)
      (by simp)) ?_
    refine (g_rDesc hm t (p i) x _ le_rfl).trans ?_
    rw [show x + p i * (t + 1) = x + p i + p i * t by ring]
    exact ih _

theorem gmacro_of {c : Cfg (GState Q N) (Fin 2)} {s t : GState Q N} {w w' : Fin 2 → ℕ}
    {r : Quad (GState Q N) (Fin 2)} (hc : c.1 ∈ Set.range GState.ent) (hchain : RT c (s, w))
    (hr : GRule B p N r) (hs : s = r.src) (hd : t = r.dst) (ha : r.op.Act w w')
    (ht : t ∈ Set.range GState.ent) :
    RcwaMachine.MacroStep (Set.range GState.ent) (godel B p N).Step c (t, w') :=
  macroStep_of_chain hc hchain ⟨r, hr, hs, hd, ha⟩ ht

/-- **Faithfulness.**  On a configuration encoding `v` with junk `J` coprime to every `p i`, a
step of `B` is one macro step of the compile. -/
theorem godel_macro [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) {J : ℕ} (hJ : 0 < J)
    (hJp : ∀ i, ¬ p i ∣ J) {q q' : Q} {v v' : ι → ℕ} (hstep : B.Step (q, v) (q', v')) :
    RcwaMachine.MacroStep (Set.range GState.ent) (godel B p N).Step
      (.ent q, genc p J v) (.ent q', genc p J v') := by
  obtain ⟨⟨src, op, dst⟩, hρ, h1, h2, h3⟩ := hstep
  simp only at h1 h2 h3
  subst h1 h2
  have hX := enc_pos hp hJ v
  change RcwaMachine.MacroStep _ _ (GState.ent q, gc (J * ∏ k, p k ^ v k) 0)
    (GState.ent q', gc (J * ∏ k, p k ^ v' k) 0)
  set X := J * ∏ k, p k ^ v k with hXdef
  have hg : RT (.ent q, gc X 0) (.grd q, gc X 0) :=
    .single (goff_of (.guard q) rfl rfl (act_t0 (decide_eq_true hX)) (by simp))
  cases op with
  | nop =>
    cases h3
    exact gmacro_of (by simp) hg (.nop hρ) rfl rfl (act_t1 rfl) (by simp)
  | inc i =>
    have hm : MoveRule B q i q' := .inl hρ
    rw [enc_inc h3 J, ← hXdef]
    refine gmacro_of (by simp) (hg.trans ?_) (.b₁Z hm) rfl rfl (act_t1 rfl) (by simp)
    refine .head (goff_of (.aIn hm) rfl rfl (act_t1 rfl) (by simp)) ?_
    have ht := g_transfer (p := p) (N := N) hm X 0 0
    simp only [Nat.zero_add] at ht
    refine ht.trans ?_
    refine .head (goff_of (.a₁Z hm) rfl rfl (act_t0 rfl) (by simp)) ?_
    have hmul := g_mul hp hρ X 0
    simp only [Nat.zero_add] at hmul
    exact hmul
  | dec i =>
    have hm : MoveRule B q i q' := .inr hρ
    have hX' := enc_dec (p := p) h3 J
    rw [← hXdef] at hX'
    refine gmacro_of (by simp) (hg.trans ?_) (.b₁Z hm) rfl rfl (act_t1 rfl) (by simp)
    refine .head (goff_of (.aIn hm) rfl rfl (act_t1 rfl) (by simp)) ?_
    have ht := g_transfer (p := p) (N := N) hm X 0 0
    simp only [Nat.zero_add] at ht
    refine ht.trans ?_
    refine .head (goff_of (.a₁Z hm) rfl rfl (act_t0 rfl) (by simp)) ?_
    have hdv := g_dv hp hρ 0 (J * ∏ k, p k ^ v' k) 0
    rw [Nat.add_zero, ← hX', Nat.zero_add] at hdv
    exact hdv
  | test i b =>
    obtain ⟨hb, hvv⟩ := h3
    rw [hvv]
    have hpi := (hp.prime i).two_le
    have hle := hp.le i
    have hw : RT (.ent q, gc X 0) (.w₁ q ⟨0, by omega⟩, gc X 0) :=
      hg.tail (goff_of (.wIn _ hρ rfl) rfl rfl (act_t1 rfl) (by simp))
    cases b with
    | true =>
      obtain ⟨a, ha⟩ := (dvd_enc_iff hp hJp v i).2 (by simp at hb; omega)
      rw [← hXdef] at ha
      refine gmacro_of (by simp) (hw.trans ?_) (.rZ ⟨0, by omega⟩ hρ rfl) rfl rfl
        (act_t1 rfl) (by simp)
      have h1 := g_w hp hρ 0 a 0
      rw [Nat.zero_add, Nat.zero_add, ← ha] at h1
      refine h1.trans ?_
      refine .head (goff_of (.exitP ⟨0, by omega⟩ hρ rfl) rfl rfl (act_t0 rfl) (by simp)) ?_
      have h2 := g_r hp hρ a 0
      rw [Nat.zero_add, ← ha] at h2
      exact h2
    | false =>
      have hnd : ¬ p i ∣ X := by
        rw [hXdef, dvd_enc_iff hp hJp v i]; simpa using hb
      have hj1 : 1 ≤ X % p i := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      have hj2 : X % p i < p i := Nat.mod_lt _ (by omega)
      have hXe : X = X % p i + p i * (X / p i) := (Nat.mod_add_div X (p i)).symm
      refine gmacro_of (by simp) (hw.trans ?_) (.rZ ⟨0, by omega⟩ hρ rfl) rfl rfl
        (act_t1 rfl) (by simp)
      have h1 := g_w hp hρ (X % p i) (X / p i) 0
      rw [Nat.zero_add, ← hXe] at h1
      refine h1.trans ?_
      have h2 := g_wChain hp hρ 0 (X / p i) (X % p i) 0 (by omega) (by omega)
      simp only [Nat.zero_add] at h2
      refine h2.trans ?_
      refine .head (goff_of (.exitZ _ hρ hj1 hj2) rfl rfl (act_t0 rfl) (by simp)) ?_
      refine (g_rDesc hρ (X / p i) (X % p i) 0 _ hj2.le).trans ?_
      have h3 := g_r hp hρ (X / p i) (X % p i)
      rw [← hXe] at h3
      simpa using h3

theorem prod_fact [Fintype ι] (hp : PrimeData p N) (v : ι → ℕ) (q : ℕ) :
    (∏ k, p k ^ v k).factorization q = ∑ k, if p k = q then v k else 0 := by
  classical
  rw [Nat.factorization_prod fun k _ => (pow_pos (hp.prime k).pos _).ne']
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul, (hp.prime _).factorization, Finsupp.single_apply]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

theorem prod_fact_at [Fintype ι] (hp : PrimeData p N) (v : ι → ℕ) (i : ι) :
    (∏ k, p k ^ v k).factorization (p i) = v i := by
  rw [prod_fact hp, Finset.sum_eq_single i (fun k _ hk => if_neg fun e => hk (hp.inj e))
    (by simp), if_pos rfl]

/-- Every positive `x` is an encoding with junk coprime to every `p i`. -/
theorem exists_enc [Fintype ι] (hp : PrimeData p N) {x : ℕ} (hx : 0 < x) :
    ∃ (J : ℕ) (v : ι → ℕ), 0 < J ∧ (∀ i, ¬ p i ∣ J) ∧ x = J * ∏ k, p k ^ v k := by
  set v : ι → ℕ := fun i => x.factorization (p i)
  have hP : 0 < ∏ k, p k ^ v k := Finset.prod_pos fun k _ => pow_pos (hp.prime k).pos _
  have hdvd : ∏ k, p k ^ v k ∣ x := by
    rw [← Nat.factorization_le_iff_dvd hP.ne' hx.ne']
    intro q
    rw [prod_fact hp]
    by_cases hq : ∃ i, p i = q
    · obtain ⟨i, rfl⟩ := hq
      rw [Finset.sum_eq_single i (fun k _ hk => if_neg fun e => hk (hp.inj e)) (by simp),
        if_pos rfl]
    · rw [Finset.sum_eq_zero fun k _ => if_neg fun e => hq ⟨k, e⟩]
      exact Nat.zero_le _
  obtain ⟨J, hJ⟩ := hdvd
  have hJ0 : 0 < J := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hJ; omega
  refine ⟨J, v, hJ0, fun i hi => ?_, by rw [hJ, mul_comm]⟩
  have h1 := congrArg (fun n => n.factorization (p i)) hJ
  rw [Nat.factorization_mul hP.ne' hJ0.ne', Finsupp.add_apply, prod_fact_at hp] at h1
  have := (hp.prime i).factorization_pos_of_dvd hJ0.ne' hi
  simp only [v] at h1
  omega

theorem act_t0_inv {x y : ℕ} {b : Bool} {w : Fin 2 → ℕ}
    (h : (Op.test (0 : Fin 2) b).Act (gc x y) w) : decide (0 < x) = b := h.1

theorem act_dec1_inv {x y : ℕ} {w : Fin 2 → ℕ}
    (h : (Op.dec (1 : Fin 2)).Act (gc x y) w) : 0 < y := h.1

/-- **The stuck run.**  At a halting ID of `B` the compile runs, off the boundary, into a stuck
configuration. -/
theorem godel_stuck_chain [Fintype ι] (hB : B.Det) (hp : PrimeData p N) {J : ℕ} (hJ : 0 < J)
    (hJp : ∀ i, ¬ p i ∣ J) {q : Q} {v : ι → ℕ} (hs : B.Stuck (q, v)) :
    ∃ d, Relation.ReflTransGen (GOff B p N) (.ent q, genc p J v) d ∧ (godel B p N).Stuck d := by
  classical
  have hX := enc_pos hp hJ v
  change ∃ d, Relation.ReflTransGen (GOff B p N) (.ent q, gc (J * ∏ k, p k ^ v k) 0) d ∧ _
  set X := J * ∏ k, p k ^ v k with hXdef
  have hg : Relation.ReflTransGen (GOff B p N) (.ent q, gc X 0) (.grd q, gc X 0) :=
    .single (goff_of (.guard q) rfl rfl (act_t0 (decide_eq_true hX)) (by simp))
  by_cases hex : ∃ ρ ∈ B, ρ.src = q
  · obtain ⟨⟨src, op, dst⟩, hρ, rfl⟩ := hex
    simp only at hg hs ⊢
    cases op with
    | nop => exact absurd ⟨_, hρ, rfl, rfl, rfl⟩ (hs (dst, v))
    | inc i =>
      exact absurd ⟨_, hρ, rfl, rfl, by simp, fun j hj => by simp [hj]⟩
        (hs (dst, Function.update v i (v i + 1)))
    | dec i =>
      by_cases hvi : 0 < v i
      · exact absurd ⟨_, hρ, rfl, rfl, hvi, by simp; omega, fun j hj => by simp [hj]⟩
          (hs (dst, Function.update v i (v i - 1)))
      have hpi := (hp.prime i).two_le
      have hle := hp.le i
      have hnd : ¬ p i ∣ X := by rw [hXdef, dvd_enc_iff hp hJp v i]; omega
      have hj1 : 1 ≤ X % p i := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      have hj2 : X % p i < p i := Nat.mod_lt _ (by omega)
      have hXe : X = p i * (X / p i) + X % p i := (Nat.div_add_mod X (p i)).symm
      have hm : MoveRule B src i dst := .inr hρ
      refine ⟨(.dv src ⟨1 + X % p i, by omega⟩, gc (X / p i) 0), ?_, ?_⟩
      · refine hg.trans (.head (goff_of (.aIn hm) rfl rfl (act_t1 rfl) (by simp)) ?_)
        have ht := g_transfer (p := p) (N := N) hm X 0 0
        simp only [Nat.zero_add] at ht
        refine ht.trans (.head (goff_of (.a₁Z hm) rfl rfl (act_t0 rfl) (by simp)) ?_)
        have hdv := g_dv hp hρ (X % p i) (X / p i) 0
        rw [← hXe, Nat.zero_add] at hdv
        refine hdv.trans (.head (goff_of (.dvIn ⟨1, by omega⟩ hρ rfl) rfl rfl
          (act_t1 (decide_eq_true (by omega))) (by simp)) ?_)
        have hc := g_dvChain hp hρ (X / p i) 0 (X % p i) 1 (by omega) le_rfl (by omega)
        simpa using hc
      · rintro d ⟨r, hr, h1, -, h3⟩
        cases hr <;> simp only [GState.dv.injEq, reduceCtorEq] at h1
        all_goals (rw [← h1.1] at h3; exact absurd (act_dec1_inv h3) (by omega))
    | test i b =>
      by_cases hb : decide (0 < v i) = b
      · exact absurd ⟨_, hρ, rfl, rfl, hb, rfl⟩ (hs (dst, v))
      have hpi := (hp.prime i).two_le
      have hle := hp.le i
      -- no rule from `src` reads the value of `v i`
      have hno : ∀ i' q'', ⟨src, .test i' (decide (0 < v i)), q''⟩ ∉ B := by
        intro i' q'' h
        obtain rfl := det_test_counter hB hρ h
        exact hs (q'', v) ⟨_, h, rfl, rfl, rfl, rfl⟩
      have hw : Relation.ReflTransGen (GOff B p N) (.ent src, gc X 0)
          (.w₁ src ⟨0, by omega⟩, gc X 0) :=
        hg.tail (goff_of (.wIn _ hρ rfl) rfl rfl (act_t1 rfl) (by simp))
      by_cases hvi : 0 < v i
      · obtain ⟨a, ha⟩ := (dvd_enc_iff hp hJp v i).2 hvi
        rw [← hXdef] at ha
        refine ⟨(.w₁ src ⟨0, by omega⟩, gc 0 a), ?_, ?_⟩
        · have h1 := g_w hp hρ 0 a 0
          rw [Nat.zero_add, Nat.zero_add, ← ha] at h1
          exact hw.trans h1
        · rintro d ⟨r, hr, h1, -, h3⟩
          cases hr <;> simp only [GState.w₁.injEq, reduceCtorEq] at h1
          · rw [← h1.1] at h3; exact absurd (act_t0_inv h3) (by simp)
          · rename_i i' _ _ j _ hj; have := (hp.prime i').two_le
            have := congrArg Fin.val h1.2; simp at this; omega
          · rename_i i' q'' j h' _
            exact hno i' q'' (by rw [h1.1]; simpa [hvi] using h')
          · rename_i j _ hj _; have := congrArg Fin.val h1.2; simp at this; omega
      · have hnd : ¬ p i ∣ X := by rw [hXdef, dvd_enc_iff hp hJp v i]; omega
        have hj1 : 1 ≤ X % p i := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
        have hj2 : X % p i < p i := Nat.mod_lt _ (by omega)
        have hXe : X = X % p i + p i * (X / p i) := (Nat.mod_add_div X (p i)).symm
        refine ⟨(.w₁ src ⟨X % p i, by omega⟩, gc 0 (X / p i)), ?_, ?_⟩
        · have h1 := g_w hp hρ (X % p i) (X / p i) 0
          rw [Nat.zero_add, ← hXe] at h1
          have h2 := g_wChain hp hρ 0 (X / p i) (X % p i) 0 (by omega) (by omega)
          simp only [Nat.zero_add] at h2
          exact hw.trans (h1.trans h2)
        · rintro d ⟨r, hr, h1, -, h3⟩
          cases hr <;> simp only [GState.w₁.injEq, reduceCtorEq] at h1
          · rw [← h1.1] at h3; exact absurd (act_t0_inv h3) (by simp)
          · rename_i i' _ _ j h' hj
            obtain rfl := det_test_counter hB hρ (h1.1 ▸ h')
            have := congrArg Fin.val h1.2; simp at this; omega
          · rename_i j _ hj; have := congrArg Fin.val h1.2; simp at this; omega
          · rename_i i' q'' j h' _ _
            exact hno i' q'' (by rw [h1.1]; simpa [hvi] using h')
  · refine ⟨_, hg, ?_⟩
    rintro d ⟨r, hr, h1, -, -⟩
    cases hr <;> simp only [GState.grd.injEq, reduceCtorEq] at h1
    · exact hex ⟨_, ‹_›, h1.symm⟩
    · rename_i hm; rcases hm with hm | hm <;> exact hex ⟨_, hm, h1.symm⟩
    · exact hex ⟨_, ‹_›, h1.symm⟩

/-- Under determinism, a run off `B` into a stuck configuration admits no macro step. -/
theorem not_macro_of_stuck {M : CM Q ι} (hM : M.Det) {B : Set Q} {c d : Cfg Q ι}
    (hcd : Relation.ReflTransGen (fun a b => M.Step a b ∧ b.1 ∉ B) c d) (hd : M.Stuck d)
    {b' : Cfg Q ι} : ¬ RcwaMachine.MacroStep B M.Step c b' := by
  rintro ⟨-, hb', x, n, hn, hx0, hxn, hstep, hoff⟩
  induction hcd using Relation.ReflTransGen.head_induction_on generalizing x n with
  | refl => exact hd _ (hx0 ▸ hstep 0 hn)
  | head hab _ ih =>
    have h1 := CM.step_functional hM (hx0 ▸ hstep 0 hn) hab.1
    by_cases hn1 : n = 1
    · subst hn1; rw [hxn] at h1; rw [h1] at hb'; exact hab.2 hb'
    · exact ih (fun i => x (i + 1)) (n - 1) (by omega) h1
        (by rw [show n - 1 + 1 = n by omega, hxn]) (fun i hi => hstep (i + 1) (by omega))
        (fun i h0 hi => hoff (i + 1) (by omega) (by omega))

/-- A halting ID of `B` gives a halting run of the compile. -/
theorem godel_halts_of_stuck [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) {J : ℕ}
    (hJ : 0 < J) (hJp : ∀ i, ¬ p i ∣ J) {q : Q} {v : ι → ℕ} (hs : B.Stuck (q, v)) :
    (godel B p N).Halts (.ent q, genc p J v) := by
  obtain ⟨d, hr, hd⟩ := godel_stuck_chain hB hp hJ hJp hs
  refine ⟨d, ?_, hd⟩
  clear hd
  induction hr with
  | refl => exact .refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih h.1

/-- **Soundness on garbage.**  Every macro step, from any configuration, starts at a guarded
boundary configuration (`x ≥ 1`, `y = 0`, an encoding with some junk) and is a step of `B`. -/
theorem godel_macro_sound [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N)
    {b b' : Cfg (GState Q N) (Fin 2)}
    (h : RcwaMachine.MacroStep (Set.range GState.ent) (godel B p N).Step b b') :
    ∃ (q q' : Q) (v v' : ι → ℕ) (J : ℕ), 0 < J ∧ (∀ i, ¬ p i ∣ J) ∧
      b = (.ent q, genc p J v) ∧ b' = (.ent q', genc p J v') ∧ B.Step (q, v) (q', v') := by
  have h₀ := h
  obtain ⟨⟨q, hq⟩, hb', x, n, hn, hx0, hxn, hstep, hoff⟩ := h
  -- the first step is the guard
  obtain ⟨r, hr, h1, h2, h3⟩ := hstep 0 hn
  rw [hx0, ← hq] at h1
  cases hr <;> simp only [GState.ent.injEq, reduceCtorEq] at h1
  subst h1
  obtain ⟨hx, hx1⟩ := h3
  rw [hx0] at hx hx1
  -- the second step is a `y = 0` test
  have hn2 : 1 < n := by
    by_contra hc
    obtain rfl : n = 1 := by omega
    obtain ⟨t, ht⟩ := hb'
    rw [← hxn, h2] at ht
    cases ht
  obtain ⟨r', hr', h1', -, h3'⟩ := hstep 1 hn2
  rw [h2] at h1'
  have hy : b.2 1 = 0 := by
    cases hr' <;> simp only [GState.grd.injEq, reduceCtorEq] at h1'
    all_goals (rw [hx1] at h3'; simpa using h3'.1)
  have hx' : 0 < b.2 0 := by simpa using hx
  obtain ⟨J, v, hJ, hJp, hxe⟩ := exists_enc hp hx'
  have hbe : b = (.ent q, genc p J v) := by
    refine Prod.ext hq.symm (funext fun j => ?_)
    fin_cases j
    · exact hxe
    · exact hy
  by_cases hst : ∃ d, B.Step (q, v) d
  · obtain ⟨⟨q', v'⟩, hst⟩ := hst
    have hm := godel_macro hB hB' hp hJ hJp hst
    rw [← hbe] at hm
    exact ⟨q, q', v, v', J, hJ, hJp, hbe, macroStep_functional (godel_det hB hB' hp) h₀ hm, hst⟩
  · obtain ⟨d, hr, hd⟩ := godel_stuck_chain hB hp hJ hJp (fun d h => hst ⟨d, h⟩)
    rw [← hbe] at hr
    exact absurd h₀ (not_macro_of_stuck (godel_det hB hB' hp) hr hd)

/-- **Lemma G.**  The compile's reverse is mortal, on all configurations, if `B`'s is. -/
theorem godel_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] (hB : B.Det) (hB' : B.Rev)
    (hp : PrimeData p N) (hmort : B.RevMortal) : (godel B p N).RevMortal := by
  refine revMortal_of_macro (godel_lapsMixed hB hB' hp) ?_
  rintro ⟨b, hb⟩
  choose q q' v v' J hJ hJp h1 h2 hst using fun n => godel_macro_sound hB hB' hp (hb n)
  have key : ∀ n, q n = q' (n + 1) ∧ v n = v' (n + 1) := by
    intro n
    have e := (h1 n).symm.trans (h2 (n + 1))
    simp only [Prod.mk.injEq, GState.ent.injEq] at e
    exact ⟨e.1, (genc_inj hp (hJ n) (hJ (n + 1)) (hJp n) (hJp (n + 1)) e.2).2⟩
  refine hmort ⟨fun n => (q n, v n), fun n => ?_⟩
  have := hst (n + 1)
  rw [← (key n).1, ← (key n).2] at this
  exact this

/-- The compile halts from an encoding (junk `1`) iff `B` halts. -/
theorem godel_halts_iff [Fintype ι] (hB : B.Det) (hB' : B.Rev) (hp : PrimeData p N) (q : Q)
    (v : ι → ℕ) :
    (godel B p N).Halts (.ent q, genc p 1 v) ↔ B.Halts (q, v) := by
  have hJp : ∀ i, ¬ p i ∣ 1 := fun i h => (hp.prime i).one_lt.ne' (Nat.dvd_one.1 h)
  refine CM.halts_iff_of_sim (godel_det hB hB' hp)
    (fun c c' => c' = (.ent c.1, genc p 1 c.2)) ?_ ?_ rfl
  · rintro ⟨q, v⟩ ⟨q', v'⟩ c' hst rfl
    exact ⟨_, macroStep_transGen (godel_macro hB hB' hp one_pos hJp hst), rfl⟩
  · rintro ⟨q, v⟩ c' hs rfl
    exact godel_halts_of_stuck hB hB' hp one_pos hJp hs

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
  have : ∏ c, p c ^ hcfg (Pi.single i₀ n) 0 c = p (.val i₀) ^ n := by
    rw [Fintype.prod_eq_single (HCtr.val i₀) fun c hc => ?_]
    · simp [hcfg]
    · cases c with
      | val i =>
        have : i ≠ i₀ := fun h => hc (by rw [h])
        simp [hcfg, this]
      | hist => simp [hcfg]
      | work => simp [hcfg]
  simp only [genc, one_mul, this]

/-- **The compiled machine.**  A deterministic `U` in normal form at `q₀` gives a valid machine
with a source state `s₀ < K` and a prime `P` such that halting from `(s₀, P ^ n, 0)` is halting
of `U` from `q₀` with `n` in counter `i₀`. -/
theorem exists_valid_machine {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι] {U : CM Q ι}
    {q₀ : Q} (hU : U.Det) (hq₀ : U.NormalAt q₀) (i₀ : ι) :
    ∃ (M : Machine) (s₀ P : ℕ), M.Valid ∧ s₀ < M.K ∧ ∀ n : ℕ,
      IsSource M.rules (s₀, P ^ n, 0) ∧
        (Halts M.rules (s₀, P ^ n, 0) ↔ U.Halts (q₀, Pi.single i₀ n)) := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite ι
  -- labels `1, …, card` of the rules
  let L := Fintype.card (Quad Q ι) + 1
  let lab : Quad Q ι → Fin L := fun ρ => ⟨Fintype.equivFin (Quad Q ι) ρ + 1, by
    have := (Fintype.equivFin (Quad Q ι) ρ).isLt; omega⟩
  have hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val := fun ρ _ => by simp [lab]
  have hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ' := fun ρ _ ρ' _ h => by
    simp only [lab, Fin.mk.injEq, Nat.add_right_cancel_iff] at h
    exact (Fintype.equivFin _).injective (Fin.ext h)
  -- distinct primes for the wrapper's counters
  let p : HCtr ι → ℕ := fun c => Nat.nth Nat.Prime (Fintype.equivFin (HCtr ι) c)
  let N := ∑ c, p c
  have hp : PrimeData p N :=
    ⟨fun c => Nat.prime_nth_prime _,
      fun c c' h => (Fintype.equivFin _).injective
        (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h)),
      fun c => Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)⟩
  let B := histWrap U lab
  have hBd : B.Det := histWrap_det hU
  have hBr : B.Rev := histWrap_rev hU hlab hinj
  have hBm : B.RevMortal := histWrap_revMortal hU hlab
  let R := godel B p N
  have hRd : R.Det := godel_det hBd hBr hp
  have hRr : R.Rev := godel_rev hBd hBr hp
  have hRm : R.RevMortal := godel_revMortal hBd hBr hp hBm
  let rs := (Finset.univ.filter (· ∈ R)).toList
  have hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R := fun ρ => by simp [rs]
  let e := Fintype.equivFin (GState (HState Q ι L) N × Bool)
  refine ⟨double rs e, (e (.ent (.bnd q₀), true)).val, p (.val i₀), double_valid e hrs hRd hRr hRm,
    (e _).isLt, fun n => ?_⟩
  have hc : ((e (.ent (.bnd q₀), true)).val, p (.val i₀) ^ n, 0) =
      dcfg e true (.ent (.bnd q₀), genc p 1 (hcfg (Pi.single i₀ n) 0)) := by
    simp only [dcfg, genc_hcfg_single]; rfl
  have hsrc : R.IsSource (.ent (.bnd q₀), genc p 1 (hcfg (Pi.single i₀ n) 0)) :=
    CM.isSource_of_normalAt (godel_normalAt (histWrap_normalAt hq₀)) _
  rw [hc]
  exact ⟨double_isSource e hrs hRd hRr hsrc, (double_halts_iff e hrs hRd hRr hsrc).trans
    ((godel_halts_iff hBd hBr hp _ _).trans (histWrap_halts_iff hU _ _))⟩

/-- **The upper half.**  `UndecidableCM` gives `HaltingUndecidable`. -/
theorem haltingUndecidable_of_undecidableCM (h : UndecidableCM) : HaltingUndecidable := by
  obtain ⟨Q, ι, _, _, U, q₀, i₀, enc, hU, hq₀, henc, hnot⟩ := h
  classical
  obtain ⟨M, s₀, P, hM, hK, hn⟩ := exists_valid_machine hU hq₀ i₀
  rintro ⟨g, hg, hspec⟩
  apply hnot
  have hg' : Computable fun n => g (M, (s₀, P ^ enc n, 0)) :=
    hg.comp (Computable.pair (Computable.const M) (Computable.pair (Computable.const s₀)
      (Computable.pair ((RcwaSameOrbit.PrimInt.nat_pow.to_comp).comp (Computable.const P) henc)
        (Computable.const 0))))
  refine ⟨Classical.decPred _, hg'.of_eq fun n => ?_⟩
  rw [Bool.eq_iff_iff, hspec M _ hM hK (hn (enc n)).1, (hn (enc n)).2, decide_eq_true_iff]

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
