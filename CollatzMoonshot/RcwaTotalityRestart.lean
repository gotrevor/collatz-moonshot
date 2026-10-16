/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaTotalityGlue

/-!
# Totality family, layer 3: Lemma A, a restart machine mortal iff `φ_e` is total

Research note `undec-lemma` §7 (Lemma A, after Kari–Ollinger's appendix), built on the fixed
universal counter machine of `CounterMachineUniversal`.

1. **A universal code for "halts on `0, …, a`".**  `exists_universal₂`: a `ToPartrec.Code` `u`
   that halts on `[a, e]` iff `φ_e` halts on every `y ≤ a`.  Then `U₂ u`, the counter machine
   `lcm (trNormal u halt)` restricted to its finite reachable set, halts from `start` with the
   main stack holding `trList [2^x − 1, e]` iff `φ_e` halts on `0, …, 2^x − 1`
   (`halts_u₂_iff`).  That stack is `x` pushes of `bit1` onto `cons :: trList [e]`, i.e. the
   numeral `gIter x (2 + 5 · inputNum e)` with `gIter x = (5 · + 4)^[x]`.
2. **The restart machine `restart u`** (counters `sim c` for the five counters of `U₂`, the input
   `x`, scratch `w`, budget `p`, spent `t`).  Each step of `U₂` is *gated*: `gate s` restarts when
   `p = 0`, else moves one token from `p` to `t` and runs `s`'s rule.  The restart `clr 0 →⋯→`
   clears the five `sim` counters and stops at `hole`, which no rule leaves.  From `back` (which
   no rule enters) it builds the input numeral from `x` (`main ↦ 5 · main + 4` per unit of `x`,
   moving `x` to `w`), moves `w` back to `x`, moves `t` into `p`, adds `1`, and enters
   `gate start`.  `glue (restart u) hole back (sim main) L` (`Asharp u L`) puts the chain
   `main += L + 1` between `hole` and `back`.
3. **Lemma A** (`mortal_asharp_iff`): `Asharp u L` halts from every configuration iff `U₂ u`
   halts on every honest input `gIter x (L + 1)`.  Garbage is flushed in two rounds: every
   configuration halts or reaches `clr 0` (`halts_or_reaches_restart`); one round from `clr 0`
   with any counters lands at `gate start` with honest counters and budget `p + t + 1`
   (`reaches_round`); from then on the rounds rerun the same input with budgets growing by one
   (`halts_of_steady`), and an input on which `U₂` runs forever gives an immortal configuration
   (`not_halts_of_not_halts`).
4. **Totality** (`mortal_iff_total`): with `L = 1 + 5 · inputNum e`, mortality is `Total e`.
-/

namespace CollatzMoonshot.RcwaTotality

open Turing Turing.PartrecToTM2 CollatzMoonshot.CounterMachine
open CollatzMoonshot.CounterMachineUniversal
open CollatzMoonshot.RcwaOrbitCount (Mortal Total)

/-! ## 1. A universal code and the universal counter machine -/

theorem foldr_and_iff {β : Type*} (f : β → Bool) (l : List β) :
    l.foldr (fun y s => f y && s) true = true ↔ ∀ y ∈ l, f y = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **A universal code for initial segments.**  `u` halts on `[a, e]` iff `φ_e` halts on every
`y ≤ a`. -/
theorem exists_universal₂ : ∃ u : ToPartrec.Code, ∀ a e : ℕ,
    (u.eval [a, e]).Dom ↔
      ∀ y ≤ a, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) y).Dom := by
  let p : ℕ × ℕ → ℕ → Bool := fun ae k => (List.range (ae.1 + 1)).foldr
    (fun y s => (Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code ae.2) y).isSome
      && s) true
  have hp : Primrec₂ p := by
    show Primrec fun x : (ℕ × ℕ) × ℕ => p x.1 x.2
    refine Primrec.list_foldr (α := (ℕ × ℕ) × ℕ) (σ := Bool) (β := ℕ)
      (h := fun x bs => (Nat.Partrec.Code.evaln x.2 (Denumerable.ofNat Nat.Partrec.Code x.1.2)
        bs.1).isSome && bs.2) (Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.fst.comp Primrec.fst))) (Primrec.const true) ?_
    refine Primrec.and.comp (Primrec.option_isSome.comp ?_) (Primrec.snd.comp Primrec.snd)
    exact Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair
      (Primrec.snd.comp Primrec.fst) ((Primrec.ofNat _).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) (Primrec.fst.comp Primrec.snd))
  let g : ℕ → ℕ →. ℕ := fun a e => Nat.rfind fun k => Part.some (p (a, e) k)
  have hg : Partrec₂ g := by
    have := Partrec.rfind (hp.to_comp.partrec₂)
    exact this.comp (Computable.pair Computable.fst Computable.snd)
  obtain ⟨u, hu⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₂.2 hg)
  refine ⟨u, fun a e => ?_⟩
  have := hu ⟨[a, e], rfl⟩
  simp only at this
  rw [this]
  simp only [Part.map_eq_map, Part.map_Dom, g, List.Vector.head, List.Vector.tail]
  refine (Nat.rfind_dom (p := fun k => Part.some (p (a, e) k))).trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨k, hk⟩ y hy
    have := (foldr_and_iff _ _).1 hk.symm y (List.mem_range.2 (by omega))
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 this
    exact Part.dom_iff_mem.2 ⟨x, Nat.Partrec.Code.evaln_sound hx⟩
  · intro h
    have hk : ∀ y, ∃ k, y ≤ a → (Nat.Partrec.Code.evaln k
        (Denumerable.ofNat Nat.Partrec.Code e) y).isSome := by
      intro y
      by_cases hy : y ≤ a
      · obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 (h y hy)
        obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hx
        exact ⟨k, fun _ => Option.isSome_iff_exists.2 ⟨x, hk⟩⟩
      · exact ⟨0, fun h => absurd h hy⟩
    choose kf hkf using hk
    refine ⟨(Finset.range (a + 1)).sup kf, ((foldr_and_iff _ _).2 fun y hy => ?_).symm⟩
    have hy' : y ≤ a := by have := List.mem_range.1 hy; omega
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hkf y hy')
    exact Option.isSome_iff_exists.2 ⟨x, Nat.Partrec.Code.evaln_mono
      (Finset.le_sup (Finset.mem_range.2 (by omega))) hx⟩

/-- The reachable states of the compiled code `u`. -/
abbrev S₂ (u : ToPartrec.Code) : Type :=
  ↥(reachSet (codeSupp u Cont'.halt))

/-- The universal counter machine of the code `u`, on its finite reachable set. -/
def U₂ (u : ToPartrec.Code) : CM (S₂ u) LCtr :=
  (lcm (trNormal u Cont'.halt)).restrict (reachSet (codeSupp u Cont'.halt))

/-- The start state. -/
def start₂ (u : ToPartrec.Code) : S₂ u :=
  ⟨.start, Or.inl rfl⟩

/-- The input step `main ↦ 5 · main + 4` (push `bit1`), iterated `x` times. -/
def gIter (x n : ℕ) : ℕ :=
  (fun m => 5 * m + 4)^[x] n

/-- The counters of `U₂` holding `n` in `main`, everything else `0`. -/
def honest (n : ℕ) : LCtr → ℕ :=
  Pi.single (some K'.main) n

theorem trNat_bit1 (m : ℕ) : trNat (2 * m + 1) = Γ'.bit1 :: trNat m := by
  have h : ((2 * m + 1 : ℕ) : Num) = Num.bit1 (m : Num) := by
    rw [← Num.to_nat_inj, Num.to_of_nat]
    have hm := Num.to_of_nat m
    generalize (m : Num) = k at hm ⊢
    subst hm
    rcases k with _ | p
    · rfl
    · show _ = ((PosNum.bit1 p : PosNum) : ℕ)
      rw [PosNum.cast_bit1]; simp; ring
  rw [trNat, h, trNat]
  rcases (m : Num) with _ | p <;> rfl

/-- `trNat (2 ^ x - 1)` is `x` copies of `bit1`. -/
theorem trNat_two_pow_sub_one (x : ℕ) : trNat (2 ^ x - 1) = List.replicate x Γ'.bit1 := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [show 2 ^ (x + 1) - 1 = 2 * (2 ^ x - 1) + 1 by
      have := Nat.one_le_two_pow (n := x); rw [pow_succ]; omega, trNat_bit1, ih,
      List.replicate_succ]

/-- The main-stack numeral of `[2 ^ x - 1, e]`. -/
theorem num_trList_pair (x e : ℕ) :
    num (trList [2 ^ x - 1, e]) = gIter x (2 + 5 * inputNum e) := by
  simp only [trList, trNat_two_pow_sub_one]
  induction x with
  | zero => simp [gIter, num, inputNum, digit, digitF, trList]
  | succ x ih =>
    rw [List.replicate_succ, List.cons_append, num, ih, gIter, gIter,
      Function.iterate_succ_apply']
    simp [digit, digitF]; ring

/-- **The universal machine on honest inputs.** -/
theorem halts_u₂_iff (u : ToPartrec.Code) (x e : ℕ) :
    (U₂ u).Halts (start₂ u, honest (gIter x (2 + 5 * inputNum e))) ↔
      (u.eval [2 ^ x - 1, e]).Dom := by
  refine (CM.halts_restrict (reachSet_closed (tr_supports u Cont'.halt))
    (q := LState.start) (Or.inl rfl) _).trans ?_
  have hS : stackVec (K'.elim (trList [2 ^ x - 1, e]) [] [] []) =
      honest (gIter x (2 + 5 * inputNum e)) := by
    funext c
    rcases c with _ | k
    · rfl
    · cases k
      · simpa [stackVec, honest, K'.elim] using num_trList_pair x e
      all_goals simp [stackVec, honest, Pi.single, Function.update, K'.elim, num]
  rw [← hS, halts_iff_eval]
  have := tr_eval u [2 ^ x - 1, e]
  simp only [init] at this
  rw [this]
  simp

/-- The universal machine is deterministic. -/
theorem u₂_det (u : ToPartrec.Code) : (U₂ u).Det :=
  CM.restrict_det (det_lcm _) _

/-! ## 2. The restart machine -/

/-- The counters: the five counters of `U₂`, the input `x`, scratch `w`, budget `p`, spent
`t`. -/
inductive ACtr
  | sim (c : LCtr)
  | x
  | w
  | p
  | t
  deriving DecidableEq, Fintype

/-- The order in which the restart clears the counters of `U₂`. -/
def clrCtr : Fin 5 → LCtr :=
  ![none, some K'.main, some K'.rev, some K'.aux, some K'.stack]

/-- The states of the restart machine.  `run s`, `gate s`, `sp₁ s`, `sp₂ s` simulate `U₂`;
`clr j`, `clr' j` clear counter `clrCtr j`; `hole`, `back` are the chain's ends; `cx …` builds
the input numeral (`mv` moves `main` into `tmp`, `ml` moves it back five-fold, `ad` adds `4`);
`cw …` moves `w` back to `x`; `bt …` moves `t` into `p` and adds `1`. -/
inductive AState (u : ToPartrec.Code)
  | run (s : S₂ u)
  | gate (s : S₂ u)
  | sp₁ (s : S₂ u)
  | sp₂ (s : S₂ u)
  | clr (j : Fin 5)
  | clr' (j : Fin 5)
  | hole
  | back
  | cx
  | cx₁
  | cx₂
  | mv
  | mv₁
  | mv₂
  | ml
  | ml₁ (j : Fin 6)
  | ad (j : Fin 4)
  | cw
  | cw₁
  | cw₂
  | bt
  | bt₁
  | bt₂
  | bt₃

/-- The rules of the restart machine. -/
inductive ARule (u : ToPartrec.Code) : Quad (AState u) ACtr → Prop
  | sim {s s' : S₂ u} {o : Op LCtr} :
      (⟨s, o, s'⟩ : Quad (S₂ u) LCtr) ∈ U₂ u → ARule u ⟨.run s, o.map .sim, .gate s'⟩
  | gateZ (s : S₂ u) : ARule u ⟨.gate s, .test .p false, .clr 0⟩
  | gateP (s : S₂ u) : ARule u ⟨.gate s, .test .p true, .sp₁ s⟩
  | sp₁ (s : S₂ u) : ARule u ⟨.sp₁ s, .dec .p, .sp₂ s⟩
  | sp₂ (s : S₂ u) : ARule u ⟨.sp₂ s, .inc .t, .run s⟩
  | clrP (j : Fin 5) : ARule u ⟨.clr j, .test (.sim (clrCtr j)) true, .clr' j⟩
  | clrD (j : Fin 5) : ARule u ⟨.clr' j, .dec (.sim (clrCtr j)), .clr j⟩
  | clrZ (j j' : Fin 5) : j'.val = j.val + 1 →
      ARule u ⟨.clr j, .test (.sim (clrCtr j)) false, .clr j'⟩
  | clrH : ARule u ⟨.clr 4, .test (.sim (clrCtr 4)) false, .hole⟩
  | back : ARule u ⟨.back, .nop, .cx⟩
  | cxZ : ARule u ⟨.cx, .test .x false, .cw⟩
  | cxP : ARule u ⟨.cx, .test .x true, .cx₁⟩
  | cx₁ : ARule u ⟨.cx₁, .dec .x, .cx₂⟩
  | cx₂ : ARule u ⟨.cx₂, .inc .w, .mv⟩
  | mvZ : ARule u ⟨.mv, .test (.sim (some K'.main)) false, .ml⟩
  | mvP : ARule u ⟨.mv, .test (.sim (some K'.main)) true, .mv₁⟩
  | mv₁ : ARule u ⟨.mv₁, .dec (.sim (some K'.main)), .mv₂⟩
  | mv₂ : ARule u ⟨.mv₂, .inc (.sim none), .mv⟩
  | mlZ : ARule u ⟨.ml, .test (.sim none) false, .ad 0⟩
  | mlP : ARule u ⟨.ml, .test (.sim none) true, .ml₁ 0⟩
  | ml₀ : ARule u ⟨.ml₁ 0, .dec (.sim none), .ml₁ 1⟩
  | mlI (j j' : Fin 6) : 1 ≤ j.val → j'.val = j.val + 1 →
      ARule u ⟨.ml₁ j, .inc (.sim (some K'.main)), .ml₁ j'⟩
  | mlL : ARule u ⟨.ml₁ 5, .inc (.sim (some K'.main)), .ml⟩
  | adI (j j' : Fin 4) : j'.val = j.val + 1 → ARule u ⟨.ad j, .inc (.sim (some K'.main)), .ad j'⟩
  | adL : ARule u ⟨.ad 3, .inc (.sim (some K'.main)), .cx⟩
  | cwZ : ARule u ⟨.cw, .test .w false, .bt⟩
  | cwP : ARule u ⟨.cw, .test .w true, .cw₁⟩
  | cw₁ : ARule u ⟨.cw₁, .dec .w, .cw₂⟩
  | cw₂ : ARule u ⟨.cw₂, .inc .x, .cw⟩
  | btZ : ARule u ⟨.bt, .test .t false, .bt₃⟩
  | btP : ARule u ⟨.bt, .test .t true, .bt₁⟩
  | bt₁ : ARule u ⟨.bt₁, .dec .t, .bt₂⟩
  | bt₂ : ARule u ⟨.bt₂, .inc .p, .bt⟩
  | bt₃ : ARule u ⟨.bt₃, .inc .p, .gate (start₂ u)⟩

/-- The restart machine around `U₂ u`. -/
def restart (u : ToPartrec.Code) : CM (AState u) ACtr :=
  {ρ | ARule u ρ}

/-- The restart machine with the chain `main += L + 1` glued from `hole` to `back`. -/
abbrev Asharp (u : ToPartrec.Code) (L : ℕ) : CM (AState u ⊕ Fin L) ACtr :=
  glue (restart u) .hole .back (.sim (some K'.main)) L

/-- The restart machine's counters: `v` on `U₂`'s counters, then `x`, `w`, `p`, `t`. -/
def acfg (v : LCtr → ℕ) (x w p t : ℕ) : ACtr → ℕ
  | .sim c => v c
  | .x => x
  | .w => w
  | .p => p
  | .t => t

/-- A coding of the states into a finite type. -/
def aCode {u : ToPartrec.Code} : AState u → (Fin 4 × S₂ u) ⊕ (Fin 3 × Fin 6) ⊕ Fin 20
  | .run s => .inl (0, s)
  | .gate s => .inl (1, s)
  | .sp₁ s => .inl (2, s)
  | .sp₂ s => .inl (3, s)
  | .clr j => .inr (.inl (0, j.castLE (by omega)))
  | .clr' j => .inr (.inl (1, j.castLE (by omega)))
  | .ml₁ j => .inr (.inl (2, j))
  | .ad j => .inr (.inr (j.castLE (by omega)))
  | .hole => .inr (.inr 4)
  | .back => .inr (.inr 5)
  | .cx => .inr (.inr 6)
  | .cx₁ => .inr (.inr 7)
  | .cx₂ => .inr (.inr 8)
  | .mv => .inr (.inr 9)
  | .mv₁ => .inr (.inr 10)
  | .mv₂ => .inr (.inr 11)
  | .ml => .inr (.inr 12)
  | .cw => .inr (.inr 13)
  | .cw₁ => .inr (.inr 14)
  | .cw₂ => .inr (.inr 15)
  | .bt => .inr (.inr 16)
  | .bt₁ => .inr (.inr 17)
  | .bt₂ => .inr (.inr 18)
  | .bt₃ => .inr (.inr 19)

/-- Finitely many states. -/
theorem finite_aState (u : ToPartrec.Code) : Finite (AState u) := by
  have : Finite (S₂ u) := (reachSet_finite _).to_subtype
  refine Finite.of_injective (aCode (u := u)) ?_
  intro a b h
  cases a <;> cases b <;> simp [aCode, Fin.ext_iff] at h <;>
    first
    | rfl
    | (subst h; rfl)
    | (congr 1; exact Fin.ext h)
    | (exfalso; omega)

/-- The restart machine is deterministic. -/
theorem restart_det (u : ToPartrec.Code) : (restart u).Det := by
  intro ρ hρ ρ' hρ' hne hsrc
  cases hρ <;> cases hρ' <;> (try cases hsrc) <;>
    first
    | exact absurd rfl hne
    | exact ⟨_, _, _, rfl, rfl, by decide⟩
    | (exfalso; apply hne; congr 2; exact Fin.ext (by omega))
    | (exfalso; simp_all; omega)
    | (exfalso; rename_i h _; exact absurd h (by decide))
    | skip
  rename_i s₁ o₁ h₁ s₂ o₂ h₂
  obtain ⟨i, b, b', hb, hb', hbb⟩ := u₂_det u _ h₁ _ h₂ (fun h => hne (by cases h; rfl)) rfl
  simp only at hb hb'
  subst hb hb'
  exact ⟨.sim i, b, b', rfl, rfl, hbb⟩

/-- No rule leaves `hole`. -/
theorem restart_src_ne_hole (u : ToPartrec.Code) : ∀ ρ ∈ restart u, ρ.src ≠ .hole := by
  intro ρ hρ h
  cases hρ <;> cases h

/-- No rule enters `back`. -/
theorem restart_normalAt_back (u : ToPartrec.Code) : (restart u).NormalAt .back := by
  intro ρ hρ h
  cases hρ <;> cases h

/-- The glued restart machine is deterministic. -/
theorem asharp_det (u : ToPartrec.Code) (L : ℕ) : (Asharp u L).Det :=
  glue_det (restart_det u) (restart_src_ne_hole u)

/-! ## 3. Runs of the glued restart machine -/

section Runs

variable {u : ToPartrec.Code} {L : ℕ}

/-- The main counter of `U₂`, inside the restart machine. -/
abbrev cM : ACtr := .sim (some K'.main)
/-- The scratch counter `tmp` of `U₂`, inside the restart machine. -/
abbrev cT : ACtr := .sim none

theorem rstep {a b : AState u} {o : Op ACtr} (h : ARule u ⟨a, o, b⟩) {f g : ACtr → ℕ}
    (ha : o.Act f g) : (Asharp u L).Step (.inl a, f) (.inl b, g) :=
  glue_step_inl ⟨_, h, rfl, rfl, ha⟩

theorem act_test' {i : ACtr} {b : Bool} {f : ACtr → ℕ} (h : decide (0 < f i) = b) :
    (Op.test i b).Act f f := ⟨h, rfl⟩

theorem act_dec' {i : ACtr} {f : ACtr → ℕ} {n : ℕ} (h : f i = n + 1) :
    (Op.dec i).Act f (Function.update f i n) :=
  ⟨by omega, by simp [h], fun j hj => by simp [hj]⟩

theorem act_nop' (f : ACtr → ℕ) : (Op.nop : Op ACtr).Act f f := rfl

macro "upd" : tactic =>
  `(tactic| (funext j; simp only [Function.update_apply]; split_ifs <;>
    first | rfl | omega | (simp_all <;> omega) | simp_all))

theorem reaches_upd {c : Cfg (AState u ⊕ Fin L) ACtr} {q : AState u ⊕ Fin L}
    {g g' : ACtr → ℕ} (h : (Asharp u L).Reaches c (q, g)) (he : g = g') :
    (Asharp u L).Reaches c (q, g') := he ▸ h

theorem mv_loop : ∀ n (f : ACtr → ℕ), f cM = n →
    (Asharp u L).Reaches (.inl .mv, f)
      (.inl .mv, Function.update (Function.update f cM 0) cT (f cT + n)) := by
  intro n
  induction n with
  | zero => intro f hf; refine reaches_upd .refl ?_; upd
  | succ n ih =>
    intro f hf
    have h1 := rstep (u := u) (L := L) .mvP (act_test' (f := f) (by simp [hf]))
    have h2 := rstep (u := u) (L := L) .mv₁ (act_dec' hf)
    have h3 := rstep (u := u) (L := L) .mv₂ (act_inc_update (Function.update f cM n) cT)
    have h4 := ih (Function.update (Function.update f cM n) cT
      (Function.update f cM n cT + 1)) (by simp)
    refine .head h1 (.head h2 (.head h3 ?_))
    exact reaches_upd h4 (by upd)
theorem act_inc_eq {i : ACtr} {f g : ACtr → ℕ} (h : g = Function.update f i (f i + 1)) :
    (Op.inc i).Act f g := h ▸ act_inc_update f i

theorem ml_loop : ∀ n (f : ACtr → ℕ), f cT = n →
    (Asharp u L).Reaches (.inl .ml, f)
      (.inl .ml, Function.update (Function.update f cT 0) cM (f cM + 5 * n)) := by
  intro n
  induction n with
  | zero => intro f hf; refine reaches_upd .refl ?_; upd
  | succ n ih =>
    intro f hf
    let g : ℕ → ACtr → ℕ := fun k => Function.update (Function.update f cT n) cM (f cM + k)
    have h4 := ih (g 5) (by simp [g])
    refine .head (rstep .mlP (act_test' (f := f) (by simp [hf]))) ?_
    refine .head (rstep .ml₀ (act_dec' hf)) ?_
    refine .head (rstep (.mlI 1 2 (by decide) (by decide))
      (act_inc_eq (g := g 1) (by simp only [g]; upd))) ?_
    refine .head (rstep (.mlI 2 3 (by decide) (by decide))
      (act_inc_eq (g := g 2) (by simp only [g]; upd))) ?_
    refine .head (rstep (.mlI 3 4 (by decide) (by decide))
      (act_inc_eq (g := g 3) (by simp only [g]; upd))) ?_
    refine .head (rstep (.mlI 4 5 (by decide) (by decide))
      (act_inc_eq (g := g 4) (by simp only [g]; upd))) ?_
    refine .head (rstep .mlL (act_inc_eq (g := g 5) (by simp only [g]; upd))) ?_
    exact reaches_upd h4 (by simp only [g]; upd)

theorem cw_loop : ∀ n (f : ACtr → ℕ), f .w = n →
    (Asharp u L).Reaches (.inl .cw, f)
      (.inl .cw, Function.update (Function.update f .w 0) .x (f .x + n)) := by
  intro n
  induction n with
  | zero => intro f hf; refine reaches_upd .refl ?_; upd
  | succ n ih =>
    intro f hf
    have h4 := ih (Function.update (Function.update f .w n) .x
      (Function.update f .w n .x + 1)) (by simp)
    refine .head (rstep .cwP (act_test' (f := f) (by simp [hf])))
      (.head (rstep .cw₁ (act_dec' hf)) (.head (rstep .cw₂ (act_inc_update _ _)) ?_))
    exact reaches_upd h4 (by upd)

theorem bt_loop : ∀ n (f : ACtr → ℕ), f .t = n →
    (Asharp u L).Reaches (.inl .bt, f)
      (.inl .bt, Function.update (Function.update f .t 0) .p (f .p + n)) := by
  intro n
  induction n with
  | zero => intro f hf; refine reaches_upd .refl ?_; upd
  | succ n ih =>
    intro f hf
    have h4 := ih (Function.update (Function.update f .t n) .p
      (Function.update f .t n .p + 1)) (by simp)
    refine .head (rstep .btP (act_test' (f := f) (by simp [hf])))
      (.head (rstep .bt₁ (act_dec' hf)) (.head (rstep .bt₂ (act_inc_update _ _)) ?_))
    exact reaches_upd h4 (by upd)

theorem clr_loop (j : Fin 5) : ∀ n (f : ACtr → ℕ), f (.sim (clrCtr j)) = n →
    (Asharp u L).Reaches (.inl (.clr j), f)
      (.inl (.clr j), Function.update f (.sim (clrCtr j)) 0) := by
  intro n
  induction n with
  | zero => intro f hf; refine reaches_upd .refl ?_; upd
  | succ n ih =>
    intro f hf
    have h4 := ih (Function.update f (.sim (clrCtr j)) n) (by simp)
    refine .head (rstep (.clrP j) (act_test' (f := f) (by simp [hf])))
      (.head (rstep (.clrD j) (act_dec' hf)) ?_)
    exact reaches_upd h4 (by upd)

theorem cx_loop : ∀ n (f : ACtr → ℕ), f .x = n → f cT = 0 →
    (Asharp u L).Reaches (.inl .cx, f)
      (.inl .cx, Function.update (Function.update (Function.update f .x 0) .w (f .w + n)) cM
        (gIter n (f cM))) := by
  intro n
  induction n with
  | zero => intro f hf _; refine reaches_upd .refl ?_; simp only [gIter]; upd
  | succ n ih =>
    intro f hf hT
    -- `x − 1`, `w + 1`
    let f₂ := Function.update (Function.update f .x n) .w (f .w + 1)
    have h1 : (Asharp u L).Reaches (.inl .cx, f) (.inl .mv, f₂) :=
      .head (rstep .cxP (act_test' (f := f) (by simp [hf])))
        (.head (rstep .cx₁ (act_dec' hf))
          (.single (rstep .cx₂ (act_inc_eq (by simp only [f₂]; upd)))))
    -- `main` into `tmp`
    let f₃ := Function.update (Function.update f₂ cM 0) cT (f cM)
    have h2 : (Asharp u L).Reaches (.inl .mv, f₂) (.inl .ml, f₃) :=
      (reaches_upd (mv_loop _ f₂ rfl) (by simp only [f₂, f₃]; upd)).tail
        (rstep .mvZ (act_test' (by simp [f₃])))
    -- `tmp` back five-fold
    let f₄ := Function.update f₂ cM (5 * f cM)
    have h3 : (Asharp u L).Reaches (.inl .ml, f₃) (.inl (.ad 0), f₄) :=
      (reaches_upd (ml_loop _ f₃ rfl) (by simp only [f₃, f₄, f₂]; upd)).tail
        (rstep .mlZ (act_test' (by simp [f₄, f₂, hT])))
    -- `+ 4`
    let g : ℕ → ACtr → ℕ := fun k => Function.update f₂ cM (5 * f cM + k)
    have h4 : (Asharp u L).Reaches (.inl (.ad 0), f₄) (.inl .cx, g 4) := by
      refine .head (rstep (.adI 0 1 rfl) (act_inc_eq (g := g 1) (by simp only [g, f₄]; upd))) ?_
      refine .head (rstep (.adI 1 2 rfl) (act_inc_eq (g := g 2) (by simp only [g]; upd))) ?_
      refine .head (rstep (.adI 2 3 rfl) (act_inc_eq (g := g 3) (by simp only [g]; upd))) ?_
      exact .single (rstep .adL (act_inc_eq (by simp only [g]; upd)))
    have h5 := ih (g 4) (by simp [g, f₂]) (by simp [g, f₂, hT])
    refine h1.trans (h2.trans (h3.trans (h4.trans (reaches_upd h5 ?_))))
    rw [show gIter (n + 1) (f cM) = gIter n (5 * f cM + 4) from
      Function.iterate_succ_apply _ _ _]
    simp only [g, f₂]; upd

/-- The clearing phase: from `clr 0` to `hole` with the five counters of `U₂` cleared. -/
theorem clr_all (v : LCtr → ℕ) (x w p t : ℕ) :
    (Asharp u L).Reaches (.inl (.clr 0), acfg v x w p t) (.inl .hole, acfg 0 x w p t) := by
  have step : ∀ (j j' : Fin 5), j'.val = j.val + 1 → ∀ f : ACtr → ℕ,
      (Asharp u L).Reaches (.inl (.clr j), f)
        (.inl (.clr j'), Function.update f (.sim (clrCtr j)) 0) := fun j j' hj f =>
    (clr_loop j _ f rfl).tail (rstep (.clrZ j j' hj) (act_test' (by simp)))
  refine ((step 0 1 rfl _).trans ((step 1 2 rfl _).trans ((step 2 3 rfl _).trans
    ((step 3 4 rfl _).trans ((clr_loop 4 _ _ rfl).tail
      (rstep .clrH (act_test' (by simp)))))))).trans (reaches_upd .refl ?_)
  funext j
  rcases j with (_ | (_ | _ | _ | _)) | _ | _ | _ | _ <;>
    simp [acfg, clrCtr]

macro "acf" : tactic =>
  `(tactic| (funext j; rcases j with (_ | (_ | _ | _ | _)) | _ | _ | _ | _ <;>
    simp [acfg, honest, Function.update_apply, Pi.single_apply] <;> omega))

theorem act_map_sim {o : Op LCtr} {v v' : LCtr → ℕ} (h : o.Act v v') (x w p t : ℕ) :
    (o.map ACtr.sim).Act (acfg v x w p t) (acfg v' x w p t) := by
  cases o with
  | test i b => obtain ⟨h1, rfl⟩ := h; exact ⟨h1, rfl⟩
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, fun j hj => ?_⟩
    rcases j with c | _ | _ | _ | _ <;> try rfl
    exact h3 c fun hc => hj (hc ▸ rfl)
  | inc i =>
    obtain ⟨h2, h3⟩ := h
    refine ⟨h2, fun j hj => ?_⟩
    rcases j with c | _ | _ | _ | _ <;> try rfl
    exact h3 c fun hc => hj (hc ▸ rfl)
  | nop => cases h; rfl

theorem act_map_sim_inv {o : Op LCtr} {f g : ACtr → ℕ} (h : (o.map ACtr.sim).Act f g) :
    o.Act (fun c => f (.sim c)) (fun c => g (.sim c)) := by
  cases o with
  | test i b => obtain ⟨h1, rfl⟩ := h; exact ⟨h1, rfl⟩
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, h2, fun j hj => h3 _ fun hc => hj (ACtr.sim.inj hc)⟩
  | inc i =>
    obtain ⟨h2, h3⟩ := h
    exact ⟨h2, fun j hj => h3 _ fun hc => hj (ACtr.sim.inj hc)⟩
  | nop => exact congrArg (fun f c => f (ACtr.sim c)) (show g = f from h)

/-- A step of `U₂` is the `sim` step of the restart machine. -/
theorem step_sim {s : S₂ u} {v : LCtr → ℕ} {d : Cfg (S₂ u) LCtr} (h : (U₂ u).Step (s, v) d)
    (x w p t : ℕ) :
    (Asharp u L).Step (.inl (.run s), acfg v x w p t) (.inl (.gate d.1), acfg d.2 x w p t) := by
  obtain ⟨⟨a, o, b⟩, hρ, h1, h2, h3⟩ := h
  simp only at h1 h2
  subst h1 h2
  exact rstep (.sim hρ) (act_map_sim h3 x w p t)

/-- A token moves from `p` to `t` and the machine enters `run s`. -/
theorem reaches_spend (s : S₂ u) (v : LCtr → ℕ) (x w p t : ℕ) :
    Relation.TransGen (Asharp u L).Step (.inl (.gate s), acfg v x w (p + 1) t)
      (.inl (.run s), acfg v x w p (t + 1)) :=
  .head (rstep (.gateP s) (act_test' (by simp [acfg])))
    (.head (rstep (.sp₁ s) (act_dec' (n := p) rfl))
      (.single (rstep (.sp₂ s) (act_inc_eq (by acf)))))

/-- **One round.**  From `clr 0` with any counters, the machine reaches `gate start` with the
honest input built from `x`, `x := x + w`, `w := 0`, budget `p + t + 1`, nothing spent. -/
theorem reaches_round (v : LCtr → ℕ) (x w p t : ℕ) :
    Relation.TransGen (Asharp u L).Step (.inl (.clr 0), acfg v x w p t)
      (.inl (.gate (start₂ u)), acfg (honest (gIter x (L + 1))) (x + w) 0 (p + t + 1) 0) := by
  have h1 := clr_all (u := u) (L := L) v x w p t
  have h2 := (glue_chain_reaches (U := restart u) (hole := .hole) (back := .back) (i := cM)
    (L := L) (acfg 0 x w p t)).to_reflTransGen
  have h3 : (Asharp u L).Step (.inl .back, Function.update (acfg 0 x w p t) cM
      (acfg 0 x w p t cM + (L + 1))) (.inl .cx, acfg (honest (L + 1)) x w p t) :=
    rstep .back (show _ = _ by acf)
  have h4 := cx_loop (u := u) (L := L) x (acfg (honest (L + 1)) x w p t) rfl
    (by simp [acfg, honest])
  have h5 : (Asharp u L).Reaches (.inl .cx, acfg (honest (L + 1)) x w p t)
      (.inl .cw, acfg (honest (gIter x (L + 1))) 0 (w + x) p t) :=
    (reaches_upd h4 (by acf)).tail (rstep .cxZ (act_test' (by simp [acfg])))
  have h6 : (Asharp u L).Reaches (.inl .cw, acfg (honest (gIter x (L + 1))) 0 (w + x) p t)
      (.inl .bt, acfg (honest (gIter x (L + 1))) (x + w) 0 p t) :=
    (reaches_upd (cw_loop _ _ rfl) (by acf)).tail (rstep .cwZ (act_test' (by simp [acfg])))
  have h7 : (Asharp u L).Reaches (.inl .bt, acfg (honest (gIter x (L + 1))) (x + w) 0 p t)
      (.inl .bt₃, acfg (honest (gIter x (L + 1))) (x + w) 0 (p + t) 0) :=
    (reaches_upd (bt_loop _ _ rfl) (by acf)).tail (rstep .btZ (act_test' (by simp [acfg])))
  exact Relation.TransGen.tail' (h1.trans (h2.trans ((Relation.ReflTransGen.single h3).trans
    (h5.trans (h6.trans h7))))) (rstep .bt₃ (act_inc_eq (by acf)))

/-- **Gated simulation.**  `m` steps of `U₂` cost `m` tokens. -/
theorem reaches_gated {s s' : S₂ u} {v v' : LCtr → ℕ} {m : ℕ}
    (h : (U₂ u).StepsN m (s, v) (s', v')) (x w p t : ℕ) :
    (Asharp u L).Reaches (.inl (.gate s), acfg v x w (p + m) t)
      (.inl (.gate s'), acfg v' x w p (t + m)) := by
  suffices key : ∀ m c d, (U₂ u).StepsN m c d → ∀ t, (Asharp u L).Reaches
      (.inl (.gate c.1), acfg c.2 x w (p + m) t) (.inl (.gate d.1), acfg d.2 x w p (t + m)) from
    key m _ _ h t
  intro m c d hm
  induction hm with
  | refl c => intro t; exact .refl
  | @head n c d e hcd _ ih =>
    intro t
    have h1 := (reaches_spend (u := u) (L := L) c.1 c.2 x w (p + n) t).to_reflTransGen
    have h2 := step_sim (L := L) (show (U₂ u).Step (c.1, c.2) d from hcd) x w (p + n) (t + 1)
    have h3 := ih (t + 1)
    rw [show p + (n + 1) = p + n + 1 by omega]
    rw [show t + 1 + n = t + (n + 1) by omega] at h3
    exact h1.trans (.head h2 h3)

/-- A halting ID of `U₂` with a token left halts the machine. -/
theorem halts_of_stuck_gate {s : S₂ u} {v : LCtr → ℕ} (h : (U₂ u).Stuck (s, v)) (x w p t : ℕ) :
    (Asharp u L).Halts (.inl (.gate s), acfg v x w (p + 1) t) := by
  refine ⟨_, (reaches_spend (u := u) (L := L) s v x w p t).to_reflTransGen, ?_⟩
  intro d hd
  obtain ⟨q', -, hst⟩ := glue_step_inl_inv (by simp) hd
  obtain ⟨r, hr, h1, h2, h3⟩ := hst
  cases hr <;> simp only [AState.run.injEq, reduceCtorEq] at h1
  rename_i a b o hρ
  subst h1
  exact h (b, fun c => d.2 (.sim c)) ⟨_, hρ, rfl, rfl, act_map_sim_inv h3⟩

/-- An empty budget restarts. -/
theorem step_gate_zero (s : S₂ u) (v : LCtr → ℕ) (x w t : ℕ) :
    (Asharp u L).Step (.inl (.gate s), acfg v x w 0 t) (.inl (.clr 0), acfg v x w 0 t) :=
  rstep (.gateZ s) (act_test' (by simp [acfg]))

/-- **A gated round ends.**  From `gate s` with budget `p`, the machine halts (`U₂` reached a
halting ID) or spends the whole budget and reaches `clr 0`. -/
theorem gate_halts_or_restart (s : S₂ u) (v : LCtr → ℕ) (x w p t : ℕ) :
    (Asharp u L).Halts (.inl (.gate s), acfg v x w p t) ∨
      ∃ v', (Asharp u L).Reaches (.inl (.gate s), acfg v x w p t)
        (.inl (.clr 0), acfg v' x w 0 (t + p)) := by
  induction p generalizing s v t with
  | zero => exact Or.inr ⟨v, .single (step_gate_zero s v x w t)⟩
  | succ p ih =>
    by_cases hs : (U₂ u).Stuck (s, v)
    · exact Or.inl (halts_of_stuck_gate hs x w p t)
    simp only [CM.Stuck, not_forall, not_not] at hs
    obtain ⟨d, hd⟩ := hs
    have hr := reaches_gated (L := L) (CM.StepsN.head hd (.refl d)) x w p t
    rcases ih d.1 d.2 (t + 1) with ⟨e, he, hes⟩ | ⟨v', hv'⟩
    · exact Or.inl ⟨e, hr.trans he, hes⟩
    · refine Or.inr ⟨v', hr.trans ?_⟩
      rwa [show t + 1 + p = t + (p + 1) by omega] at hv'

/-! ### Garbage: every configuration halts or reaches the restart -/

/-- Halts, or reaches `clr 0`. -/
def GB (u : ToPartrec.Code) (L : ℕ) (c : Cfg (AState u ⊕ Fin L) ACtr) : Prop :=
  (Asharp u L).Halts c ∨ ∃ v x w p t, (Asharp u L).Reaches c (.inl (.clr 0), acfg v x w p t)

theorem gb_eta (c : ACtr → ℕ) :
    c = acfg (fun l => c (.sim l)) (c .x) (c .w) (c .p) (c .t) := by
  funext k; cases k <;> rfl

theorem gb_of_reaches {c d : Cfg (AState u ⊕ Fin L) ACtr} (h : (Asharp u L).Reaches c d)
    (hd : GB u L d) : GB u L c := by
  rcases hd with ⟨e, he, hs⟩ | ⟨v, x, w, p, t, hr⟩
  · exact Or.inl ⟨e, h.trans he, hs⟩
  · exact Or.inr ⟨v, x, w, p, t, h.trans hr⟩

/-- A configuration all of whose successors are good is good. -/
theorem gb_next {q : AState u} (hq : q ≠ .hole) (c : ACtr → ℕ)
    (h : ∀ r, ARule u r → r.src = q → ∀ c', r.op.Act c c' → GB u L (.inl r.dst, c')) :
    GB u L (.inl q, c) := by
  by_cases hs : (Asharp u L).Stuck (.inl q, c)
  · exact Or.inl ⟨_, .refl, hs⟩
  simp only [CM.Stuck, not_forall, not_not] at hs
  obtain ⟨d, hd⟩ := hs
  obtain ⟨q', hq', ρ, hρ, h1, h2, h3⟩ := glue_step_inl_inv hq hd
  have hd' : d = (.inl ρ.dst, d.2) := Prod.ext (hq'.trans (congrArg Sum.inl h2)) rfl
  exact gb_of_reaches (.single hd) (hd' ▸ h ρ hρ h1.symm d.2 h3)

theorem gb_clr0 (c : ACtr → ℕ) : GB u L (.inl (.clr 0), c) := by
  refine Or.inr ⟨fun l => c (.sim l), c .x, c .w, c .p, c .t, ?_⟩
  rw [← gb_eta c]; exact .refl

theorem gb_gate (s : S₂ u) (c : ACtr → ℕ) : GB u L (.inl (.gate s), c) := by
  rw [gb_eta c]
  rcases gate_halts_or_restart (L := L) s _ (c .x) (c .w) (c .p) (c .t) with h | ⟨v', h⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, _, _, _, _, h⟩

theorem gb_run (s : S₂ u) (c : ACtr → ℕ) : GB u L (.inl (.run s), c) :=
  gb_next (by simp) c fun r hr hs c' _ => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_gate _ _

theorem gb_sp₂ (s : S₂ u) (c : ACtr → ℕ) : GB u L (.inl (.sp₂ s), c) :=
  gb_next (by simp) c fun r hr hs c' _ => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_run _ _

theorem gb_sp₁ (s : S₂ u) (c : ACtr → ℕ) : GB u L (.inl (.sp₁ s), c) :=
  gb_next (by simp) c fun r hr hs c' _ => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_sp₂ _ _

/-- Induction on one counter. -/
theorem gb_ind (X : ACtr) (P : (ACtr → ℕ) → Prop) (h0 : ∀ c, c X = 0 → P c)
    (hs : ∀ n c, c X = n + 1 → (∀ c', c' X = n → P c') → P c) : ∀ c, P c := by
  suffices ∀ n c, c X = n → P c from fun c => this _ c rfl
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact fun c hc => hs n c hc ih

theorem gb_bt₃ (c : ACtr → ℕ) : GB u L (.inl .bt₃, c) :=
  gb_next (by simp) c fun r hr hs c' _ => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_gate _ _

theorem gb_bt (c : ACtr → ℕ) : GB u L (.inl .bt, c) := by
  refine gb_ind .t (fun c => GB u L (.inl .bt, c)) (fun c hc => ?_) (fun n c hc ih => ?_) c
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · exact gb_bt₃ _
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
    · obtain ⟨-, rfl⟩ := ha
      refine gb_next (q := .bt₁) (by simp) _ fun r hr hs c₁ ha₁ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h2, h3⟩ := ha₁
      refine gb_next (q := .bt₂) (by simp) c₁ fun r hr hs c₂ ha₂ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h5⟩ := ha₂
      exact ih _ (by rw [h5 .t (by decide)]; omega)

theorem gb_cw (c : ACtr → ℕ) : GB u L (.inl .cw, c) := by
  refine gb_ind .w (fun c => GB u L (.inl .cw, c)) (fun c hc => ?_) (fun n c hc ih => ?_) c
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · exact gb_bt _
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
    · obtain ⟨-, rfl⟩ := ha
      refine gb_next (q := .cw₁) (by simp) _ fun r hr hs c₁ ha₁ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h2, h3⟩ := ha₁
      refine gb_next (q := .cw₂) (by simp) c₁ fun r hr hs c₂ ha₂ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h5⟩ := ha₂
      exact ih _ (by rw [h5 .w (by decide)]; omega)

section CxLap

variable (n : ℕ) (hcx : ∀ c : ACtr → ℕ, c .x = n → GB u L (.inl .cx, c))
include hcx

theorem gb_ad : ∀ k (j : Fin 4), j.val + k = 3 → ∀ c : ACtr → ℕ, c .x = n →
    GB u L (.inl (.ad j), c) := by
  intro k
  induction k with
  | zero =>
    intro j hj c hc
    refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq, AState.ad.injEq] at hs
    · rename_i j₁ j' hj'
      subst hs; have := j'.isLt; omega
    · obtain ⟨-, h⟩ := ha
      exact hcx _ (by rw [h .x (by decide), hc])
  | succ k ih =>
    intro j hj c hc
    refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq, AState.ad.injEq] at hs
    · rename_i j₁ j' hj'
      subst hs
      obtain ⟨-, h⟩ := ha
      exact ih j' (by omega) _ (by rw [h .x (by decide), hc])
    · subst hs; simp at hj

omit hcx in
theorem gb_ml₁ (m : ℕ) (hml : ∀ c : ACtr → ℕ, c .x = n → c (.sim none) = m →
      GB u L (.inl .ml, c)) :
    ∀ k (j : Fin 6), 1 ≤ j.val → j.val + k = 5 → ∀ c : ACtr → ℕ, c .x = n →
      c (.sim none) = m → GB u L (.inl (.ml₁ j), c) := by
  intro k
  induction k with
  | zero =>
    intro j hj1 hj c hc hm
    refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq, AState.ml₁.injEq] at hs
    · subst hs; simp at hj
    · rename_i j₁ j' h1 hj'
      subst hs; have := j'.isLt; omega
    · obtain ⟨-, h⟩ := ha
      exact hml _ (by rw [h .x (by decide), hc]) (by rw [h (.sim none) (by decide), hm])
  | succ k ih =>
    intro j hj1 hj c hc hm
    refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq, AState.ml₁.injEq] at hs
    · subst hs; simp at hj1
    · rename_i j₁ j' h1 hj'
      subst hs
      obtain ⟨-, h⟩ := ha
      exact ih j' (by omega) (by omega) _ (by rw [h .x (by decide), hc])
        (by rw [h (.sim none) (by decide), hm])
    · subst hs; simp at hj

theorem gb_ml (c : ACtr → ℕ) (hc : c .x = n) : GB u L (.inl .ml, c) := by
  revert hc
  refine gb_ind (.sim none) (fun c => c .x = n → GB u L (.inl .ml, c))
    (fun c h0 hc => ?_) (fun m c hm ih hc => ?_) c
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨-, rfl⟩ := ha
      exact gb_ad n hcx 3 0 rfl _ hc
    · obtain ⟨h1, -⟩ := ha; simp [h0] at h1
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨h1, -⟩ := ha; simp [hm] at h1
    · obtain ⟨-, rfl⟩ := ha
      refine gb_next (q := .ml₁ 0) (by simp) _ fun r hr hs c₁ ha₁ => ?_
      cases hr <;> simp only [reduceCtorEq, AState.ml₁.injEq] at hs
      · obtain ⟨-, h2, h3⟩ := ha₁
        exact gb_ml₁ n m (fun c' h1 h2 => ih c' h2 h1) 4 1 le_rfl rfl _
          (by rw [h3 .x (by decide), hc]) (by omega)
      · rename_i j₁ j' h1 hj'; subst hs; simp at h1
      · simp at hs

theorem gb_mv (c : ACtr → ℕ) (hc : c .x = n) : GB u L (.inl .mv, c) := by
  revert hc
  refine gb_ind (.sim (some K'.main)) (fun c => c .x = n → GB u L (.inl .mv, c))
    (fun c h0 hc => ?_) (fun m c hm ih hc => ?_) c
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨-, rfl⟩ := ha
      exact gb_ml n hcx _ hc
    · obtain ⟨h1, -⟩ := ha; simp [h0] at h1
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨h1, -⟩ := ha; simp [hm] at h1
    · obtain ⟨-, rfl⟩ := ha
      refine gb_next (q := .mv₁) (by simp) _ fun r hr hs c₁ ha₁ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h2, h3⟩ := ha₁
      refine gb_next (q := .mv₂) (by simp) c₁ fun r hr hs c₂ ha₂ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h5⟩ := ha₂
      exact ih _ (by rw [h5 _ (by decide)]; omega)
        (by rw [h5 .x (by decide), h3 .x (by decide), hc])

end CxLap

theorem gb_cx (c : ACtr → ℕ) : GB u L (.inl .cx, c) := by
  refine gb_ind .x (fun c => GB u L (.inl .cx, c)) (fun c hc => ?_) (fun n c hc ih => ?_) c
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · exact gb_cw _
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
  · refine gb_next (by simp) c fun r hr hs c' ha => ?_
    cases hr <;> simp only [reduceCtorEq] at hs
    · obtain ⟨h1, -⟩ := ha; simp [hc] at h1
    · obtain ⟨-, rfl⟩ := ha
      refine gb_next (q := .cx₁) (by simp) _ fun r hr hs c₁ ha₁ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h2, h3⟩ := ha₁
      refine gb_next (q := .cx₂) (by simp) c₁ fun r hr hs c₂ ha₂ => ?_
      cases hr <;> simp only [reduceCtorEq] at hs
      obtain ⟨-, h5⟩ := ha₂
      exact gb_mv n ih _ (by rw [h5 .x (by decide)]; omega)

theorem gb_back (c : ACtr → ℕ) : GB u L (.inl .back, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_cx _

theorem gb_hole (c : ACtr → ℕ) : GB u L (.inl .hole, c) :=
  gb_of_reaches (glue_chain_reaches c).to_reflTransGen (gb_back _)

theorem gb_inr (k : Fin L) (c : ACtr → ℕ) : GB u L (.inr k, c) :=
  gb_of_reaches (glue_chain_reaches_of_inr k c).to_reflTransGen (gb_back _)

theorem gb_clr : ∀ k (j : Fin 5), j.val + k = 4 → ∀ c : ACtr → ℕ,
    GB u L (.inl (.clr j), c) := by
  intro k
  induction k with
  | zero =>
    intro j hj c
    refine gb_ind (.sim (clrCtr j)) (fun c => GB u L (.inl (.clr j), c))
      (fun c h0 => ?_) (fun m c hm ih => ?_) c
    · refine gb_next (by simp) c fun r hr hs c' ha => ?_
      cases hr <;> simp only [reduceCtorEq, AState.clr.injEq] at hs
      · subst hs; obtain ⟨h1, -⟩ := ha; simp [h0] at h1
      · rename_i j₁ j' hj'; subst hs; have := j'.isLt; omega
      · exact gb_hole _
    · refine gb_next (by simp) c fun r hr hs c' ha => ?_
      cases hr <;> simp only [reduceCtorEq, AState.clr.injEq] at hs
      · subst hs; obtain ⟨-, rfl⟩ := ha
        refine gb_next (q := .clr' _) (by simp) _ fun r hr hs c₁ ha₁ => ?_
        cases hr <;> simp only [reduceCtorEq, AState.clr'.injEq] at hs
        subst hs; obtain ⟨-, h2, -⟩ := ha₁
        exact ih _ (by omega)
      · rename_i j₁ j' hj'; subst hs; obtain ⟨h1, -⟩ := ha; simp [hm] at h1
      · subst hs; obtain ⟨h1, -⟩ := ha; simp [hm] at h1
  | succ k ihk =>
    intro j hj c
    refine gb_ind (.sim (clrCtr j)) (fun c => GB u L (.inl (.clr j), c))
      (fun c h0 => ?_) (fun m c hm ih => ?_) c
    · refine gb_next (by simp) c fun r hr hs c' ha => ?_
      cases hr <;> simp only [reduceCtorEq, AState.clr.injEq] at hs
      · subst hs; obtain ⟨h1, -⟩ := ha; simp [h0] at h1
      · rename_i j₁ j' hj'; subst hs; exact ihk j' (by omega) _
      · subst hs; simp at hj
    · refine gb_next (by simp) c fun r hr hs c' ha => ?_
      cases hr <;> simp only [reduceCtorEq, AState.clr.injEq] at hs
      · subst hs; obtain ⟨-, rfl⟩ := ha
        refine gb_next (q := .clr' _) (by simp) _ fun r hr hs c₁ ha₁ => ?_
        cases hr <;> simp only [reduceCtorEq, AState.clr'.injEq] at hs
        subst hs; obtain ⟨-, h2, -⟩ := ha₁
        exact ih _ (by omega)
      · rename_i j₁ j' hj'; subst hs; obtain ⟨h1, -⟩ := ha; simp [hm] at h1
      · subst hs; obtain ⟨h1, -⟩ := ha; simp [hm] at h1

theorem gb_clr' (j : Fin 5) (c : ACtr → ℕ) : GB u L (.inl (.clr' j), c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq, AState.clr'.injEq] at hs
    exact gb_clr (4 - j.val) _ (by omega) _

theorem gb_mv' (c : ACtr → ℕ) : GB u L (.inl .mv, c) := gb_mv _ (fun c _ => gb_cx c) c rfl

theorem gb_ml' (c : ACtr → ℕ) : GB u L (.inl .ml, c) := gb_ml _ (fun c _ => gb_cx c) c rfl

theorem gb_ml₁' (j : Fin 6) (c : ACtr → ℕ) : GB u L (.inl (.ml₁ j), c) := by
  by_cases hj : 1 ≤ j.val
  · exact gb_ml₁ (c .x) (c (.sim none)) (fun c _ _ => gb_ml' c) (5 - j.val) j hj
      (by omega) c rfl rfl
  · obtain rfl : j = 0 := Fin.ext (by omega)
    exact gb_next (by simp) c fun r hr hs c' ha => by
      cases hr <;> simp only [reduceCtorEq, AState.ml₁.injEq] at hs
      · exact gb_ml₁ (c' .x) (c' (.sim none)) (fun c _ _ => gb_ml' c) 4 1 le_rfl rfl c' rfl rfl
      · rename_i j₁ j' h1 hj'; subst hs; simp at h1
      · simp at hs

theorem gb_mv₂ (c : ACtr → ℕ) : GB u L (.inl .mv₂, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_mv' _

theorem gb_mv₁ (c : ACtr → ℕ) : GB u L (.inl .mv₁, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_mv₂ _

theorem gb_cx₂ (c : ACtr → ℕ) : GB u L (.inl .cx₂, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_mv' _

theorem gb_cx₁ (c : ACtr → ℕ) : GB u L (.inl .cx₁, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_cx₂ _

theorem gb_cw₂ (c : ACtr → ℕ) : GB u L (.inl .cw₂, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_cw _

theorem gb_cw₁ (c : ACtr → ℕ) : GB u L (.inl .cw₁, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_cw₂ _

theorem gb_bt₂ (c : ACtr → ℕ) : GB u L (.inl .bt₂, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_bt _

theorem gb_bt₁ (c : ACtr → ℕ) : GB u L (.inl .bt₁, c) :=
  gb_next (by simp) c fun r hr hs c' ha => by
    cases hr <;> simp only [reduceCtorEq] at hs
    exact gb_bt₂ _

/-- **Garbage.**  From every configuration the machine halts or reaches `clr 0`. -/
theorem halts_or_reaches_restart (c : Cfg (AState u ⊕ Fin L) ACtr) :
    (Asharp u L).Halts c ∨
      ∃ v x w p t, (Asharp u L).Reaches c (.inl (.clr 0), acfg v x w p t) := by
  obtain ⟨q, v⟩ := c
  rcases q with q | k
  · cases q with
    | run s => exact gb_run s v
    | gate s => exact gb_gate s v
    | sp₁ s => exact gb_sp₁ s v
    | sp₂ s => exact gb_sp₂ s v
    | clr j => exact gb_clr (4 - j.val) j (by omega) v
    | clr' j => exact gb_clr' j v
    | hole => exact gb_hole v
    | back => exact gb_back v
    | cx => exact gb_cx v
    | cx₁ => exact gb_cx₁ v
    | cx₂ => exact gb_cx₂ v
    | mv => exact gb_mv' v
    | mv₁ => exact gb_mv₁ v
    | mv₂ => exact gb_mv₂ v
    | ml => exact gb_ml' v
    | ml₁ j => exact gb_ml₁' j v
    | ad j => exact gb_ad _ (fun c _ => gb_cx c) (3 - j.val) j (by omega) v rfl
    | cw => exact gb_cw v
    | cw₁ => exact gb_cw₁ v
    | cw₂ => exact gb_cw₂ v
    | bt => exact gb_bt v
    | bt₁ => exact gb_bt₁ v
    | bt₂ => exact gb_bt₂ v
    | bt₃ => exact gb_bt₃ v
  · exact gb_inr k v

/-- A run of `n` steps splits after `m ≤ n` steps. -/
theorem stepsN_split {Q ι : Type*} {M : CM Q ι} :
    ∀ {n m : ℕ} {c d : Cfg Q ι}, M.StepsN n c d → m ≤ n →
      ∃ e, M.StepsN m c e ∧ M.StepsN (n - m) e d := by
  intro n m c d h
  induction h generalizing m with
  | refl c => intro hm; obtain rfl : m = 0 := by omega
              exact ⟨c, .refl _, .refl _⟩
  | @head n c d e hs _ ih =>
    intro hm
    rcases m with _ | m
    · exact ⟨c, .refl _, by simpa using CM.StepsN.head hs ‹_›⟩
    · obtain ⟨f, h1, h2⟩ := ih (m := m) (by omega)
      exact ⟨f, .head hs h1, by simpa [Nat.add_sub_add_right] using h2⟩

/-- A run of `n` steps reaches its end. -/
theorem reaches_of_stepsN {Q ι : Type*} {M : CM Q ι} {n : ℕ} {c d : Cfg Q ι}
    (h : M.StepsN n c d) : M.Reaches c d := by
  induction h with
  | refl => exact .refl
  | head hs _ ih => exact .head hs ih

/-- The first `n` steps of an infinite run. -/
theorem stepsN_of_forever {Q ι : Type*} {M : CM Q ι} (y : ℕ → Cfg Q ι)
    (hy : ∀ n, M.Step (y n) (y (n + 1))) : ∀ n, M.StepsN n (y 0) (y n) := by
  suffices ∀ n k, M.StepsN n (y k) (y (k + n)) from fun n => by simpa using this n 0
  intro n
  induction n with
  | zero => intro k; exact .refl _
  | succ n ih =>
    intro k
    have := ih (k + 1)
    rw [show k + 1 + n = k + (n + 1) by omega] at this
    exact .head (hy k) this

/-- **Steady rounds halt** when `U₂` halts on the input: the budget grows by one per round. -/
theorem halts_of_steady {x : ℕ} (h : (U₂ u).Halts (start₂ u, honest (gIter x (L + 1))))
    (v : LCtr → ℕ) (t : ℕ) : (Asharp u L).Halts (.inl (.clr 0), acfg v x 0 0 t) := by
  have back : ∀ {c d : Cfg (AState u ⊕ Fin L) ACtr}, (Asharp u L).Reaches c d →
      (Asharp u L).Halts d → (Asharp u L).Halts c :=
    fun hr ⟨e, he, hs⟩ => ⟨e, hr.trans he, hs⟩
  obtain ⟨d, hd, hds⟩ := h
  obtain ⟨n, hn⟩ := CM.StepsN.of_reaches hd
  suffices ∀ k t v, n ≤ t + k → (Asharp u L).Halts (.inl (.clr 0), acfg v x 0 0 t) from
    this n t v (by omega)
  intro k
  induction k with
  | zero =>
    intro t v hnt
    have hr := reaches_round (u := u) (L := L) v x 0 0 t
    rw [Nat.add_zero, Nat.zero_add, show t + 1 = (t - n) + 1 + n by omega] at hr
    refine back hr.to_reflTransGen (back (reaches_gated hn x 0 _ 0) ?_)
    exact halts_of_stuck_gate hds x 0 (t - n) (0 + n)
  | succ k ih =>
    intro t v hnt
    by_cases hnt' : n ≤ t
    · exact ih t v (by omega)
    obtain ⟨e, he, -⟩ := stepsN_split hn (m := t + 1) (by omega)
    have hr := reaches_round (u := u) (L := L) v x 0 0 t
    rw [Nat.add_zero, Nat.zero_add, show t + 1 = 0 + (t + 1) by omega] at hr
    refine back hr.to_reflTransGen (back (reaches_gated he x 0 0 0) ?_)
    refine back (.single (step_gate_zero _ _ _ _ _)) ?_
    rw [Nat.zero_add]
    exact ih (t + 1) e.2 (by omega)

/-- **An immortal configuration** from an input on which `U₂` runs forever. -/
theorem not_halts_of_not_halts {x : ℕ} (h : ¬ (U₂ u).Halts (start₂ u, honest (gIter x (L + 1)))) :
    ¬ (Asharp u L).Halts (.inl (.clr 0), acfg 0 x 0 0 0) := by
  obtain ⟨y, hy0, hy⟩ := RcwaOrbitCount.exists_forever_of_not_halts h
  -- one round from `clr 0` with `t` spent returns to `clr 0` with `t + 1` spent
  have hround : ∀ (v : LCtr → ℕ) (t : ℕ), ∃ v', Relation.TransGen (Asharp u L).Step
      (.inl (.clr 0), acfg v x 0 0 t) (.inl (.clr 0), acfg v' x 0 0 (t + 1)) := by
    intro v t
    have hr := reaches_round (u := u) (L := L) v x 0 0 t
    rw [Nat.add_zero, Nat.zero_add, show t + 1 = 0 + (t + 1) by omega] at hr
    have hg := reaches_gated (L := L) (hy0 ▸ stepsN_of_forever y hy (t + 1)) x 0 0 0
    refine ⟨(y (t + 1)).2, ?_⟩
    have := (hr.trans_left hg).tail (step_gate_zero _ _ _ _ _)
    rwa [Nat.zero_add] at this
  rintro ⟨d, hd, hds⟩
  obtain ⟨n, hn⟩ := CM.StepsN.of_reaches hd
  clear hd
  suffices ∀ n (v : LCtr → ℕ) (t : ℕ),
      (Asharp u L).StepsN n (.inl (.clr 0), acfg v x 0 0 t) d → False from this n 0 0 hn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v t hn
    obtain ⟨v', hv'⟩ := hround v t
    obtain ⟨m, hm, hmd⟩ := CM.StepsN.of_transGen (asharp_det u L) hds hv' hn
    exact ih m hm v' (t + 1) hmd

/-- **Lemma A, machine form.**  The glued restart machine is mortal iff `U₂` halts on every
honest input. -/
theorem mortal_asharp_iff :
    Mortal (Asharp u L) ↔ ∀ x : ℕ, (U₂ u).Halts (start₂ u, honest (gIter x (L + 1))) := by
  have back : ∀ {c d : Cfg (AState u ⊕ Fin L) ACtr}, (Asharp u L).Reaches c d →
      (Asharp u L).Halts d → (Asharp u L).Halts c :=
    fun hr ⟨e, he, hs⟩ => ⟨e, hr.trans he, hs⟩
  constructor
  · intro h x
    by_contra hx
    exact not_halts_of_not_halts hx (h _)
  · intro h c
    rcases halts_or_reaches_restart c with hc | ⟨v, x, w, p, t, hr⟩
    · exact hc
    refine back hr (back (reaches_round v x w p t).to_reflTransGen ?_)
    rcases gate_halts_or_restart (start₂ u) _ (x + w) 0 (p + t + 1) 0 with hg | ⟨v', hg⟩
    · exact hg
    · rw [Nat.zero_add] at hg
      exact back hg (halts_of_steady (h (x + w)) v' _)

end Runs

/-! ## 4. Totality -/

/-- **Lemma A.**  With `u` from `exists_universal₂` and the chain length
`L = 1 + 5 · inputNum e`, the glued restart machine is mortal iff `φ_e` is total. -/
theorem mortal_iff_total {u : ToPartrec.Code}
    (hu : ∀ a e : ℕ, (u.eval [a, e]).Dom ↔
      ∀ y ≤ a, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) y).Dom)
    (e : ℕ) : Mortal (Asharp u (1 + 5 * inputNum e)) ↔ Total e := by
  rw [mortal_asharp_iff, show 1 + 5 * inputNum e + 1 = 2 + 5 * inputNum e by omega]
  simp only [halts_u₂_iff, hu]
  constructor
  · intro h y
    have : y < 2 ^ y := Nat.lt_two_pow_self
    exact h y y (by omega)
  · intro h x y _
    exact h y

end CollatzMoonshot.RcwaTotality
