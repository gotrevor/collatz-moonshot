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

/-- **A universal code for initial segments.**  `u` halts on `[a, e]` iff `φ_e` halts on every
`y ≤ a`. -/
theorem exists_universal₂ : ∃ u : ToPartrec.Code, ∀ a e : ℕ,
    (u.eval [a, e]).Dom ↔
      ∀ y ≤ a, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) y).Dom := by
  sorry

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

/-- `trNat (2 ^ x - 1)` is `x` copies of `bit1`. -/
theorem trNat_two_pow_sub_one (x : ℕ) : trNat (2 ^ x - 1) = List.replicate x Γ'.bit1 := by
  sorry

/-- The main-stack numeral of `[2 ^ x - 1, e]`. -/
theorem num_trList_pair (x e : ℕ) :
    num (trList [2 ^ x - 1, e]) = gIter x (2 + 5 * inputNum e) := by
  sorry

/-- **The universal machine on honest inputs.** -/
theorem halts_u₂_iff (u : ToPartrec.Code) (x e : ℕ) :
    (U₂ u).Halts (start₂ u, honest (gIter x (2 + 5 * inputNum e))) ↔
      (u.eval [2 ^ x - 1, e]).Dom := by
  sorry

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

/-- Finitely many states. -/
theorem finite_aState (u : ToPartrec.Code) : Finite (AState u) := by
  sorry

/-- The restart machine is deterministic. -/
theorem restart_det (u : ToPartrec.Code) : (restart u).Det := by
  sorry

/-- No rule leaves `hole`. -/
theorem restart_src_ne_hole (u : ToPartrec.Code) : ∀ ρ ∈ restart u, ρ.src ≠ .hole := by
  sorry

/-- No rule enters `back`. -/
theorem restart_normalAt_back (u : ToPartrec.Code) : (restart u).NormalAt .back := by
  sorry

/-- The glued restart machine is deterministic. -/
theorem asharp_det (u : ToPartrec.Code) (L : ℕ) : (Asharp u L).Det :=
  glue_det (restart_det u) (restart_src_ne_hole u)

/-! ## 3. Runs of the glued restart machine -/

section Runs

variable {u : ToPartrec.Code} {L : ℕ}

/-- **One round.**  From `clr 0` with any counters, the machine reaches `gate start` with the
honest input built from `x`, `x := x + w`, `w := 0`, budget `p + t + 1`, nothing spent. -/
theorem reaches_round (v : LCtr → ℕ) (x w p t : ℕ) :
    Relation.TransGen (Asharp u L).Step (.inl (.clr 0), acfg v x w p t)
      (.inl (.gate (start₂ u)), acfg (honest (gIter x (L + 1))) (x + w) 0 (p + t + 1) 0) := by
  sorry

/-- **Gated simulation.**  `m` steps of `U₂` cost `m` tokens. -/
theorem reaches_gated {s s' : S₂ u} {v v' : LCtr → ℕ} {m : ℕ}
    (h : (U₂ u).StepsN m (s, v) (s', v')) (x w p t : ℕ) :
    (Asharp u L).Reaches (.inl (.gate s), acfg v x w (p + m) t)
      (.inl (.gate s'), acfg v' x w p (t + m)) := by
  sorry

/-- A halting ID of `U₂` with a token left halts the machine. -/
theorem halts_of_stuck_gate {s : S₂ u} {v : LCtr → ℕ} (h : (U₂ u).Stuck (s, v)) (x w p t : ℕ) :
    (Asharp u L).Halts (.inl (.gate s), acfg v x w (p + 1) t) := by
  sorry

/-- An empty budget restarts. -/
theorem step_gate_zero (s : S₂ u) (v : LCtr → ℕ) (x w t : ℕ) :
    (Asharp u L).Step (.inl (.gate s), acfg v x w 0 t) (.inl (.clr 0), acfg v x w 0 t) := by
  sorry

/-- **A gated round ends.**  From `gate s` with budget `p`, the machine halts (`U₂` reached a
halting ID) or spends the whole budget and reaches `clr 0`. -/
theorem gate_halts_or_restart (s : S₂ u) (v : LCtr → ℕ) (x w p t : ℕ) :
    (Asharp u L).Halts (.inl (.gate s), acfg v x w p t) ∨
      ∃ v', (Asharp u L).Reaches (.inl (.gate s), acfg v x w p t)
        (.inl (.clr 0), acfg v' x w 0 (t + p)) := by
  sorry

/-- **Garbage.**  From every configuration the machine halts or reaches `clr 0`. -/
theorem halts_or_reaches_restart (c : Cfg (AState u ⊕ Fin L) ACtr) :
    (Asharp u L).Halts c ∨
      ∃ v x w p t, (Asharp u L).Reaches c (.inl (.clr 0), acfg v x w p t) := by
  sorry

/-- **Steady rounds halt** when `U₂` halts on the input: the budget grows by one per round. -/
theorem halts_of_steady {x : ℕ} (h : (U₂ u).Halts (start₂ u, honest (gIter x (L + 1))))
    (v : LCtr → ℕ) (t : ℕ) : (Asharp u L).Halts (.inl (.clr 0), acfg v x 0 0 t) := by
  sorry

/-- **An immortal configuration** from an input on which `U₂` runs forever. -/
theorem not_halts_of_not_halts {x : ℕ} (h : ¬ (U₂ u).Halts (start₂ u, honest (gIter x (L + 1)))) :
    ¬ (Asharp u L).Halts (.inl (.clr 0), acfg 0 x 0 0 0) := by
  sorry

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
