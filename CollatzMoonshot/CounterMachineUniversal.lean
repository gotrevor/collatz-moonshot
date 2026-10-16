/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.CounterMachine

/-!
# A fixed counter machine with an undecidable halting problem

The lower half of the hypothesis-free Theorem C: Mathlib's halting problem
(`ComputablePred.halting_problem`) gives `CounterMachine.UndecidableCM`.

1. **A universal code.**  `Turing.ToPartrec.Code.exists_code` turns the partial recursive
   `n ↦ Nat.Partrec.Code.eval (ofNat n) 0` into one fixed `ToPartrec.Code` `u`, and halting of
   `u` on `[n]` is not computable (`not_computable_universal`).
2. **Stacks as numerals.**  Mathlib's `Turing.PartrecToTM2.tr` runs every `ToPartrec.Code` on a
   TM2 machine with four stacks over the 4-letter alphabet `Γ'` and local store `Option Γ'`
   (`tr_eval`).  A stack `a₀ :: a₁ :: …` is the numeral `digit a₀ + 5 · digit a₁ + …` with digits
   `1, …, 4` (`num`), top digit least significant, so push is `n ↦ 5n + d` and pop is division by
   `5` with remainder (`0` iff the stack is empty).
3. **The compile.**  One counter per stack plus a scratch counter `tmp` (`Option K'`, `none` =
   `tmp`).  The machine `lcm l₀` has a state `stmt s v` for every TM2 statement `s` and store
   `v`, and gadget states `gad s v ph`.  A statement runs as a Morita gadget (Minsky's
   multiply/divide loops through `tmp`): `push` multiplies by `5` and adds the digit, `pop`
   divides by `5` keeping the remainder in the state, `peek` divides and restores, `load`,
   `branch`, `goto` are one `nop`, `halt` has no rule.  A fresh `start` state (normal form) steps
   to `stmt (tr l₀) none`.  The machine is syntactically deterministic (`det_lcm`).
4. **Simulation.**  `repCfg` sends a TM2 configuration to a counter configuration; one TM2 step
   is a nonempty run (`stepAux_reaches`), and a halted TM2 configuration is stuck.  So halting
   matches (`halts_iff_eval`).
5. **Finiteness and the interface.**  The states reachable from `codeSupp u halt` form a finite
   closed set (`reachSet`, from Mathlib's `tr_supports`), so restricting to it gives a finite
   machine, and `undecidableCM` assembles the interface Prop with `enc = inputNum`.
-/

namespace CollatzMoonshot.CounterMachineUniversal

open Turing Turing.PartrecToTM2 CollatzMoonshot.CounterMachine

/-! ## 1. A universal code -/

/-- A fixed `ToPartrec.Code` that halts on `[n]` iff the `n`-th `Nat.Partrec.Code` halts on `0`. -/
theorem exists_universal : ∃ u : ToPartrec.Code, ∀ n : ℕ,
    (u.eval [n]).Dom ↔ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0).Dom := by
  let f₀ : ℕ →. ℕ := fun n => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0
  have hf : Partrec f₀ :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
  obtain ⟨u, hu⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 hf)
  refine ⟨u, fun n => ?_⟩
  have := hu ⟨[n], rfl⟩
  simp only at this
  rw [this]
  simp only [f₀, Part.map_eq_map, Part.map_Dom]
  exact Iff.rfl

/-- Halting of a universal code is not computable. -/
theorem not_computable_universal {u : ToPartrec.Code}
    (hu : ∀ n : ℕ,
      (u.eval [n]).Dom ↔ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0).Dom) :
    ¬ ComputablePred fun n : ℕ => (u.eval [n]).Dom := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.1 h
  apply ComputablePred.halting_problem 0
  refine ComputablePred.computable_iff.2 ⟨fun c => f (Encodable.encode c),
    hf.comp Computable.encode, funext fun c => ?_⟩
  have := congrFun hfe (Encodable.encode c)
  have h1 := hu (Encodable.encode c)
  rw [Denumerable.ofNat_encode] at h1
  rw [← this, h1]

/-! ## 2. Stacks as numerals -/

instance : Fintype K' where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro x; cases x <;> simp

/-- The digit of a stack symbol, `1, …, 4`. -/
def digitF : Γ' → Fin 5
  | .consₗ => 1
  | .cons => 2
  | .bit0 => 3
  | .bit1 => 4

/-- The digit as a natural number. -/
def digit (a : Γ') : ℕ :=
  (digitF a).val

/-- The symbol of a remainder: `0` is the empty stack, `1, …, 4` the four symbols. -/
def undigit : Fin 5 → Option Γ'
  | 1 => some .consₗ
  | 2 => some .cons
  | 3 => some .bit0
  | 4 => some .bit1
  | _ => none

/-- A stack as a numeral in base `5`, top digit least significant. -/
def num : List Γ' → ℕ
  | [] => 0
  | a :: l => digit a + 5 * num l

/-- The counters of a TM2 configuration's stacks (`tmp = 0`). -/
def stackVec (S : K' → List Γ') : Option K' → ℕ
  | some k => num (S k)
  | none => 0

/-- The input numeral: the main stack of `init u [n]`. -/
def inputNum (n : ℕ) : ℕ :=
  num (trList [n])

/-- The remainder mod `5` of a numeral reads the top symbol. -/
theorem undigit_num (l : List Γ') :
    undigit ⟨num l % 5, Nat.mod_lt _ (by norm_num)⟩ = l.head? := by
  cases l with
  | nil => rfl
  | cons a l =>
    have : num (a :: l) % 5 = digit a := by
      simp only [num]; cases a <;> simp [digit, digitF]
    simp only [this]
    cases a <;> rfl

/-- The quotient by `5` of a numeral is the numeral of the tail. -/
theorem num_div_five (l : List Γ') : num l / 5 = num l.tail := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [num, List.tail_cons]
    have : digit a < 5 := (digitF a).isLt
    omega

/-- Pushing is `n ↦ 5 n + digit a`. -/
theorem num_cons (a : Γ') (l : List Γ') : num (a :: l) = 5 * num l + digit a := by
  simp only [num]; ring

/-- The initial counters: the input numeral on the main stack, everything else `0`. -/
theorem stackVec_init (n : ℕ) :
    stackVec (K'.elim (trList [n]) [] [] []) = Pi.single (some K'.main) (inputNum n) := by
  funext x
  rcases x with _ | k
  · rfl
  · cases k <;> simp [stackVec, inputNum, Pi.single, Function.update, K'.elim, num]

/-- The input numeral of a positive binary numeral. -/
theorem inputNum_pos (p : PosNum) : inputNum (p : ℕ) = num (trPosNum p ++ [Γ'.cons]) := by
  simp [inputNum, trList, trNat, trNum]

/-- The input numeral is computable. -/
theorem computable_inputNum : Computable inputNum := by
  have hrec : ∀ n, inputNum n =
      if n = 0 then 2 else 3 + n % 2 + 5 * inputNum (n / 2) := by
    intro n
    split_ifs with hn
    · subst hn; rfl
    · rw [← Num.to_of_nat n] at hn ⊢
      generalize (n : Num) = m at hn ⊢
      rcases m with _ | p
      · exact absurd rfl hn
      · rcases p with _ | q | q
        · rfl
        · simp only [Num.cast_pos]
          rw [inputNum_pos, PosNum.cast_bit1,
            show ((q : ℕ) + q + 1) / 2 = (q : ℕ) by omega, inputNum_pos]
          simp [trPosNum, num, digit, digitF]; omega
        · simp only [Num.cast_pos]
          rw [inputNum_pos, PosNum.cast_bit0,
            show ((q : ℕ) + q) / 2 = (q : ℕ) by omega, inputNum_pos]
          simp [trPosNum, num, digit, digitF]; omega
  let g : Unit → List ℕ → Option ℕ := fun _ l =>
    some (if l.length = 0 then 2 else 3 + l.length % 2 + 5 * l.getD (l.length / 2) 0)
  have hg : Primrec₂ g := by
    refine Primrec.option_some.comp (Primrec.ite ?_ (Primrec.const 2) ?_)
    · exact (PrimrecRel.comp Primrec.eq (Primrec.list_length.comp Primrec.snd)
        (Primrec.const 0))
    · have hlen : Primrec fun p : Unit × List ℕ => p.2.length :=
        Primrec.list_length.comp Primrec.snd
      refine Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 3)
        (Primrec.nat_mod.comp hlen (Primrec.const 2)))
        (Primrec.nat_mul.comp (Primrec.const 5) ?_)
      exact (Primrec.list_getD 0).comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2))
  have hf : Primrec₂ fun (_ : Unit) n => inputNum n := by
    refine Primrec.nat_strong_rec _ hg fun _ n => ?_
    simp only [g, List.length_map, List.length_range]
    rw [hrec n]
    split_ifs with hn
    · rfl
    · congr 3
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
  exact (hf.comp (Primrec.const ()) Primrec.id).to_comp

/-! ## 3. The compile -/

/-- The phases of a statement gadget (`k` is the statement's stack, `tmp` the scratch counter).

* push: `pa`/`pb`/`pc` move `k` into `tmp`; `pd` tests `tmp`; `pe 0` decrements `tmp`, `pe 1…5`
  increment `k` (so `k := 5 · tmp`); `pg j` adds the digit.
* pop and peek: `da j`/`dc j`/`dd` divide `k` by `5` into `tmp`, the remainder `j` in the state;
  `db r` tests `tmp`, `de r` decrements it, `df r j` increments `k` (once for pop, from `df r 5`;
  five times for peek, from `df r 1`); peek then adds `r` back in `dg r j`. -/
inductive Phase
  | pa | pb | pc | pd
  | pe (j : Fin 6)
  | pg (j : Fin 5)
  | da (j : Fin 5) | dc (j : Fin 5) | dd
  | db (r : Fin 5) | de (r : Fin 5) | df (r : Fin 5) (j : Fin 6)
  | dg (r : Fin 5) (j : Fin 5)
  deriving DecidableEq, Fintype

/-- The states: a fresh start, statement entries `stmt s v`, and gadget states. -/
inductive LState
  | start
  | stmt (s : Stmt') (v : Option Γ')
  | gad (s : Stmt') (v : Option Γ') (ph : Phase)

/-- The counters: `some k` is stack `k`, `none` the scratch counter `tmp`. -/
abbrev LCtr : Type := Option K'

/-- The division gadget shared by pop and peek: from `da 0` with `tmp = 0`, end at `db r` with
`k = 0`, `tmp = n / 5`, `r = n % 5`. -/
def divRules (s : Stmt') (v : Option Γ') (k : K') : List (Quad LState LCtr) :=
  (List.finRange 5).flatMap (fun j => [⟨.gad s v (.da j), .test (some k) false, .gad s v (.db j)⟩,
    ⟨.gad s v (.da j), .test (some k) true, .gad s v (.dc j)⟩]) ++
  (List.finRange 4).map (fun j =>
    ⟨.gad s v (.dc j.castSucc), .dec (some k), .gad s v (.da j.succ)⟩) ++
  [⟨.gad s v (.dc (Fin.last 4)), .dec (some k), .gad s v .dd⟩,
    ⟨.gad s v .dd, .inc none, .gad s v (.da 0)⟩]

/-- The return loop shared by pop and peek: `df r j` increments `k` and moves to `df r (j+1)`,
and `df r 5` back to `db r`; `de r` decrements `tmp` and enters at `df r e`. -/
def backRules (s : Stmt') (v : Option Γ') (k : K') (e : Fin 6) : List (Quad LState LCtr) :=
  (List.finRange 5).flatMap fun r =>
    [⟨.gad s v (.db r), .test none true, .gad s v (.de r)⟩,
      ⟨.gad s v (.de r), .dec none, .gad s v (.df r e)⟩,
      ⟨.gad s v (.df r (Fin.last 5)), .inc (some k), .gad s v (.db r)⟩] ++
    (List.finRange 4).map fun j =>
      ⟨.gad s v (.df r j.succ.castSucc), .inc (some k), .gad s v (.df r j.succ.succ)⟩

/-- The rules of statement `s` with store `v`. -/
def gadget : Stmt' → Option Γ' → List (Quad LState LCtr)
  | s@(TM2.Stmt.push k f q), v =>
    let d := digitF (f v)
    [⟨.stmt s v, .nop, .gad s v .pa⟩,
      ⟨.gad s v .pa, .test (some k) false, .gad s v .pd⟩,
      ⟨.gad s v .pa, .test (some k) true, .gad s v .pb⟩,
      ⟨.gad s v .pb, .dec (some k), .gad s v .pc⟩,
      ⟨.gad s v .pc, .inc none, .gad s v .pa⟩,
      ⟨.gad s v .pd, .test none false, .gad s v (.pg 0)⟩,
      ⟨.gad s v .pd, .test none true, .gad s v (.pe 0)⟩,
      ⟨.gad s v (.pe 0), .dec none, .gad s v (.pe 1)⟩,
      ⟨.gad s v (.pe (Fin.last 5)), .inc (some k), .gad s v .pd⟩,
      ⟨.gad s v (.pg d), .nop, .stmt q v⟩] ++
    (List.finRange 4).map (fun j =>
      ⟨.gad s v (.pe j.succ.castSucc), .inc (some k), .gad s v (.pe j.succ.succ)⟩) ++
    ((List.finRange 4).filter fun j => j.val < d.val).map fun j =>
      ⟨.gad s v (.pg j.castSucc), .inc (some k), .gad s v (.pg j.succ)⟩
  | s@(TM2.Stmt.pop k f q), v =>
    ⟨.stmt s v, .nop, .gad s v (.da 0)⟩ :: divRules s v k ++ backRules s v k (Fin.last 5) ++
      (List.finRange 5).map fun r =>
        ⟨.gad s v (.db r), .test none false, .stmt q (f v (undigit r))⟩
  | s@(TM2.Stmt.peek k f q), v =>
    ⟨.stmt s v, .nop, .gad s v (.da 0)⟩ :: divRules s v k ++ backRules s v k 1 ++
      (List.finRange 5).flatMap fun r =>
        [⟨.gad s v (.db r), .test none false, .gad s v (.dg r 0)⟩,
          ⟨.gad s v (.dg r r), .nop, .stmt q (f v (undigit r))⟩] ++
        ((List.finRange 4).filter fun j => j.val < r.val).map fun j =>
          ⟨.gad s v (.dg r j.castSucc), .inc (some k), .gad s v (.dg r j.succ)⟩
  | s@(TM2.Stmt.load a q), v => [⟨.stmt s v, .nop, .stmt q (a v)⟩]
  | s@(TM2.Stmt.branch f q₁ q₂), v => [⟨.stmt s v, .nop, .stmt (cond (f v) q₁ q₂) v⟩]
  | s@(TM2.Stmt.goto f), v => [⟨.stmt s v, .nop, .stmt (tr (f v)) v⟩]
  | TM2.Stmt.halt, _ => []

/-- The compiled machine started at label `l₀`. -/
def lcm (l₀ : Λ') : CM LState LCtr :=
  {ρ | ρ = ⟨.start, .nop, .stmt (tr l₀) none⟩ ∨ ∃ s v, ρ ∈ gadget s v}

/-- An abstract gadget rule over the two counters a gadget touches (`none` = `tmp`,
`some ()` = its stack): source phase (`none` = the entry `stmt s v`), operation, and target
(`inl ph` a phase, `inr r` the `r`-th exit). -/
structure ARule where
  src : Option Phase
  op : Op (Option Unit)
  dst : Phase ⊕ Fin 5
  deriving DecidableEq

/-- Abstract division rules (mirror of `divRules`). -/
def divA : List ARule :=
  (List.finRange 5).flatMap (fun j => [⟨some (.da j), .test (some ()) false, .inl (.db j)⟩,
    ⟨some (.da j), .test (some ()) true, .inl (.dc j)⟩]) ++
  (List.finRange 4).map (fun j =>
    ⟨some (.dc j.castSucc), .dec (some ()), .inl (.da j.succ)⟩) ++
  [⟨some (.dc (Fin.last 4)), .dec (some ()), .inl .dd⟩,
    ⟨some .dd, .inc none, .inl (.da 0)⟩]

/-- Abstract return rules (mirror of `backRules`). -/
def backA (e : Fin 6) : List ARule :=
  (List.finRange 5).flatMap fun r =>
    [⟨some (.db r), .test none true, .inl (.de r)⟩,
      ⟨some (.de r), .dec none, .inl (.df r e)⟩,
      ⟨some (.df r (Fin.last 5)), .inc (some ()), .inl (.db r)⟩] ++
    (List.finRange 4).map fun j =>
      ⟨some (.df r j.succ.castSucc), .inc (some ()), .inl (.df r j.succ.succ)⟩

/-- Abstract push gadget for digit `d`. -/
def pushA (d : Fin 5) : List ARule :=
  [⟨none, .nop, .inl .pa⟩,
    ⟨some .pa, .test (some ()) false, .inl .pd⟩,
    ⟨some .pa, .test (some ()) true, .inl .pb⟩,
    ⟨some .pb, .dec (some ()), .inl .pc⟩,
    ⟨some .pc, .inc none, .inl .pa⟩,
    ⟨some .pd, .test none false, .inl (.pg 0)⟩,
    ⟨some .pd, .test none true, .inl (.pe 0)⟩,
    ⟨some (.pe 0), .dec none, .inl (.pe 1)⟩,
    ⟨some (.pe (Fin.last 5)), .inc (some ()), .inl .pd⟩,
    ⟨some (.pg d), .nop, .inr 0⟩] ++
  (List.finRange 4).map (fun j =>
    ⟨some (.pe j.succ.castSucc), .inc (some ()), .inl (.pe j.succ.succ)⟩) ++
  ((List.finRange 4).filter fun j => j.val < d.val).map fun j =>
    ⟨some (.pg j.castSucc), .inc (some ()), .inl (.pg j.succ)⟩

/-- Abstract pop gadget. -/
def popA : List ARule :=
  ⟨none, .nop, .inl (.da 0)⟩ :: divA ++ backA (Fin.last 5) ++
    (List.finRange 5).map fun r => ⟨some (.db r), .test none false, .inr r⟩

/-- Abstract peek gadget. -/
def peekA : List ARule :=
  ⟨none, .nop, .inl (.da 0)⟩ :: divA ++ backA 1 ++
    (List.finRange 5).flatMap fun r =>
      [⟨some (.db r), .test none false, .inl (.dg r 0)⟩,
        ⟨some (.dg r r), .nop, .inr r⟩] ++
      ((List.finRange 4).filter fun j => j.val < r.val).map fun j =>
        ⟨some (.dg r j.castSucc), .inc (some ()), .inl (.dg r j.succ)⟩

/-- The abstract rules of a statement. -/
def gadA : Stmt' → Option Γ' → List ARule
  | TM2.Stmt.push _ f _, v => pushA (digitF (f v))
  | TM2.Stmt.pop .., _ => popA
  | TM2.Stmt.peek .., _ => peekA
  | TM2.Stmt.load .., _ => [⟨none, .nop, .inr 0⟩]
  | TM2.Stmt.branch .., _ => [⟨none, .nop, .inr 0⟩]
  | TM2.Stmt.goto _, _ => [⟨none, .nop, .inr 0⟩]
  | TM2.Stmt.halt, _ => []

/-- The stack a statement's gadget works on. -/
def gadK : Stmt' → K'
  | TM2.Stmt.push k _ _ => k
  | TM2.Stmt.pop k _ _ => k
  | TM2.Stmt.peek k _ _ => k
  | _ => .main

/-- The exits of a statement's gadget. -/
def gadExit : Stmt' → Option Γ' → Fin 5 → LState
  | TM2.Stmt.push _ _ q, v, _ => .stmt q v
  | TM2.Stmt.pop _ f q, v, r => .stmt q (f v (undigit r))
  | TM2.Stmt.peek _ f q, v, r => .stmt q (f v (undigit r))
  | TM2.Stmt.load a q, v, _ => .stmt q (a v)
  | TM2.Stmt.branch f q₁ q₂, v, _ => .stmt (cond (f v) q₁ q₂) v
  | TM2.Stmt.goto f, v, _ => .stmt (tr (f v)) v
  | TM2.Stmt.halt, _, _ => .start

/-- The source state of an abstract source. -/
def embSrc (s : Stmt') (v : Option Γ') : Option Phase → LState
  | none => .stmt s v
  | some ph => .gad s v ph

/-- Realize an abstract rule in statement `s`, store `v`. -/
def emb (s : Stmt') (v : Option Γ') (a : ARule) : Quad LState LCtr :=
  ⟨embSrc s v a.src, a.op.map (Option.map fun _ => gadK s),
    a.dst.elim (.gad s v) (gadExit s v)⟩

theorem gadget_eq (s : Stmt') (v : Option Γ') : gadget s v = (gadA s v).map (emb s v) := by
  cases s <;> simp [gadget, gadA, emb, embSrc, gadExit, gadK, pushA, popA, peekA, divRules,
    divA, backRules, backA, Op.map, List.map_flatMap, Function.comp_def]

/-- Abstract determinism. -/
def ADet (L : List ARule) : Prop :=
  ∀ a ∈ L, ∀ a' ∈ L, a ≠ a' → a.src = a'.src →
    ∃ i b b', a.op = .test i b ∧ a'.op = .test i b' ∧ b ≠ b'

instance (L : List ARule) : Decidable (ADet L) := by unfold ADet; infer_instance

theorem pushA_det : ∀ d, ADet (pushA d) := by decide
theorem popA_det : ADet popA := by decide
set_option maxRecDepth 20000 in
theorem peekA_det : ADet peekA := by decide

theorem gadA_det (s : Stmt') (v : Option Γ') : ADet (gadA s v) := by
  cases s <;> simp only [gadA]
  · exact pushA_det _
  · exact peekA_det
  · exact popA_det
  all_goals decide

theorem embSrc_inj {s s' : Stmt'} {v v' : Option Γ'} {x x' : Option Phase}
    (h : embSrc s v x = embSrc s' v' x') : s = s' ∧ v = v' ∧ x = x' := by
  cases x <;> cases x' <;> simp_all [embSrc]

theorem mem_gadget {ρ : Quad LState LCtr} {s : Stmt'} {v : Option Γ'} (h : ρ ∈ gadget s v) :
    ∃ a ∈ gadA s v, ρ = emb s v a := by
  rw [gadget_eq] at h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact ⟨a, ha, rfl⟩

/-- The compiled machine is deterministic (Morita's Def 9.2). -/
theorem det_lcm (l₀ : Λ') : (lcm l₀).Det := by
  intro ρ hρ ρ' hρ' hne hsrc
  rcases hρ with rfl | ⟨s, v, hρ⟩ <;> rcases hρ' with rfl | ⟨s', v', hρ'⟩
  · exact absurd rfl hne
  · obtain ⟨a', -, rfl⟩ := mem_gadget hρ'
    rcases h : a'.src <;> simp [emb, embSrc, h] at hsrc
  · obtain ⟨a, -, rfl⟩ := mem_gadget hρ
    rcases h : a.src <;> simp [emb, embSrc, h] at hsrc
  · obtain ⟨a, ha, rfl⟩ := mem_gadget hρ
    obtain ⟨a', ha', rfl⟩ := mem_gadget hρ'
    obtain ⟨rfl, rfl, hsa⟩ := embSrc_inj hsrc
    have hne' : a ≠ a' := fun h => hne (h ▸ rfl)
    obtain ⟨i, b, b', hb, hb', hbb⟩ := gadA_det s v a ha a' ha' hne' hsa
    exact ⟨i.map fun _ => gadK s, b, b', by simp [emb, hb, Op.map], by simp [emb, hb', Op.map], hbb⟩

/-- No rule enters `start`. -/
theorem normalAt_lcm (l₀ : Λ') : (lcm l₀).NormalAt .start := by
  intro ρ hρ hd
  rcases hρ with rfl | ⟨s, v, hρ⟩
  · simp at hd
  · obtain ⟨a, ha, rfl⟩ := mem_gadget hρ
    rcases h : a.dst with ph | r <;> simp only [emb, h, Sum.elim_inl, Sum.elim_inr] at hd
    · cases hd
    · cases s <;> simp [gadA] at ha <;> simp [gadExit] at hd

/-! ## 4. Simulation -/

/-- The counter configuration of a TM2 configuration: a running one sits at the entry of its
label's statement, a halted one at `stmt halt`. -/
def repCfg (c : Cfg') : Cfg LState LCtr :=
  match c with
  | ⟨some l, v, S⟩ => (.stmt (tr l) v, stackVec S)
  | ⟨none, v, S⟩ => (.stmt TM2.Stmt.halt v, stackVec S)

/-- **One statement.**  The gadget of `s` carries `(s, v, S)` to the configuration of
`stepAux s v S`, in at least one step unless the result has halted. -/
theorem stepAux_reaches (l₀ : Λ') (s : Stmt') (v : Option Γ') (S : K' → List Γ') :
    (lcm l₀).Reaches (.stmt s v, stackVec S) (repCfg (TM2.stepAux s v S)) ∧
      ((TM2.stepAux s v S).l.isSome →
        Relation.TransGen (lcm l₀).Step (.stmt s v, stackVec S) (repCfg (TM2.stepAux s v S))) := by
  sorry

/-- A halted TM2 configuration is a halting ID. -/
theorem stuck_halt (l₀ : Λ') (v : Option Γ') (w : LCtr → ℕ) :
    (lcm l₀).Stuck (.stmt TM2.Stmt.halt v, w) := by
  rintro d ⟨ρ, hρ, hs, -, -⟩
  rcases hρ with rfl | ⟨s, v', hρ⟩
  · simp at hs
  · obtain ⟨a, ha, rfl⟩ := mem_gadget hρ
    have : s = TM2.Stmt.halt := by
      rcases h : a.src <;> simp [emb, embSrc, h] at hs
      injection hs with h1; exact h1.symm
    subst this
    simp [gadA] at ha

/-- **Halting matches.**  From `start` with the stacks `S`, the counter machine halts iff the
TM2 run of `tr` from label `l₀`, store `none` and stacks `S` halts. -/
theorem halts_iff_eval (l₀ : Λ') (S : K' → List Γ') :
    (lcm l₀).Halts (.start, stackVec S) ↔
      (StateTransition.eval (TM2.step tr) ⟨some l₀, none, S⟩).Dom := by
  sorry

/-! ## 5. Finiteness and the interface -/

/-- The states of the statements reachable from the label set `L`. -/
def reachSet (L : Finset Λ') : Set LState :=
  {x | x = .start ∨ ∃ s v, some s ∈ TM2.stmts tr L ∧ (x = .stmt s v ∨ ∃ ph, x = .gad s v ph)}

/-- Finitely many states are reachable. -/
theorem reachSet_finite (L : Finset Λ') : (reachSet L).Finite := by
  sorry

/-- The reachable states are closed under the rules when `L` supports `tr` from `l₀`. -/
theorem reachSet_closed {l₀ : Λ'} {L : Finset Λ'} (hL : @TM2.Supports _ _ _ _ ⟨l₀⟩ tr L) :
    ∀ ρ ∈ lcm l₀, ρ.src ∈ reachSet L → ρ.dst ∈ reachSet L := by
  sorry

/-- **The lower half.**  A fixed deterministic counter machine with an undecidable halting
problem: `lcm (trNormal u halt)` restricted to `reachSet (codeSupp u halt)`, input `inputNum`
on the main stack. -/
theorem undecidableCM : UndecidableCM := by
  sorry

end CollatzMoonshot.CounterMachineUniversal
