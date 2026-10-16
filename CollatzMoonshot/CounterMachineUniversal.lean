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

/-- Abstract gadget states: `inl none` the entry, `inl (some ph)` a phase, `inr r` exit `r`. -/
abbrev AState : Type := Option Phase ⊕ Fin 5

/-- The target of an abstract rule as an abstract state. -/
def adst : Phase ⊕ Fin 5 → AState :=
  Sum.elim (fun ph => .inl (some ph)) .inr

/-- The two-counter machine of an abstract rule list. -/
def AM (L : List ARule) : CM AState (Option Unit) :=
  {q | ∃ a ∈ L, q = ⟨.inl a.src, a.op, adst a.dst⟩}

/-- Two counters: `tmp = t`, stack `= n`. -/
def uv (t n : ℕ) : Option Unit → ℕ
  | none => t
  | some _ => n

theorem astep {L : List ARule} (a : ARule) (ha : a ∈ L) {u u' : Option Unit → ℕ}
    (h : a.op.Act u u') : (AM L).Step (.inl a.src, u) (adst a.dst, u') :=
  ⟨_, ⟨a, ha, rfl⟩, rfl, rfl, h⟩

section acts
variable {t n : ℕ}
theorem act_nop {u : Option Unit → ℕ} : (Op.nop : Op (Option Unit)).Act u u := rfl
theorem act_test_tmp0 : (Op.test none false).Act (uv 0 n) (uv 0 n) := ⟨rfl, rfl⟩
theorem act_test_tmp1 : (Op.test none true).Act (uv (t + 1) n) (uv (t + 1) n) :=
  ⟨by simp [uv], rfl⟩
theorem act_test_stk0 : (Op.test (some ()) false).Act (uv t 0) (uv t 0) := ⟨rfl, rfl⟩
theorem act_test_stk1 : (Op.test (some ()) true).Act (uv t (n + 1)) (uv t (n + 1)) :=
  ⟨by simp [uv], rfl⟩
theorem act_dec_tmp : (Op.dec none).Act (uv (t + 1) n) (uv t n) := by
  refine ⟨by simp [uv], rfl, ?_⟩
  rintro (_ | ⟨⟩) h
  · exact absurd rfl h
  · rfl
theorem act_dec_stk : (Op.dec (some ())).Act (uv t (n + 1)) (uv t n) := by
  refine ⟨by simp [uv], rfl, ?_⟩
  rintro (_ | ⟨⟩) h
  · rfl
  · exact absurd rfl h
theorem act_inc_tmp : (Op.inc none).Act (uv t n) (uv (t + 1) n) := by
  refine ⟨rfl, ?_⟩
  rintro (_ | ⟨⟩) h
  · exact absurd rfl h
  · rfl
theorem act_inc_stk : (Op.inc (some ())).Act (uv t n) (uv t (n + 1)) := by
  refine ⟨rfl, ?_⟩
  rintro (_ | ⟨⟩) h
  · rfl
  · exact absurd rfl h
end acts

/-! ### Push -/

theorem pushA_mems (d : Fin 5) :
    ⟨none, .nop, .inl .pa⟩ ∈ pushA d ∧
    ⟨some .pa, .test (some ()) false, .inl .pd⟩ ∈ pushA d ∧
    ⟨some .pa, .test (some ()) true, .inl .pb⟩ ∈ pushA d ∧
    ⟨some .pb, .dec (some ()), .inl .pc⟩ ∈ pushA d ∧
    ⟨some .pc, .inc none, .inl .pa⟩ ∈ pushA d ∧
    ⟨some .pd, .test none false, .inl (.pg 0)⟩ ∈ pushA d ∧
    ⟨some .pd, .test none true, .inl (.pe 0)⟩ ∈ pushA d ∧
    ⟨some (.pe 0), .dec none, .inl (.pe 1)⟩ ∈ pushA d ∧
    ⟨some (.pe 1), .inc (some ()), .inl (.pe 2)⟩ ∈ pushA d ∧
    ⟨some (.pe 2), .inc (some ()), .inl (.pe 3)⟩ ∈ pushA d ∧
    ⟨some (.pe 3), .inc (some ()), .inl (.pe 4)⟩ ∈ pushA d ∧
    ⟨some (.pe 4), .inc (some ()), .inl (.pe 5)⟩ ∈ pushA d ∧
    ⟨some (.pe 5), .inc (some ()), .inl .pd⟩ ∈ pushA d ∧
    ⟨some (.pg d), .nop, .inr 0⟩ ∈ pushA d := by
  revert d; decide

theorem pushA_pg : ∀ d j : Fin 5, j.val < d.val →
    ⟨some (.pg j), .inc (some ()), .inl (.pg (j + 1))⟩ ∈ pushA d := by
  decide

theorem push_move (d : Fin 5) (n t : ℕ) :
    (AM (pushA d)).Reaches (.inl (some .pa), uv t n) (.inl (some .pd), uv (t + n) 0) := by
  obtain ⟨-, h1, h2, h3, h4, -⟩ := pushA_mems d
  induction n generalizing t with
  | zero => exact .single (astep _ h1 act_test_stk0)
  | succ n ih =>
    refine .head (astep _ h2 act_test_stk1) (.head (astep _ h3 act_dec_stk)
      (.head (astep _ h4 act_inc_tmp) ?_))
    rw [show t + (n + 1) = t + 1 + n by omega]
    exact ih (t + 1)

theorem push_ret (d : Fin 5) (t a : ℕ) :
    (AM (pushA d)).Reaches (.inl (some .pd), uv t a) (.inl (some (.pg 0)), uv 0 (a + 5 * t)) := by
  obtain ⟨-, -, -, -, -, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := pushA_mems d
  induction t generalizing a with
  | zero => exact .single (astep _ h5 act_test_tmp0)
  | succ t ih =>
    refine .head (astep _ h6 act_test_tmp1) (.head (astep _ h7 act_dec_tmp)
      (.head (astep _ h8 act_inc_stk) (.head (astep _ h9 act_inc_stk)
      (.head (astep _ h10 act_inc_stk) (.head (astep _ h11 act_inc_stk)
      (.head (astep _ h12 act_inc_stk) ?_))))))
    rw [show a + 5 * (t + 1) = a + 1 + 1 + 1 + 1 + 1 + 5 * t by omega]
    exact ih _

theorem push_digit (d : Fin 5) (a : ℕ) : ∀ m (j : Fin 5), j.val + m = d.val →
    (AM (pushA d)).Reaches (.inl (some (.pg j)), uv 0 a) (.inl (some (.pg d)), uv 0 (a + m)) := by
  intro m
  induction m generalizing a with
  | zero =>
    intro j hj
    obtain rfl : j = d := Fin.ext (by omega)
    exact .refl
  | succ m ih =>
    intro j hj
    refine .head (astep _ (pushA_pg d j (by omega)) act_inc_stk) ?_
    rw [show a + (m + 1) = a + 1 + m by omega]
    exact ih (a + 1) (j + 1) (by rw [Fin.val_add_one_of_lt (by
      rw [Fin.lt_def]; simp; omega)]; omega)

theorem push_run (d : Fin 5) (n : ℕ) :
    Relation.TransGen (AM (pushA d)).Step (.inl none, uv 0 n) (.inr 0, uv 0 (5 * n + d)) := by
  obtain ⟨h0, -, -, -, -, -, -, -, -, -, -, -, -, h13⟩ := pushA_mems d
  have h1 := push_move d n 0
  rw [Nat.zero_add] at h1
  have h2 := push_digit d (0 + 5 * n) d.val 0 (by simp)
  rw [show 0 + 5 * n + d.val = 5 * n + d by omega] at h2
  exact Relation.TransGen.head' (astep _ h0 act_nop)
    (((h1.trans (push_ret d n 0)).trans h2).tail (astep _ h13 act_nop))

/-! ### Pop and peek -/

theorem divA_mems :
    (∀ j : Fin 5, ⟨some (.da j), .test (some ()) false, .inl (.db j)⟩ ∈ divA ∧
      ⟨some (.da j), .test (some ()) true, .inl (.dc j)⟩ ∈ divA) ∧
    (∀ j : Fin 5, j.val < 4 → ⟨some (.dc j), .dec (some ()), .inl (.da (j + 1))⟩ ∈ divA) ∧
    ⟨some (.dc 4), .dec (some ()), .inl .dd⟩ ∈ divA ∧
    ⟨some .dd, .inc none, .inl (.da 0)⟩ ∈ divA := by
  decide

/-- The remainder as a phase index. -/
def rem5 (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by norm_num)⟩

theorem div_loop {L : List ARule} (hL : ∀ a ∈ divA, a ∈ L) (n : ℕ) :
    ∀ (j : Fin 5) (t : ℕ), (AM L).Reaches (.inl (some (.da j)), uv t n)
      (.inl (some (.db (rem5 (j.val + n)))), uv (t + (j.val + n) / 5) 0) := by
  obtain ⟨hda, hdc, hdc4, hdd⟩ := divA_mems
  induction n with
  | zero =>
    intro j t
    have h1 : rem5 (j.val + 0) = j := Fin.ext (by simp [rem5])
    have h2 : t + (j.val + 0) / 5 = t := by have := j.isLt; omega
    rw [h1, h2]
    exact .single (astep _ (hL _ (hda j).1) act_test_stk0)
  | succ n ih =>
    intro j t
    refine .head (astep _ (hL _ (hda j).2) act_test_stk1) ?_
    by_cases hj : j.val < 4
    · refine .head (astep _ (hL _ (hdc j hj)) act_dec_stk) ?_
      have hv : (j + 1).val = j.val + 1 := Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)
      have := ih (j + 1) t
      rw [hv, show j.val + 1 + n = j.val + (n + 1) by omega] at this
      exact this
    · obtain rfl : j = 4 := Fin.ext (by have := j.isLt; simp; omega)
      refine .head (astep _ (hL _ hdc4) act_dec_stk) (.head (astep _ (hL _ hdd) act_inc_tmp) ?_)
      have := ih 0 (t + 1)
      have h1 : rem5 ((0 : Fin 5).val + n) = rem5 ((4 : Fin 5).val + (n + 1)) :=
        Fin.ext (by simp [rem5]; omega)
      have h2 : t + 1 + ((0 : Fin 5).val + n) / 5 = t + ((4 : Fin 5).val + (n + 1)) / 5 := by
        simp; omega
      rw [h1, h2] at this
      exact this

theorem popA_mems :
    (∀ a ∈ divA, a ∈ popA) ∧ ⟨none, .nop, .inl (.da 0)⟩ ∈ popA ∧
    (∀ r : Fin 5, ⟨some (.db r), .test none true, .inl (.de r)⟩ ∈ popA ∧
      ⟨some (.de r), .dec none, .inl (.df r 5)⟩ ∈ popA ∧
      ⟨some (.df r 5), .inc (some ()), .inl (.db r)⟩ ∈ popA ∧
      ⟨some (.db r), .test none false, .inr r⟩ ∈ popA) := by
  decide

theorem pop_ret (r : Fin 5) (t a : ℕ) :
    (AM popA).Reaches (.inl (some (.db r)), uv t a) (.inl (some (.db r)), uv 0 (a + t)) := by
  obtain ⟨-, -, h⟩ := popA_mems
  obtain ⟨h1, h2, h3, -⟩ := h r
  induction t generalizing a with
  | zero => exact .refl
  | succ t ih =>
    refine .head (astep _ h1 act_test_tmp1) (.head (astep _ h2 act_dec_tmp)
      (.head (astep _ h3 act_inc_stk) ?_))
    rw [show a + (t + 1) = a + 1 + t by omega]
    exact ih _

theorem pop_run (n : ℕ) :
    Relation.TransGen (AM popA).Step (.inl none, uv 0 n) (.inr (rem5 n), uv 0 (n / 5)) := by
  obtain ⟨hd, h0, h⟩ := popA_mems
  have h1 := div_loop hd n 0 0
  simp only [Fin.val_zero, Nat.zero_add] at h1
  have h2 := pop_ret (rem5 n) (n / 5) 0
  rw [Nat.zero_add] at h2
  exact Relation.TransGen.head' (astep _ h0 act_nop)
    ((h1.trans h2).tail (astep _ (h _).2.2.2 act_test_tmp0))

theorem peekA_mems :
    (∀ a ∈ divA, a ∈ peekA) ∧ ⟨none, .nop, .inl (.da 0)⟩ ∈ peekA ∧
    (∀ r : Fin 5, ⟨some (.db r), .test none true, .inl (.de r)⟩ ∈ peekA ∧
      ⟨some (.de r), .dec none, .inl (.df r 1)⟩ ∈ peekA ∧
      ⟨some (.df r 1), .inc (some ()), .inl (.df r 2)⟩ ∈ peekA ∧
      ⟨some (.df r 2), .inc (some ()), .inl (.df r 3)⟩ ∈ peekA ∧
      ⟨some (.df r 3), .inc (some ()), .inl (.df r 4)⟩ ∈ peekA ∧
      ⟨some (.df r 4), .inc (some ()), .inl (.df r 5)⟩ ∈ peekA ∧
      ⟨some (.df r 5), .inc (some ()), .inl (.db r)⟩ ∈ peekA ∧
      ⟨some (.db r), .test none false, .inl (.dg r 0)⟩ ∈ peekA ∧
      ⟨some (.dg r r), .nop, .inr r⟩ ∈ peekA) ∧
    (∀ r j : Fin 5, j.val < r.val →
      ⟨some (.dg r j), .inc (some ()), .inl (.dg r (j + 1))⟩ ∈ peekA) := by
  decide

theorem peek_ret (r : Fin 5) (t a : ℕ) :
    (AM peekA).Reaches (.inl (some (.db r)), uv t a) (.inl (some (.db r)), uv 0 (a + 5 * t)) := by
  obtain ⟨-, -, h, -⟩ := peekA_mems
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h r
  induction t generalizing a with
  | zero => exact .refl
  | succ t ih =>
    refine .head (astep _ h1 act_test_tmp1) (.head (astep _ h2 act_dec_tmp)
      (.head (astep _ h3 act_inc_stk) (.head (astep _ h4 act_inc_stk)
      (.head (astep _ h5 act_inc_stk) (.head (astep _ h6 act_inc_stk)
      (.head (astep _ h7 act_inc_stk) ?_))))))
    rw [show a + 5 * (t + 1) = a + 1 + 1 + 1 + 1 + 1 + 5 * t by omega]
    exact ih _

theorem peek_digit (r : Fin 5) (a : ℕ) : ∀ m (j : Fin 5), j.val + m = r.val →
    (AM peekA).Reaches (.inl (some (.dg r j)), uv 0 a) (.inl (some (.dg r r)), uv 0 (a + m)) := by
  obtain ⟨-, -, -, hg⟩ := peekA_mems
  intro m
  induction m generalizing a with
  | zero =>
    intro j hj
    obtain rfl : j = r := Fin.ext (by omega)
    exact .refl
  | succ m ih =>
    intro j hj
    refine .head (astep _ (hg r j (by omega)) act_inc_stk) ?_
    rw [show a + (m + 1) = a + 1 + m by omega]
    exact ih (a + 1) (j + 1) (by rw [Fin.val_add_one_of_lt (by
      rw [Fin.lt_def]; simp; omega)]; omega)

theorem peek_run (n : ℕ) :
    Relation.TransGen (AM peekA).Step (.inl none, uv 0 n) (.inr (rem5 n), uv 0 n) := by
  obtain ⟨hd, h0, h, -⟩ := peekA_mems
  obtain ⟨-, -, -, -, -, -, -, h8, h9⟩ := h (rem5 n)
  have h1 := div_loop hd n 0 0
  simp only [Fin.val_zero, Nat.zero_add] at h1
  have h2 := peek_ret (rem5 n) (n / 5) 0
  rw [Nat.zero_add] at h2
  have h3 := peek_digit (rem5 n) (5 * (n / 5)) (rem5 n).val 0 (by simp)
  rw [show 5 * (n / 5) + (rem5 n).val = n by simp [rem5]; omega] at h3
  exact Relation.TransGen.head' (astep _ h0 act_nop)
    ((((h1.trans h2).tail (astep _ h8 act_test_tmp0)).trans h3).tail (astep _ h9 act_nop))

theorem one_run (u : Option Unit → ℕ) :
    Relation.TransGen (AM [⟨none, .nop, .inr 0⟩]).Step (.inl none, u) (.inr 0, u) :=
  .single (astep _ (List.mem_singleton_self _) act_nop)

/-! ### Transfer to the compiled machine -/

/-- Write the two abstract counters into stack `k` and `tmp` of `w`. -/
def put (k : K') (w : LCtr → ℕ) (u : Option Unit → ℕ) : LCtr → ℕ
  | none => u none
  | some k' => if k' = k then u (some ()) else w (some k')

theorem put_map (k : K') (w : LCtr → ℕ) (u : Option Unit → ℕ) (i : Option Unit) :
    put k w u (i.map fun _ => k) = u i := by
  rcases i with _ | ⟨⟩
  · rfl
  · simp [put]

theorem put_frame (k : K') (w : LCtr → ℕ) {u u' : Option Unit → ℕ} {i : Option Unit}
    (h : ∀ j, j ≠ i → u' j = u j) :
    ∀ j, j ≠ i.map (fun _ => k) → put k w u' j = put k w u j := by
  rintro (_ | k') hj
  · rcases i with _ | ⟨⟩
    · exact absurd rfl hj
    · exact h none (by simp)
  · simp only [put]
    split_ifs with hk
    · subst hk
      rcases i with _ | ⟨⟩
      · exact h (some ()) (by simp)
      · exact absurd rfl hj
    · rfl

theorem act_map_put {o : Op (Option Unit)} (k : K') (w : LCtr → ℕ) {u u' : Option Unit → ℕ}
    (h : o.Act u u') : (o.map (Option.map fun _ => k)).Act (put k w u) (put k w u') := by
  cases o with
  | test i b =>
    obtain ⟨hb, rfl⟩ := h
    exact ⟨by rw [put_map]; exact hb, rfl⟩
  | dec i =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rw [put_map]; exact h1, by rw [put_map, put_map]; exact h2, put_frame k w h3⟩
  | inc i =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [put_map, put_map]; exact h1, put_frame k w h2⟩
  | nop =>
    cases h; rfl

/-- The real state of an abstract state. -/
def embState (s : Stmt') (v : Option Γ') : AState → LState :=
  Sum.elim (embSrc s v) (gadExit s v)

theorem am_step (l₀ : Λ') {s : Stmt'} {v : Option Γ'} (w : LCtr → ℕ)
    {c d : AState × (Option Unit → ℕ)} (h : (AM (gadA s v)).Step c d) :
    (lcm l₀).Step (embState s v c.1, put (gadK s) w c.2)
      (embState s v d.1, put (gadK s) w d.2) := by
  obtain ⟨ρ, ⟨⟨src, op, dst⟩, ha, rfl⟩, hs, hd, hact⟩ := h
  refine ⟨emb s v ⟨src, op, dst⟩, Or.inr ⟨s, v, ?_⟩, ?_, ?_, act_map_put _ w hact⟩
  · rw [gadget_eq]; exact List.mem_map_of_mem ha
  · rw [hs]; rfl
  · rw [hd]; cases dst <;> rfl

theorem real_run (l₀ : Λ') {s : Stmt'} {v : Option Γ'} {u u' : Option Unit → ℕ} {r : Fin 5}
    (h : Relation.TransGen (AM (gadA s v)).Step (.inl none, u) (.inr r, u')) (w : LCtr → ℕ) :
    Relation.TransGen (lcm l₀).Step (.stmt s v, put (gadK s) w u)
      (gadExit s v r, put (gadK s) w u') :=
  h.lift (fun c => (embState s v c.1, put (gadK s) w c.2)) fun _ _ h => am_step l₀ w h

theorem put_stackVec (k : K') (S : K' → List Γ') (l : List Γ') :
    put k (stackVec S) (uv 0 (num l)) = stackVec (Function.update S k l) := by
  funext i
  rcases i with _ | k'
  · rfl
  · simp only [put, stackVec, uv, Function.update]
    split_ifs with hk
    · subst hk; rfl
    · rfl

theorem put_self (k : K') (S : K' → List Γ') :
    put k (stackVec S) (uv 0 (num (S k))) = stackVec S := by
  rw [put_stackVec, Function.update_eq_self]

theorem chain {l₀ : Λ'} {c d e : Cfg LState LCtr} (h : Relation.TransGen (lcm l₀).Step c d)
    (h' : (lcm l₀).Reaches d e) :
    (lcm l₀).Reaches c e ∧ Relation.TransGen (lcm l₀).Step c e :=
  ⟨h.to_reflTransGen.trans h', h.trans_left h'⟩

theorem one_real (l₀ : Λ') {s : Stmt'} {v : Option Γ'} (S : K' → List Γ')
    (hs : gadA s v = [⟨none, .nop, .inr 0⟩]) :
    Relation.TransGen (lcm l₀).Step (.stmt s v, stackVec S) (gadExit s v 0, stackVec S) := by
  have h := real_run l₀ (s := s) (v := v) (hs ▸ one_run (uv 0 (num (S (gadK s))))) (stackVec S)
  rwa [put_self] at h

/-- **One statement.**  The gadget of `s` carries `(s, v, S)` to the configuration of
`stepAux s v S`, in at least one step unless the result has halted. -/
theorem stepAux_reaches (l₀ : Λ') (s : Stmt') (v : Option Γ') (S : K' → List Γ') :
    (lcm l₀).Reaches (.stmt s v, stackVec S) (repCfg (TM2.stepAux s v S)) ∧
      ((TM2.stepAux s v S).l.isSome →
        Relation.TransGen (lcm l₀).Step (.stmt s v, stackVec S) (repCfg (TM2.stepAux s v S))) := by
  induction s generalizing v S with
  | push k f q ih =>
    have h := real_run l₀ (s := TM2.Stmt.push k f q) (v := v)
      (push_run (digitF (f v)) (num (S k))) (stackVec S)
    simp only [gadK, gadExit] at h
    rw [put_self, show 5 * num (S k) + ((digitF (f v) : Fin 5) : ℕ) = num (f v :: S k) by
      rw [num_cons]; rfl, put_stackVec] at h
    have := chain h (ih v _).1
    exact ⟨this.1, fun _ => this.2⟩
  | peek k f q ih =>
    have h := real_run l₀ (s := TM2.Stmt.peek k f q) (v := v) (peek_run (num (S k))) (stackVec S)
    simp only [gadK, gadExit] at h
    rw [put_self, show undigit (rem5 (num (S k))) = (S k).head? from undigit_num _] at h
    have := chain h (ih _ S).1
    exact ⟨this.1, fun _ => this.2⟩
  | pop k f q ih =>
    have h := real_run l₀ (s := TM2.Stmt.pop k f q) (v := v) (pop_run (num (S k))) (stackVec S)
    simp only [gadK, gadExit] at h
    rw [put_self, show undigit (rem5 (num (S k))) = (S k).head? from undigit_num _,
      num_div_five, put_stackVec] at h
    have := chain h (ih _ _).1
    exact ⟨this.1, fun _ => this.2⟩
  | load a q ih =>
    have := chain (one_real l₀ (s := TM2.Stmt.load a q) (v := v) S rfl) (ih _ S).1
    exact ⟨this.1, fun _ => this.2⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
    have h := one_real l₀ (s := TM2.Stmt.branch f q₁ q₂) (v := v) S rfl
    simp only [gadExit] at h
    simp only [TM2.stepAux]
    cases hf : f v <;> rw [hf] at h <;> simp only [cond_false, cond_true] at h ⊢
    · have := chain h (ih₂ v S).1
      exact ⟨this.1, fun _ => this.2⟩
    · have := chain h (ih₁ v S).1
      exact ⟨this.1, fun _ => this.2⟩
  | goto f =>
    have h := one_real l₀ (s := TM2.Stmt.goto f) (v := v) S rfl
    exact ⟨h.to_reflTransGen, fun _ => h⟩
  | halt => exact ⟨.refl, by simp [TM2.stepAux]⟩

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

theorem start_step (l₀ : Λ') (w : LCtr → ℕ) :
    (lcm l₀).Step (.start, w) (.stmt (tr l₀) none, w) :=
  ⟨_, Or.inl rfl, rfl, rfl, rfl⟩

/-- One TM2 step is a counter run between the representing configurations. -/
theorem tm2_step_reaches (l₀ : Λ') {a b : Cfg'} (h : b ∈ TM2.step tr a) :
    (lcm l₀).Reaches (repCfg a) (repCfg b) := by
  obtain ⟨_ | l, v, S⟩ := a
  · cases h
  · cases h
    exact (stepAux_reaches l₀ (tr l) v S).1

/-- **Halting matches.**  From `start` with the stacks `S`, the counter machine halts iff the
TM2 run of `tr` from label `l₀`, store `none` and stacks `S` halts. -/
theorem halts_iff_eval (l₀ : Λ') (S : K' → List Γ') :
    (lcm l₀).Halts (.start, stackVec S) ↔
      (StateTransition.eval (TM2.step tr) ⟨some l₀, none, S⟩).Dom := by
  constructor
  · rintro ⟨d, hr, hd⟩
    obtain ⟨n, hn⟩ := CM.StepsN.of_reaches hr
    obtain ⟨m, -, hm⟩ :=
      CM.StepsN.of_transGen (det_lcm l₀) hd (.single (start_step l₀ (stackVec S))) hn
    clear hr hn
    have key : ∀ m (a : Cfg'), (lcm l₀).StepsN m (repCfg a) d →
        (StateTransition.eval (TM2.step tr) a).Dom := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        rintro ⟨_ | l, v, S⟩ ha
        · exact Part.dom_iff_mem.2 ⟨_, StateTransition.mem_eval.2 ⟨.refl, rfl⟩⟩
        · have hstep : TM2.stepAux (tr l) v S ∈ TM2.step tr ⟨some l, v, S⟩ := rfl
          rw [StateTransition.reaches_eval (Relation.ReflTransGen.single hstep)]
          rcases hl : (TM2.stepAux (tr l) v S).l with _ | l'
          · exact Part.dom_iff_mem.2 ⟨_, StateTransition.mem_eval.2 ⟨.refl, by
              simp only [TM2.step]; rw [show TM2.stepAux (tr l) v S =
                ⟨none, (TM2.stepAux (tr l) v S).var, (TM2.stepAux (tr l) v S).stk⟩ by
                  rw [← hl]]⟩⟩
          · have ht := (stepAux_reaches l₀ (tr l) v S).2 (by simp [hl])
            obtain ⟨m', hm', h'⟩ := CM.StepsN.of_transGen (det_lcm l₀) hd ht ha
            exact ih m' hm' _ h'
    exact key m _ hm
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h
    obtain ⟨hr, hb0⟩ := StateTransition.mem_eval.1 hb
    have hreach : (lcm l₀).Reaches (repCfg ⟨some l₀, none, S⟩) (repCfg b) := by
      clear hb hb0 h
      induction hr with
      | refl => exact .refl
      | tail _ hst ih => exact ih.trans (tm2_step_reaches l₀ hst)
    obtain ⟨_ | l, v, S'⟩ := b
    · exact ⟨_, Relation.ReflTransGen.head (start_step l₀ _) hreach, stuck_halt l₀ v _⟩
    · simp [TM2.step] at hb0

/-! ## 5. Finiteness and the interface -/

/-- The states of the statements reachable from the label set `L`. -/
def reachSet (L : Finset Λ') : Set LState :=
  {x | x = .start ∨ ∃ s v, some s ∈ TM2.stmts tr L ∧ (x = .stmt s v ∨ ∃ ph, x = .gad s v ph)}

/-- Finitely many states are reachable. -/
theorem reachSet_finite (L : Finset Λ') : (reachSet L).Finite := by
  classical
  have hT : {s : Stmt' | some s ∈ TM2.stmts tr L}.Finite :=
    (TM2.stmts tr L).finite_toSet.preimage (Option.some_injective _).injOn
  have h1 := (hT.prod (Set.finite_univ (α := Option Γ'))).image fun p => LState.stmt p.1 p.2
  have h2 := (hT.prod ((Set.finite_univ (α := Option Γ')).prod
    (Set.finite_univ (α := Phase)))).image fun p => LState.gad p.1 p.2.1 p.2.2
  refine (((Set.finite_singleton LState.start).union h1).union h2).subset ?_
  rintro x (rfl | ⟨s, v, hs, rfl | ⟨ph, rfl⟩⟩)
  · simp
  · exact Or.inl (Or.inr ⟨(s, v), ⟨hs, trivial⟩, rfl⟩)
  · exact Or.inr ⟨(s, v, ph), ⟨hs, trivial, trivial⟩, rfl⟩

/-- A label in `L` has its statement in `stmts`. -/
theorem tr_mem_stmts {L : Finset Λ'} {l : Λ'} (hl : l ∈ L) : some (tr l) ∈ TM2.stmts tr L := by
  classical
  refine Finset.mem_insertNone.2 ?_
  rintro a ⟨⟩
  exact Finset.mem_biUnion.2 ⟨l, hl, TM2.stmts₁_self⟩

/-- The reachable states are closed under the rules when `L` supports `tr` from `l₀`. -/
theorem reachSet_closed {l₀ : Λ'} {L : Finset Λ'} (hL : @TM2.Supports _ _ _ _ ⟨l₀⟩ tr L) :
    ∀ ρ ∈ lcm l₀, ρ.src ∈ reachSet L → ρ.dst ∈ reachSet L := by
  classical
  rintro ρ (rfl | ⟨s, v, hρ⟩) hsrc
  · exact Or.inr ⟨_, none, tr_mem_stmts hL.1, Or.inl rfl⟩
  · obtain ⟨⟨src, op, dst⟩, ha, rfl⟩ := mem_gadget hρ
    have hs : some s ∈ TM2.stmts tr L := by
      rcases hsrc with h | ⟨s', v', hs', h | ⟨ph, h⟩⟩
      · cases src <;> simp [emb, embSrc] at h
      · cases src <;> simp [emb, embSrc] at h
        injection h with h1; exact h1 ▸ hs'
      · cases src <;> simp [emb, embSrc] at h
        injection h with h1; exact h1 ▸ hs'
    rcases dst with ph | r
    · exact Or.inr ⟨s, v, hs, Or.inr ⟨ph, rfl⟩⟩
    · show gadExit s v r ∈ reachSet L
      have sub : ∀ {q : Stmt'}, q ∈ TM2.stmts₁ s → ∀ v', LState.stmt q v' ∈ reachSet L :=
        fun h v' => Or.inr ⟨_, v', TM2.stmts_trans h hs, Or.inl rfl⟩
      cases s with
      | push k f q => exact sub (Finset.mem_insert_of_mem TM2.stmts₁_self) _
      | peek k f q => exact sub (Finset.mem_insert_of_mem TM2.stmts₁_self) _
      | pop k f q => exact sub (Finset.mem_insert_of_mem TM2.stmts₁_self) _
      | load a q => exact sub (Finset.mem_insert_of_mem TM2.stmts₁_self) _
      | branch f q₁ q₂ =>
        simp only [gadExit]
        cases f v
        · exact sub (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self)) _
        · exact sub (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self)) _
      | goto f =>
        let _ : Inhabited Λ' := ⟨l₀⟩
        have := TM2.stmts_supportsStmt hL hs
        exact Or.inr ⟨_, v, tr_mem_stmts (this v), Or.inl rfl⟩
      | halt => simp [gadA] at ha

/-- **The lower half.**  A fixed deterministic counter machine with an undecidable halting
problem: `lcm (trNormal u halt)` restricted to `reachSet (codeSupp u halt)`, input `inputNum`
on the main stack. -/
theorem undecidableCM : UndecidableCM := by
  obtain ⟨u, hu⟩ := exists_universal
  have hL := tr_supports u Cont'.halt
  refine ⟨reachSet (codeSupp u Cont'.halt), LCtr, (reachSet_finite _).to_subtype,
    inferInstance, (lcm (trNormal u Cont'.halt)).restrict (reachSet (codeSupp u Cont'.halt)),
    ⟨.start, Or.inl rfl⟩, some K'.main, inputNum,
    CM.restrict_det (det_lcm _) _, CM.restrict_normalAt (normalAt_lcm _) _ _,
    computable_inputNum, fun hc => not_computable_universal hu (hc.of_eq fun n => ?_)⟩
  refine (CM.halts_restrict (reachSet_closed hL) (q := LState.start) (Or.inl rfl) _).trans ?_
  have key : (lcm (trNormal u Cont'.halt)).Halts (.start, stackVec (K'.elim (trList [n]) [] [] []))
      ↔ (u.eval [n]).Dom := by
    rw [halts_iff_eval]
    have := tr_eval u [n]
    simp only [init] at this
    rw [this]
    simp
  convert key using 4
  rw [stackVec_init]
  congr
  exact Subsingleton.elim _ _

end CollatzMoonshot.CounterMachineUniversal
