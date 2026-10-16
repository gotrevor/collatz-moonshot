/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaEngineGen
import CollatzMoonshot.RcwaMachine

/-!
# Theorem C on `ℤ`, assembled: same-orbit for `{2,3}`-slope RCWA permutations encodes halting

A reversible 2-counter machine `M` with `K` states is run inside `ℤ` by Lemma P at level `j`
(`RcwaEngineGen`, phases mod `5^j`, `K ≤ orderOf (3 : ZMod (5^j))`), and the completion of
`RcwaMachine` closes the resulting partial injection into a permutation `σ` of `ℤ` with all slopes
in `2^ℤ 3^ℤ`.  A source configuration `c` and the next highway point after its encoding lie on one
`σ`-orbit iff the run of `M` from `c` halts.  So same-orbit is undecidable on these permutations,
given undecidability of halting for the machines.

1. **RCWA.**  `IsRcwa23At M σ`: on each class mod `M`, `c · σ n = a n + b` with
   `a / c ∈ 2^ℤ 3^ℤ`.  `RcwaTable` is the finite data, `RcwaTable.eval` the map it describes, and
   `tableFrom f M` reads the table of `f` off two values per class (`tableFrom_spec`).
2. **Machines.**  Guarded rules `(src, t₁, t₂, d₁, d₂, dst)` on `ℕ × ℕ × ℕ` (state, counters): a
   zero test `= 0`, `≥ 1` or none on each counter and a move in `{-1, 0, 1}` on each counter.
   Determinism and reversibility are semantic, on *all* configurations (the guarded counter
   machines of Kari–Ollinger 2008 with guards `{0}`, `[1, ∞)`, `ℕ`).  Morita's (1996) quadruples
   are the rules with one test and no move, or one move and no test.  A `Machine` is `K`, a rule
   list with states `< K`, and a list `pair` permuting `0, …, K − 1` (the sink-to-source
   relabelling of the completion).  `step` fires the first rule that applies.
3. **Bridge.**  `F j R`: on the engine, the first rule firing on `decode j n` is applied as the
   Lemma P piece `move j n dst d₁ d₂` (`F_eq_some_iff`: conjugacy with `step`, junk fixed;
   `move_slope`: slope in `2^ℤ 3^ℤ`).
4. **Assembly.**  The *line* is the non-engine set together with the engine sources; a *highway*
   is a finite list of disjoint residue classes, all moduli `5^j · 2^α 3^β`, covering the line, and
   `hwNext` steps along it.  `sigma` is `F` where it is defined, `hwNext ∘ τ` on engine sinks
   (`τ` multiplies by `3^{pair s − s}`), and `hwNext` off the engine.  `sigma_bijective`,
   `isRcwa23At_sigma`, and the headline `sameCycle_hwNext_iff` under (H1) no bi-infinite run and
   (H2) every finite run from a source ends at a sink paired back to it.
5. **Undecidability.**  `highwayOf`, `tableOf` (computable data, `computable_reduction`), the
   literature input `HaltingUndecidable`, and `not_computable_sameCycle`.
-/

namespace CollatzMoonshot.RcwaSameOrbit

open CollatzMoonshot.RcwaEngineGen

/-! ## 1. RCWA maps with slopes in `2^ℤ 3^ℤ` -/

/-- On each class `r` mod `M`, `c · σ n = a · n + b` exactly, with `c ≠ 0` and
`a / c = 2^i 3^j`. -/
def IsRcwa23At (M : ℕ) (σ : ℤ → ℤ) : Prop :=
  ∀ r : ℤ, ∃ a b c : ℤ, c ≠ 0 ∧ (∃ i j : ℤ, (a : ℚ) / c = (2 : ℚ) ^ i * (3 : ℚ) ^ j) ∧
    ∀ n, n ≡ r [ZMOD M] → c * σ n = a * n + b

/-- `σ` is residue-class-wise affine with all slopes in `2^ℤ 3^ℤ`, for some modulus `M > 0`. -/
def IsRcwa23 (σ : ℤ → ℤ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ IsRcwa23At M σ

/-- Finite RCWA data: a modulus and one triple `(a, b, c)` per class `0, …, modulus − 1`. -/
structure RcwaTable where
  /-- The modulus. -/
  modulus : ℕ
  /-- The triple `(a, b, c)` for class `k`, meaning `n ↦ (a n + b) / c`, at index `k`. -/
  pieces : List (ℤ × ℤ × ℤ)

namespace RcwaTable

/-- The triple used at `n` (the identity triple if the index is out of range). -/
def piece (T : RcwaTable) (n : ℤ) : ℤ × ℤ × ℤ :=
  T.pieces.getD (n % (T.modulus : ℤ)).toNat (1, 0, 1)

/-- The map a table describes: `n ↦ (a n + b) / c` with the triple of `n`'s class. -/
def eval (T : RcwaTable) (n : ℤ) : ℤ :=
  ((T.piece n).1 * n + (T.piece n).2.1) / (T.piece n).2.2

/-- A table is *exact* when it has one piece per class, every slope lies in `2^ℤ 3^ℤ`, and every
division is exact. -/
structure Exact (T : RcwaTable) : Prop where
  pos : 0 < T.modulus
  length : T.pieces.length = T.modulus
  slope : ∀ p ∈ T.pieces, p.2.2 ≠ 0 ∧ ∃ i j : ℤ, (p.1 : ℚ) / p.2.2 = (2 : ℚ) ^ i * (3 : ℚ) ^ j
  dvd : ∀ n, (T.piece n).2.2 ∣ (T.piece n).1 * n + (T.piece n).2.1

/-- The piece at `n` of an exact table is one of its pieces. -/
theorem piece_mem {T : RcwaTable} (hT : T.Exact) (n : ℤ) : T.piece n ∈ T.pieces := by
  have hM : (0 : ℤ) < T.modulus := by exact_mod_cast hT.pos
  have hlt : (n % (T.modulus : ℤ)).toNat < T.pieces.length := by
    rw [hT.length]
    have := Int.emod_lt_of_pos n hM
    have := Int.emod_nonneg n hM.ne'
    omega
  rw [piece, List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

/-- An exact table evaluates to an `IsRcwa23` map. -/
theorem isRcwa23_eval {T : RcwaTable} (hT : T.Exact) : IsRcwa23 T.eval := by
  refine ⟨T.modulus, hT.pos, fun r => ?_⟩
  obtain ⟨hc, hs⟩ := hT.slope _ (piece_mem hT r)
  refine ⟨(T.piece r).1, (T.piece r).2.1, (T.piece r).2.2, hc, hs, fun n hn => ?_⟩
  have hp : T.piece n = T.piece r := by
    rw [piece, piece, show n % (T.modulus : ℤ) = r % T.modulus from hn]
  rw [eval, ← hp]
  exact Int.mul_ediv_cancel' (hT.dvd n)

end RcwaTable

/-- The table of `f` with modulus `M`, read off `f r` and `f (r + M)` for each class `r`: the
slope is `q = (f (r + M) − f r) / M` and the triple is `(q.num, q.den · f r − q.num · r, q.den)`. -/
def tableFrom (f : ℤ → ℤ) (M : ℕ) : RcwaTable where
  modulus := M
  pieces := (List.range M).map fun k =>
    let q : ℚ := ((f (k + M) - f k : ℤ) : ℚ) / M
    (q.num, (q.den : ℤ) * f k - q.num * k, (q.den : ℤ))

/-- The slope `tableFrom` reads off class `k`. -/
def tableSlope (f : ℤ → ℤ) (M : ℕ) (k : ℤ) : ℚ :=
  ((f (k + M) - f k : ℤ) : ℚ) / M

/-- The triple `tableFrom` stores for class `k`. -/
def tableRow (f : ℤ → ℤ) (M : ℕ) (k : ℤ) : ℤ × ℤ × ℤ :=
  ((tableSlope f M k).num, ((tableSlope f M k).den : ℤ) * f k - (tableSlope f M k).num * k,
    ((tableSlope f M k).den : ℤ))

theorem tableFrom_length (f : ℤ → ℤ) (M : ℕ) : (tableFrom f M).pieces.length = M := by
  simp [tableFrom]

theorem tableFrom_getElem (f : ℤ → ℤ) (M k : ℕ) (hk : k < (tableFrom f M).pieces.length) :
    (tableFrom f M).pieces[k] = tableRow f M k := by
  have hL : List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range M) =
      (List.range M).map (fun a : ℕ => (a : ℤ)) := List.map_eq_flatMap.symm
  simp [tableFrom, hL, tableRow, tableSlope]

theorem tableFrom_mem {f : ℤ → ℤ} {M : ℕ} {p : ℤ × ℤ × ℤ} (hp : p ∈ (tableFrom f M).pieces) :
    ∃ k : ℕ, p = tableRow f M k := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact ⟨k, tableFrom_getElem f M k hk⟩

theorem tableFrom_piece {f : ℤ → ℤ} {M : ℕ} (hM : 0 < M) (n : ℤ) :
    (tableFrom f M).piece n = tableRow f M (n % M) := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have h0 := Int.emod_nonneg n hM'.ne'
  have hlt : (n % (M : ℤ)).toNat < (tableFrom f M).pieces.length := by
    rw [tableFrom_length]
    have := Int.emod_lt_of_pos n hM'
    omega
  unfold RcwaTable.piece
  rw [show (tableFrom f M).modulus = M from rfl, List.getD_eq_getElem _ _ hlt,
    tableFrom_getElem, Int.toNat_of_nonneg h0]

/-- On the class of `k`, the row read off at `k` is exact: `den · f n = num · n + b`, and the
slope is in `2^ℤ 3^ℤ`. -/
theorem tableRow_spec {f : ℤ → ℤ} {M : ℕ} (hM : 0 < M) (hf : IsRcwa23At M f) (k n : ℤ)
    (hn : n ≡ k [ZMOD M]) :
    (tableRow f M k).2.2 * f n = (tableRow f M k).1 * n + (tableRow f M k).2.1 ∧
      ∃ i j : ℤ, tableSlope f M k = (2 : ℚ) ^ i * (3 : ℚ) ^ j := by
  set q : ℚ := tableSlope f M k with hqdef
  obtain ⟨a, b, c, hc, ⟨i, j, hij⟩, h⟩ := hf k
  have hk := h k (Int.ModEq.refl k)
  have hkM := h (k + M) (by simp [Int.ModEq])
  have hnn := h n hn
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hq : q = a / c := by
    rw [hqdef, tableSlope, div_eq_div_iff hMq hcq]
    have : (f (k + M) - f k) * c = a * M := by linear_combination hkM - hk
    exact_mod_cast this
  refine ⟨?_, i, j, hq ▸ hij⟩
  have hnum : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
  have hfn : (c : ℚ) * (f n - f k) = a * (n - k) := by
    have : c * (f n - f k) = a * (n - k) := by linear_combination hnn - hk
    exact_mod_cast this
  have key : ∀ d : ℚ, d * f n = q * d * n + (d * f k - q * d * k) := by
    intro d; rw [hq]; field_simp; linear_combination d * hfn
  have key' := key q.den
  rw [← hnum] at key'
  simp only [tableRow, ← hqdef]
  exact_mod_cast key'

/-- If `f` is RCWA with slopes in `2^ℤ 3^ℤ` at modulus `M > 0`, `tableFrom f M` is
an exact table for `f`. -/
theorem tableFrom_spec {f : ℤ → ℤ} {M : ℕ} (hM : 0 < M) (hf : IsRcwa23At M f) :
    (tableFrom f M).Exact ∧ (tableFrom f M).eval = f := by
  have hkey : ∀ n : ℤ, _ := fun n =>
    tableRow_spec hM hf (n % M) n (Int.mod_modEq n M).symm
  have hden : ∀ k, (tableRow f M k).2.2 ≠ 0 := fun k => by
    simp only [tableRow]; exact_mod_cast (Rat.den_pos _).ne'
  have hev : ∀ n, (tableFrom f M).eval n = f n := by
    intro n
    rw [RcwaTable.eval, tableFrom_piece hM, ← (hkey n).1]
    exact Int.mul_ediv_cancel_left _ (hden _)
  refine ⟨⟨hM, tableFrom_length f M, ?_, fun n => ?_⟩, funext hev⟩
  · intro p hp
    obtain ⟨k, rfl⟩ := tableFrom_mem hp
    refine ⟨hden k, ?_⟩
    obtain ⟨i, j, hij⟩ := (tableRow_spec hM hf (k : ℤ) k (Int.ModEq.refl _)).2
    refine ⟨i, j, ?_⟩
    simp only [tableRow]
    rw [Int.cast_natCast, Rat.num_div_den]
    exact hij
  · rw [tableFrom_piece hM, ← (hkey n).1]
    exact dvd_mul_right _ _

/-! ## 2. Reversible 2-counter machines -/

/-- A zero test on one counter: `= 0`, `≥ 1`, or none. -/
inductive Test
  | zero
  | pos
  | any
  deriving DecidableEq

/-- The test as a Boolean. -/
def Test.ok : Test → ℕ → Bool
  | .zero, c => c == 0
  | .pos, c => 1 ≤ c
  | .any, _ => true

/-- A move on one counter: `-1`, `0` or `+1`. -/
inductive Move
  | minus
  | zero
  | plus
  deriving DecidableEq

/-- The move as an integer. -/
def Move.val : Move → ℤ
  | .minus => -1
  | .zero => 0
  | .plus => 1

/-- A configuration: a state and two counters. -/
abbrev Cfg : Type := ℕ × ℕ × ℕ

/-- A guarded rule: from `src`, if both tests pass, add `(d₁, d₂)` and go to `dst`. -/
structure Rule where
  /-- The state the rule leaves. -/
  src : ℕ
  /-- The test on counter 1. -/
  t₁ : Test
  /-- The test on counter 2. -/
  t₂ : Test
  /-- The move on counter 1. -/
  d₁ : Move
  /-- The move on counter 2. -/
  d₂ : Move
  /-- The state the rule enters. -/
  dst : ℕ
  deriving DecidableEq

namespace Rule

/-- `ρ` applies at `c`: the state matches, both tests pass, and both counters stay `≥ 0`. -/
def Fires (ρ : Rule) (c : Cfg) : Prop :=
  c.1 = ρ.src ∧ ρ.t₁.ok c.2.1 = true ∧ ρ.t₂.ok c.2.2 = true ∧
    0 ≤ (c.2.1 : ℤ) + ρ.d₁.val ∧ 0 ≤ (c.2.2 : ℤ) + ρ.d₂.val

instance (ρ : Rule) : DecidablePred ρ.Fires := fun c => by
  unfold Fires; infer_instance

/-- The configuration `ρ` produces from `c`. -/
def target (ρ : Rule) (c : Cfg) : Cfg :=
  (ρ.dst, ((c.2.1 : ℤ) + ρ.d₁.val).toNat, ((c.2.2 : ℤ) + ρ.d₂.val).toNat)

end Rule

/-- One step: the first rule of `R` that fires. -/
def step (R : List Rule) (c : Cfg) : Option Cfg :=
  (R.find? fun ρ => decide (ρ.Fires c)).map fun ρ => ρ.target c

/-- Two rules that fire at one configuration produce the same configuration. -/
def Deterministic (R : List Rule) : Prop :=
  ∀ ρ ∈ R, ∀ ρ' ∈ R, ∀ c, ρ.Fires c → ρ'.Fires c → ρ.target c = ρ'.target c

/-- Two rule firings with the same result start from the same configuration (on *all*
configurations, reachable or not). -/
def Reversible (R : List Rule) : Prop :=
  ∀ ρ ∈ R, ∀ ρ' ∈ R, ∀ c c', ρ.Fires c → ρ'.Fires c' → ρ.target c = ρ'.target c' → c = c'

/-- The `n`-step run from `c` (`none` once it has halted). -/
def run (R : List Rule) (n : ℕ) (c : Cfg) : Option Cfg :=
  (fun o : Option Cfg => o.bind (step R))^[n] (some c)

/-- `c` has no predecessor. -/
def IsSource (R : List Rule) (c : Cfg) : Prop :=
  ∀ c', step R c' ≠ some c

/-- `c` has no successor. -/
def IsSink (R : List Rule) (c : Cfg) : Prop :=
  step R c = none

/-- The run from `c` halts: it reaches a sink. -/
def Halts (R : List Rule) (c : Cfg) : Prop :=
  ∃ n d, run R n c = some d ∧ IsSink R d

/-- **(H1)** No bi-infinite run (in particular no cycle), from any configuration. -/
def NoBiInfinite (R : List Rule) : Prop :=
  ∀ g : ℤ → Cfg, ¬ ∀ i, step R (g i) = some (g (i + 1))

/-- **(H2)** A finite run from a source ends at a sink whose `pair`-relabelling is the source. -/
def EndToStart (R : List Rule) (pair : ℕ → ℕ) : Prop :=
  ∀ c d n, IsSource R c → run R n c = some d → IsSink R d → (pair d.1, d.2) = c

/-- The source test as a Boolean: no rule produces `c` from its candidate predecessor. -/
def isSourceB (R : List Rule) (c : Cfg) : Bool :=
  R.all fun ρ =>
    !(decide (ρ.dst = c.1 ∧ 0 ≤ (c.2.1 : ℤ) - ρ.d₁.val ∧ 0 ≤ (c.2.2 : ℤ) - ρ.d₂.val) &&
      decide (step R (ρ.src, ((c.2.1 : ℤ) - ρ.d₁.val).toNat, ((c.2.2 : ℤ) - ρ.d₂.val).toNat) =
        some c))

/-- A step is the target of some firing rule. -/
theorem exists_rule_of_step {R : List Rule} {c d : Cfg} (h : step R c = some d) :
    ∃ ρ ∈ R, ρ.Fires c ∧ ρ.target c = d := by
  simp only [step, Option.map_eq_some_iff] at h
  obtain ⟨ρ, hρ, rfl⟩ := h
  exact ⟨ρ, List.mem_of_find?_eq_some hρ, by simpa using List.find?_some hρ, rfl⟩

/-- The Boolean source test is correct. -/
theorem isSourceB_iff (R : List Rule) (c : Cfg) : isSourceB R c = true ↔ IsSource R c := by
  rw [isSourceB, List.all_eq_true]
  constructor
  · intro h c' hc'
    obtain ⟨ρ, hρ, hf, rfl⟩ := exists_rule_of_step hc'
    have := h ρ hρ
    obtain ⟨hs, -, -, h3, h4⟩ := hf
    have hA : ρ.dst = (ρ.target c').1 ∧ 0 ≤ ((ρ.target c').2.1 : ℤ) - ρ.d₁.val ∧
        0 ≤ ((ρ.target c').2.2 : ℤ) - ρ.d₂.val := by
      simp only [Rule.target, Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4]
      exact ⟨trivial, by omega, by omega⟩
    have hpre : ((ρ.src, (((ρ.target c').2.1 : ℤ) - ρ.d₁.val).toNat,
        (((ρ.target c').2.2 : ℤ) - ρ.d₂.val).toNat) : Cfg) = c' := by
      obtain ⟨c0, c1, c2⟩ := c'
      simp only [Rule.target, Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4] at hs ⊢
      simp [hs]
    have hB : step R (ρ.src, (((ρ.target c').2.1 : ℤ) - ρ.d₁.val).toNat,
        (((ρ.target c').2.2 : ℤ) - ρ.d₂.val).toNat) = some (ρ.target c') := by
      rw [hpre]; exact hc'
    rw [decide_eq_true hA, decide_eq_true hB] at this
    exact absurd this (by decide)
  · intro h ρ hρ
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hc
    push Not at hc
    exact h _ hc.2

/-- A machine: `K` states `0, …, K − 1`, its rules, and the list `pair` (state `s < K` is
relabelled `pair[s]` when a sink returns to the highway). -/
structure Machine where
  /-- The number of states. -/
  K : ℕ
  /-- The rules. -/
  rules : List Rule
  /-- The sink-to-source relabelling, as the list of images of `0, …, K − 1`. -/
  pair : List ℕ

namespace Machine

/-- The relabelling as a function (the identity from `K` on). -/
def pairFn (M : Machine) (s : ℕ) : ℕ :=
  M.pair.getD s s

/-- Well-formed: rules use states `< K`, and `pair` is a permutation of `0, …, K − 1`. -/
structure WF (M : Machine) : Prop where
  src_lt : ∀ ρ ∈ M.rules, ρ.src < M.K
  dst_lt : ∀ ρ ∈ M.rules, ρ.dst < M.K
  pair_perm : M.pair.Perm (List.range M.K)

/-- The machine side of the reduction: well-formed, reversible, `pair` matches sinks to sources
with the same counters, (H1) and (H2). -/
structure Valid (M : Machine) : Prop where
  wf : M.WF
  rev : Reversible M.rules
  pair_sink : ∀ c : Cfg, IsSink M.rules c ↔ IsSource M.rules (M.pairFn c.1, c.2)
  noBiInfinite : NoBiInfinite M.rules
  endToStart : EndToStart M.rules M.pairFn

end Machine

/-- A partial injection from an injective partial function (the inverse by choice). -/
noncomputable def ofInjective {α β : Type*} (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') : PEquiv α β where
  toFun := f
  invFun b := by classical exact if h : ∃ a, f a = some b then some h.choose else none
  inv a b := by
    classical
    constructor
    · intro h
      split_ifs at h with hb
      · cases h; exact hb.choose_spec
    · intro h
      have hb : ∃ a, f a = some b := ⟨a, h⟩
      rw [dif_pos hb, hf _ _ _ hb.choose_spec h]

/-- Under determinism every firing rule gives the step. -/
theorem step_eq_of_fires {R : List Rule} (hdet : Deterministic R) {ρ : Rule} (hρ : ρ ∈ R)
    {c : Cfg} (hc : ρ.Fires c) : step R c = some (ρ.target c) := by
  cases h : R.find? (fun ρ => decide (ρ.Fires c)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simpa using hc) (h ρ hρ)
  | some ρ₀ =>
    have h0 := List.find?_some h
    simp only [decide_eq_true_eq] at h0
    simp only [step, h, Option.map_some, Option.some.injEq]
    exact hdet _ (List.mem_of_find?_eq_some h) _ hρ c h0 hc

/-- Under reversibility the step is injective. -/
theorem step_injective {R : List Rule} (hrev : Reversible R) {c c' d : Cfg}
    (h : step R c = some d) (h' : step R c' = some d) : c = c' := by
  obtain ⟨ρ, hρ, hf, rfl⟩ := exists_rule_of_step h
  obtain ⟨ρ', hρ', hf', he⟩ := exists_rule_of_step h'
  exact hrev ρ hρ ρ' hρ' c c' hf hf' he.symm

/-- The configuration graph of a reversible machine, as a partial injection. -/
noncomputable def machine (R : List Rule) (hrev : Reversible R) : PEquiv Cfg Cfg :=
  ofInjective (step R) fun _ _ _ h h' => step_injective hrev h h'

/-! ## 3. The engine map (Lemma P → a partial injection of `ℤ`) -/

instance (j : ℕ) : DecidablePred (InEngine j) := fun n => by
  unfold InEngine; infer_instance

/-- The configuration an engine point encodes. -/
def decode (j : ℕ) (n : ℤ) : Cfg :=
  (phase j n, C1 j n, C2 j n)

/-- The engine point for `c` with junk `(0, 0, 1)`: `2^{N c₁} 3^{s + N c₂}`. -/
def enc (j : ℕ) (c : Cfg) : ℤ :=
  2 ^ (N j * c.2.1) * 3 ^ (c.1 + N j * c.2.2)

/-- The Lemma P piece: go to state `s'`, add `(δ₁, δ₂)` to the counters. -/
def move (j : ℕ) (n : ℤ) (s' : ℕ) (δ₁ δ₂ : ℤ) : ℤ :=
  scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)

/-- The engine map: on the engine, the first rule firing on `decode j n`, as a Lemma P piece. -/
def F (j : ℕ) (R : List Rule) (n : ℤ) : Option ℤ :=
  if InEngine j n then
    (R.find? fun ρ => decide (ρ.Fires (decode j n))).map fun ρ =>
      move j n ρ.dst ρ.d₁.val ρ.d₂.val
  else none

/-- Every rule's states are phases at level `j`. -/
def Fits (j : ℕ) (R : List Rule) : Prop :=
  ∀ ρ ∈ R, ρ.src < orderOf (3 : ZMod (5 ^ j)) ∧ ρ.dst < orderOf (3 : ZMod (5 ^ j))

theorem orderOf_three_pos {j : ℕ} (hj : 1 ≤ j) : 0 < orderOf (3 : ZMod (5 ^ j)) :=
  orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N j, N_pos j, three_pow_N hj⟩)

/-- An engine phase is below the order of `3`. -/
theorem phase_lt_ord {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    phase j n < orderOf (3 : ZMod (5 ^ j)) := by
  have hpos := orderOf_three_pos hj
  have hlt : phase j n % orderOf (3 : ZMod (5 ^ j)) < N j :=
    lt_of_lt_of_le (Nat.mod_lt _ hpos) (orderOf_three_le hj)
  have hx : (3 : ZMod (5 ^ j)) ^ (phase j n % orderOf (3 : ZMod (5 ^ j))) = (n : ZMod (5 ^ j)) := by
    rw [pow_mod_orderOf]; exact hn.2.2.1
  have hmin : ∀ i < phase j n, (3 : ZMod (5 ^ j)) ^ i ≠ n := (dlog3_spec hlt hx).2
  have hle : phase j n ≤ phase j n % orderOf (3 : ZMod (5 ^ j)) := by
    by_contra h
    exact hmin _ (by omega) hx
  exact lt_of_le_of_lt hle (Nat.mod_lt _ hpos)

/-- The Lemma P piece on decoded configurations. -/
theorem decode_move {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) {s' : ℕ}
    (hs' : s' < orderOf (3 : ZMod (5 ^ j))) {δ₁ δ₂ : ℤ} (h₁ : 0 ≤ (C1 j n : ℤ) + δ₁)
    (h₂ : 0 ≤ (C2 j n : ℤ) + δ₂) :
    InEngine j (move j n s' δ₁ δ₂) ∧
      decode j (move j n s' δ₁ δ₂) = (s', ((C1 j n : ℤ) + δ₁).toNat, ((C2 j n : ℤ) + δ₂).toNat) ∧
      junk j (move j n s' δ₁ δ₂) = junk j n := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := build_scale_spec hj hn hs' h₁ h₂
  exact ⟨h0, by rw [decode, move, h1, h2, h3], h4⟩

/-- Engine points with equal decoding and junk are equal. -/
theorem decode_inj {j : ℕ} (hj : 1 ≤ j) {n n' : ℤ} (hn : InEngine j n) (hn' : InEngine j n')
    (hd : decode j n = decode j n') (hjk : junk j n = junk j n') : n = n' := by
  simp only [decode, Prod.mk.injEq] at hd
  exact eq_of_decode_eq hj hn hn' hd.1 hd.2.1 hd.2.2 hjk

/-- `enc j c` lies on the engine and decodes to `c`. -/
theorem enc_spec {j : ℕ} (hj : 1 ≤ j) {c : Cfg} (hc : c.1 < orderOf (3 : ZMod (5 ^ j))) :
    InEngine j (enc j c) ∧ decode j (enc j c) = c := by
  have he : enc j c = build j 0 0 1 c.1 c.2.1 c.2.2 := by simp [enc, build]
  obtain ⟨h0, h1, h2, h3, -⟩ := build_spec (m := 1) hj (N_pos j) (N_pos j) hc
    (by decide) (by decide) (by simp) c.2.1 c.2.2
  rw [he]
  exact ⟨h0, by rw [decode, h1, h2, h3]⟩

/-- `F` is undefined off the engine. -/
theorem F_of_not_inEngine (j : ℕ) (R : List Rule) {n : ℤ} (hn : ¬ InEngine j n) :
    F j R n = none := by
  simp [F, hn]

/-- **Conjugacy (Lemma P).**  On the engine, `F` is the machine step on decoded
configurations, with the junk fixed. -/
theorem F_eq_some_iff {j : ℕ} (hj : 1 ≤ j) {R : List Rule} (hR : Fits j R) {n m : ℤ}
    (hn : InEngine j n) :
    F j R n = some m ↔
      InEngine j m ∧ junk j m = junk j n ∧ step R (decode j n) = some (decode j m) := by
  unfold F step
  rw [if_pos hn]
  cases h : R.find? (fun ρ => decide (ρ.Fires (decode j n))) with
  | none => simp
  | some ρ =>
    have hf := List.find?_some h
    simp only [decide_eq_true_eq] at hf
    obtain ⟨-, -, -, h₁, h₂⟩ := hf
    obtain ⟨hE, hd, hjk⟩ := decode_move hj hn (hR ρ (List.mem_of_find?_eq_some h)).2 h₁ h₂
    simp only [Option.map_some, Option.some.injEq]
    have ht : ρ.target (decode j n) = decode j (move j n ρ.dst ρ.d₁.val ρ.d₂.val) := by
      rw [hd]; rfl
    constructor
    · rintro rfl; exact ⟨hE, hjk, ht⟩
    · rintro ⟨hm, hjm, hdm⟩
      exact decode_inj hj hE hm (ht.symm.trans hdm) (hjk.trans hjm.symm)

/-- Under determinism, every rule firing on `decode j n` gives `F` as its piece. -/
theorem F_eq_move {j : ℕ} (hj : 1 ≤ j) {R : List Rule} (hR : Fits j R) (hdet : Deterministic R)
    {n : ℤ} (hn : InEngine j n) {ρ : Rule} (hρ : ρ ∈ R) (hf : ρ.Fires (decode j n)) :
    F j R n = some (move j n ρ.dst ρ.d₁.val ρ.d₂.val) := by
  obtain ⟨-, -, -, h₁, h₂⟩ := id hf
  obtain ⟨hE, hd, hjk⟩ := decode_move hj hn (hR ρ hρ).2 h₁ h₂
  rw [F_eq_some_iff hj hR hn, step_eq_of_fires hdet hρ hf, hd]
  exact ⟨hE, hjk, rfl⟩

theorem zpow_toNat (x : ℚ) (hx : x ≠ 0) (A : ℤ) : x ^ A = x ^ A.toNat / x ^ (-A).toNat := by
  conv_lhs => rw [← Int.toNat_sub_toNat_neg A]
  rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast]

/-- Each piece is linear with slope in `2^ℤ 3^ℤ`. -/
theorem move_slope {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) {s' : ℕ}
    (hs' : s' < orderOf (3 : ZMod (5 ^ j))) {δ₁ δ₂ : ℤ} (h₁ : 0 ≤ (C1 j n : ℤ) + δ₁)
    (h₂ : 0 ≤ (C2 j n : ℤ) + δ₂) :
    (move j n s' δ₁ δ₂ : ℚ) =
      (2 : ℚ) ^ ((N j : ℤ) * δ₁) * (3 : ℚ) ^ ((N j : ℤ) * δ₂ + s' - phase j n) * n := by
  have h := scale_spec hj hn hs' h₁ h₂
  have hq : (move j n s' δ₁ δ₂ : ℚ) * 2 ^ (-(N j * δ₁ : ℤ)).toNat *
        3 ^ (-(N j * δ₂ + s' - phase j n : ℤ)).toNat =
      n * 2 ^ (N j * δ₁ : ℤ).toNat * 3 ^ (N j * δ₂ + s' - phase j n : ℤ).toNat := by
    exact_mod_cast h
  rw [zpow_toNat 2 (by norm_num), zpow_toNat 3 (by norm_num)]
  field_simp
  linear_combination hq

/-- Under reversibility `F` is injective. -/
theorem F_injective {j : ℕ} (hj : 1 ≤ j) {R : List Rule} (hR : Fits j R) (hrev : Reversible R)
    {n n' m : ℤ} (h : F j R n = some m) (h' : F j R n' = some m) : n = n' := by
  have hn : InEngine j n := by
    by_contra hn; rw [F_of_not_inEngine j R hn] at h; cases h
  have hn' : InEngine j n' := by
    by_contra hn'; rw [F_of_not_inEngine j R hn'] at h'; cases h'
  obtain ⟨-, hj1, hs1⟩ := (F_eq_some_iff hj hR hn).1 h
  obtain ⟨-, hj2, hs2⟩ := (F_eq_some_iff hj hR hn').1 h'
  exact decode_inj hj hn hn' (step_injective hrev hs1 hs2) (hj1.symm.trans hj2)

/-- The engine map as a partial injection of `ℤ`. -/
noncomputable def engine {j : ℕ} (hj : 1 ≤ j) {R : List Rule} (hR : Fits j R)
    (hrev : Reversible R) : PEquiv ℤ ℤ :=
  ofInjective (F j R) fun _ _ _ h h' => F_injective hj hR hrev h h'

/-! ## 4. Assembly: the highway and the permutation -/

/-- `n` lies in the class `rm.1 + rm.2 ℤ`. -/
def InClass (rm : ℤ × ℤ) (n : ℤ) : Prop :=
  n ≡ rm.1 [ZMOD rm.2]

/-- The line: the non-engine points and the engine points that decode to a source. -/
def Line (j : ℕ) (R : List Rule) : Set ℤ :=
  {n | ¬ InEngine j n ∨ IsSource R (decode j n)}

/-- A highway: disjoint residue classes, all moduli `5^j · 2^α 3^β`, covering the line. -/
structure IsHighway (j : ℕ) (R : List Rule) (hw : List (ℤ × ℤ)) : Prop where
  ne_nil : hw ≠ []
  modulus : ∀ rm ∈ hw, ∃ α β : ℕ, rm.2 = 5 ^ j * 2 ^ α * 3 ^ β
  disjoint : hw.Pairwise fun a b => ∀ n, ¬ (InClass a n ∧ InClass b n)
  cover : ∀ n, n ∈ Line j R ↔ ∃ rm ∈ hw, InClass rm n

/-- The index of the first class of `hw` containing `n`. -/
def hwIdx (hw : List (ℤ × ℤ)) (n : ℤ) : ℕ :=
  hw.findIdx fun rm => n % rm.2 == rm.1 % rm.2

/-- The line position `k t + i` of `n = r_i + m_i t` (`k` classes). -/
def hwPos (hw : List (ℤ × ℤ)) (n : ℤ) : ℤ :=
  hw.length * ((n - (hw.getD (hwIdx hw n) (0, 1)).1) / (hw.getD (hwIdx hw n) (0, 1)).2) +
    hwIdx hw n

/-- The point at line position `p = k t + i`: `r_i + m_i t`. -/
def hwPoint (hw : List (ℤ × ℤ)) (p : ℤ) : ℤ :=
  (hw.getD (p % hw.length).toNat (0, 1)).1 +
    (hw.getD (p % hw.length).toNat (0, 1)).2 * (p / hw.length)

/-- The highway shift `ν = θ ∘ (+1) ∘ θ⁻¹`: `r_i + m_i t ↦ r_{i+1} + m_{i+1} t`, and the last
class to `r_0 + m_0 (t + 1)`. -/
def hwNext (hw : List (ℤ × ℤ)) (n : ℤ) : ℤ :=
  hwPoint hw (hwPos hw n + 1)

theorem inClass_iff (rm : ℤ × ℤ) (n : ℤ) :
    InClass rm n ↔ (n % rm.2 == rm.1 % rm.2) = true := by
  simp [InClass, Int.ModEq]

theorem IsHighway.mod_pos {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw)
    {rm : ℤ × ℤ} (hrm : rm ∈ hw) : 0 < rm.2 := by
  obtain ⟨α, β, he⟩ := h.modulus rm hrm
  rw [he]; positivity

theorem IsHighway.length_pos {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw) :
    0 < hw.length := List.length_pos_iff.2 h.ne_nil

/-- The class index of a point of class `i` is `i`. -/
theorem hwIdx_eq {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw) {i : ℕ}
    (hi : i < hw.length) {n : ℤ} (hn : InClass hw[i] n) : hwIdx hw n = i := by
  rw [hwIdx, List.findIdx_eq hi]
  refine ⟨(inClass_iff _ _).1 hn, fun k hk => ?_⟩
  have hd := List.pairwise_iff_getElem.1 h.disjoint k i (by omega) hi hk n
  rw [← Bool.not_eq_true, ← inClass_iff]
  exact fun hk' => hd ⟨hk', hn⟩

/-- The line positions enumerate the line: `θ = hwPoint` is a bijection `ℤ → Line`. -/
theorem hwPoint_hwPos {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw)
    {n : ℤ} (hn : n ∈ Line j R) : hwPoint hw (hwPos hw n) = n := by
  obtain ⟨rm, hrm, hin⟩ := (h.cover n).1 hn
  have hlt : hwIdx hw n < hw.length :=
    List.findIdx_lt_length_of_exists ⟨rm, hrm, (inClass_iff _ _).1 hin⟩
  have hcl : InClass hw[hwIdx hw n] n := (inClass_iff _ _).2 (List.findIdx_getElem (w := hlt))
  have hk := h.length_pos
  set i := hwIdx hw n with hi
  have hg : hw.getD i (0, 1) = hw[i] := List.getD_eq_getElem _ _ hlt
  have hdvd : hw[i].2 ∣ n - hw[i].1 := (Int.ModEq.dvd hcl.symm)
  have hpos : hwPos hw n = hw.length * ((n - hw[i].1) / hw[i].2) + i := by
    rw [hwPos, ← hi, hg]
  have hmod : hwPos hw n % hw.length = i := by
    rw [hpos, Int.mul_add_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hdiv : hwPos hw n / hw.length = (n - hw[i].1) / hw[i].2 := by
    rw [hpos, Int.mul_add_ediv_left _ _ (by omega),
      Int.ediv_eq_zero_of_lt (a := (i : ℤ)) (by omega) (by omega), add_zero]
  rw [hwPoint, hmod, hdiv, Int.toNat_natCast, hg, Int.mul_ediv_cancel' hdvd]
  ring

/-- The other half of the line bijection. -/
theorem hwPos_hwPoint {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw)
    (p : ℤ) : hwPoint hw p ∈ Line j R ∧ hwPos hw (hwPoint hw p) = p := by
  have hk : (0 : ℤ) < hw.length := by exact_mod_cast h.length_pos
  have h0 := Int.emod_nonneg p hk.ne'
  have hlt : (p % hw.length).toNat < hw.length := by
    have := Int.emod_lt_of_pos p hk; omega
  set i := (p % hw.length).toNat with hi
  have hg : hw.getD i (0, 1) = hw[i] := List.getD_eq_getElem _ _ hlt
  have hx : hwPoint hw p = hw[i].1 + hw[i].2 * (p / hw.length) := by rw [hwPoint, ← hi, hg]
  have hcl : InClass hw[i] (hwPoint hw p) := by
    rw [hx, InClass]
    exact (Int.modEq_iff_dvd.2 ⟨-(p / hw.length), by ring⟩)
  have hm := h.mod_pos (List.getElem_mem hlt)
  refine ⟨(h.cover _).2 ⟨_, List.getElem_mem hlt, hcl⟩, ?_⟩
  rw [hwPos, hwIdx_eq h hlt hcl, hg, hx, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hm.ne',
    hi, Int.toNat_of_nonneg h0, Int.mul_ediv_add_emod]

/-- The highway modulus at level `j`: `5^j · 2^{2N} · 3^{3N}`.  Line membership is periodic
mod it (the counter conditions `C_i = 0`, `= 1`, `≥ 2` are `v₂`, `v₃` thresholds below `2N`,
`3N`). -/
def hwModulus (j : ℕ) : ℕ :=
  5 ^ j * 2 ^ (2 * N j) * 3 ^ (3 * N j)

/-- The highway at level `j`: every class mod `hwModulus j` that lies in the line. -/
def highwayAt (j : ℕ) (R : List Rule) : List (ℤ × ℤ) :=
  ((List.range (hwModulus j)).filter fun r =>
      !decide (InEngine j (r : ℤ)) || isSourceB R (decode j (r : ℤ))).map
    fun r => ((r : ℤ), (hwModulus j : ℤ))

/-- **Open.**  `highwayAt j R` is a highway. -/
theorem isHighway_highwayAt {j : ℕ} (hj : 1 ≤ j) (R : List Rule) :
    IsHighway j R (highwayAt j R) := by
  sorry

/-- The permutation: `F` where defined, `ν ∘ τ` on engine sinks (`τ` relabels the state by
`pairFn`, keeping counters and junk), and `ν` off the engine. -/
def sigma (j : ℕ) (M : Machine) (hw : List (ℤ × ℤ)) (n : ℤ) : ℤ :=
  match F j M.rules n with
  | some m => m
  | none =>
    if InEngine j n then hwNext hw (move j n (M.pairFn (phase j n)) 0 0) else hwNext hw n

/-- The hypotheses for bijectivity: a level that fits the machine, well-formedness,
reversibility, `pair` matching sinks to sources with the same counters, and a highway. -/
structure Good (j : ℕ) (M : Machine) (hw : List (ℤ × ℤ)) : Prop where
  one_le : 1 ≤ j
  fits : M.K ≤ orderOf (3 : ZMod (5 ^ j))
  wf : M.WF
  rev : Reversible M.rules
  pair_sink : ∀ c : Cfg, IsSink M.rules c ↔ IsSource M.rules (M.pairFn c.1, c.2)
  highway : IsHighway j M.rules hw

section Assembly

open CollatzMoonshot.RcwaMachine

theorem ofInjective_symm_eq_none {α β : Type*} {f : α → Option β}
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') {b : β} :
    (ofInjective f hf).symm b = none ↔ ∀ a, f a ≠ some b := by
  constructor
  · intro h a ha
    have : (ofInjective f hf).symm b = some a := (PEquiv.eq_some_iff _).2 ha
    rw [h] at this; cases this
  · intro h
    by_contra h'
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h'
    exact h a ((PEquiv.eq_some_iff _).1 ha)

theorem inEngine_of_F {j : ℕ} {R : List Rule} {n m : ℤ} (h : F j R n = some m) :
    InEngine j n := by
  by_contra hn; rw [F_of_not_inEngine j R hn] at h; cases h

theorem F_eq_none_iff {j : ℕ} {R : List Rule} {n : ℤ} (hn : InEngine j n) :
    F j R n = none ↔ step R (decode j n) = none := by
  simp [F, step, hn]

/-- A highway machine fits its level. -/
theorem Good.fitsR {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    Fits j M.rules := fun ρ hρ =>
  ⟨lt_of_lt_of_le (h.wf.src_lt ρ hρ) h.fits, lt_of_lt_of_le (h.wf.dst_lt ρ hρ) h.fits⟩

/-- The engine partial injection of a good machine. -/
noncomputable def Good.eng {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    PEquiv ℤ ℤ :=
  engine h.one_le h.fitsR h.rev

theorem Good.eng_apply {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) (n : ℤ) :
    h.eng n = F j M.rules n := rfl

/-- The sources of the engine are the line. -/
theorem engine_symm_eq_none_iff {j : ℕ} (hj : 1 ≤ j) {R : List Rule} (hR : Fits j R)
    (hrev : Reversible R) {x : ℤ} : (engine hj hR hrev).symm x = none ↔ x ∈ Line j R := by
  rw [engine, ofInjective_symm_eq_none]
  by_cases hx : InEngine j x
  · simp only [Line, Set.mem_ofPred_eq, hx, not_true_eq_false, false_or]
    constructor
    · intro h c' hc'
      obtain ⟨ρ, hρ, hf, -⟩ := exists_rule_of_step hc'
      have hs : c'.1 < orderOf (3 : ZMod (5 ^ j)) := hf.1 ▸ (hR ρ hρ).1
      obtain ⟨a, ha, h1, h2, h3, h4⟩ := exists_decode hj hx hs c'.2.1 c'.2.2
      have hda : decode j a = c' := by rw [decode, h1, h2, h3]
      exact h a ((F_eq_some_iff hj hR ha).2 ⟨hx, h4.symm, hda ▸ hc'⟩)
    · intro h a ha
      exact h _ ((F_eq_some_iff hj hR (inEngine_of_F ha)).1 ha).2.2
  · simp only [Line, Set.mem_ofPred_eq, hx, not_false_eq_true, true_or, iff_true]
    intro a ha
    exact hx ((F_eq_some_iff hj hR (inEngine_of_F ha)).1 ha).1

/-- The line enumeration `θ`. -/
noncomputable def Good.theta {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    ℤ ≃ Src h.eng ⊕ Empty where
  toFun p := Sum.inl ⟨hwPoint hw p, (engine_symm_eq_none_iff _ _ _).2 (hwPos_hwPoint h.highway p).1⟩
  invFun := Sum.elim (fun s => hwPos hw s.1) Empty.elim
  left_inv p := (hwPos_hwPoint h.highway p).2
  right_inv := by
    rintro (s | e)
    · exact congrArg Sum.inl (Subtype.ext
        (hwPoint_hwPos h.highway ((engine_symm_eq_none_iff _ _ _).1 s.2)))
    · exact e.elim

theorem Good.theta_apply {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) (p : ℤ) :
    lineEmb h.eng (h.theta p) = Sum.inl (hwPoint hw p) := rfl

theorem Good.theta_symm_apply {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (s : Src h.eng) : h.theta.symm (Sum.inl s) = hwPos hw s.1 := rfl

theorem Good.nu_inl {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (s : Src h.eng) : nu h.eng h.theta (Sum.inl s) = Sum.inl (hwNext hw s.1) := rfl


namespace Machine

theorem WF.length_pair {M : Machine} (h : M.WF) : M.pair.length = M.K := by
  rw [h.pair_perm.length_eq, List.length_range]

theorem WF.pairFn_lt {M : Machine} (h : M.WF) {s : ℕ} (hs : s < M.K) : M.pairFn s < M.K := by
  have hl : s < M.pair.length := h.length_pair ▸ hs
  rw [pairFn, List.getD_eq_getElem _ _ hl]
  exact List.mem_range.1 (h.pair_perm.subset (List.getElem_mem hl))

theorem WF.pairFn_of_le {M : Machine} (h : M.WF) {s : ℕ} (hs : M.K ≤ s) : M.pairFn s = s := by
  rw [pairFn, List.getD_eq_default _ _ (h.length_pair ▸ hs)]

theorem WF.pairFn_injective {M : Machine} (h : M.WF) : Function.Injective M.pairFn := by
  have hnd : M.pair.Nodup := h.pair_perm.nodup_iff.2 List.nodup_range
  intro s t hst
  rcases lt_or_ge s M.K with hs | hs <;> rcases lt_or_ge t M.K with ht | ht
  · have hs' : s < M.pair.length := h.length_pair ▸ hs
    have ht' : t < M.pair.length := h.length_pair ▸ ht
    rw [pairFn, pairFn, List.getD_eq_getElem _ _ hs', List.getD_eq_getElem _ _ ht'] at hst
    exact (hnd.getElem_inj_iff).1 hst
  · have := h.pairFn_lt hs; rw [hst, h.pairFn_of_le ht] at this; omega
  · have := h.pairFn_lt ht; rw [← hst, h.pairFn_of_le hs] at this; omega
  · rwa [h.pairFn_of_le hs, h.pairFn_of_le ht] at hst

theorem WF.pairFn_surjective {M : Machine} (h : M.WF) : Function.Surjective M.pairFn := by
  intro t
  rcases lt_or_ge t M.K with ht | ht
  · obtain ⟨s, hs, he⟩ := List.getElem_of_mem (h.pair_perm.symm.subset (List.mem_range.2 ht))
    exact ⟨s, by rw [pairFn, List.getD_eq_getElem _ _ hs, he]⟩
  · exact ⟨t, h.pairFn_of_le ht⟩

end Machine

theorem Good.pairFn_lt_ord {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {s : ℕ}
    (hs : s < orderOf (3 : ZMod (5 ^ j))) : M.pairFn s < orderOf (3 : ZMod (5 ^ j)) := by
  rcases lt_or_ge s M.K with hK | hK
  · exact lt_of_lt_of_le (h.wf.pairFn_lt hK) h.fits
  · rwa [h.wf.pairFn_of_le hK]

/-- The Lemma P piece with no counter move. -/
theorem decode_move_zero {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) {s' : ℕ}
    (hs' : s' < orderOf (3 : ZMod (5 ^ j))) :
    InEngine j (move j n s' 0 0) ∧ decode j (move j n s' 0 0) = (s', C1 j n, C2 j n) ∧
      junk j (move j n s' 0 0) = junk j n := by
  obtain ⟨h0, h1, h2⟩ := decode_move hj hn hs' (δ₁ := 0) (δ₂ := 0) (by omega) (by omega)
  refine ⟨h0, ?_, h2⟩
  rw [h1]; simp

theorem Good.isSink_of_snk {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (x : Snk h.eng) (hx : InEngine j x.1) : IsSink M.rules (decode j x.1) :=
  (F_eq_none_iff hx).1 x.2

/-- The relabelling `τ` on points. -/
def tauPt (j : ℕ) (M : Machine) (x : ℤ) : ℤ :=
  if InEngine j x then move j x (M.pairFn (phase j x)) 0 0 else x

theorem Good.tauPt_spec {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {x : ℤ}
    (hx : InEngine j x) :
    InEngine j (tauPt j M x) ∧ decode j (tauPt j M x) = (M.pairFn (phase j x), C1 j x, C2 j x) ∧
      junk j (tauPt j M x) = junk j x := by
  rw [tauPt, if_pos hx]
  exact decode_move_zero h.one_le hx (h.pairFn_lt_ord (phase_lt_ord h.one_le hx))

theorem Good.tauPt_mem {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (x : Snk h.eng) : h.eng.symm (tauPt j M x.1) = none := by
  change (engine h.one_le h.fitsR h.rev).symm _ = none
  rw [engine_symm_eq_none_iff]
  by_cases hx : InEngine j x.1
  · obtain ⟨h0, h1, -⟩ := h.tauPt_spec hx
    right
    rw [h1]
    exact (h.pair_sink (decode j x.1)).1 (h.isSink_of_snk x hx)
  · left; rwa [tauPt, if_neg hx]

theorem Good.tauPt_bijective {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    Function.Bijective (fun x : Snk h.eng => (⟨tauPt j M x.1, h.tauPt_mem x⟩ : Src h.eng)) := by
  have hj := h.one_le
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have he : tauPt j M x.1 = tauPt j M y.1 := congrArg Subtype.val hxy
    apply Subtype.ext
    by_cases hx : InEngine j x.1 <;> by_cases hy : InEngine j y.1
    · obtain ⟨hx0, hx1, hx2⟩ := h.tauPt_spec hx
      obtain ⟨hy0, hy1, hy2⟩ := h.tauPt_spec hy
      rw [he] at hx1 hx2
      rw [hx1] at hy1
      simp only [Prod.mk.injEq] at hy1
      obtain ⟨hp, hc1, hc2⟩ := hy1
      refine decode_inj hj hx hy ?_ (hx2.symm.trans hy2)
      rw [decode, decode, h.wf.pairFn_injective hp, hc1, hc2]
    · have := (h.tauPt_spec hx).1; rw [he, tauPt, if_neg hy] at this; exact absurd this hy
    · have := (h.tauPt_spec hy).1; rw [← he, tauPt, if_neg hx] at this; exact absurd this hx
    · rwa [tauPt, tauPt, if_neg hx, if_neg hy] at he
  · by_cases hy : InEngine j y.1
    · have hsrc : IsSource M.rules (decode j y.1) := by
        have := (engine_symm_eq_none_iff _ _ _).1 y.2
        exact this.resolve_left (not_not.2 hy)
      obtain ⟨s, hs⟩ := h.wf.pairFn_surjective (phase j y.1)
      have hs' : s < orderOf (3 : ZMod (5 ^ j)) := by
        rcases lt_or_ge s M.K with hK | hK
        · exact lt_of_lt_of_le hK h.fits
        · rw [h.wf.pairFn_of_le hK] at hs; rw [hs]; exact phase_lt_ord hj hy
      obtain ⟨x, hx, h1, h2, h3, h4⟩ := exists_decode hj hy hs' (C1 j y.1) (C2 j y.1)
      have hdx : decode j x = (s, C1 j y.1, C2 j y.1) := by rw [decode, h1, h2, h3]
      have hsink : IsSink M.rules (decode j x) := by
        rw [h.pair_sink, hdx]; simpa [hs, decode] using hsrc
      have hxs : h.eng x = none := (F_eq_none_iff hx).2 hsink
      refine ⟨⟨x, hxs⟩, Subtype.ext ?_⟩
      obtain ⟨t0, t1, t2⟩ := h.tauPt_spec hx
      refine decode_inj hj t0 hy ?_ (t2.trans h4)
      rw [t1, h1, h2, h3, hs]; rfl
    · have hxs : h.eng y.1 = none := F_of_not_inEngine j M.rules hy
      refine ⟨⟨y.1, hxs⟩, Subtype.ext ?_⟩
      show tauPt j M y.1 = y.1
      rw [tauPt, if_neg hy]

/-- The sink-to-source pairing `τ`. -/
noncomputable def Good.tau {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    Snk h.eng ≃ Src h.eng :=
  Equiv.ofBijective _ h.tauPt_bijective

theorem Good.completeFun_eq {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (n : ℤ) : completeFun h.eng h.tau h.theta (Sum.inl n) = Sum.inl (sigma j M hw n) := by
  cases hF : F j M.rules n with
  | some m =>
    rw [completeFun_some h.tau h.theta (show h.eng n = some m from hF)]
    simp [sigma, hF]
  | none =>
    rw [completeFun_none h.tau h.theta (show h.eng n = none from hF), h.nu_inl]
    simp only [sigma, hF, Sum.inl.injEq]
    show hwNext hw (tauPt j M n) = _
    rw [tauPt]
    split_ifs <;> rfl

/-- `sigma` is a bijection of `ℤ` (Lemma C part 1: no hypothesis on runs). -/
theorem sigma_bijective {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    Function.Bijective (sigma j M hw) := by
  have he : sigma j M hw = Equiv.sumEmpty ℤ Empty ∘ completeFun h.eng h.tau h.theta ∘
      (Equiv.sumEmpty ℤ Empty).symm := by
    funext n
    simp [h.completeFun_eq]
  rw [he]
  exact (Equiv.bijective _).comp ((completeFun_bijective _ _ _).comp (Equiv.bijective _))

/-- The permutation `σ`. -/
noncomputable def sigmaPerm {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) :
    Equiv.Perm ℤ :=
  Equiv.ofBijective _ (sigma_bijective h)

/-- **Open.**  `σ` is RCWA with all slopes in `2^ℤ 3^ℤ`, at modulus `3^N · L` for any `L > 0`
that the highway moduli and `5^j 2^N 3^{2N}` (the zero tests) divide. -/
theorem isRcwa23At_sigma {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {L : ℕ}
    (hL : 0 < L) (hhw : ∀ rm ∈ hw, rm.2 ∣ L) (htest : 5 ^ j * 2 ^ N j * 3 ^ (2 * N j) ∣ L) :
    IsRcwa23At (3 ^ N j * L) (sigma j M hw) := by
  sorry

/-- Same-cycle transfers along an injective intertwiner. -/
theorem sameCycle_transfer {α β : Type*} {e : α → β} (he : Function.Injective e)
    {σ : Equiv.Perm α} {τ : Equiv.Perm β} (h : ∀ x, τ (e x) = e (σ x)) {a b : α} :
    τ.SameCycle (e a) (e b) ↔ σ.SameCycle a b := by
  have hk : ∀ k : ℤ, ∀ x, (τ ^ k) (e x) = e ((σ ^ k) x) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]
    | pred k ih =>
      intro x
      have hi : τ⁻¹ (e x) = e (σ⁻¹ x) := by
        rw [Equiv.Perm.inv_eq_iff_eq, h]; simp
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hi, ih]
  constructor
  · rintro ⟨k, hk'⟩
    exact ⟨k, he (by rw [← hk, hk'])⟩
  · rintro ⟨k, hk'⟩
    exact ⟨k, by rw [hk, hk']⟩

/-- A run halts iff it stops (reaches `none`). -/
theorem halts_iff_exists_run_eq_none {R : List Rule} {c : Cfg} :
    Halts R c ↔ ∃ k, run R k c = none := by
  have hsucc : ∀ k c, run R (k + 1) c = (run R k c).bind (step R) := fun k c =>
    Function.iterate_succ_apply' _ _ _
  constructor
  · rintro ⟨k, d, hk, hd⟩
    exact ⟨k + 1, by rw [hsucc, hk, Option.bind_some]; exact hd⟩
  · intro h
    classical
    have h0 : Nat.find h ≠ 0 := fun h0 => by
      have := Nat.find_spec h; rw [h0] at this; cases this
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hlt : ¬ run R m c = none := Nat.find_min h (by omega)
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hlt
    refine ⟨m, d, hd, ?_⟩
    have := Nat.find_spec h
    rwa [hm, hsucc, hd, Option.bind_some] at this

/-- The engine runs the machine on decoded configurations, junk fixed. -/
theorem Good.fwd_eng {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {n : ℤ}
    (hn : InEngine j n) (k : ℕ) :
    (fwd h.eng k n).map (decode j) = run M.rules k (decode j n) ∧
      ∀ x, fwd h.eng k n = some x → InEngine j x ∧ junk j x = junk j n := by
  induction k with
  | zero => exact ⟨rfl, fun x hx => by cases hx; exact ⟨hn, rfl⟩⟩
  | succ k ih =>
    have hr : run M.rules (k + 1) (decode j n) =
        (run M.rules k (decode j n)).bind (step M.rules) := Function.iterate_succ_apply' _ _ _
    rw [fwd_succ, hr, ← ih.1]
    cases hx : fwd h.eng k n with
    | none => exact ⟨rfl, fun x hx' => by cases hx'⟩
    | some x =>
      obtain ⟨hxE, hxj⟩ := ih.2 x hx
      simp only [Option.bind_some, Option.map_some]
      cases hm : h.eng x with
      | none =>
        refine ⟨?_, fun y hy => by cases hy⟩
        rw [Option.map_none, eq_comm]
        exact (F_eq_none_iff hxE).1 hm
      | some m =>
        obtain ⟨hmE, hmj, hs⟩ := (F_eq_some_iff h.one_le h.fitsR hxE).1 hm
        refine ⟨by rw [Option.map_some, hs], fun y hy => ?_⟩
        cases hy
        exact ⟨hmE, hmj.trans hxj⟩

/-- An engine point diverges iff its decoded run does not halt. -/
theorem Good.diverges_iff {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {n : ℤ}
    (hn : InEngine j n) : Diverges h.eng n ↔ ¬ Halts M.rules (decode j n) := by
  rw [halts_iff_exists_run_eq_none, Diverges]
  push Not
  refine forall_congr' fun k => ?_
  rw [← (h.fwd_eng hn k).1]
  simp

/-- (H1) transfers to the engine. -/
theorem Good.noBiInfinite {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (h1 : NoBiInfinite M.rules) : RcwaMachine.NoBiInfinite h.eng := by
  intro g hg
  apply h1 (fun i => decode j (g i))
  intro i
  have hE := inEngine_of_F (hg i)
  exact ((F_eq_some_iff h.one_le h.fitsR hE).1 (hg i)).2.2

theorem Good.tau_apply {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (t : Snk h.eng) : (h.tau t).1 = tauPt j M t.1 := rfl

/-- (H2) transfers to the engine. -/
theorem Good.endToStart {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (h2 : EndToStart M.rules M.pairFn) : RcwaMachine.EndToStart h.eng h.tau := by
  intro s t n hst
  have hline := (engine_symm_eq_none_iff _ _ _).1 s.2
  apply Subtype.ext
  rw [h.tau_apply]
  by_cases hs : InEngine j s.1
  · have hsrc : IsSource M.rules (decode j s.1) := hline.resolve_left (not_not.2 hs)
    obtain ⟨hmap, hinv⟩ := h.fwd_eng hs n
    obtain ⟨htE, htj⟩ := hinv _ hst
    rw [hst, Option.map_some] at hmap
    have hsink : IsSink M.rules (decode j t.1) := (F_eq_none_iff htE).1 t.2
    have he := h2 _ _ _ hsrc hmap.symm hsink
    obtain ⟨t0, t1, t2⟩ := h.tauPt_spec htE
    refine decode_inj h.one_le t0 hs ?_ (t2.trans htj)
    rw [t1, ← he]; rfl
  · have hF : h.eng s.1 = none := F_of_not_inEngine j M.rules hs
    cases n with
    | zero =>
      rw [fwd_zero, Option.some.injEq] at hst
      rw [← hst, tauPt, if_neg hs]
    | succ n => rw [fwd_succ_of_none hF] at hst; cases hst

theorem Good.complete_inl {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) (x : ℤ) :
    complete h.eng h.tau h.theta (Sum.inl x) = Sum.inl (sigmaPerm h x) := by
  rw [complete_apply, h.completeFun_eq]; rfl

theorem Good.sameCycle_iff {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    {a b : ℤ} : (complete h.eng h.tau h.theta).SameCycle (Sum.inl a) (Sum.inl b) ↔
      (sigmaPerm h).SameCycle a b :=
  sameCycle_transfer Sum.inl_injective h.complete_inl

/-- **Headline.**  Under (H1) and (H2), an engine point `n` decoding to a source and
the next highway point after it lie on one `σ`-orbit iff the run from `decode j n` halts. -/
theorem sameCycle_hwNext_iff {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (h1 : NoBiInfinite M.rules) (h2 : EndToStart M.rules M.pairFn) {n : ℤ} (hn : InEngine j n)
    (hs : IsSource M.rules (decode j n)) :
    (sigmaPerm h).SameCycle n (hwNext hw n) ↔ Halts M.rules (decode j n) := by
  have hline : n ∈ Line j M.rules := Or.inr hs
  set p := hwPos hw n with hp
  have hθ : ∀ s : Src h.eng, h.theta p = Sum.inl s → s.1 = n := by
    intro s hs'
    have := congrArg (lineEmb h.eng) hs'
    rw [h.theta_apply, hp, hwPoint_hwPos h.highway hline] at this
    exact (Sum.inl.inj this).symm
  have hl0 : lineEmb h.eng (h.theta p) = Sum.inl n := by
    rw [h.theta_apply, hp, hwPoint_hwPos h.highway hline]
  have hl1 : lineEmb h.eng (h.theta (p + 1)) = Sum.inl (hwNext hw n) := h.theta_apply _
  rw [← h.sameCycle_iff, ← hl0, ← hl1]
  constructor
  · intro hsc
    by_contra hh
    rcases hθp : h.theta p with s | e
    · have hd : Diverges h.eng s.1 := by rw [hθ s hθp]; exact (h.diverges_iff hn).2 hh
      exact not_sameCycle_of_cut _ _ _ (h.noBiInfinite h1) (h.endToStart h2) s hd hθp le_rfl
        (lt_add_one p) hsc
    · exact e.elim
  · intro hh
    refine sameCycle_succ_of_not_diverges _ _ _ (h.endToStart h2) p fun s hs' => ?_
    rw [hθ s hs', h.diverges_iff hn]
    exact not_not.2 hh

/-- The headline at the encoding `enc j c` of a source `c` with state `< K`. -/
theorem sameCycle_enc_iff {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (h1 : NoBiInfinite M.rules) (h2 : EndToStart M.rules M.pairFn) {c : Cfg} (hK : c.1 < M.K)
    (hc : IsSource M.rules c) :
    (sigmaPerm h).SameCycle (enc j c) (hwNext hw (enc j c)) ↔ Halts M.rules c := by
  obtain ⟨hE, hd⟩ := enc_spec h.one_le (lt_of_lt_of_le hK h.fits)
  have := sameCycle_hwNext_iff h h1 h2 hE (by rw [hd]; exact hc)
  rwa [hd] at this

/-- **One orbit iff every source halts** (Theorem C(1) shape). -/
theorem sameCycle_all_iff {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw)
    (h1 : NoBiInfinite M.rules) (h2 : EndToStart M.rules M.pairFn) :
    (∀ a b : ℤ, (sigmaPerm h).SameCycle a b) ↔ ∀ c, IsSource M.rules c → Halts M.rules c := by
  have hL : (∀ a b : ℤ, (sigmaPerm h).SameCycle a b) ↔
      ∀ a b : ℤ ⊕ Empty, (complete h.eng h.tau h.theta).SameCycle a b := by
    constructor
    · rintro hall (a | e) (b | e')
      · exact h.sameCycle_iff.2 (hall a b)
      · exact e'.elim
      · exact e.elim
      · exact e.elim
    · intro hall a b
      exact h.sameCycle_iff.1 (hall _ _)
  rw [hL, RcwaMachine.sameCycle_all_iff _ _ _ (h.noBiInfinite h1) (h.endToStart h2)]
  constructor
  · intro hno c hc
    by_cases hord : c.1 < orderOf (3 : ZMod (5 ^ j))
    · obtain ⟨hE, hd⟩ := enc_spec h.one_le hord
      have hsrc : h.eng.symm (enc j c) = none :=
        (engine_symm_eq_none_iff _ _ _).2 (Or.inr (by rw [hd]; exact hc))
      have := hno ⟨enc j c, hsrc⟩
      rwa [h.diverges_iff hE, not_not, hd] at this
    · refine ⟨0, c, rfl, ?_⟩
      rw [IsSink, step, Option.map_eq_none_iff, List.find?_eq_none]
      intro ρ hρ hf
      have := h.wf.src_lt ρ hρ
      have hf' : ρ.Fires c := by simpa using hf
      have := hf'.1
      have := h.fits
      omega
  · intro hall s
    by_cases hs : InEngine j s.1
    · have hsrc : IsSource M.rules (decode j s.1) :=
        ((engine_symm_eq_none_iff _ _ _).1 s.2).resolve_left (not_not.2 hs)
      rw [h.diverges_iff hs, not_not]
      exact hall _ hsrc
    · intro hd
      exact hd 1 (fwd_succ_of_none (F_of_not_inEngine j M.rules hs) 0)

end Assembly

/-! ## 5. Undecidability of same-orbit -/

/-- The level used for `M`: `j = K + 1`, so `K < j ≤ orderOf (3 : ZMod (5^j))`. -/
def level (M : Machine) : ℕ :=
  M.K + 1

/-- The highway used for `M`. -/
def highwayOf (M : Machine) : List (ℤ × ℤ) :=
  highwayAt (level M) M.rules

/-- The table of `σ` for `M`, at modulus `3^N · hwModulus`. -/
def tableOf (M : Machine) : RcwaTable :=
  tableFrom (sigma (level M) M (highwayOf M)) (3 ^ N (level M) * hwModulus (level M))

/-- The instance the reduction produces: the table and the two points. -/
def reduce (p : Machine × Cfg) : RcwaTable × ℤ × ℤ :=
  (tableOf p.1, enc (level p.1) p.2, hwNext (highwayOf p.1) (enc (level p.1) p.2))

/-- **Open.**  A valid machine is good at its level with its highway. -/
theorem good_of_valid {M : Machine} (hM : M.Valid) : Good (level M) M (highwayOf M) := by
  sorry

/-- **Open.**  For a valid machine, `tableOf M` is an exact table for `σ`. -/
theorem tableOf_spec {M : Machine} (hM : M.Valid) :
    (tableOf M).Exact ∧ (tableOf M).eval = sigma (level M) M (highwayOf M) := by
  sorry

/-- `Test ≃ Fin 3`. -/
def Test.equivFin : Test ≃ Fin 3 where
  toFun | .zero => 0 | .pos => 1 | .any => 2
  invFun | 0 => .zero | 1 => .pos | 2 => .any
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- `Move ≃ Fin 3`. -/
def Move.equivFin : Move ≃ Fin 3 where
  toFun | .minus => 0 | .zero => 1 | .plus => 2
  invFun | 0 => .minus | 1 => .zero | 2 => .plus
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable Test := Primcodable.ofEquiv _ Test.equivFin

instance : Primcodable Move := Primcodable.ofEquiv _ Move.equivFin

/-- A rule as a tuple. -/
def Rule.equivProd : Rule ≃ ℕ × Test × Test × Move × Move × ℕ where
  toFun ρ := (ρ.src, ρ.t₁, ρ.t₂, ρ.d₁, ρ.d₂, ρ.dst)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Rule := Primcodable.ofEquiv _ Rule.equivProd

/-- A machine as a tuple. -/
def Machine.equivProd : Machine ≃ ℕ × List Rule × List ℕ where
  toFun M := (M.K, M.rules, M.pair)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Machine := Primcodable.ofEquiv _ Machine.equivProd

/-- A table as a tuple. -/
def RcwaTable.equivProd : RcwaTable ≃ ℕ × List (ℤ × ℤ × ℤ) where
  toFun T := (T.modulus, T.pieces)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable RcwaTable := Primcodable.ofEquiv _ RcwaTable.equivProd

/-- **Open.**  The reduction is computable (the bulk of the computability layer). -/
theorem computable_reduce : Computable reduce := by
  sorry

/-- **Literature input** (a hypothesis, never an axiom): halting from a source is undecidable
for valid machines in this file's format.

*Instruction set.*  `Rule` as defined here: per rule a test `= 0` / `≥ 1` / none on each of the
two counters and a move in `{-1, 0, 1}` on each, with semantic determinism and reversibility on
all configurations.  The reduction lands in the sub-format of Morita's quadruples (one test and
no move, or one move and no test) closed under the turnaround rules below.  The format matters:
Dudenhefner (FSCD 2022, Remark 20) records an instruction set for reversible two-counter machines
on which halting is decidable, so the hypothesis is stated for this format only.

*Construction transcribed.*  Morita, *Universality of a reversible two-counter machine*, TCS 168
(1996): every counter machine is simulated by a reversible two-counter machine in quadruple form.
Kari–Ollinger, *Periodicity and immortality in reversible computing*, MFCS 2008: the Remark to
Thm 1 (an always-incremented counter makes the reverse mortal) and Thm 3 (the forward/backward
doubling `D(R)` on states `Q × {+, −}`, with a turnaround on every sink cell).  For `R` with mortal
reverse, `D(R)` is `Valid` with `pair (q, −) = (q, +)`: its sinks are `(x, −)` for the sources `x`
of `R`, every finite run from `(x, +)` ends at `(x, −)`, and there is no bi-infinite run.  The
step "Morita's conversion preserves the mortality status at every configuration", which
Kari–Ollinger state without proof, is Lemmas M, H, G of research note `undec-lemma` (§4-§6),
with the run of `φ_e(e)` as the source (§8 part 2). -/
def HaltingUndecidable : Prop :=
  ¬ ∃ g : Machine × Cfg → Bool, Computable g ∧
    ∀ (M : Machine) (c : Cfg), M.Valid → c.1 < M.K → IsSource M.rules c →
      (g (M, c) = true ↔ Halts M.rules c)

/-- **Open.**  **Same-orbit is undecidable** on exact tables with bijective evaluation (so on
RCWA permutations of `ℤ` with all slopes in `2^ℤ 3^ℤ`), given `HaltingUndecidable`. -/
theorem not_computable_sameCycle (hlit : HaltingUndecidable) :
    ¬ ∃ g : RcwaTable × ℤ × ℤ → Bool, Computable g ∧
      ∀ (T : RcwaTable) (a b : ℤ), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g (T, a, b) = true ↔ Equiv.Perm.SameCycle (Equiv.ofBijective T.eval hb) a b) := by
  sorry

end CollatzMoonshot.RcwaSameOrbit
