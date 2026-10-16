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

/-- Firing depends only on the state and which counters are zero. -/
theorem fires_congr {ρ : Rule} {c c' : Cfg} (h0 : c.1 = c'.1) (h1 : c.2.1 = 0 ↔ c'.2.1 = 0)
    (h2 : c.2.2 = 0 ↔ c'.2.2 = 0) : ρ.Fires c ↔ ρ.Fires c' := by
  obtain ⟨s, a, b⟩ := c
  obtain ⟨s', a', b'⟩ := c'
  simp only at h0 h1 h2
  subst h0
  unfold Rule.Fires
  simp only
  have k1 : ρ.t₁.ok a = ρ.t₁.ok a' := by
    cases ρ.t₁ <;> simp [Test.ok] <;> omega
  have k2 : ρ.t₂.ok b = ρ.t₂.ok b' := by
    cases ρ.t₂ <;> simp [Test.ok] <;> omega
  have k3 : (0 ≤ (a : ℤ) + ρ.d₁.val ↔ 0 ≤ (a' : ℤ) + ρ.d₁.val) := by
    cases ρ.d₁ <;> simp [Move.val] <;> omega
  have k4 : (0 ≤ (b : ℤ) + ρ.d₂.val ↔ 0 ≤ (b' : ℤ) + ρ.d₂.val) := by
    cases ρ.d₂ <;> simp [Move.val] <;> omega
  rw [k1, k2, k3, k4]

theorem Move.val_le (d : Move) : d.val ≤ 1 := by cases d <;> simp [Move.val]

theorem Move.neg_one_le_val (d : Move) : -1 ≤ d.val := by cases d <;> simp [Move.val]

theorem not_isSource_of_congr {R : List Rule} {c c' : Cfg} (h0 : c.1 = c'.1)
    (h1 : min c.2.1 2 = min c'.2.1 2) (h2 : min c.2.2 2 = min c'.2.2 2)
    (h : ¬ IsSource R c) : ¬ IsSource R c' := by
  simp only [IsSource, not_forall, not_not] at h ⊢
  obtain ⟨d, hd⟩ := h
  unfold step at hd
  cases hF : R.find? (fun ρ => decide (ρ.Fires d)) with
  | none => rw [hF] at hd; cases hd
  | some ρ =>
    rw [hF] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    have hf := List.find?_some hF
    simp only [decide_eq_true_eq] at hf
    obtain ⟨-, -, -, f1, f2⟩ := id hf
    have e1 := Move.val_le ρ.d₁
    have e2 := Move.val_le ρ.d₂
    have e1' := Move.neg_one_le_val ρ.d₁
    have e2' := Move.neg_one_le_val ρ.d₂
    subst hd
    simp only [Rule.target] at h0 h1 h2
    set d' : Cfg := (d.1, ((c'.2.1 : ℤ) - ρ.d₁.val).toNat, ((c'.2.2 : ℤ) - ρ.d₂.val).toNat)
    have hfc : ∀ ρ' : Rule, ρ'.Fires d ↔ ρ'.Fires d' := fun ρ' =>
      fires_congr rfl (by simp only [d']; omega) (by simp only [d']; omega)
    refine ⟨d', ?_⟩
    unfold step
    have hfind : R.find? (fun ρ => decide (ρ.Fires d')) =
        R.find? (fun ρ => decide (ρ.Fires d)) := by
      congr 1; funext ρ'; simp [hfc ρ']
    rw [hfind, hF]
    obtain ⟨c0, c1, c2⟩ := c'
    simp only [Option.map_some, Rule.target, d', Option.some.injEq, Prod.mk.injEq] at h0 h1 h2 ⊢
    exact ⟨h0, by omega, by omega⟩

theorem isSource_congr {R : List Rule} {c c' : Cfg} (h0 : c.1 = c'.1)
    (h1 : min c.2.1 2 = min c'.2.1 2) (h2 : min c.2.2 2 = min c'.2.2 2) :
    IsSource R c ↔ IsSource R c' := by
  constructor
  · intro h; by_contra h'; exact not_isSource_of_congr h0.symm h1.symm h2.symm h' h
  · intro h; by_contra h'; exact not_isSource_of_congr h0 h1 h2 h' h

/-- Valuations capped at `K` agree on integers congruent mod `p^K`. -/
theorem min_padicValInt_le {p : ℕ} [Fact p.Prime] {n n' : ℤ} (hn' : n' ≠ 0) {K : ℕ}
    (h : (p : ℤ) ^ K ∣ n - n') : min (padicValInt p n) K ≤ min (padicValInt p n') K := by
  have hm : (p : ℤ) ^ min (padicValInt p n) K ∣ n :=
    (pow_dvd_pow _ (min_le_left _ _)).trans (padicValInt_dvd n)
  have hm' : (p : ℤ) ^ min (padicValInt p n) K ∣ n' := by
    have := dvd_sub hm ((pow_dvd_pow _ (min_le_right _ _)).trans h)
    rwa [sub_sub_cancel] at this
  have := ((padicValInt_dvd_iff _ n').1 hm').resolve_left hn'
  exact le_min this (min_le_right _ _)

theorem min_padicValInt_eq {p : ℕ} [Fact p.Prime] {n n' : ℤ} (hn : n ≠ 0) (hn' : n' ≠ 0)
    {K : ℕ} (h : (p : ℤ) ^ K ∣ n - n') : min (padicValInt p n) K = min (padicValInt p n') K :=
  le_antisymm (min_padicValInt_le hn' h)
    (min_padicValInt_le hn (by rw [← neg_sub]; exact (dvd_neg).2 h))

theorem min_div_two (v N : ℕ) (hN : 0 < N) : min (v / N) 2 = min v (2 * N) / N := by
  rcases le_or_gt (2 * N) v with h | h
  · rw [min_eq_right h, Nat.mul_div_cancel _ hN, min_eq_right]
    exact (Nat.le_div_iff_mul_le hN).2 h
  · rw [min_eq_left h.le, min_eq_left]
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hN).2 (by omega))

theorem hwModulus_dvd (j : ℕ) :
    (5 : ℤ) ^ j ∣ hwModulus j ∧ (2 : ℤ) ^ (2 * N j) ∣ hwModulus j ∧
      (3 : ℤ) ^ (3 * N j) ∣ hwModulus j := by
  refine ⟨⟨2 ^ (2 * N j) * 3 ^ (3 * N j), ?_⟩, ⟨5 ^ j * 3 ^ (3 * N j), ?_⟩,
    ⟨5 ^ j * 2 ^ (2 * N j), ?_⟩⟩ <;> simp [hwModulus] <;> ring

theorem inEngine_of_modEq {j : ℕ} (hj : 1 ≤ j) {n n' : ℤ} (h : n ≡ n' [ZMOD hwModulus j])
    (hn : InEngine j n) : InEngine j n' ∧ phase j n' = phase j n := by
  obtain ⟨h5, -, h3⟩ := hwModulus_dvd j
  have hcast : (n : ZMod (5 ^ j)) = n' := by
    have := (Int.ModEq.of_dvd h5 h)
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 (by exact_mod_cast this)
  have hph : phase j n' = phase j n := by rw [phase, phase, hcast]
  have h5' : ¬ (5 : ℤ) ∣ n' := by
    intro hd
    apply hn.2.1
    have : (5 : ℤ) ∣ n - n' := (dvd_pow_self 5 (by omega)).trans
      (h5.trans (Int.ModEq.dvd h.symm))
    have := dvd_add this hd
    rwa [sub_add_cancel] at this
  have hn' : n' ≠ 0 := by rintro rfl; exact h5' (dvd_zero _)
  have hv := min_padicValInt_eq (p := 3) hn.1 hn' (K := 3 * N j)
    (by exact_mod_cast h3.trans (Int.ModEq.dvd h.symm))
  have hlt := phase_lt hj hn
  refine ⟨⟨hn', h5', by rw [hph, hn.2.2.1, hcast], ?_⟩, hph⟩
  have h4 := hn.2.2.2
  rw [hph]
  unfold v3 at h4 ⊢
  omega

theorem line_of_modEq {j : ℕ} (hj : 1 ≤ j) {R : List Rule} {n n' : ℤ}
    (h : n ≡ n' [ZMOD hwModulus j]) (hn : n ∈ Line j R) : n' ∈ Line j R := by
  rcases hn with hn | hn
  · left; intro hn'; exact hn (inEngine_of_modEq hj h.symm hn').1
  by_cases hE : InEngine j n
  · obtain ⟨hE', hph⟩ := inEngine_of_modEq hj h hE
    right
    obtain ⟨-, h2, h3⟩ := hwModulus_dvd j
    have hd : (hwModulus j : ℤ) ∣ n - n' := Int.ModEq.dvd h.symm
    have hv2 := min_padicValInt_eq (p := 2) hE.1 hE'.1 (K := 2 * N j)
      (by exact_mod_cast h2.trans hd)
    have hv3 := min_padicValInt_eq (p := 3) hE.1 hE'.1 (K := 3 * N j)
      (by exact_mod_cast h3.trans hd)
    have hN := N_pos j
    have hlt := phase_lt hj hE
    refine (isSource_congr (c := decode j n) (c' := decode j n') hph.symm ?_ ?_).1 hn
    · show min (C1 j n) 2 = min (C1 j n') 2
      rw [C1, C1, min_div_two _ _ hN, min_div_two _ _ hN]
      unfold v2; rw [hv2]
    · show min (C2 j n) 2 = min (C2 j n') 2
      rw [C2, C2, min_div_two _ _ hN, min_div_two _ _ hN, hph]
      unfold v3 at hv3 ⊢
      congr 1
      omega
  · left
    intro hE'
    exact hE (inEngine_of_modEq hj h.symm hE').1

theorem hwModulus_pos (j : ℕ) : 0 < hwModulus j := by
  unfold hwModulus; positivity

theorem highwayAt_eq (j : ℕ) (R : List Rule) : highwayAt j R =
    (((List.range (hwModulus j)).map (fun a : ℕ => (a : ℤ))).filter fun r =>
      !decide (InEngine j r) || isSourceB R (decode j r)).map fun r => (r, (hwModulus j : ℤ)) := by
  unfold highwayAt
  congr 2
  exact List.map_eq_flatMap.symm

/-- `highwayAt j R` is a highway. -/
theorem isHighway_highwayAt {j : ℕ} (hj : 1 ≤ j) (R : List Rule) :
    IsHighway j R (highwayAt j R) := by
  have hL := hwModulus_pos j
  have hpred : ∀ r : ℤ, ((!decide (InEngine j r) || isSourceB R (decode j r)) = true
      ↔ r ∈ Line j R) := by
    intro r
    simp [Line, isSourceB_iff]
  rw [highwayAt_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnil
    have : (0, (hwModulus j : ℤ)) ∈ ((((List.range (hwModulus j)).map (fun a : ℕ => (a : ℤ))).filter
        fun r => !decide (InEngine j r) || isSourceB R (decode j r)).map
          fun r => (r, (hwModulus j : ℤ))) := by
      simp only [List.mem_map, List.mem_filter, List.mem_range]
      exact ⟨0, ⟨⟨0, hL, rfl⟩, (hpred 0).2 (Or.inl fun h => h.1 rfl)⟩, rfl⟩
    rw [hnil] at this; cases this
  · intro rm hrm
    simp only [List.mem_map] at hrm
    obtain ⟨r, -, rfl⟩ := hrm
    exact ⟨2 * N j, 3 * N j, by simp [hwModulus]⟩
  · refine List.Pairwise.map (R := fun a b : ℤ => ∀ n : ℤ, ¬ (n ≡ a [ZMOD hwModulus j] ∧
      n ≡ b [ZMOD hwModulus j])) _ (fun a b h => h) (List.Pairwise.filter _ ?_)
    have hlt : List.Pairwise (fun a b : ℤ => a < b)
        ((List.range (hwModulus j)).map (fun a : ℕ => (a : ℤ))) :=
      List.Pairwise.map _ (fun a b h => by exact_mod_cast h) List.pairwise_lt_range
    refine hlt.imp_of_mem fun {a b} ha hb hab n ⟨hna, hnb⟩ => ?_
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have := hna.symm.trans hnb
    unfold Int.ModEq at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  · intro n
    have hL' : (0 : ℤ) < hwModulus j := by exact_mod_cast hL
    simp only [List.mem_map, List.mem_filter, List.mem_range, InClass]
    constructor
    · intro hn
      refine ⟨_, ⟨n % hwModulus j, ⟨⟨(n % hwModulus j).toNat, ?_, ?_⟩, ?_⟩, rfl⟩, ?_⟩
      · have := Int.emod_lt_of_pos n hL'; omega
      · exact Int.toNat_of_nonneg (Int.emod_nonneg _ hL'.ne')
      · exact (hpred _).2 (line_of_modEq hj (Int.mod_modEq n _).symm hn)
      · exact (Int.mod_modEq n _).symm
    · rintro ⟨_, ⟨r, ⟨-, hr⟩, rfl⟩, hin⟩
      exact line_of_modEq hj hin.symm ((hpred r).1 hr)

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

/-- `InEngine` and the phase are constant mod any `Q` that `5^j` and `3^N` divide. -/
theorem inEngine_of_dvd {j : ℕ} (hj : 1 ≤ j) {Q n n' : ℤ} (h5 : (5 : ℤ) ^ j ∣ Q)
    (h3 : (3 : ℤ) ^ N j ∣ Q) (h : Q ∣ n - n') (hn : InEngine j n) :
    InEngine j n' ∧ phase j n' = phase j n := by
  have hcast : (n : ZMod (5 ^ j)) = n' := by
    have : n ≡ n' [ZMOD 5 ^ j] := (Int.modEq_iff_dvd.2 (by
      rw [← neg_sub]; exact (dvd_neg).2 (h5.trans h)))
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 (by exact_mod_cast this)
  have hph : phase j n' = phase j n := by rw [phase, phase, hcast]
  have h5' : ¬ (5 : ℤ) ∣ n' := by
    intro hd
    apply hn.2.1
    have : (5 : ℤ) ∣ n - n' := (dvd_pow_self 5 (by omega)).trans (h5.trans h)
    have := dvd_add this hd
    rwa [sub_add_cancel] at this
  have hn' : n' ≠ 0 := by rintro rfl; exact h5' (dvd_zero _)
  have hv := min_padicValInt_eq (p := 3) hn.1 hn' (K := N j) (by exact_mod_cast h3.trans h)
  have hlt := phase_lt hj hn
  refine ⟨⟨hn', h5', by rw [hph, hn.2.2.1, hcast], ?_⟩, hph⟩
  have h4 := hn.2.2.2
  rw [hph]
  unfold v3 at h4 ⊢
  omega

theorem dvd_iff_of_dvd_sub {Q n n' d : ℤ} (hd : d ∣ Q) (h : Q ∣ n - n') : d ∣ n ↔ d ∣ n' := by
  have h' := hd.trans h
  constructor
  · intro hn; have := dvd_sub hn h'; rwa [sub_sub_cancel] at this
  · intro hn; have := dvd_add h' hn; rwa [sub_add_cancel] at this

/-- On the engine, the firing pattern is constant mod `Q` when `5^j 2^N 3^{2N} ∣ Q`. -/
theorem decode_class {j : ℕ} (hj : 1 ≤ j) {Q n n' : ℤ}
    (hQ : (5 : ℤ) ^ j * 2 ^ N j * 3 ^ (2 * N j) ∣ Q) (h : Q ∣ n - n') (hn : InEngine j n) :
    InEngine j n' ∧ (decode j n').1 = (decode j n).1 ∧
      ((decode j n').2.1 = 0 ↔ (decode j n).2.1 = 0) ∧
      ((decode j n').2.2 = 0 ↔ (decode j n).2.2 = 0) := by
  have h5 : (5 : ℤ) ^ j ∣ Q := (Dvd.intro (2 ^ N j * 3 ^ (2 * N j)) (by ring)).trans hQ
  have h2 : (2 : ℤ) ^ N j ∣ Q := (Dvd.intro (5 ^ j * 3 ^ (2 * N j)) (by ring)).trans hQ
  have h33 : (3 : ℤ) ^ (2 * N j) ∣ Q := (Dvd.intro_left _ rfl).trans hQ
  have h3 : (3 : ℤ) ^ N j ∣ Q := (pow_dvd_pow 3 (by omega)).trans h33
  obtain ⟨hn', hph⟩ := inEngine_of_dvd hj h5 h3 h hn
  have hlt := phase_lt hj hn
  refine ⟨hn', hph, ?_, ?_⟩
  · show C1 j n' = 0 ↔ C1 j n = 0
    have e : 1 ≤ C1 j n' ↔ 1 ≤ C1 j n := by
      rw [one_le_C1_iff hj hn', one_le_C1_iff hj hn]; exact (dvd_iff_of_dvd_sub h2 h).symm
    omega
  · show C2 j n' = 0 ↔ C2 j n = 0
    have e : 1 ≤ C2 j n' ↔ 1 ≤ C2 j n := by
      rw [one_le_C2_iff hj hn', one_le_C2_iff hj hn, hph]
      exact (dvd_iff_of_dvd_sub ((pow_dvd_pow 3 (by omega)).trans h33) h).symm
    omega

theorem hwIdx_congr {hw : List (ℤ × ℤ)} {L x y : ℤ} (hhw : ∀ rm ∈ hw, rm.2 ∣ L)
    (h : L ∣ x - y) : hwIdx hw x = hwIdx hw y := by
  unfold hwIdx
  induction hw with
  | nil => rfl
  | cons rm t ih =>
    have hm : x % rm.2 = y % rm.2 := Int.emod_eq_emod_iff_emod_sub_eq_zero.2
      (Int.emod_eq_zero_of_dvd ((hhw rm List.mem_cons_self).trans h))
    rw [List.findIdx_cons, List.findIdx_cons, hm,
      ih fun rm' h' => hhw rm' (List.mem_cons_of_mem _ h')]

theorem hwPoint_mul_add {hw : List (ℤ × ℤ)} (q : ℤ) {i : ℕ} (hi : i < hw.length) :
    hwPoint hw (hw.length * q + i) = hw[i].1 + hw[i].2 * q := by
  have hk : (0 : ℤ) < hw.length := by omega
  have hmod : (hw.length * q + i) % hw.length = i := by
    rw [Int.mul_add_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hdiv : (hw.length * q + i) / hw.length = q := by
    rw [Int.mul_add_ediv_left _ _ (by omega),
      Int.ediv_eq_zero_of_lt (a := (i : ℤ)) (by omega) (by omega), add_zero]
  rw [hwPoint, hmod, hdiv, Int.toNat_natCast, List.getD_eq_getElem _ _ hi]

theorem IsHighway.ratio {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw)
    {rm rm' : ℤ × ℤ} (hrm : rm ∈ hw) (hrm' : rm' ∈ hw) :
    ∃ α β : ℤ, (rm'.2 : ℚ) / rm.2 = (2 : ℚ) ^ α * (3 : ℚ) ^ β := by
  obtain ⟨a, b, he⟩ := h.modulus rm hrm
  obtain ⟨a', b', he'⟩ := h.modulus rm' hrm'
  refine ⟨(a' : ℤ) - a, (b' : ℤ) - b, ?_⟩
  rw [he, he', zpow_sub₀ (by norm_num), zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast,
    zpow_natCast, zpow_natCast]
  push_cast
  field_simp

/-- `hwNext` is affine with a `{2,3}` slope on each class of the highway. -/
theorem hwNext_affine {j : ℕ} {R : List Rule} {hw : List (ℤ × ℤ)} (h : IsHighway j R hw)
    {i : ℕ} (hi : i < hw.length) :
    ∃ a b c : ℤ, c ≠ 0 ∧ (∃ α β : ℤ, (a : ℚ) / c = (2 : ℚ) ^ α * (3 : ℚ) ^ β) ∧
      ∀ x, hwIdx hw x = i → c * hwNext hw x = a * x + b := by
  have hm := h.mod_pos (List.getElem_mem hi)
  have hpos : ∀ x, hwIdx hw x = i →
      hwPos hw x = hw.length * ((x - hw[i].1) / hw[i].2) + i ∧ hw[i].2 ∣ x - hw[i].1 := by
    intro x hx
    have hcl : InClass hw[hwIdx hw x] x := (inClass_iff _ _).2
      (List.findIdx_getElem (w := hx ▸ hi))
    simp only [hx] at hcl
    refine ⟨?_, Int.ModEq.dvd hcl.symm⟩
    rw [hwPos, hx, List.getD_eq_getElem _ _ hi]
  rcases lt_or_ge (i + 1) hw.length with hi1 | hi1
  · obtain ⟨α, β, hr⟩ := h.ratio (List.getElem_mem hi) (List.getElem_mem hi1)
    refine ⟨hw[i + 1].2, hw[i].2 * hw[i + 1].1 - hw[i + 1].2 * hw[i].1, hw[i].2, hm.ne', ⟨α, β, hr⟩,
      fun x hx => ?_⟩
    obtain ⟨hp, hd⟩ := hpos x hx
    rw [hwNext, hp, add_assoc, show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; rfl,
      hwPoint_mul_add _ hi1]
    obtain ⟨t, ht⟩ := hd
    rw [ht, Int.mul_ediv_cancel_left _ hm.ne']
    linear_combination (-hw[i + 1].2) * ht
  · have h0 : 0 < hw.length := h.length_pos
    have hik : i + 1 = hw.length := by omega
    obtain ⟨α, β, hr⟩ := h.ratio (List.getElem_mem hi) (List.getElem_mem h0)
    refine ⟨hw[0].2, hw[i].2 * hw[0].1 - hw[0].2 * hw[i].1 + hw[i].2 * hw[0].2, hw[i].2, hm.ne',
      ⟨α, β, hr⟩, fun x hx => ?_⟩
    obtain ⟨hp, hd⟩ := hpos x hx
    have he : hwPos hw x + 1 = hw.length * ((x - hw[i].1) / hw[i].2 + 1) + ((0 : ℕ) : ℤ) := by
      rw [hp]; push_cast; rw [show ((hw.length : ℕ) : ℤ) = (i : ℤ) + 1 by exact_mod_cast hik.symm]
      ring
    rw [hwNext, he, hwPoint_mul_add _ h0]
    obtain ⟨t, ht⟩ := hd
    rw [ht, Int.mul_ediv_cancel_left _ hm.ne']
    linear_combination (-hw[0].2) * ht

theorem find_fires_congr {R : List Rule} {c c' : Cfg} (h : ∀ ρ : Rule, ρ.Fires c ↔ ρ.Fires c') :
    R.find? (fun ρ => decide (ρ.Fires c)) = R.find? (fun ρ => decide (ρ.Fires c')) := by
  congr 1; funext ρ; simp [h ρ]

theorem sigma_of_F_some {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} {n m : ℤ}
    (hF : F j M.rules n = some m) : sigma j M hw n = m := by
  simp [sigma, hF]

theorem sigma_of_sink {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} {n : ℤ} (hn : InEngine j n)
    (hF : F j M.rules n = none) :
    sigma j M hw n = hwNext hw (move j n (M.pairFn (phase j n)) 0 0) := by
  simp [sigma, hF, hn]

theorem sigma_of_not_inEngine {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} {n : ℤ}
    (hn : ¬ InEngine j n) : sigma j M hw n = hwNext hw n := by
  simp [sigma, F_of_not_inEngine j M.rules hn, hn]

theorem F_of_find {j : ℕ} {R : List Rule} {n : ℤ} (hn : InEngine j n) :
    F j R n = (R.find? fun ρ => decide (ρ.Fires (decode j n))).map fun ρ =>
      move j n ρ.dst ρ.d₁.val ρ.d₂.val := by
  simp [F, hn]

/-- `σ` is RCWA with all slopes in `2^ℤ 3^ℤ`, at modulus `3^N · L` for any `L > 0`
that the highway moduli and `5^j 2^N 3^{2N}` (the zero tests) divide. -/
theorem isRcwa23At_sigma {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)} (h : Good j M hw) {L : ℕ}
    (hL : 0 < L) (hhw : ∀ rm ∈ hw, rm.2 ∣ L) (htest : 5 ^ j * 2 ^ N j * 3 ^ (2 * N j) ∣ L) :
    IsRcwa23At (3 ^ N j * L) (sigma j M hw) := by
  have hj := h.one_le
  intro r
  have hLQ : (L : ℤ) ∣ ((3 ^ N j * L : ℕ) : ℤ) := by push_cast; exact Dvd.intro_left _ rfl
  have hQt : (5 : ℤ) ^ j * 2 ^ N j * 3 ^ (2 * N j) ∣ ((3 ^ N j * L : ℕ) : ℤ) :=
    (by exact_mod_cast htest : ((5 ^ j * 2 ^ N j * 3 ^ (2 * N j) : ℕ) : ℤ) ∣ (L : ℤ)).trans hLQ
  have hcls : ∀ n, n ≡ r [ZMOD ((3 ^ N j * L : ℕ) : ℤ)] → ((3 ^ N j * L : ℕ) : ℤ) ∣ r - n :=
    fun n hn => Int.ModEq.dvd hn
  have hhwL : ∀ rm ∈ hw, rm.2 ∣ (L : ℤ) := hhw
  by_cases hr : InEngine j r
  · have hfr : ∀ n, n ≡ r [ZMOD ((3 ^ N j * L : ℕ) : ℤ)] → InEngine j n ∧
        phase j n = phase j r ∧ M.rules.find? (fun ρ => decide (ρ.Fires (decode j n))) =
          M.rules.find? (fun ρ => decide (ρ.Fires (decode j r))) ∧
        ∀ ρ : Rule, ρ.Fires (decode j n) ↔ ρ.Fires (decode j r) := by
      intro n hn
      obtain ⟨hnE, hd0, hd1, hd2⟩ := decode_class hj hQt (hcls n hn) hr
      have hfc : ∀ ρ : Rule, ρ.Fires (decode j n) ↔ ρ.Fires (decode j r) :=
        fun ρ => fires_congr hd0 hd1 hd2
      exact ⟨hnE, hd0, find_fires_congr hfc, hfc⟩
    cases hF : M.rules.find? (fun ρ => decide (ρ.Fires (decode j r))) with
    | some ρ =>
      have hρ := List.mem_of_find?_eq_some hF
      have hfρ := List.find?_some hF
      simp only [decide_eq_true_eq] at hfρ
      set A : ℤ := (N j : ℤ) * ρ.d₁.val
      set B : ℤ := (N j : ℤ) * ρ.d₂.val + ρ.dst - phase j r
      refine ⟨2 ^ A.toNat * 3 ^ B.toNat, 0, 2 ^ (-A).toNat * 3 ^ (-B).toNat, by positivity,
        ⟨A, B, ?_⟩, fun n hn => ?_⟩
      · push_cast
        rw [zpow_toNat 2 (by norm_num), zpow_toNat 3 (by norm_num)]
        field_simp
      · obtain ⟨hnE, hph, hfind, hfc⟩ := hfr n hn
        have hfn := (hfc ρ).2 hfρ
        obtain ⟨-, -, -, h₁, h₂⟩ := hfn
        have hs := scale_spec hj hnE (h.fitsR ρ hρ).2 h₁ h₂
        rw [sigma_of_F_some (m := move j n ρ.dst ρ.d₁.val ρ.d₂.val)
          (by rw [F_of_find hnE, hfind, hF]; rfl)]
        rw [hph] at hs
        unfold move
        rw [hph]
        linear_combination hs
    | none =>
      set s'' := M.pairFn (phase j r)
      have hs'' : s'' < orderOf (3 : ZMod (5 ^ j)) := h.pairFn_lt_ord (phase_lt_ord hj hr)
      set E : ℤ := (s'' : ℤ) - phase j r
      -- the relabelled point `τ n` and its exact relation `τ n · 3^{E⁻} = n · 3^{E⁺}`
      have hτ : ∀ n, InEngine j n → phase j n = phase j r →
          move j n s'' 0 0 * 3 ^ (-E).toNat = n * 3 ^ E.toNat := by
        intro n hnE hph
        have hs := scale_spec hj hnE hs'' (δ₁ := 0) (δ₂ := 0) (by omega) (by omega)
        rw [hph] at hs
        unfold move
        rw [hph]
        simp only [mul_zero, neg_zero, Int.toNat_zero, pow_zero, mul_one, zero_add] at hs ⊢
        exact hs
      have hrL : move j r s'' 0 0 ∈ Line j M.rules := by
        obtain ⟨-, hd, -⟩ := decode_move_zero hj hr hs''
        right
        rw [hd]
        have hsink : IsSink M.rules (decode j r) := by simp [IsSink, step, hF]
        exact (h.pair_sink (decode j r)).1 hsink
      obtain ⟨rm, hrm, hin⟩ := (h.highway.cover _).1 hrL
      have hi : hwIdx hw (move j r s'' 0 0) < hw.length :=
        List.findIdx_lt_length_of_exists ⟨rm, hrm, (inClass_iff _ _).1 hin⟩
      obtain ⟨a, b, c, hc, ⟨α, β, hab⟩, hx⟩ := hwNext_affine h.highway hi
      refine ⟨a * 3 ^ E.toNat, 3 ^ (-E).toNat * b, 3 ^ (-E).toNat * c, by positivity,
        ⟨α, β + E, ?_⟩, fun n hn => ?_⟩
      · push_cast
        rw [zpow_add₀ (by norm_num), zpow_toNat 3 (by norm_num) E]
        have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
        rw [show (a : ℚ) * 3 ^ E.toNat / (3 ^ (-E).toNat * c) =
          (a / c) * (3 ^ E.toNat / 3 ^ (-E).toNat) by field_simp, hab]
        ring
      · obtain ⟨hnE, hph, hfind, -⟩ := hfr n hn
        have hFn : F j M.rules n = none := by rw [F_of_find hnE, hfind, hF]; rfl
        rw [sigma_of_sink hnE hFn, hph]
        have hEle : (-E).toNat ≤ N j := by have := phase_lt hj hr; omega
        have hidx : hwIdx hw (move j n s'' 0 0) = hwIdx hw (move j r s'' 0 0) := by
          apply hwIdx_congr hhwL
          have h1 := hτ n hnE hph
          have h2 := hτ r hr rfl
          have hd : ((3 : ℤ) ^ (-E).toNat * (3 ^ (N j - (-E).toNat) * L)) ∣
              3 ^ (-E).toNat * (move j n s'' 0 0 - move j r s'' 0 0) := by
            have hdiv : ((3 ^ N j * L : ℕ) : ℤ) ∣ 3 ^ E.toNat * (n - r) :=
              (dvd_neg.2 (hcls n hn) |>.trans (by rw [neg_sub])).mul_left _
            rw [show (3 : ℤ) ^ (-E).toNat * (move j n s'' 0 0 - move j r s'' 0 0) =
              3 ^ E.toNat * (n - r) by linear_combination h1 - h2]
            refine (dvd_of_eq ?_).trans hdiv
            push_cast
            rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hEle]
          exact (Dvd.intro_left _ rfl).trans
            ((mul_dvd_mul_iff_left (by positivity)).1 hd)
        have := hx _ hidx
        linear_combination (3 : ℤ) ^ (-E).toNat * this + a * hτ n hnE hph
  · obtain ⟨rm, hrm, hin⟩ := (h.highway.cover r).1 (Or.inl hr)
    have hi : hwIdx hw r < hw.length :=
      List.findIdx_lt_length_of_exists ⟨rm, hrm, (inClass_iff _ _).1 hin⟩
    obtain ⟨a, b, c, hc, hab, hx⟩ := hwNext_affine h.highway hi
    refine ⟨a, b, c, hc, hab, fun n hn => ?_⟩
    have hnE : ¬ InEngine j n := fun hnE =>
      hr (decode_class hj hQt (by rw [← neg_sub]; exact dvd_neg.2 (hcls n hn)) hnE).1
    rw [sigma_of_not_inEngine hnE]
    exact hx n (hwIdx_congr hhwL (by rw [← neg_sub]; exact dvd_neg.2 (hLQ.trans (hcls n hn))))

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

/-- A valid machine is good at its level with its highway. -/
theorem good_of_valid {M : Machine} (hM : M.Valid) : Good (level M) M (highwayOf M) := by
  have h1 : 1 ≤ level M := by simp [level]
  exact ⟨h1, (Nat.le_succ _).trans (le_orderOf_three h1), hM.wf, hM.rev, hM.pair_sink,
    isHighway_highwayAt h1 M.rules⟩

/-- For a valid machine, `tableOf M` is an exact table for `σ`. -/
theorem tableOf_spec {M : Machine} (hM : M.Valid) :
    (tableOf M).Exact ∧ (tableOf M).eval = sigma (level M) M (highwayOf M) := by
  have hG := good_of_valid hM
  have hL := hwModulus_pos (level M)
  refine tableFrom_spec (by positivity) (isRcwa23At_sigma hG hL ?_ ?_)
  · intro rm hrm
    rw [highwayOf, highwayAt_eq, List.mem_map] at hrm
    obtain ⟨r, -, rfl⟩ := hrm
    exact dvd_rfl
  · unfold hwModulus
    exact mul_dvd_mul (mul_dvd_mul_left _ (pow_dvd_pow _ (by omega))) (pow_dvd_pow _ (by omega))

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

/-! ### Primitive recursion on `ℤ` (transported through `(a, b) ↦ a − b`) -/

namespace PrimInt
open Encodable Denumerable

theorem encode_ofNat' (n : ℕ) : encode (n : ℤ) = 2 * n := by
  show Equiv.intEquivNat _ = _
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat]; rfl

theorem encode_negSucc (n : ℕ) : encode (Int.negSucc n) = 2 * n + 1 := by
  show Equiv.intEquivNat _ = _
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat]

theorem ofNat_two_mul (k : ℕ) : ofNat ℤ (2 * k) = k := by
  rw [← encode_ofNat', ofNat_encode]

theorem ofNat_two_mul_add_one (k : ℕ) : ofNat ℤ (2 * k + 1) = Int.negSucc k := by
  rw [← encode_negSucc, ofNat_encode]

/-- The positive part. -/
theorem int_toNat : Primrec Int.toNat := by
  refine (Primrec.cond (Primrec.nat_bodd.comp Primrec.encode) (Primrec.const 0)
    (Primrec.nat_div2.comp Primrec.encode)).of_eq fun z => ?_
  rcases z with n | n
  · simp [encode_ofNat']
  · simp [encode_negSucc]

/-- The negative part. -/
theorem int_negPart : Primrec fun z : ℤ => (-z).toNat := by
  refine (Primrec.cond (Primrec.nat_bodd.comp Primrec.encode)
    (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode)) (Primrec.const 0)).of_eq fun z => ?_
  rcases z with n | n
  · simp [encode_ofNat']
  · rw [encode_negSucc]; simp [Int.negSucc_eq]

/-- `(a, b) ↦ a − b` into `ℤ`. -/
theorem int_natSub : Primrec₂ fun a b : ℕ => (a : ℤ) - b := by
  refine ((Primrec.ofNat ℤ).comp (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1))))))
    |>.of_eq fun ⟨a, b⟩ => ?_
  dsimp only
  split_ifs with h
  · rw [ofNat_two_mul]; push_cast [h]; ring
  · rw [ofNat_two_mul_add_one, Int.negSucc_eq]; push_cast [show 1 ≤ b - a by omega]
    have : b - a - 1 + 1 = b - a := by omega
    omega

theorem of_parts {α : Type*} [Primcodable α] {f : α → ℤ} (h1 : Primrec fun a => (f a).toNat)
    (h2 : Primrec fun a => (-f a).toNat) : Primrec f :=
  (int_natSub.comp h1 h2).of_eq fun a => by omega

theorem int_natCast : Primrec (fun n : ℕ => (n : ℤ)) :=
  (int_natSub.comp Primrec.id (Primrec.const 0)).of_eq fun n => by simp

theorem int_add : Primrec₂ (· + · : ℤ → ℤ → ℤ) :=
  (int_natSub.comp (Primrec.nat_add.comp (int_toNat.comp Primrec.fst) (int_toNat.comp Primrec.snd))
    (Primrec.nat_add.comp (int_negPart.comp Primrec.fst) (int_negPart.comp Primrec.snd))).of_eq
    fun ⟨x, y⟩ => by dsimp only; push_cast; omega

theorem int_neg : Primrec (fun x : ℤ => -x) :=
  (int_natSub.comp int_negPart int_toNat).of_eq fun x => by omega

theorem int_sub : Primrec₂ (· - · : ℤ → ℤ → ℤ) :=
  (int_add.comp Primrec.fst (int_neg.comp Primrec.snd)).of_eq fun ⟨x, y⟩ => by
    dsimp only; ring

theorem int_mul : Primrec₂ (· * · : ℤ → ℤ → ℤ) := by
  refine (int_natSub.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (int_toNat.comp .fst) (int_toNat.comp .snd))
      (Primrec.nat_mul.comp (int_negPart.comp .fst) (int_negPart.comp .snd)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (int_toNat.comp .fst) (int_negPart.comp .snd))
      (Primrec.nat_mul.comp (int_negPart.comp .fst) (int_toNat.comp .snd)))).of_eq
    fun ⟨x, y⟩ => ?_
  dsimp only
  have hx : x = (x.toNat : ℤ) - ((-x).toNat : ℤ) := by omega
  have hy : y = (y.toNat : ℤ) - ((-y).toNat : ℤ) := by omega
  push_cast
  conv_rhs => rw [hx, hy]
  ring

theorem int_le : PrimrecRel (· ≤ · : ℤ → ℤ → Prop) :=
  (Primrec.nat_le.comp (Primrec.nat_add.comp (int_toNat.comp .fst) (int_negPart.comp .snd))
    (Primrec.nat_add.comp (int_toNat.comp .snd) (int_negPart.comp .fst))).of_eq fun ⟨x, y⟩ => by
    dsimp only; omega


/-- Division by a natural number, by cases on the sign. -/
theorem ediv_natCast_eq (x : ℤ) (n : ℕ) : x / (n : ℤ) =
    if n = 0 then 0 else if 0 ≤ x then ((x.toNat / n : ℕ) : ℤ)
      else -((((-x).toNat - 1) / n : ℕ) : ℤ) - 1 := by
  split_ifs with h0 hx
  · subst h0; simp
  · conv_lhs => rw [← Int.toNat_of_nonneg hx]
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, x = Int.negSucc m := ⟨(-x).toNat - 1, by omega⟩
    rw [Int.negSucc_ediv m (by omega)]
    have : (-Int.negSucc m).toNat - 1 = m := by rw [Int.negSucc_eq]; omega
    rw [this]
    push_cast
    rw [show (Int.ediv m n) = (m : ℤ) / (n : ℤ) from rfl]
    ring

theorem int_ediv_nat : Primrec₂ fun (x : ℤ) (n : ℕ) => x / (n : ℤ) := by
  refine (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (int_le.comp (Primrec.const 0) Primrec.fst)
      (int_natCast.comp (Primrec.nat_div.comp (int_toNat.comp Primrec.fst) Primrec.snd))
      (int_sub.comp (int_neg.comp (int_natCast.comp (Primrec.nat_div.comp
        (Primrec.nat_sub.comp (int_negPart.comp Primrec.fst) (Primrec.const 1)) Primrec.snd)))
        (Primrec.const 1)))).of_eq fun ⟨x, n⟩ => ?_
  dsimp only
  rw [ediv_natCast_eq]

theorem int_ediv : Primrec₂ (· / · : ℤ → ℤ → ℤ) := by
  refine (Primrec.ite (int_le.comp (Primrec.const 0) Primrec.snd)
    (int_ediv_nat.comp Primrec.fst (int_toNat.comp Primrec.snd))
    (int_neg.comp (int_ediv_nat.comp Primrec.fst (int_negPart.comp Primrec.snd)))).of_eq
    fun ⟨x, y⟩ => ?_
  dsimp only
  split_ifs with h
  · rw [Int.toNat_of_nonneg h]
  · rw [show ((-y).toNat : ℤ) = -y by omega, Int.ediv_neg, neg_neg]

theorem int_emod : Primrec₂ (· % · : ℤ → ℤ → ℤ) :=
  (int_sub.comp Primrec.fst (int_mul.comp Primrec.snd int_ediv)).of_eq fun ⟨x, y⟩ => by
    dsimp only; rw [Int.emod_def]

theorem int_dvd : PrimrecRel (· ∣ · : ℤ → ℤ → Prop) :=
  (Primrec.eq.comp (int_emod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    fun ⟨x, y⟩ => by dsimp only; rw [Int.dvd_iff_emod_eq_zero]

theorem nat_pow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) := by
  refine (Primrec.nat_iterate Primrec.snd (Primrec.const 1)
    (Primrec.nat_mul.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂).of_eq
    fun ⟨a, k⟩ => ?_
  dsimp only
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ]

/-- `find?` with a parameter. -/
theorem list_find? {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  refine (Primrec.list_foldr hf (Primrec.const none)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  dsimp only
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.find?_cons]; cases p a b <;> rfl

/-- `all` with a parameter. -/
theorem list_all {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  refine (Primrec.list_foldr hf (Primrec.const true)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)).to₂).of_eq fun a => ?_
  dsimp only
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.all_cons]; cases p a b <;> rfl


theorem padicValInt_eq_findGreatest (p : ℕ) [hp : Fact p.Prime] (n : ℤ) :
    padicValInt p n = Nat.findGreatest (fun k => (p : ℤ) ^ k ∣ n) n.natAbs := by
  by_cases hn : n = 0
  · subst hn; simp
  symm
  rw [Nat.findGreatest_eq_iff]
  have hd : (p : ℤ) ^ padicValInt p n ∣ n := padicValInt_dvd n
  refine ⟨?_, fun _ => hd, fun k hk _ hdk => ?_⟩
  · have h1 : p ^ padicValInt p n ∣ n.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hd
      simpa [Int.natAbs_pow] using this
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hn) h1
    exact ((Nat.lt_pow_self hp.out.one_lt).le).trans h2
  · have := ((padicValInt_dvd_iff k n).1 hdk).resolve_left hn
    omega

theorem int_natAbs : Primrec Int.natAbs :=
  (Primrec.nat_add.comp int_toNat int_negPart).of_eq fun n => by omega

theorem padicValInt_primrec (p : ℕ) [Fact p.Prime] : Primrec (padicValInt p) := by
  have hR : PrimrecRel (fun (n : ℤ) (k : ℕ) => ((p ^ k : ℕ) : ℤ) ∣ n) :=
    int_dvd.comp (int_natCast.comp (nat_pow.comp (Primrec.const p) Primrec.snd)) Primrec.fst
  refine (Primrec.nat_findGreatest int_natAbs hR).of_eq fun n => ?_
  rw [padicValInt_eq_findGreatest]
  push_cast
  rfl

end PrimInt

section Prim

open PrimInt
variable {α : Type*} [Primcodable α]

theorem pr_intPow (b : ℕ) {k : α → ℕ} (hk : Primrec k) :
    Primrec fun a => (b : ℤ) ^ k a :=
  (int_natCast.comp (nat_pow.comp (Primrec.const b) hk)).of_eq fun a => by push_cast; rfl

theorem pr_N {j : α → ℕ} (hj : Primrec j) : Primrec fun a => N (j a) :=
  Primrec.nat_mul.comp (Primrec.const 4)
    (nat_pow.comp (Primrec.const 5) (Primrec.nat_sub.comp hj (Primrec.const 1)))

theorem phase_eq (j : ℕ) (n : ℤ) : phase j n = ((List.range (N j)).find? fun k =>
    decide ((3 : ℤ) ^ k % (5 : ℤ) ^ j = n % (5 : ℤ) ^ j)).getD 0 := by
  unfold phase dlog3
  congr 2
  funext k
  have : ((3 : ZMod (5 ^ j)) ^ k = (n : ZMod (5 ^ j))) ↔
      ((3 : ℤ) ^ k % (5 : ℤ) ^ j = n % (5 : ℤ) ^ j) := by
    rw [show (3 : ZMod (5 ^ j)) ^ k = (((3 : ℤ) ^ k : ℤ) : ZMod (5 ^ j)) by push_cast; rfl,
      ZMod.intCast_eq_intCast_iff']
    push_cast; rfl
  simp only [this]

theorem pr_phase {j : α → ℕ} {n : α → ℤ} (hj : Primrec j) (hn : Primrec n) :
    Primrec fun a => phase (j a) (n a) := by
  have hp : Primrec₂ fun (a : α) (k : ℕ) =>
      decide ((3 : ℤ) ^ k % (5 : ℤ) ^ j a = n a % (5 : ℤ) ^ j a) :=
    (Primrec.eq.comp (int_emod.comp (pr_intPow 3 Primrec.snd) (pr_intPow 5 (hj.comp Primrec.fst)))
      (int_emod.comp (hn.comp Primrec.fst) (pr_intPow 5 (hj.comp Primrec.fst)))).decide
  refine (Primrec.option_getD.comp (list_find? (Primrec.list_range.comp (pr_N hj)) hp)
    (Primrec.const 0)).of_eq fun a => ?_
  rw [phase_eq]

theorem inEngine_iff_dec (j : ℕ) (n : ℤ) : InEngine j n ↔
    (n ≠ 0 ∧ ¬ (5 : ℤ) ∣ n ∧ (3 : ℤ) ^ phase j n % (5 : ℤ) ^ j = n % (5 : ℤ) ^ j ∧
      (3 : ℤ) ^ phase j n ∣ n) := by
  unfold InEngine
  have h1 : ((3 : ZMod (5 ^ j)) ^ phase j n = (n : ZMod (5 ^ j))) ↔
      ((3 : ℤ) ^ phase j n % (5 : ℤ) ^ j = n % (5 : ℤ) ^ j) := by
    rw [show (3 : ZMod (5 ^ j)) ^ phase j n = (((3 : ℤ) ^ phase j n : ℤ) : ZMod (5 ^ j)) by
      push_cast; rfl, ZMod.intCast_eq_intCast_iff']
    push_cast; rfl
  constructor
  · rintro ⟨h0, h5, h3, hv⟩
    exact ⟨h0, h5, h1.1 h3, by
      have := (padicValInt_dvd_iff (p := 3) (phase j n) n).2 (Or.inr hv)
      exact_mod_cast this⟩
  · rintro ⟨h0, h5, h3, hv⟩
    refine ⟨h0, h5, h1.2 h3, ?_⟩
    have := (padicValInt_dvd_iff (p := 3) (phase j n) n).1 (by exact_mod_cast hv)
    exact this.resolve_left h0

theorem pr_inEngine {j : α → ℕ} {n : α → ℤ} (hj : Primrec j) (hn : Primrec n) :
    Primrec fun a => decide (InEngine (j a) (n a)) := by
  have hph := pr_phase hj hn
  have h0 : PrimrecPred fun a => n a ≠ 0 := (Primrec.eq.comp hn (Primrec.const 0)).not
  have h5 : PrimrecPred fun a => ¬ (5 : ℤ) ∣ n a := (int_dvd.comp (Primrec.const 5) hn).not
  have h3 : PrimrecPred fun a => (3 : ℤ) ^ phase (j a) (n a) % (5 : ℤ) ^ j a =
      n a % (5 : ℤ) ^ j a :=
    Primrec.eq.comp (int_emod.comp (pr_intPow 3 hph) (pr_intPow 5 hj))
      (int_emod.comp hn (pr_intPow 5 hj))
  have hv : PrimrecPred fun a => (3 : ℤ) ^ phase (j a) (n a) ∣ n a :=
    int_dvd.comp (pr_intPow 3 hph) hn
  have := (h0.and (h5.and (h3.and hv))).of_eq fun a => (inEngine_iff_dec (j a) (n a)).symm
  exact this.decide

theorem pr_C1 {j : α → ℕ} {n : α → ℤ} (hj : Primrec j) (hn : Primrec n) :
    Primrec fun a => C1 (j a) (n a) :=
  Primrec.nat_div.comp ((padicValInt_primrec 2).comp hn) (pr_N hj)

theorem pr_C2 {j : α → ℕ} {n : α → ℤ} (hj : Primrec j) (hn : Primrec n) :
    Primrec fun a => C2 (j a) (n a) :=
  Primrec.nat_div.comp (Primrec.nat_sub.comp ((padicValInt_primrec 3).comp hn) (pr_phase hj hn))
    (pr_N hj)

theorem pr_decode {j : α → ℕ} {n : α → ℤ} (hj : Primrec j) (hn : Primrec n) :
    Primrec fun a => decode (j a) (n a) :=
  (pr_phase hj hn).pair ((pr_C1 hj hn).pair (pr_C2 hj hn))


theorem pr_rule {ρ : α → Rule} (hρ : Primrec ρ) :
    Primrec (fun a => Rule.equivProd (ρ a)) :=
  (Primrec.of_equiv (e := Rule.equivProd)).comp hρ

theorem pr_src {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).src :=
  Primrec.fst.comp (pr_rule hρ)
theorem pr_t₁ {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).t₁ :=
  Primrec.fst.comp (Primrec.snd.comp (pr_rule hρ))
theorem pr_t₂ {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).t₂ :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (pr_rule hρ)))
theorem pr_d₁ {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).d₁ :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (pr_rule hρ))))
theorem pr_d₂ {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).d₂ :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (pr_rule hρ)))))
theorem pr_dst {ρ : α → Rule} (hρ : Primrec ρ) : Primrec fun a => (ρ a).dst :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (pr_rule hρ)))))

theorem pr_testOk {t : α → Test} {c : α → ℕ} (ht : Primrec t) (hc : Primrec c) :
    Primrec fun a => (t a).ok (c a) := by
  refine (Primrec.cond (Primrec.beq.comp ht (Primrec.const Test.zero))
    (Primrec.beq.comp hc (Primrec.const 0))
    (Primrec.cond (Primrec.beq.comp ht (Primrec.const Test.pos))
      (Primrec.nat_le.comp (Primrec.const 1) hc).decide (Primrec.const true))).of_eq fun a => ?_
  cases t a <;> rfl

theorem pr_moveVal {d : α → Move} (hd : Primrec d) : Primrec fun a => (d a).val := by
  refine (Primrec.cond (Primrec.beq.comp hd (Primrec.const Move.minus)) (Primrec.const (-1))
    (Primrec.cond (Primrec.beq.comp hd (Primrec.const Move.zero)) (Primrec.const 0)
      (Primrec.const 1))).of_eq fun a => ?_
  cases d a <;> rfl

theorem pr_fires {ρ : α → Rule} {c : α → Cfg} (hρ : Primrec ρ) (hc : Primrec c) :
    Primrec fun a => decide ((ρ a).Fires (c a)) := by
  have h1 := (Primrec.eq.comp (Primrec.fst.comp hc) (pr_src hρ))
  have h2 := (Primrec.eq.comp (pr_testOk (pr_t₁ hρ) (Primrec.fst.comp (Primrec.snd.comp hc)))
    (Primrec.const true))
  have h3 := (Primrec.eq.comp (pr_testOk (pr_t₂ hρ) (Primrec.snd.comp (Primrec.snd.comp hc)))
    (Primrec.const true))
  have h4 := (int_le.comp (Primrec.const 0) (int_add.comp
    (int_natCast.comp (Primrec.fst.comp (Primrec.snd.comp hc))) (pr_moveVal (pr_d₁ hρ))))
  have h5 := (int_le.comp (Primrec.const 0) (int_add.comp
    (int_natCast.comp (Primrec.snd.comp (Primrec.snd.comp hc))) (pr_moveVal (pr_d₂ hρ))))
  exact (h1.and (h2.and (h3.and (h4.and h5)))).decide

theorem pr_target {ρ : α → Rule} {c : α → Cfg} (hρ : Primrec ρ) (hc : Primrec c) :
    Primrec fun a => (ρ a).target (c a) :=
  (pr_dst hρ).pair ((int_toNat.comp (int_add.comp
    (int_natCast.comp (Primrec.fst.comp (Primrec.snd.comp hc))) (pr_moveVal (pr_d₁ hρ)))).pair
    (int_toNat.comp (int_add.comp
    (int_natCast.comp (Primrec.snd.comp (Primrec.snd.comp hc))) (pr_moveVal (pr_d₂ hρ)))))

theorem pr_step {R : α → List Rule} {c : α → Cfg} (hR : Primrec R) (hc : Primrec c) :
    Primrec fun a => step (R a) (c a) :=
  Primrec.option_map (list_find? hR (pr_fires Primrec.snd (hc.comp Primrec.fst)).to₂)
    (pr_target Primrec.snd (hc.comp Primrec.fst)).to₂

theorem pr_isSourceB {R : α → List Rule} {c : α → Cfg} (hR : Primrec R) (hc : Primrec c) :
    Primrec fun a => isSourceB (R a) (c a) := by
  unfold isSourceB
  have hc' := hc.comp (Primrec.fst (α := α) (β := Rule))
  have hρ := Primrec.snd (α := α) (β := Rule)
  have hpre := int_sub.comp (int_natCast.comp (Primrec.fst.comp (Primrec.snd.comp hc')))
    (pr_moveVal (pr_d₁ hρ))
  have hpre2 := int_sub.comp (int_natCast.comp (Primrec.snd.comp (Primrec.snd.comp hc')))
    (pr_moveVal (pr_d₂ hρ))
  have hA := ((Primrec.eq.comp (pr_dst hρ) (Primrec.fst.comp hc')).and
    ((int_le.comp (Primrec.const 0) hpre).and (int_le.comp (Primrec.const 0) hpre2))).decide
  have hB := (Primrec.eq.comp (pr_step (hR.comp Primrec.fst) ((pr_src hρ).pair
    ((int_toNat.comp hpre).pair (int_toNat.comp hpre2)))) (Primrec.option_some.comp hc')).decide
  exact list_all hR (Primrec.not.comp (Primrec.and.comp hA hB)).to₂


theorem pr_scale {n A B : α → ℤ} (hn : Primrec n) (hA : Primrec A) (hB : Primrec B) :
    Primrec fun a => scale (n a) (A a) (B a) :=
  int_ediv.comp (int_mul.comp (int_mul.comp hn (pr_intPow 2 (int_toNat.comp hA)))
      (pr_intPow 3 (int_toNat.comp hB)))
    (int_mul.comp (pr_intPow 2 (int_negPart.comp hA)) (pr_intPow 3 (int_negPart.comp hB)))

theorem pr_move {j : α → ℕ} {n : α → ℤ} {s : α → ℕ} {δ₁ δ₂ : α → ℤ} (hj : Primrec j)
    (hn : Primrec n) (hs : Primrec s) (h₁ : Primrec δ₁) (h₂ : Primrec δ₂) :
    Primrec fun a => move (j a) (n a) (s a) (δ₁ a) (δ₂ a) :=
  pr_scale hn (int_mul.comp (int_natCast.comp (pr_N hj)) h₁)
    (int_sub.comp (int_add.comp (int_mul.comp (int_natCast.comp (pr_N hj)) h₂)
      (int_natCast.comp hs)) (int_natCast.comp (pr_phase hj hn)))

theorem pr_F {j : α → ℕ} {R : α → List Rule} {n : α → ℤ} (hj : Primrec j) (hR : Primrec R)
    (hn : Primrec n) : Primrec fun a => F (j a) (R a) (n a) := by
  have hj' := hj.comp (Primrec.fst (α := α) (β := Rule))
  have hn' := hn.comp (Primrec.fst (α := α) (β := Rule))
  refine (Primrec.cond (pr_inEngine hj hn)
    (Primrec.option_map (list_find? hR (pr_fires Primrec.snd (pr_decode hj' hn')).to₂)
      (pr_move hj' hn' (pr_dst Primrec.snd) (pr_moveVal (pr_d₁ Primrec.snd))
        (pr_moveVal (pr_d₂ Primrec.snd))).to₂)
    (Primrec.const none)).of_eq fun a => ?_
  unfold F
  by_cases h : InEngine (j a) (n a) <;> simp [h]

theorem pr_machine {M : α → Machine} (hM : Primrec M) :
    Primrec (fun a => Machine.equivProd (M a)) :=
  (Primrec.of_equiv (e := Machine.equivProd)).comp hM

theorem pr_K {M : α → Machine} (hM : Primrec M) : Primrec fun a => (M a).K :=
  Primrec.fst.comp (pr_machine hM)
theorem pr_rules {M : α → Machine} (hM : Primrec M) : Primrec fun a => (M a).rules :=
  Primrec.fst.comp (Primrec.snd.comp (pr_machine hM))
theorem pr_pair {M : α → Machine} (hM : Primrec M) : Primrec fun a => (M a).pair :=
  Primrec.snd.comp (Primrec.snd.comp (pr_machine hM))

theorem pr_pairFn {M : α → Machine} {s : α → ℕ} (hM : Primrec M) (hs : Primrec s) :
    Primrec fun a => (M a).pairFn (s a) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp (pr_pair hM) hs) hs).of_eq fun a => by
    simp [Machine.pairFn, List.getD_eq_getElem?_getD]

theorem pr_hwIdx {hw : α → List (ℤ × ℤ)} {n : α → ℤ} (hhw : Primrec hw) (hn : Primrec n) :
    Primrec fun a => hwIdx (hw a) (n a) :=
  Primrec.list_findIdx hhw (Primrec.beq.comp
    (int_emod.comp (hn.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (int_emod.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂

theorem pr_hwPos {hw : α → List (ℤ × ℤ)} {n : α → ℤ} (hhw : Primrec hw) (hn : Primrec n) :
    Primrec fun a => hwPos (hw a) (n a) := by
  have hg := (Primrec.list_getD (0, 1)).comp hhw (pr_hwIdx hhw hn)
  exact int_add.comp (int_mul.comp (int_natCast.comp (Primrec.list_length.comp hhw))
    (int_ediv.comp (int_sub.comp hn (Primrec.fst.comp hg)) (Primrec.snd.comp hg)))
    (int_natCast.comp (pr_hwIdx hhw hn))

theorem pr_hwPoint {hw : α → List (ℤ × ℤ)} {p : α → ℤ} (hhw : Primrec hw) (hp : Primrec p) :
    Primrec fun a => hwPoint (hw a) (p a) := by
  have hl := int_natCast.comp (Primrec.list_length.comp hhw)
  have hg := (Primrec.list_getD (0, 1)).comp hhw (int_toNat.comp (int_emod.comp hp hl))
  exact int_add.comp (Primrec.fst.comp hg) (int_mul.comp (Primrec.snd.comp hg)
    (int_ediv.comp hp hl))

theorem pr_hwNext {hw : α → List (ℤ × ℤ)} {n : α → ℤ} (hhw : Primrec hw) (hn : Primrec n) :
    Primrec fun a => hwNext (hw a) (n a) :=
  pr_hwPoint hhw (int_add.comp (pr_hwPos hhw hn) (Primrec.const 1))

theorem pr_hwModulus {j : α → ℕ} (hj : Primrec j) : Primrec fun a => hwModulus (j a) :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (nat_pow.comp (Primrec.const 5) hj)
    (nat_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2) (pr_N hj))))
    (nat_pow.comp (Primrec.const 3) (Primrec.nat_mul.comp (Primrec.const 3) (pr_N hj)))

/-- `filter` with a parameter. -/
theorem list_filter {β : Type*} [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).filter (p a) := by
  refine (Primrec.list_foldr hf (Primrec.const [])
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  dsimp only
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.filter_cons]; cases p a b <;> rfl

theorem pr_highwayAt {j : α → ℕ} {R : α → List Rule} (hj : Primrec j) (hR : Primrec R) :
    Primrec fun a => highwayAt (j a) (R a) := by
  have hj' := hj.comp (Primrec.fst (α := α) (β := ℤ))
  have hR' := hR.comp (Primrec.fst (α := α) (β := ℤ))
  have hpred := Primrec.or.comp (Primrec.not.comp (pr_inEngine hj' Primrec.snd))
    (pr_isSourceB hR' (pr_decode hj' Primrec.snd))
  refine (Primrec.list_map (list_filter (Primrec.list_map
      (Primrec.list_range.comp (pr_hwModulus hj)) (int_natCast.comp Primrec.snd).to₂) hpred.to₂)
    (Primrec.pair Primrec.snd (int_natCast.comp (pr_hwModulus hj'))).to₂).of_eq
    fun a => ?_
  rw [highwayAt_eq]


theorem sigma_eq_getD (j : ℕ) (M : Machine) (hw : List (ℤ × ℤ)) (n : ℤ) :
    sigma j M hw n = (F j M.rules n).getD
      (if InEngine j n then hwNext hw (move j n (M.pairFn (phase j n)) 0 0) else hwNext hw n) := by
  unfold sigma
  cases F j M.rules n <;> rfl

theorem pr_sigma {j : α → ℕ} {M : α → Machine} {hw : α → List (ℤ × ℤ)} {n : α → ℤ}
    (hj : Primrec j) (hM : Primrec M) (hhw : Primrec hw) (hn : Primrec n) :
    Primrec fun a => sigma (j a) (M a) (hw a) (n a) := by
  refine (Primrec.option_getD.comp (pr_F hj (pr_rules hM) hn)
    (Primrec.ite (Primrec.primrecPred (pr_inEngine hj hn))
      (pr_hwNext hhw (pr_move hj hn (pr_pairFn hM (pr_phase hj hn)) (Primrec.const 0)
        (Primrec.const 0)))
      (pr_hwNext hhw hn))).of_eq fun a => ?_
  rw [sigma_eq_getD]

theorem gcd_eq_findGreatest (a b : ℕ) :
    Nat.gcd a b = Nat.findGreatest (fun g => g ∣ a ∧ g ∣ b) (a + b) := by
  by_cases h : a + b = 0
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp
  have hpos : 0 < Nat.gcd a b := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; rw [Nat.gcd_zero_left]; omega
    · exact Nat.gcd_pos_of_pos_left _ ha
  symm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩, fun k hk _ ⟨h1, h2⟩ => ?_⟩
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; rw [Nat.gcd_zero_left]; omega
    · exact (Nat.gcd_le_left _ ha).trans (by omega)
  · have := Nat.le_of_dvd hpos (Nat.dvd_gcd h1 h2)
    omega

theorem nat_gcd : Primrec₂ Nat.gcd := by
  have hR : PrimrecRel (fun (x : ℕ × ℕ) (g : ℕ) => g ∣ x.1 ∧ g ∣ x.2) := by
    have hd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
        fun ⟨a, b⟩ => by dsimp only; exact (Nat.dvd_iff_mod_eq_zero).symm
    exact (hd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (hd.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  refine (Primrec.nat_findGreatest (Primrec.nat_add.comp Primrec.fst Primrec.snd) hR).of_eq
    fun x => ?_
  rw [gcd_eq_findGreatest]

/-- The numerator of `d / m` without `ℚ`. -/
def numZ (d : ℤ) (m : ℕ) : ℤ :=
  if m = 0 then 0 else d / ((m.gcd d.natAbs : ℕ) : ℤ)

/-- The denominator of `d / m` without `ℚ`. -/
def denN (d : ℤ) (m : ℕ) : ℕ :=
  if m = 0 then 1 else m / m.gcd d.natAbs

theorem num_div_eq_numZ (d : ℤ) (m : ℕ) : ((d : ℚ) / m).num = numZ d m := by
  rw [← Rat.mkRat_eq_div, Rat.num_mkRat, numZ]

theorem den_div_eq_denN (d : ℤ) (m : ℕ) : ((d : ℚ) / m).den = denN d m := by
  rw [← Rat.mkRat_eq_div, Rat.den_mkRat, denN]

theorem pr_numZ {d : α → ℤ} {m : α → ℕ} (hd : Primrec d) (hm : Primrec m) :
    Primrec fun a => numZ (d a) (m a) :=
  Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const 0)
    (int_ediv.comp hd (int_natCast.comp (nat_gcd.comp hm (int_natAbs.comp hd))))

theorem pr_denN {d : α → ℤ} {m : α → ℕ} (hd : Primrec d) (hm : Primrec m) :
    Primrec fun a => denN (d a) (m a) :=
  Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const 1)
    (Primrec.nat_div.comp hm (nat_gcd.comp hm (int_natAbs.comp hd)))

theorem tableFrom_eq (f : ℤ → ℤ) (M : ℕ) : tableFrom f M = RcwaTable.equivProd.symm
    (M, ((List.range M).map (fun a : ℕ => (a : ℤ))).map fun k =>
      (numZ (f (k + M) - f k) M,
        (denN (f (k + M) - f k) M : ℤ) * f k - numZ (f (k + M) - f k) M * k,
        (denN (f (k + M) - f k) M : ℤ))) := by
  unfold tableFrom
  have hL : List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range M) =
      (List.range M).map (fun a : ℕ => (a : ℤ)) := List.map_eq_flatMap.symm
  simp only [RcwaTable.equivProd, Equiv.coe_fn_symm_mk, num_div_eq_numZ, den_div_eq_denN]
  congr 1
  rw [← hL]
  rfl

theorem pr_tableFrom {f : α → ℤ → ℤ} {m : α → ℕ} (hf : Primrec₂ f) (hm : Primrec m) :
    Primrec fun a => tableFrom (f a) (m a) := by
  have hm' := hm.comp (Primrec.fst (α := α) (β := ℤ))
  have hd := int_sub.comp (hf.comp Primrec.fst (int_add.comp Primrec.snd (int_natCast.comp hm')))
    (hf.comp Primrec.fst Primrec.snd)
  have hden := int_natCast.comp (pr_denN hd hm')
  have hrow := (pr_numZ hd hm').pair ((int_sub.comp (int_mul.comp hden
    (hf.comp Primrec.fst Primrec.snd)) (int_mul.comp (pr_numZ hd hm') Primrec.snd)).pair hden)
  refine ((Primrec.of_equiv_symm (e := RcwaTable.equivProd)).comp (hm.pair (Primrec.list_map
    (Primrec.list_map (Primrec.list_range.comp hm) (int_natCast.comp Primrec.snd).to₂)
    hrow.to₂))).of_eq fun a => ?_
  rw [tableFrom_eq]

theorem pr_enc {j : α → ℕ} {c : α → Cfg} (hj : Primrec j) (hc : Primrec c) :
    Primrec fun a => enc (j a) (c a) :=
  int_mul.comp
    (pr_intPow 2 (Primrec.nat_mul.comp (pr_N hj) (Primrec.fst.comp (Primrec.snd.comp hc))))
    (pr_intPow 3 (Primrec.nat_add.comp (Primrec.fst.comp hc)
      (Primrec.nat_mul.comp (pr_N hj) (Primrec.snd.comp (Primrec.snd.comp hc)))))

end Prim

open PrimInt in
/-- The reduction is computable (the bulk of the computability layer). -/
theorem computable_reduce : Computable reduce := by
  apply Primrec.to_comp
  have hM := Primrec.fst (α := Machine) (β := Cfg)
  have hl : Primrec fun p : Machine × Cfg => level p.1 := Primrec.succ.comp (pr_K hM)
  have hhw : Primrec fun p : Machine × Cfg => highwayOf p.1 :=
    pr_highwayAt hl (pr_rules hM)
  have he := pr_enc hl Primrec.snd
  have hs : Primrec₂ fun (p : Machine × Cfg) (n : ℤ) => sigma (level p.1) p.1 (highwayOf p.1) n :=
    pr_sigma (hl.comp Primrec.fst) (hM.comp Primrec.fst) (hhw.comp Primrec.fst) Primrec.snd
  have hm : Primrec fun p : Machine × Cfg => 3 ^ N (level p.1) * hwModulus (level p.1) :=
    Primrec.nat_mul.comp (nat_pow.comp (Primrec.const 3) (pr_N hl)) (pr_hwModulus hl)
  have ht : Primrec fun p : Machine × Cfg => tableOf p.1 := pr_tableFrom hs hm
  exact ht.pair (he.pair (pr_hwNext hhw he))

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

/-- **Same-orbit is undecidable** on exact tables with bijective evaluation (so on
RCWA permutations of `ℤ` with all slopes in `2^ℤ 3^ℤ`), given `HaltingUndecidable`. -/
theorem not_computable_sameCycle (hlit : HaltingUndecidable) :
    ¬ ∃ g : RcwaTable × ℤ × ℤ → Bool, Computable g ∧
      ∀ (T : RcwaTable) (a b : ℤ), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g (T, a, b) = true ↔ Equiv.Perm.SameCycle (Equiv.ofBijective T.eval hb) a b) := by
  rintro ⟨g, hg, hspec⟩
  refine hlit ⟨g ∘ reduce, hg.comp computable_reduce, fun M c hM hK hc => ?_⟩
  have hG := good_of_valid hM
  obtain ⟨hex, hev⟩ := tableOf_spec hM
  have hb : Function.Bijective (tableOf M).eval := hev ▸ sigma_bijective hG
  have he : Equiv.ofBijective (tableOf M).eval hb = sigmaPerm hG := by
    ext x; simp [sigmaPerm, hev]
  have := hspec (tableOf M) (enc (level M) c) (hwNext (highwayOf M) (enc (level M) c)) hex hb
  rw [he, sameCycle_enc_iff hG hM.noBiInfinite hM.endToStart hK hc] at this
  exact this

end CollatzMoonshot.RcwaSameOrbit
