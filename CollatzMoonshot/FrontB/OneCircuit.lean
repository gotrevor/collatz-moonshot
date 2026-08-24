/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontB.Words
import CollatzMoonshot.FrontB.Powers

/-!
# The one-circuit (base of the ladder): a canonical 1-circuit cycle is trivial

The circuit ladder that closes Front B (`Threads.lean`, `LadderCompletes` /
`hercher_min_circuit_count`) has its base case at `circuits v = 1`.  Up to
rotation every one-circuit word is `trueᵃ falseᵇ` (`a` odd steps then `b`
halvings).  This file pins the **arithmetic core** of the base case, with no
transcendence input, purely from the `Words.lean` definitions.

## Closed forms (proved)

For `w = trueᵃ ++ falseᵇ`:
* `ones w = a`, `w.length = a + b`;
* `numer w = 3ᵃ − 2ᵃ` — **independent of `b`** (the trailing halvings contribute
  nothing to the numerator: `numer (false :: t) = 2 · numer t` and
  `numer (falseᵇ) = 0`, while each prepended `true` adds `3^(ones tail)`);
* `den w = 2^(a+b) − 3ᵃ`.

## The Diophantine base case

`oneCircuitCanonical_trivial`: for `a, b ≥ 1`, if `0 < den w` and `den w ∣ numer w`
then `a = 1 ∧ b = 1` (the trivial cycle `{1,2}`, member `1`).  Verified by
`experiments`: the sole solution through `a ≤ 8` is `(1,1)`.

Reduction (proved, transcendence-free): `numer w + den w = 2ᵃ (2ᵇ − 1)` and
`den w` is odd, so `den w ∣ numer w ↔ den w ∣ 2ᵇ − 1`.  The `a = 1` slice is then
closed elementarily here.

**The `a ≥ 2` slice is NOT elementary — it is Steiner's theorem (1977).**  After
the reduction it asks: can `den w = 2^(a+b) − 3ᵃ` divide `2ᵇ − 1` with `a ≥ 2`?
`den ∣ 2ᵇ−1` gives `den ≤ 2ᵇ−1`, which with `den > 0` pins `2ᵇ` to the interval
`(3ᵃ/2ᵃ, 3ᵃ/(2ᵃ−1))` — width-ratio `2ᵃ/(2ᵃ−1) → 1`.  "No power of `2` in that
interval for `a ≥ 2`" is exactly the statement `‖a·log₂3‖ ≳ 2^{−a}`, an **effective
irrationality-measure / Baker** lower bound (Steiner used transcendence to close the
one-circuit / one-cycle case; cf. `FRONT-B-ROUTES.md` §filter).  It is therefore
**not** an `omega` argument (correcting the earlier `PENDING_WORK.md` "path 1"
claim), and it is **off the ladder's critical path**: `hercher_min_circuit_count`
(no-transcendence, in `Threads.lean`) already gives triviality for every circuit
count `≤ 91`, this rung included.

We therefore keep the file **transcendence-free** by isolating that single input as
an explicit hypothesis `SteinerOneCircuit` (a `def`, in the style of the board's
`Compression`/`LadderCompletes` open targets), NOT as a `sorry` and NOT as a new
axiom.  The elementary reduction below is complete and sorry-free.
-/

namespace CollatzMoonshot.FrontB

/-- The canonical one-circuit word: `a` odd steps then `b` halvings. -/
def oneCircuitWord (a b : ℕ) : List Bool :=
  List.replicate a true ++ List.replicate b false

@[simp] theorem ones_replicate_true (n : ℕ) : ones (List.replicate n true) = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ones]; omega

@[simp] theorem ones_replicate_false (n : ℕ) : ones (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ones]; exact ih

@[simp] theorem numer_replicate_false (n : ℕ) : numer (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, numer, ih]

@[simp] theorem ones_oneCircuitWord (a b : ℕ) : ones (oneCircuitWord a b) = a := by
  unfold oneCircuitWord; rw [ones_append]; simp

@[simp] theorem length_oneCircuitWord (a b : ℕ) :
    (oneCircuitWord a b).length = a + b := by
  simp [oneCircuitWord]

/-- **Closed form for the numerator**, independent of `b`: `numer (trueᵃ falseᵇ) = 3ᵃ − 2ᵃ`. -/
theorem numer_oneCircuitWord (a b : ℕ) :
    numer (oneCircuitWord a b) = 3 ^ a - 2 ^ a := by
  unfold oneCircuitWord
  induction a with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, numer, ih, ones_append,
      ones_replicate_true, ones_replicate_false]
    have h2 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
    rw [pow_succ 2 n, pow_succ 3 n, Nat.add_zero]
    omega

/-- Closed form for the denominator. -/
theorem den_oneCircuitWord (a b : ℕ) :
    den (oneCircuitWord a b) = 2 ^ (a + b) - 3 ^ a := by
  unfold den
  rw [length_oneCircuitWord, ones_oneCircuitWord]

/-- `numer w + den w = 2ᵃ (2ᵇ − 1)` (as integers), the identity behind the
`den ∣ numer ↔ den ∣ 2ᵇ − 1` reduction. -/
theorem numer_add_den_oneCircuitWord (a b : ℕ) (hpos : 0 < den (oneCircuitWord a b)) :
    (numer (oneCircuitWord a b) : ℤ) + den (oneCircuitWord a b)
      = 2 ^ a * (2 ^ b - 1) := by
  have hden : den (oneCircuitWord a b) = 2 ^ (a + b) - 3 ^ a := den_oneCircuitWord a b
  have hnum : numer (oneCircuitWord a b) = 3 ^ a - 2 ^ a := numer_oneCircuitWord a b
  have h2 : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hnumZ : (numer (oneCircuitWord a b) : ℤ) = (3 : ℤ) ^ a - 2 ^ a := by
    rw [hnum]; push_cast [h2]; ring
  rw [hnumZ, hden]
  have : (2 : ℤ) ^ (a + b) = 2 ^ a * 2 ^ b := by rw [pow_add]
  rw [this]; ring

/-! ## The concrete family really has one circuit

Connecting `oneCircuitWord` to the abstract `circuits` counter that the board's ladder
(`Compression`/`LadderCompletes`) is stated over: the canonical one-circuit word has
exactly one falling edge (`true`→`false`), cyclically.  This is the base of the
circuit-block normal form any circuit-count (compression) argument works with. -/

/-- Over the linearized cyclic pairs of an all-`false` word, no pair is a falling edge:
every first component is `false`, for any sentinel. -/
theorem countP_falls_cpairs_replicate_false :
    ∀ (n : ℕ) (f : Bool),
      ((cpairs (List.replicate n false) f).countP fun q => q.1 && !q.2) = 0
  | 0, _ => by simp [cpairs]
  | 1, _ => by simp [cpairs]
  | (n + 2), f => by
    rw [show List.replicate (n + 2) false
          = false :: (false :: List.replicate n false) from by
        rw [List.replicate_succ, List.replicate_succ], cpairs, List.countP_cons,
      show (false :: List.replicate n false) = List.replicate (n + 1) false from
        (List.replicate_succ).symm, countP_falls_cpairs_replicate_false (n + 1) f]
    decide

/-- All-`true` word with sentinel `false`: exactly one falling edge — the final pair
`(true, false[sentinel])`; the internal `(true, true)` pairs are not falls. -/
theorem countP_falls_cpairs_replicate_true :
    ∀ (a : ℕ),
      ((cpairs (List.replicate (a + 1) true) false).countP fun q => q.1 && !q.2) = 1
  | 0 => by simp [cpairs]
  | (a + 1) => by
    rw [show List.replicate (a + 2) true = true :: (true :: List.replicate a true) from by
        rw [List.replicate_succ, List.replicate_succ], cpairs, List.countP_cons,
      show (true :: List.replicate a true) = List.replicate (a + 1) true from
        (List.replicate_succ).symm, countP_falls_cpairs_replicate_true a]
    decide

/-- **The canonical one-circuit word has exactly one circuit.**  Ties `oneCircuitWord`
(and hence `oneCircuitCanonical_trivial`) to the abstract `circuits` counter the ladder
uses: this is the `C = 1` shape of the circuit-block normal form. -/
theorem circuits_oneCircuitWord (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    circuits (oneCircuitWord a b) = 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hword : oneCircuitWord (a' + 1) (b' + 1)
      = true :: (List.replicate a' true ++ List.replicate (b' + 1) false) := by
    unfold oneCircuitWord; rw [List.replicate_succ, List.cons_append]
  have hsplit : oneCircuitWord (a' + 1) (b' + 1)
      = List.replicate (a' + 1) true ++ false :: List.replicate b' false := by
    unfold oneCircuitWord; rw [show List.replicate (b' + 1) false
      = false :: List.replicate b' false from List.replicate_succ]
  rw [hword, circuits_cons, ← hword, hsplit,
    cpairs_append false (List.replicate b' false) true (List.replicate (a' + 1) true),
    List.countP_append, countP_falls_cpairs_replicate_true a',
    show (false :: List.replicate b' false) = List.replicate (b' + 1) false from
      (List.replicate_succ).symm, countP_falls_cpairs_replicate_false (b' + 1) true]

/-! ### The circuit-block normal form (general `m`)

Toward Front B `Compression`: assemble words from circuit blocks and read off the
circuit count. `blockWord [(a₁,b₁),…,(aₘ,bₘ)] = trueᵃ¹falseᵇ¹ ⋯ trueᵃᵐfalseᵇᵐ`, and with
every block nonempty (`aᵢ,bᵢ ≥ 1`) it has exactly `m` circuits — one falling edge per
block. This is the vocabulary any circuit-count (compression) bound is stated in. -/

/-- Prepending a single `false` to the argument of `cpairs` adds no falling edge (its
first component is `false`), whatever follows and whatever the sentinel. -/
theorem countP_falls_cpairs_false_cons (z : List Bool) (f : Bool) :
    ((cpairs (false :: z) f).countP fun q => q.1 && !q.2)
      = ((cpairs z f).countP fun q => q.1 && !q.2) := by
  cases z with
  | nil => simp [cpairs]
  | cons y t => rw [cpairs, List.countP_cons]; simp

/-- A whole `false`-block prefix adds no falling edge. -/
theorem countP_falls_cpairs_false_prefix :
    ∀ (n : ℕ) (rest : List Bool) (f : Bool),
      ((cpairs (List.replicate n false ++ rest) f).countP fun q => q.1 && !q.2)
        = ((cpairs rest f).countP fun q => q.1 && !q.2)
  | 0, _, _ => by simp
  | (n + 1), rest, f => by
    rw [List.replicate_succ, List.cons_append, countP_falls_cpairs_false_cons,
      countP_falls_cpairs_false_prefix n rest f]

/-- Words assembled from circuit blocks: `trueᵃ¹falseᵇ¹ trueᵃ²falseᵇ² ⋯`. -/
def blockWord : List (ℕ × ℕ) → List Bool
  | [] => []
  | (a, b) :: rest => List.replicate a true ++ List.replicate b false ++ blockWord rest

/-- The head-`true` fall count of a block word agrees with `circuits` (both `0` when
empty; when the first block is nonempty the head is `true`, the `circuits` sentinel). -/
theorem cpairs_true_falls_blockWord (L : List (ℕ × ℕ)) (h : ∀ blk ∈ L, 1 ≤ blk.1) :
    ((cpairs (blockWord L) true).countP fun q => q.1 && !q.2) = circuits (blockWord L) := by
  cases L with
  | nil => simp [blockWord, circuits, rot, cpairs]
  | cons ab L' =>
    obtain ⟨a, b⟩ := ab
    have ha : 1 ≤ a := h (a, b) (by simp)
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hhead : blockWord ((a' + 1, b) :: L')
        = true :: (List.replicate a' true ++ List.replicate b false ++ blockWord L') := by
      show List.replicate (a' + 1) true ++ List.replicate b false ++ blockWord L' = _
      rw [List.replicate_succ, List.cons_append, List.cons_append]
    rw [hhead, circuits_cons]

/-- **The circuit-block normal form counts circuits.** A word assembled from `m` nonempty
circuit blocks has exactly `m` circuits — the base fact behind any bound on circuit count. -/
theorem circuits_blockWord :
    ∀ (L : List (ℕ × ℕ)), (∀ blk ∈ L, 1 ≤ blk.1 ∧ 1 ≤ blk.2) →
      circuits (blockWord L) = L.length
  | [], _ => by simp [blockWord, circuits, rot, cpairs]
  | (a, b) :: L', h => by
    obtain ⟨ha, hb⟩ := h (a, b) (by simp)
    have hL' : ∀ blk ∈ L', 1 ≤ blk.1 ∧ 1 ≤ blk.2 :=
      fun blk hmem => h blk (List.mem_cons_of_mem _ hmem)
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hsplit : blockWord ((a' + 1, b' + 1) :: L')
        = List.replicate (a' + 1) true ++ false :: (List.replicate b' false ++ blockWord L') := by
      have hb1 : List.replicate (b' + 1) false = false :: List.replicate b' false :=
        List.replicate_succ
      simp only [blockWord, hb1, List.append_assoc, List.cons_append]
    have hcirc : circuits (blockWord ((a' + 1, b' + 1) :: L'))
        = ((cpairs (blockWord ((a' + 1, b' + 1) :: L')) true).countP fun q => q.1 && !q.2) :=
      (cpairs_true_falls_blockWord _ (fun blk hm => (h blk hm).1)).symm
    rw [hcirc, hsplit,
      cpairs_append false (List.replicate b' false ++ blockWord L') true
        (List.replicate (a' + 1) true),
      List.countP_append, countP_falls_cpairs_replicate_true a',
      countP_falls_cpairs_false_cons,
      countP_falls_cpairs_false_prefix b' (blockWord L') true,
      cpairs_true_falls_blockWord L' (fun blk hm => (hL' blk hm).1),
      circuits_blockWord L' hL', List.length_cons]
    omega

/-! ### The converse: every canonical word IS a block form

The reduction that makes the block dictionary usable on real cycles: peel the leading
odd-run then even-run, recurse.  A word with `head = true` and `last = false` equals
`blockWord` of its run-length data. -/

/-- Peel the leading maximal `true`-run. -/
theorem peel_true_run : ∀ (v : List Bool), v.head? = some true →
    ∃ a r, 1 ≤ a ∧ v = List.replicate a true ++ r ∧ (r = [] ∨ r.head? = some false)
  | [], h => by simp at h
  | false :: _, h => by simp at h
  | true :: t, _ => by
    cases t with
    | nil => exact ⟨1, [], le_refl 1, by simp, Or.inl rfl⟩
    | cons x t' =>
      cases x with
      | false => exact ⟨1, false :: t', le_refl 1, by simp, Or.inr rfl⟩
      | true =>
        obtain ⟨a, r, ha, hval, hr⟩ := peel_true_run (true :: t') (by simp)
        exact ⟨a + 1, r, by omega, by rw [hval, List.replicate_succ, List.cons_append], hr⟩

/-- Peel the leading maximal `false`-run. -/
theorem peel_false_run : ∀ (v : List Bool), v.head? = some false →
    ∃ b r, 1 ≤ b ∧ v = List.replicate b false ++ r ∧ (r = [] ∨ r.head? = some true)
  | [], h => by simp at h
  | true :: _, h => by simp at h
  | false :: t, _ => by
    cases t with
    | nil => exact ⟨1, [], le_refl 1, by simp, Or.inl rfl⟩
    | cons x t' =>
      cases x with
      | true => exact ⟨1, true :: t', le_refl 1, by simp, Or.inr rfl⟩
      | false =>
        obtain ⟨b, r, hb, hval, hr⟩ := peel_false_run (false :: t') (by simp)
        exact ⟨b + 1, r, by omega, by rw [hval, List.replicate_succ, List.cons_append], hr⟩

/-- **The block normal form exists.** A word with `head = true` and `last = false` is
`blockWord` of its run data, all blocks nonempty. -/
theorem exists_blockWord_canonical : ∀ (v : List Bool),
    v.head? = some true → v.getLast? = some false →
      ∃ L, (∀ blk ∈ L, 1 ≤ blk.1 ∧ 1 ≤ blk.2) ∧ v = blockWord L
  | v, hhead, hlast => by
    obtain ⟨a, r, ha, hv, hr⟩ := peel_true_run v hhead
    have hrne : r ≠ [] := by
      rintro rfl
      rw [hv, List.append_nil] at hlast
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [List.replicate_succ', List.getLast?_append_of_ne_nil _ (by simp)] at hlast
      simp at hlast
    have hrhead : r.head? = some false := hr.resolve_left hrne
    obtain ⟨b, s, hb, hr2, hs⟩ := peel_false_run r hrhead
    have hvfull : v = List.replicate a true ++ (List.replicate b false ++ s) := by
      rw [hv, hr2]
    cases hsc : s with
    | nil =>
      refine ⟨[(a, b)], ?_, ?_⟩
      · intro blk hblk
        rw [List.mem_singleton] at hblk; subst hblk; exact ⟨ha, hb⟩
      · rw [hvfull, hsc]; simp [blockWord]
    | cons y s' =>
      have hsne : s ≠ [] := by rw [hsc]; simp
      have hne1 : List.replicate b false ++ s ≠ [] := by rw [hsc]; simp
      have hshead : s.head? = some true := hs.resolve_left hsne
      have hslast : s.getLast? = some false := by
        rw [hvfull, List.getLast?_append_of_ne_nil _ hne1,
          List.getLast?_append_of_ne_nil _ hsne] at hlast
        exact hlast
      have hlen : s.length < v.length := by
        rw [hvfull]
        simp only [List.length_append, List.length_replicate]
        omega
      obtain ⟨L', hL', hsblock⟩ := exists_blockWord_canonical s hshead hslast
      refine ⟨(a, b) :: L', ?_, ?_⟩
      · intro blk hblk
        rcases List.mem_cons.mp hblk with h | h
        · subst h; exact ⟨ha, hb⟩
        · exact hL' blk h
      · rw [hvfull, hsblock]; simp [blockWord, List.append_assoc]
  termination_by v => v.length
  decreasing_by exact hlen

/-- **The reduction, with the circuit count.** A canonical word decomposes into exactly
`circuits v` nonempty blocks.  So "bound `circuits v`" (for canonical cycle words) is
literally "bound the block count of the normal form" — the shape `Compression` needs.
(For an arbitrary integer-cycle word, rotate to a run boundary first: `circuits` is
rotation-invariant.) -/
theorem exists_blockWord_canonical_circuits (v : List Bool)
    (hh : v.head? = some true) (hl : v.getLast? = some false) :
    ∃ L, (∀ blk ∈ L, 1 ≤ blk.1 ∧ 1 ≤ blk.2) ∧ v = blockWord L ∧ circuits v = L.length := by
  obtain ⟨L, hL, hv⟩ := exists_blockWord_canonical v hh hl
  exact ⟨L, hL, hv, by rw [hv, circuits_blockWord L hL]⟩

/-! ### The S-unit structure of `numer` on the block normal form

The Route-2 leverage: the cycle equation `numer v = N · den v` is an S-unit relation over
`{2,3}`.  On the block normal form its terms collapse to **one per circuit** — the odd-run
of length `aⱼ` telescopes to the single monomial-difference `3^{aⱼ} − 2^{aⱼ}` (exactly the
one-circuit numerator).  So the term count is `m = circuits`, not the cycle length; that is
why a bound on `m` (Compression) would make the subspace/Baker machinery apply. -/

/-- Prepending a `false`-block multiplies the numerator by `2^b`. -/
theorem numer_replicate_false_prefix (b : ℕ) (Y : List Bool) :
    (numer (List.replicate b false ++ Y) : ℤ) = 2 ^ b * numer Y := by
  induction b with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [numer]
    push_cast [ih]
    ring

/-- Prepending a `true`-block of length `a`: `2^a`-scaling plus the collapsed odd-run term
`3^{ones Y}·(3^a − 2^a)`. -/
theorem numer_replicate_true_prefix (a : ℕ) (Y : List Bool) :
    (numer (List.replicate a true ++ Y) : ℤ)
      = 2 ^ a * numer Y + 3 ^ ones Y * (3 ^ a - 2 ^ a) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [numer]
    have hones : ones (List.replicate k true ++ Y) = k + ones Y := by
      rw [ones_append, ones_replicate_true]
    rw [hones]
    push_cast [ih]
    ring

/-- **The block-normal-form cycle equation, one S-unit term per circuit.**  `numer` of an
`m`-block word is `2^{a+b}`-scaled recursion plus the collapsed odd-run term of the head
block — the `m`-term S-unit structure that makes circuit count the term count. -/
theorem numer_blockWord_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    (numer (blockWord ((a, b) :: L)) : ℤ)
      = 2 ^ (a + b) * numer (blockWord L)
        + 3 ^ ones (blockWord L) * (3 ^ a - 2 ^ a) := by
  have hbw : blockWord ((a, b) :: L)
      = List.replicate a true ++ (List.replicate b false ++ blockWord L) := by
    simp only [blockWord, List.append_assoc]
  rw [hbw, numer_replicate_true_prefix, numer_replicate_false_prefix,
    ones_append, ones_replicate_false, Nat.zero_add, pow_add]
  ring

/-- The odd-step count of a block form is the sum of the odd-run lengths `Σ aⱼ`. -/
@[simp] theorem ones_blockWord (L : List (ℕ × ℕ)) :
    ones (blockWord L) = (L.map Prod.fst).sum := by
  induction L with
  | nil => simp [blockWord]
  | cons ab L' ih =>
    obtain ⟨a, b⟩ := ab
    simp only [blockWord, ones_append, ones_replicate_true, ones_replicate_false, ih,
      List.map_cons, List.sum_cons]
    omega

/-- The length of a block form is `Σ (aⱼ + bⱼ)`. -/
@[simp] theorem length_blockWord (L : List (ℕ × ℕ)) :
    (blockWord L).length = (L.map fun p => p.1 + p.2).sum := by
  induction L with
  | nil => simp [blockWord]
  | cons ab L' ih =>
    obtain ⟨a, b⟩ := ab
    simp only [blockWord, List.length_append, List.length_replicate, ih,
      List.map_cons, List.sum_cons]

/-- The denominator of a block form, exponents explicit:
`den = 2^{Σ(aⱼ+bⱼ)} − 3^{Σ aⱼ}`.  Together with `numer_blockWord_cons` this gives the
whole cycle equation `numer = N·den` with its exponent vectors read off the `m` blocks —
the bounded S-unit datum a fixed-`m` argument works from. -/
theorem den_blockWord (L : List (ℕ × ℕ)) :
    den (blockWord L)
      = 2 ^ (L.map fun p => p.1 + p.2).sum - 3 ^ (L.map Prod.fst).sum := by
  rw [den, length_blockWord, ones_blockWord]

open scoped BigOperators in
/-- **The explicit S-unit closed form.**  Unrolling `numer_blockWord_cons` all the way gives
the cycle numerator as a sum of exactly `m = L.length` monomial-difference terms — one per
circuit.  Block `j` contributes `2^{Σ_{i<j}(aᵢ+bᵢ)} · 3^{Σ_{i>j} aᵢ} · (3^{aⱼ} − 2^{aⱼ})`:
a `{2,3}`-unit coefficient times the collapsed odd-run difference.  This is the exact S-unit
datum a subspace-theorem/Baker bound on the number of terms would consume — the term count
being `circuits`, so a bound on the block count would bound the S-unit rank.  (Any method —
SdW, ESS, Baker — reads the cycle equation `numer = N·den` off this canonical form.) -/
theorem numer_blockWord_explicit (L : List (ℕ × ℕ)) :
    (numer (blockWord L) : ℤ) =
      ∑ j ∈ Finset.range L.length,
        2 ^ ((L.take j).map (fun c => c.1 + c.2)).sum
        * 3 ^ ((L.drop (j + 1)).map Prod.fst).sum
        * (3 ^ (L.getD j (0, 0)).1 - 2 ^ (L.getD j (0, 0)).1) := by
  induction L with
  | nil => simp [blockWord]
  | cons c L' ih =>
    obtain ⟨a, b⟩ := c
    rw [List.length_cons, Finset.sum_range_succ']
    have hzero : (2 : ℤ) ^ ((((a, b) :: L').take 0).map (fun c => c.1 + c.2)).sum
        * 3 ^ ((((a, b) :: L').drop (0 + 1)).map Prod.fst).sum
        * (3 ^ (((a, b) :: L').getD 0 (0, 0)).1 - 2 ^ (((a, b) :: L').getD 0 (0, 0)).1)
        = 3 ^ ones (blockWord L') * (3 ^ a - 2 ^ a) := by
      simp only [List.take_zero, List.map_nil, List.sum_nil, pow_zero, one_mul,
        Nat.zero_add, List.drop_one, List.tail_cons, List.getD_cons_zero, ones_blockWord]
    have hshift : ∀ j ∈ Finset.range L'.length,
        (2 : ℤ) ^ ((((a, b) :: L').take (j + 1)).map (fun c => c.1 + c.2)).sum
          * 3 ^ ((((a, b) :: L').drop (j + 1 + 1)).map Prod.fst).sum
          * (3 ^ (((a, b) :: L').getD (j + 1) (0, 0)).1 - 2 ^ (((a, b) :: L').getD (j + 1) (0, 0)).1)
        = 2 ^ (a + b) *
          (2 ^ ((L'.take j).map (fun c => c.1 + c.2)).sum
            * 3 ^ ((L'.drop (j + 1)).map Prod.fst).sum
            * (3 ^ (L'.getD j (0, 0)).1 - 2 ^ (L'.getD j (0, 0)).1)) := by
      intro j _
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons,
        List.getD_cons_succ, pow_add]
      ring
    rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum, hzero, ← ih, numer_blockWord_cons]

/-- **The single transcendence input for the one-circuit base rung** (Steiner 1977).
Isolated as an explicit hypothesis — a `def`, exactly as the board states its open
targets `Compression`/`LadderCompletes` — so that `OneCircuit.lean` stays
sorry-free and axiom-free while naming precisely what is not elementary.

Content: for `a ≥ 2` there is no canonical one-circuit integer cycle, i.e. the odd
denominator `den (trueᵃfalseᵇ) = 2^(a+b) − 3ᵃ` (when positive) never divides
`2ᵇ − 1`.  Equivalently (via `den ∣ 2ᵇ−1 ⇒ den ≤ 2ᵇ−1`) the interval
`(3ᵃ/2ᵃ, 3ᵃ/(2ᵃ−1))` contains no power of `2` — an effective irrationality-measure
lower bound `‖a·log₂3‖ ≳ 2^{−a}` (Baker/Rhin). -/
def SteinerOneCircuit : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → 0 < den (oneCircuitWord a b) →
    ¬ (den (oneCircuitWord a b) ∣ (2 ^ b - 1 : ℤ))

/-- **Base of the circuit ladder (arithmetic core).**  A canonical one-circuit
integer cycle is the trivial one.

Transcendence-free modulo the single explicit input `SteinerOneCircuit`: the `a = 1`
slice is proved elementarily; the `a ≥ 2` slice is Steiner's theorem, discharged by
the hypothesis (see its docstring and `PENDING_WORK.md`). -/
theorem oneCircuitCanonical_trivial (hSteiner : SteinerOneCircuit)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpos : 0 < den (oneCircuitWord a b))
    (hdvd : den (oneCircuitWord a b) ∣ (numer (oneCircuitWord a b) : ℤ)) :
    a = 1 ∧ b = 1 := by
  -- reduction: den is odd and den ∣ numer + den = 2ᵃ(2ᵇ−1), so den ∣ 2ᵇ − 1.
  have hne : oneCircuitWord a b ≠ [] := by
    intro h; have := length_oneCircuitWord a b; rw [h] at this; simp at this; omega
  have hodd : ¬ (2 : ℤ) ∣ den (oneCircuitWord a b) := not_two_dvd_den hne
  have hsum := numer_add_den_oneCircuitWord a b hpos
  have hdvd_sum : den (oneCircuitWord a b) ∣ 2 ^ a * (2 ^ b - 1) := by
    rw [← hsum]; exact dvd_add hdvd dvd_rfl
  have hcop : IsCoprime (den (oneCircuitWord a b)) ((2 : ℤ) ^ a) := by
    have : IsCoprime (den (oneCircuitWord a b)) (2 : ℤ) :=
      (Int.prime_two.coprime_iff_not_dvd.mpr hodd).symm
    exact this.pow_right
  have hdvd_pow : den (oneCircuitWord a b) ∣ (2 ^ b - 1) :=
    hcop.dvd_of_dvd_mul_left hdvd_sum
  -- from here: the classical bound forcing a = 1.
  rcases Nat.lt_or_ge a 2 with haa | haa
  · -- a = 1
    have ha1 : a = 1 := by omega
    subst ha1
    -- den = 2^(1+b) - 3, numer = 3 - 2 = 1, so den ∣ 1 hence den = 1, giving b = 1.
    have hnum1 : (numer (oneCircuitWord 1 b) : ℤ) = 1 := by
      rw [numer_oneCircuitWord]; norm_num
    have hden1 : den (oneCircuitWord 1 b) = 2 ^ (1 + b) - 3 := by
      rw [den_oneCircuitWord]; norm_num
    have hdvd1 : den (oneCircuitWord 1 b) ∣ (1 : ℤ) := by rw [← hnum1]; exact hdvd
    have hle : den (oneCircuitWord 1 b) = 1 := by
      have := Int.le_of_dvd (by norm_num) hdvd1
      omega
    rw [hden1] at hle
    -- 2^(1+b) - 3 = 1 → 2^(1+b) = 4 → 1+b = 2 → b = 1
    have h4 : (2 : ℤ) ^ (1 + b) = 4 := by omega
    have hn4 : (2 : ℕ) ^ (1 + b) = 2 ^ 2 := by
      have h : (2 : ℕ) ^ (1 + b) = 4 := by exact_mod_cast h4
      omega
    have hb1 : 1 + b = 2 := Nat.pow_right_injective (by norm_num) hn4
    exact ⟨rfl, by omega⟩
  · -- a ≥ 2: no canonical one-circuit integer cycle exists (Steiner 1977).
    -- hpos (0 < 2^(a+b)−3^a), hdvd_pow (den ∣ 2^b−1), and haa (2 ≤ a) are jointly
    -- contradictory — this is exactly the isolated transcendence input.
    exact absurd hdvd_pow (hSteiner a b haa hb hpos)

/-! ### Rotation to canonical form — the block reduction applies to ALL integer cycles

`exists_blockWord_canonical_circuits` only covers words already in `head=true, last=false`
form.  A general integer-cycle word need not start/end that way, but `circuits` is
rotation-invariant and every integer cycle contains both a `true` (odd step, `ones ≥ 1`)
and a `false` (else `den = 2ⁿ − 3ⁿ ≤ 0`), so some rotation reaches the canonical form.
This closes the reduction: **for any integer-cycle word, bounding `circuits` is literally
bounding the block count `L.length` of a genuine block normal form.** -/

/-- `circuits` is invariant under a single rotation `rot`.  The cyclic-adjacency pair list
(`cpairs`, sentinel = head) merely cycles by one entry under `rot`, so its falling-edge
count is unchanged.  Proof: peel the head pair off both sides via `cpairs_append`. -/
theorem circuits_rot (v : List Bool) : circuits (rot v) = circuits v := by
  match v with
  | [] => rfl
  | [b] => cases b <;> rfl
  | b :: c :: s =>
    rw [show rot (b :: c :: s) = c :: (s ++ [b]) from rfl, circuits_cons c (s ++ [b]),
      show c :: (s ++ [b]) = (c :: s) ++ [b] from rfl,
      cpairs_append b [] c (c :: s), List.countP_append, circuits_cons b (c :: s)]
    simp only [cpairs, List.countP_cons, List.countP_nil]; omega

private theorem rot_eq_rotate_aux (v : List Bool) : rot v = v.rotate 1 := by
  cases v with
  | nil => rfl
  | cons b t => rw [List.rotate_cons_succ, List.rotate_zero]; rfl

/-- `circuits` is invariant under any rotation `List.rotate k`. -/
theorem circuits_rotate (v : List Bool) (k : ℕ) : circuits (v.rotate k) = circuits v := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show v.rotate (n + 1) = (v.rotate n).rotate 1 from by rw [List.rotate_rotate],
      ← rot_eq_rotate_aux, circuits_rot, ih]

/-- A word whose head is `false` and which contains a `true` can be rotated to canonical
form (`head = true, last = false`): rotate to the first `true`; its predecessor lies before
the first `true` so it is `false`, giving the required trailing `false`. -/
theorem rotate_canonical_of_head_false {u : List Bool}
    (h0 : u.head? = some false) (ht : true ∈ u) :
    ∃ k, (u.rotate k).head? = some true ∧ (u.rotate k).getLast? = some false := by
  set i := u.findIdx (· == true) with hi
  have hilt : i < u.length := List.findIdx_lt_length_of_exists ⟨true, ht, by simp⟩
  have hui : u[i] = true := by
    have h := @List.findIdx_getElem _ (· == true) u hilt
    rwa [beq_iff_eq] at h
  have huiq : u[i]? = some true := by rw [List.getElem?_eq_getElem hilt, hui]
  have hu0 : u[0]? = some false := by rw [← List.head?_eq_getElem?]; exact h0
  have hipos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exfalso; rw [h] at huiq; rw [hu0] at huiq; simp at huiq
    · exact h
  have hui1 : u[i - 1]? = some false := by
    obtain ⟨hbound, hall⟩ := (List.lt_findIdx_iff u (· == true) (i - 1)).mp (by rw [← hi]; omega)
    have hpred := hall (i - 1) (le_refl _)
    have hval : u[i - 1] = false := by revert hpred; cases u[i - 1] <;> simp
    rw [List.getElem?_eq_getElem hbound, hval]
  refine ⟨i, ?_, ?_⟩
  · rw [List.head?_rotate hilt]; exact huiq
  · rw [List.rotate_eq_drop_append_take (le_of_lt hilt),
      List.getLast?_append_of_ne_nil, List.getLast?_take]
    · simp only [show i ≠ 0 from by omega, if_false]; rw [hui1]; rfl
    · intro hcon
      have : (List.take i u).length = 0 := by rw [hcon]; rfl
      rw [List.length_take] at this; omega

/-- **Any word containing both a `true` and a `false` rotates to canonical form.**  Rotate
to the first `false`, then apply `rotate_canonical_of_head_false`. -/
theorem exists_rotate_canonical {v : List Bool} (hf : false ∈ v) (ht : true ∈ v) :
    ∃ k, (v.rotate k).head? = some true ∧ (v.rotate k).getLast? = some false := by
  set jf := v.findIdx (· == false) with hjf
  have hjflt : jf < v.length := List.findIdx_lt_length_of_exists ⟨false, hf, by simp⟩
  have hu0 : (v.rotate jf).head? = some false := by
    rw [List.head?_rotate hjflt]
    have hval : v[jf] = false := by
      have h := @List.findIdx_getElem _ (· == false) v hjflt
      rwa [beq_iff_eq] at h
    rw [List.getElem?_eq_getElem hjflt, hval]
  have hut : true ∈ v.rotate jf := by rw [List.mem_rotate]; exact ht
  obtain ⟨k, hk1, hk2⟩ := rotate_canonical_of_head_false hu0 hut
  exact ⟨jf + k, by rw [← List.rotate_rotate]; exact hk1,
    by rw [← List.rotate_rotate]; exact hk2⟩

/-- **The block reduction for arbitrary integer cycles.**  Every integer-cycle word — after
a rotation `v.rotate k` — is a genuine block normal form `blockWord L` (all blocks nonempty)
with `circuits v = L.length`.  So bounding the circuit count of an integer cycle (the
content of `Compression`) is exactly bounding its block count, the `m`-term S-unit datum. -/
theorem exists_blockWord_of_integerCycle {v : List Bool} (hv : IntegerCycle v) :
    ∃ (L : List (ℕ × ℕ)) (k : ℕ), (∀ blk ∈ L, 1 ≤ blk.1 ∧ 1 ≤ blk.2) ∧
      v.rotate k = blockWord L ∧ circuits v = L.length := by
  obtain ⟨-, hones, hden, -⟩ := hv
  obtain ⟨k, hh, hl⟩ := exists_rotate_canonical (false_mem_of_den_pos hden)
    (true_mem_of_ones_pos hones)
  obtain ⟨L, hL, hvk, hcirc⟩ := exists_blockWord_canonical_circuits (v.rotate k) hh hl
  exact ⟨L, k, hL, hvk, by rw [← hcirc, circuits_rotate]⟩

end CollatzMoonshot.FrontB
