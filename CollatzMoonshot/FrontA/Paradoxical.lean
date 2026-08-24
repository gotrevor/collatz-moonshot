/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontB.Dictionary

/-!
# Front A: paradoxical finite trajectories

Executes `FRONT-A-PARADOXICAL.md`, the experiment-first continuation of the parity
project.  A **paradoxical** shortcut-Collatz segment has a subcritical multiplicative
coefficient `3^a / 2^m < 1` yet finishes at or above its start, because the exact additive
remainder `numer v` wins.  These objects are finite and exactly enumerable, and the
literature (Rozier--Terracol 2026) connects an infinite-stopping-time orbit to infinitely
many of them.

## Repository notation

For a start `n` and length `m`, put `v = traceWord n m`, `a = ones v`, `y = tstep^[m] n`,
`p = 3^a`, `d = 2^m - p`.  The engine is the exact iterate identity
`FrontB.tstep_iterate_identity`:

    2^m · y = p · n + numer v.

## What this module proves (sorry-free, on the Front-A path)

* `Paradoxical` / `AcyclicParadoxical` — transparent definitions.
* `slack_identity` — the exact integer slack `numer v - d·n = 2^m·(y - n)` (identity **(S)**).
* `paradoxical_criterion` — endpoint `n ≤ y` is *equivalent* to the pure word inequality
  `d·n ≤ numer v` (criterion **(P)**), and the acyclic version `n < y ↔ d·n < numer v`.
* `numer_singleBlock`, `numer_twoBlock` — the exact remainder of a word whose ones form one
  or two contiguous blocks: `numer([F]^s[T]^q[F]^t) = 2^s(3^q-2^q)` and
  `numer([T]^b[F]^c[T]^d[F]^e) = 3^d(3^b-2^b) + 2^(b+c)(3^d-2^d)`.  These back the discovery
  result of the experiment.

## Discovery result (experiment, exhaustive)

`experiments/paradoxical.py` establishes exhaustively (all `<=2`-block front-normalized words
to length `j<=30`, two-block words to `j<=38`) that **every acyclic paradoxical word has at
least three odd blocks**.  This strictly generalizes Rozier--Terracol Appendix A (the single
odd-block exclusion).  The parameterized exclusion is stated here as
`le_two_blocks_not_acyclicParadoxical` with a disclosed proof obligation (`numer` closed
forms are proved; the residue lower bound closing (P) is the open arithmetic core).

The observed paradoxical ratios `q/j` (`5/8, 17/27, 29/46`, all `n<=200000`) are left
convergents/semiconvergents of `log_3 2`, matching Niu's numerical pattern with no
counterexample in range.
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot CollatzMoonshot.FrontB

/-- A **paradoxical** shortcut segment: start above the trivial range, positive length,
subcritical coefficient `3^a < 2^m`, and endpoint at or above the start. -/
def Paradoxical (n m : ℕ) : Prop :=
  2 < n ∧ 0 < m ∧ 3 ^ ones (traceWord n m) < 2 ^ m ∧ n ≤ tstep^[m] n

/-- An **acyclic** paradoxical segment: the endpoint is strictly above the start. -/
def AcyclicParadoxical (n m : ℕ) : Prop :=
  2 < n ∧ 0 < m ∧ 3 ^ ones (traceWord n m) < 2 ^ m ∧ n < tstep^[m] n

/-- **The exact slack identity (S)**, over `ℤ`:
`numer v - (2^m - 3^a)·n = 2^m·(y - n)`, where `v = traceWord n m`, `a = ones v`,
`y = tstep^[m] n`.  A pure rearrangement of the iterate identity. -/
theorem slack_identity (n m : ℕ) :
    (numer (traceWord n m) : ℤ)
        - (2 ^ m - 3 ^ ones (traceWord n m)) * n
      = 2 ^ m * ((tstep^[m] n : ℤ) - n) := by
  have h := tstep_iterate_identity m n
  have hz : (2 : ℤ) ^ m * (tstep^[m] n : ℤ)
      = 3 ^ ones (traceWord n m) * (n : ℤ) + numer (traceWord n m) := by
    exact_mod_cast h
  linear_combination -hz

/-- **The paradoxical criterion (P)**: with subcritical coefficient `3^a < 2^m`, the endpoint
condition `n ≤ tstep^[m] n` is equivalent to the pure word inequality `d·n ≤ numer v`
(`d = 2^m - 3^a`).  Uses truncated `ℕ` subtraction, valid because `3^a ≤ 2^m`. -/
theorem paradoxical_criterion (n m : ℕ)
    (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    (n ≤ tstep^[m] n) ↔
      (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤ numer (traceWord n m) := by
  have hd : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ)
      = (2 ^ m : ℤ) - 3 ^ ones (traceWord n m) := by
    rw [Nat.cast_sub hsub.le]
    push_cast
    ring
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  have hS := slack_identity n m
  constructor
  · intro hy
    have hyz : (n : ℤ) ≤ tstep^[m] n := by exact_mod_cast hy
    have : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ) * n
        ≤ numer (traceWord n m) := by rw [hd]; nlinarith [hS, hpos, hyz]
    exact_mod_cast this
  · intro hp
    have hpz : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ) * n
        ≤ numer (traceWord n m) := by exact_mod_cast hp
    rw [hd] at hpz
    have : (n : ℤ) ≤ tstep^[m] n := by nlinarith [hS, hpos, hpz]
    exact_mod_cast this

/-- **The acyclic criterion**: `n < tstep^[m] n ↔ d·n < numer v`. -/
theorem acyclicParadoxical_criterion (n m : ℕ)
    (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    (n < tstep^[m] n) ↔
      (2 ^ m - 3 ^ ones (traceWord n m)) * n < numer (traceWord n m) := by
  have hd : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ)
      = (2 ^ m : ℤ) - 3 ^ ones (traceWord n m) := by
    rw [Nat.cast_sub hsub.le]
    push_cast
    ring
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  have hS := slack_identity n m
  constructor
  · intro hy
    have hyz : (n : ℤ) < tstep^[m] n := by exact_mod_cast hy
    have : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ) * n
        < numer (traceWord n m) := by rw [hd]; nlinarith [hS, hpos, hyz]
    exact_mod_cast this
  · intro hp
    have hpz : ((2 ^ m - 3 ^ ones (traceWord n m) : ℕ) : ℤ) * n
        < numer (traceWord n m) := by exact_mod_cast hp
    rw [hd] at hpz
    have : (n : ℤ) < tstep^[m] n := by nlinarith [hS, hpos, hpz]
    exact_mod_cast this

/-! ## Exact remainders of few-block words (backing the `≥3 odd blocks` discovery) -/

@[simp] theorem ones_replicate_false (t : ℕ) : ones (List.replicate t false) = 0 := by
  induction t with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ]; simpa [ones] using ih

@[simp] theorem ones_replicate_true (q : ℕ) : ones (List.replicate q true) = q := by
  induction q with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ]; simp [ones, ih]

theorem ones_replicate_true_append (q : ℕ) (w : List Bool) :
    ones (List.replicate q true ++ w) = q + ones w := by
  induction q with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append]; simp [ones, ih]; ring

/-- Prepending `t` even letters doubles the remainder `t` times. -/
theorem numer_replicate_false_append (t : ℕ) (w : List Bool) :
    numer (List.replicate t false ++ w) = 2 ^ t * numer w := by
  induction t with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append]; simp [numer, ih]; ring

/-- **The all-ones-prefix recursion** over `ℤ` (`ring` handles the exponent laws):
`numer (1^q ++ w) = 2^q · numer w + 3^(ones w)·(3^q − 2^q)`. -/
theorem numer_true_prefix (q : ℕ) (w : List Bool) :
    (numer (List.replicate q true ++ w) : ℤ)
      = 2 ^ q * numer w + 3 ^ ones w * (3 ^ q - 2 ^ q) := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    have hr : ones (List.replicate k true ++ w) = k + ones w := ones_replicate_true_append k w
    have : (numer (true :: (List.replicate k true ++ w)) : ℤ)
        = 2 * numer (List.replicate k true ++ w) + 3 ^ (k + ones w) := by
      simp only [numer, hr]; push_cast; ring
    rw [this, ih]; ring

@[simp] theorem numer_replicate_false (t : ℕ) : numer (List.replicate t false) = 0 := by
  have := numer_replicate_false_append t ([] : List Bool)
  simpa using this

theorem ones_append (a b : List Bool) : ones (a ++ b) = ones a + ones b := by
  induction a with
  | nil => simp
  | cons x t ih => cases x <;> simp [ones, ih] <;> ring

/-- Numer of `1^q ++ 0^t` is `3^q − 2^q` (over `ℤ`). -/
theorem numer_true_false (q t : ℕ) :
    (numer (List.replicate q true ++ List.replicate t false) : ℤ) = 3 ^ q - 2 ^ q := by
  rw [numer_true_prefix]; simp

/-- Exact remainder of a **single odd block** `[F]^s [T]^q [F]^t`:
`numer = 2^s (3^q − 2^q)`.  (`s = 0` is Rozier--Terracol Appendix A.) -/
theorem numer_singleBlock (s q t : ℕ) :
    numer (List.replicate s false ++ (List.replicate q true ++ List.replicate t false))
      = 2 ^ s * (3 ^ q - 2 ^ q) := by
  have hle : 2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have hz : (numer (List.replicate s false ++ (List.replicate q true
                ++ List.replicate t false)) : ℤ) = 2 ^ s * (3 ^ q - 2 ^ q) := by
    rw [numer_replicate_false_append]; push_cast; rw [numer_true_false]
  have : (numer (List.replicate s false ++ (List.replicate q true
                ++ List.replicate t false)) : ℤ) = ((2 ^ s * (3 ^ q - 2 ^ q) : ℕ) : ℤ) := by
    rw [hz, Nat.cast_mul, Nat.cast_sub hle]; push_cast; ring
  exact_mod_cast this

/-- Exact remainder of a **two odd block** front-normalized word `[T]^b [F]^c [T]^d [F]^e`
(right-associated): `numer = 3^d (3^b − 2^b) + 2^(b+c) (3^d − 2^d)`. -/
theorem numer_twoBlock (b c d e : ℕ) :
    numer (List.replicate b true ++ (List.replicate c false
             ++ (List.replicate d true ++ List.replicate e false)))
      = 3 ^ d * (3 ^ b - 2 ^ b) + 2 ^ (b + c) * (3 ^ d - 2 ^ d) := by
  have hb : 2 ^ b ≤ 3 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have hd : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by norm_num) d
  have hones : ones (List.replicate c false
                        ++ (List.replicate d true ++ List.replicate e false)) = d := by
    rw [ones_append, ones_append]; simp
  have hinner : (numer (List.replicate c false
                        ++ (List.replicate d true ++ List.replicate e false)) : ℤ)
      = 2 ^ c * (3 ^ d - 2 ^ d) := by
    rw [numer_replicate_false_append]; push_cast; rw [numer_true_false]
  have hz : (numer (List.replicate b true ++ (List.replicate c false
             ++ (List.replicate d true ++ List.replicate e false))) : ℤ)
      = 3 ^ d * (3 ^ b - 2 ^ b) + 2 ^ (b + c) * (3 ^ d - 2 ^ d) := by
    rw [numer_true_prefix, hones, hinner]; push_cast [pow_add]; ring
  have : (numer (List.replicate b true ++ (List.replicate c false
             ++ (List.replicate d true ++ List.replicate e false))) : ℤ)
      = ((3 ^ d * (3 ^ b - 2 ^ b) + 2 ^ (b + c) * (3 ^ d - 2 ^ d) : ℕ) : ℤ) := by
    rw [hz]; push_cast [Nat.cast_sub hb, Nat.cast_sub hd]; ring
  exact_mod_cast this

/-! ## The single odd-block exclusion (Rozier--Terracol Appendix A, proved sorry-free)

The head-block case `[T]^q [F]^t` needs **no** residue bound: with a subcritical coefficient
the additive remainder `3^q − 2^q` is too small to overcome the multiplicative shortfall, for
*every* start realizing the word.  From the identity `2^m y + 2^q = 3^q (n+1)` and `3^q < 2^m`
one gets `2^m y < 2^m (n+1)`, hence `y ≤ n`. -/

/-- Endpoint bound for a **head odd-block** word `[T]^q [F]^t`: `tstep^[q+t] n ≤ n` for every
`n` realizing the word with subcritical coefficient.  (Contains RT Appendix A: no such
segment is paradoxical.) -/
theorem headBlock_endpoint_le (n q t : ℕ)
    (hword : traceWord n (q + t) = List.replicate q true ++ List.replicate t false)
    (hsub : 3 ^ q < 2 ^ (q + t)) :
    tstep^[q + t] n ≤ n := by
  have hm : (2 : ℕ) ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have hid := tstep_iterate_identity (q + t) n
  rw [hword] at hid
  have hones : ones (List.replicate q true ++ List.replicate t false) = q := by
    rw [ones_append]; simp
  have hnum : numer (List.replicate q true ++ List.replicate t false) = 3 ^ q - 2 ^ q := by
    have := numer_singleBlock 0 q t; simpa using this
  rw [hones, hnum] at hid
  -- hid : 2^(q+t) * tstep^[q+t] n = 3^q * n + (3^q - 2^q)
  have key : 2 ^ (q + t) * tstep^[q + t] n + 2 ^ q = 3 ^ q * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hlt : 3 ^ q * (n + 1) < 2 ^ (q + t) * (n + 1) :=
    Nat.mul_lt_mul_of_pos_right hsub (Nat.succ_pos n)
  have h2q : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hy : 2 ^ (q + t) * tstep^[q + t] n < 2 ^ (q + t) * (n + 1) := by omega
  have := Nat.lt_of_mul_lt_mul_left hy
  omega

/-- **Rozier--Terracol Appendix A (formalized)**: a head odd-block word `[T]^q [F]^t` is never
acyclic paradoxical. -/
theorem headBlock_not_acyclicParadoxical (n q t : ℕ)
    (hword : traceWord n (q + t) = List.replicate q true ++ List.replicate t false) :
    ¬ AcyclicParadoxical n (q + t) := by
  rintro ⟨-, -, hsub, hlt⟩
  rw [hword, ones_append] at hsub
  simp only [ones_replicate_true, ones_replicate_false, add_zero] at hsub
  exact absurd (headBlock_endpoint_le n q t hword hsub) (by omega)

/-- **Head-block residue constraint.**  If the first `b` accelerated letters of `n` are all
odd (`traceWord n b = [T]^b`), then `2^b ∣ (n+1)`.  Proof by the `u = x+1` conjugation: an odd
step sends `x+1 = 2u` to `tstep x + 1 = 3u`, so each odd letter contributes one factor of `2`
to `n+1`.  This is the foundational piece of the realizing-residue reconstruction that the
interior two-block exclusion needs. -/
theorem headBlock_dvd_succ (n b : ℕ)
    (hword : traceWord n b = List.replicate b true) : 2 ^ b ∣ (n + 1) := by
  induction b generalizing n with
  | zero => simp
  | succ k ih =>
    rw [traceWord, List.replicate_succ, List.cons.injEq] at hword
    obtain ⟨hhead, htail⟩ := hword
    have hodd : n % 2 = 1 := by
      by_contra h
      rw [decide_eq_true_eq] at hhead
      exact h hhead
    have hdvd : 2 ^ k ∣ (tstep n + 1) := ih (tstep n) htail
    obtain ⟨u, hu⟩ : 2 ∣ (n + 1) := by omega
    have hts : tstep n + 1 = 3 * u := by
      unfold tstep; rw [if_neg (by omega)]; omega
    rw [hts] at hdvd
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by decide)
    have hu2 : 2 ^ k ∣ u := hcop.dvd_of_dvd_mul_left hdvd
    rw [hu, pow_succ, mul_comm (2 ^ k) 2]
    exact mul_dvd_mul_left 2 hu2

/-- **Discovery (≥ 3 odd blocks).**  Exhaustively verified in `experiments/paradoxical.py`
(all `≤2`-block front-normalized words to length `30`; two-block words to length `38`): a
word whose ones form at most two contiguous blocks realizes **no** acyclic paradoxical start.
This strictly generalizes Rozier--Terracol Appendix A (now proved sorry-free as
`headBlock_not_acyclicParadoxical`, the `b`-only head-block, `c = ∞` degenerate case).  The
`numer` closed forms above are the proved kernel; the open arithmetic core for a genuine
*interior* gap (`c ≥ 1` with a second block) is a lower bound on the realizing residue that
closes criterion (P) — the head-block proof avoids it because a pure head block has remainder
only `3^q − 2^q`, too small on its own.  Stated here as the next formal obligation. -/
theorem le_two_blocks_not_acyclicParadoxical
    (b c d e n : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hword : traceWord n (b + c + d + e)
      = List.replicate b true ++ List.replicate c false
          ++ List.replicate d true ++ List.replicate e false) :
    ¬ AcyclicParadoxical n (b + c + d + e) := by
  sorry

end CollatzMoonshot.FrontA
