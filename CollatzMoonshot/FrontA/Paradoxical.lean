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

/-- **Word decomposition.**  The parity itinerary of `i+j` steps splits at step `i`:
`traceWord n (i+j) = traceWord n i ++ traceWord (tstep^[i] n) j`.  The reconstruction tool for
extracting the individual blocks of a multi-block word. -/
theorem traceWord_add (n i j : ℕ) :
    traceWord n (i + j) = traceWord n i ++ traceWord (tstep^[i] n) j := by
  induction i generalizing n with
  | zero => simp [traceWord]
  | succ k ih =>
    rw [Nat.succ_add, traceWord, traceWord, List.cons_append, ih (tstep n),
      Function.iterate_succ_apply]

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

set_option maxHeartbeats 800000 in
/-- **Sharp elementary regime of the residue core (integer ceiling, no least residue).**
The "gap" is stated in a division-free `∀`-form: *for every* `w` with `2^(c+d) − 2^c + 1 ≤
3^b·w`, the strict bound `3^d(2^c − 1) − 2^(c+d) < (2^m − 3^(b+d))·w` holds.  Instantiated at
the actual `w₁ = (n+1)/2^b` (which satisfies the antecedent because `w₂ ≥ 1 ⇒ X ≥ 2^d − 1 ⇒
3^b·w₁ = 2^c·X + 1 ≥ 2^(c+d) − 2^c + 1`), this contradicts the contrapositive upper bound
`(2^m − 3^(b+d))·w₁ ≤ 3^d(2^c − 1) − 2^(c+d)` derived from the exact identity
`2^m·y + 2^(b+c+d) = 3^(b+d)(n+1) + 3^d·2^b(2^c−1)` under `n < y`.

Using the *integer* lower bound on `w₁` (rather than the real-valued `w₁ ≥ t/3^b`) makes the
gap hold for **all** subcritical `(b,c,d,e)` except exactly two near-critical tuples,
`(2,3,3,0)` and `(3,3,2,0)` (exhaustively checked to `b,c,d,e < 34`); both are closed
separately (`residue_core_exc1`/`exc2`).  No least-residue argument is used here. -/
theorem core_of_gap (b c d e n X y : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * y + 2 ^ d = 3 ^ d * (X + 1))
    (hsub : 3 ^ (b + d) < 2 ^ (b + c + d + e))
    (hgap : ∀ w : ℕ, 2 ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w →
        (3 ^ d * (2 ^ c - 1) - 2 ^ (c + d) : ℤ)
          < (2 ^ (b + c + d + e) - 3 ^ (b + d)) * w) :
    y ≤ n := by
  -- Extract `w₁` with `n+1 = 2^b·w₁` and `3^b·w₁ = 2^c·X + 1`.
  have key : 3 ^ b * (n + 1) = 2 ^ b * (2 ^ c * X + 1) := by rw [← hI, pow_add]; ring
  have hcop1 : Nat.Coprime (2 ^ b) (3 ^ b) :=
    Nat.Coprime.pow_right b (Nat.Coprime.pow_left b (show Nat.Coprime 2 3 by decide))
  obtain ⟨w1, hw1⟩ : (2 : ℕ) ^ b ∣ (n + 1) := hcop1.dvd_of_dvd_mul_left ⟨2 ^ c * X + 1, key⟩
  have e1 : 3 ^ b * w1 = 2 ^ c * X + 1 := by
    have h : 2 ^ b * (3 ^ b * w1) = 2 ^ b * (2 ^ c * X + 1) := by rw [← key, hw1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  -- `X ≥ 2^d − 1` from `2^d ∣ (X+1)` (which follows from hII).
  have hXlb : 2 ^ d ≤ X + 1 := by
    have h3 : 3 ^ d * (X + 1) = 2 ^ d * (2 ^ e * y + 1) := by rw [← hII, pow_add]; ring
    have hcop2 : Nat.Coprime (2 ^ d) (3 ^ d) :=
      Nat.Coprime.pow_right d (Nat.Coprime.pow_left d (show Nat.Coprime 2 3 by decide))
    exact Nat.le_of_dvd (Nat.succ_pos X) (hcop2.dvd_of_dvd_mul_left ⟨2 ^ e * y + 1, h3⟩)
  -- Antecedent of the gap for `w = w₁`.
  have ht : 2 ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w1 := by
    rw [e1, pow_add]
    have hmul : 2 ^ c * 2 ^ d ≤ 2 ^ c * (X + 1) := Nat.mul_le_mul (le_refl _) hXlb
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hgw := hgap w1 ht
  -- Contrapositive: under `n < y`, `(2^m − 3^(b+d))·w₁ ≤ 3^d(2^c−1) − 2^(c+d)`.
  by_contra hcon
  push_neg at hcon
  have hconz : (n : ℤ) + 1 ≤ y := by exact_mod_cast hcon
  have hw1z : (n : ℤ) + 1 = 2 ^ b * w1 := by exact_mod_cast hw1
  have hIz : (2 : ℤ) ^ (b + c) * X + 2 ^ b = 3 ^ b * ((n : ℤ) + 1) := by exact_mod_cast hI
  have hIIz : (2 : ℤ) ^ (d + e) * y + 2 ^ d = 3 ^ d * ((X : ℤ) + 1) := by exact_mod_cast hII
  have hsubz : (3 : ℤ) ^ (b + d) < 2 ^ (b + c + d + e) := by exact_mod_cast hsub
  have hgwz : (3 ^ d * (2 ^ c - 1) - 2 ^ (c + d) : ℤ)
      < (2 ^ (b + c + d + e) - 3 ^ (b + d)) * w1 := by exact_mod_cast hgw
  simp only [pow_add] at hIz hIIz hsubz hgwz hw1z
  -- MAIN identity.
  have hMAIN : (2 : ℤ) ^ b * 2 ^ c * 2 ^ d * 2 ^ e * y + 2 ^ b * 2 ^ c * 2 ^ d
      = 3 ^ b * 3 ^ d * ((n : ℤ) + 1) + 3 ^ d * 2 ^ b * (2 ^ c - 1) := by
    linear_combination (3 : ℤ) ^ d * hIz + 2 ^ b * 2 ^ c * hIIz
  have p2b : (0 : ℤ) < 2 ^ b := by positivity
  have hy : (2 : ℤ) ^ b * 2 ^ c * 2 ^ d * 2 ^ e * ((n : ℤ) + 1)
      ≤ 2 ^ b * 2 ^ c * 2 ^ d * 2 ^ e * y := by
    apply mul_le_mul_of_nonneg_left hconz; positivity
  -- UP in `n`-form, then divide by `2^b` to the `w₁`-form.
  have hUPn : ((2 : ℤ) ^ b * 2 ^ c * 2 ^ d * 2 ^ e - 3 ^ b * 3 ^ d) * ((n : ℤ) + 1)
      ≤ 2 ^ b * (3 ^ d * (2 ^ c - 1) - 2 ^ c * 2 ^ d) := by nlinarith [hMAIN, hy]
  have hUP : ((2 : ℤ) ^ b * 2 ^ c * 2 ^ d * 2 ^ e - 3 ^ b * 3 ^ d) * w1
      ≤ 3 ^ d * (2 ^ c - 1) - 2 ^ c * 2 ^ d := by
    have hstep : (2 : ℤ) ^ b * (((2 : ℤ) ^ b * 2 ^ c * 2 ^ d * 2 ^ e - 3 ^ b * 3 ^ d) * w1)
        ≤ 2 ^ b * (3 ^ d * (2 ^ c - 1) - 2 ^ c * 2 ^ d) := by
      rw [hw1z] at hUPn; nlinarith [hUPn]
    exact le_of_mul_le_mul_left hstep p2b
  linarith [hUP, hgwz]

/-- Exceptional tuple `(b,c,d,e) = (2,3,3,0)` of the residue core: the segment identities
become the concrete linear system `32·X + 4 = 9·(n+1)`, `8·y + 8 = 27·(X+1)`, closed by
`omega`.  (One of the only two tuples where the sharp gap `core_of_gap` fails.) -/
theorem residue_core_exc1 (n X y : ℕ)
    (hI : 2 ^ (2 + 3) * X + 2 ^ 2 = 3 ^ 2 * (n + 1))
    (hII : 2 ^ (3 + 0) * y + 2 ^ 3 = 3 ^ 3 * (X + 1)) :
    y ≤ n := by norm_num at hI hII ⊢; omega

/-- Exceptional tuple `(b,c,d,e) = (3,3,2,0)` of the residue core: the concrete system
`64·X + 8 = 27·(n+1)`, `4·y + 4 = 9·(X+1)`, closed by `omega`. -/
theorem residue_core_exc2 (n X y : ℕ)
    (hI : 2 ^ (3 + 3) * X + 2 ^ 3 = 3 ^ 3 * (n + 1))
    (hII : 2 ^ (2 + 0) * y + 2 ^ 2 = 3 ^ 2 * (X + 1)) :
    y ≤ n := by norm_num at hI hII ⊢; omega

/-- **Near-critical containment (the sharpened crux).**  This isolates *exactly* what remains
open in the two-block exclusion, as a self-contained arithmetic statement with clean
hypotheses.  Suppose the sharp gap of `core_of_gap` fails: there is a natural `w` with
`2^(c+d) − 2^c + 1 ≤ 3^b·w` (the lower bound `w ≥ ⌈L/3^b⌉`, forced by `w₂ ≥ 1 ⇒ X ≥ 2^d − 1`)
yet `(2^m − 3^(b+d))·w ≤ 3^d(2^c − 1) − 2^(c+d)` (the contrapositive upper bound `w ≤ U₁/D`).
Under whole-word subcriticality this **forces** `(b,c,d,e)` to be one of the two near-critical
tuples `(2,3,3,0)` or `(3,3,2,0)`.

Exhaustively verified: the set of tuples admitting such a `w` is *exactly* those two
(`scratchpad/squeeze.py`, checked `b,c,d,e < 45`).

**What this lap proved sorry-free (the elementary squeeze):** from the two bounds one gets, by
one multiplication each and cancelling `2^c > 0`, the division-free near-critical inequality
  `(2^m − 3^(b+d))·(2^d − 1) < 3^(b+d)`  `[hsqueeze]`
together with the "real bound" `(2^m − 3^(b+d))·L ≤ 3^b·U₁`.  These squeeze `2^m/3^(b+d)` into
the multiplicative window `(1, 2^d/(2^d−1))`, whose width `→ 1` as `d` grows.

**What remains (the sole open obligation):** the containment itself — that this near-critical
window, intersected with the *integrality* of `w` (equivalently `⌈L/3^b⌉ ≤ U₁/D`), admits only
the two listed tuples.

**REFUTED this lap (attack #1 is dead):** one cannot bound `b+d` (nor `d`) from the real bound
`D·L ≤ 3^b·U₁` alone.  Exhaustively (`scratchpad/dbig.py`, `b+d ≤ 306`), the real-bound set is
genuinely *infinite* in every parameter: `d` reaches `9` (first witness `b+d = 306`, tracking the
good rational approximations `2^m/3^k` at continued-fraction denominators `k = 5,17,29,41,147,…`),
and `b,c,e` are unbounded.  So ceiling-discreteness + the real bound will NEVER give a finite box;
the *integrality* of `w` (`⌈L/3^b⌉ ≤ U₁/D`) is strictly essential.

Concretely the bracket is `3^(b+d) < 2^m` and `2^m·(2^d − 1) < 3^(b+d)·2^d` (from `hsqueeze`),
i.e. `2^m/3^(b+d) ∈ (1, 2^d/(2^d−1))`; the residual finiteness is a genuine `2^m` vs `3^k`
separation (effective irrationality of `log₂ 3`, Baker).  Narrow lap by lap; see `PENDING_WORK.md`. -/
theorem near_critical_containment (b c d e w : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hsub : 3 ^ (b + d) < 2 ^ (b + c + d + e))
    (hlo : 2 ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w)
    (hhi : ((2 ^ (b + c + d + e) - 3 ^ (b + d) : ℤ)) * w
        ≤ 3 ^ d * (2 ^ c - 1) - 2 ^ (c + d)) :
    (b = 2 ∧ c = 3 ∧ d = 3 ∧ e = 0) ∨ (b = 3 ∧ c = 3 ∧ d = 2 ∧ e = 0) := by
  -- Work in ℤ.  Abbreviations: D = 2^m − 3^(b+d) > 0, U₁ = 3^d(2^c−1) − 2^(c+d), L = 2^(c+d)−2^c+1.
  have hle : (2 : ℕ) ^ c ≤ 2 ^ (c + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsubz : (3 : ℤ) ^ (b + d) < 2 ^ (b + c + d + e) := by exact_mod_cast hsub
  have hloz : (2 : ℤ) ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w := by
    have := hlo; zify [hle] at this; linarith
  set D : ℤ := 2 ^ (b + c + d + e) - 3 ^ (b + d) with hDdef
  set U1 : ℤ := 3 ^ d * (2 ^ c - 1) - 2 ^ (c + d) with hU1def
  set L : ℤ := 2 ^ (c + d) - 2 ^ c + 1 with hLdef
  have hDpos : (0 : ℤ) < D := by rw [hDdef]; linarith
  -- `w ≥ 1`.
  have hLpos : (1 : ℤ) ≤ L := by
    have : (2 : ℤ) ^ c ≤ 2 ^ (c + d) := by exact_mod_cast hle
    rw [hLdef]; linarith
  have hwpos : (1 : ℤ) ≤ (w : ℤ) := by
    have h3b : (1 : ℤ) ≤ 3 ^ b := one_le_pow₀ (by norm_num)
    nlinarith [hloz, hLpos, h3b]
  -- Squeeze 1 (the "real bound"):  D·L ≤ 3^b·U₁.
  have h3bpos : (0 : ℤ) < 3 ^ b := by positivity
  have s1 : D * L ≤ 3 ^ b * U1 := by
    have t1 : D * L ≤ D * (3 ^ b * w) := by
      have := mul_le_mul_of_nonneg_left hloz hDpos.le; linarith
    have t3 : (3 : ℤ) ^ b * (D * w) ≤ 3 ^ b * U1 :=
      mul_le_mul_of_nonneg_left hhi h3bpos.le
    nlinarith [t1, t3]
  -- L ≥ 2^c·(2^d − 1)  and  U₁ < 3^d·2^c.
  have hpcd : (2 : ℤ) ^ (c + d) = 2 ^ c * 2 ^ d := by rw [pow_add]
  have hLge : (2 : ℤ) ^ c * (2 ^ d - 1) ≤ L := by rw [hLdef, hpcd]; ring_nf; linarith
  have hU1lt : U1 < 3 ^ d * 2 ^ c := by
    have h3d : (0 : ℤ) < 3 ^ d := by positivity
    have h2cd : (0 : ℤ) < 2 ^ (c + d) := by positivity
    rw [hU1def]; nlinarith [h3d, h2cd]
  -- Squeeze 2 (the near-critical window):  D·(2^d − 1) < 3^(b+d).
  have h2cpos : (0 : ℤ) < 2 ^ c := by positivity
  have h3bd : (3 : ℤ) ^ (b + d) = 3 ^ b * 3 ^ d := by rw [pow_add]
  have hsqueeze : D * (2 ^ d - 1) < 3 ^ (b + d) := by
    have a1 : D * (2 ^ c * (2 ^ d - 1)) ≤ D * L :=
      mul_le_mul_of_nonneg_left hLge hDpos.le
    have a2 : (3 : ℤ) ^ b * U1 < 3 ^ b * (3 ^ d * 2 ^ c) :=
      mul_lt_mul_of_pos_left hU1lt h3bpos
    -- ⇒ D·(2^d−1)·2^c < 3^(b+d)·2^c, then cancel 2^c.
    have hmul : D * (2 ^ d - 1) * 2 ^ c < 3 ^ (b + d) * 2 ^ c := by
      rw [h3bd]; nlinarith [a1, a2, s1]
    exact lt_of_mul_lt_mul_right hmul h2cpos.le
  -- Clean power bracket:  `2^m·(2^d − 1) < 3^(b+d)·2^d`  (⇔ `2^m/3^(b+d) < 2^d/(2^d−1)`).
  have hbracket : (2 : ℤ) ^ (b + c + d + e) * (2 ^ d - 1) < 3 ^ (b + d) * 2 ^ d := by
    rw [hDdef] at hsqueeze; nlinarith [hsqueeze]
  -- The residual finiteness containment.  With `3^(b+d) < 2^m` (hsub) this pins
  -- `2^m/3^(b+d) ∈ (1, 2^d/(2^d−1))`; integrality of `w` (hlo/hhi) then selects the two tuples.
  -- Genuine `2^m` vs `3^k` separation content — disclosed, narrowed lap by lap.
  sorry

/-- **The isolated arithmetic crux of the two-block exclusion.**  Purely a statement about
naturals: given the two exact head-block segment identities
`2^(b+c)·X + 2^b = 3^b·(n+1)` (segment `[T]^b[F]^c`, start `n`, interior odd value `X`) and
`2^(d+e)·y + 2^d = 3^d·(X+1)` (segment `[T]^d[F]^e`, start `X`, endpoint `y`), together with
whole-word subcriticality `3^(b+d) < 2^m` and `n > 2`, the endpoint satisfies `y ≤ n`.

This is **equivalent** to the two-block exclusion (the segment identities exactly encode the
realizing residue: `X` natural ⟺ `2^(b+c) ∣ 3^b(n+1) − 2^b`, and `y` natural adds the second
2-adic constraint).  It is verified true over a large exact range
(`experiments/paradoxical.py`: 1893 solutions, 0 violations) but is **not** closable from
`w₁ ≥ 1`/`w₂ ≥ 1` alone — it requires the joint 2-adic/3-adic force selecting the minimal
realizing residue.  Disclosed as the single remaining `src/` obligation on this front.  The
next attack (linear-Diophantine `3^b w₁ − 2^(c+d) w₂ = 1 − 2^c`; least-residue bound via
`ZMod (3^b)`) is written in `PENDING_WORK.md`.  Because the statement is self-contained
arithmetic, it is a clean candidate for an independent formal attack. -/
theorem two_block_residue_core (b c d e n X y : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1))
    (hII : 2 ^ (d + e) * y + 2 ^ d = 3 ^ d * (X + 1))
    (hsub : 3 ^ (b + d) < 2 ^ (b + c + d + e))
    (hn : 2 < n) :
    y ≤ n := by
  by_cases hgap : ∀ w : ℕ, 2 ^ (c + d) - 2 ^ c + 1 ≤ 3 ^ b * w →
      (3 ^ d * (2 ^ c - 1) - 2 ^ (c + d) : ℤ)
        < (2 ^ (b + c + d + e) - 3 ^ (b + d)) * w
  · -- Sharp elementary regime: closed without any least-residue argument.
    exact core_of_gap b c d e n X y hb hd hI hII hsub hgap
  · -- Residual: the sharp gap fails.  Negation gives a witness `w` with `L ≤ 3^b·w` and
    -- `D·w ≤ U₁`; `near_critical_containment` forces `(b,c,d,e) ∈ {(2,3,3,0),(3,3,2,0)}`, then
    -- the concrete tuples close by `residue_core_exc1`/`exc2`.
    push_neg at hgap
    obtain ⟨w, hlo, hhi⟩ := hgap
    rcases near_critical_containment b c d e w hb hd hsub hlo hhi with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact residue_core_exc1 n X y hI hII
    · exact residue_core_exc2 n X y hI hII

/-- **Discovery (≥ 3 odd blocks).**  Exhaustively verified in `experiments/paradoxical.py`
(all `≤2`-block front-normalized words to length `30`; two-block words to length `38`): a
word whose ones form at most two contiguous blocks realizes **no** acyclic paradoxical start.
This strictly generalizes Rozier--Terracol Appendix A (`headBlock_not_acyclicParadoxical`).

**Proof decomposition (this lap).**  Split the itinerary at step `b+c` into two head-block
segments `[T]^b[F]^c` (start `n`, endpoint `X`) and `[T]^d[F]^e` (start `X`, endpoint `y`).
Subcriticality of the whole word `3^(b+d) < 2^m` forbids *both* blocks from being
supercritical, leaving three cases:

* **Case A — both blocks subcritical: PROVED sorry-free.**  Two applications of
  `headBlock_endpoint_le` give `y ≤ X ≤ n`, so the segment is not acyclic paradoxical.
* **Case B — first super, second subcritical / Case C — first subcritical, second super:**
  the single-block bound closes one inequality (`X ≤ n` in C, `y ≤ X` in B) but not the
  target `y ≤ n`.  Both reduce to the **joint 2-adic/3-adic residue force** on the realizing
  start: the minimal interior odd value `X` selected by `3^b ∣ 2^c X + 1` is large enough to
  close criterion (P).  Verified insufficient from `w₁ ≥ 1` alone (needs the true 3-adic
  minimal `w₂`); disclosed as two `sorry`s.  See `FRONT-A-PARADOXICAL.md` RESULTS / `GOAL2'`
  in `PENDING_WORK.md`. -/
theorem le_two_blocks_not_acyclicParadoxical
    (b c d e n : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hword : traceWord n (b + c + d + e)
      = List.replicate b true ++ List.replicate c false
          ++ List.replicate d true ++ List.replicate e false) :
    ¬ AcyclicParadoxical n (b + c + d + e) := by
  rintro ⟨hn, hm, hsub, hlt⟩
  set X := tstep^[b + c] n with hX
  -- The two-block word has exactly `b + d` odd letters, so subcriticality is `3^(b+d) < 2^m`.
  have hones : ones (traceWord n (b + c + d + e)) = b + d := by
    rw [hword, ones_append, ones_append, ones_append]
    simp
  rw [hones] at hsub
  -- Split the itinerary at step `b + c` into the two head-block segments `[T]^b[F]^c`
  -- (from `n`, reaching `X`) and `[T]^d[F]^e` (from `X`, reaching the endpoint).
  have hadd : traceWord n (b + c + d + e)
      = traceWord n (b + c) ++ traceWord X (d + e) := by
    have h := traceWord_add n (b + c) (d + e)
    rwa [show (b + c) + (d + e) = b + c + d + e from by ring, ← hX] at h
  have hWeq : traceWord n (b + c) ++ traceWord X (d + e)
      = (List.replicate b true ++ List.replicate c false)
          ++ (List.replicate d true ++ List.replicate e false) := by
    rw [← hadd, hword]; simp only [List.append_assoc]
  have hlenA : (traceWord n (b + c)).length
      = (List.replicate b true ++ List.replicate c false).length := by
    simp
  obtain ⟨hsegA, hsegB⟩ := List.append_inj hWeq hlenA
  -- The endpoint of the whole word is the endpoint of the second segment applied to `X`.
  have hy_eq : tstep^[b + c + d + e] n = tstep^[d + e] X := by
    rw [hX, show b + c + d + e = (d + e) + (b + c) from by ring, Function.iterate_add_apply]
  rw [hy_eq] at hlt
  -- Extract the two exact head-block segment identities from `tstep_iterate_identity`.
  have h2b : (2 : ℕ) ^ b ≤ 3 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have h2d : (2 : ℕ) ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by norm_num) d
  have hnumA : numer (List.replicate b true ++ List.replicate c false) = 3 ^ b - 2 ^ b := by
    have := numer_singleBlock 0 b c; simpa using this
  have hnumB : numer (List.replicate d true ++ List.replicate e false) = 3 ^ d - 2 ^ d := by
    have := numer_singleBlock 0 d e; simpa using this
  have hI : 2 ^ (b + c) * X + 2 ^ b = 3 ^ b * (n + 1) := by
    have hid := tstep_iterate_identity (b + c) n
    rw [hsegA, ← hX] at hid
    simp only [ones_append, ones_replicate_true, ones_replicate_false, add_zero, hnumA] at hid
    -- hid : 2^(b+c) * X = 3^b * n + (3^b - 2^b)
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hII : 2 ^ (d + e) * (tstep^[d + e] X) + 2 ^ d = 3 ^ d * (X + 1) := by
    have hid := tstep_iterate_identity (d + e) X
    rw [hsegB] at hid
    simp only [ones_append, ones_replicate_true, ones_replicate_false, add_zero, hnumB] at hid
    rw [Nat.mul_add, Nat.mul_one]; omega
  -- Case split on the criticality of the first block.  Subcriticality of the *whole* word
  -- forbids both blocks from being supercritical simultaneously.
  by_cases hbc : 3 ^ b < 2 ^ (b + c)
  · -- First block subcritical: `X ≤ n` by the head-block lemma (Appendix A).
    have hXn : X ≤ n := headBlock_endpoint_le n b c hsegA hbc
    by_cases hde : 3 ^ d < 2 ^ (d + e)
    · -- **Case A (both blocks subcritical): PROVED, no residue.**  Second head-block lemma
      -- gives `tstep^[d+e] X ≤ X ≤ n`, contradicting `n < endpoint`.
      have hyX : tstep^[d + e] X ≤ X := headBlock_endpoint_le X d e hsegB hde
      omega
    · -- **Case C (first sub, second supercritical).**  `X ≤ n` alone is insufficient; close via
      -- the isolated arithmetic core `two_block_residue_core`.
      exact absurd hlt (by
        have := two_block_residue_core b c d e n X (tstep^[d + e] X) hb hd hI hII hsub hn
        omega)
  · -- **Case B (first block supercritical).**  The single-block bound gives no help toward
    -- `endpoint ≤ n` (the supercritical first block makes `X ≥ n`); close via the core.
    exact absurd hlt (by
      have := two_block_residue_core b c d e n X (tstep^[d + e] X) hb hd hI hII hsub hn
      omega)

end CollatzMoonshot.FrontA
