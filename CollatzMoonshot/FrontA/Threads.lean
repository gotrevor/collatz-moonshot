/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Invariant
import CollatzMoonshot.Assumed.Tao2019

/-!
# The Front A thread board: ruling out divergent orbits

`FRONT-A-ROUTES.md` is the prose map; this file pins its main logical interfaces.
As in `FrontB/Threads.lean`, our proposed new mathematics is a `def`, never an
axiom.  The proved statements here are wiring or falsification lemmas.

The main correction recorded by this board is that **many divergent starting
values do not contradict Tao 2019**.  If they all enter one fixed divergent seed
`d`, their orbit minima are at most `d`, so they are eventually Tao-good for
every function tending to infinity.  A backward-tree argument must preserve a
floor while it amplifies successively higher tails of the divergent orbit.
-/

namespace CollatzMoonshot.FrontA

open Filter

/-- `n` reaches the value `d` after finitely many Collatz steps. -/
def ReachesValue (n d : ℕ) : Prop := ∃ k, step^[k] n = d

/-- Entering a fixed seed puts that seed above the minimum of the whole orbit. -/
theorem orbitMin_le_of_reachesValue {n d : ℕ} (h : ReachesValue n d) : orbitMin n ≤ d := by
  obtain ⟨k, hk⟩ := h
  apply Nat.sInf_le
  exact ⟨k, hk⟩

/-- The good set appearing in the local rendering of Tao 2019. -/
def TaoGood (f : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (orbitMin n : ℝ) < f n}

/-- **Why raw backward density is insufficient.**  A predecessor of a fixed
seed `d` is Tao-good whenever the test function at that predecessor exceeds
`d`, even if `d` and the predecessor both have divergent orbits. -/
theorem mem_taoGood_of_reachesValue {f : ℕ → ℝ} {n d : ℕ} (hn : 1 ≤ n)
    (hreach : ReachesValue n d) (hdf : (d : ℝ) < f n) : n ∈ TaoGood f := by
  refine ⟨hn, ?_⟩
  have hle : (orbitMin n : ℝ) ≤ d := by
    exact_mod_cast orbitMin_le_of_reachesValue hreach
  exact hle.trans_lt hdf

/-! ## Thread A1: orbit-limit parity rigidity -/

/-- **Strength audit for W1.**  W1 already rules out a positive nontrivial
cycle: the uniform invariant measure on that cycle is supported on its orbit
closure and gives `{1,2,4}` zero mass.  This is theorem-grade finite measure
theory, but remains a stated target until the uniform cycle measure is built in
the Lean layer.  In particular W1 is not a Front-A-only pin. -/
def W1AlreadyOwnsFrontB : Prop := MeasureRigidityW1 → NoNontrivialCycle

/-- **Calibration target for W1'.**  The forward implication is milestone M2'.
For the reverse implication, `NoDivergentOrbit` makes every positive orbit
eventually periodic; the unique invariant probability on its finite orbit
closure is uniform on the eventual cycle, whose odd frequency is strictly below
`log 2 / log 6` by `3^a < 2^b`.

Thus W1' should be an exact measure-theoretic rendering of Front A, not itself a
weaker conjecture. -/
def W1PrimeIffFrontA : Prop := ParityRigidityW1' ↔ NoDivergentOrbit

/-- A scalar empirical limit of the only observable the drift argument consumes.
This avoids quantifying over invariant measures in the orbit closure that are
never sampled by the actual orbit. -/
def IsOddFrequencyLimit (n : ℕ) (q : ℝ) : Prop :=
  ∃ ks : ℕ → ℕ, StrictMono ks ∧
    Tendsto (fun j => (oddSteps n (ks j) : ℝ) / ks j) atTop (nhds q)

/-- **The weaker empirical pin.**  Every positive orbit has at least one
subsequential odd-frequency limit below the sharp threshold.  Only empirical
limits are mentioned; current W1' quantifies over every invariant measure
supported on the orbit closure.  Compactness, finite-shift invariance, and the
free-floor lemma should turn this into Front A. -/
def EmpiricalParityRigidity : Prop :=
  ∀ n, 1 ≤ n → ∃ q, IsOddFrequencyLimit n q ∧ q < sharpThreshold

/-- The intended consumption statement for the weaker empirical pin.  It is
left open because its proof needs the subsequence/finite-shift plumbing that M2'
is meant to build. -/
def EmpiricalParityClosesFrontA : Prop :=
  EmpiricalParityRigidity → NoDivergentOrbit

/-! ## Thread A2: Tao forward × backward, with the missing condition made exact -/

/-- **Floor-preserving saturation.**  A divergent orbit must manufacture a
function `f → ∞` for which Tao's good set fails to have logarithmic density one.

The intended mechanism is stronger than this minimal output statement: take
tails whose forward floors tend to infinity (`exists_floor_of_diverges`) and
amplify them through backward branches while keeping every intermediate value
above `f` at the branch's starting scale.  Merely making the backward basin of
one fixed seed large cannot establish this, by
`mem_taoGood_of_reachesValue`. -/
def FloorPreservingSaturation : Prop :=
  (∃ n, 1 ≤ n ∧ Diverges n) →
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ ¬ HasLogDensityOne (TaoGood f)

/-- Tao 2019 plus floor-preserving saturation closes Front A immediately. -/
theorem noDivergent_of_floorPreservingSaturation
    (hSat : FloorPreservingSaturation) : NoDivergentOrbit := by
  intro n hn hdiv
  obtain ⟨f, hf, hbad⟩ := hSat ⟨n, hn, hdiv⟩
  apply hbad
  simpa [TaoGood] using Assumed.tao_2019_almost_bounded f hf

/-! ## Thread A3: direct certificates -/

/-- A termination certificate need only force descent from starts assumed to be
divergent; this is genuinely Front A and permits bounded nontrivial cycles. -/
def DivergentDescentCertificate : Prop :=
  ∀ n, 1 ≤ n → Diverges n → ∃ k, step^[k] n < n

/-- The certificate's axiom-clean consumption theorem. -/
theorem noDivergent_of_certificate (h : DivergentDescentCertificate) : NoDivergentOrbit :=
  noDivergent_of_descends_if_diverges h

/-- A finite-witness certificate that respects the two-front split: every
positive start either repeats (bounded, but possibly on a nontrivial cycle) or
strictly descends.  Unlike `DescentAll`, this statement does not ask the cycle
front to disappear. -/
def RepeatOrDescendCertificate : Prop :=
  ∀ n, 1 ≤ n →
    (∃ i j, i < j ∧ step^[i] n = step^[j] n) ∨
    ∃ k, step^[k] n < n

/-- A bounded orbit repeats.  This is the finite pigeonhole half of Front A,
factored out so certificate statements can use it without importing the cycle
classification front. -/
theorem exists_orbit_repeat_of_not_diverges {n : ℕ} (hnd : ¬ Diverges n) :
    ∃ i j, i < j ∧ step^[i] n = step^[j] n := by
  have hb : ∃ M, ∀ k, step^[k] n < M := by
    unfold Diverges at hnd
    push Not at hnd
    exact hnd
  obtain ⟨M, hM⟩ := hb
  obtain ⟨i, j, hij, hfeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k : ℕ => (⟨step^[k] n, hM k⟩ : Fin M))
  have heq : step^[i] n = step^[j] n := by simpa using hfeq
  rcases Nat.lt_trichotomy i j with hlt | heq' | hgt
  · exact ⟨i, j, hlt, heq⟩
  · exact absurd heq' hij
  · exact ⟨j, i, hgt, heq.symm⟩

/-- Repeat-or-descend is enough for Front A: a divergent orbit cannot take the
repeat branch, and the remaining divergent-descent condition is consumed by
strong induction. -/
theorem noDivergent_of_repeatOrDescend (h : RepeatOrDescendCertificate) :
    NoDivergentOrbit := by
  apply noDivergent_of_descends_if_diverges
  intro n hn hdiv
  rcases h n hn with hrep | hdesc
  · obtain ⟨i, j, hij, heq⟩ := hrep
    exact (not_diverges_of_repeat hij heq hdiv).elim
  · exact hdesc

/-- **Exact Front-A calibration.**  Repeat-or-descend is neither weaker nor
stronger than Front A: a nondivergent orbit takes the repeat branch, while the
forward implication is `noDivergent_of_repeatOrDescend`. -/
theorem repeatOrDescend_iff_noDivergent :
    RepeatOrDescendCertificate ↔ NoDivergentOrbit := by
  constructor
  · exact noDivergent_of_repeatOrDescend
  · intro hnd n hn
    exact Or.inl (exists_orbit_repeat_of_not_diverges (hnd n hn))

end CollatzMoonshot.FrontA
