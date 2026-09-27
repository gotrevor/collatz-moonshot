import Mathlib
import CollatzMoonshot.FrontB.Dictionary

/-!
# Obstructions encountered while pursuing three arithmetic lifts

The semigroup length obstruction and the pair-integrality equivalence are
proved here.  The approximate-fixed-series statement and decay arithmetic
are recorded below; PositiveApproximation.lean proves the general coefficient
identity against these unchanged definitions.  See RESEARCH-2026-09-27-arithmetic-lifts-followup.md.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

open CollatzMoonshot.FrontB

def certificateValue (twos : ℕ) (sources : List ℕ) : ℚ :=
  (2 : ℚ) ^ twos * (sources.map fun (u : ℕ) => (u : ℚ) / (tstep u : ℚ)).prod

def validSources (sources : List ℕ) : Prop :=
  ∀ u ∈ sources, 0 < u ∧ u % 2 = 1

def certificate71 : List ℕ :=
  [25, 19, 29, 11, 17, 13, 5, 355, 533, 7, 7, 11, 17, 55, 65, 83]

theorem certificate71_valid : validSources certificate71 := by
  unfold validSources
  native_decide

theorem certificate71_value : certificateValue 16 certificate71 = 71 := by native_decide

theorem certificate71_length : 16 + certificate71.length = 32 := by decide

theorem seventy_one_no_short_path :
    ∀ k ∈ Finset.range 33, (tstep^[k]) 71 ≠ 1 := by native_decide

theorem seventy_one_reaches_one : (tstep^[65]) 71 = 1 := by native_decide

theorem two_edge_repair_anchor :
    certificateValue 0 [23, 245] = certificateValue 0 [35, 53] ∧
    certificateValue 4 [35, 53] = 7 ∧ tstep 35 = 53 ∧ tstep 53 = 80 := by
  native_decide

/-- Cross-multiplied identity for the parametric neutral exchange.
For positive t=1 mod4 all four arguments are positive odd integers. -/
theorem two_edge_repair_identity (t : ℚ) :
    (23 * t) * ((483 * t + 7) / 2) * (3 * (35 * t) + 1) *
      (3 * ((105 * t + 1) / 2) + 1) =
    (35 * t) * ((105 * t + 1) / 2) * (3 * (23 * t) + 1) *
      (3 * ((483 * t + 7) / 2) + 1) := by ring

/-- Exact factor equation behind the complete two-odd-factor fiber of 7/16. -/
theorem two_odd_fiber_identity (c d : ℚ) :
    64 * c * d = 7 * (3 * c + 1) * (3 * d + 1) ↔
      (c - 21) * (d - 21) = 448 := by
  constructor <;> intro h <;> nlinarith

/-- A repair into a genuine path cannot always preserve or decrease the total
number of factors.  This quantifies over all valid semigroup certificates. -/
theorem length_nonincreasing_repair_false :
    ¬ (∀ (twos : ℕ) (sources : List ℕ) (n : ℕ), 0 < n → validSources sources →
      certificateValue twos sources = (n : ℚ) →
      ∃ k, k ≤ twos + sources.length ∧ (tstep^[k]) n = 1) := by
  intro h
  obtain ⟨k, hk, heq⟩ := h 16 certificate71 71 (by decide)
    certificate71_valid certificate71_value
  rw [certificate71_length] at hk
  exact seventy_one_no_short_path k (Finset.mem_range.mpr (by omega)) heq

def Integral (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

/-- Once the set includes a halving edge, integrality of every pairwise gap
is precisely integrality of the states themselves. -/
theorem pair_integrality_iff (S : Set ℚ) (x : ℚ)
    (hx : x ∈ S) (hhalf : x / 2 ∈ S) :
    (∀ u ∈ S, ∀ v ∈ S, Integral (u - v)) ↔
      (∀ u ∈ S, Integral u) := by
  constructor
  · intro h u hu
    obtain ⟨z, hz⟩ := h x hx (x / 2) hhalf
    obtain ⟨d, hd⟩ := h u hu x hx
    refine ⟨d + 2 * z, ?_⟩
    push_cast
    linarith
  · intro h u hu v hv
    obtain ⟨a, ha⟩ := h u hu
    obtain ⟨b, hb⟩ := h v hv
    exact ⟨a - b, by push_cast; rw [ha, hb]⟩

/-- An integral Vandermonde product is weaker than integral pairwise gaps,
even with positive widely separated points and an actual halving edge.
This is a set control, not a claimed Collatz cycle. -/
theorem vandermonde_control (t : ℤ) :
    ((126 : ℚ) / 5 - 63 / 5) *
      (((126 : ℚ) + 125 * t) / 5 - 126 / 5) *
      (((126 : ℚ) + 125 * t) / 5 - 63 / 5) =
      ((63 * t * (63 + 125 * t) : ℤ) : ℚ) := by
  push_cast
  ring

/-- Arithmetic estimate used in the positive approximate-fixed-vector family. -/
theorem endpoint_ratio_lt {a b : ℚ} (ha : 1 < a) (hab : a < b) :
    (a - 1) / (b - 1) < a / b := by
  have hb : 0 < b := by linarith
  have hbm : 0 < b - 1 := by linarith
  apply (div_lt_div_iff₀ hbm hb).2
  nlinarith

theorem geometric_endpoint_ratio (k : ℕ) (hk : 0 < k) :
    ((2 : ℚ) ^ k - 1) / ((3 : ℚ) ^ k - 1) < (2 / 3 : ℚ) ^ k := by
  have h2 : (1 : ℚ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have h23 : (2 : ℚ) ^ k < 3 ^ k :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  simpa only [div_pow] using endpoint_ratio_lt h2 h23

/-- Exact dyadic ray.  The finite exponent bound loses no term for positive n:
if n=2^j*base with base>0, then j<=n. -/
def rayCoeff (base n : ℕ) : ℚ :=
  if (List.range (n + 1)).any (fun j => n == 2 ^ j * base) then 1 else 0

def approxCoeff (K n : ℕ) : ℚ :=
  rayCoeff (2 ^ K - 1) n +
    ∑ j ∈ Finset.Ico 1 K, if n = 3 ^ j * 2 ^ (K - j) - 1 then 1 else 0

def transfer (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  a (2 * n) + if n % 3 = 2 then a ((2 * n - 1) / 3) else 0

/-- The general coefficient statement, proved by positiveApproximationFamily
in PositiveApproximation.lean.  Kept separate from its proof module. -/
def PositiveApproximationFamily : Prop :=
  ∀ K, 2 ≤ K →
    (∀ n, approxCoeff K n = 0 ∨ approxCoeff K n = 1) ∧
    approxCoeff K (2 ^ K - 1) = 1 ∧
    (∀ n, n < 2 ^ K - 1 → approxCoeff K n = 0) ∧
    (∀ n, 0 < n → transfer (approxCoeff K) n - approxCoeff K n =
      if n = 3 ^ K - 1 then 1 else 0)

theorem approximation_anchor :
    approxCoeff 2 3 = 1 ∧ approxCoeff 2 5 = 1 ∧ approxCoeff 2 8 = 0 ∧
    transfer (approxCoeff 2) 8 - approxCoeff 2 8 = 1 := by native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
