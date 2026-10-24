/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.FourierLattice

/-!
# A non-oscillatory bound for the fixed-frequency coefficients (the mirror of Tao 2019, §7)

The lattice values `V_n(m) = latticeCoeff ξ n m` satisfy, two levels at a time,
`V_{n+2}(m) = ¼V_n(m) + ¼(φ(n,m) + φ(n+1,m)) V_n(m+1) + ¼φ(n+1,m)φ(n,m+1) V_n(m+2)`,
and the middle phases are two truncations of the same `2`-adic number:
`⟨x⟩_{n+2} = 2⟨x⟩_{n+3} (mod 1)` with `x = ξ·3^{−(m+1)}`.  So `|φ(n,m) + φ(n+1,m)| =
2|cos π⟨x⟩_{n+3}|`, and the triangle inequality, applied once per pair of levels rather than per
level, keeps the cancellation inside each pair.  This is the mirror of Tao's pairing (2019,
arXiv 1909.03562, eq. 7.5 and Lemma 7.2, with the primes swapped): `|G_{2i}(ξ)| ≤ U_i(0)`, where
`U` is a **positive** lattice walk weighted by `|cos πΘ|` (`pairBound`).

* **Evidence** (`experiments/conjugacy/pairbound.py`): `U ≥ |G|` at every even `n ≤ 200` for
  seven frequencies, minimum slack `1.1e-9` (the bound is nearly attained, so the check has
  teeth); and `log₂ U_n / n ≈ −0.146` at `ξ = 1, 5, 27` and a random `2`-adic unit, stable from
  `n = 400` to `1600`.  At the resonant `ξ = 3^{n/2}`, `U_n = 0.38, 0.23, 0.13` at
  `n = 64, 256, 1024`: slow, as it must be.
* **The protection lemma** (`pairTheta_far`), the mirror of Tao's (7.16): if `3^t ∤ ξ` and
  `ξ < 2^k`, then `Θ(k,t) = ⟨ξ·3^{−t}⟩_k` stays at distance `≥ (1 − ξ/2^k)/3^t` from the
  integers.  So for a fixed integer frequency, the walk starts in a strip of small `t` where no
  factor is close to `1`; the strip disappears exactly when high powers of `3` divide `ξ`,
  which is the resonance.  Checked exhaustively (`protect.py`), equality attained.

So `LowFreqDecay`, an exponential-sum statement, follows from `PairBoundDecay`, a statement about
a positive random walk in the `|cos πΘ|` environment: the analogue of Tao's Prop 7.3, which is
where a proof should now go.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology

/-- `Θ(k, t) = ⟨ξ·3^{−t}⟩_k = (ξ·3^{−t} mod 2^k) / 2^k`. -/
noncomputable def pairTheta (ξ k t : ℕ) : ℝ :=
  ((((3 : ZMod (2 ^ k))⁻¹ ^ t * ξ).val : ℕ) : ℝ) / 2 ^ k

/-- The pair factor `|cos π Θ(k, t)|`. -/
noncomputable def pairCos (ξ k t : ℕ) : ℝ := |Real.cos (Real.pi * pairTheta ξ k t)|

/-- The positive pairing walk: `pairBound ξ i m` bounds `‖latticeCoeff ξ (2i) m‖`
(`norm_latticeCoeff_le_pairBound`).  Pair `i` covers levels `2i+1, 2i` and contributes the factor
`pairCos ξ (2i+3) (m+1)` when it holds exactly one step of the walk. -/
noncomputable def pairBound (ξ : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | i + 1, m => (1 / 4 : ℝ) * pairBound ξ i m +
      (1 / 2 : ℝ) * pairCos ξ (2 * i + 3) (m + 1) * pairBound ξ i (m + 1) +
      (1 / 4 : ℝ) * pairBound ξ i (m + 2)

/-- **The pairing bound.**  Proof sketch: induction on `i`, generalising `m`.  Unroll
`latticeCoeff` two levels (`n = 2i`); the middle coefficient is `¼(latticePhase ξ (2i) m +
latticePhase ξ (2i+1) m)`, of norm `½ pairCos ξ (2i+3) (m+1)` because the two exponents are
`−⟨x⟩_{2i+2}` and `−⟨x⟩_{2i+3}` with `⟨x⟩_{2i+2} ≡ 2⟨x⟩_{2i+3} (mod 1)` and
`|1 + e(−a)| = 2|cos πa|`; the outer coefficients have norm `¼`.  Triangle inequality and the
induction hypothesis.  Confidence 95% (numerics in the module docstring). -/
theorem norm_latticeCoeff_le_pairBound (ξ i m : ℕ) :
    ‖latticeCoeff ξ (2 * i) m‖ ≤ pairBound ξ i m := by
  sorry

/-- **Node: the positive walk decays.**  For each odd `ξ` and each fixed offset `m`, the pairing
walk tends to `0`.  Non-oscillatory: a statement about how often a random walk in the space-time
environment `|cos πΘ(k, t)|` meets factors bounded away from `1`, the analogue of Tao's Prop 7.3.
Evidence: `log₂ U_n / n ≈ −0.146` for four frequencies to `n = 1600` (`pairbound.py`); the start
of the walk is protected by `pairTheta_far`.  Confidence 85%. -/
def PairBoundDecay : Prop :=
  ∀ ξ : ℕ, Odd ξ → ∀ m : ℕ, Tendsto (fun i => pairBound ξ i m) atTop (𝓝 0)

/-- **Edge: the positive walk controls the fixed frequencies.**  Even `j = 2i`:
`fourierCoeff_eq_latticeCoeff_zero` and `norm_latticeCoeff_le_pairBound` at `m = 0`.  Odd
`j = 2i + 1`: one level of `latticeCoeff` gives `‖G_{2i+1}(ξ)‖ ≤ ½ U_i(0) + ½ U_i(1)`.  Squeeze.
Confidence 98%. -/
theorem lowFreqDecay_of_pairBoundDecay (h : PairBoundDecay) : LowFreqDecay := by
  sorry

/-- **The protection lemma** (mirror of Tao 2019, eq. 7.16).  If `3^t ∤ ξ` and `ξ < 2^k`, then
`Θ(k, t)` is at distance at least `(1 − ξ/2^k)/3^t` from every integer.  Proof: with `q = 3^t`
and `X = ξ q⁻¹ mod 2^k`, `qX = ξ + 2^k M` for an integer `M`, so `Θ = M/q + ξ/(q 2^k)`;
`M ≡ −ξ 2^{−k} (mod q)` is nonzero mod `q` because `q ∤ ξ`, so `M/q` is at distance `≥ 1/q` from
the integers, and the second term lies in `[0, 1/q)`.  Checked exhaustively (`protect.py`),
equality attained.  Confidence 99%. -/
theorem pairTheta_far (ξ k t : ℕ) (h3 : ¬ 3 ^ t ∣ ξ) (hk : ξ < 2 ^ k) (z : ℤ) :
    (1 - (ξ : ℝ) / 2 ^ k) / 3 ^ t ≤ |pairTheta ξ k t - z| := by
  let q : ℕ := 3 ^ t
  let N : ℕ := 2 ^ k
  let a : ZMod N := (3 : ZMod N)⁻¹
  let X : ℕ := (a ^ t * ξ).val
  have hqpos : 0 < q := by simp [q]
  have hNpos : 0 < N := by simp [N]
  have hcop : Nat.Coprime 3 N := by
    dsimp only [N]
    exact Nat.Coprime.pow_right k (by decide)
  have hunit : IsUnit (3 : ZMod N) := (ZMod.isUnit_iff_coprime 3 N).2 hcop
  have h3a : (3 : ZMod N) * a = 1 := by
    simpa only [a] using ZMod.mul_inv_of_unit (3 : ZMod N) hunit
  have hX : (X : ZMod N) = a ^ t * ξ := by
    exact ZMod.natCast_zmod_val _
  have hcast : ((q * X : ℕ) : ZMod N) = (ξ : ZMod N) := by
    push_cast
    rw [hX]
    dsimp only [q]
    rw [Nat.cast_pow]
    change (3 : ZMod N) ^ t * (a ^ t * ξ) = ξ
    calc
      (3 : ZMod N) ^ t * (a ^ t * ξ) = ((3 : ZMod N) ^ t * a ^ t) * ξ := by ring
      _ = ξ := by rw [← mul_pow, h3a, one_pow, one_mul]
  have hzero : ((((q * X : ℕ) : ℤ) - (ξ : ℤ) : ℤ) : ZMod N) = 0 := by
    push_cast
    exact sub_eq_zero.mpr (by simpa only [Nat.cast_mul] using hcast)
  have hdiv : (N : ℤ) ∣ (q * X : ℕ) - (ξ : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  let M : ℤ := ((q * X : ℕ) - (ξ : ℤ)) / N
  have hM : (q * X : ℕ) - (ξ : ℤ) = M * N := by
    exact (Int.ediv_mul_cancel hdiv).symm
  have hEq : ((q : ℤ) * X : ℤ) = ξ + N * M := by
    norm_num only [Nat.cast_mul] at hM
    calc
      (q : ℤ) * X = ξ + M * N := by omega
      _ = ξ + N * M := by ring
  have hqM : ¬(q : ℤ) ∣ M := by
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    apply h3
    rw [← Int.ofNat_dvd]
    refine ⟨(X : ℤ) - N * c, ?_⟩
    rw [hc] at hEq
    nlinarith
  let A : ℤ := M - q * z
  have hA : A ≠ 0 := by
    intro hAzero
    apply hqM
    refine ⟨z, ?_⟩
    dsimp only [A] at hAzero
    omega
  have hAabs : (1 : ℝ) ≤ |(A : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hA
  have hquot : (1 : ℝ) / q ≤ |(A : ℝ) / q| := by
    rw [abs_div, abs_of_pos (by exact_mod_cast hqpos : (0 : ℝ) < q)]
    exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < q) (by positivity : (0 : ℝ) < q)).2
      (by nlinarith)
  have hdelta : 0 ≤ (ξ : ℝ) / ((q : ℝ) * N) := by positivity
  have hEqR : (q : ℝ) * X = ξ + N * M := by exact_mod_cast hEq
  have hdecomp :
      (X : ℝ) / N - z = (A : ℝ) / q + (ξ : ℝ) / ((q : ℝ) * N) := by
    dsimp only [A]
    push_cast
    field_simp [show (q : ℝ) ≠ 0 by positivity, show (N : ℝ) ≠ 0 by positivity]
    nlinarith
  have hresult : (1 - (ξ : ℝ) / N) / q ≤ |(X : ℝ) / N - z| := by
    rw [hdecomp]
    calc
      (1 - (ξ : ℝ) / N) / q =
          1 / q - (ξ : ℝ) / ((q : ℝ) * N) := by field_simp
      _ ≤ |(A : ℝ) / q| - |(ξ : ℝ) / ((q : ℝ) * N)| := by
        rw [abs_of_nonneg hdelta]
        linarith
      _ ≤ |(A : ℝ) / q + (ξ : ℝ) / ((q : ℝ) * N)| :=
        abs_sub_abs_le_abs_add _ _
  simpa only [pairTheta, q, N, a, X, Nat.cast_pow, Nat.cast_ofNat] using hresult

end CollatzMoonshot.Conjugacy
