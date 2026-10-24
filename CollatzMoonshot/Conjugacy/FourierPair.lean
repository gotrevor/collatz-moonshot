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

/-- Reduction by one power of two preserves the inverse of three. -/
theorem pair_cast_inv_three (n : ℕ) :
    (ZMod.castHom (pow_dvd_pow 2 (by omega : n + 1 ≤ n + 2))
      (ZMod (2 ^ (n + 1)))) ((3 : ZMod (2 ^ (n + 2)))⁻¹) =
        (3 : ZMod (2 ^ (n + 1)))⁻¹ := by
  let f := ZMod.castHom (pow_dvd_pow 2 (by omega : n + 1 ≤ n + 2))
    (ZMod (2 ^ (n + 1)))
  have hcop : Nat.Coprime 3 (2 ^ (n + 2)) :=
    Nat.Coprime.pow_right (n + 2) (by decide)
  have hunit : IsUnit (3 : ZMod (2 ^ (n + 2))) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ (n + 2))).2 hcop
  have hinv := ZMod.mul_inv_of_unit (3 : ZMod (2 ^ (n + 2))) hunit
  have hmap := congrArg f hinv
  have hmul : (3 : ZMod (2 ^ (n + 1))) *
      f ((3 : ZMod (2 ^ (n + 2)))⁻¹) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using hmap
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ hmul).symm

/-- Complex exponentials with congruent integer numerators agree. -/
theorem pair_exp_int_congr (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (h : a ≡ b [ZMOD (N : ℤ)]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / N) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / N) := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨c, hc⟩ := h
  have hb : b = a + N * c := by omega
  rw [hb]
  rw [show
      2 * Real.pi * Complex.I * ((a + (N : ℤ) * c : ℤ) : ℂ) / (N : ℂ) =
        2 * Real.pi * Complex.I * (a : ℂ) / N +
          (c : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]]
  rw [Complex.exp_add, Complex.exp_periodic.int_mul_eq]
  simp

/-- The phase at the lower level is the square of the phase at the upper level. -/
theorem latticePhase_even_eq_sq (ξ i m : ℕ) :
    latticePhase ξ (2 * i) m = latticePhase ξ (2 * i + 1) m ^ 2 := by
  let n : ℕ := 2 * i
  let N : ℕ := 2 ^ (n + 2)
  let H : ℕ := 2 ^ (n + 3)
  let lo : ZMod N := (3 : ZMod N)⁻¹ ^ (m + 1) * ξ
  let hi : ZMod H := (3 : ZMod H)⁻¹ ^ (m + 1) * ξ
  let X : ℕ := hi.val
  let Y : ℕ := lo.val
  have hN : 0 < N := by simp [N]
  have hH : 0 < H := by simp [H]
  have hNdivH : N ∣ H := pow_dvd_pow 2 (by omega)
  let c := ZMod.castHom hNdivH (ZMod N)
  have hcinv : c ((3 : ZMod H)⁻¹) = (3 : ZMod N)⁻¹ := by
    simpa only [c, H, N, n] using pair_cast_inv_three (n + 1)
  have hchi : c hi = lo := by
    simp only [hi, lo, map_mul, map_pow, map_natCast, hcinv]
  have hXH : (X : ZMod H) = hi := ZMod.natCast_zmod_val _
  have hYN : (Y : ZMod N) = lo := ZMod.natCast_zmod_val _
  have hXN : (X : ZMod N) = lo := by
    calc
      (X : ZMod N) = c (X : ZMod H) := by simp [c]
      _ = c hi := by rw [hXH]
      _ = lo := hchi
  have hXY : (((X : ℕ) : ℤ) : ZMod N) = (((Y : ℕ) : ℤ) : ZMod N) := by
    norm_cast
    exact hXN.trans hYN.symm
  have hmod : (X : ℤ) ≡ (Y : ℤ) [ZMOD (N : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ N).1 hXY
  have hHN : (H : ℤ) = 2 * N := by
    norm_cast
    dsimp only [H, N]
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    omega
  have hscaled : -(2 * (Y : ℤ)) ≡ -(2 * (X : ℤ)) [ZMOD (H : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hmod ⊢
    obtain ⟨d, hd⟩ := hmod
    refine ⟨d, ?_⟩
    rw [hHN]
    nlinarith
  have hexp := pair_exp_int_congr H hH (-(2 * (Y : ℤ))) (-(2 * (X : ℤ))) hscaled
  unfold latticePhase
  rw [show 2 * i + 1 + 2 = n + 3 by omega, show 2 * i + 2 = n + 2 by omega]
  have hlo : (((3 : ZMod (2 ^ (n + 2)))⁻¹ ^ (m + 1) * ξ).val) = Y := by rfl
  have hhi : (((3 : ZMod (2 ^ (n + 3)))⁻¹ ^ (m + 1) * ξ).val) = X := by rfl
  rw [hlo, hhi]
  rw [← Complex.exp_nat_mul]
  convert hexp using 1 <;> dsimp only [N, H] <;> push_cast <;>
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN),
      show (H : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hH)] <;> ring

/-- The elementary half-angle identity in the form used by the paired phases. -/
theorem norm_exp_neg_two_pi_add_one (x : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ))) + 1‖ =
      2 * |Real.cos (Real.pi * x)| := by
  let r : ℝ := Real.pi * x
  have harg : -(2 * Real.pi * Complex.I * (x : ℂ)) = -(2 * (r : ℂ) * Complex.I) := by
    dsimp only [r]
    push_cast
    ring
  rw [harg]
  have hfac :
      Complex.exp (-(2 * (r : ℂ) * Complex.I)) + 1 =
        Complex.exp (-(r : ℂ) * Complex.I) *
          (Complex.exp (-(r : ℂ) * Complex.I) + Complex.exp ((r : ℂ) * Complex.I)) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · ring
    · ring_nf
      simp
  rw [hfac, norm_mul]
  have hnorm : ‖Complex.exp (-(r : ℂ) * Complex.I)‖ = 1 := by
    rw [show -(r : ℂ) * Complex.I = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hnorm, one_mul]
  have hsum :
      Complex.exp (-(r : ℂ) * Complex.I) + Complex.exp ((r : ℂ) * Complex.I) =
        ((2 * Real.cos r : ℝ) : ℂ) := by
    rw [show -(r : ℂ) * Complex.I = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num
  rfl

/-- Exact norm of the middle coefficient in one two-level lattice step. -/
theorem norm_latticePhase_pair (ξ i m : ℕ) :
    ‖latticePhase ξ (2 * i) m + latticePhase ξ (2 * i + 1) m‖ =
      2 * pairCos ξ (2 * i + 3) (m + 1) := by
  rw [latticePhase_even_eq_sq]
  let E := latticePhase ξ (2 * i + 1) m
  rw [show E ^ 2 + E = E * (E + 1) by ring, norm_mul]
  let theta : ℝ :=
    ((((3 : ZMod (2 ^ (2 * i + 3)))⁻¹ ^ (m + 1) * ξ).val : ℕ) : ℝ) /
      2 ^ (2 * i + 3)
  have hE : E = Complex.exp (-(2 * Real.pi * Complex.I * (theta : ℂ))) := by
    dsimp only [E, latticePhase, theta]
    rw [show 2 * i + 1 + 2 = 2 * i + 3 by omega]
    congr 1
    push_cast
    ring
  have hEnorm : ‖E‖ = 1 := by
    rw [hE]
    rw [show -(2 * Real.pi * Complex.I * (theta : ℂ)) =
        ((-(2 * Real.pi * theta) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hEnorm, one_mul]
  rw [hE, norm_exp_neg_two_pi_add_one]
  congr 2

/-- Every lattice phase lies on the complex unit circle. -/
theorem norm_latticePhase (ξ n m : ℕ) : ‖latticePhase ξ n m‖ = 1 := by
  let theta : ℝ :=
    ((((3 : ZMod (2 ^ (n + 2)))⁻¹ ^ (m + 1) * ξ).val : ℕ) : ℝ) / 2 ^ (n + 2)
  have hphase : latticePhase ξ n m =
      Complex.exp (-(2 * Real.pi * Complex.I * (theta : ℂ))) := by
    dsimp only [latticePhase, theta]
    congr 1
    push_cast
    ring
  rw [hphase]
  rw [show -(2 * Real.pi * Complex.I * (theta : ℂ)) =
      ((-(2 * Real.pi * theta) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The pairing bound.**  Proof sketch: induction on `i`, generalising `m`.  Unroll
`latticeCoeff` two levels (`n = 2i`); the middle coefficient is `¼(latticePhase ξ (2i) m +
latticePhase ξ (2i+1) m)`, of norm `½ pairCos ξ (2i+3) (m+1)` because the two exponents are
`−⟨x⟩_{2i+2}` and `−⟨x⟩_{2i+3}` with `⟨x⟩_{2i+2} ≡ 2⟨x⟩_{2i+3} (mod 1)` and
`|1 + e(−a)| = 2|cos πa|`; the outer coefficients have norm `¼`.  Triangle inequality and the
induction hypothesis.  Confidence 95% (numerics in the module docstring). -/
theorem norm_latticeCoeff_le_pairBound (ξ i m : ℕ) :
    ‖latticeCoeff ξ (2 * i) m‖ ≤ pairBound ξ i m := by
  induction i generalizing m with
  | zero =>
      norm_num [latticeCoeff, pairBound]
  | succ i ih =>
      let A : ℂ := (1 / 4 : ℂ) * latticeCoeff ξ (2 * i) m
      let B : ℂ := (1 / 4 : ℂ) *
        (latticePhase ξ (2 * i) m + latticePhase ξ (2 * i + 1) m) *
          latticeCoeff ξ (2 * i) (m + 1)
      let C : ℂ := (1 / 4 : ℂ) * latticePhase ξ (2 * i + 1) m *
        latticePhase ξ (2 * i) (m + 1) * latticeCoeff ξ (2 * i) (m + 2)
      have hexpand : latticeCoeff ξ (2 * (i + 1)) m = A + B + C := by
        rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega]
        simp only [latticeCoeff]
        dsimp only [A, B, C]
        ring
      rw [hexpand]
      calc
        ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
        _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by
          gcongr
          exact norm_add_le _ _
        _ = (1 / 4 : ℝ) * ‖latticeCoeff ξ (2 * i) m‖ +
            (1 / 2 : ℝ) * pairCos ξ (2 * i + 3) (m + 1) *
              ‖latticeCoeff ξ (2 * i) (m + 1)‖ +
            (1 / 4 : ℝ) * ‖latticeCoeff ξ (2 * i) (m + 2)‖ := by
          have hquarter : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num [norm_div]
          dsimp only [A, B, C]
          simp only [norm_mul, norm_latticePhase, one_mul]
          rw [hquarter, norm_latticePhase_pair]
          ring
        _ ≤ (1 / 4 : ℝ) * pairBound ξ i m +
            (1 / 2 : ℝ) * pairCos ξ (2 * i + 3) (m + 1) * pairBound ξ i (m + 1) +
            (1 / 4 : ℝ) * pairBound ξ i (m + 2) := by
          have hcos : 0 ≤ pairCos ξ (2 * i + 3) (m + 1) := abs_nonneg _
          gcongr
          · exact ih m
          · exact ih (m + 1)
          · exact ih (m + 2)
        _ = pairBound ξ (i + 1) m := by rfl

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
