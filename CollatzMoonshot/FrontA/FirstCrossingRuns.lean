import CollatzMoonshot.FrontA.FirstCrossingTwoRun
import CollatzMoonshot.FrontA.FixedBlocks

/-! # First crossing: the run-product bound

Let `n` be odd with first crossing at length `m`, `K` odd steps and `r` maximal odd runs, and
suppose `n` survives, `n ≤ y := tstep^[m] n`.  Telescoping the head identity of every run
(`2^(q+e)·x' + 2^q = 3^q·(x+1)`) and using that every run start is at least `n` gives

    2^m · n^(r−1) · y ≤ 3^K · (n+1)^r.

Two consequences: `y · n^(r−1) < (n+1)^r`, so the overshoot `y − n` is at most about `r`, the
number of odd runs (sharper than `a/3` when runs are few); and
`(2^m − 3^K) · n^r ≤ 3^K · ((n+1)^r − n^r)`, the integer form of Simons–de Weger's Lemma 4
(`Λ < Σ 1/xᵢ`) for first-crossing near-cycles.  No open hypothesis is used. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- `Π (xᵢ + 1)` over the run starts of a block list, from `n`. -/
def runProd : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 1
  | (q, e) :: L, n => (n + 1) * runProd L (tstep^[q + e] n)

/-- `Π xᵢ` over the run starts. -/
def runProdStart : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 1
  | (q, e) :: L, n => n * runProdStart L (tstep^[q + e] n)

/-- `Π xᵢ₊₁`: the run starts shifted by one, ending at the endpoint. -/
def runProdNext : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 1
  | (q, e) :: L, n => tstep^[q + e] n * runProdNext L (tstep^[q + e] n)

theorem blockWord_cons_length (q e : ℕ) (L : List (ℕ × ℕ)) :
    (blockWord ((q, e) :: L)).length = q + e + (blockWord L).length := by
  simp only [blockWord, List.length_append, List.length_replicate]

theorem runProdNext_pos : ∀ (L : List (ℕ × ℕ)) (n : ℕ), 1 ≤ n → 1 ≤ runProdNext L n
  | [], _, _ => by simp [runProdNext]
  | (q, e) :: L, n, hn => by
    simp only [runProdNext]
    have h1 := tstep_iterate_pos hn (q + e)
    have h2 := runProdNext_pos L (tstep^[q + e] n) h1
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- **Lemma A: the telescoped head identities.**  `2^m · Π xᵢ₊₁ ≤ 3^K · Π (xᵢ + 1)`. -/
theorem runProd_identity_bound : ∀ (L : List (ℕ × ℕ)) (n : ℕ),
    traceWord n (blockWord L).length = blockWord L →
    2 ^ (blockWord L).length * runProdNext L n ≤ 3 ^ ones (blockWord L) * runProd L n
  | [], n, _ => by simp [runProdNext, runProd, blockWord]
  | (q, e) :: L, n, hword => by
    have hlen := blockWord_cons_length q e L
    have hsplit : traceWord n (q + e) ++ traceWord (tstep^[q + e] n) (blockWord L).length =
        (List.replicate q true ++ List.replicate e false) ++ blockWord L := by
      rw [← traceWord_add, ← hlen, hword]; rfl
    obtain ⟨hhead, htail⟩ := List.append_inj hsplit (by simp)
    have hid := segment_identity_of_word hhead
    have ih := runProd_identity_bound L (tstep^[q + e] n) htail
    have hones : ones (blockWord ((q, e) :: L)) = q + ones (blockWord L) := by
      simp only [blockWord, ones_append]; simp
    have h1 : 2 ^ (q + e) * tstep^[q + e] n ≤ 3 ^ q * (n + 1) := by
      rw [← hid]; exact Nat.le_add_right _ _
    rw [hlen, hones, pow_add 2 (q + e), pow_add 3 q]
    simp only [runProdNext, runProd]
    calc 2 ^ (q + e) * 2 ^ (blockWord L).length *
          (tstep^[q + e] n * runProdNext L (tstep^[q + e] n))
        = (2 ^ (q + e) * tstep^[q + e] n) *
          (2 ^ (blockWord L).length * runProdNext L (tstep^[q + e] n)) := by ring
      _ ≤ (3 ^ q * (n + 1)) * (3 ^ ones (blockWord L) * runProd L (tstep^[q + e] n)) :=
          Nat.mul_le_mul h1 ih
      _ = 3 ^ q * 3 ^ ones (blockWord L) * ((n + 1) * runProd L (tstep^[q + e] n)) := by ring

/-- **Lemma B: the floor bound.**  If every run start is at least `n₀`, then
`Π (xᵢ + 1) · n₀^r ≤ (n₀ + 1)^r · Π xᵢ`. -/
theorem runProd_floor_bound (n₀ : ℕ) : ∀ (L : List (ℕ × ℕ)) (n : ℕ),
    (∀ p ∈ L, 0 < p.1) →
    (∀ j < (blockWord L).length, n₀ ≤ tstep^[j] n) →
    runProd L n * n₀ ^ L.length ≤ (n₀ + 1) ^ L.length * runProdStart L n
  | [], n, _, _ => by simp [runProd, runProdStart]
  | (q, e) :: L, n, hpos, hlow => by
    have hq : 0 < q := hpos (q, e) (by simp)
    have hlen := blockWord_cons_length q e L
    have hn0 : n₀ ≤ n := by simpa using hlow 0 (by rw [hlen]; omega)
    have hlow' : ∀ j < (blockWord L).length, n₀ ≤ tstep^[j] (tstep^[q + e] n) := by
      intro j hj
      rw [← Function.iterate_add_apply]
      exact hlow (j + (q + e)) (by rw [hlen]; omega)
    have ih := runProd_floor_bound n₀ L (tstep^[q + e] n)
      (fun p hp => hpos p (by simp [hp])) hlow'
    simp only [runProd, runProdStart, List.length_cons, pow_succ]
    have h1 : (n + 1) * n₀ ≤ (n₀ + 1) * n := by nlinarith
    calc (n + 1) * runProd L (tstep^[q + e] n) * (n₀ ^ L.length * n₀)
        = ((n + 1) * n₀) * (runProd L (tstep^[q + e] n) * n₀ ^ L.length) := by ring
      _ ≤ ((n₀ + 1) * n) * ((n₀ + 1) ^ L.length * runProdStart L (tstep^[q + e] n)) :=
          Nat.mul_le_mul h1 ih
      _ = (n₀ + 1) ^ L.length * (n₀ + 1) * (n * runProdStart L (tstep^[q + e] n)) := by ring

/-- **Lemma C: the shifted product.**  `Π xᵢ · y = n · Π xᵢ₊₁`. -/
theorem runProdStart_mul_endpoint : ∀ (L : List (ℕ × ℕ)) (n : ℕ),
    runProdStart L n * tstep^[(blockWord L).length] n = n * runProdNext L n
  | [], n => by simp [runProdStart, runProdNext, blockWord]
  | (q, e) :: L, n => by
    have ih := runProdStart_mul_endpoint L (tstep^[q + e] n)
    rw [blockWord_cons_length, add_comm (q + e), Function.iterate_add_apply]
    simp only [runProdStart, runProdNext]
    calc n * runProdStart L (tstep^[q + e] n) * tstep^[(blockWord L).length] (tstep^[q + e] n)
        = n * (runProdStart L (tstep^[q + e] n) *
            tstep^[(blockWord L).length] (tstep^[q + e] n)) := by ring
      _ = n * (tstep^[q + e] n * runProdNext L (tstep^[q + e] n)) := by rw [ih]
      _ = _ := by ring

/-- **The run-product bound.**  For an odd survivor of its first crossing with `r` odd runs,
`2^m · n^(r−1) · y ≤ 3^K · (n+1)^r`. -/
theorem run_product_bound {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n) :
    2 ^ m * n ^ (oddRunCount (traceWord n m) - 1) * tstep^[m] n ≤
      3 ^ ones (traceWord n m) * (n + 1) ^ oddRunCount (traceWord n m) := by
  have hhead : (traceWord n m).head? = some true := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
    simp [traceWord, hn]
  obtain ⟨L, hpos, hword, hcount⟩ := exists_blockWord_oddRunCount _ hhead
  have hlen : m = (blockWord L).length := by
    have := congrArg List.length hword; simpa using this
  subst hlen
  rw [hword] at hcount
  rw [hword, ← hcount]
  have hA := runProd_identity_bound L n hword
  have hB := runProd_floor_bound n L n hpos
    (fun j hj => iterate_ge_of_prefix_supercritical (h.2.1 j hj))
  have hC := runProdStart_mul_endpoint L n
  have hn1 : 1 ≤ n := by omega
  have hN := runProdNext_pos L n hn1
  obtain ⟨r', hr⟩ : ∃ r', L.length = r' + 1 := by
    rcases L with _ | ⟨p, L⟩
    · exfalso; have := h.1; simp [blockWord] at this
    · exact ⟨L.length, by simp⟩
  rw [hr] at hB ⊢
  simp only [Nat.add_sub_cancel]
  set y := tstep^[(blockWord L).length] n with hy
  set N := runProdNext L n
  set P := runProd L n
  set S := runProdStart L n
  set K := ones (blockWord L)
  set M := (blockWord L).length
  have key : (2 ^ M * n ^ r' * y) * (n * N) ≤ (3 ^ K * (n + 1) ^ (r' + 1)) * (n * N) := by
    calc (2 ^ M * n ^ r' * y) * (n * N) = (2 ^ M * N) * (n ^ (r' + 1) * y) := by ring
      _ ≤ (3 ^ K * P) * (n ^ (r' + 1) * y) := Nat.mul_le_mul_right _ hA
      _ = 3 ^ K * ((P * n ^ (r' + 1)) * y) := by ring
      _ ≤ 3 ^ K * (((n + 1) ^ (r' + 1) * S) * y) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB)
      _ = (3 ^ K * (n + 1) ^ (r' + 1)) * (S * y) := by ring
      _ = (3 ^ K * (n + 1) ^ (r' + 1)) * (n * N) := by rw [hC]
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **The overshoot is at most about the run count**: `y · n^(r−1) < (n+1)^r`. -/
theorem endpoint_mul_pow_lt {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n) :
    tstep^[m] n * n ^ (oddRunCount (traceWord n m) - 1) <
      (n + 1) ^ oddRunCount (traceWord n m) := by
  have hb := run_product_bound hn h hsurv
  have hsub := h.2.2
  have hpos : 0 < (n + 1) ^ oddRunCount (traceWord n m) := by positivity
  have h2 : 2 ^ m * (tstep^[m] n * n ^ (oddRunCount (traceWord n m) - 1)) <
      2 ^ m * (n + 1) ^ oddRunCount (traceWord n m) := by
    calc 2 ^ m * (tstep^[m] n * n ^ (oddRunCount (traceWord n m) - 1))
        = 2 ^ m * n ^ (oddRunCount (traceWord n m) - 1) * tstep^[m] n := by ring
      _ ≤ 3 ^ ones (traceWord n m) * (n + 1) ^ oddRunCount (traceWord n m) := hb
      _ < 2 ^ m * (n + 1) ^ oddRunCount (traceWord n m) :=
          Nat.mul_lt_mul_of_pos_right hsub hpos
  exact Nat.lt_of_mul_lt_mul_left h2

/-- **Integer Simons–de Weger Lemma 4**: `(2^m − 3^K) · n^r ≤ 3^K · ((n+1)^r − n^r)`. -/
theorem gap_mul_pow_le {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n ^ oddRunCount (traceWord n m) ≤
      3 ^ ones (traceWord n m) *
        ((n + 1) ^ oddRunCount (traceWord n m) - n ^ oddRunCount (traceWord n m)) := by
  have hb := run_product_bound hn h hsurv
  obtain ⟨r', hr⟩ : ∃ r', oddRunCount (traceWord n m) = r' + 1 := by
    have hhead : (traceWord n m).head? = some true := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
      simp [traceWord, hn]
    obtain ⟨L, _, hword, hcount⟩ := exists_blockWord_oddRunCount _ hhead
    rcases L with _ | ⟨p, L⟩
    · exfalso; have := h.1; have hl := congrArg List.length hword; simp [blockWord] at hl; omega
    · exact ⟨L.length, by rw [← hcount]; simp⟩
  rw [hr] at hb ⊢
  simp only [Nat.add_sub_cancel] at hb
  have h1 : 2 ^ m * n ^ (r' + 1) ≤ 3 ^ ones (traceWord n m) * (n + 1) ^ (r' + 1) := by
    calc 2 ^ m * n ^ (r' + 1) = 2 ^ m * n ^ r' * n := by ring
      _ ≤ 2 ^ m * n ^ r' * tstep^[m] n := Nat.mul_le_mul_left _ hsurv
      _ ≤ _ := hb
  rw [tsub_mul, mul_tsub]
  exact Nat.sub_le_sub_right h1 _

end CollatzMoonshot.FrontA.FirstCrossing
