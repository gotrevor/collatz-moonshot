/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycle.Count

/-!
# The quantized ladder and the near-cycle reduction

The 2026-10-14 "fsfloor" agent (research §35).  A *rung* is a forward survivor `n` that is not its
orbit's minimum; its *depth* `g` is its first backward drop, `p = Vᵍ n` is the next lower forward
survivor (§31's P′), and `ρ = n/p ∈ (1, 3/2]`.

**`rung_log_ratio` (Theorem SQ, part 1).**  Along `p → n` each step is `x ↦ (3x + e)/2^d` with
`e ∈ {0, ±1}`, and `e ≠ 0` only at odd points, which are intermediate points `> n` (a ladder
excursion never dips below its endpoint).  So `log ρ = g log 3 − a log 2` up to a carry
`≤ g/(3n − 1)`, not the `O(log g)` of a general return.

**`rung_depth_spectrum` (Theorem SQ, part 2).**  Hence, once the carry is small, `{gθ} ≤ θ − 1`
(`θ = log₂ 3`): forward-survivor depths lie in the Sturmian set `{1, 2, 4, 6, 7, 9, 11, 12, …}`.
Backward-survivor depths lie in the complementary set `{1, 3, 5, 8, 10, 13, …}`.  Checked on all
of `[1, 2²³)`: 0 off-spectrum.  The rewired `τ` and `τ_odd` break it on 35–43% of their rungs.

**`bwdSurvivor_odd_separation`.**  The mirror of Sep3: two backward survivors `n < n'` on one orbit
with `n'` odd satisfy `4n ≤ 3n' + 1`.

**`infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null` (Theorem NC′).**  A `D`-near-cycle
start is a `p` whose forward orbit first re-enters `[0, p + D]` inside `(p, p + D]`.  If
near-cycle starts have density `0` for every `D`, then forward survivors of positive upper
density already imply Klamkin (a): the threshold of §31's C2′ drops from `c` to `0`.  Proof
(`NearCycle.card_fwdSurvivor_le`): under `r` orbits, a forward survivor below `X` is an orbit
minimum (at most `r`) or a rung with predecessor `p` (`NearCycle.IsRungPred`).  On one orbit `p`
is the next lower forward survivor (P′), so the rungs with gap `> D` are `D`-separated: at most
`r (X/D + 1)` of them.  Every other rung's predecessor is a `D`-near-cycle start, injectively
(`n` is the minimum of `p`'s forward orbit after time `0`).  This linear packing replaces the
kickoff's multiplicative telescoping.
-/

namespace CollatzMoonshot.Amusical

/-- **Proved (Sep3 mirror).**  Odd backward survivors separate orbits.  (`h0` is not used.) -/
theorem bwdSurvivor_odd_separation {n n' : ℤ} (hn : BwdSurvivor n) (hn' : BwdSurvivor n')
    (h0 : 0 ≤ n) (hlt : n < n') (hodd : Odd n') (horb : n ∈ amusicalOrbit n') :
    4 * n ≤ 3 * n' + 1 := by
  have hU := NearCycle.four_mul_amusical_le_of_odd hodd
  obtain ⟨t, ht | ht⟩ := Ceiling.exists_iterate_of_mem_amusicalOrbit horb
  · rcases t with _ | t
    · simp at ht; omega
    have key : n ≤ amusical n' := by
      rcases t with _ | t
      · simp at ht; omega
      · have hback : amusicalInv^[t + 1] n = amusical n' := by
          rw [ht, Function.iterate_add_apply]
          simpa using (Function.LeftInverse.iterate amusicalInv_amusical (t + 1)) (amusical n')
        have := hn (t + 1) (by omega)
        omega
    omega
  · rcases t with _ | t
    · simp at ht; omega
    · have := hn' (t + 1) (by omega)
      omega

/-- **Proved (Theorem SQ, part 1).**  The log-ratio of a rung is `g log 3 − a log 2` up to the
carry `g/(3n − 1)`.  (`hg` is not used: for `g = 0` the hypothesis `hdrop` is false.) -/
theorem rung_log_ratio {n : ℤ} {g : ℕ} (hg : 1 ≤ g) (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) :
    ∃ a : ℕ, |Real.log ((n : ℝ) / (amusicalInv^[g] n : ℝ)) - (g * Real.log 3 - a * Real.log 2)|
      ≤ g / (3 * (n : ℝ) - 1) := by
  obtain ⟨a, ha⟩ := NearCycle.rung_log_iter hn hpos hdrop hmin g le_rfl
  obtain ⟨hp2, -, -⟩ := NearCycle.rung_base hn hpos hdrop hmin
  refine ⟨a, ?_⟩
  rw [NearCycle.iterate_rung le_rfl, Nat.sub_self, Function.iterate_zero, id_eq] at ha
  have hp : (0 : ℝ) < (amusicalInv^[g] n : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) < amusicalInv^[g] n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < n)
  rw [Real.log_div hn0.ne' hp.ne']
  convert ha using 2
  ring

/-- **Proved (Theorem SQ, part 2).**  Once the carry is below both margins, the depth of a rung is
a forward-survivor depth: `{gθ} ≤ θ − 1`. -/
theorem rung_depth_spectrum {n : ℤ} {g : ℕ} (hg : 1 ≤ g) (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n)
    (hbig : (g : ℝ) / ((3 * n - 1) * Real.log 2) <
      min (1 - Int.fract (g * Real.logb 2 3))
        |Int.fract (g * Real.logb 2 3) - (Real.logb 2 3 - 1)|) :
    Int.fract (g * Real.logb 2 3) ≤ Real.logb 2 3 - 1 := by
  obtain ⟨a, ha⟩ := rung_log_ratio hg hn hpos hdrop hmin
  obtain ⟨hp2, -, h32⟩ := NearCycle.rung_base hn hpos hdrop hmin
  set p := amusicalInv^[g] n with hpdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < p)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < n)
  have hn3 : (0 : ℝ) < 3 * (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hpos
    linarith
  set θ := Real.logb 2 3 with hθ
  have hθ' : θ = Real.log 3 / Real.log 2 := rfl
  set lam := Real.log ((n : ℝ) / p) with hlam
  -- `0 < λ ≤ log 3 − log 2`
  have hlam0 : 0 < lam := Real.log_pos (by rw [one_lt_div hp]; exact_mod_cast hdrop)
  have hlam1 : lam ≤ Real.log 3 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    apply Real.log_le_log (div_pos hn0 hp)
    rw [div_le_div_iff₀ hp (by norm_num)]
    have : (2 : ℝ) * n ≤ 3 * p := by exact_mod_cast h32
    linarith
  set ε := (g : ℝ) / ((3 * n - 1) * Real.log 2) with hε
  have hs : |lam / Real.log 2 - (g * θ - a)| ≤ ε := by
    have h1 : lam / Real.log 2 - (g * θ - a) =
        (lam - (g * Real.log 3 - a * Real.log 2)) / Real.log 2 := by
      rw [hθ']; field_simp
    rw [h1, abs_div, abs_of_pos hl2, hε, ← div_div]
    exact div_le_div_of_nonneg_right ha hl2.le
  set s := lam / Real.log 2 with hsdef
  have hs0 : 0 < s := div_pos hlam0 hl2
  have hs1 : s ≤ θ - 1 := by
    rw [hsdef, div_le_iff₀ hl2, hθ', sub_mul, div_mul_cancel₀ _ hl2.ne']
    linarith
  by_contra hf
  push Not at hf
  set f := Int.fract (g * θ) with hfdef
  have hε1 : ε < 1 - f := lt_of_lt_of_le hbig (min_le_left _ _)
  have hε2 : ε < f - (θ - 1) := by
    have := lt_of_lt_of_le hbig (min_le_right _ _)
    rwa [abs_of_pos (by linarith)] at this
  have hfl : g * θ = ⌊g * θ⌋ + f := by rw [hfdef, Int.fract]; ring
  rw [abs_le] at hs
  rcases le_or_gt 0 (⌊(g : ℝ) * θ⌋ - (a : ℤ)) with hk | hk
  · have : (0 : ℝ) ≤ ((⌊(g : ℝ) * θ⌋ - (a : ℤ) : ℤ) : ℝ) := by exact_mod_cast hk
    push_cast at this
    linarith
  · have : ((⌊(g : ℝ) * θ⌋ - (a : ℤ) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : _ ≤ (-1 : ℤ))
    push_cast at this
    linarith

/-- A `D`-near-cycle start: the forward orbit of `p` first re-enters `[0, p + D]` inside
`(p, p + D]`. -/
def NearCycleStart (D p : ℕ) : Prop :=
  ∃ g ≥ 1, (p : ℤ) < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
    ∀ k, 1 ≤ k → k < g → (p : ℤ) + D < amusical^[k] p

open Classical in
/-- **Proved (Theorem NC′).**  If near-cycle starts have density `0` for every `D`, forward
survivors of positive upper density imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null
    (hNC : ∀ D : ℕ, Filter.Tendsto (fun X : ℕ =>
        (((Finset.range X).filter (NearCycleStart D)).card : ℝ) / X) Filter.atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ)
    (hFS : ∃ᶠ X : ℕ in Filter.atTop,
        δ * X ≤ ((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  obtain ⟨r, hr⟩ := NearCycle.card_fwdSurvivor_le hfin
  set D : ℕ := ⌈8 * (r : ℝ) / δ⌉₊ + 1 with hDdef
  have hD1 : 1 ≤ D := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have hrD : 8 * (r : ℝ) ≤ δ * D := by
    have h1 : 8 * (r : ℝ) / δ ≤ D := by
      rw [hDdef]; push_cast; linarith [Nat.le_ceil (8 * (r : ℝ) / δ)]
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hNCD := (hNC D).eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by linarith))
  obtain ⟨X, hX1, hX2, hX3⟩ := (hFS.and_eventually (hNCD.and
    (Filter.eventually_ge_atTop (⌈4 * (r : ℝ) / δ⌉₊ + 1)))).exists
  have hXpos' : 0 < X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hXpos'
  have hX4 : 4 * (r : ℝ) < δ * X := by
    have h1 : 4 * (r : ℝ) / δ < X := by
      have := Nat.le_ceil (4 * (r : ℝ) / δ)
      have h2 : ((⌈4 * (r : ℝ) / δ⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX3
      push_cast at h2
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hNC' := (div_lt_iff₀ hXpos).mp hX2
  have hcount := hr D X hD1
  have hcountR : (((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card : ℝ) ≤
      2 * r + r * ((X / D : ℕ) : ℝ) +
        (((Finset.range X).filter (NearCycleStart D)).card : ℝ) := by
    exact_mod_cast hcount
  have hXD : (r : ℝ) * ((X / D : ℕ) : ℝ) ≤ δ * X / 8 := by
    calc (r : ℝ) * ((X / D : ℕ) : ℝ) ≤ r * ((X : ℝ) / D) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
      _ = (8 * r) * X / (8 * D) := by field_simp
      _ ≤ (δ * D) * X / (8 * D) := by gcongr
      _ = δ * X / 8 := by field_simp
  nlinarith

end CollatzMoonshot.Amusical
