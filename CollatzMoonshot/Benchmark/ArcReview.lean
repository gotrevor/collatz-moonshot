/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Benchmark.ArcDelay

/-! Second-opinion targets, 2026-10-09.  These separate possible mechanisms from the
existing conjectures; no geometric liveness or bounded-delay claim is proved here.
-/
namespace CollatzMoonshot.Benchmark.ArcReview

open ArcTrap ArcDelay

/-- A legal predecessor of a strategy.  The same move must work for both unseen top bits.
This retains the fractional-position restriction absent from the refuted carry-only game. -/
def geometricPre (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ) (r : ℕ) : Set ℝ :=
  {a | a ∈ Set.Ico 0 1 ∧ ∃ u : ℝ, a ≤ u ∧ u + 2 * l / 3 ≤ a + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ u ∧ u + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b < 2, Int.fract (3 * u / 2 + ((r % 2 : ℕ) : ℝ) / 2) ∈
      P (((3 * r - r % 2) / 2 + (⌊3 * u / 2 + ((r % 2 : ℕ) : ℝ) / 2⌋).toNat) %
        2 ^ (k - 1) + b * 2 ^ (k - 1))}

/-- Add legal predecessors without deleting the seed strategy. -/
def saturate (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ) : ℕ → ℕ → Set ℝ
  | 0 => P
  | n + 1 => fun r => saturate s t l k P n r ∪
      geometricPre s t l k (saturate s t l k P n) r

/-- Candidate mechanism, not an established invariant: every live seed can be enlarged by
finitely many predecessor layers to have a common start at every pair of lifts.
This is stronger than weak liveness.  The first control is the known k=6 dodging strategy:
remove its forbidden-class constraint and ask whether saturation restores the missing base.
Its failure would retire this mechanism, not weak liveness itself.
**First control passed (2026-10-09, `arc_trap_k.saturate_vw`):** from the `k = 6` dodge (arc
`[2/5, 2/5 + 87/100]`, widths `j = 100, 130`, base `27` missing), ONE predecessor layer restores base
`27` (good bases `31 → 32`), and saturation converges in 36 rounds to a strategy live at all 64 classes.
That limit is strictly inside the greatest fixed point.  Regression `test_saturation_restores_the_dodged_base`.
Confidence 60%: one discriminating instance; no other non-maximal seed is known to test. -/
def PredecessorSaturationAllBases : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k →
    KRelaxedStrategy s t l k P → (∃ r < 2 ^ k, (P r).Nonempty) →
    ∃ n, KRelaxedStrategy s t l k (saturate s t l k P n) ∧
      ∀ b < 2 ^ (k - 1),
        (saturate s t l k P n b ∩ saturate s t l k P n (b + 2 ^ (k - 1))).Nonempty

theorem PredecessorSaturationAllBases.allBasesGood
    (h : PredecessorSaturationAllBases) : KRelaxedAllBasesGood := by
  intro s t l k P hk hP hne
  obtain ⟨n, hn, hb⟩ := h s t l k P hk hP hne
  exact ⟨saturate s t l k P n, hn, hb⟩

/-- Only compare worst start depths.  Unlike StartDelayCostBounded, the premise must kill
ALL k-residues at D; a fast individual residue need not retain its advantage after lifting. -/
def WorstStartDelayCostBounded (β : ℚ) (c : ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∀ D,
    (∀ r < 2 ^ k, advKills β k D 0 3 r = true) →
    ∀ r < 2 ^ (k + 1), advKills β (k + 1) (D + c) 0 3 r = true

theorem StartDelayCostBounded.worst {β : ℚ} {c : ℕ}
    (h : StartDelayCostBounded β c) : WorstStartDelayCostBounded β c := by
  intro k hk D hD r hr
  exact h k hk D r hr (hD _ (Nat.mod_lt _ (by positivity)))

/-- No bounded increment is needed if one constructs any explicit finite envelope F. -/
def StartKillEnvelope (β : ℚ) (F : ℕ → ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∀ r < 2 ^ k, advKills β k (F k) 0 3 r = true

theorem worstStartDelay_envelope {β : ℚ} {c D : ℕ}
    (h : WorstStartDelayCostBounded β c)
    (h1 : ∀ r < 2, advKills β 1 D 0 3 r = true) :
    StartKillEnvelope β (fun k => D + (k - 1) * c) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h1
  | succ k hk ih =>
    have hh := h k hk _ ih
    have e : D + k * c = D + (k - 1) * c + c := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp [add_mul, add_assoc]
    simpa only [Nat.add_sub_cancel, e] using hh

/-- The envelope route still owes a geometric estimate; this is just its implication. -/
theorem finiteMemoryRelaxedValue_of_envelopes
    (h : ∀ β : ℚ, 7 / 57 < β → β < 1 / 2 →
      ∃ F : ℕ → ℕ, StartKillEnvelope β F) : FiniteMemoryRelaxedValue := by
  intro k hk β hβ hβ' l P hne hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hβ
  have e1 : (7 / 57 : ℝ) = ((7 / 57 : ℚ) : ℝ) := by push_cast; ring
  have e2 : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; ring
  obtain ⟨F, hF⟩ := h q (by rw [e1] at hq1; exact_mod_cast hq1)
    (by have := hq2.trans hβ'; rw [e2] at this; exact_mod_cast this)
  exact not_kRelaxedStrategy_of_advKills hk (hF k hk) l P hne (hS.mono hq2.le)

end CollatzMoonshot.Benchmark.ArcReview
