/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# Assumed: cycle-length lower bounds

Tier: THEOREM-grade (published proofs, unformalized).  This is Front B territory
(`APPROACHES.md`, Approach 3): Baker linear forms + the continued fraction of
`log₂ 3` make cycle lengths astronomically large.
-/

namespace CollatzMoonshot.Assumed

/-- **[ASSUMED - published theorem]** Any cycle of `step` outside the trivial one
has period at least `27,869,189`.

Provenance: Eliahou (1993), *The 3x+1 problem: new lower bounds on nontrivial
cycle lengths* (Discrete Math. 118; PDF + summary in `papers/`), via the product
identity `∏ (3 + 1/n) = 2^k` over odd cycle elements plus the continued-fraction
structure of `log₂ 3` and the 1993 verification cutoff `2⁴⁰`.  ⚠️ Map bookkeeping:
Eliahou's headline `17,087,915` counts iterations of the SHORTCUT map
(`(3n+1)/2` in one step), with `10,781,274` odd steps; this repo's `step` takes
the odd move in two steps, so the corresponding bound here is the sum,
`27,869,189`.  The modern frontier (Hercher 2023 + Bařina's `2⁷¹` verification)
pushes this to ~`3.6 × 10¹¹` for this map - verified firsthand 2026-08-22 and
adopted below as `hercher_odd_members_bound`; this 1993 bound stays for
provenance-pinned results.

Stated for ALL periods, not just the minimal one: any period is a multiple of the
minimal period, so the bound transfers. -/
axiom eliahou_min_cycle_length :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 27869189 ≤ m

/-- **[ASSUMED - published theorem + computation]** Any nontrivial cycle of
`step` passes through at least `1.375 × 10¹¹` odd values per period.

Provenance: Hercher 2023 (*J. Integer Seq.* 26, 23.3.5), Corollary 29: if the
verification frontier `X₀ ≥ 1536 · 2⁶⁰`, every nontrivial cycle contains
`K ≥ 1.375 × 10¹¹` odd members - combined with Bařina 2025 (`X₀ = 2075 · 2⁶⁰`,
see `Computation.lean`), which clears that threshold with 35% headroom.  Both
sources verified firsthand 2026-08-22 (summaries in `papers/`).  The count is
odd STEPS in one period, which for the minimal period is exactly Hercher's
count of odd members and for a multiple of it is a multiple of that.

⚠️ Two-source axiom: this stands on a published proof AND compute-trust of the
distributed verification.  The docstring is the ledger entry for both. -/
axiom hercher_odd_members_bound :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨
        137500000000 ≤ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card

/-- The frontier cycle-length bound, PROVED from `hercher_odd_members_bound`:
a nontrivial cycle's period is at least `1.375 × 10¹¹` - four orders of
magnitude past `eliahou_min_cycle_length`.  (The period bounds the odd-step
count trivially.) -/
theorem frontier_min_cycle_length :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 137500000000 ≤ m := by
  intro n m hn hm hcyc
  rcases hercher_odd_members_bound n m hn hm hcyc with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans h ?_)
    calc ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card
        ≤ (Finset.range m).card := Finset.card_filter_le _ _
      _ = m := Finset.card_range m

end CollatzMoonshot.Assumed
