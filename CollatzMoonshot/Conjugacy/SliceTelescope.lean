/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Bridge3

/-!
# SEC6S lap 1: the slice mixture identity (`SEC6S-PLAN.md` §2(a))

Reducing the slice law `(j, a)` modulo `3^{a'}` (`a' < a`) is a binomially weighted mixture of
the slice laws `(t − 1, a')`, `1 ≤ t ≤ j`:

    levelClass j a a' c = Σ_{t=1}^{j} C(j − t, a − a' − 1) · levelMass (t − 1) a' c.

Why: for `r < 2^j` with trace word `w` (`a` ones), `2^j · T^j r = 3^a · r + numer w`
(`tstep_iterate_identity`), and `numer (u ++ v) = 3^{ones v} · numer u + 2^{|u|} · numer v`
(induction on `v` from `numer_append_true` / `numer_append_false`).  Split `w = u ++ v` with `u`
the prefix through the `(a − a')`-th one (position `s`) and `v` the suffix (length
`t − 1 = j − s`, `a'` ones).  Then `3^a r + 3^{a'} numer u ≡ 0`, so
`T^j r ≡ 2^{−(t−1)} · numer v ≡ T^{t−1} r' (mod 3^{a'})`, where `r' < 2^{t−1}` is the start with
trace word `v`; and `T^{t−1} r' < 3^{a'}` (`tstep_iterate_lt_three_pow`), so the residue is the
value.  The prefix `u` (ending in a one, `a − a'` ones in all) has `C(s − 1, a − a' − 1)`
`= C(j − t, a − a' − 1)` choices.  Exact check: `experiments/conjugacy/mixture.py` (455 triples,
`j ≤ 13`, 0 mismatches; the off-by-one control fails 449/455).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-- **Frozen.**  The slice mixture identity (SEC6S §2(a)): the class count of the slice `(j, a)`
modulo `3^{a'}` is the binomially weighted sum of the slice masses `(t − 1, a')`, `1 ≤ t ≤ j`. -/
theorem levelClass_eq_sum_levelMass (j a a' c : ℕ) (h : a' < a) :
    levelClass j a a' c =
      ∑ t ∈ Finset.Icc 1 j, (j - t).choose (a - a' - 1) * levelMass (t - 1) a' c := by
  sorry

end CollatzMoonshot.Conjugacy
