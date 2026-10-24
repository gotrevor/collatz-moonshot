# Bridge3: prove the three owed edges 🌉

**Objective:** make `CollatzMoonshot/Conjugacy/Bridge3.lean` sorry-free.  The headline is axiom-clean:
`#print axioms CollatzMoonshot.Conjugacy.biasDecays_of_truncatedSyracMixing` reports
`[propext, Classical.choice, Quot.sound]`.

**Do not change** any statement in `Bridge3.lean`: the definitions `levelSet`, `levelSign`,
`levelMass`, `levelClass`, `levelOsc`, the node `TruncatedSyracMixing`, and the three theorem
statements.  Do not edit any other `Conjugacy/*.lean` file; in particular `Fourier.lean` is
another session's.  Put helper lemmas in a new file `CollatzMoonshot/Conjugacy/Bridge3Aux.lean`
and import it from `Bridge3.lean`, or put them above the theorem in `Bridge3.lean`.  No
`native_decide`, no new `axiom`.  `decide +kernel` is fine for concrete values.  Read the module
docstring of `Bridge3.lean` and research note §11 (`RESEARCH-2026-10-21-conjugacy-ladder.md`)
first.

## The three edges, with proof plans

1. **`bias_eq_sum_levelSign`**: `bias j = Σ_{a < j+1} levelSign j a`.  Use a fiberwise sum over
   `fun r => oddCount r j` mapping `range (2^j)` into `range (j+1)`
   (`Finset.sum_fiberwise_of_maps_to`).  It needs `oddCount r j ≤ j`, since `ones` of a
   length-`j` trace is at most `j`; check `Ladder.lean` and `Obstructions/ParityWordGenericity`
   for `traceWord` length lemmas.

2. **`abs_levelSign_le`** (`m ≤ a`).  Let `S = levelSet j a`, and let `σ(y) = ±1` be the parity
   sign.
   - For `r ∈ S`, `tstep^[j] r < 3^a` by `tstep_iterate_lt_three_pow`.  So
     `levelSign = Σ_{y < 3^a} levelMass y · σ y`, regrouping `S` by the value `tstep^[j] r`.
   - Write `λ y = 3^m/3^a · levelClass (y % 3^m)`.  Then `Σ mass·σ = Σ (mass − λ)·σ + Σ λ·σ`.
     The first term is `≤ levelOsc`, since `|σ| = 1`.
   - For the second, use the bijection `y ↔ (c, t)`, `y = c + 3^m t`, `c < 3^m`, `t < 3^(a−m)`.
     `σ(c + 3^m t) = σ(c)·(−1)^t` because `3^m` is odd, and `Σ_{t < 3^(a−m)} (−1)^t = 1` because
     `3^(a−m)` is odd.  So `|Σ λ σ| ≤ 3^m/3^a · Σ_c levelClass c = 3^m/3^a · #S`; the classes
     partition `S`, as `tstep^[j] r % 3^m < 3^m`.

3. **`biasDecays_of_truncatedSyracMixing`**.
   - Divide `bias j` by `2^j` and split with edge 1 into `a ≤ 11j/20` and `a > 11j/20`.
   - Low `a`: the node with `ε` plus edge 2 give `|levelSign j a| ≤ 2ε·#levelSet j a`.  The
     `levelSet j a` are disjoint subsets of `range (2^j)`, so their total size is `≤ 2^j`.
   - High `a`: `|levelSign j a| ≤ #levelSet j a`.  The total is `#{r < 2^j : oddCount r j > 11j/20}`.
     Show it is `o(2^j)` by Chebyshev, which avoids Chernoff.  Via the Terras bijection
     `r ↦ traceWord r j`, this is the number of length-`j` binary words with more than `11j/20`
     ones, and `Σ_w (ones w − j/2)² = (j/4)·2^j`.  So the count is
     `≤ (j/4)·2^j / (j/20)² = 100·2^j/j`.
   - If the Terras bijection is not in the repo, use the alternative.  Prove
     `Σ_{r<2^j} (oddCount r j − j/2)² = (j/4)·2^j` directly, by induction on `j`, from
     `accWord_add_two_pow`: the top bit flips the `j`-th letter and leaves the earlier letters
     unchanged.

**Verify:** `lake build CollatzMoonshot.Conjugacy.Bridge3`; `#print axioms` on the three theorems;
the teeth `levelSign_four`, `levelSign_five` and `levelSet_card_five` must stay green.
