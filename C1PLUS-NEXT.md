# C1⁺ (`WeakDecayOnZ3`): plan for the treadmill (personal-c5, 2026-10-26)

**Target:** `CollatzMoonshot/Conjugacy/WeakDecay.lean` sorry-free.  The headline is
`weakDecayOnZ3 : WeakDecayOnZ3` (already assembled from the two edges below).

**Completed checkpoint (2026-10-26):** the target is sorry-free and `weakDecayOnZ3` is proved;
see `HANDOFF-2026-10-26-c1plus-twist.md`. The Fourier-mass estimate needed a correction:
the uniform `O(a+k)` conjecture is false near a shifted pole, while the proved sufficient bound is
`sum ‖twistedHat‖ ≤ 3^k * 4 * (a+k+1)`. Edge 2 is closed by a generalized fine-modulus
gap-pairing module and padding missing pair sums by `2`, at fixed-`k` cost at most `25^k`.
The real target gate is green and the headline theorem uses only the standard trust base.

## Frozen (never change these statements)
- `WeakDecayOnZ3`, `biasClassPow` (`Recursion.lean`), `BiasDecays`, `bias`, `levelSet`.
- `overPrecChar`, `OverPrecSliceCharDecay`, and the statements of the three theorems in `WeakDecay.lean`.
- Do not edit `SliceSeven.lean`, `SliceFourier.lean`, `C1.lean`, `Recursion.lean`, `Bridge3*.lean` or
  `SliceDecay.lean`.  New lemmas go in new files (`WeakDecayAux.lean`, `WeakDecaySec7P.lean`, …),
  imported by `WeakDecay.lean`.  tao-collatz (`.lake/packages/TaoCollatz`) is read-only: import its
  public theorems, do not modify it.
- No `native_decide`, no new `axiom`, no new `maxHeartbeats` above what SliceSeven already uses.  Commit
  locally; never push.

## Edge 1: `weakDecayOnZ3_of_overPrecSliceCharDecay` (COMPLETE)
1. Character expansion of the class indicator on `ℤ/3^k`:
   `biasClassPow m k c = 3^{−k} Σ_{η < 3^k} e(−ηc/3^k) · Tw m k η`, where
   `Tw m k η = Σ_{r < 2^m} (−1)^{T^m r} e(η r / 3^k)`.  `Tw m k 0 = bias m`, so it is done by `biasDecays`.
   For `c ≥ 3^k` the class is empty.
2. Split `Tw` over slices `levelSet m a`.  Slices with `a/m ∉ [1/4, 11/20]` lie in `outOddSet m`,
   which has card `≤ 100·2^m/m` (`outOddSet_card_mul_sq_le`).
3. On a slice: `tstep_iterate_identity` gives `2^m y = 3^a r + N_r`, `y = T^m r < 3^a`
   (`tstep_iterate_lt_three_pow`).  So `e(η r/3^k) = e(η (2^m y − N_r)/3^{a+k})` exactly (an equality of
   rationals).
4. Expand `g(y) = (−1)^y e(η 2^m y / 3^{a+k})` on `[0, 3^a)` in characters of `ℤ/3^a`.
   Comparing the shifted grid with all ordinary parity coefficients at the fine modulus proves
   the sufficient ℓ¹ bound `3^k * 4 * (a+k+1)`.
5. `y ≡ 2^{−m} N_r (mod 3^a)`, so each term is `e(ζ N_r/3^{a+k})`, `ζ = 3^k ξ·(2^{−m} mod 3^a) − η`.
   `v₃(ζ) = v₃(η) =: v < k`, so it is `overPrecChar m a (k − v) ζ'` with `3 ∤ ζ'`.
6. Bound: `|Tw on main slices| ≤ O(a)·C_{k}·m^{−3}·Σ #slice ≤ O(2^m/m^2)`; plus tails `O(2^m/m)`.

Numerical check of steps 3–5 (exact identity): `experiments/conjugacy/c1plus_twistcheck.py`.

## Edge 2: `overPrecSliceCharDecay` (COMPLETE)
1. Level-`(a + k)` version of `norm_sliceChar_le_mode_damping` (SliceSeven): bound
   `‖overPrecChar j a k ξ‖ ≤ (j+1)^2 · C(j,a) · E_{b ~ Pascal(p)^{⌊a/2⌋}} ∏_{q < ⌊a/2⌋} ‖fCond (a+k) ξ' (xArg (a+k) q (pre b (q+1))) (b q)‖`
   with `p = a/j`, `ξ'` a unit multiple of `ξ` (the `2^{−j}` twist).  Re-run SliceSeven's proof with
   modulus `3^{a+k}` in place of `3^a`.  The pairing and slice-to-Pascal conditioning never use `n = a`
   except through the modulus.
2. Padding: extend `b` to `⌊(a+k)/2⌋` coordinates with the fixed value `2`. The added pair
   factors have norm one, and their Pascal mass is `p² ≥ 1/25`, so the partial expectation is
   at most `25^d` times the full damping, `d = ⌊(a+k)/2⌋-⌊a/2⌋ ≤ k`.
3. Apply the public full `pascal_damping_decay` theorem at `n = a+k`.
4. Absorb `(j+1)^2` and `(a+k)^{−A'}` vs `j^{−A}` as in `sliceCharDecay_of_pascalDampingDecay`
   (`a ≥ j/5`).

The required generalized lemmas live in the new `WeakDecaySec7P.lean`; `SliceSeven.lean` was not
edited. No further work remains under this target.
