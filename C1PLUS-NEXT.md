# C1⁺ (`WeakDecayOnZ3`): plan for the treadmill (personal-c5, 2026-10-26)

**Target:** `CollatzMoonshot/Conjugacy/WeakDecay.lean` sorry-free.  The headline is
`weakDecayOnZ3 : WeakDecayOnZ3` (already assembled from the two edges below).

## Frozen (never change these statements)
- `WeakDecayOnZ3`, `biasClassPow` (`Recursion.lean`), `BiasDecays`, `bias`, `levelSet`.
- `overPrecChar`, `OverPrecSliceCharDecay`, and the statements of the three theorems in `WeakDecay.lean`.
- Do not edit `SliceSeven.lean`, `SliceFourier.lean`, `C1.lean`, `Recursion.lean`, `Bridge3*.lean` or
  `SliceDecay.lean`.  New lemmas go in new files (`WeakDecayAux.lean`, `WeakDecaySec7P.lean`, …),
  imported by `WeakDecay.lean`.  tao-collatz (`.lake/packages/TaoCollatz`) is read-only: import its
  public theorems, do not modify it.
- No `native_decide`, no new `axiom`, no new `maxHeartbeats` above what SliceSeven already uses.  Commit
  locally; never push.

## Edge 1: `weakDecayOnZ3_of_overPrecSliceCharDecay` (the SliceFourier pattern, simpler)
1. Character expansion of the class indicator on `ℤ/3^k`:
   `biasClassPow m k c = 3^{−k} Σ_{η < 3^k} e(−ηc/3^k) · Tw m k η`, where
   `Tw m k η = Σ_{r < 2^m} (−1)^{T^m r} e(η r / 3^k)`.  `Tw m k 0 = bias m`, so it is done by `biasDecays`.
   For `c ≥ 3^k` the class is empty.
2. Split `Tw` over slices `levelSet m a`.  Slices with `a/m ∉ [1/4, 11/20]` lie in `outOddSet m`,
   which has card `≤ 100·2^m/m` (`outOddSet_card_mul_sq_le`).
3. On a slice: `tstep_iterate_identity` gives `2^m y = 3^a r + N_r`, `y = T^m r < 3^a`
   (`tstep_iterate_lt_three_pow`).  So `e(η r/3^k) = e(η (2^m y − N_r)/3^{a+k})` exactly (an equality of
   rationals).
4. Expand `g(y) = (−1)^y e(η 2^m y / 3^{a+k})` on `[0, 3^a)` in characters of `ℤ/3^a`.  The Fourier
   coefficient is a geometric sum, `|ĝ(ξ)| ≤ min(1, 1/(3^a |sin π φ_ξ|))`, with `φ_ξ = 1/2 + η2^m/3^{a+k} − ξ/3^a`.
   The ℓ¹ weight is `O(a)`.  Reuse SliceFourier's `O(log M)` cosecant-sum lemmas where they generalize;
   the shift by `η2^m/3^{a+k}` is the new part.
5. `y ≡ 2^{−m} N_r (mod 3^a)`, so each term is `e(ζ N_r/3^{a+k})`, `ζ = 3^k ξ·(2^{−m} mod 3^a) − η`.
   `v₃(ζ) = v₃(η) =: v < k`, so it is `overPrecChar m a (k − v) ζ'` with `3 ∤ ζ'`.
6. Bound: `|Tw on main slices| ≤ O(a)·C_{k}·m^{−3}·Σ #slice ≤ O(2^m/m^2)`; plus tails `O(2^m/m)`.

Numerical check of steps 3–5 (exact identity): `experiments/conjugacy/c1plus_twistcheck.py`.

## Edge 2: `overPrecSliceCharDecay` (Sec7P absorbs a fixed precision shift)
1. Level-`(a + k)` version of `norm_sliceChar_le_mode_damping` (SliceSeven): bound
   `‖overPrecChar j a k ξ‖ ≤ (j+1)^2 · C(j,a) · E_{b ~ Pascal(p)^{⌊a/2⌋}} ∏_{q < ⌊a/2⌋} ‖fCond (a+k) ξ' (xArg (a+k) q (pre b (q+1))) (b q)‖`
   with `p = a/j`, `ξ'` a unit multiple of `ξ` (the `2^{−j}` twist).  Re-run SliceSeven's proof with
   modulus `3^{a+k}` in place of `3^a`.  The pairing and slice-to-Pascal conditioning never use `n = a`
   except through the modulus.
2. Padding: extend `b` to `⌊(a+k)/2⌋` coordinates with independent `Pascal(p)` entries.  Whiteness
   at `q` depends only on `pre b (q+1)` (prefix), so
   `exp(−ε³ #white_{q < ⌊a/2⌋}) ≤ exp(ε³ ⌈k/2⌉+1) · exp(−ε³ #white_{q < ⌊(a+k)/2⌋})`.
3. `prod_fCond_le_dampingP` on the kept product (each `‖fCond‖ ≤ 1`, so a sub-product of the
   `if white then exp(−ε³) else 1` bound), then `renewal_white_encountersP` at `n = a + k`.
4. Absorb `(j+1)^2` and `(a+k)^{−A'}` vs `j^{−A}` as in `sliceCharDecay_of_pascalDampingDecay`
   (`a ≥ j/5`).

If edge 2 step 1 turns out to need SliceSeven internals that are private or `n = a`-specialized, copy
the needed lemma into `WeakDecaySec7P.lean` generalized to level `n ≥ a` (do not edit SliceSeven).
Record any wall here, under a dated lap checkpoint.
