# Handoff — quadratic invariants (2026-09-27)

Both frozen headlines in `CollatzMoonshot/Obstructions/QuadraticInvariants.lean`
are proved.  `lake build` on the root is green; no `sorry` in the module.

## Kernel state

```
small_generator_count_invariant  → [propext, Classical.choice, Quot.sound]
no_catalyst_for_five_exchange    → [propext, Classical.choice, Quot.sound]
pair_small_core                  → [propext, Classical.choice, Quot.sound]
five_exchange_value              → + its native_decide anchor (pre-existing)
```

No statement was changed or weakened; no other module was touched.

## How it goes through

1. **Symmetries.** `pairRel a b c d : (3(a+b)+1)cd = ab(3(c+d)+1)` is symmetric
   in `a↔b`, `c↔d` and pair↔pair — `pairRel_swap_left/right/symm`, each a
   one-line `linear_combination`.

2. **`pair_smaller_bound`** — a local copy of the private `MinimalRepairs`
   argument (integral form of `r_u = 2u/(3u+1) < 2/3`).  Instantiated at
   `D = 3(a+b)+1`, `A = ab`, `M = 2a+1`, whose two side conditions
   `3A ≤ DM` and `6AM + A < DM²` are pure positivity (`nlinarith`).  Gives
   `pair_small_head_bound : c < 2a+1` for the sorted replacement pair, with
   **no upper bound on `b`**.

3. **`pair_small_core`** (a ∈ {1,3,5}, c ≤ d, all positive and odd).  Rearrange
   `pairRel` into the bilinear `key : 3(a-c)·b·d + a(3c+1)·b = c(3a+1)·d`.
   * `c = a` ⇒ `a·(3a+1)·(d-b) = 0` ⇒ `d = b` (`pair_same_head`).
   * `c < a` ⇒ dropping the positive `a(3c+1)b` and cancelling `d > 0` gives
     `3(a-c)b < c(3a+1)`; over `a ≤ 5` this forces `b < 8`, and
     `interval_cases c <;> interval_cases b <;> omega` finishes from `key`.
   * `a < c` ⇒ cancelling `b > 0` gives `3(c-a)d < a(3c+1)`, hence `d < 19`;
     `interval_cases c <;> interval_cases d <;> omega` finishes, oddness of `b`
     killing the residual `c = 7, 9` solutions (`b = 18, 28, 84, 198, …`).
   Conclusion: the sorted new pair is `(a,b)` or `(b,a)`.

4. **`pair_small_eq` / `step_pair_eq`.** `le_total` plus `pairRel_swap_right`
   removes the sortedness hypothesis; the three other symmetries move *any* of
   the four labels into the first slot.  So: if a small generator occurs
   anywhere among `a,b,c,d`, then `{a,b} = {c,d}` as multisets.

5. **`count_pair_eq`.** If the small `x` occurs in neither pair both counts are
   `0`; otherwise step 4 makes the pairs equal.  Multiplicity is therefore
   preserved even when both labels coincide — no injectivity side-condition
   needed.

6. **`small_generator_count_invariant`** — `ReflTransGen` induction, the common
   catalyst `r` cancelling via `Multiset.count_add`.

7. **`no_catalyst_for_five_exchange`** — `count 5 {5,55,83} = 1` versus
   `count 5 {11,13,17} = 0` (both `decide`), catalyst counts cancelling.  This
   is exactly the invariant the earlier cubic `{7,65,133}→{13,19,29}`
   obstruction lacked: that one was a finite-component argument and dies once
   `r121` is adjoined, whereas this one survives every finite catalyst.

## Owed

Nothing.  Task closed at the two headlines plus the green root build; no
successor work was started.
