# Architect notes - 2026-08-22 🌙

*Supersedes [architect-notes-2026-08-20.md](architect-notes-2026-08-20.md) (still the
reference for Lane 1 / the drift keystone).  Front B session: four threads pulled, the map
moved into Lean.*

## What changed

Trevor's steer: **Lean deliverables of known results are not the goal on this repo** - the
currency is a pruned search tree, and a killed route is a deliverable.  Acting on that, the
prose route map is now mirrored as statements in `CollatzMoonshot/FrontB/`.

### New, axiom-clean

| Theorem | File | Content |
|---|---|---|
| `two_mul_numer_rot_false/true` | `FrontB/Words.lean` | the exact rotation identity (`propext` only) |
| `dvd_numer_rot_iff` | `FrontB/Words.lean` | **the Route-1 collapse**: integrality is rotation-invariant |
| `route1_gcdHarvest_false` | `FrontB/Threads.lean` | thread 7 refuted as a stated `Prop` |
| `cycle_neg_one/five/seventeen` | `FrontB/Negative.lean` | the three negative cycles, by `decide` |
| `exists_nontrivial_cycleZ` | `FrontB/Negative.lean` | **the falsification harness** |
| `frontB_of_compression` | `FrontB/Threads.lean` | Route 2's wiring |
| `finite_shapes_of_boundedDen` | `FrontB/Threads.lean` | **the filter as a theorem**; footprints to exactly `baker_bounded_difference` |

## Load-bearing reasoning (do not re-derive)

1. **`numer` has a clean prepend recursion** - `numer (false :: t) = 2 · numer t` and
   `numer (true :: t) = 2 · numer t + 3 ^ ones t` - because prepending shifts every one up a
   position (doubling) and a leading one is the *first* one.  Everything else follows from
   that plus the append lemmas.  Do not go back to the `Σ 3^(x−1−i) 2^(dᵢ)` form; it is
   unusable for induction.
2. **The rotation identity is exact over `ℤ`**, not just mod `den`: `2·numer (rot v)` equals
   `numer v` after an even step and `3·numer v + den v` after an odd one.  The mod-`den`
   unit-multiple law is the corollary, and *that* is what kills Route 1.
3. **The filter is now a theorem, not an opinion**: `finite_shapes_of_boundedDen` shows an
   upper bound on `|den|` leaves finitely many shapes via Baker.  No lower bound can do
   this, which is why every purely Diophantine input fails to close.
4. **`gcd(W, D)` is not a metric.**  Numerics cannot guide the compression lemma; do not
   spend more compute looking for near-misses.
5. **Word-vs-necklace normalisation bit twice in one session.**  Every count over rotations
   inflates by `k`.  Deduplicate before reading any signal.

## Owed

- ⚠️ The dictionary `NoNontrivialCycle ↔ FrontB` (Halbeisen-Hungerbühler /
  Bernstein-Lagarias) is **provable and unproved**.  Until it lands, `FrontB/` results are
  about words, not about `ℕ`.  Flagged in the file header; do not quote them otherwise.
- The disputed `abc` line in `APPROACHES.md`.
- The real circuit frontier (68? 91? 92?) - we cite these and have not verified them.

## Next

Threads 10 (Knight's trick for a second extremal family) and 17 (sum-product / additive
energy) are the two with actual mathematics in them.  Thread 13's harness now exists, so run
new lemmas against `-1`, `-5`, `-17` before believing them.
