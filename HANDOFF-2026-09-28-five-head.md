# Handoff: five-head legal pair exchanges (2026-09-28 lap)

**Checkpointed 2026-09-29.** Branch `main`, HEAD `83efd19cc3cc04d0a9933e7a2af04b6bbfe7875f`
(`83efd19 Prove both frozen five-head legal pair exchanges and the lower-family height bound`).
Treadmill stop signalled via `box done --green`; this lap's scoped objective
(`sorry-free:CollatzMoonshot/Obstructions/FiveHead.lean`) is **met**.

Working tree at checkpoint: `CollatzMoonshot/Obstructions/FiveHead.lean` and this
handoff are committed. Other modified/untracked paths (`APPROACHES.md`,
`CollatzMoonshot.lean`, `RESEARCH-2026-09-28-*.md`, `experiments/*`) belong to
other agents and were deliberately left untouched — note that the root import
`import CollatzMoonshot.Obstructions.FiveHead` in `CollatzMoonshot.lean` is
present but **still uncommitted by its owner**; the full `lake build` is green
with it in place.

## Landed

`CollatzMoonshot/Obstructions/FiveHead.lean`, imported from the root
`CollatzMoonshot.lean`. All three frozen declarations are proved, no `sorry`,
no `native_decide`:

- `observed_five_head_pair (h : ℕ)`
- `lower_five_head_pair (h : ℕ)`
- `lower_five_head_height (h : ℕ)`

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]` only.
Full `lake build` green.

## How the proof goes

Three new reusable lemmas in the same namespace:

1. `two_tstep_odd {u} (hu : u % 2 = 1) : 2 * tstep u = 3 * u + 1`
   — unfold `tstep`, discharge the even branch by `omega`.
2. `odd_ratio {u} (hu : u % 2 = 1) : (u:ℚ)/(tstep u) = 2*u/(3*u+1)`
   — cast (1) to ℚ, `tstep u > 0` by `nlinarith`, then `field_simp; nlinarith`.
   (`linarith` is *not* enough at the end: the cleared goal is
   `u * (3*u+1) = u * tstep u * 2`, which is bilinear.)
3. `five_head_pair_of_Q5 {n c d}` — the whole content, parameterised by
   positivity, oddness of `n, c, d`, and the **Nat** relation
   `Q5 : 5*c*(3*n+1)*(3*d+1) = d*(15*n+1)*(3*c+1)`.
   Availability is `le_refl` (the state *is* the input pair), the two length
   goals are `rfl`, the four label goals are `omega`, and the value equality is
   `odd_ratio` four times + `field_simp` + `nlinarith [Q5 cast to ℚ]`.

Each family then closes as
`refine five_head_pair_of_Q5 ?_ … ?_ <;> dsimp [...] <;> try omega` followed by
a single `ring` for the surviving `Q5` goal. This is exactly the kickoff's
recommended route and it avoided any large symbolic-division `norm_num`.

## What is deliberately NOT claimed

- No unit-borrowing statement. `observedC h > observedN h`, and no uniform
  legal unit containing `observedC h` is known.
- No repair theorem: `lower_five_head_pair` leaves `lowerD h` in the word, so
  the virtual-to-actual repair is untouched.
- No Collatz conclusion.

## Next attack (for whoever picks this up)

The crux ahead is availability of the second input in a *larger* state, i.e.
turning `legalPairMove` at the isolated pair into `legalPairMoves` along a real
word. `five_head_pair_of_Q5` is already stated so that only the multiset
hypothesis `[5*n, c] ≤ s` needs strengthening — generalise it from `le_refl` to
a hypothesis and the lemma becomes reusable inside a borrowing argument. That
generalisation is the single smallest next step.

## Exact next steps

1. (Owner of `CollatzMoonshot.lean`) commit the root import so `FiveHead` is
   reachable from a clean checkout.
2. Generalise `five_head_pair_of_Q5` by replacing the `le_refl _` availability
   witness with a hypothesis `hs : ([5*n, c] : Multiset ℕ) ≤ (s : Multiset ℕ)`
   and taking `s` as a parameter. Nothing else in that proof depends on
   `s = [5*n, c]`, so this is mechanical and it is what a borrowing argument
   needs.
3. Only then consider chaining exchanges via `legalPairMoves` / `applyPairMove`
   along a real word. Note `applyPairMove` uses `List.diff`, so the multiset
   bound above does not by itself give the post-state; that gap is the real
   crux, not the single-pair legality proved here.
4. Do NOT read these theorems as borrowing or repair results: `observedC h >
   observedN h` with no known uniform legal unit containing it, and
   `lower_five_head_pair` leaves `lowerD h` in the word.

`DIRECTION.md` authorizes no successor proof lap on the first-crossing route;
steps 2–3 above are exchange-algebra scaffolding, not a mechanism for the
run-count gap node, and should not be mistaken for one.
