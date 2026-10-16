# HANDOFF: amusical depth fusion (M1, research §55)

Kickoff: `KICKOFF-2026-10-15-amusical-depth-fusion.md`.  Target: the `sorry` in
`CollatzMoonshot/AmusicalDepthFusion.lean` (`exists_depthFusion`).

## Log

- Step 1 proved, generic over any two perms: `zpow_apply_eq_of_agree`,
  `exists_change_of_disagree` (disagreement at depth `d` ⇒ change of `τ` at some `σ^i n`, `|i| ≤ d`).
- Step 2 proved: `segTop D X` (max of `U^i n`, `n < X`, `|i| ≤ D*`), `le_segTop` (`X ≤ segTop + 1`),
  `card_disagree_le` (union bound over `i ∈ Icc (-D*) D*` of images of the change set below
  `segTop + 1`; no injectivity argument needed).
- Step 3 proved, closing `exists_depthFusion` (ratified statement unchanged; `#print axioms`:
  propext, Classical.choice, Quot.sound).  Budget: `F N := sInf (q '' {X | N ≤ segTop D X + 1})`, `q X := G X / (2 D* + 1)`.
  Then `F (segTop X + 1) ≤ q X` for every `X` (no eventuality needed); `hG` only feeds `F → ∞`.

## Status

Done.  `exists_depthFusion` is proved.  Note for the write-up: the final count holds for *every*
`X`, not just eventually, since `F (segTop X + 1) ≤ q X` by construction; and `hG` is used only
with `C = 2k`, to make `F → ∞`.
