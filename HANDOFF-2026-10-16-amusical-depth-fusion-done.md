# HANDOFF 2026-10-16: amusical depth fusion (M1) done

- Branch `wip/amusical-depth-fusion`; proof commits `d56864c` (helpers), `64e50aa` (M1 closed).
  Not pushed (host pushes).
- `CollatzMoonshot/AmusicalDepthFusion.lean` is sorry-free.  `exists_depthFusion` is proved and its
  ratified statement is unchanged; `#print axioms`: propext, Classical.choice, Quot.sound.
- New declarations: `zpow_apply_eq_of_agree`, `exists_change_of_disagree` (generic perms),
  `segTop`, `le_segTop`, `card_disagree_le`.
- Run notes: `HANDOFF-amusical-depth-fusion.md`.  The disagreement bound in fact holds for every
  `X`, not just eventually; `hG` (at `C = 2k`) is used only to make the odd-rewire budget `F → ∞`.

## Next steps

- Host: push the branch and open the PR into `main`.
- If research §55 is written up, cite `exists_depthFusion` and note the every-`X` strengthening.
  The ratified statement doesn't need changing for that.
