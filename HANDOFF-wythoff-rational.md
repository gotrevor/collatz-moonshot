# HANDOFF: Wythoff rational family (`WythoffRational`, `WythoffRationalMarkov`)

Kickoff: `KICKOFF-2026-10-16-wythoff-rational.md`.  Branch `wip/wythoff-rational`.

## Status: DONE

* `CollatzMoonshot/WythoffRational.lean`: sorry-free (all 36 ratified lemmas, §1-§8).
* `CollatzMoonshot/WythoffRationalMarkov.lean`: sorry-free (all 8 ratified lemmas, Theorem M).
* Ratified statements and definitions unchanged (textual check of every ratified declaration
  against `23ff3fa`, 15 + 53 declarations).  No `native_decide`, no axioms, no heartbeat bumps,
  lines ≤ 100 characters.

## Proof routes (Markov file)

* **M1** (`fwdClass_eq`, even `p`): class counts over one forward period follow `F`; Lemma 1
  bridges `fwd_count_even/odd`, the AP lemma (`sum_ap_two`, step `p/2`) does the tail.
* **M2** (`bwdClass_eq`, even `p`): block `m = c + p y`, `W⁻¹(c + p y) = W⁻¹ c + 2Q y`
  (`wythoffInv_add`), AP lemma with step `Q` prime to `p/2` (`bwd_step`).  The one-step count
  `bwd_count` is *not* done by the kickoff's "direct route": instead `sum_window` shows the window
  `[W 0, W 0 + p)` holds exactly the values `W(2t)`, `t < q` (strict monotonicity of the even
  branch, `wythoff_two_mul_lt`), and `sum_shift` moves the window to `[0, p)`.  So
  `#{c < p : c ≡ e, W⁻¹ c even} = #{t < q : W(2t) ≡ e} = q F(0 → e)`, i.e. the detailed-balance
  identity `(p/2) B(e → 0) = q F(0 → e)`; Lemma 1 then gives `B`.
* **Joint** (`cylCount_markov`): window → `k` periods (`sum_mul_period`), block
  `x = u + 2A i` (`sum_range_mul_block`), forward part constant in `i` (`cylInd_block`), inner sum
  by `sum_ap_two` with step `A = (qR)^L` prime to `(p/2)^{L'}`, outer by `sum_fwd_cond` (parity
  split).  Count `= k · fwdClass · bwdClass`.
* **Odd `p`** (`cylCount_iid`): general periodicity `fwdItin_periodic_gen` (mod `2^{L+1}(qR)^L`)
  and `bwdItin_periodic_gen` (mod `p^L`), both valid for every `p`.  `fwdClassOdd_eq`: every
  class has size `(qR)^L` (AP lemma with step `p`, prime to `2qR`; no Lemma 1 needed).
  `bwdCountOdd_eq`: step `2Q` prime to `p^L`, one-step count `card_even_preimage` (`= q`, from
  `sum_window` with `φ = 1`).
* Instances (`cylCount_fwd/_bwd/_condIndep`, `tenThirds_dependent`) are direct corollaries of
  `cylCount_eq`; the `10/3` counts are evaluated by `norm_num` on the formula, not by `decide`.

## Notes (for anyone extending this)

* `ediv_eq_iff` (bracket characterization of `Int.ediv`) + `linarith` does all floor work.
* `rw [h]` with `h : q = …` rewrites every `q`, including inside `wythoffInv s p q`; use
  `Eq.trans ?_ h.symm` instead.
* `split_ifs` on a goal containing `wythoffInv_add`'s piece `if W⁻¹ c % 2 = 0 then q else R`
  splits that `if` first; `generalize` the piece to `Q` (with its coprimality fact) beforehand.
* `((p / 2 : ℕ) : ℤ) = (p : ℤ) / 2` holds by `rfl` after `push_cast` (`congr`).
* Box: "Too many open files" / "failed to create file" during `lake` are host-side fd exhaustion
  (system-wide `file-nr` ≈ 176k from other containers); retry after 30 s.  A cold
  `lake env lean` on a scratch file costs ~2-3 min of sys time, so batch many lemmas per check.
