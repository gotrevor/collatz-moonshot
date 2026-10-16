# HANDOFF: Wythoff rational family (`WythoffRational`, `WythoffRationalMarkov`)

Kickoff: `KICKOFF-2026-10-16-wythoff-rational.md`.  Branch `wip/wythoff-rational`.

## Status

* `CollatzMoonshot/WythoffRational.lean`: **sorry-free** (all 36 ratified lemmas, §1-§8).
* `CollatzMoonshot/WythoffRationalMarkov.lean`: in progress (Theorem M).  HEAD `29cda73`.
  * Done: counting tools (`sum_shift` A, `sum_ap` B, `sum_ap_two` C, `sum_range_two_mul_parity` D,
    `sum_mul_period` E, `sum_range_mul_block` F), `fwdItin_succ`/`bwdItin_succ`, `wythoffInv_add`,
    `cast_add_two_mul`, **`fwdItin_periodic`, `bwdItin_periodic`** (ratified), M0 params
    (`half_coprime`, `isCoprime_half_pow`, `emod_two_eq_val`, `sum_ite_const`, `sum_zmod2_add`),
    and **M1** `fwdClass_eq`: `fwdClass e w := Σ_{i<(qR)^|w|} fwdInd w (e.val + 2i)` equals
    `(qR)^|w| · wordWeight F e w` (step lemma `fwd_step`, Lemma 1 bridges `fwd_count_even/odd`).

## Next (in order)

1. **M2** backward, mirroring M1: `bwdInd`, `bwdClass e w := Σ_{i<(p/2)^|w|} bwdInd w (e.val+2i)`,
   claim `= (p/2)^|w| · wordWeight B e w`.  Step: `range (2 r B') = range (p * B')`, block
   `m = c + p y` (Tool F with `(p, B')`), `W⁻¹(c + p y) = W⁻¹ c + 2 Q_c y` (`wythoffInv_add`),
   `(c + p y) ≡ c` (`cast_add_two_mul`), then Tool C with step `Q_c` (coprime to `r^L'`) and Tool D.
   Then the inner class sum is `bwdClass g w`; but first you need the parity split of
   `Σ_{x<2B} [x ≡ e] …` (Tool D) — note M2's outer sum is over all `m < 2B` with `[m ≡ e]`, so
   state the induction on `Σ_{m<2B} [m≡e ∧ bwd m = b]` or convert with Tool D.
   One-step count needed: `#{c < p : c ≡ e ∧ W⁻¹ c ≡ g} = (p/2) · B(e → g)` — kickoff "direct
   route": `W⁻¹ c` even iff `v < q`, `v := (−cq) mod p` (`+`), resp. `1 ≤ p − (cq mod p) ≤ q`
   (`−`); `c ↦ v` bijective on `[0,p)` and parity-preserving (Tool B-style `sum_nbij`).
2. **Joint `cylCount_eq`**: window → one period by Tool E (indicator periodic mod `2AB`);
   block `x = u + 2A i` (Tool F with `(2A, B)`); fwd part fixed by `fwdItin_periodic`; inner sum
   by Tool C (step `A` coprime to `B`) = `bwdClass (u mod 2) b`; Tool D for the outer
   `Σ_{u<2A}[u≡e ∧ fwd u = f]` = `fwdClass e f`.
3. `cylCount_fwd`/`_bwd` (instances), `cylCount_condIndep` (four instances, ring in ℚ),
   `tenThirds_dependent` (six instances; counts 28+9, 70+45, 42+21).
4. `cylCount_eq_odd`: odd `p`; forward period `2^{L+1}(qR)^L` with Tool B (step `p` coprime),
   folding the parity condition into the indicator; backward period `p^{L'}` without parity
   (needs a separate odd periodicity helper), one-step `#{c<p : W⁻¹ c ≡ g} = q` or `R`.

## Notes (for the next lap)

* `ediv_eq_iff` (bracket characterization of `Int.ediv`) + `linarith` does all floor work; linarith
  normalizes polynomial products (`(m + 1 - k) * p`) as monomials, so no manual expansion needed.
* Branch lemmas `wythoff_{plus,minus}_{even,odd}` (at `2k`, `2k − 1`) and `wythoffInv_{plus,minus}_eq`
  are the API; `even_or_odd_two_mul` splits `n`.
* `omega` treats `σ x` with `σ` a `set`-local and `evenPerm j h x` as different atoms: do not
  `set σ := evenPerm …` in proofs that end in `omega`; write `evenPerm j hj1` out.
* `field_simp` normalizes compound denominators (`2qR − q − R`) and then fails to use the `≠ 0`
  hypothesis; `generalize hD : <denominator> = D at hD0 ⊢; field_simp; subst hD; ring` works.
* Box sometimes hits "Too many open files" on `lake env lean` (host-side); retry after 60 s.
