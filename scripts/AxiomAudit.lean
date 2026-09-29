import CollatzMoonshot

/-!
Print the dependency ledgers for representative public-facing theorems. This file is
compiled in CI so the exact output is visible in the build log. The declarations span
trust-base-only wiring, an explicit hypothesis, a cited literature axiom, and the conditional
cycle front.  (As of 2026-09-01 no disclosed `sorry` remains; `sorryAx` must not appear.)
-/

#print axioms CollatzMoonshot.conjecture_iff_split
#print axioms CollatzMoonshot.conjecture_iff_descent
#print axioms CollatzMoonshot.parityRigidityW1'_imp_noDivergent
#print axioms CollatzMoonshot.finite_acyclicParadoxical_imp_noDivergent
#print axioms CollatzMoonshot.FrontA.trunk_slack_identity
#print axioms CollatzMoonshot.FrontA.trunk_acyclic_criterion
#print axioms CollatzMoonshot.FrontA.trunk_equality_criterion
#print axioms CollatzMoonshot.FrontA.trunk_depth_data_insufficient
#print axioms CollatzMoonshot.FrontA.trunk_climb_one_step_control
#print axioms CollatzMoonshot.FrontA.headBlock_conjugate
#print axioms CollatzMoonshot.FrontA.blockCascade_compose
#print axioms CollatzMoonshot.FrontA.blockCascade_of_identities
#print axioms CollatzMoonshot.FrontA.affineFixedPoint_dominates
#print axioms CollatzMoonshot.FrontA.blockPotential_step
#print axioms CollatzMoonshot.FrontA.blockPotential_has_unit
#print axioms CollatzMoonshot.FrontA.blockPotential_mass_bound
#print axioms CollatzMoonshot.FrontA.affineCycle_multiplier_lower
#print axioms CollatzMoonshot.FrontA.affineCycle_has_small
#print axioms CollatzMoonshot.FrontA.affineBlock_lt_square
#print axioms CollatzMoonshot.FrontA.affineBlockCycle_mass_bound
#print axioms CollatzMoonshot.FrontA.affinePath_cycle_envelope
#print axioms CollatzMoonshot.FrontA.headBlock_cascade_composition
#print axioms CollatzMoonshot.FrontA.blockComposition_length_bound
#print axioms CollatzMoonshot.FrontA.headBlock_cascade_length_bound
#print axioms CollatzMoonshot.FrontA.exists_blockWord_oddRunCount
#print axioms CollatzMoonshot.FrontA.blockWord_segment_identities
#print axioms CollatzMoonshot.FrontA.acyclicParadoxical_length_lt_of_oddRunCount
#print axioms CollatzMoonshot.FrontA.oddRunCount_boundary_controls
#print axioms CollatzMoonshot.FrontA.fixedBlockLength_nonvacuous
#print axioms CollatzMoonshot.FrontA.seventeen_pow_le_rhinLitePositive_coeff
#print axioms CollatzMoonshot.FrontA.rhinLitePositive_coeff_le_eighteen_pow
#print axioms CollatzMoonshot.FrontA.rhinLiteCriticalRoot_exhaustive_Icc
#print axioms CollatzMoonshot.FrontA.rhinLiteKernelAbs_div_pow_le
#print axioms CollatzMoonshot.FrontA.rhinLiteKernelAbs_div_pow_le_on_Icc
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomial_natDegree
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomial_centralCoeff_bounds
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenNormalized_nonneg
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenNormalized_le
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenIntegral_le
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenIntegral_pos_23
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenIntegral_pos_34
#print axioms CollatzMoonshot.FrontA.integral_monomial_div_pow
#print axioms CollatzMoonshot.FrontA.integral_poly_div_pow
#print axioms CollatzMoonshot.FrontA.integral_poly_div_pow_split
#print axioms CollatzMoonshot.FrontA.sub_natCast_dvd_lcmUpto
#print axioms CollatzMoonshot.FrontA.endpoint_pow_dvd_twelve_pow
#print axioms CollatzMoonshot.FrontA.tail_term_cleared
#print axioms CollatzMoonshot.FrontA.lcm_cleared_log_form
#print axioms CollatzMoonshot.FrontA.content_zpow_isInt
#print axioms CollatzMoonshot.FrontA.tail_term_cleared_K1
#print axioms CollatzMoonshot.FrontA.lcm_cleared_log_form_K1
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomialZ_natDegree
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomialZ_centralCoeff_bounds
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_two_log_forms
#print axioms CollatzMoonshot.FrontA.linForm_eq_log23
#print axioms CollatzMoonshot.FrontA.elim_identity
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_integrand
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_small_23
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_small_34
#print axioms CollatzMoonshot.FrontA.logForm_conditional_lower
#print axioms CollatzMoonshot.FrontA.rhinLite_forms_bounded
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_two_log_forms_K1
#print axioms CollatzMoonshot.FrontA.rhinLite_forms_bounded_K1
#print axioms CollatzMoonshot.FrontA.lcmUpto_log_le_chebyshev
#print axioms CollatzMoonshot.FrontA.lcmUpto_le_pow_eventually
#print axioms CollatzMoonshot.FrontA.rhinLite_forms_full
#print axioms CollatzMoonshot.FrontA.rhinLiteFD_spec
#print axioms CollatzMoonshot.FrontA.rhinLiteFD_eq
#print axioms CollatzMoonshot.FrontA.rhinLite_row_relations
#print axioms CollatzMoonshot.FrontA.rhinLite_formMatrix_det_cast
#print axioms CollatzMoonshot.FrontA.rhinLiteCentral_pos
#print axioms CollatzMoonshot.FrontA.rhinLiteI₁_pos
#print axioms CollatzMoonshot.FrontA.rhinLiteI₂_pos
#print axioms CollatzMoonshot.FrontA.rhinLite_integralMatrix_det_cofactor
#print axioms CollatzMoonshot.FrontA.det_dominance_of_step_bounds
#print axioms CollatzMoonshot.FrontA.rhinLiteKernelAbs_nonneg
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_step_le
#print axioms CollatzMoonshot.FrontA.rhinLite_stepFactor_le_one_sixteenth
#print axioms CollatzMoonshot.FrontA.rhinLiteI₁_step_decay16
#print axioms CollatzMoonshot.FrontA.rhinLiteI₂_step_decay16
#print axioms CollatzMoonshot.FrontA.rhinLitePositive_add
#print axioms CollatzMoonshot.FrontA.rhinLitePositive_coeffNonneg
#print axioms CollatzMoonshot.FrontA.rhinLiteCentral_coeff_link
#print axioms CollatzMoonshot.FrontA.rhinLiteCentral_step_growth16
#print axioms CollatzMoonshot.FrontA.rhinLiteKappa_pos
#print axioms CollatzMoonshot.FrontA.rhinLite_ratio_gap_of_step_bounds
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_step_le_of_bound
#print axioms CollatzMoonshot.FrontA.rhinLite_boundProduct_certificate_tight
#print axioms CollatzMoonshot.FrontA.rhinLiteKernelAbs_div_pow_le_tight
#print axioms CollatzMoonshot.FrontA.rhinLiteRootLeft_ge_three
#print axioms CollatzMoonshot.FrontA.rhinLiteKernelAbs_div_pow_le_on_Icc34
#print axioms CollatzMoonshot.FrontA.rhinLiteI₂_peak_upper
#print axioms CollatzMoonshot.FrontA.rhinLiteEven_logForm_step_ge_of_bound
#print axioms CollatzMoonshot.FrontA.interval_sq_integral_cauchySchwarz
#print axioms CollatzMoonshot.FrontA.rhinLiteI₁_logConvex
#print axioms CollatzMoonshot.FrontA.rhinLiteI₁_ratio_base
#print axioms CollatzMoonshot.FrontA.rhinLiteI₁_concentration_lower
#print axioms CollatzMoonshot.FrontA.rhinLite_ratio_gap
#print axioms CollatzMoonshot.FrontA.rhinLite_det_dominance
#print axioms CollatzMoonshot.FrontA.rhinLite_integralMatrix_det_ne_zero
#print axioms CollatzMoonshot.FrontA.rhinLite_pointwise_lower
#print axioms CollatzMoonshot.FrontA.lcmUpto_remainder_majorant
#print axioms CollatzMoonshot.FrontA.rhinLite_n_eq
#print axioms CollatzMoonshot.FrontA.rhinLite_nonvanishing_of_large
#print axioms CollatzMoonshot.FrontA.rhinLite_nonvanishing_triple
#print axioms CollatzMoonshot.FrontA.rhinLite_formMatrix_det_ne_zero
#print axioms CollatzMoonshot.FrontA.rhinLite_selection_envelope
#print axioms CollatzMoonshot.FrontA.rhinLiteLIMeasure
#print axioms CollatzMoonshot.FrontA.overcleared_remainder_ge_one
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomialZ_three_adic_content
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomialZ_two_adic_content
#print axioms CollatzMoonshot.FrontA.rhinLiteEvenPolynomialZ_content
#print axioms CollatzMoonshot.FrontA.lcmUpto_even_le_pow
#print axioms CollatzMoonshot.FrontA.rhinLiteLIMeasure_explicit
#print axioms CollatzMoonshot.FrontA.rhinLite_log23_measure
#print axioms CollatzMoonshot.FrontA.crossover_exp_436_141000
#print axioms CollatzMoonshot.FrontA.sep_two_three_finite_141000
#print axioms CollatzMoonshot.FrontA.sep_two_three_rhinLite
#print axioms CollatzMoonshot.FrontA.crossover_exp_450
#print axioms CollatzMoonshot.FrontA.sep_two_three_small_450
#print axioms CollatzMoonshot.FrontA.sep_of_linear_form_poly_threshold
#print axioms CollatzMoonshot.FrontA.sep_two_three
#print axioms CollatzMoonshot.FrontA.bd_reduction
#print axioms CollatzMoonshot.FrontA.le_two_blocks_not_acyclicParadoxical
#print axioms CollatzMoonshot.FrontA.acyclicParadoxical_seven_eight
#print axioms CollatzMoonshot.FrontA.sep_strong_492276
#print axioms CollatzMoonshot.FrontA.threeBlock_window_infeasible
#print axioms CollatzMoonshot.FrontA.threeBlock_gap_of_long
#print axioms CollatzMoonshot.FrontA.threeBlock_not_acyclicParadoxical_of_long
#print axioms CollatzMoonshot.FrontA.threeBlock_not_acyclicParadoxical_of_exceptional
#print axioms CollatzMoonshot.FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical
#print axioms CollatzMoonshot.Assumed.rozier_terracol_3_2
#print axioms CollatzMoonshot.infinite_paradoxical_of_infiniteStoppingTime
#print axioms CollatzMoonshot.FrontA.two_pow_approx_three_pow_from_above
#print axioms CollatzMoonshot.FrontA.exists_mul_box
#print axioms CollatzMoonshot.FrontA.exists_two_pow_three_pow_ratio_close
#print axioms CollatzMoonshot.FrontA.approx_from_above_of_ratio_close
#print axioms CollatzMoonshot.paradoxical_two_pow_mul
#print axioms CollatzMoonshot.orbit_numer_mono
#print axioms CollatzMoonshot.infinite_paradoxical_of_bounded_orbit
#print axioms CollatzMoonshot.const_mul_pow_lt_pow
#print axioms CollatzMoonshot.noNontrivialCycle_of_unboundedParadoxicalStarts
#print axioms CollatzMoonshot.not_unboundedParadoxicalStarts_of_bounded
#print axioms CollatzMoonshot.infinite_paradoxical_of_tstep_cycle
#print axioms CollatzMoonshot.diverges_imp_infinite_acyclicParadoxical
#print axioms CollatzMoonshot.FrontB.frontB_of_compression_le_91
#print axioms CollatzMoonshot.Furstenberg.isClosed_invariant_finite_or_univ
#print axioms CollatzMoonshot.Furstenberg.dense_orbit_of_not_isOfFinAddOrder
#print axioms CollatzMoonshot.Assumed.furstenberg_topological_rigidity

-- Cubic continuation: retain the specified smaller endpoint and exact consumer types.
-- These anchors catch changing a definition while proving a correspondingly altered claim.
open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example (s : ℕ) : cubicM s = 17959838810 + 27440626500*s := rfl

open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example (s : ℕ) : CollatzMoonshot.FrontB.tstep (cubicV s) = 16*cubicM s :=
  (cubic_peel_frontiers s).2

open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example (j : ℕ) : ∃ s : ℕ,
    Nat.ModEq (2^(j+2)) (32327709860 + 49393127700*s) 0 :=
  cubic_peel_growth_congruence j


-- Signed-flow consumers: freeze both the meanings and the unrestricted coefficient types.
open CollatzMoonshot.Obstructions.SignedFlow in
example (n : ℕ) : reachesOne n = (∃ k : ℕ, CollatzMoonshot.FrontB.tstep^[k] n = 1) := rfl

open CollatzMoonshot.Obstructions.SignedFlow in
example (c : ℕ →₀ ℤ) : boundary c = c.sum (fun u z => z •
    (Finsupp.single u (1 : ℤ) - Finsupp.single (CollatzMoonshot.FrontB.tstep u) (1 : ℤ))) := rfl

open CollatzMoonshot.Obstructions.SignedFlow in
example (n : ℕ) : (∃ c : ℕ →₀ ℤ,
    boundary c = Finsupp.single n (1 : ℤ) - Finsupp.single 1 (1 : ℤ)) ↔ reachesOne n :=
  exists_signed_flow_iff_reachesOne n

open CollatzMoonshot.Obstructions.SignedFlow in
example (n : ℕ) (k : ℤ) (hk : k ≠ 0) (c : ℕ →₀ ℤ)
    (hc : boundary c = k • (Finsupp.single n (1 : ℤ) - Finsupp.single 1 (1 : ℤ))) :
    reachesOne n := scaled_signed_flow_reachesOne n k hk c hc


-- Cubic carry consumers: preserve the neighbor and actual unbounded-gap claim.
open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example (s : ℕ) : neighbor s = 32 * CollatzMoonshot.FrontB.tstep (cubicQ1 s) := rfl

open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example (s : ℕ) : CollatzMoonshot.FrontB.tstep^[3] (cubicN s) + 14 =
    32 * CollatzMoonshot.FrontB.tstep (cubicQ1 s) := cubic_carry_third s

open CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
example : ∀ B : ℕ, ∃ s : ℕ,
    CollatzMoonshot.FrontB.tstep^[2] (neighbor s) + B <
      CollatzMoonshot.FrontB.tstep^[5] (cubicN s) := cubic_carry_gap_unbounded
