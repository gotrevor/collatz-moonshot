import CollatzMoonshot

/-!
Print the dependency ledgers for representative public-facing theorems. This file is
compiled in CI so the exact output is visible in the build log. The declarations span
trust-base-only wiring, an explicit hypothesis, a cited literature axiom, the disclosed
`sorry`, and the conditional cycle front.
-/

#print axioms CollatzMoonshot.conjecture_iff_split
#print axioms CollatzMoonshot.conjecture_iff_descent
#print axioms CollatzMoonshot.parityRigidityW1'_imp_noDivergent
#print axioms CollatzMoonshot.finite_acyclicParadoxical_imp_noDivergent
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
#print axioms CollatzMoonshot.FrontA.overcleared_remainder_ge_one
#print axioms CollatzMoonshot.FrontA.log23_effective_measure
#print axioms CollatzMoonshot.FrontA.log23_effective_measure_concrete
#print axioms CollatzMoonshot.FrontA.crossover_exp_450
#print axioms CollatzMoonshot.FrontA.sep_two_three_small_450
#print axioms CollatzMoonshot.FrontA.sep_of_linear_form_poly_threshold
#print axioms CollatzMoonshot.FrontA.sep_two_three
#print axioms CollatzMoonshot.FrontA.bd_reduction
#print axioms CollatzMoonshot.Assumed.rhin_1987_log_two_three_measure
#print axioms CollatzMoonshot.FrontA.le_two_blocks_not_acyclicParadoxical
#print axioms CollatzMoonshot.FrontB.frontB_of_compression_le_91
#print axioms CollatzMoonshot.Furstenberg.isClosed_invariant_finite_or_univ
#print axioms CollatzMoonshot.Furstenberg.dense_orbit_of_not_isOfFinAddOrder
#print axioms CollatzMoonshot.Assumed.furstenberg_topological_rigidity
