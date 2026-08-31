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
#print axioms CollatzMoonshot.FrontA.le_two_blocks_not_acyclicParadoxical
#print axioms CollatzMoonshot.FrontB.frontB_of_compression_le_91
#print axioms CollatzMoonshot.Furstenberg.isClosed_invariant_finite_or_univ
#print axioms CollatzMoonshot.Furstenberg.dense_orbit_of_not_isOfFinAddOrder
#print axioms CollatzMoonshot.Assumed.furstenberg_topological_rigidity
