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
#print axioms CollatzMoonshot.FrontA.le_two_blocks_not_acyclicParadoxical
#print axioms CollatzMoonshot.FrontB.frontB_of_compression_le_91
