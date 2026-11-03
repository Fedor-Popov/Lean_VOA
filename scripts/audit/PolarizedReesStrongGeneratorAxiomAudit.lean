import VOA.Examples.PolarizedReesStrongGenerator

-- §1 Interface structures (Rees Virasoro relations (32); comparison Ψ of (33),
--    items 1–4 of section 6.1)
-- (ReesVirasoroData, ComparisonData, and leadingPrincipal_diagonal report the
--  strict subset [propext, Quot.sound] of the base axioms and are excluded
--  from the enforced probe per precedent; recorded in HANDOFF.md.)

-- §2 The finite-matrix payload of the bi-Rees lemma (section 5)
#print axioms VOA.PolarizedRees.signDiag
#print axioms VOA.PolarizedRees.cumulativeDegree
#print axioms VOA.PolarizedRees.MinorPayload
#print axioms VOA.PolarizedRees.det_leadingPrincipal_signDiag

-- §3 Main theorem and its compositions with Core.MinorPivots / Core.FlagMinors
#print axioms VOA.PolarizedRees.MinorPayload.sign_det_leadingPrincipal_pos
#print axioms VOA.PolarizedRees.MinorPayload.det_leadingPrincipal_ne_zero
#print axioms VOA.PolarizedRees.MinorPayload.flag_restrict_nondegenerate
#print axioms VOA.PolarizedRees.schurOfLeading_posDef_of_ratios_of_pivot_ne_zero
#print axioms VOA.PolarizedRees.schurOfLeading_negDef_of_ratios_of_pivot_ne_zero
#print axioms VOA.PolarizedRees.MinorPayload.ratio_sign
#print axioms VOA.PolarizedRees.MinorPayload.layer_schur_posDef_of_even
#print axioms VOA.PolarizedRees.MinorPayload.layer_schur_negDef_of_odd
#print axioms VOA.PolarizedRees.MinorPayload.layer_schur_definite

-- §4 The bundled strong-generator package
#print axioms VOA.PolarizedRees.StrongGeneratorPackage
#print axioms VOA.PolarizedRees.StrongGeneratorPackage.sign_det_leadingPrincipal_pos
#print axioms VOA.PolarizedRees.StrongGeneratorPackage.layer_schur_definite

-- §5 Non-vacuity witnesses
#print axioms VOA.PolarizedRees.wittEnd
#print axioms VOA.PolarizedRees.wittEnd_apply
#print axioms VOA.PolarizedRees.wittRees
#print axioms VOA.PolarizedRees.wittEnd_ne_zero
#print axioms VOA.PolarizedRees.wittRees_L_noncommutative
#print axioms VOA.PolarizedRees.wittComparison
#print axioms VOA.PolarizedRees.toyPayload
#print axioms VOA.PolarizedRees.toyPackage
#print axioms VOA.PolarizedRees.toyPayload_minor_two_neg
#print axioms VOA.PolarizedRees.toyPayload_layer_one_negDef
