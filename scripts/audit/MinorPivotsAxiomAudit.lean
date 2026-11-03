import VOA.Core.MinorPivots

-- §1 Congruence invariance of leading principal minors
-- (blockTriangular_leadingPrincipal and leadingPrincipal_submatrix_finSumFinEquiv
--  report strict subsets of the base axioms and are deliberately not listed;
--  their verbatim reports are recorded in HANDOFF.md.)
#print axioms VOA.FlagMinors.leadingPrincipal_mul_right_of_blockTriangular
#print axioms VOA.FlagMinors.leadingPrincipal_mul_left_of_transpose_blockTriangular
#print axioms VOA.FlagMinors.det_leadingPrincipal_eq_one_of_unitriangular
#print axioms VOA.FlagMinors.det_leadingPrincipal_unitriangular_congr

-- §2 The Jacobi quotient identity
#print axioms VOA.FlagMinors.det_leadingPrincipal_eq_mul_det_schurOfLeading

-- §3 Converse Sylvester and the layer lemmas
#print axioms VOA.FlagMinors.posDef_fin_one_of_det_pos
#print axioms VOA.FlagMinors.isHermitian_schurOfLeading
#print axioms VOA.FlagMinors.posDef_of_det_leadingPrincipal_pos
#print axioms VOA.FlagMinors.leadingPrincipal_schurOfLeading
#print axioms VOA.FlagMinors.det_schurOfLeading_eq_div
#print axioms VOA.FlagMinors.schurOfLeading_posDef_of_sign_ratios
#print axioms VOA.FlagMinors.schurOfLeading_negDef_of_sign_ratios
