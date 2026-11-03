import VOA.DeligneAudit.SL4TRound110Audit
import VOA.DeligneAudit.SL4TCellCount

/-!
# The two-alphabet quotient and the cell flags: declaration inventory and type-A collision audit

Scope: the two-alphabet quotient presentation, characteristic products, the four
boundary identifications, surjective Thom maps, images of ideals, the four polynomial
relations, representative formulas, and every boundary vanishing case.
The Thom pieces are represented as ideals in the appropriate quotient rings;
`thomNGPiece_eq_map` and `thomBothPiece_eq_map` identify these images explicitly.
Only the upper-bound route is used. No exact dimension, annihilator equality,
or injectivity of the three multiplication maps is asserted.

The all-parameter induction is `k1_recursive`. The list `cellCatalog` orders the
actual subset pairs by the last site, as `nn < ng < both < gn`. Its validity,
completeness, uniqueness, and union cutoffs are proved. The endpoint `k1_spanning`
exports natural-indexed generators and ideals whose restrictions to complex vector
spaces are exactly the generator prefix spans. Zero generators are allowed.

The count endpoint is `cell_count_formula`, with `u` in Finset form.
Applying these flags to the multiplicity modules and assembling the sl4 truncated Weyl
bound is not done here; neither that bound nor the D4 bound is asserted here. Polynomial coefficient extraction for `u` is not needed.

Implementation remarks: keep `Polynomial.C` qualified in the combined semantic
imports. Avoid rewriting natural-number indices through quotient-ring carriers;
use `change` or congruence for the indexed coefficient instead. `List.map_id'`
handles the literal identity lambda. The flag transport uses complex-linear spans,
not merely ideal spans, through `thomFlagIdeal_step` and `thomFlag_polynomial`.

This module imports both type-A chains through `SL4TRound110Audit`.
Every explicit declaration is inventoried below by source file.
-/

-- SL4TCharacteristic.lean
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly_coeff
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly_coeff_of_tail
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly_degree
#print axioms VOA.DeligneAudit.SL4T.descendingPoly
#print axioms VOA.DeligneAudit.SL4T.descendingPoly_eq_sum
#print axioms VOA.DeligneAudit.SL4T.descendingPoly_constant
#print axioms VOA.DeligneAudit.SL4T.grassP
#print axioms VOA.DeligneAudit.SL4T.grassPbar
#print axioms VOA.DeligneAudit.SL4T.grassP_eq_sum
#print axioms VOA.DeligneAudit.SL4T.grassPbar_eq_sum
#print axioms VOA.DeligneAudit.SL4T.grassP_constant
#print axioms VOA.DeligneAudit.SL4T.grassPbar_constant
#print axioms VOA.DeligneAudit.SL4T.grass_coefficient_product
#print axioms VOA.DeligneAudit.SL4T.grass_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.H_characteristic_product

-- SL4TTwoAlphabet.lean
#print axioms VOA.DeligneAudit.SL4T.BiSymPoly
#print axioms VOA.DeligneAudit.SL4T.alphabetIn
#print axioms VOA.DeligneAudit.SL4T.biGrassIdeal
#print axioms VOA.DeligneAudit.SL4T.BiGrass
#print axioms VOA.DeligneAudit.SL4T.S
#print axioms VOA.DeligneAudit.SL4T.biLeft
#print axioms VOA.DeligneAudit.SL4T.biRight
#print axioms VOA.DeligneAudit.SL4T.biLeft_mk
#print axioms VOA.DeligneAudit.SL4T.biRight_mk
#print axioms VOA.DeligneAudit.SL4T.leftE
#print axioms VOA.DeligneAudit.SL4T.rightE
#print axioms VOA.DeligneAudit.SL4T.leftH
#print axioms VOA.DeligneAudit.SL4T.rightH
#print axioms VOA.DeligneAudit.SL4T.leftP
#print axioms VOA.DeligneAudit.SL4T.leftPbar
#print axioms VOA.DeligneAudit.SL4T.rightP
#print axioms VOA.DeligneAudit.SL4T.rightPbar
#print axioms VOA.DeligneAudit.SL4T.leftP_eq_sum
#print axioms VOA.DeligneAudit.SL4T.rightP_eq_sum
#print axioms VOA.DeligneAudit.SL4T.leftPbar_eq_sum
#print axioms VOA.DeligneAudit.SL4T.rightPbar_eq_sum
#print axioms VOA.DeligneAudit.SL4T.leftP_constant
#print axioms VOA.DeligneAudit.SL4T.rightP_constant
#print axioms VOA.DeligneAudit.SL4T.leftPbar_constant
#print axioms VOA.DeligneAudit.SL4T.rightPbar_constant
#print axioms VOA.DeligneAudit.SL4T.left_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.right_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.left_boundary_product
#print axioms VOA.DeligneAudit.SL4T.right_boundary_product

-- SL4TTwoBoundary.lean
#print axioms VOA.DeligneAudit.SL4T.boundaryIndex
#print axioms VOA.DeligneAudit.SL4T.boundaryPoly
#print axioms VOA.DeligneAudit.SL4T.BoundaryAllowed
#print axioms VOA.DeligneAudit.SL4T.grassIdeal_boundary
#print axioms VOA.DeligneAudit.SL4T.biBoundaryRel
#print axioms VOA.DeligneAudit.SL4T.boundaryIdeal
#print axioms VOA.DeligneAudit.SL4T.boundaryIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.biGrassIdeal_boundary
#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot
#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot_mk

-- SL4TAlphabetPeel.lean
#print axioms VOA.DeligneAudit.SL4T.descendingPoly_map
#print axioms VOA.DeligneAudit.SL4T.descendingPoly_step
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_mk
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftE
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightE
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftH
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightH
#print axioms VOA.DeligneAudit.SL4T.leftE_eq_zero
#print axioms VOA.DeligneAudit.SL4T.rightE_eq_zero
#print axioms VOA.DeligneAudit.SL4T.leftP_as_descending
#print axioms VOA.DeligneAudit.SL4T.rightP_as_descending
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftP
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightP

-- SL4TThomMap.lean
#print axioms VOA.DeligneAudit.SL4T.principalMul
#print axioms VOA.DeligneAudit.SL4T.principalThom
#print axioms VOA.DeligneAudit.SL4T.principalThom_mk
#print axioms VOA.DeligneAudit.SL4T.principalThom_surjective
#print axioms VOA.DeligneAudit.SL4T.thom_kills_span_sup
#print axioms VOA.DeligneAudit.SL4T.principalThom_mul_mk
#print axioms VOA.DeligneAudit.SL4T.principalThomIdeal
#print axioms VOA.DeligneAudit.SL4T.principalThomIdeal_mono
#print axioms VOA.DeligneAudit.SL4T.principalThomIdeal_top

-- SL4TThomChain.lean
#print axioms VOA.DeligneAudit.SL4T.thomI1
#print axioms VOA.DeligneAudit.SL4T.thomI2
#print axioms VOA.DeligneAudit.SL4T.thomI3
#print axioms VOA.DeligneAudit.SL4T.thomI1_le_I2
#print axioms VOA.DeligneAudit.SL4T.thomI2_le_I3
#print axioms VOA.DeligneAudit.SL4T.thomNN_kills
#print axioms VOA.DeligneAudit.SL4T.thomNG_kills
#print axioms VOA.DeligneAudit.SL4T.thomBoth_kills
#print axioms VOA.DeligneAudit.SL4T.thomNN
#print axioms VOA.DeligneAudit.SL4T.thomNN_surjective
#print axioms VOA.DeligneAudit.SL4T.ThomNGPiece
#print axioms VOA.DeligneAudit.SL4T.thomNG
#print axioms VOA.DeligneAudit.SL4T.thomNG_surjective
#print axioms VOA.DeligneAudit.SL4T.ThomBothPiece
#print axioms VOA.DeligneAudit.SL4T.thomBoth
#print axioms VOA.DeligneAudit.SL4T.thomBoth_surjective
#print axioms VOA.DeligneAudit.SL4T.thomI3_eq_boundary
#print axioms VOA.DeligneAudit.SL4T.thomGN

-- SL4TThomPolynomial.lean
#print axioms VOA.DeligneAudit.SL4T.relationIdeal
#print axioms VOA.DeligneAudit.SL4T.relationIdeal_product
#print axioms VOA.DeligneAudit.SL4T.relationIdeal_power
#print axioms VOA.DeligneAudit.SL4T.polynomial_divX_mul
#print axioms VOA.DeligneAudit.SL4T.polynomial_nn
#print axioms VOA.DeligneAudit.SL4T.polynomial_nn_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_ng
#print axioms VOA.DeligneAudit.SL4T.polynomial_ng_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_complement_divX
#print axioms VOA.DeligneAudit.SL4T.polynomial_both
#print axioms VOA.DeligneAudit.SL4T.polynomial_both_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_gn
#print axioms VOA.DeligneAudit.SL4T.polynomial_gn_mem

-- SL4TThomRelations.lean
#print axioms VOA.DeligneAudit.SL4T.S_relationIdeal
#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_eq_map
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_eq_map
#print axioms VOA.DeligneAudit.SL4T.thom_relation_nn
#print axioms VOA.DeligneAudit.SL4T.thom_relation_ng
#print axioms VOA.DeligneAudit.SL4T.thom_relation_both
#print axioms VOA.DeligneAudit.SL4T.thom_relation_gn

-- SL4TThomEdges.lean
#print axioms VOA.DeligneAudit.SL4T.hClass_height_zero
#print axioms VOA.DeligneAudit.SL4T.leftE_zero_index
#print axioms VOA.DeligneAudit.SL4T.rightE_zero_index
#print axioms VOA.DeligneAudit.SL4T.leftH_zero_index
#print axioms VOA.DeligneAudit.SL4T.rightH_zero_index
#print axioms VOA.DeligneAudit.SL4T.eClass_eq_zero_of_width_zero
#print axioms VOA.DeligneAudit.SL4T.leftE_top
#print axioms VOA.DeligneAudit.SL4T.rightE_top
#print axioms VOA.DeligneAudit.SL4T.leftH_empty
#print axioms VOA.DeligneAudit.SL4T.rightH_empty
#print axioms VOA.DeligneAudit.SL4T.thomI1_top_left
#print axioms VOA.DeligneAudit.SL4T.thomI1_top_right
#print axioms VOA.DeligneAudit.SL4T.thomI1_zero_right
#print axioms VOA.DeligneAudit.SL4T.thomI2_zero_left
#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_top_left
#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_zero_right
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_zero_left
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_zero_right
#print axioms VOA.DeligneAudit.SL4T.thomI3_zero_left
#print axioms VOA.DeligneAudit.SL4T.thomI3_top_right

-- SL4TThomTransport.lean
#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot_symm_mk
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_surjective
#print axioms VOA.DeligneAudit.SL4T.thomNN_mk
#print axioms VOA.DeligneAudit.SL4T.thomNG_mk
#print axioms VOA.DeligneAudit.SL4T.thomBoth_mk
#print axioms VOA.DeligneAudit.SL4T.thomGN_mk
#print axioms VOA.DeligneAudit.SL4T.thomGN_surjective
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftP_divX
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightP_divX


-- SL4TSpanningFlag.lean
#print axioms VOA.DeligneAudit.SL4T.SpanningChain
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.append
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_lower
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_mul
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_mono
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_bot
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_top
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_step
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom

-- SL4TFlagPolynomial.lean
#print axioms VOA.DeligneAudit.SL4T.thomFlag_polynomial

-- SL4TFlagPieces.lean
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom_of_generators
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_eq_zero
#print axioms VOA.DeligneAudit.SL4T.flagPiece_nn
#print axioms VOA.DeligneAudit.SL4T.flagPiece_ng
#print axioms VOA.DeligneAudit.SL4T.flagPiece_both
#print axioms VOA.DeligneAudit.SL4T.flagPiece_gn

-- SL4TK1.lean
#print axioms VOA.DeligneAudit.SL4T.cellLevels
#print axioms VOA.DeligneAudit.SL4T.S_zero_algebraMap_surjective
#print axioms VOA.DeligneAudit.SL4T.S_zero_span_one
#print axioms VOA.DeligneAudit.SL4T.spanningChain_zero
#print axioms VOA.DeligneAudit.SL4T.thomI2_top_left
#print axioms VOA.DeligneAudit.SL4T.thomI3_zero_right
#print axioms VOA.DeligneAudit.SL4T.k1_recursive

-- SL4TCellCatalog.lean
#print axioms VOA.DeligneAudit.SL4T.SiteCell
#print axioms VOA.DeligneAudit.SL4T.CellValid
#print axioms VOA.DeligneAudit.SL4T.cellLift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog
#print axioms VOA.DeligneAudit.SL4T.cell_not_mem_last
#print axioms VOA.DeligneAudit.SL4T.cellValid_mono
#print axioms VOA.DeligneAudit.SL4T.cellValid_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.cellCutoff
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_levels
#print axioms VOA.DeligneAudit.SL4T.k1_catalog

-- SL4TCellEnumeration.lean
#print axioms VOA.DeligneAudit.SL4T.cellRemove
#print axioms VOA.DeligneAudit.SL4T.cellLast
#print axioms VOA.DeligneAudit.SL4T.erase_last_subset
#print axioms VOA.DeligneAudit.SL4T.cellRemove_valid
#print axioms VOA.DeligneAudit.SL4T.cellLift_remove
#print axioms VOA.DeligneAudit.SL4T.cellRemove_lift
#print axioms VOA.DeligneAudit.SL4T.cellLast_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_complete
#print axioms VOA.DeligneAudit.SL4T.mem_cellCatalog

-- SL4TFlagExport.lean
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.export
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix_zero
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix_succ
#print axioms VOA.DeligneAudit.SL4T.idealFlag_eq_prefix
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.prefix_export

-- SL4TCellUniqueness.lean
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_lift_nodup
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_nodup
#print axioms VOA.DeligneAudit.SL4T.k1_spanning

-- SL4TCellCount.lean
#print axioms VOA.DeligneAudit.SL4T.cellSet
#print axioms VOA.DeligneAudit.SL4T.mem_cellSet
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_toFinset
#print axioms VOA.DeligneAudit.SL4T.cellWeight
#print axioms VOA.DeligneAudit.SL4T.u
#print axioms VOA.DeligneAudit.SL4T.cell_card_identities
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_bounds
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_pos
#print axioms VOA.DeligneAudit.SL4T.cellWeight_closed
#print axioms VOA.DeligneAudit.SL4T.cell_count_list
#print axioms VOA.DeligneAudit.SL4T.list_sum_getD
#print axioms VOA.DeligneAudit.SL4T.cell_count_formula
