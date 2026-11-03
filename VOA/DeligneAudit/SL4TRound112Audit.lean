import VOA.DeligneAudit.SL4TRound111Audit
import VOA.DeligneAudit.SL4TMixed

/-!
# The pi-form theorem, the two-alphabet core, and the mixed ring: declaration audit

This leaf checks the declarations below together with both type-A Levi chains.

Proved endpoints:
* `pi_cellFlag_bound`: the full Newton/Garland pi-form theorem, including zero cutoffs.
  Its explicit ring inputs are nilpotence of positive power sums and a Newton tail.
* `S_pi_bound`: those ring inputs are proved for the two-alphabet ring; the bound
  is the sum of 3^intersection times 2^symmetric-difference weights.
* `MixedRing`: the five alphabets with exactly the finite (H), (F) windows, and
  elementary generator tails. Integer parameters make decremented zero lengths invalid.
* `mixedBState_invalid`: the invalid-state direction of Lemma Q for all four b-states.

Not proved here: the valid-state algebra isomorphisms of Lemma Q (the four
presentation-ideal identities for valid next tuples) and the transport of E_y and P_y
through the quotients. Neither K1-mix nor the final sl4 module bound is claimed here.

`Garland.garland` has trivial Cartan correction, so `garland_corrected_step` and
`garland_pi_coeff` are proved with the full Newton series instead.

The inventory below contains every explicit source declaration, grouped by file.
Lean-generated structure projections, recursors, and derived instances are omitted.
-/

-- SL4TPiPolynomial.lean
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_monomial
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_C_mul_X_pow
#print axioms VOA.DeligneAudit.SL4T.PiCharacteristic
#print axioms VOA.DeligneAudit.SL4T.PiCharacteristic.mul
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_truncation
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_relationIdeal
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_ideal
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_cell

-- SL4TPiNilpotent.lean
#print axioms VOA.DeligneAudit.SL4T.ideal_cell_nilpotent_mul

-- SL4TPiTheorem.lean
#print axioms VOA.DeligneAudit.SL4T.cellFlag_step_bound_any
#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound_any
#print axioms VOA.DeligneAudit.SL4T.pi_prefix_le_cellFlag
#print axioms VOA.DeligneAudit.SL4T.pi_currentSpan_eq_cellFlag
#print axioms VOA.DeligneAudit.SL4T.pi_cellFlag_bound_of_characteristic
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.pi_bound_of_characteristic
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.newtonEnd
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_rec
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_unique
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_pi
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_map
#print axioms VOA.DeligneAudit.SL4T.signed_esymm_newton
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_psum
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_psum_map
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_pi_esymm
#print axioms VOA.DeligneAudit.SL4T.garland_H_series
#print axioms VOA.DeligneAudit.SL4T.garland_E_series
#print axioms VOA.DeligneAudit.SL4T.garland_corrected_step
#print axioms VOA.DeligneAudit.SL4T.garland_corrected_iter
#print axioms VOA.DeligneAudit.SL4T.newtonSeries
#print axioms VOA.DeligneAudit.SL4T.newtonSeries_raising
#print axioms VOA.DeligneAudit.SL4T.newtonSeries_differential
#print axioms VOA.DeligneAudit.SL4T.garland_pi_coeff
#print axioms VOA.DeligneAudit.SL4T.garland_pi_one
#print axioms VOA.DeligneAudit.SL4T.piCharacteristic_of_highest
#print axioms VOA.DeligneAudit.SL4T.pi_cellFlag_bound

-- SL4TCore.lean
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_powerSumOfCoeff
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_psum_map
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_nilpotent
#print axioms VOA.DeligneAudit.SL4T.grassSeries
#print axioms VOA.DeligneAudit.SL4T.grassSeries_unit
#print axioms VOA.DeligneAudit.SL4T.grassSeries_zero
#print axioms VOA.DeligneAudit.SL4T.S_series
#print axioms VOA.DeligneAudit.SL4T.S_series_zero
#print axioms VOA.DeligneAudit.SL4T.S_series_degree
#print axioms VOA.DeligneAudit.SL4T.S_series_unit
#print axioms VOA.DeligneAudit.SL4T.S_powerSum
#print axioms VOA.DeligneAudit.SL4T.S_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.S_newtonCoeff_tail
#print axioms VOA.DeligneAudit.SL4T.S_powerSum_nilpotent
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly_coeffs
#print axioms VOA.DeligneAudit.SL4T.S_descending_newton
#print axioms VOA.DeligneAudit.SL4T.bal_sum_cells
#print axioms VOA.DeligneAudit.SL4T.S_pi_bound

-- SL4TMixed.lean
#print axioms VOA.DeligneAudit.SL4T.MixedParams
#print axioms VOA.DeligneAudit.SL4T.mixedP
#print axioms VOA.DeligneAudit.SL4T.mixedQ
#print axioms VOA.DeligneAudit.SL4T.mixedWeight
#print axioms VOA.DeligneAudit.SL4T.MixedValid
#print axioms VOA.DeligneAudit.SL4T.MixedPoly
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabet
#print axioms VOA.DeligneAudit.SL4T.mixedE
#print axioms VOA.DeligneAudit.SL4T.mixedH
#print axioms VOA.DeligneAudit.SL4T.mixedConv
#print axioms VOA.DeligneAudit.SL4T.mixedU
#print axioms VOA.DeligneAudit.SL4T.mixedV
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime
#print axioms VOA.DeligneAudit.SL4T.mixed_series_zero
#print axioms VOA.DeligneAudit.SL4T.mixedLengths
#print axioms VOA.DeligneAudit.SL4T.mixedRelations
#print axioms VOA.DeligneAudit.SL4T.mixedIdeal
#print axioms VOA.DeligneAudit.SL4T.MixedRing
#print axioms VOA.DeligneAudit.SL4T.mixedRelation_zero
#print axioms VOA.DeligneAudit.SL4T.mixedRing_invalid
#print axioms VOA.DeligneAudit.SL4T.MixedBState
#print axioms VOA.DeligneAudit.SL4T.mixedBNext
#print axioms VOA.DeligneAudit.SL4T.mixedBZeroRoots
#print axioms VOA.DeligneAudit.SL4T.mixedBPair
#print axioms VOA.DeligneAudit.SL4T.mixedBStateIdeal
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_sites
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_weight
#print axioms VOA.DeligneAudit.SL4T.mixedBBoundary
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_invalid_iff
#print axioms VOA.DeligneAudit.SL4T.mixedBPair_one_of_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedBStateIdeal_eq_top_of_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedBState_invalid
