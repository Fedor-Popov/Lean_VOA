import VOA.DeligneAudit.SL4TMultiDoubledInvariantAudit
import VOA.DeligneAudit.SL4TStratumInvariantDescent

/-!
# Deformed remainder minors, stratum initial ideals, and exact invariant counts

The deformed-minor containment is proved for every parameter and every selected
position set. The proof does not assume a rank formula, a gcd computation, or a flat family.

`deformedRemainderMinor_top` expands the determinant columnwise. Each summand is homogeneous
of the sum of its selected power degrees minus the sum of its row indices. Only the choice
of the highest power in every column has the largest degree. Its coefficient is one.
Integer degrees handle negative-degree zero terms uniformly. The scalar deformation may
be any polynomial with the specified leading coefficient and degree bound.

`coefficientMinor_eq_zero_of_common_divisor` proves that polynomials of degree below r
sharing a monic divisor of degree s have zero j-minors when r-s < j. Dividing by the common
divisor places the columns in the polynomial space of dimension r-s. Applied to actual
configuration points, the common divisor has one factor for every occupied selected site.
`fullFlag_selected_card` identifies its degree deficit with the number of selected doubles.
This proves `deformedRemainderMinor_configuration_zero`. Distinct site values are not
needed for this vanishing theorem or for the resulting initial-ideal containment.

`remainderAllIdeal_le_configurationInitialIdeal` and its top-row consequence give the
containment. Together with the scalar upper bound, they give
`fullFlagStratumIdeal_eq_pointInitialIdeal` and
`fullFlagAllStratumIdeal_eq_pointInitialIdeal`, for all 2*k <= B and distinct site values.
These statements include empty strata, the empty minor, and sizes beyond the row length.
`fullFlagStratum_finrank_eq_configurations` is the exact scalar dimension formula.

The comparison is equivariant for every finite group of position permutations preserving
the selected set. `fullFlagStratum_invariant_finrank` gives the exact dimension of the
invariants of the actual stratum quotient, as the number of configuration orbits.
`colourStratum_invariant_finrank` specializes to the actual Young subgroup and counts
the attained site colour multisets. These are invariant dimension theorems, not deductions
from a scalar dimension estimate.

Reynolds descent is also instantiated on these polynomial rings.
`fixedPolynomialQuotientEquiv` identifies fixed coefficients modulo the contracted ideal
with the fixed quotient algebra. `fullFlagStratum_contracted_finrank` gives its finite
dimension and orbit count; `colourStratum_contracted_finrank` gives the Young specialization.
The kernel here is explicitly the contraction of the actual full-flag stratum ideal.
It is *not* identified here with the four-block power-sum tail ideal in the mixed ring.

## Proved and not proved here
* The deformed-minor containment, both stratum squeezes, refined invariant orbit counts,
  and Reynolds descent to fixed polynomials modulo the contracted ideal are proved.
* Not proved: the presentation of this fixed polynomial quotient as `MixedRing q` modulo
  `middleFlagAllTailIdeal q (B - k)`, for `q` in `mixedValidBlocks 0 B`; in particular the
  identification of the contraction of the coordinate-power ideal with the four block power
  sums in every mode at least B-k. The generic Reynolds theorem does not prove this
  generator identification.
* Not proved: the matching of the attained site colour multisets with the
  multiplicity-preserving catalog `multiDoubledSiteCellCatalog`, including the
  selected-double threshold.
* Not proved: the transport of the strict graded determinantal certificate to the actual
  mixed quotient, with its ideals refined by degree and bases to construct
  `MultiDoubledSiteCoefficientFlag B k q`.
* Thus `truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags` is conditional on those
  flags, and `truncatedWeyl_sl4_multiDoubledSite_rank_le` is not defined or proved here.

This file imports `SL4TMultiDoubledInvariantAudit` and every content file of this layer.
Axiom check: no `sorryAx` occurs. All 44 explicit declarations, including 37 theorems, are
inventoried by file below; every one prints exactly `[propext, Classical.choice, Quot.sound]`.
-/

-- SL4TDeformedRemainderLeading.lean
#print axioms VOA.DeligneAudit.SL4T.monomial_integerWeight
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_eq_zero
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_nat
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_totalDegree_le
#print axioms VOA.DeligneAudit.SL4T.integerHomogeneous_component_eq_zero
#print axioms VOA.DeligneAudit.SL4T.determinant_column_sum
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_expansion
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_term_homogeneous
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_top

-- SL4TDeformedRemainderVanishing.lean
#print axioms VOA.DeligneAudit.SL4T.coefficientMinor_eq_zero_of_common_divisor
#print axioms VOA.DeligneAudit.SL4T.scalarRemainderMinor_eq_zero
#print axioms VOA.DeligneAudit.SL4T.scalarRemainder_coeff
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_evaluate

-- SL4TConfigurationRootDivisor.lean
#print axioms VOA.DeligneAudit.SL4T.fullFlag_selected_card
#print axioms VOA.DeligneAudit.SL4T.product_image_dvd_product
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_monic
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_natDegree
#print axioms VOA.DeligneAudit.SL4T.selectedAlphabetCharacteristic_evaluate
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_characteristic
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_sites
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_configuration_zero

-- SL4TStratumInitialIdeal.lean
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_integerHomogeneous
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderAllIdeal_le_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_le_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_eq_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagAllStratumIdeal_eq_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_eq_configurations

-- SL4TStratumInvariantCount.lean
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPositionRepresentation
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPointComparison_equivariant
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.colourStratum_invariant_finrank

-- SL4TStratumInvariantDescent.lean
#print axioms VOA.DeligneAudit.SL4T.stableIdeal_map_eq
#print axioms VOA.DeligneAudit.SL4T.stableIdealQuotientAlgebraAction
#print axioms VOA.DeligneAudit.SL4T.stableIdealQuotientAlgebraAction_mk
#print axioms VOA.DeligneAudit.SL4T.fixedPolynomialQuotientEquiv
#print axioms VOA.DeligneAudit.SL4T.polynomialPositionAlgebraAction
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_algebra_stable
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumFixedLinearEquiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_contracted_finrank
#print axioms VOA.DeligneAudit.SL4T.colourStratum_contracted_finrank

