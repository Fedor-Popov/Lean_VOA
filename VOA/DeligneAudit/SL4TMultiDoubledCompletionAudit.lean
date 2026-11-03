import VOA.DeligneAudit.SL4TMultiDoubledClosureAudit
import VOA.DeligneAudit.SL4TMultiDoubledCompletion

/-!
# Completion of the multi-doubled-site rank bound: declaration and axiom audit

The multi-doubled-site rank bound holds with no hypotheses beyond `2 * k ≤ B`:

    truncatedWeyl_sl4_multiDoubledSite_rank_le (B k : ℕ) (hk : 2 * k ≤ B) :
      FiniteDimensional ℂ (TruncatedLabelModule 0 B 0 (B - k)) ∧
        Module.finrank ℂ (TruncatedLabelModule 0 B 0 (B - k)) ≤ 20 ^ k * 6 ^ (B - 2 * k)

Its only hypothesis is `2 * k ≤ B`. For `k ≥ 1` it discharges the flag hypothesis of
`truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags` through
`multiDoubledSiteCoefficientFlag_valid`, which constructs `MultiDoubledSiteCoefficientFlag B k q`
for every `q ∈ mixedValidBlocks 0 B`; for `k = 0` it uses the local bound.

Route, by file:
* `SL4TLineFlagRefinement`: line flags from a subspace to the whole coefficient algebra. A
  layer `U ≤ U'` whose positive power sums map `U'` into `U` contributes `dim U' - dim U` lines
  of one level; a chain of ideals refined by homogeneous degree gives a flag of cost
  `Σ_j (dim G_j - dim G_{j+1}) · cost(L_j)` (`lineFlagFrom_gradedStrata`). Flags push forward
  along surjective algebra maps (`lineFlagFrom_map`), and in a mixed coefficient quotient they
  are `MixedQuotientSubspaceFlag` (`mixedQuotientSubspaceFlag_of_lineFlag`).
* `SL4TColourStratumGrading`: the source ring `ColourTruncatedFlagRing` is the Young-invariant
  polynomial algebra modulo the contraction of the full-flag truncation ideal; its strata are
  the contracted top-minor ideals of the selected colours. Proved: the minors vanish beyond the
  alphabet length and descend by Laplace expansion; every stratum is spanned by averaged
  homogeneous components in degrees `0 .. B * N`; above `B * N` homogeneous invariants lie in
  the coordinate-power ideal; each stratum quotient has the attained colour-multiplicity count
  as dimension (from `colourStratum_contracted_finrank`).
* `SL4TColourStratumCertificate`: `alphabetCharacteristic_eq_newton` (the characteristic
  polynomial of any alphabet is the Newton polynomial of its power sums); coefficientwise
  averaging is linear over invariant coefficients, so membership in `(P, X ^ N)` descends to
  invariant coefficients; `colourTruncatedStratum_certificate` is the graded top-row Cramer
  certificate in the invariant ring, with corrections in the stratum and in larger degrees.
* `SL4TMiddleFlagStratumTransport`: the stratum line flag (`colourTruncatedFlagRing_lineFlag`)
  and its transport by `middleFlagTruncatedEvaluation`, a surjection onto
  `MixedRing q ⧸ middleFlagAllTailIdeal q N` sending the selected power sums to
  `mixedPowerSum q` and the Newton polynomial to `mixedCharacteristic q`
  (`multiDoubledSiteCoefficientFlag_of_stratumCost`). Injectivity is neither proved nor used.
* `SL4TStratumOrbitCount`, `SL4TSiteWordCatalog`, `SL4TMultiDoubledCompletion`: the weighted
  stratum count is a sum over attained site colour multiplicities; every catalog sum is a sum
  over site words; an attained multiplicity function decodes injectively to a word of the same
  colour content whose triples are its selected doubled sites. Hence
  `middleFlag_stratumCost_le_blockBound`: the flag cost is at most
  `multiDoubledSiteBlockBound B k q`. Only this upper bound is proved; equality of the stratum
  dimensions with word counts is not claimed here.

Axiom check: no `sorryAx` occurs. All 128 explicit declarations of the seven content files of
this layer are printed below: 115 depend on exactly `[propext, Classical.choice, Quot.sound]`,
the rest on a subset (seven on `[propext, Quot.sound]`, two on `[propext]`, four on none).
No `sorry`, `admit`, `native_decide` or project axiom is used.
-/

-- SL4TLineFlagRefinement.lean
#print axioms VOA.DeligneAudit.SL4T.lineLevelCost
#print axioms VOA.DeligneAudit.SL4T.LineFlagFrom
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_top
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_mono
#print axioms VOA.DeligneAudit.SL4T.consSequence
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix_consSequence
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_prepend
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_layer
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_layers
#print axioms VOA.DeligneAudit.SL4T.gradedStratumLayer
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_gradedStrata
#print axioms VOA.DeligneAudit.SL4T.lineFlagFrom_map
#print axioms VOA.DeligneAudit.SL4T.mixedQuotientSubspaceFlag_of_lineFlag

-- SL4TColourStratumGrading.lean
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_eq_zero_of_length_le
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_eq_bot_of_length_lt
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_succ_le
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_antitone_step
#print axioms VOA.DeligneAudit.SL4T.isWeightedHomogeneous_rename_one
#print axioms VOA.DeligneAudit.SL4T.weightedComponent_sum_image_support
#print axioms VOA.DeligneAudit.SL4T.weight_one_nonneg
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_component_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_of_high_degree
#print axioms VOA.DeligneAudit.SL4T.colourStratumPermutationFintype
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_mem_stable
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_fixed
#print axioms VOA.DeligneAudit.SL4T.colourHomogeneousPiece
#print axioms VOA.DeligneAudit.SL4T.mem_colourHomogeneousPiece
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_homogeneous
#print axioms VOA.DeligneAudit.SL4T.colourHomogeneousPiece_mul
#print axioms VOA.DeligneAudit.SL4T.colourPolynomial_homogeneous_decomposition
#print axioms VOA.DeligneAudit.SL4T.colourTruncationIdeal
#print axioms VOA.DeligneAudit.SL4T.ColourTruncatedFlagRing
#print axioms VOA.DeligneAudit.SL4T.colourStratumContraction
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedDegree
#print axioms VOA.DeligneAudit.SL4T.selectedColourPowerSum
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedPowerSum
#print axioms VOA.DeligneAudit.SL4T.selectedColourPowerSum_val
#print axioms VOA.DeligneAudit.SL4T.selectedColourPowerSum_homogeneous
#print axioms VOA.DeligneAudit.SL4T.colourTruncationIdeal_le_contraction
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_mem_iff
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedDegree_powerSum_mul
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedDegree_eq_bot
#print axioms VOA.DeligneAudit.SL4T.fullFlagColourStratumIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_homogeneous
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_zero
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_eq_bot
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_succ_le
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratumQuotientEquiv
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_quotient_finrank
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedFlagRing_finite

-- SL4TColourStratumCertificate.lean
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_eq_newton
#print axioms VOA.DeligneAudit.SL4T.colourCertificatePermutationFintype
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_coeff
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_add
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_sub
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_mul_map
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_map
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_monomial
#print axioms VOA.DeligneAudit.SL4T.colourAverageCoefficients_mem_span
#print axioms VOA.DeligneAudit.SL4T.selectedRemainderTopIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.selectedStratumIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_topIdeal_component_mem
#print axioms VOA.DeligneAudit.SL4T.selectedColourCharacteristic_map
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedStratum_certificate

-- SL4TMiddleFlagStratumTransport.lean
#print axioms VOA.DeligneAudit.SL4T.colourStratumCount
#print axioms VOA.DeligneAudit.SL4T.colourStratumCost
#print axioms VOA.DeligneAudit.SL4T.ideal_restrictScalars_finrank
#print axioms VOA.DeligneAudit.SL4T.colourTruncatedFlagRing_lineFlag
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_eq_middleFlagTail
#print axioms VOA.DeligneAudit.SL4T.middleFlagTruncatedEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagTruncatedEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagTruncatedEvaluation_powerSum
#print axioms VOA.DeligneAudit.SL4T.middleFlagSelected_card
#print axioms VOA.DeligneAudit.SL4T.middleFlagTruncatedEvaluation_characteristic
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCoefficientFlag_of_stratumCost

-- SL4TStratumOrbitCount.lean
#print axioms VOA.DeligneAudit.SL4T.selectedDoubleSiteCount
#print axioms VOA.DeligneAudit.SL4T.selectedDoubleSiteCount_multiplicity
#print axioms VOA.DeligneAudit.SL4T.attainedColourMultiplicities
#print axioms VOA.DeligneAudit.SL4T.mem_attainedColourMultiplicities
#print axioms VOA.DeligneAudit.SL4T.colourStratumCount_eq_card
#print axioms VOA.DeligneAudit.SL4T.colourStratumCost_le_attained

-- SL4TSiteWordCatalog.lean
#print axioms VOA.DeligneAudit.SL4T.list_map_flatMap_sum
#print axioms VOA.DeligneAudit.SL4T.mixedBStateColour
#print axioms VOA.DeligneAudit.SL4T.mixedBStateColour_order
#print axioms VOA.DeligneAudit.SL4T.mixedBOrder_stateColour
#print axioms VOA.DeligneAudit.SL4T.simpleSiteColourCount
#print axioms VOA.DeligneAudit.SL4T.doubledSiteColourCount
#print axioms VOA.DeligneAudit.SL4T.SiteWord
#print axioms VOA.DeligneAudit.SL4T.simpleSiteWordData
#print axioms VOA.DeligneAudit.SL4T.siteWordData
#print axioms VOA.DeligneAudit.SL4T.sum_tuple_succ
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_zero_map_sum
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_map_sum
#print axioms VOA.DeligneAudit.SL4T.siteWordContent
#print axioms VOA.DeligneAudit.SL4T.siteWordTriples
#print axioms VOA.DeligneAudit.SL4T.mixedParamsOfContent
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious_ofContent
#print axioms VOA.DeligneAudit.SL4T.mixedParamsOfContent_injective
#print axioms VOA.DeligneAudit.SL4T.simpleSiteWordData_params
#print axioms VOA.DeligneAudit.SL4T.simpleSiteWordData_triples
#print axioms VOA.DeligneAudit.SL4T.siteWordData_params
#print axioms VOA.DeligneAudit.SL4T.siteWordData_triples
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_map_sum
#print axioms VOA.DeligneAudit.SL4T.exists_doubledSiteColourCount
#print axioms VOA.DeligneAudit.SL4T.exists_simpleSiteColourCount
#print axioms VOA.DeligneAudit.SL4T.doubledSiteTripleCount_eq
#print axioms VOA.DeligneAudit.SL4T.doubledSiteIndexOf
#print axioms VOA.DeligneAudit.SL4T.simpleSiteIndexOf
#print axioms VOA.DeligneAudit.SL4T.doubledSiteIndexOf_spec
#print axioms VOA.DeligneAudit.SL4T.simpleSiteIndexOf_spec
#print axioms VOA.DeligneAudit.SL4T.siteWordOf
#print axioms VOA.DeligneAudit.SL4T.sum_sites_split

-- SL4TMultiDoubledCompletion.lean
#print axioms VOA.DeligneAudit.SL4T.attainedColourMultiplicities_site_total
#print axioms VOA.DeligneAudit.SL4T.attainedColourMultiplicities_colour_total
#print axioms VOA.DeligneAudit.SL4T.not_mem_characteristic_iff
#print axioms VOA.DeligneAudit.SL4T.siteWordOf_doubled
#print axioms VOA.DeligneAudit.SL4T.siteWordOf_simple
#print axioms VOA.DeligneAudit.SL4T.siteWordOf_injOn
#print axioms VOA.DeligneAudit.SL4T.siteWordOf_content
#print axioms VOA.DeligneAudit.SL4T.siteWordOf_triples
#print axioms VOA.DeligneAudit.SL4T.attained_sum_le_wordSum
#print axioms VOA.DeligneAudit.SL4T.middleFlagPosition_colourCount
#print axioms VOA.DeligneAudit.SL4T.mixedParamsOfContent_middleFlagLength
#print axioms VOA.DeligneAudit.SL4T.middleFlag_stratumCost_le_blockBound
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCoefficientFlag_valid
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_multiDoubledSite_rank_le
