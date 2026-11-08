import VOA.Moonshine.MoonshineCNAudit17
import VOA.Moonshine.MoonshineCNGammaZeroAudit
import VOA.Moonshine.MoonshineCNGenusZeroAudit3
import VOA.Moonshine.MoonshineCNReplicationFormal
import VOA.Moonshine.MoonshineCNReplicationAnalytic
import VOA.Moonshine.MoonshineCNTwistedCombinatorics
import VOA.Moonshine.MoonshineCNTwistedTransfer
import VOA.Moonshine.MoonshineCNTwistedPBW
import VOA.Moonshine.MoonshineCNTwistedBases
import VOA.Moonshine.MoonshineCNTwistedCharacters
import VOA.Moonshine.MoonshineCNTwistedDenominator

/-! Kernel dependency audit for the twisted denominator identities and complete replicability:
formal replication from the twisted denominator identity (Faber polynomials, logarithm-free), the
analytic replication formula for finite-order McKay–Thompson series, the character identities of
graded words and multisets, the transfer of weighted counts along diagonal intertwiners, PBW and
word coordinates, homogeneous eigenbases and torus symmetries of the positive part, the twisted
denominator identity for Borcherds data, and its Monster instance with complete replicability and
the Conway–Norton conjecture conditional on generation by simple root spaces and finite order. -/

#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_add
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_sub
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_neg
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_one
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_X
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_mul
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_map
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_rescale
#print axioms VOA.Moonshine.ConwayNorton.twistedUnitSeries
#print axioms VOA.Moonshine.ConwayNorton.twistedPowerSum
#print axioms VOA.Moonshine.ConwayNorton.TwistedDenominatorIdentity
#print axioms VOA.Moonshine.ConwayNorton.positiveGeometricSeries
#print axioms VOA.Moonshine.ConwayNorton.one_sub_X_mul_positiveGeometricSeries
#print axioms VOA.Moonshine.ConwayNorton.coeff_coeff_twistedPowerSum_of_le
#print axioms VOA.Moonshine.ConwayNorton.replicationCoeff
#print axioms VOA.Moonshine.ConwayNorton.coeff_coeff_twistedPowerSum_add
#print axioms VOA.Moonshine.ConwayNorton.faberGenerating
#print axioms VOA.Moonshine.ConwayNorton.constantCoeff_faberGenerating
#print axioms VOA.Moonshine.ConwayNorton.faberLogDerivSeries
#print axioms VOA.Moonshine.ConwayNorton.faberGenerating_mul_faberLogDerivSeries
#print axioms VOA.Moonshine.ConwayNorton.faberEvaluation
#print axioms VOA.Moonshine.ConwayNorton.coeff_faberEvaluation
#print axioms VOA.Moonshine.ConwayNorton.faberEvaluation_eulerDeriv
#print axioms VOA.Moonshine.ConwayNorton.laurentEmbedding
#print axioms VOA.Moonshine.ConwayNorton.laurentEmbedding_injective
#print axioms VOA.Moonshine.ConwayNorton.coeff_one_sub_X_mul_one_sub_twistedUnitSeries
#print axioms VOA.Moonshine.ConwayNorton.algebraMap_laurentSeries
#print axioms VOA.Moonshine.ConwayNorton.faberEvaluation_faberGenerating
#print axioms VOA.Moonshine.ConwayNorton.twistedFaberRecursion
#print axioms VOA.Moonshine.ConwayNorton.faberEvaluation_faberLogDerivSeries
#print axioms VOA.Moonshine.ConwayNorton.faberLogDerivSeries_coeff_eval
#print axioms VOA.Moonshine.ConwayNorton.faberLogDerivSeries_coeff_eq_faberPoly
#print axioms VOA.Moonshine.ConwayNorton.faberPoly_replication
#print axioms VOA.Moonshine.ConwayNorton.homogenizedEval
#print axioms VOA.Moonshine.ConwayNorton.ofPowerSeries_homogenizedEval
#print axioms VOA.Moonshine.ConwayNorton.homogenizedEval_faberPoly
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.add
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.mul
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.const
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.one
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.zero
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.X
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.pow
#print axioms VOA.Moonshine.ConwayNorton.HasAbsEvalAt.sum
#print axioms VOA.Moonshine.ConwayNorton.poleQSeriesFun
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFun_eq_poleQSeriesFun
#print axioms VOA.Moonshine.ConwayNorton.qPar_ne_zero
#print axioms VOA.Moonshine.ConwayNorton.isJDominated_mckayThompson
#print axioms VOA.Moonshine.ConwayNorton.summable_norm_coeff_mul_qPar
#print axioms VOA.Moonshine.ConwayNorton.hasAbsEvalAt_qSeriesUnit
#print axioms VOA.Moonshine.ConwayNorton.hasAbsEvalAt_homogenizedEval
#print axioms VOA.Moonshine.ConwayNorton.qPar_heckePoint_eq_exp_mul
#print axioms VOA.Moonshine.ConwayNorton.exp_heckeShift_pow
#print axioms VOA.Moonshine.ConwayNorton.sum_range_exp_pow
#print axioms VOA.Moonshine.ConwayNorton.hasSum_heckeCosetSum_regular
#print axioms VOA.Moonshine.ConwayNorton.sum_inv_qPar_heckePoint
#print axioms VOA.Moonshine.ConwayNorton.hasSum_heckeSum
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFamily
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFamily_one
#print axioms VOA.Moonshine.ConwayNorton.hasSum_faberPoly_eval
#print axioms VOA.Moonshine.ConwayNorton.faberPoly_eval_mckayThompsonFun
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicableOfFinOrder_of_twistedDenominator
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicable_of_twistedDenominator
#print axioms VOA.Moonshine.ConwayNorton.bigradedSeries
#print axioms VOA.Moonshine.ConwayNorton.bigradedConv
#print axioms VOA.Moonshine.ConwayNorton.bigradedSeries_ext
#print axioms VOA.Moonshine.ConwayNorton.bigradedSeries_mul
#print axioms VOA.Moonshine.ConwayNorton.one_eq_bigradedSeries
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_bigradedSeries
#print axioms VOA.Moonshine.ConwayNorton.bigradedConv_congr
#print axioms VOA.Moonshine.ConwayNorton.bigradedConv_comm
#print axioms VOA.Moonshine.ConwayNorton.sum_antidiagonal_ite_fst
#print axioms VOA.Moonshine.ConwayNorton.sum_shift_eq_bigradedConv
#print axioms VOA.Moonshine.ConwayNorton.prod_add_tsub_cancel_left
#print axioms VOA.Moonshine.ConwayNorton.prod_add_tsub_cancel_right
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.finite_le
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.lowerLetters
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.mem_lowerLetters
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.listDeg
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.finite_wordFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.wordFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.mem_wordFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.wordCount
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.letterCount
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.wordCount_eq
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetDeg
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.card_le_msetDeg
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.finite_msetFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.mem_msetFiber
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetCount
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.powerSumCount
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetDeg_le_of_le
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.sum_msetFiber_count_ge
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.firstDegree_mul_msetCount_eq
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.wordSeries
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.letterSeries
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetSeries
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.powerSumSeries
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.wordSeries_mul_one_sub_letterSeries
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.eulerDeriv_msetSeries
#print axioms VOA.Moonshine.ConwayNorton.eulerDeriv_eq_of_inverse
#print axioms VOA.Moonshine.ConwayNorton.finsuppDiag
#print axioms VOA.Moonshine.ConwayNorton.finsuppDiag_single
#print axioms VOA.Moonshine.ConwayNorton.finsuppDiag_apply
#print axioms VOA.Moonshine.ConwayNorton.apply_single_eq_zero_of_diag
#print axioms VOA.Moonshine.ConwayNorton.card_le_of_injective_support
#print axioms VOA.Moonshine.ConwayNorton.card_fiber_eq_of_diag_equiv
#print axioms VOA.Moonshine.ConwayNorton.sum_eq_sum_of_diag_equiv
#print axioms VOA.Moonshine.ConwayNorton.list_prod_map_smul
#print axioms VOA.Moonshine.ConwayNorton.finsuppDiag_domLCongr
#print axioms VOA.Moonshine.ConwayNorton.topBasis
#print axioms VOA.Moonshine.ConwayNorton.topBasis_apply
#print axioms VOA.Moonshine.ConwayNorton.bot_isCompl_top
#print axioms VOA.Moonshine.ConwayNorton.zeroBottomRep
#print axioms VOA.Moonshine.ConwayNorton.balancing_bot_eq_bot
#print axioms VOA.Moonshine.ConwayNorton.envelopingInducedEquiv
#print axioms VOA.Moonshine.ConwayNorton.envelopingInducedEquiv_apply
#print axioms VOA.Moonshine.ConwayNorton.pbwCoordinates
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWord_bot
#print axioms VOA.Moonshine.ConwayNorton.pbwCoordinates_sorted
#print axioms VOA.Moonshine.ConwayNorton.pbwCoordinates_symm_single
#print axioms VOA.Moonshine.ConwayNorton.pbwCoordinates_envelopingMap
#print axioms VOA.Moonshine.ConwayNorton.tensorAlgebra_basis_apply
#print axioms VOA.Moonshine.ConwayNorton.tensorAlgebra_repr_lift_diag
#print axioms VOA.Moonshine.ConwayNorton.wordPBWEquiv
#print axioms VOA.Moonshine.ConwayNorton.wordPBWEquiv_diag
#print axioms VOA.Moonshine.ConwayNorton.exists_eigenbasis_of_pow_eq_one
#print axioms VOA.Moonshine.ConwayNorton.trace_pow_eq_sum_of_eigenbasis
#print axioms VOA.Moonshine.ConwayNorton.isInternal_comap_subtype
#print axioms VOA.Moonshine.ConwayNorton.borcherdsStringIndex_decidableEq
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightDecompose
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightDecompose_of_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightTorus
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightTorus_of_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.mem_weightSpace_iSup
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightTorus_lie
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightTorus_mem_weightSpan
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTorus
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTorus_coe
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightTorus_genSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveWeight_isInternal
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveBasis_coe
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveBasis_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorStrings_isInternal
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBasis_coe
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBasis_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTorus_positiveBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTorus_generatorBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTorus_generator_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightAction
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightAction_pow
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartAction_positiveBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartAction_generatorBasis
#print axioms VOA.Moonshine.ConwayNorton.borcherdsHeightDegree
#print axioms VOA.Moonshine.ConwayNorton.borcherdsHeightDegree_injOn
#print axioms VOA.Moonshine.ConwayNorton.borcherdsStringDegree_cone
#print axioms VOA.Moonshine.ConwayNorton.sigmaGradedLetters
#print axioms VOA.Moonshine.ConwayNorton.sum_sigma_fiber
#print axioms VOA.Moonshine.ConwayNorton.heightCharFirst
#print axioms VOA.Moonshine.ConwayNorton.heightCharTotal
#print axioms VOA.Moonshine.ConwayNorton.heightCharFirst_add
#print axioms VOA.Moonshine.ConwayNorton.heightCharTotal_add
#print axioms VOA.Moonshine.ConwayNorton.heightCharFirst_of_cone
#print axioms VOA.Moonshine.ConwayNorton.heightCharTotal_of_cone
#print axioms VOA.Moonshine.ConwayNorton.list_prod_two_pow
#print axioms VOA.Moonshine.ConwayNorton.multiset_prod_two_pow
#print axioms VOA.Moonshine.ConwayNorton.two_pow_inj
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.listDeg_fst
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.listDeg_snd
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetDeg_fst
#print axioms VOA.Moonshine.ConwayNorton.GradedLetters.msetDeg_snd
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveLetters
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorLetters
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorLetters_wordCount_eq
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.twistedDenominatorIdentity_of_eigenbasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightAction_one
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.twistedDenominatorIdentity_of_finOrder
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_weightAction_trace
#print axioms VOA.Moonshine.ConwayNorton.twistedDenominatorIdentity_of_simpleRootGeneration
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicableOfFinOrder_of_simpleRootGeneration
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicable_of_simpleRootGeneration
#print axioms VOA.Moonshine.ConwayNorton.conwayNorton_of_simpleRootGeneration

open VOA.Moonshine.ConwayNorton VOA.Moonshine.AutMonster in
example (hgen : MonsterLieSimpleRootGeneration) : CompletelyReplicableOfFinOrder :=
  completelyReplicableOfFinOrder_of_simpleRootGeneration hgen

open VOA.Moonshine.ConwayNorton VOA.Moonshine.AutMonster in
example (hgen : MonsterLieSimpleRootGeneration) (hfin : ∀ g : AutVnat, IsOfFinOrder g) :
    ConwayNortonConjecture :=
  conwayNorton_of_simpleRootGeneration hgen hfin

#check @VOA.Moonshine.ConwayNorton.twistedDenominatorIdentity_of_simpleRootGeneration
#check @VOA.Moonshine.ConwayNorton.completelyReplicable_of_simpleRootGeneration
#check @VOA.Moonshine.ConwayNorton.conwayNorton_of_simpleRootGeneration
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.twistedDenominatorIdentity_of_finOrder
#check @VOA.Moonshine.ConwayNorton.completelyReplicableOfFinOrder_of_twistedDenominator
