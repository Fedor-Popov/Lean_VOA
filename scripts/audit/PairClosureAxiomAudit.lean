import VOA.Modules.PairClosure
import VOA.Examples.TripletWpPairClosure
-- §1  Modules.PairClosure: graded bookkeeping
#print axioms VOA.eq_zero_of_mem_grading_ne
#print axioms VOA.smul_grading_neg_eq_zero
#print axioms VOA.isIterProd_exists_grading
#print axioms VOA.mem_span_gradedWords
-- §2  The two levels of the weight-sum strong induction
#print axioms VOA.GenLevel
#print axioms VOA.ProdLevel
#print axioms VOA.genLevel_step
#print axioms VOA.prodLevel_step
#print axioms VOA.prodLevel_all
-- §3  ⭐⭐ The reduction: pair closure controls the whole span
#print axioms VOA.iterProdSpan_smul_closed
-- §4  ⭐ The (ω, ω) row is free in any VOA
#print axioms VOA.conformal_smul_conformal_mem_iterProdSpan
-- §5  Translation, L₀, and the skew transport
#print axioms VOA.L_neg_one_mem_iterProdSpan
#print axioms VOA.T_pow_mem_iterProdSpan
#print axioms VOA.L_zero_mem_iterProdSpan
#print axioms VOA.conformal_smul_zero_mem_iterProdSpan
#print axioms VOA.conformal_smul_one_mem_iterProdSpan
#print axioms VOA.smul_mem_iterProdSpan_of_skew
-- §6  Examples.TripletWpPairClosure: the finite-table hypothesis and the reduction chain
#print axioms VOA.LatGen.WpC2.tripGens_grading_bounded
#print axioms VOA.LatGen.WpC2.tripGens_posHomog
#print axioms VOA.LatGen.WpC2.GenPairClosedWp
#print axioms VOA.LatGen.WpC2.genPairClosedWp_of_bdd
#print axioms VOA.LatGen.WpC2.smulClosedWp_of_genPairClosed
#print axioms VOA.LatGen.WpC2.strongGenWp_of_genPairClosed
#print axioms VOA.LatGen.WpC2.adjoinGenWp_of_genPairClosed
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_of_genPairs
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_two_of_genPairs
-- §7  Pairs discharged directly
#print axioms VOA.LatGen.WpC2.pair_omegaTrip_omegaTrip
#print axioms VOA.LatGen.WpC2.pair_Etrip_Etrip
#print axioms VOA.LatGen.WpC2.pair_Ftrip_Ftrip
-- §8  The sharp residual split: tails + mixed pairs
#print axioms VOA.LatGen.WpC2.screenGens
#print axioms VOA.LatGen.WpC2.screenGens_subset_tripGens
#print axioms VOA.LatGen.WpC2.tripGens_cases
#print axioms VOA.LatGen.WpC2.screenGens_mem_grading
#print axioms VOA.LatGen.WpC2.OmegaTailWp
#print axioms VOA.LatGen.WpC2.MixedPairsWp
#print axioms VOA.LatGen.WpC2.omegaTailWp_of_bdd
#print axioms VOA.LatGen.WpC2.mixedPairsWp_of_bdd
#print axioms VOA.LatGen.WpC2.omega_row_of_tail
#print axioms VOA.LatGen.WpC2.genPairClosedWp_of_tail_mixed
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_of_tail_mixed
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_two_of_tail_mixed
-- §9  ⭐⭐⭐ Residual 1 discharged: E, H, F are Virasoro primary at every p
#print axioms VOA.LatGen.WpC2.bgOsc_vacuum
#print axioms VOA.LatGen.WpC2.LSecBg_vacuum_pos
#print axioms VOA.LatGen.WpC2.LBg_latChargeGen_pos
#print axioms VOA.LatGen.WpC2.L_latChargeGen_pos
#print axioms VOA.LatGen.WpC2.smul_omegaTrip_eq_L
#print axioms VOA.LatGen.WpC2.omegaTrip_smul_Ftrip_tail
#print axioms VOA.LatGen.WpC2.Qwp_omegaTrip
#print axioms VOA.LatGen.WpC2.omegaTrip_smul_Htrip_tail
#print axioms VOA.LatGen.WpC2.omegaTrip_smul_Etrip_tail
#print axioms VOA.LatGen.WpC2.screenGens_primary
#print axioms VOA.LatGen.WpC2.omegaTailWp_all
-- §10  ⭐⭐⭐ The end state: two residuals
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_of_mixed_AM
#print axioms VOA.LatGen.WpC2.c2Cofinite_tripletWVOA_two_of_mixed_AM
