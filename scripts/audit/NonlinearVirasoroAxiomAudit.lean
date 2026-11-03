import VOA.Core.NonlinearVirasoro
import VOA.Examples.NonlinearVirasoroTransport
import VOA.Examples.NonlinearVirasoroGenuine
-- §1  Core.NonlinearVirasoro: the closed form of the Virasoro ∫₋ᵀ⁰ and of the relation
#print axioms VOA.NonlinearConformal.Lstep_iterate_closed
#print axioms VOA.NonlinearConformal.Ttr_pow_gv
#print axioms VOA.NonlinearConformal.virasoro_opeInt_l0
#print axioms VOA.NonlinearConformal.virasoro_opeInt
#print axioms VOA.NonlinearConformal.virasoro_rel
-- §2  MRtwo: De Sole–Kac's M(R) for a linear OPE datum
#print axioms VOA.NonlinearConformal.MRtwo
#print axioms VOA.NonlinearConformal.MRbot_le_MRtwo
#print axioms VOA.NonlinearConformal.MRbot_lt_MRtwo_virasoro
-- §3  Transport of IsField / Local / DCovariant, and of a whole PreVertexAlgebra
#print axioms VOA.NonlinearConformal.mapDist₂_mulBySubPow
#print axioms VOA.NonlinearConformal.conjDist_isField
#print axioms VOA.NonlinearConformal.conjDist_local
#print axioms VOA.NonlinearConformal.conjDist_cov
#print axioms VOA.NonlinearConformal.transportVA
-- §4  ⭐⭐ The refutation of GenFields over the left ideal MRbot
#print axioms VOA.NonlinearConformal.wordCoord_wbasis_mul_rel
#print axioms VOA.NonlinearConformal.wordCoord_testWord_MRbot
#print axioms VOA.NonlinearConformal.not_nonempty_genFields_MRbot_virasoro
-- §5  Exact conformal weight
#print axioms VOA.NonlinearConformal.Ttr_mem_gr
#print axioms VOA.NonlinearConformal.virasoroOPE_isConformal
#print axioms VOA.NonlinearConformal.virasoro_rel_mem_gr
-- §6  Examples.NonlinearVirasoroTransport: the comparison map and the corrected ideal
#print axioms VOA.VirModule.psiVir_Ttr
#print axioms VOA.VirModule.psiVir_rel
#print axioms VOA.VirModule.PhiVir_surjective
#print axioms VOA.VirModule.PhiVir_Ttr
#print axioms VOA.VirModule.MVir
#print axioms VOA.VirModule.MRtwo_le_MVir
#print axioms VOA.VirModule.eVir
-- §7  ⭐⭐ Deliverable A: GenFields for a nonempty generator set
#print axioms VOA.VirModule.genFieldVir_nonneg
#print axioms VOA.VirModule.fldVir_cre
#print axioms VOA.VirModule.genFieldsVir
-- §8  ⭐⭐ Deliverable B: the vertex operator map, unbundled and bundled
#print axioms VOA.VirModule.virasoro_UR_YA
#print axioms VOA.VirModule.virasoroURVA
#print axioms VOA.VirModule.virasoroURVA_Y_gv
#print axioms VOA.VirModule.virasoroURVA_vacuum
-- §9  ⭐⭐ Deliverable C: the equivalence with the Borcherds-axiomatised Virasoro VOA
#print axioms VOA.VirModule.eVir_fldVir
#print axioms VOA.VirModule.fldVir_virasoro
#print axioms VOA.VirModule.virasoro_presentation_equivalence
-- §10  The vacuity trap, settled
#print axioms VOA.VirModule.UR_MVir_nontrivial
#print axioms VOA.VirModule.sortedWordSt_linearIndependent
#print axioms VOA.VirModule.gv_linearIndependent
-- §11  ⭐⭐ Examples.NonlinearVirasoroGenuine: the straightening lemma and the genuine theorem
#print axioms VOA.VirModule.wstUw_swap
#print axioms VOA.VirModule.leftMulU_sorted_insert
#print axioms VOA.VirModule.wstUw_mem_sortedSpanU
#print axioms VOA.VirModule.sortedWstUw_span
#print axioms VOA.VirModule.MRtwo_eq_ker_PhiVir
#print axioms VOA.VirModule.eVirTwo
#print axioms VOA.VirModule.genFieldsVirTwo
#print axioms VOA.VirModule.virasoro_UR_YA_genuine
#print axioms VOA.VirModule.virasoroURVATwo
#print axioms VOA.VirModule.fldVirTwo_virasoro
#print axioms VOA.VirModule.virasoro_presentation_equivalence_genuine
#print axioms VOA.VirModule.UR_MRtwo_nontrivial
#print axioms VOA.VirModule.sortedWordSt_linearIndependent_two
