import VOA.Core.NonlinearZeta
import VOA.Core.NPExtension
import VOA.Core.NonlinearMR
import VOA.Core.VAPresentation
import VOA.Core.PresentationDoctrine
-- §1  Core.NonlinearZeta: the De Sole–Kac ζ-filtration (deg T = 0) and the graded toolkit
#print axioms VOA.NonlinearConformal.Ttr_mem_zfilt
#print axioms VOA.NonlinearConformal.filt_le_zfilt
#print axioms VOA.NonlinearConformal.ope_mem_zfilt
#print axioms VOA.NonlinearConformal.brk_mem_zfilt
#print axioms VOA.NonlinearConformal.opeInt_mem_zfilt
#print axioms VOA.NonlinearConformal.brk_mem_gr
#print axioms VOA.NonlinearConformal.opeInt_mem_gr
#print axioms VOA.NonlinearConformal.rel_mem_gr
#print axioms VOA.NonlinearConformal.aug_gr_pos
#print axioms VOA.NonlinearConformal.Ttr_mem_grPos
#print axioms VOA.NonlinearConformal.grProj
#print axioms VOA.NonlinearConformal.sum_grProj_of_mem_filt
#print axioms VOA.NonlinearConformal.mem_grPos_iff
-- §2  Core.NPExtension: the DK Lemma 3.2 interface and its first consequences
#print axioms VOA.NonlinearConformal.Tdiv_gv
#print axioms VOA.NonlinearConformal.NPExtension.P_eventually_zero
#print axioms VOA.NonlinearConformal.NPExtension.P_gv_eq_brk
#print axioms VOA.NonlinearConformal.NPExtension.P_bot_eq_ope
#print axioms VOA.NonlinearConformal.NPExtension.P_gv_vanish
#print axioms VOA.NonlinearConformal.NPExtension.N_mem_grPos_right
#print axioms VOA.NonlinearConformal.NPExtension.N_mem_grPos_left
-- §3  Core.NonlinearMR: the full M(R) over the interface, and its graded guard
#print axioms VOA.NonlinearConformal.relDF
#print axioms VOA.NonlinearConformal.relDF_one
#print axioms VOA.NonlinearConformal.Ttr_relDF
#print axioms VOA.NonlinearConformal.Ttr_mem_MRfullCar
#print axioms VOA.NonlinearConformal.NMIdeal.toMIdeal
#print axioms VOA.NonlinearConformal.MRfull
#print axioms VOA.NonlinearConformal.MRfull_le
#print axioms VOA.NonlinearConformal.MRbot_le_MRfull
#print axioms VOA.NonlinearConformal.relDF_mem_grPos
#print axioms VOA.NonlinearConformal.MRfull_le_grPos
#print axioms VOA.NonlinearConformal.aug_MRfull
#print axioms VOA.NonlinearConformal.vacU_ne_zero_MRfull
-- §4  Core.NonlinearMR: the linear-compatibility theorem
#print axioms VOA.NonlinearConformal.N_linSub
#print axioms VOA.NonlinearConformal.relDF_linear
#print axioms VOA.NonlinearConformal.MRfullCar_eq_MRtwoCar
#print axioms VOA.NonlinearConformal.MRfullCar_indep
#print axioms VOA.NonlinearConformal.virasoroOPE_isLinear
#print axioms VOA.NonlinearConformal.MRfull_virasoro
-- §5  Core.VAPresentation: the presentation ideal, L2 recovery, the corrected guard
#print axioms VOA.NonlinearConformal.RelIdeal_left
#print axioms VOA.NonlinearConformal.MPres
#print axioms VOA.NonlinearConformal.InRelIdeal.eq_zero
#print axioms VOA.NonlinearConformal.MPres_empty
#print axioms VOA.NonlinearConformal.MPres_empty_linear
#print axioms VOA.NonlinearConformal.RelIdeal_le_grPos
#print axioms VOA.NonlinearConformal.aug_MPres
#print axioms VOA.NonlinearConformal.vacU_ne_zero_MPres
-- §6  Core.VAPresentation: the machine-checked counterexample to the model-free guard
#print axioms VOA.NonlinearConformal.omegaRelPresentation
#print axioms VOA.NonlinearConformal.one_mem_relIdeal_omegaRel
#print axioms VOA.NonlinearConformal.aug_ne_zero_relIdeal_omegaRel
#print axioms VOA.NonlinearConformal.not_relBracketVacuumFree_omegaRel
-- §7  Core.PresentationDoctrine: evaluation, nullity certificates, THE VOA
#print axioms VOA.NonlinearConformal.evTR
#print axioms VOA.NonlinearConformal.evTR_one
#print axioms VOA.NonlinearConformal.evTR_gv
#print axioms VOA.NonlinearConformal.evTR_bot
#print axioms VOA.NonlinearConformal.mem_maxGradedIdeal_of_null
#print axioms VOA.NonlinearConformal.relIdealNull_of_isIdeal
#print axioms VOA.NonlinearConformal.relIdealNull_iff_forms_vanish
#print axioms VOA.NonlinearConformal.TheVOA
