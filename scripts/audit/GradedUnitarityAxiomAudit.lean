import VOA.Core.FlagMinors
import VOA.Examples.VirasoroGradedUnitarity
-- Axiom probe for the graded-unitarity layer (ABLR Def. 2.2: statement + reduction).
--
-- NOTE.  Three further declarations of this layer are deliberately NOT listed:
--   VOA.FlagMinors.leadingPrincipal            -- [Quot.sound]
--   VOA.FlagMinors.leadingPrincipal_apply      -- [propext, Quot.sound]
--   VOA.VirGoodFil.length_le_energyVir         -- [propext, Quot.sound]
-- They depend on a STRICT SUBSET of the sanctioned base axioms, which is strictly better than the
-- trust boundary; but `run_axiom_audits.validate_reports` enforces EXACT equality with
-- {propext, Classical.choice, Quot.sound}, so listing them here would report a false failure.
-- Their verbatim reports are recorded in HANDOFF.md.
-- §1  Core.RealStructure: clauses (i)–(ii), the anti-linear ρ with parity
#print axioms VOA.RealStructure
#print axioms VOA.RealStructure.map_zero
#print axioms VOA.RealStructure.map_add
#print axioms VOA.RealStructure.map_neg
#print axioms VOA.RealStructure.rho_L
#print axioms VOA.RealStructure.Fixes
#print axioms VOA.RealStructure.Fixes.apply
#print axioms VOA.RealStructure.parity_eq_one_of_fixes
-- §2  Core.GoodFiltration: clause (iv), the graded flag
#print axioms VOA.GradedFlag
#print axioms VOA.GradedFlag.monotone
#print axioms VOA.GradedFlag.directed
#print axioms VOA.GradedFlag.ModeCompatible
#print axioms VOA.GradedFlag.pieceIn
#print axioms VOA.GradedFlag.mem_pieceIn
#print axioms VOA.GradedFlag.pieceIn_mono
#print axioms VOA.GradedFlag.pieceLT
#print axioms VOA.GradedFlag.pieceLT_zero
#print axioms VOA.GradedFlag.pieceLT_succ
#print axioms VOA.GradedFlag.pieceLT_le_pieceIn
#print axioms VOA.GradedFlag.iSup_pieceIn
#print axioms VOA.GoodFiltration
-- §3  Core.GradedUnitarity: clauses (iii),(v),(vi) and the layer reduction
#print axioms VOA.sesqForm
#print axioms VOA.sesqForm_apply
#print axioms VOA.sesqForm_add_left
#print axioms VOA.sesqForm_add_right
#print axioms VOA.sesqForm_smul_left
#print axioms VOA.sesqForm_smul_right
#print axioms VOA.sesqForm_eq_form_of_fixes
-- §3a  The DEFECT, recorded as a theorem: the old ℂ-bilinear encoding of clause (vi) forced ⊥
#print axioms VOA.eq_bot_of_bilinear_pos
-- §3b  The FIX: clause (vi) on a bundled SESQUILINEAR form
#print axioms VOA.SesqForm
#print axioms VOA.SesqForm.coe_mk
#print axioms VOA.SesqForm.zero_right
#print axioms VOA.SesqForm.zero_left
#print axioms VOA.SesqForm.smul_self
#print axioms VOA.SesqForm.I_smul_self
#print axioms VOA.SesqForm.orthogonal
#print axioms VOA.SesqForm.mem_orthogonal
#print axioms VOA.IsPosOn
#print axioms VOA.isPosOn_bot
#print axioms VOA.isPosOn_I_smul
#print axioms VOA.signedForm
#print axioms VOA.signedForm_apply
-- §3c  Honesty witnesses: satisfiable on a nonzero subspace, and NOT trivially true
#print axioms VOA.stdHerm
#print axioms VOA.stdHerm_apply
#print axioms VOA.top_ne_bot_of_complex
#print axioms VOA.isPosOn_stdHerm_top
#print axioms VOA.isPosOn_signedForm_stdHerm_zero
#print axioms VOA.not_isPosOn_signedForm_stdHerm_one
#print axioms VOA.nondegenerate_restrict_bot
#print axioms VOA.sup_inf_orthogonal_eq
#print axioms VOA.disjoint_inf_orthogonal
#print axioms VOA.finrank_add_inf_orthogonal
#print axioms VOA.gradedSesq
#print axioms VOA.gradedSesq_apply
#print axioms VOA.RhoStableOn
#print axioms VOA.orthogonal_gradedSesq_eq
#print axioms VOA.GradedFlag.layer
#print axioms VOA.GradedFlag.layer_le_pieceIn
#print axioms VOA.GradedFlag.layer_zero
#print axioms VOA.LayerNondegenerate
#print axioms VOA.LayerPositive
#print axioms VOA.GradedUnitaryAt
#print axioms VOA.GradedUnitary
#print axioms VOA.sesq_diag_eq_gradedForm
#print axioms VOA.nondegenerate_pieceLT
#print axioms VOA.layerDecomposition
#print axioms VOA.finrank_pieceLT_add_layer
#print axioms VOA.pieceIn_le_iSup_layer
#print axioms VOA.iSup_layer_eq_top
#print axioms VOA.exists_layer_ne_bot
-- §3d  The sign, calibrated at the vacuum (signed and untwisted)
#print axioms VOA.vacuumIn
#print axioms VOA.coe_vacuumIn
#print axioms VOA.vacuumIn_mem_layer_zero
#print axioms VOA.signedForm_gradedSesq_vacuum
#print axioms VOA.vacuumIn_ne_zero
#print axioms VOA.layer_zero_ne_bot
#print axioms VOA.isPosOn_layer_zero_vacuum
#print axioms VOA.layer_zero_ne_bot_and_isPosOn
#print axioms VOA.pos_gradedSesq_vacuum
-- §4  Core.FlagMinors: leading principal minors (VOA-free)
#print axioms VOA.FlagMinors.initFam
#print axioms VOA.FlagMinors.initFam_apply
#print axioms VOA.FlagMinors.initFam_linearIndependent
#print axioms VOA.FlagMinors.initFlag
#print axioms VOA.FlagMinors.initFlag_mono
#print axioms VOA.FlagMinors.initBasis
#print axioms VOA.FlagMinors.coe_initBasis
#print axioms VOA.FlagMinors.finrank_initFlag
#print axioms VOA.FlagMinors.toMatrix_restrict_initFlag
#print axioms VOA.FlagMinors.nondegenerate_restrict_initFlag_iff
#print axioms VOA.FlagMinors.RefinesBasis
#print axioms VOA.FlagMinors.RefinesBasis.finrank_eq
#print axioms VOA.FlagMinors.nondegenerate_flag_iff_minors
-- §5  Examples.VirasoroFormSymmetry: determinacy and symmetry of canB
#print axioms VOA.VirFormSym.adjLop
#print axioms VOA.VirFormSym.vac_negWord_cons
#print axioms VOA.VirFormSym.vac_row_ext
#print axioms VOA.VirFormSym.negWord_cons_left
#print axioms VOA.VirFormSym.negWord_row_ext
#print axioms VOA.VirFormSym.invariantForm_ext
#print axioms VOA.VirFormSym.transpose_normalized
#print axioms VOA.VirFormSym.canB_isSymmetric
#print axioms VOA.VirFormSym.canB_isRefl
#print axioms VOA.VirFormSym.gradedForm_canB_isRefl
-- §6  Examples.VirasoroQuotientForm: the form on L(c,0) is canGram
#print axioms VOA.VirQuotForm.Bsimp
#print axioms VOA.VirQuotForm.Bsimp_normalized
#print axioms VOA.VirQuotForm.Bsimp_isFullyInvariant
#print axioms VOA.VirQuotForm.Bsimp_leftRadical
#print axioms VOA.VirQuotForm.mkQ_L
#print axioms VOA.VirQuotForm.Bpull
#print axioms VOA.VirQuotForm.Bpull_apply
#print axioms VOA.VirQuotForm.Bpull_normalized
#print axioms VOA.VirQuotForm.canB_quot_mkQ
#print axioms VOA.VirQuotForm.gram_simple_negWord
#print axioms VOA.VirQuotForm.Bsimp_isSymmetric
#print axioms VOA.VirQuotForm.Bsimp_isRefl
#print axioms VOA.VirQuotForm.gradedForm_Bsimp_isRefl
-- §7  Examples.VirasoroGoodFiltration: the length flag on L(c,0)
#print axioms VOA.VirGoodFil.virFil
#print axioms VOA.VirGoodFil.goodFil
#print axioms VOA.VirGoodFil.virFil_mono
#print axioms VOA.VirGoodFil.goodFil_mono
#print axioms VOA.VirGoodFil.virFil_le_grading
#print axioms VOA.VirGoodFil.goodFil_le_grading
#print axioms VOA.VirGoodFil.virFil_zero_of_pos
#print axioms VOA.VirGoodFil.goodFil_zero_of_pos
#print axioms VOA.VirGoodFil.virFil_zero_zero_gens
#print axioms VOA.VirGoodFil.virFil_zero_zero
#print axioms VOA.VirGoodFil.goodFil_zero_zero
#print axioms VOA.VirGoodFil.sortedSpan_le_iSup_virFil
#print axioms VOA.VirGoodFil.iSup_virFil
#print axioms VOA.VirGoodFil.iSup_goodFil
#print axioms VOA.VirGoodFil.virFil_eq_grading_of_le
#print axioms VOA.VirGoodFil.goodFil_eq_grading_of_le
#print axioms VOA.VirGoodFil.virGradedFlag
#print axioms VOA.VirGoodFil.virGradedFlag_piece
-- §8  Examples.AdmissiblePartitions: the cited Salazar hypothesis
#print axioms VOA.AdmissiblePartitions.AdmissibleBasisHyp
#print axioms VOA.AdmissiblePartitions.FlagBasisHyp
#print axioms VOA.AdmissiblePartitions.altSum
#print axioms VOA.AdmissiblePartitions.altSum_zero
#print axioms VOA.AdmissiblePartitions.altSum_succ
#print axioms VOA.AdmissiblePartitions.finrank_pieceIn_of_flagBasisHyp
-- §9  Examples.VirasoroGradedUnitarity: the statement and the reduction
#print axioms VOA.VirGradedUnitarity.VirGradedUnitary
#print axioms VOA.VirGradedUnitarity.virGradedUnitary_iff
#print axioms VOA.VirGradedUnitarity.signedForm_gradedSesq_vacuum_simple
#print axioms VOA.VirGradedUnitarity.isPosOn_layer_zero_vacuum_simple
#print axioms VOA.VirGradedUnitarity.virLayerDecomposition
#print axioms VOA.VirGradedUnitarity.virFinrank_layer
#print axioms VOA.VirGradedUnitarity.virISup_layer_eq_top
#print axioms VOA.VirGradedUnitarity.layerNondegenerate_iff_minors
#print axioms VOA.VirGradedUnitarity.toMatrix_eq_canB_of_monomials
#print axioms VOA.VirGradedUnitarity.gradedUnitaryAt_iff_minors_and_positive
