import VOA.Classification.COne.OrbOctaZCStep22

/-! The certified intrinsic degree-25 octahedral Zhu relation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu OrbOctaZ Polynomial

/-- The actual conformal candidate annihilates the top self-mode. -/
theorem p25_selfMode31 : aeval (omegaL W) candidatePolynomial (selfMode 31) = 0 := by
  have h := partial46_holds
  simp only [partial46, evalRel, zp_pscaleL, map_mul, aeval_C, Module.End.mul_apply,
    Module.algebraMap_end_apply, add_zero, p25List_spec] at h
  exact (smul_eq_zero.mp h).resolve_left eliminationScale_ne_zero

/-- The requested intrinsic S4 Zhu relation, without a rationality hypothesis. -/
theorem OctahedralConformalZhuRelation_holds : OctahedralConformalZhuRelation := by
  obtain ⟨c, hc, ht⟩ := self_top_nonzero
  have h := p25_selfMode31
  rw [ht, map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hc

end VOA.Classification.COne.OrbOctaZC
