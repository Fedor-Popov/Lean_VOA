import VOA.Moonshine.MoonshineCNStringSymmetry

/-! # Direct comparison of the physical and longitudinal radical quotients -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H]

namespace StringModule

variable (M : StringModule H)

def physicalKQuotientEquiv (hc : M.c = 26) (hF : M.LightConeSplit) :
    M.weightRadicalQuotient M.physical 1 ≃ₗ[ℂ] M.weightRadicalQuotient M.kVacuum 1 :=
  (M.transversePhysicalQuotientEquiv hc hF).symm.trans (M.transverseKQuotientEquiv hF 1)

theorem physicalKQuotientEquiv_isometry (hc : M.c = 26) (hF : M.LightConeSplit)
    (p q : M.weightRadicalQuotient M.physical 1) :
    M.radicalQuotientForm M.kVacuum 1 (M.physicalKQuotientEquiv hc hF p)
      (M.physicalKQuotientEquiv hc hF q) = M.radicalQuotientForm M.physical 1 p q := by
  obtain ⟨p, rfl⟩ := (M.transversePhysicalQuotientEquiv hc hF).surjective p
  obtain ⟨q, rfl⟩ := (M.transversePhysicalQuotientEquiv hc hF).surjective q
  simp only [physicalKQuotientEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (M.transverseKQuotientEquiv_isometry hF 1 p q).trans
    (M.transversePhysicalQuotientEquiv_isometry hc hF p q).symm

end StringModule

namespace StringGroupAction

variable {M : StringModule H} {G : Type*} [Group G] (A : StringGroupAction M G)

theorem physicalKQuotientEquiv_equivariant (hc : M.c = 26) (hF : M.LightConeSplit)
    (g : G) (p : M.weightRadicalQuotient M.physical 1) :
    M.physicalKQuotientEquiv hc hF
      (A.stableWeightQuotientAction M.physical A.action_preserves_physical 1 g p) =
      A.stableWeightQuotientAction M.kVacuum A.action_preserves_kVacuum 1 g
        (M.physicalKQuotientEquiv hc hF p) := by
  simp only [StringModule.physicalKQuotientEquiv, LinearEquiv.trans_apply]
  rw [A.physicalQuotientRepresentative_equivariant, A.transverseKQuotientEquiv_equivariant]

end StringGroupAction

end VOA.Moonshine.ConwayNorton
