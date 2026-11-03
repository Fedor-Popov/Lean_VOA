import VOA.DeligneAudit.DeligneFusionCV
import VOA.DeligneAudit.DeligneFusionU7

/-!
# Unconditional A₂ classical freeness

The actual universal CV dimension induction is instantiated with its two proved
base families. It gives the every-model total-dimension bound at all adjoint
powers. The existing evaluation-model Demazure realization and carrier squeeze
then give classical freeness and the exact C₂ kernel, with no named
mathematical input remaining.
-/

namespace VOA.DeligneAudit.A2

/-- The universal fusion degree-sum bound, at every adjoint power. -/
theorem CVUniv.fusionTotalDim : SectorWeyl.FusionTotalDim :=
  CVUniv.fusionTotalDim_of_cvBases CVUniv.sharpRectangularBases CVUniv.residualTheta3Bound

open VOA.DeligneHigherRankConditionalCapstone

/-- A₂ classical freeness and the full explicit C₂ kernel, unconditionally. -/
theorem classicallyFree :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_totalDim' CVUniv.fusionTotalDim

end VOA.DeligneAudit.A2

#print axioms VOA.DeligneAudit.A2.CVUniv.fusionTotalDim
#print axioms VOA.DeligneAudit.A2.classicallyFree
