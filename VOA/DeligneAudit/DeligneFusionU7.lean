import VOA.DeligneAudit.DeligneFusionEvalModel
import VOA.DeligneAudit.DeligneFusionKernelLower

/-!
# The A₂ residuals after U7

U7 (`∀ n, DemazureRealization n`) is a theorem (`EvalModel.demazureRealization_all`), so A₂ classical
freeness rests on the single named residual `RavinderKernelLower` (S2).
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneGaussian VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ classical freeness from S2 alone.** -/
theorem classicallyFree_of_kernelLower' (hK : RavinderKernelLower) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_kernelLower hK EvalModel.demazureRealization_all

/-- U7 together with `FusionTotalDim`, for reference. -/
theorem classicallyFree_of_totalDim' (hF : SectorWeyl.FusionTotalDim) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_totalDim hF EvalModel.demazureRealization_all

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_kernelLower'
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_totalDim'
end AxiomAudit
