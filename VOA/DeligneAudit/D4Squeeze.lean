/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCountTypes

/-!
# D₄ Deligne classical freeness from the fusion squeeze inputs

`D4Lie.classicallyFree_of_fusionBoundZ` (U5 for the unclamped `d4FusionFZ`) combined with
`d4_fusionModuleBoundZ_of_squeeze`, whose Demazure count `Σ = 29^m` is proved from the algorithm
(`d4_demazure_total`).  The remaining inputs are the generic squeeze inputs for a family `M` of
graded characters and the universal bound for modules with the D₄ local Weyl relations.
-/

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneCharacter
  PowerSeries

/-- **D₄ Deligne classical freeness from the squeeze inputs.** -/
theorem classicallyFree_of_squeeze {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG D4Wp.hilbSeriesZ 28 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.D4sector.f V) (w : V),
      LocalWeylRelG VOA.DeligneAudit.DeligneSector.D4.D4sector ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  classicallyFree_of_fusionBoundZ (d4_fusionModuleBoundZ_of_squeeze h huniv)

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Lie.classicallyFree_of_squeeze
end AxiomAudit
