import VOA.Classification.COne.AdmissibleOrdinaryFinite
import VOA.Huang.PzTensorDecomp

/-! # Removing DLM 8.1(c) from the associativity consumer

The remaining inputs are explicitly ABD weak admissibility and DLM finiteness.
-/

namespace VOA.Classification.COne.AdmissibleOrdinary

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- The existing DLM associativity bridge with the ordinary-module citation discharged. -/
theorem associativityInput_of_stronglyRational
    (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hFin : DLMFinitelyManyIrredAdmissible W) :
    VOA.Huang.AssocTarget.AssociativityInput W :=
  VOA.Huang.PzTensorDecomp.associativityInput_of_DLM hV hABD
    (dlmSimpleAdmissibleOrdinary_of_stronglyRational hV) hFin

end VOA.Classification.COne.AdmissibleOrdinary
