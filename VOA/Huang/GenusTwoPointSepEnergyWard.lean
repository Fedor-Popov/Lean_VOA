import VOA.Huang.GenusTwoPointSepEnergyIdentity
import VOA.Huang.GenusTwoPointSepWardTransport

/-!
# Ward transport after the proof of coordinate conjugation

Only the actual square Ward identities remain hypotheses. This file does not
assert them for an individual mode coefficient or for an unevaluated trace sum.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne QEquation
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- Left Ward transport with coordinate conjugation discharged. -/
theorem huangCollectedLeftWard_of_squareWard (P₁ P₂ : LWModule W)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hS : SquareLeftWard P₁ P₂ c S) :
    CollectedLeftWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      (huangScaledKernels c) (huangModifyPair P₁ P₂ S) :=
  collectedLeftWard_of_square P₁ P₂
    (normalizedSquareConjugation_holds P₁) (normalizedSquareConjugation_holds P₂) c S hS

/-- Right Ward transport, retaining the opposite oriented elliptic kernels. -/
theorem huangCollectedRightWard_of_squareWard (P₁ P₂ : LWModule W)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hS : SquareRightWard P₁ P₂ c S) :
    CollectedRightWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      (huangScaledKernels c) (huangModifyPair P₁ P₂ S) :=
  collectedRightWard_of_square P₁ P₂
    (normalizedSquareConjugation_holds P₁) (normalizedSquareConjugation_holds P₂) c S hS

/-- The TraceDescent consumer requires just the two square Ward
identities for the supplied bilinear function and kernels. -/
theorem huangTraceDescent_of_squareWard (P₁ P₂ : LWModule W)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hL : SquareLeftWard P₁ P₂ c S) (hR : SquareRightWard P₁ P₂ c S) :
    TraceDescent P₁.isMod.toWeakModule P₂.isMod.toWeakModule (huangScaledKernels c)
      (tensorTrace (R := ℂ) (huangModifyPair P₁ P₂ S)) :=
  traceDescent_of_squareWard P₁ P₂
    (normalizedSquareConjugation_holds P₁) (normalizedSquareConjugation_holds P₂) c S hL hR

end VOA.Huang.GenusTwoPoint.Separate
