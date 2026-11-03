/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteFactors
import VOA.Examples.Sl2CosetRelativeAuxiliary

/-!
# The concrete coset map to BRST cohomology

Every affine factor and every support hypothesis is fixed. The actual map
appends the auxiliary and ghost vacua. Its injectivity theorem retains only the
coset VOA, its simplicity and its identification with the restricted products.

`Sl2CosetConcreteVOA` constructs the conformal VOA on this commutant and
specializes injectivity to its simplicity alone.

OPEN: prove simplicity and identify this coset with the simple Lee–Yang VOA.
No graded-unitarity transfer is asserted here.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite Sl2Coset
open scoped TensorProduct

noncomputable section

/-- The actual diagonal-current commutant in the two simple affine factors. -/
abbrev CosetSpace := cosetSubspace diagonalAction.toAffineSl2Action

/-- The representative map appending the two auxiliary vacua. -/
def cosetToComplex : CosetSpace →ₗ[ℂ] MatterSpace ⊗[ℂ] Sl2GhostSpace :=
  auxiliaryCosetToComplex diagonalAction uAction abParityCompatible uParityCompatible
    abuTensorGrading leeYangMatter_level

theorem cosetToComplex_apply (x : CosetSpace) :
    cosetToComplex x = (x.val ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := rfl

theorem cosetToComplex_closed (x : CosetSpace) : leeYangBRSTComplex.Q (cosetToComplex x) = 0 :=
  auxiliaryCosetToComplex_closed diagonalAction uAction abParityCompatible uParityCompatible
    abuTensorGrading leeYangMatter_level x

theorem cosetToComplex_relative (x : CosetSpace) :
    cosetToComplex x ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action :=
  auxiliaryCosetToComplex_relative diagonalAction uAction abParityCompatible uParityCompatible
    abuTensorGrading leeYangMatter_level x

theorem cosetToComplex_mode (x y : CosetSpace) (n : ℤ) :
    cosetToComplex (cosetMode diagonalAction.toAffineSl2Action diagonalAction.translation x n y) =
      mode (brstSVA.Y (cosetToComplex x)) n (cosetToComplex y) :=
  auxiliaryCosetToComplex_mode diagonalAction uAction abParityCompatible uParityCompatible
    abuTensorGrading leeYangMatter_level x y n

/-- The concrete map has codomain literally the zero-ghost-degree cohomology. -/
def leeYangCosetToH0 : CosetSpace →ₗ[ℂ] leeYangBRSTComplex.H0 :=
  Sl2Coset.leeYangCosetToH0 aAction bAction uAction
    aParityCompatible bParityCompatible uParityCompatible abTensorGrading abuTensorGrading
    matterGhostTensorGrading

/-- Only the conformal coset and simplicity remain as inputs to injectivity. -/
theorem leeYangCosetToH0_injective
    (C : VertexOperatorAlgebra CosetSpace) (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum diagonalAction.toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode diagonalAction.toAffineSl2Action diagonalAction.translation x n y) :
    Function.Injective leeYangCosetToH0 :=
  Sl2Coset.leeYangCosetToH0_injective aAction bAction uAction
    aParityCompatible bParityCompatible uParityCompatible abTensorGrading abuTensorGrading
    matterGhostTensorGrading C hsimple hvac hmode
    aNatSupported bNatSupported uNatSupported aVacuum_ne_zero bVacuum_ne_zero uVacuum_ne_zero

-- The concrete relative kernel has several nested tensor and quotient instances.
set_option synthInstance.maxHeartbeats 100000 in
theorem relativeVacuum_survives :
    relativeVacuumClass leeYangMatterAction matterParityCompatible matterGhostTensorGrading ≠ 0 :=
  relativeVacuumClass_ne_zero leeYangMatterAction matterParityCompatible matterGhostTensorGrading
    matterNatSupported matterVacuum_ne_zero

end
end VOA.Sl2CosetConcrete
