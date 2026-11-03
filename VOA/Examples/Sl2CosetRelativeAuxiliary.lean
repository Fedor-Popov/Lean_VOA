/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetEmbedding
import VOA.Examples.Sl2CosetRelative

/-!
# The auxiliary-vacuum coset injection into relative cohomology

The actual representative `(x ⊗ vacuum_U) ⊗ vacuum_gh` defines a relative
cohomology class. Its image in absolute cohomology is the established coset
class. Simplicity and nonnegative factor weights therefore imply injectivity
into relative cohomology as well.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite
open scoped TensorProduct

universe u v
variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {V : SuperVertexAlgebra M} {W : SuperVertexAlgebra N} {k l : ℂ}
variable (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
variable (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
variable (hVW : TensorVA.TensorGradingHyp V W) (hlevel : k + l = -4)
variable (hg : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) sl2GhostSVA)

/-- Append the auxiliary and ghost vacua and pass to actual relative cohomology. -/
noncomputable def auxiliaryCosetToRelativeCohomology :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ]
      RelativeCohomology (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
        (parityCompatible_tensorSVA V W hV hW hVW) hg :=
  (cosetToRelativeCohomology
    (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
    (parityCompatible_tensorSVA V W hV hW hVW) hg).comp
      (auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV hW hVW)

/-- The relative class has the absolute class constructed above as image. -/
@[simp] theorem relativeCohomologyToAbsolute_auxiliaryCoset
    (x : cosetSubspace A.toAffineSl2Action) :
    relativeCohomologyToAbsolute
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
      (parityCompatible_tensorSVA V W hV hW hVW) hg
      (auxiliaryCosetToRelativeCohomology A B hV hW hVW hlevel hg x) =
        auxiliaryCosetToCohomology A B hV hW hVW hlevel hg x := rfl

/-- Compatibility of the two auxiliary-vacuum maps as a commuting triangle. -/
theorem relativeCohomologyToAbsolute_comp_auxiliaryCoset :
    (relativeCohomologyToAbsolute
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
      (parityCompatible_tensorSVA V W hV hW hVW) hg).comp
      (auxiliaryCosetToRelativeCohomology A B hV hW hVW hlevel hg) =
        auxiliaryCosetToCohomology A B hV hW hVW hlevel hg := rfl

/-- The original vacuum maps to the canonical relative matter-ghost vacuum class. -/
theorem auxiliaryCosetToRelativeCohomology_vacuum :
    auxiliaryCosetToRelativeCohomology A B hV hW hVW hlevel hg
      (cosetVacuum A.toAffineSl2Action) =
        relativeVacuumClass
          (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
          (parityCompatible_tensorSVA V W hV hW hVW) hg := rfl

/-- Any injectivity proof for the absolute auxiliary-vacuum map also proves
injectivity of the relative map. -/
theorem auxiliaryCosetToRelativeCohomology_injective_of_absolute
    (hinj : Function.Injective (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg)) :
    Function.Injective (auxiliaryCosetToRelativeCohomology A B hV hW hVW hlevel hg) := by
  intro x y hxy
  apply hinj
  rw [← relativeCohomologyToAbsolute_auxiliaryCoset A B hV hW hVW hlevel hg x,
    ← relativeCohomologyToAbsolute_auxiliaryCoset A B hV hW hVW hlevel hg y, hxy]

/-- Simplicity of the actual original coset and nonnegative factor weights
give its injection into the actual relative cohomology. Vacuum survival is
proved by the weight-zero ghost-degree argument. -/
theorem auxiliaryCosetToRelativeCohomology_injective_of_natSupported
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode A.toAffineSl2Action A.translation x n y)
    (hnV : DSMor.NatSupported V.grading) (hnW : DSMor.NatSupported W.grading)
    (hvV : V.vacuum ≠ 0) (hvW : W.vacuum ≠ 0) :
    Function.Injective (auxiliaryCosetToRelativeCohomology A B hV hW hVW hlevel hg) :=
  auxiliaryCosetToRelativeCohomology_injective_of_absolute A B hV hW hVW hlevel hg
    (auxiliaryCosetToCohomology_injective_of_natSupported A B hV hW hVW hlevel hg
      C hsimple hvac hmode hnV hnW hvV hvW)

end VOA.Sl2Coset
