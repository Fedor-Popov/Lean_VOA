/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetAuxiliary
import VOA.Examples.Sl2CosetInjective
import VOA.Examples.Sl2CosetVacuum

/-!
# Injection of the original coset into degree-zero cohomology

The actual map appends the auxiliary and ghost vacua. Its kernel is an ideal,
so simplicity gives injectivity. Non-exactness of the vacuum is proved from
nonnegative integral factor weights and nonzero factor vacua.

OPEN: construct the concrete Lee–Yang coset VOA, its Sugawara difference
conformal vector, and its simplicity/identification. Here a VOA on the actual
commutant carrier with its proved vacuum and modes is explicit input.
OPEN: filtration strictness, the second/Hodge differential, invariant-form and
conjugation compatibility, and the dimension squeeze are not asserted here.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite
open scoped TensorProduct

universe u v w
variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {V : SuperVertexAlgebra M} {W : SuperVertexAlgebra N} {k l : ℂ}

section Auxiliary
variable (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
variable (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
variable (hVW : TensorVA.TensorGradingHyp V W) (hlevel : k + l = -4)
variable (hg : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) sl2GhostSVA)

/-- Simplicity of the original coset makes its actual auxiliary-vacuum map
injective, provided the target vacuum class is nonzero. -/
theorem auxiliaryCosetToCohomology_injective
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode A.toAffineSl2Action A.translation x n y)
    (hclass : (semiInfiniteBRSTComplex
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
      (parityCompatible_tensorSVA V W hV hW hVW) hg).cohomology.vacuum ≠ 0) :
    Function.Injective (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg) := by
  apply injective_of_simple_mode_map C (semiInfiniteBRSTComplex
    (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
    (parityCompatible_tensorSVA V W hV hW hVW) hg).cohomology
    (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg) hsimple
  · intro x y n
    rw [hmode]
    exact auxiliaryCosetToCohomology_mode A B hV hW hVW hlevel hg x y n
  · rw [hvac, auxiliaryCosetToCohomology_vacuum]
    exact hclass

/-- Factorwise weight support proves the target vacuum survives, discharging
the non-exactness premise of the simple-kernel argument. -/
theorem auxiliaryCosetToCohomology_injective_of_natSupported
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode A.toAffineSl2Action A.translation x n y)
    (hnV : DSMor.NatSupported V.grading) (hnW : DSMor.NatSupported W.grading)
    (hvV : V.vacuum ≠ 0) (hvW : W.vacuum ≠ 0) :
    Function.Injective (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg) :=
  auxiliaryCosetToCohomology_injective A B hV hW hVW hlevel hg C hsimple hvac hmode
    (semiInfinite_cohomology_vacuum_ne_zero
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
      (parityCompatible_tensorSVA V W hV hW hVW) hg
      (natSupported_tensorSVA V W hV hW hVW hnV hnW)
      (tensorSVA_vacuum_ne_zero V W hV hW hVW hvV hvW))

/-- The actual injection into `H⁰`, with non-exactness proved rather than assumed. -/
theorem auxiliaryCosetToH0_injective_of_natSupported
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode A.toAffineSl2Action A.translation x n y)
    (hnV : DSMor.NatSupported V.grading) (hnW : DSMor.NatSupported W.grading)
    (hvV : V.vacuum ≠ 0) (hvW : W.vacuum ≠ 0) :
    Function.Injective (auxiliaryCosetToH0 A B hV hW hVW hlevel hg) := by
  intro x y hxy
  apply auxiliaryCosetToCohomology_injective_of_natSupported A B hV hW hVW hlevel hg
    C hsimple hvac hmode hnV hnW hvV hvW
  exact congrArg Subtype.val hxy

end Auxiliary

end VOA.Sl2Coset
