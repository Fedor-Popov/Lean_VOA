/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetEmbedding

/-! # The degree-zero coset injection at the Lee–Yang levels

All affine factors and the simple conformal coset remain explicit inputs.
This specialization proves the state injection, not the Lee–Yang identification
or graded-unitarity transfer.
-/

namespace VOA.Sl2Coset
open Sl2SemiInfinite
open scoped TensorProduct
universe u v w
variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {V : SuperVertexAlgebra M} {W : SuperVertexAlgebra N}
section LeeYangLevels
variable {P : Type w} [AddCommGroup P] [Module ℂ P]
variable {U : SuperVertexAlgebra P}
variable (A : TranslatedAffineSl2Action V (-4 / 3))
variable (B : TranslatedAffineSl2Action W 1)
variable (F : TranslatedAffineSl2Action U (-11 / 3))
variable (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
variable (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
variable (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U)
variable (hg : TensorVA.TensorGradingHyp (tensorThreeSVA V W U hV hW hU hVW hVWU) sl2GhostSVA)

/-- At the Lee–Yang levels, this is the concrete state map from the commutant
in the first two factors to degree-zero cohomology of all three factors. -/
noncomputable def leeYangCosetToH0 :=
  auxiliaryCosetToH0 (tensorTranslatedAffineAction A B hV hW hVW) F
    (parityCompatible_tensorSVA V W hV hW hVW) hU hVWU leeYangMatter_level hg

set_option maxHeartbeats 1600000 in
/-- The Lee–Yang-level coset map is injective under the actual coset simplicity
input and factorwise nonnegative weights/nonzero vacua. -/
theorem leeYangCosetToH0_injective
    (C : VertexOperatorAlgebra
      (cosetSubspace (tensorTranslatedAffineAction A B hV hW hVW).toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum =
      cosetVacuum (tensorTranslatedAffineAction A B hV hW hVW).toAffineSl2Action)
    (hmode : ∀ x y n, C.smul x n y =
      cosetMode (tensorTranslatedAffineAction A B hV hW hVW).toAffineSl2Action
        (tensorTranslatedAffineAction A B hV hW hVW).translation x n y)
    (hnV : DSMor.NatSupported V.grading) (hnW : DSMor.NatSupported W.grading)
    (hnU : DSMor.NatSupported U.grading)
    (hvV : V.vacuum ≠ 0) (hvW : W.vacuum ≠ 0) (hvU : U.vacuum ≠ 0) :
    Function.Injective (leeYangCosetToH0 A B F hV hW hU hVW hVWU hg) :=
  auxiliaryCosetToH0_injective_of_natSupported (tensorTranslatedAffineAction A B hV hW hVW) F
    (parityCompatible_tensorSVA V W hV hW hVW) hU hVWU
    leeYangMatter_level hg C hsimple hvac hmode
    (natSupported_tensorSVA V W hV hW hVW hnV hnW) hnU
    (tensorSVA_vacuum_ne_zero V W hV hW hVW hvV hvW) hvU

end LeeYangLevels
end VOA.Sl2Coset
