/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralRigidityBasis
import VOA.Examples.Sl2SemiInfiniteGhosts

/-!
# Support of the concrete affine factors

The ordinary vertex operator algebras underlying the coset construction are
viewed as purely even super vertex algebras. Their CFT-type positivity proves
natural-number support, hence the convolution grading hypotheses for every
pair of factors. The simple factors are the actual maximal-ideal quotients.
-/

namespace VOA.Sl2CosetConcrete

open AffineSl2GeneralRigidity

universe u v

/-- CFT-type positivity gives natural support after passing to complex weights. -/
theorem voaNatSupported {M : Type u} [AddCommGroup M] [Module ℂ M]
    (V : VertexOperatorAlgebra M) :
    DSMor.NatSupported V.toPreVertexAlgebra.toSuper.grading :=
  DSMor.natSupported_toSuper V.toPreVertexAlgebra V.positivity

/-- Every ordinary VOA is parity-compatible in its purely even reading. -/
theorem voaParityCompatible {M : Type u} [AddCommGroup M] [Module ℂ M]
    (V : VertexOperatorAlgebra M) :
    TensorVA.ParityCompatible V.toPreVertexAlgebra.toSuper :=
  DSMor.parityCompatible_toSuper V.toPreVertexAlgebra

/-- The tensor grading conditions require no further data for ordinary VOAs. -/
theorem voaTensorGradingHyp {M : Type u} {N : Type v}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (V : VertexOperatorAlgebra M) (W : VertexOperatorAlgebra N) :
    TensorVA.TensorGradingHyp V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper :=
  DSMor.tensorGradingHyp_of_natSupported _ _ (voaNatSupported V) (voaNatSupported W)

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The universal affine VOA, regarded as a purely even super vertex algebra. -/
noncomputable abbrev universalSVA := (universal k hk).toPreVertexAlgebra.toSuper

/-- The actual simple quotient, regarded as a purely even super vertex algebra. -/
noncomputable abbrev simpleSVA := (simple k hk).toPreVertexAlgebra.toSuper

theorem universalParityCompatible : TensorVA.ParityCompatible (universalSVA k hk) :=
  voaParityCompatible (universal k hk)

theorem simpleParityCompatible : TensorVA.ParityCompatible (simpleSVA k hk) :=
  voaParityCompatible (simple k hk)

theorem universalNatSupported : DSMor.NatSupported (universalSVA k hk).grading :=
  voaNatSupported (universal k hk)

theorem simpleNatSupported : DSMor.NatSupported (simpleSVA k hk).grading :=
  voaNatSupported (simple k hk)

/-- The universal vacuum is nonzero through the concrete affine PBW basis. -/
theorem universalVacuum_ne_zero : (universalSVA k hk).vacuum ≠ 0 :=
  AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk

/-- The actual maximal-ideal quotient does not kill the affine vacuum. -/
theorem simpleVacuum_ne_zero : (simpleSVA k hk).vacuum ≠ 0 :=
  simple_vacuum_ne_zero k hk

/-- The convolution grading for two actual simple affine quotients. -/
theorem simpleTensorGradingHyp (l : ℂ) (hl : l + 2 ≠ 0) :
    TensorVA.TensorGradingHyp (simpleSVA k hk) (simpleSVA l hl) :=
  voaTensorGradingHyp (simple k hk) (simple l hl)

/-- The convolution grading for an actual simple quotient and a universal factor. -/
theorem simpleUniversalTensorGradingHyp (l : ℂ) (hl : l + 2 ≠ 0) :
    TensorVA.TensorGradingHyp (simpleSVA k hk) (universalSVA l hl) :=
  voaTensorGradingHyp (simple k hk) (universal l hl)

end VOA.Sl2CosetConcrete
