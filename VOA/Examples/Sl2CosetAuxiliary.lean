/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetTensor
import VOA.Examples.Sl2CosetComplex

/-!
# The coset map with the auxiliary affine vacuum

A state in the commutant of the original current action remains in the
commutant after adjoining an auxiliary affine vacuum. Adjoining the ghost
vacuum then gives the displayed representative `(x ⊗ vacuum) ⊗ vacuum`.
It is relative, closed, of ghost degree zero, and preserves vacuum and all
vertex products after passage to BRST cohomology.
-/

namespace VOA.Sl2Coset
open Sl2SemiInfinite
open scoped TensorProduct
universe u v
variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {V : SuperVertexAlgebra M} {W : SuperVertexAlgebra N} {k l : ℂ}

/-- Adjoin the auxiliary affine vacuum in the right tensor factor. -/
noncomputable def auxiliaryVacuumEmbedding (W : SuperVertexAlgebra N) :
    M →ₗ[ℂ] M ⊗[ℂ] N :=
  (TensorProduct.mk ℂ M N).flip W.vacuum

@[simp] theorem auxiliaryVacuumEmbedding_apply (x : M) :
    auxiliaryVacuumEmbedding W x = x ⊗ₜ[ℂ] W.vacuum := rfl

/-- Every nonnegative diagonal current mode kills the auxiliary-vacuum image. -/
theorem auxiliaryVacuumEmbedding_mem_coset (A : AffineSl2Action V k)
    (B : AffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) {x : M} (hx : x ∈ cosetSubspace A) :
    auxiliaryVacuumEmbedding W x ∈ cosetSubspace (tensorAffineAction A B hV hW hg) := by
  intro a n hn
  change mode (TensorVA.tenY V W (tensorCurrentState A B a)) n
    (x ⊗ₜ[ℂ] W.vacuum) = 0
  rw [tensorCurrentMode_tmul, hx a n hn, (W.creation (B.current a)).2 n hn,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]

/-- The actual linear map from the original commutant into the matter commutant. -/
noncomputable def auxiliaryCosetEmbedding (A : AffineSl2Action V k)
    (B : AffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    cosetSubspace A →ₗ[ℂ] cosetSubspace (tensorAffineAction A B hV hW hg) :=
  ((auxiliaryVacuumEmbedding W).comp (cosetSubspace A).subtype).codRestrict _
    (fun x => auxiliaryVacuumEmbedding_mem_coset A B hV hW hg x.property)

@[simp] theorem auxiliaryCosetEmbedding_apply (A : AffineSl2Action V k)
    (B : AffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) (x : cosetSubspace A) :
    (auxiliaryCosetEmbedding A B hV hW hg x : M ⊗[ℂ] N) =
      (x : M) ⊗ₜ[ℂ] W.vacuum := rfl

/-- Adjoining the auxiliary vacuum preserves all vertex modes. -/
theorem auxiliaryVacuumEmbedding_mode (x y : M) (n : ℤ) :
    auxiliaryVacuumEmbedding W (mode (V.Y x) n y) =
      mode (TensorVA.tenY V W (auxiliaryVacuumEmbedding W x)) n
        (auxiliaryVacuumEmbedding W y) :=
  (tenY_left_unit V W x y W.vacuum (-n - 1)).symm

section Translated
variable (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
variable (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
variable (hVW : TensorVA.TensorGradingHyp V W) (hlevel : k + l = -4)

/-- The exact representative with both the auxiliary and ghost vacua. -/
noncomputable def auxiliaryCosetToComplex :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (M ⊗[ℂ] N) ⊗[ℂ] Sl2GhostSpace :=
  (cosetToComplex ((tensorTranslatedAffineActionAt A B hV hW hVW (-4)
    hlevel)).toAffineSl2Action).comp (auxiliaryCosetEmbedding A.toAffineSl2Action
    B.toAffineSl2Action hV hW hVW)

@[simp] theorem auxiliaryCosetToComplex_apply (x : cosetSubspace A.toAffineSl2Action) :
    auxiliaryCosetToComplex A B hV hW hVW hlevel x =
      ((x : M) ⊗ₜ[ℂ] W.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := rfl

/-- The original coset maps into the genuine relative carrier. -/
theorem auxiliaryCosetToComplex_relative (x : cosetSubspace A.toAffineSl2Action) :
    auxiliaryCosetToComplex A B hV hW hVW hlevel x ∈ relativeCarrier
      ((tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)).toAffineSl2Action :=
  cosetToComplex_relative ((tensorTranslatedAffineActionAt A B hV hW hVW (-4)
    hlevel)).toAffineSl2Action ((auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV
    hW hVW) x)

/-- The actual semi-infinite differential kills every original-coset representative. -/
theorem auxiliaryCosetToComplex_closed (x : cosetSubspace A.toAffineSl2Action) :
    semiInfiniteQ ((tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)).toAffineSl2Action
      (auxiliaryCosetToComplex A B hV hW hVW hlevel x) = 0 :=
  cosetToComplex_closed ((tensorTranslatedAffineActionAt A B hV hW hVW (-4)
    hlevel)).toAffineSl2Action ((auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV
    hW hVW) x)

/-- The representative has ghost degree zero. -/
theorem auxiliaryCosetToComplex_ghost (x : cosetSubspace A.toAffineSl2Action) :
    auxiliaryCosetToComplex A B hV hW hVW hlevel x ∈ matterGhostGrading (M ⊗[ℂ] N) 0 :=
  cosetToComplex_ghost ((tensorTranslatedAffineActionAt A B hV hW hVW (-4)
    hlevel)).toAffineSl2Action ((auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV
    hW hVW) x)

/-- Every vertex product is already preserved on the complex representatives. -/
theorem auxiliaryCosetToComplex_mode (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ) :
    auxiliaryCosetToComplex A B hV hW hVW hlevel
      (cosetMode A.toAffineSl2Action A.translation x n y) =
      mode (TensorVA.tenY (TensorVA.tensorSVA V W hV hW hVW) sl2GhostSVA
        (auxiliaryCosetToComplex A B hV hW hVW hlevel x)) n
        (auxiliaryCosetToComplex A B hV hW hVW hlevel y) := by
  change ghostVacuumEmbedding (TensorVA.tensorSVA V W hV hW hVW) (auxiliaryVacuumEmbedding W
    (mode (V.Y (x : M)) n (y : M))) = _
  rw [auxiliaryVacuumEmbedding_mode]
  exact ghostVacuumEmbedding_mode (V := (TensorVA.tensorSVA V W hV hW hVW))
    (auxiliaryVacuumEmbedding W (x : M)) (auxiliaryVacuumEmbedding W (y : M)) n

variable (hg : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) sl2GhostSVA)

/-- The induced original-coset map into actual BRST cohomology. -/
noncomputable def auxiliaryCosetToCohomology :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (semiInfiniteBRSTComplex
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel) (parityCompatible_tensorSVA V W hV
      hW hVW) hg).Coh :=
  (cosetToCohomology (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
    (parityCompatible_tensorSVA V W hV hW hVW) hg).comp (auxiliaryCosetEmbedding
    A.toAffineSl2Action B.toAffineSl2Action hV hW hVW)

/-- Its image belongs to ghost degree zero cohomology. -/
theorem auxiliaryCosetToCohomology_mem_H0 (x : cosetSubspace A.toAffineSl2Action) :
    auxiliaryCosetToCohomology A B hV hW hVW hlevel hg x ∈
      (semiInfiniteBRSTComplex (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
        (parityCompatible_tensorSVA V W hV hW hVW) hg).H0 :=
  cosetToCohomology_mem_H0 (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
    (parityCompatible_tensorSVA V W hV hW hVW) hg ((auxiliaryCosetEmbedding A.toAffineSl2Action
    B.toAffineSl2Action hV hW hVW) x)

/-- The cohomology map with codomain restricted to `H⁰`. -/
noncomputable def auxiliaryCosetToH0 :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (semiInfiniteBRSTComplex
      (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel) (parityCompatible_tensorSVA V W hV
      hW hVW) hg).H0 :=
  (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg).codRestrict _
    (auxiliaryCosetToCohomology_mem_H0 A B hV hW hVW hlevel hg)

/-- The vacuum maps to the cohomology vacuum. -/
theorem auxiliaryCosetToCohomology_vacuum :
    auxiliaryCosetToCohomology A B hV hW hVW hlevel hg
      (cosetVacuum A.toAffineSl2Action) =
      (semiInfiniteBRSTComplex (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
        (parityCompatible_tensorSVA V W hV hW hVW) hg).cohomology.vacuum := rfl

/-- The map into cohomology preserves every actual coset vertex product. -/
theorem auxiliaryCosetToCohomology_mode
    (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ) :
    auxiliaryCosetToCohomology A B hV hW hVW hlevel hg
      (cosetMode A.toAffineSl2Action A.translation x n y) =
      mode ((semiInfiniteBRSTComplex (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
        (parityCompatible_tensorSVA V W hV hW hVW) hg).cohomology.Y
        (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg x)) n
        (auxiliaryCosetToCohomology A B hV hW hVW hlevel hg y) := by
  simp only [auxiliaryCosetToCohomology, LinearMap.comp_apply]
  refine Eq.trans ?_ (cosetToCohomology_mode
    (tensorTranslatedAffineActionAt A B hV hW hVW (-4) hlevel)
    (parityCompatible_tensorSVA V W hV hW hVW) hg
    (auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV hW hVW x)
    (auxiliaryCosetEmbedding A.toAffineSl2Action B.toAffineSl2Action hV hW hVW y) n)
  congr 1
  apply Subtype.ext
  exact auxiliaryVacuumEmbedding_mode (x : M) (y : M) n

end Translated
end VOA.Sl2Coset
