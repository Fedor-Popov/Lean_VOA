/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetComplex
import VOA.Examples.Sl2CosetVacuum

/-!
# Coset classes in actual relative cohomology

The closed relative representatives give a linear map to relative cycles modulo
relative boundaries. Inclusion of relative cycles descends to absolute BRST
cohomology and recovers the already constructed coset map. Consequently any
injectivity proof for the absolute coset map also proves relative injectivity.
The vacuum is the actual relative vacuum class constructed in `Sl2CosetVacuum`.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite
open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M}
variable (A : TranslatedAffineSl2Action V (-4))
variable (hV : TensorVA.ParityCompatible V)
variable (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)

/-- Inclusion of relative cycles into absolute BRST cycles. -/
noncomputable def relativeCyclesToAbsoluteCycles :
    LinearMap.ker (relativeQ A hV hg) →ₗ[ℂ] (semiInfiniteBRSTComplex A hV hg).kerQ :=
  ((relativeCarrier A.toAffineSl2Action).subtype.comp
    (LinearMap.ker (relativeQ A hV hg)).subtype).codRestrict _
      (fun x => congrArg Subtype.val x.property)

@[simp] theorem relativeCyclesToAbsoluteCycles_coe
    (x : LinearMap.ker (relativeQ A hV hg)) :
    ((relativeCyclesToAbsoluteCycles A hV hg x :
      (semiInfiniteBRSTComplex A hV hg).kerQ) : M ⊗[ℂ] Sl2GhostSpace) = x.val.val := rfl

/-- A relative boundary becomes zero in absolute cohomology. -/
theorem relativeBoundary_to_absolute_zero
    (x : LinearMap.ker (relativeQ A hV hg)) (hx : x ∈ relativeBoundaries A hV hg) :
    (semiInfiniteBRSTComplex A hV hg).prj (relativeCyclesToAbsoluteCycles A hV hg x) = 0 := by
  rw [BRST.BRSTComplex.prj_eq_zero]
  obtain ⟨y, hy⟩ := hx
  exact ⟨y.val, congrArg Subtype.val hy⟩

/-- Inclusion of the relative complex induces the canonical map to absolute
BRST cohomology. This map is not asserted to be injective on all classes. -/
noncomputable def relativeCohomologyToAbsolute :
    RelativeCohomology A hV hg →ₗ[ℂ] (semiInfiniteBRSTComplex A hV hg).Coh :=
  (relativeBoundaries A hV hg).liftQ
    ((semiInfiniteBRSTComplex A hV hg).prj.comp (relativeCyclesToAbsoluteCycles A hV hg))
    (fun x hx => relativeBoundary_to_absolute_zero A hV hg x hx)

@[simp] theorem relativeCohomologyToAbsolute_mkQ
    (x : LinearMap.ker (relativeQ A hV hg)) :
    relativeCohomologyToAbsolute A hV hg ((relativeBoundaries A hV hg).mkQ x) =
      (semiInfiniteBRSTComplex A hV hg).prj (relativeCyclesToAbsoluteCycles A hV hg x) := rfl

/-- The displayed coset representative inside the relative carrier. -/
noncomputable def cosetToRelativeComplex :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] relativeCarrier A.toAffineSl2Action :=
  (cosetToComplex A.toAffineSl2Action).codRestrict _
    (cosetToComplex_relative A.toAffineSl2Action)

/-- The displayed coset representative is a relative cycle. -/
noncomputable def cosetToRelativeCycles :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] LinearMap.ker (relativeQ A hV hg) :=
  (cosetToRelativeComplex A).codRestrict _ (fun x => by
    apply Subtype.ext
    exact cosetToComplex_closed A.toAffineSl2Action x)

@[simp] theorem relativeCyclesToAbsoluteCycles_coset
    (x : cosetSubspace A.toAffineSl2Action) :
    relativeCyclesToAbsoluteCycles A hV hg (cosetToRelativeCycles A hV hg x) =
      cosetToCycles A hV hg x := rfl

/-- The coset maps into actual relative cohomology by its vacuum representative. -/
noncomputable def cosetToRelativeCohomology :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] RelativeCohomology A hV hg :=
  (relativeBoundaries A hV hg).mkQ.comp (cosetToRelativeCycles A hV hg)

/-- Forgetting relative conditions recovers the absolute coset class. -/
@[simp] theorem relativeCohomologyToAbsolute_coset
    (x : cosetSubspace A.toAffineSl2Action) :
    relativeCohomologyToAbsolute A hV hg (cosetToRelativeCohomology A hV hg x) =
      cosetToCohomology A hV hg x := rfl

/-- Compatibility as an equality of linear maps. -/
theorem relativeCohomologyToAbsolute_comp_coset :
    (relativeCohomologyToAbsolute A hV hg).comp (cosetToRelativeCohomology A hV hg) =
      cosetToCohomology A hV hg := rfl

/-- The relative coset map sends the vacuum to the canonical relative class. -/
theorem cosetToRelativeCohomology_vacuum :
    cosetToRelativeCohomology A hV hg
      ⟨V.vacuum, vacuum_mem_cosetSubspace A.toAffineSl2Action⟩ =
      relativeVacuumClass A hV hg := rfl

/-- The relative vacuum class becomes the absolute vacuum class. -/
@[simp] theorem relativeCohomologyToAbsolute_vacuum :
    relativeCohomologyToAbsolute A hV hg (relativeVacuumClass A hV hg) =
      (semiInfiniteBRSTComplex A hV hg).cohomology.vacuum := rfl

/-- Injectivity into absolute cohomology implies injectivity into relative
cohomology, by the proved factorization. -/
theorem cosetToRelativeCohomology_injective_of_absolute
    (hinj : Function.Injective (cosetToCohomology A hV hg)) :
    Function.Injective (cosetToRelativeCohomology A hV hg) := by
  intro x y hxy
  apply hinj
  rw [← relativeCohomologyToAbsolute_coset A hV hg x,
    ← relativeCohomologyToAbsolute_coset A hV hg y, hxy]

end VOA.Sl2Coset
