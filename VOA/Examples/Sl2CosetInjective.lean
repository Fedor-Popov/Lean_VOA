/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetComplex
import VOA.Examples.Sl2CosetVacuum
import VOA.Core.BilinearForm

/-!
# Simplicity makes the coset cohomology map injective

The kernel of a linear map preserving every vertex mode is an ideal in the
repository's existing sense. For a simple source it is zero provided the vacuum
has nonzero image. This applies to the actual coset map into BRST cohomology.

The conformal VOA structure on the coset and nonvanishing of the vacuum class
are explicit inputs. Neither is inferred merely from an affine current action.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite

universe u v

/-- A mode-preserving map from a simple VOA to any super vertex algebra is
injective as soon as its vacuum image is nonzero. -/
theorem injective_of_simple_mode_map
    {X : Type u} [AddCommGroup X] [Module ℂ X]
    {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
    (C : VertexOperatorAlgebra X) (D : SuperVertexAlgebra Y) (f : X →ₗ[ℂ] Y)
    (hsimple : C.IsSimple)
    (hmode : ∀ (x y : X) (n : ℤ),
      f (C.smul x n y) = mode (D.Y (f x)) n (f y))
    (hvac : f C.vacuum ≠ 0) : Function.Injective f := by
  have hker : C.IsIdeal (LinearMap.ker f) := by
    intro x y n hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [hmode, hy, map_zero]
  apply LinearMap.ker_eq_bot.mp
  rcases hsimple.2 (LinearMap.ker f) hker with hbot | htop
  · exact hbot
  · exfalso
    apply hvac
    apply LinearMap.mem_ker.mp
    rw [htop]
    exact Submodule.mem_top

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M}
variable (A : TranslatedAffineSl2Action V (-4))
variable (hV : TensorVA.ParityCompatible V)
variable (hg : TensorVA.TensorGradingHyp V Sl2SemiInfinite.sl2GhostSVA)

/-- The actual coset-to-BRST-cohomology map is injective under simplicity and
nonvanishing of the vacuum class. The supplied VOA uses the proved coset products. -/
theorem cosetToCohomology_injective
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ),
      C.smul x n y = cosetMode A.toAffineSl2Action A.translation x n y)
    (hclass : (semiInfiniteBRSTComplex A hV hg).cohomology.vacuum ≠ 0) :
    Function.Injective (cosetToCohomology A hV hg) := by
  apply injective_of_simple_mode_map C (semiInfiniteBRSTComplex A hV hg).cohomology
    (cosetToCohomology A hV hg) hsimple
  · intro x y n
    rw [hmode]
    exact cosetToCohomology_mode A hV hg x y n
  · rw [hvac]
    intro hz
    apply hclass
    exact (cosetToCohomology_vacuum A hV hg).symm.trans hz

/-- Restricting the target to ghost degree zero preserves this injectivity. -/
theorem cosetToH0_injective
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ),
      C.smul x n y = cosetMode A.toAffineSl2Action A.translation x n y)
    (hclass : (semiInfiniteBRSTComplex A hV hg).cohomology.vacuum ≠ 0) :
    Function.Injective (cosetToH0 A hV hg) := by
  intro x y hxy
  apply cosetToCohomology_injective A hV hg C hsimple hvac hmode hclass
  exact congrArg Subtype.val hxy

/-- For nonnegative integral matter weights the vacuum class nonvanishing
needed for injectivity is a theorem of the actual ghost complex. -/
theorem cosetToCohomology_injective_of_natSupported
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ),
      C.smul x n y = cosetMode A.toAffineSl2Action A.translation x n y)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    Function.Injective (cosetToCohomology A hV hg) :=
  cosetToCohomology_injective A hV hg C hsimple hvac hmode
    (semiInfinite_cohomology_vacuum_ne_zero A hV hg hn hv)

/-- The nonnegative-weight injectivity theorem with codomain restricted to H⁰. -/
theorem cosetToH0_injective_of_natSupported
    (C : VertexOperatorAlgebra (cosetSubspace A.toAffineSl2Action))
    (hsimple : C.IsSimple)
    (hvac : C.vacuum = cosetVacuum A.toAffineSl2Action)
    (hmode : ∀ (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ),
      C.smul x n y = cosetMode A.toAffineSl2Action A.translation x n y)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    Function.Injective (cosetToH0 A hV hg) :=
  cosetToH0_injective A hV hg C hsimple hvac hmode
    (semiInfinite_cohomology_vacuum_ne_zero A hV hg hn hv)

end VOA.Sl2Coset
