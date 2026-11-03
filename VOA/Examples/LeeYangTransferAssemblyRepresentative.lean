/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangTransferAssemblyComplex

/-!
# The actual relative cocycle representing a Lee--Yang state

The conformal-weight preservation proved here is a consequence of the concrete
coset grading and the zero weights of the two appended vacua. Closure and
relative-carrier membership are the existing concrete BRST theorems.
-/

namespace VOA.LeeYangTransferAssembly

open Sl2CosetConcrete Sl2SemiInfinite VirSimple LeeYang LeeYangCosetTransfer
open scoped TensorProduct

noncomputable section

/-- Appending the auxiliary and ghost vacua preserves the actual conformal weight. -/
theorem cosetToComplex_mem_weight (n : ℤ) (x : CosetSpace)
    (hx : x ∈ cosetVOA.grading n) :
    cosetToComplex x ∈ brstSVA.grading (n : ℂ) := by
  rw [cosetToComplex_apply]
  change (x.val ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
    TensorVA.tenGrading matterSVA sl2GhostSVA (n : ℂ)
  apply TensorVA.tmul_mem_tenGrading matterSVA sl2GhostSVA (h₁ := (n : ℂ))
  · change x.val ⊗ₜ[ℂ] USVA.vacuum ∈ TensorVA.tenGrading abSVA USVA (n : ℂ)
    apply TensorVA.tmul_mem_tenGrading abSVA USVA (h₁ := (n : ℂ))
    · exact hx
    · simpa only [sub_self] using USVA.vacuum_mem
  · simpa only [sub_self] using sl2GhostSVA.vacuum_mem

/-- The concrete representative of a Lee--Yang weight-space vector in the finite
relative complex. -/
def cosetWeightRepresentative (ident : CosetIdentification) (n : ℤ) :
    (virasoroSimple leeYangC).grading n →ₗ[ℂ] relativeWeight n :=
  ((cosetToComplex.comp (cosetVOA.grading n).subtype).comp
    (ident.weightEquiv n).symm.toLinearMap).codRestrict _ (fun x =>
      ⟨cosetToComplex_relative _, cosetToComplex_mem_weight n _
        ((ident.weightEquiv n).symm x).property⟩)

@[simp] theorem cosetWeightRepresentative_coe (ident : CosetIdentification) (n : ℤ)
    (x : (virasoroSimple leeYangC).grading n) :
    (cosetWeightRepresentative ident n x : BRSTSpace) =
      cosetToComplex (ident.equiv.symm x) := rfl

/-- Every such representative is closed for the restricted differential. -/
theorem cosetWeightRepresentative_closed (ident : CosetIdentification) (n : ℤ)
    (x : (virasoroSimple leeYangC).grading n) :
    relativeDifferential n (cosetWeightRepresentative ident n x) = 0 := by
  apply Subtype.ext
  exact cosetToComplex_closed (ident.equiv.symm x)

/-- The Lee--Yang representative with codomain restricted to relative cycles. -/
def cosetWeightCycles (ident : CosetIdentification) (n : ℤ) :
    (virasoroSimple leeYangC).grading n →ₗ[ℂ] LinearMap.ker (relativeDifferential n) :=
  (cosetWeightRepresentative ident n).codRestrict _
    (cosetWeightRepresentative_closed ident n)

/-- A linear family of cycles defines a linear family of cohomology classes. -/
def cycleClassOfCycles {K M : Type*} [AddCommGroup K] [Module ℂ K]
    [AddCommGroup M] [Module ℂ M] (Q : K →ₗ[ℂ] K)
    (f : M →ₗ[ℂ] LinearMap.ker Q) : M →ₗ[ℂ] cycleQuotient Q :=
  (boundariesInCycles Q).mkQ.comp f

/-- A family of cycles is injective in cohomology when exactness detects only
the zero source vector. -/
theorem cycleClassOfCycles_injective_of_exact {K M : Type*}
    [AddCommGroup K] [Module ℂ K] [AddCommGroup M] [Module ℂ M]
    (Q : K →ₗ[ℂ] K) (f : M →ₗ[ℂ] LinearMap.ker Q)
    (hexact : ∀ x, f x ∈ boundariesInCycles Q → x = 0) :
    Function.Injective (cycleClassOfCycles Q f) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  exact hexact x ((Submodule.Quotient.mk_eq_zero (boundariesInCycles Q)).mp hx)

/-- The actual map from a Lee--Yang weight space to relative BRST cohomology. -/
def cosetWeightClass (ident : CosetIdentification) (n : ℤ) :=
  cycleClassOfCycles (K := relativeWeight n) (M := (virasoroSimple leeYangC).grading n)
    (relativeDifferential n)
    (cosetWeightCycles ident n)

/-- The absolute class of the actual relative cycle is exactly the already
verified concrete coset-to-`H⁰` map. -/
theorem cosetWeightCycles_toAbsolute (ident : CosetIdentification) (n : ℤ)
    (x : (virasoroSimple leeYangC).grading n) :
    leeYangBRSTComplex.prj (weightCyclesToAbsolute n (cosetWeightCycles ident n x)) =
      (leeYangCosetToH0 (ident.equiv.symm x) : leeYangBRSTComplex.Coh) := rfl

set_option maxHeartbeats 2000000 in
/-- Injectivity follows through absolute cohomology; relative-to-absolute
injectivity is not needed. -/
theorem cosetWeightClass_injective (ident : CosetIdentification) (n : ℤ) :
    Function.Injective (cosetWeightClass ident n) := by
  have result := cycleClassOfCycles_injective_of_exact
    (K := relativeWeight n) (M := (virasoroSimple leeYangC).grading n)
    (relativeDifferential n) (cosetWeightCycles ident n) (fun x hb => by
      have ha := weightBoundary_toAbsolute n (cosetWeightCycles ident n x) hb
      rw [cosetWeightCycles_toAbsolute] at ha
      have hz : leeYangCosetToH0 (ident.equiv.symm x) = 0 := Subtype.ext ha
      have hi : ident.equiv.symm x = 0 := ident.cosetToH0_injective (by simpa using hz)
      apply Subtype.ext
      exact ident.equiv.symm.injective (by simpa using hi))
  exact result

end
end VOA.LeeYangTransferAssembly
