/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangIntertwinerDescent

/-!
# The Feigin--Fuchs boundary for the Lee--Yang inverse-DS field

The background-charge files construct Virasoro modes of central charge
`1 - 12 * ⟨λ,λ⟩`, and give a charged exponential of half norm `X` the weight
`X - ⟨λ,β⟩`.  In rank one, imposing central charge `-22/5` and weight `-1/5` leaves
two possible half norms: `1/10` and `2/5`.

Neither is the half norm of a vector in an even integral lattice.  Thus the existing lattice
vertex operators cannot be specialized to the required Lee--Yang field: one must extend their
exponential construction to a nonintegral Fock coset.  This file proves that arithmetic boundary
and packages the exact coefficient-level result available once such a coset field is supplied.

Only five primary Ward identities are required.  Passage from the Fock carriers to the simple
Lee--Yang carriers then has exactly the null-submodule condition isolated in
`InverseDSLeeYangIntertwinerDescent`: every field coefficient must map the source singular
submodule into the target singular submodule.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangFockBoundary

open Module (End)
open ScreeningCoset ScreeningLowering
open LeeYangWardClosure

noncomputable section

universe u v

/-! ## Exact rank-one momentum arithmetic -/

/-- The Lee--Yang central charge fixes the squared background charge to `9/20`. -/
theorem leeYang_backgroundSquare
    (lambdaSq : ℂ) (hc : 1 - 12 * lambdaSq = (-22 / 5 : ℂ)) :
    lambdaSq = 9 / 20 := by
  linear_combination (-1 / 12) * hc

/-- Let `X = ⟨β,β⟩/2`.  In rank one, the weight equation says
`⟨λ,β⟩ = X + 1/5`, while collinearity and `⟨λ,λ⟩ = 9/20` say
`(X + 1/5)^2 = 9X/10`.  Its two exact solutions are `X = 1/10` and `X = 2/5`. -/
theorem leeYang_halfNorm_solutions (X : ℂ)
    (hRankOne : (X + 1 / 5) ^ 2 = (9 / 10) * X) :
    X = 1 / 10 ∨ X = 2 / 5 := by
  have hfactor : (X - 1 / 10) * (X - 2 / 5) = 0 := by
    calc
      (X - 1 / 10) * (X - 2 / 5) =
          (X + 1 / 5) ^ 2 - (9 / 10) * X := by ring
      _ = 0 := sub_eq_zero.mpr hRankOne
  rcases mul_eq_zero.mp hfactor with hsmall | hlarge
  · exact Or.inl (sub_eq_zero.mp hsmall)
  · exact Or.inr (sub_eq_zero.mp hlarge)

/-- Both candidate half norms really solve the rank-one momentum equation. -/
theorem leeYang_halfNorm_candidates_solve (X : ℂ)
    (hX : X = 1 / 10 ∨ X = 2 / 5) :
    (X + 1 / 5) ^ 2 = (9 / 10) * X := by
  rcases hX with rfl | rfl <;> norm_num

/-- An even integral lattice has integral half norms, so neither Lee--Yang candidate can occur.
This is the precise obstruction to reusing the current integral-lattice exponential API. -/
theorem leeYang_halfNorm_not_integral (X : ℤ)
    (hX : (X : ℂ) = 1 / 10 ∨ (X : ℂ) = 2 / 5) : False := by
  rcases hX with hsmall | hlarge
  · have htenComplex : (10 : ℂ) * (X : ℂ) = 1 := by
      rw [hsmall]
      norm_num
    have hten : (10 : ℤ) * X = 1 := by
      exact_mod_cast htenComplex
    omega
  · have hfiveComplex : (5 : ℂ) * (X : ℂ) = 2 := by
      rw [hlarge]
      norm_num
    have hfive : (5 : ℤ) * X = 2 := by
      exact_mod_cast hfiveComplex
    omega

/-! ## The coefficient-level Fock-coset endpoint -/

variable {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module ℂ Source]
variable [AddCommGroup Target] [Module ℂ Target]

/-- The data still required from an arbitrary-momentum Fock-coset exponential construction.
The Virasoro representations themselves contain all infinite mode relations; the new exponential
must supply lower truncation and only five coefficient identities. -/
structure K85FockCosetCoefficientData
    (sourceRep : VirRep Source) (targetRep : VirRep Target) where
  field : FormalDist (Source →ₗ[ℂ] Target)
  isHeterotypicField : ScreeningCoset.IsHeterotypicField field
  ward_negTwo : PrimaryWardAt k85ScreeningVirWeight
    (virMode sourceRep) (virMode targetRep) field (-2)
  ward_negOne : PrimaryWardAt k85ScreeningVirWeight
    (virMode sourceRep) (virMode targetRep) field (-1)
  ward_zero : PrimaryWardAt k85ScreeningVirWeight
    (virMode sourceRep) (virMode targetRep) field 0
  ward_one : PrimaryWardAt k85ScreeningVirWeight
    (virMode sourceRep) (virMode targetRep) field 1
  ward_two : PrimaryWardAt k85ScreeningVirWeight
    (virMode sourceRep) (virMode targetRep) field 2

/-- A nonintegral Fock-coset field with the five checked identities gives the exact infinite
Ward package consumed by the inverse-DS lowering-current construction. -/
def K85FockCosetCoefficientData.toScreeningFieldData
    (sourceRep : VirRep Source) (targetRep : VirRep Target)
    (hSourceCentral : sourceRep.centralCharge = leeYangCentralCharge)
    (hTargetCentral : targetRep.centralCharge = leeYangCentralCharge)
    (D : K85FockCosetCoefficientData sourceRep targetRep) :
    K85VirasoroScreeningFieldData (Vir := Source) (ShiftedVir := Target) :=
  K85VirasoroScreeningFiveModeData.toScreeningFieldData
    { sourceL := virMode sourceRep
      targetL := virMode targetRep
      field := D.field
      isHeterotypicField := D.isHeterotypicField
      sourceVirasoro := virMode_isLeeYangModeFamily sourceRep hSourceCentral
      targetVirasoro := virMode_isLeeYangModeFamily targetRep hTargetCentral
      ward_negTwo := D.ward_negTwo
      ward_negOne := D.ward_negOne
      ward_zero := D.ward_zero
      ward_one := D.ward_one
      ward_two := D.ward_two }

end
end LeeYangFockBoundary
end InverseDS
end VOA
