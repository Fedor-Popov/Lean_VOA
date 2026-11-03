/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangWardClosure

/-!
# Descent of the Lee--Yang screening field to simple quotients

A Feigin--Fuchs construction first produces the weight `-1/5` primary field on Fock or
universal Virasoro carriers.  The inverse-DS application, however, uses the simple Lee--Yang
quotient.  This file isolates and solves the quotient-theoretic part of that passage.

For source and target submodules `S` and `T`, a heterotypic coefficient `I_t : A -> B` descends
exactly when it maps `S` into `T`.  If the Virasoro modes preserve the two submodules, the
coefficientwise Ward identity descends automatically.  Lower truncation also descends, by
choosing a representative of a quotient vector.

Consequently the analytic/free-field construction has one precise simple-quotient obligation:
every coefficient of the Fock intertwiner must carry the Lee--Yang source null submodule into
the corresponding target null submodule.  No additional quotient or Ward calculation remains.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangIntertwinerDescent

open Module (End)
open ScreeningCoset
open ScreeningLowering

noncomputable section

universe u v

variable {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module ℂ Source]
variable [AddCommGroup Target] [Module ℂ Target]

variable (S : Submodule ℂ Source) (T : Submodule ℂ Target)

/-! ## Coefficientwise quotient maps -/

/-- A heterotypic map respects the chosen source and target null submodules. -/
def RespectsNullSubmodules (f : Source →ₗ[ℂ] Target) : Prop :=
  ∀ x, x ∈ S → f x ∈ T

/-- A heterotypic field respects the null submodules coefficient by coefficient. -/
def FieldRespectsNullSubmodules
    (I : FormalDist (Source →ₗ[ℂ] Target)) : Prop :=
  ∀ t, RespectsNullSubmodules S T (I t)

/-- The descended heterotypic coefficient. -/
def quotientCoeff (f : Source →ₗ[ℂ] Target)
    (hf : RespectsNullSubmodules S T f) :
    (Source ⧸ S) →ₗ[ℂ] (Target ⧸ T) :=
  Submodule.mapQ S T f hf

@[simp] theorem quotientCoeff_mkQ (f : Source →ₗ[ℂ] Target)
    (hf : RespectsNullSubmodules S T f) (x : Source) :
    quotientCoeff S T f hf (S.mkQ x) = T.mkQ (f x) := by
  exact Submodule.mapQ_apply S T f x

/-- The descended heterotypic field. -/
def quotientField (I : FormalDist (Source →ₗ[ℂ] Target))
    (hI : FieldRespectsNullSubmodules S T I) :
    FormalDist ((Source ⧸ S) →ₗ[ℂ] (Target ⧸ T)) :=
  fun t => quotientCoeff S T (I t) (hI t)

@[simp] theorem quotientField_mkQ
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hI : FieldRespectsNullSubmodules S T I) (t : ℤ) (x : Source) :
    quotientField S T I hI t (S.mkQ x) = T.mkQ (I t x) := by
  exact quotientCoeff_mkQ S T (I t) (hI t) x

/-- Mapping the source null submodule into the target null submodule is not merely sufficient:
it is exactly the condition for a coefficient to factor through the two quotient maps. -/
theorem respectsNullSubmodules_iff_factors
    (f : Source →ₗ[ℂ] Target) :
    RespectsNullSubmodules S T f ↔
      ∃ fbar : (Source ⧸ S) →ₗ[ℂ] (Target ⧸ T),
        ∀ x, fbar (S.mkQ x) = T.mkQ (f x) := by
  constructor
  · intro hf
    exact ⟨quotientCoeff S T f hf, quotientCoeff_mkQ S T f hf⟩
  · rintro ⟨fbar, hbar⟩ x hx
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change T.mkQ (f x) = 0
    rw [← hbar x]
    have hxzero : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
    rw [hxzero, map_zero]

/-- Coefficientwise null-submodule compatibility is exactly factorization of the whole formal
distribution through the source and target quotient carriers. -/
theorem fieldRespectsNullSubmodules_iff_factors
    (I : FormalDist (Source →ₗ[ℂ] Target)) :
    FieldRespectsNullSubmodules S T I ↔
      ∃ Ibar : FormalDist ((Source ⧸ S) →ₗ[ℂ] (Target ⧸ T)),
        ∀ t x, Ibar t (S.mkQ x) = T.mkQ (I t x) := by
  constructor
  · intro hI
    exact ⟨quotientField S T I hI, quotientField_mkQ S T I hI⟩
  · rintro ⟨Ibar, hbar⟩ t
    exact (respectsNullSubmodules_iff_factors S T (I t)).mpr
      ⟨Ibar t, hbar t⟩

/-- Lower truncation survives passage to quotient carriers. -/
theorem quotientField_isHeterotypicField
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hI : FieldRespectsNullSubmodules S T I)
    (hfield : ScreeningCoset.IsHeterotypicField I) :
    ScreeningCoset.IsHeterotypicField (quotientField S T I hI) := by
  intro xbar
  obtain ⟨x, rfl⟩ := S.mkQ_surjective xbar
  obtain ⟨B, hB⟩ := hfield x
  refine ⟨B, fun n hn => ?_⟩
  rw [quotientField_mkQ, hB n hn, map_zero]

/-! ## Virasoro modes on the quotients -/

/-- A family of operators preserves a submodule. -/
def ModeFamilyPreserves (Lop : ℤ → End ℂ Source) : Prop :=
  ∀ m x, x ∈ S → Lop m x ∈ S

/-- A mode descended to the quotient by an invariant submodule. -/
def quotientMode (Lop : ℤ → End ℂ Source)
    (hL : ModeFamilyPreserves S Lop) (m : ℤ) : End ℂ (Source ⧸ S) :=
  Submodule.mapQ S S (Lop m) (hL m)

@[simp] theorem quotientMode_mkQ (Lop : ℤ → End ℂ Source)
    (hL : ModeFamilyPreserves S Lop) (m : ℤ) (x : Source) :
    quotientMode S Lop hL m (S.mkQ x) = S.mkQ (Lop m x) := by
  exact Submodule.mapQ_apply S S (Lop m) x

/-! ## Descent of the Ward identity -/

/-- The primary Ward identity descends as soon as the field and both mode families preserve the
chosen null submodules. -/
theorem k85Ward_quotient
    (sourceL : ℤ → End ℂ Source) (targetL : ℤ → End ℂ Target)
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hSource : ModeFamilyPreserves S sourceL)
    (hTarget : ModeFamilyPreserves T targetL)
    (hI : FieldRespectsNullSubmodules S T I)
    (hWard : K85VirasoroIntertwinerWard sourceL targetL I) :
    K85VirasoroIntertwinerWard
      (quotientMode S sourceL hSource) (quotientMode T targetL hTarget)
      (quotientField S T I hI) := by
  intro m t
  apply LinearMap.ext
  intro xbar
  obtain ⟨x, rfl⟩ := S.mkQ_surjective xbar
  have h := LinearMap.congr_fun (hWard m t) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [quotientField_mkQ, quotientMode_mkQ, quotientMode_mkQ,
    quotientField_mkQ, quotientField_mkQ, ← map_sub, h, map_smul]

/-! ## Packaging the exact simple-quotient gate -/

/-- The three invariance statements needed to descend a concrete Lee--Yang screening field.
For the source simple vacuum VOA, `sourceNull` is instantiated by its maximal null ideal. -/
structure K85ScreeningDescentData
    (D : K85VirasoroScreeningFieldData (Vir := Source) (ShiftedVir := Target)) where
  sourceNull : Submodule ℂ Source
  targetNull : Submodule ℂ Target
  sourceMode_preserves : ModeFamilyPreserves sourceNull D.sourceL
  targetMode_preserves : ModeFamilyPreserves targetNull D.targetL
  field_preserves : FieldRespectsNullSubmodules sourceNull targetNull D.field

/-- A concrete universal/Fock screening package plus the null-submodule compatibility produces
the full screening package on the corresponding simple quotients. -/
def K85ScreeningDescentData.toQuotientScreeningFieldData
    {D : K85VirasoroScreeningFieldData (Vir := Source) (ShiftedVir := Target)}
    (Q : K85ScreeningDescentData D) :
    K85VirasoroScreeningFieldData
      (Vir := Source ⧸ Q.sourceNull) (ShiftedVir := Target ⧸ Q.targetNull) where
  sourceL := quotientMode Q.sourceNull D.sourceL Q.sourceMode_preserves
  targetL := quotientMode Q.targetNull D.targetL Q.targetMode_preserves
  field := quotientField Q.sourceNull Q.targetNull D.field Q.field_preserves
  isHeterotypicField := quotientField_isHeterotypicField
    Q.sourceNull Q.targetNull D.field Q.field_preserves D.isHeterotypicField
  ward := k85Ward_quotient Q.sourceNull Q.targetNull D.sourceL D.targetL D.field
    Q.sourceMode_preserves Q.targetMode_preserves Q.field_preserves D.ward

end
end LeeYangIntertwinerDescent
end InverseDS
end VOA
