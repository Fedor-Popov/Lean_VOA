/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteFactors
import VOA.Examples.Sl2CosetConcreteSimpleSugawara

/-!
# The concrete coset conformal state

The ambient state is the sum of the conformal vectors of the actual simple
affine factors. Subtracting the diagonal Sugawara state at level `-1/3`
gives a weight-two even vector of their actual current commutant.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite Sl2Coset
open scoped TensorProduct

noncomputable section

/-- Retagging the boundary level preserves its actual Sugawara state. -/
theorem aAction_sugawara : sugawaraState aAction.toAffineSl2Action = AVOA.conformalVector := by
  change (2 * ((-4 / 3 : ℂ) + 2))⁻¹ •
    quadraticState (simpleAction ALevel aNoncritical).toAffineSl2Action = _
  rw [← aLevel_eq]
  exact simpleAction_sugawara ALevel aNoncritical

theorem bAction_sugawara : sugawaraState bAction.toAffineSl2Action = BVOA.conformalVector :=
  simpleAction_sugawara 1 bNoncritical

/-- The conformal-vector sum in the two actual simple affine factors. -/
def ambientConformal : ASpace ⊗[ℂ] BSpace :=
  AVOA.conformalVector ⊗ₜ[ℂ] BSVA.vacuum + ASVA.vacuum ⊗ₜ[ℂ] BVOA.conformalVector

/-- The diagonal Sugawara vector uses level `-4/3 + 1 = -1/3`. -/
def diagonalSugawara : ASpace ⊗[ℂ] BSpace := sugawaraState diagonalAction.toAffineSl2Action

/-- The proposed coset conformal vector, on the ambient tensor carrier. -/
def cosetOmega : ASpace ⊗[ℂ] BSpace := ambientConformal - diagonalSugawara

theorem ambientConformal_eq_tensorSugawara :
    ambientConformal = tensorSugawaraState aAction.toAffineSl2Action bAction.toAffineSl2Action := by
  simp only [ambientConformal, tensorSugawaraState, aAction_sugawara, bAction_sugawara]

/-- The actual concrete Sugawara difference lies in the actual commutant. -/
def cosetConformalData : CosetConformalData diagonalAction.toAffineSl2Action
    ambientConformal diagonalSugawara := by
  rw [ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalData aAction.toAffineSl2Action bAction.toAffineSl2Action
    (by norm_num) (by norm_num) (by norm_num)
    aParityCompatible bParityCompatible abTensorGrading

theorem cosetOmega_mem : cosetOmega ∈ cosetSubspace diagonalAction.toAffineSl2Action :=
  cosetConformalData.mem_coset

/-- The conformal difference, as a vector of the actual commutant. -/
def cosetOmegaState : cosetSubspace diagonalAction.toAffineSl2Action :=
  ⟨cosetOmega, cosetOmega_mem⟩

theorem cosetOmega_weight : cosetOmega ∈ abSVA.grading 2 := by
  rw [cosetOmega, ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalState_weight aAction.toAffineSl2Action bAction.toAffineSl2Action
    (by norm_num) (by norm_num) (by norm_num)
    aParityCompatible bParityCompatible abTensorGrading

theorem cosetOmega_even : cosetOmega ∈ abSVA.parity 0 := by
  rw [cosetOmega, ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalState_even aAction.toAffineSl2Action bAction.toAffineSl2Action
    (by norm_num) (by norm_num) (by norm_num)
    aParityCompatible bParityCompatible abTensorGrading

end
end VOA.Sl2CosetConcrete
