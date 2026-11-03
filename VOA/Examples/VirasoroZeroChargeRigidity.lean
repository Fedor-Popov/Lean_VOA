/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFixedReconstruction

/-!
# The zero-charge simple Virasoro algebra is graded rigid

At charge zero the universal conformal vector has zero canonical norm and
spans weight two. It lies in the radical and disappears in the simple quotient.
Its actual deformation self-products therefore have no central variation.
-/
namespace VOA.VirDeformModes
open VirModule VirSimple VertexOperatorAlgebra Deform

/-- At charge zero the conformal vector vanishes in the simple quotient.
It is orthogonal to all of weight two, hence belongs to the maximal ideal. -/
theorem zeroCharge_conformal_eq_zero : (virasoroSimple 0).conformalVector = 0 := by
  have hm : omegaVir 0 ∈ maxIdealVir 0 := by
    apply (LiRadical.mem_maxGradedIdeal_iff_grading (VirGram4.canB_isFullyInvariant 0)
      (VirGram4.canB_normalized 0) (omegaVir_mem_gradingVir_two 0)).mpr
    intro y hy
    change y ∈ gradingVir 0 2 at hy
    rw [VirDefLow.gradingVir_two, Submodule.mem_span_singleton] at hy
    obtain ⟨r, rfl⟩ := hy
    change (VirGram4.canB 0).form (LeeYang.L2vac 0) (r • LeeYang.L2vac 0) = 0
    rw [map_smul, VirGram4.canB_L2_L2]
    simp
  exact (Submodule.Quotient.mk_eq_zero _).mpr hm

/-- Every graded deformation at zero charge is a coordinate change.
The central correction vanishes because its conformal input itself is zero. -/
theorem zeroCharge_graded_rigidity : Deform.IsRigidGraded (virasoroSimple 0) := by
  intro D hD
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData 0 D hD
  have hα : α = 0 := by
    have h := ha.symm
    rw [zeroCharge_conformal_eq_zero, D.smul₁_zero_left] at h
    exact (smul_eq_zero.mp h).resolve_right (virasoroSimple_vacuum_ne_zero 0)
  apply isTrivial_of_zero_central_variation 0 D hD α β ha hb
  simp [hα]

end VOA.VirDeformModes
