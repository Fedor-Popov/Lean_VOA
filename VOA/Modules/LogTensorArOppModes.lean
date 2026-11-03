/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArComul
import VOA.Modules.LogTensorContraCoordinates

/-! # Actual opposite current modes on arbitrary weak modules

The finite VOA L(1) tower gives a linear opposite action without any ordinary
module requirement. On a genuine generalized module it is the actual adjoint
used to construct the contragredient module.
-/
namespace VOA.LogTensor.Ar
open Module (End)
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
variable (N : WeakModule W M)

/-- The opposite modes of a homogeneous state, as a linear family on `W.grading wt`. -/
noncomputable def oppFam (wt : ℤ) : W.grading wt →ₗ[ℂ] ℤ → Module.End ℂ M where
  toFun u := fun k => (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ j) (u : V))) (2 * wt - k - 2 - (j : ℤ))
  map_add' u v := by
    funext k
    simp only [Submodule.coe_add, map_add, mode_add, smul_add, Finset.sum_add_distrib,
      Pi.add_apply]
  map_smul' c u := by
    funext k
    simp only [Submodule.coe_smul, map_smul, mode_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.sum_congr rfl fun j _ => smul_comm ((j.factorial : ℂ)⁻¹) c _, ← Finset.smul_sum,
      smul_comm]

/-- **The opposite modes** `u°ₖ`, linear in the state. -/
noncomputable def oppB : V →ₗ[ℂ] ℤ → Module.End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oppFam N)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem oppB_homog {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (k : ℤ) :
    oppB N u k = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oppB N u = oppFam N wt ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (oppFam N)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (oppFam N) wt ⟨u, hu⟩
  rw [hcollapse]; rfl


end VOA.LogTensor.Ar
