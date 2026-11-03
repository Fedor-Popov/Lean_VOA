/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3CurrentAction

/-!
# The matrix-current bracket

Bilinearity extends the checked basis table to every pair of actual
trace-zero matrices. This is the loop-current part of the representation;
the degree derivation still requires a separate energy-covariance proof.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- The actual polynomial currents realize the trace-normalized affine
bracket for arbitrary trace-zero matrices at every complex level. -/
theorem currentAction_bracket (k : ℂ) (m n : ℤ) (x y : Sl3) :
    ⁅currentAction k m x,currentAction k n y⁆ = currentAction k (m+n) ⁅x,y⁆+
      (if m+n=0 then ((m : ℂ)*k*form x y) • (1 : Module.End ℂ Fock) else 0) := by
  let z : ℂ := if m+n=0 then (m : ℂ)*k else 0
  let A : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] Module.End ℂ Fock := {
    toFun := fun u => {
      toFun := fun v => ⁅currentAction k m u,currentAction k n v⁆
      map_add' := by intro v w; simp only [map_add,lie_add]
      map_smul' := by intro a v; simp only [map_smul,comm_smul_right,RingHom.id_apply] }
    map_add' := by intro u v; ext w : 1; dsimp only; simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,map_add,add_lie]
    map_smul' := by
      intro a u; ext v : 1
      dsimp only
      simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,map_smul,comm_smul_left,RingHom.id_apply] }
  let B : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] Module.End ℂ Fock := {
    toFun := fun u => {
      toFun := fun v => currentAction k (m+n) ⁅u,v⁆+z • (form u v • (1 : Module.End ℂ Fock))
      map_add' := by
        intro v w
        simp only [lie_add,map_add,add_smul,smul_add]
        module
      map_smul' := by
        intro a v
        simp only [lie_smul,map_smul,RingHom.id_apply,smul_smul,smul_add]
        module }
    map_add' := by
      intro u v; ext w : 1
      dsimp only
      simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,add_lie,map_add,LinearMap.map_add₂,add_smul,smul_add]
      module
    map_smul' := by
      intro a u; ext v : 1
      dsimp only
      simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,smul_lie,map_smul,LinearMap.map_smul₂,
        RingHom.id_apply,smul_smul,smul_add]
      module }
  have hb (i j : Fin 8) : A (generator i) (generator j)=B (generator i) (generator j) := by
    change ⁅currentAction k m (generator i),currentAction k n (generator j)⁆ =
      currentAction k (m+n) ⁅generator i,generator j⁆+z • (form (generator i) (generator j) • 1)
    rw [currentAction_generator,currentAction_generator,currentBasis_bracket]
    change _ = (∑ c,structureConstant i j c • currentBasis k c (m+n)) + _
    by_cases hz : m+n=0 <;> simp [z,hz,smul_smul,mul_assoc]
  have hab : A=B := by
    apply LinearMap.ext; intro u
    apply LinearMap.ext; intro v
    rw [← reconstruct u,← reconstruct v]
    simp only [LinearMap.map_sum₂,map_sum,LinearMap.map_smul₂,map_smul,
      Finset.sum_apply,LinearMap.sum_apply,LinearMap.smul_apply]
    simp_rw [hb]
  have h := congrArg (fun T : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] Module.End ℂ Fock => T x y) hab
  change ⁅currentAction k m x,currentAction k n y⁆ =
    currentAction k (m+n) ⁅x,y⁆+z • (form x y • 1) at h
  by_cases hz : m+n=0 <;> simpa [z,hz,smul_smul,mul_assoc] using h

end
end VOA.AffineSl3.FreeField
