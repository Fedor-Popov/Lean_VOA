/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ParabolicExact

/-! # Exact finite joint dimensions of the actual parabolic module -/
namespace VOA.AffineVOA.HighestModule
open Wak.Charged (JointIndex)
noncomputable section
local instance parabolicJointIndexFintype (N : ℕ) (c : ℤ) : Fintype (JointIndex N c) := Wak.Charged.jointIndexFintype N c

/-- The reflection preserves affine energy and absolute Cartan eigenvalue. -/
theorem horizontalReflection_joint_iff (k : ℂ) (d N : ℕ) (c : ℤ)
    (x : Verma k (-(d : ℂ)-2)) :
    horizontalReflection k d x ∈ jointSpace k d N c ↔
      x ∈ jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1) := by
  rw [mem_jointSpace_iff,mem_jointSpace_iff]
  have hshift : -(d : ℂ)-2 + 2*((c+(d : ℤ)+1 : ℤ) : ℂ) = (d : ℂ)+2*(c : ℂ) := by
    push_cast
    ring
  rw [hshift]
  have hd := universalMap_intertwines (rho k d) (horizontalState k d (d+1))
    (horizontalState_reflection_highest k d)
    (AffineLie.ell0 kappaForm kappaForm_isInvariant) x
  have hh := universalMap_intertwines (rho k d) (horizontalState k d (d+1))
    (horizontalState_reflection_highest k d) (modeElement 2 0) x
  change horizontalReflection k d
    (rho k (-(d : ℂ)-2) (AffineLie.ell0 kappaForm kappaForm_isInvariant) x) =
    rho k d (AffineLie.ell0 kappaForm kappaForm_isInvariant) (horizontalReflection k d x) at hd
  change horizontalReflection k d (mode k (-(d : ℂ)-2) 2 0 x) =
    mode k d 2 0 (horizontalReflection k d x) at hh
  rw [← hd,← hh,← map_smul,← map_smul]
  exact and_congr (horizontalReflection_injective k d).eq_iff
    (horizontalReflection_injective k d).eq_iff

/-- The actual image of a finite joint Verma space in the parabolic quotient. -/
def parabolicJointSpace (k : ℂ) (d N : ℕ) (c : ℤ) : Submodule ℂ (Parabolic k d) :=
  (jointSpace k d N c).map (parabolicProjection k d)

private def jointProjection (k : ℂ) (d N : ℕ) (c : ℤ) :
    jointSpace k d N c →ₗ[ℂ] Parabolic k d :=
  (parabolicProjection k d).comp (jointSpace k d N c).subtype

/-- The reflection restricted to the matching finite joint spaces. -/
def horizontalReflectionJoint (k : ℂ) (d N : ℕ) (c : ℤ) :
    jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1) →ₗ[ℂ] jointSpace k d N c :=
  ((horizontalReflection k d).comp (jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1)).subtype).codRestrict
    (jointSpace k d N c) (fun x => (horizontalReflection_joint_iff k d N c x).mpr x.2)

theorem horizontalReflectionJoint_injective (k : ℂ) (d N : ℕ) (c : ℤ) :
    Function.Injective (horizontalReflectionJoint k d N c) := by
  intro x y hxy
  apply Subtype.ext
  exact horizontalReflection_injective k d (congrArg Subtype.val hxy)

private theorem reflectionJoint_range_eq_ker (k : ℂ) (d N : ℕ) (c : ℤ) :
    LinearMap.range (horizontalReflectionJoint k d N c) =
      LinearMap.ker (jointProjection k d N c) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change parabolicProjection k d (horizontalReflection k d y.1) = 0
    exact (LinearMap.mem_ker.mp ((horizontalReflection_range_eq_kernel k d) ▸
      (show horizontalReflection k d y.1 ∈ LinearMap.range (horizontalReflection k d) from ⟨y.1,rfl⟩)))
  · intro hx
    have hx' : x.1 ∈ LinearMap.ker (parabolicProjection k d) := hx
    rw [← horizontalReflection_range_eq_kernel] at hx'
    obtain ⟨y,hy⟩ := hx'
    have hy' : y ∈ jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1) :=
      (horizontalReflection_joint_iff k d N c y).mp (hy ▸ x.2)
    exact ⟨⟨y,hy'⟩,Subtype.ext hy⟩

/-- Every finite joint parabolic dimension is the literal difference of the
two Verma occupation counts in the exact horizontal reflection sequence. -/
theorem parabolicJointSpace_finrank_add (k : ℂ) (d N : ℕ) (c : ℤ) :
    Module.finrank ℂ (parabolicJointSpace k d N c) +
      Fintype.card (JointIndex N (c+(d : ℤ)+1)) = Fintype.card (JointIndex N c) := by
  letI : Module.Finite ℂ (jointSpace k d N c) := Module.Finite.of_basis (jointBasis k d N c)
  have h := (jointProjection k d N c).finrank_range_add_finrank_ker
  have hr : LinearMap.range (jointProjection k d N c) = parabolicJointSpace k d N c := by
    rw [jointProjection,LinearMap.range_comp,Submodule.range_subtype]
    rfl
  rw [hr,← reflectionJoint_range_eq_ker,
    LinearMap.finrank_range_of_inj (horizontalReflectionJoint_injective k d N c),
    jointSpace_finrank,jointSpace_finrank] at h
  exact h

end
end VOA.AffineVOA.HighestModule
