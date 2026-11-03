/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ParabolicAdaptedBasis

/-! # The actual finite joint parabolic character -/
namespace VOA.AffineVOA.HighestModule
noncomputable section
local instance parabolicCharJointFintype (N : ℕ) (c : ℤ) :
    Fintype (Wak.Charged.JointIndex N c) := Wak.Charged.jointIndexFintype N c

/-- Telescoping the actual horizontal exact sequence produces precisely the
finite horizontal string times the ordinary negative-current PBW count. -/
theorem parabolicJointSpace_finrank_eq_sum_vacuum (k : ℂ) (d N : ℕ) (c : ℤ) :
    Module.finrank ℂ (parabolicJointSpace k d N c) =
      ∑ j ∈ Finset.range (d+1),
        Fintype.card (AffineSl2GeneralRigidity.JointIndex (N : ℤ) (2*(c+(j : ℤ)))) := by
  have H : ∀ d : ℕ,∀ c : ℤ,
      (∑ j ∈ Finset.range (d+1),
        Fintype.card (AffineSl2GeneralRigidity.JointIndex (N : ℤ) (2*(c+(j : ℤ))))) +
      Fintype.card (Wak.Charged.JointIndex N (c+(d : ℤ)+1)) =
        Fintype.card (Wak.Charged.JointIndex N c) := by
    intro d
    induction d with
    | zero =>
      intro c
      simpa only [Nat.zero_add,Finset.sum_range_one,Nat.cast_zero,add_zero] using
        (joint_vacuum_dimension N c).symm
    | succ d ih =>
      intro c
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add,Nat.cast_one]
      have hi := ih (c+1)
      have hv := joint_vacuum_dimension N c
      have he : (fun j : ℕ => Fintype.card
          (AffineSl2GeneralRigidity.JointIndex (N : ℤ) (2*(c+((j : ℤ)+1))))) =
          (fun j : ℕ => Fintype.card
          (AffineSl2GeneralRigidity.JointIndex (N : ℤ) (2*((c+1)+(j : ℤ))))) := by
        funext j
        congr 2 <;> ring
      rw [he]
      have hs : c+((d : ℤ)+1)+1 = (c+1)+(d : ℤ)+1 := by ring
      rw [hs]
      simp only [Nat.cast_zero,add_zero]
      omega
  have h := parabolicJointSpace_finrank_add k d N c
  have hh := H d c
  omega

end
end VOA.AffineVOA.HighestModule
