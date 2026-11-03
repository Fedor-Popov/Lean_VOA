import VOA.Examples.AffineSl2BoundaryVacuumResonances
import VOA.Examples.AffineSl2ParabolicJoint

/-! # Actual parabolic dimensions in the vacuum determinant valuation -/
namespace VOA.AffineSl2BoundaryVacuumResonances
open AffineVOA.HighestModule
noncomputable section
local instance orderPairFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c

/-- The genuine joint dimension of a spin-r parabolic term shifted in energy. -/
def shiftedParabolicCount (k : ℂ) (n : ℕ) (c : ℤ) (energy r : ℕ) : ℕ :=
  if energy≤n then Module.finrank ℂ (parabolicJointSpace k (2*r) (n-energy) (c-r)) else 0

/-- Exact horizontal reflection turns each two-count difference into the
dimension of an actual finite-horizontal quotient. -/
theorem shifted_joint_difference (k : ℂ) (n : ℕ) (c : ℤ) (energy r : ℕ) :
    (shiftedJointCount n c energy (r:ℤ) : ℤ) -
      shiftedJointCount n (c+1) energy (-(r:ℤ)) =
        shiftedParabolicCount k n c energy r := by
  by_cases he : energy≤n
  · simp only [shiftedJointCount,shiftedParabolicCount,if_pos he]
    have h := parabolicJointSpace_finrank_add k (2*r) (n-energy) (c-r)
    have hc : c-(r:ℤ)+((2*r:ℕ):ℤ)+1=(c+1)-(-(r:ℤ)) := by push_cast; ring
    rw [hc] at h
    omega
  · simp [shiftedJointCount,shiftedParabolicCount,he]

theorem shiftedJointCount_shift (n : ℕ) (c : ℤ) (energy : ℕ) (charge a : ℤ) :
    shiftedJointCount n (c+a) energy (charge+a) = shiftedJointCount n c energy charge := by
  simp [shiftedJointCount,show c+a-(charge+a)=c-charge by ring]

/-- Each pair of adjacent boundary resonance families is precisely an
odd-spin parabolic dimension minus the next even-spin one. -/
theorem resonance_pair_difference (P s : ℕ) (hs : 0<s) (k : ℂ) (n : ℕ) (c : ℤ) :
    ((shiftedJointCount n c (lowerEnergy P s) (2*(s:ℤ)-1) +
        shiftedJointCount n c (upperEnergy P s) (-(2*(s:ℤ)+1)) : ℕ) : ℤ) -
      (shiftedJointCount n (c+1) (upperEnergy P s) (2*(s:ℤ)+1) +
        shiftedJointCount n (c+1) (lowerEnergy P s) (-(2*(s:ℤ)-1))) =
      (shiftedParabolicCount k n c (lowerEnergy P s) (2*s-1) : ℤ) -
        shiftedParabolicCount k n c (upperEnergy P s) (2*s) := by
  have hodd := shifted_joint_difference k n c (lowerEnergy P s) (2*s-1)
  have heven := shifted_joint_difference k n c (upperEnergy P s) (2*s)
  have hc : ((2*s-1:ℕ):ℤ)=2*(s:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*s)]; push_cast; rfl
  rw [hc] at hodd
  have hepos : shiftedJointCount n (c+1) (upperEnergy P s) (2*(s:ℤ)+1) =
      shiftedJointCount n c (upperEnergy P s) (2*(s:ℤ)) :=
    shiftedJointCount_shift n c _ _ 1
  have heneg : shiftedJointCount n c (upperEnergy P s) (-(2*(s:ℤ)+1)) =
      shiftedJointCount n (c+1) (upperEnergy P s) (-(2*(s:ℤ))) := by
    have hh := shiftedJointCount_shift n c (upperEnergy P s) (-(2*(s:ℤ)+1)) 1
    rw [show -(2*(s:ℤ)+1)+1= -(2*(s:ℤ)) by ring] at hh
    exact hh.symm
  rw [hepos,heneg]
  push_cast at heven ⊢
  omega

/-- Pointwise all-degree root-order cancellation, identified with actual
parabolic joint dimensions. All determinant and energy cutoffs are included. -/
theorem boundary_order_difference (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (k : ℂ) (n : ℕ) (c : ℤ) :
    (Wak.Charged.vacuumOrder (2/(P:ℂ)-2) n c : ℤ) -
      Wak.Charged.reflectedOrder (2/(P:ℂ)-2) n (c+1) =
      ∑ s∈Finset.Icc 1 n,
        ((shiftedParabolicCount k n c (lowerEnergy P s) (2*s-1) : ℤ) -
          shiftedParabolicCount k n c (upperEnergy P s) (2*s)) := by
  rw [vacuumOrder_boundary P hP hcop,reflectedOrder_boundary P hP hcop]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  exact resonance_pair_difference P s (Finset.mem_Icc.mp hs).1 k n c

end
end VOA.AffineSl2BoundaryVacuumResonances
