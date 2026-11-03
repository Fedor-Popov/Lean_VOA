/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2UniversalCharacter
import VOA.Examples.AffineSl2BoundaryVacuumOrderPairs

/-! # Exact finite all-charge sums of the parabolic character -/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA
noncomputable section

/-- Exact oscillator count in one conformal energy, using actual PBW occupations. -/
def universalPBWCount (N : ℕ) : ℕ := Nat.card (EnergyIndex N)

/-- Translating root charges within a sufficiently large ambient window loses no nonzero term. -/
theorem sum_shifted_joint_count (N L : ℕ) (q : ℤ)
    (hplus : (L : ℤ)+q≤N) (hminus : (L : ℤ)-q≤N) :
    (∑ c ∈ chargeWindow N,Fintype.card (JointIndex L (2*(c+q)))) = universalPBWCount L := by
  have hsum : (∑ c ∈ chargeWindow N,Fintype.card (JointIndex L (2*(c+q)))) =
      ∑ c ∈ chargeWindow L,Fintype.card (JointIndex L (2*c)) := by
    apply Finset.sum_bij_ne_zero (fun c _ _ => c+q)
    · intro c hc hn
      obtain ⟨i⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
      exact jointIndex_charge_mem_window L (c+q) i
    · intro a ha hna b hb hnb he
      omega
    · intro b hb hn
      have hb' := Finset.mem_Icc.mp hb
      have ha : b-q ∈ chargeWindow N := by
        simp only [chargeWindow,Finset.mem_Icc]
        omega
      refine ⟨b-q,ha,?_,by omega⟩
      simpa only [sub_add_cancel] using hn
    · intro c hc hn
      rfl
  rw [hsum,← universal_grading_finrank_eq_sum_joint 1 (by norm_num),
    universal_grading_finrank_eq_energy_count]
  rfl

/-- Each actual horizontal spin-r module contributes exactly 2r+1 copies
of the ordinary vacuum oscillator count after summing all charges. -/
theorem sum_parabolic_joint_finrank (k : ℂ) (N L r : ℕ) (h : L+r≤N) :
    (∑ c ∈ chargeWindow N,Module.finrank ℂ
      (HighestModule.parabolicJointSpace k (2*r) L (c-(r : ℤ)))) =
      (2*r+1)*universalPBWCount L := by
  calc
    _ = ∑ c ∈ chargeWindow N,∑ j ∈ Finset.range (2*r+1),
        Fintype.card (JointIndex L (2*(c-(r : ℤ)+(j : ℤ)))) := by
      exact Finset.sum_congr rfl (fun c _ => HighestModule.parabolicJointSpace_finrank_eq_sum_vacuum _ _ _ _)
    _ = ∑ j ∈ Finset.range (2*r+1),∑ c ∈ chargeWindow N,
        Fintype.card (JointIndex L (2*(c-(r : ℤ)+(j : ℤ)))) := Finset.sum_comm
    _ = ∑ _j ∈ Finset.range (2*r+1),universalPBWCount L := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have he : (fun c : ℤ => Fintype.card (JointIndex L (2*(c-(r : ℤ)+(j : ℤ))))) =
          (fun c : ℤ => Fintype.card (JointIndex L (2*(c+((j : ℤ)-(r : ℤ)))))) := by
        funext c
        congr 2 <;> ring
      rw [he]
      exact sum_shifted_joint_count N L ((j : ℤ)-(r : ℤ)) (by omega) (by omega)
    _ = _ := by simp

/-- The same exact count in the integer ring used by determinant root orders. -/
theorem sum_parabolic_joint_finrank_int (k : ℂ) (N L r : ℕ) (h : L+r≤N) :
    (∑ c ∈ chargeWindow N,(Module.finrank ℂ
      (HighestModule.parabolicJointSpace k (2*r) L (c-(r : ℤ))) : ℤ)) =
      (2*(r : ℤ)+1)*(universalPBWCount L : ℤ) := by
  exact_mod_cast sum_parabolic_joint_finrank k N L r h

/-- The oscillator count is the coefficient of the literal reciprocal Euler cube. -/
theorem universalPBWCount_eq_coeff (N : ℕ) :
    (universalPBWCount N : ℚ) =
      PowerSeries.coeff N ((QSeries.reciprocalEuler : PowerSeries ℚ)^3) := by
  have hk : (1 : ℂ)+2≠0 := by norm_num
  rw [universalPBWCount,← universal_grading_finrank_eq_energy_count 1 hk]
  exact universal_grading_finrank_eq_reciprocalEuler_cube 1 hk N

/-- A shifted oscillator count is zero if the prescribed energy exceeds the grade. -/
def shiftedPBWCount (N energy : ℕ) : ℕ :=
  if energy≤N then universalPBWCount (N-energy) else 0

theorem sum_shiftedParabolicCount (k : ℂ) (N energy r : ℕ) (hr : r≤energy) :
    (∑ c ∈ chargeWindow N,
      AffineSl2BoundaryVacuumResonances.shiftedParabolicCount k N c energy r) =
        (2*r+1)*shiftedPBWCount N energy := by
  by_cases he : energy≤N
  · simp only [AffineSl2BoundaryVacuumResonances.shiftedParabolicCount,shiftedPBWCount,if_pos he]
    exact sum_parabolic_joint_finrank k N (N-energy) r (by omega)
  · simp [AffineSl2BoundaryVacuumResonances.shiftedParabolicCount,shiftedPBWCount,he]

/-- The finite sum of every actual vacuum root-order difference is the exact
odd/even Weyl tail, expressed through honest nonnegative oscillator counts. -/
theorem sum_boundary_order_difference (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2) (N : ℕ) :
    (∑ c ∈ chargeWindow N,
      ((Wak.Charged.vacuumOrder (2/(P:ℂ)-2) N c : ℤ) -
        Wak.Charged.reflectedOrder (2/(P:ℂ)-2) N (c+1))) =
      ∑ s ∈ Finset.Icc 1 N,
        ((4*(s : ℤ)-1)*(shiftedPBWCount N
          (AffineSl2BoundaryVacuumResonances.lowerEnergy P s) : ℤ) -
         (4*(s : ℤ)+1)*(shiftedPBWCount N
          (AffineSl2BoundaryVacuumResonances.upperEnergy P s) : ℤ)) := by
  simp_rw [AffineSl2BoundaryVacuumResonances.boundary_order_difference P hP hcop 1 N]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : 0<s := (Finset.mem_Icc.mp hs).1
  have hps : 0<P*s := Nat.mul_pos hP hs'
  have hlo : 2*s-1≤AffineSl2BoundaryVacuumResonances.lowerEnergy P s :=
    Nat.le_mul_of_pos_left _ hps
  have hhi : 2*s≤AffineSl2BoundaryVacuumResonances.upperEnergy P s :=
    (Nat.le_succ (2*s)).trans (Nat.le_mul_of_pos_left _ hps)
  rw [Finset.sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,
    sum_shiftedParabolicCount 1 N _ _ hlo,sum_shiftedParabolicCount 1 N _ _ hhi]
  have hc : ((2*(2*s-1)+1 : ℕ) : ℤ)=4*(s : ℤ)-1 := by
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤2*s)]
    push_cast
    ring
  rw [Nat.cast_mul,Nat.cast_mul,hc]
  push_cast
  ring

end
end VOA.AffineSl2GeneralRigidity
