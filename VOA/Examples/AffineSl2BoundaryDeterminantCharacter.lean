/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.QWeylPairing
import VOA.Examples.AffineSl2ParabolicChargeSum
import VOA.Examples.AffineSl2BoundaryCharacterLowerBound

/-! # Actual total vacuum determinant order and the boundary character product -/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA.HighestModule Wak.Charged QSeries
noncomputable section
open scoped Classical

private theorem boundaryLevel_noncritical (P : ℕ) (hP : 0<P) :
    2/(P : ℂ)-2+2 ≠ 0 := by
  simpa only [sub_add_cancel] using
    div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hP))

/-- The finite sum of actual Gram determinant orders is exactly the
paired Weyl correction, with every energy guard and charge window proved. -/
theorem vacuumRootOrderTotal_eq_weylPairTail (P : ℕ) (hP : 0<P)
    (hcop : P.Coprime 2) (N : ℕ) :
    (vacuumRootOrderTotal (2/(P : ℂ)-2) N : ℚ) = weylPairTail P N := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) (sum_boundary_order_difference P hP hcop N)
  push_cast at he
  have hr : (vacuumRootOrderTotal (2/(P : ℂ)-2) N : ℚ) =
      ∑ c ∈ chargeWindow N, ((vacuumOrder (2/(P : ℂ)-2) N c : ℚ) -
        (reflectedOrder (2/(P : ℂ)-2) N (c+1) : ℚ)) := by
    simp only [vacuumRootOrderTotal,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply (eq_sub_iff_add_eq).mpr
    exact_mod_cast vacuum_determinant_order_add_reflected
      (2/(P : ℂ)-2) (boundaryLevel_noncritical P hP) N c
  rw [hr,he]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : 0<s := (Finset.mem_Icc.mp hs).1
  have hw : ((4*s-1 : ℕ) : ℚ) = 4*(s : ℚ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4*s)]
    push_cast
    rfl
  change (4*(s : ℚ)-1)*(shiftedPBWCount N _ : ℚ) -
      (4*(s : ℚ)+1)*(shiftedPBWCount N _ : ℚ) = _
  simp only [AffineSl2BoundaryVacuumResonances.lowerEnergy,
    AffineSl2BoundaryVacuumResonances.upperEnergy,shiftedPBWCount]
  rw [hw]
  split_ifs <;> simp [universalPBWCount_eq_coeff]

/-- The total actual root order plus the Euler product coefficient is the
full universal vacuum coefficient. This is the exact numerical identity
needed with the actual corank bound to close the character formula. -/
theorem vacuumRootOrderTotal_add_product (P : ℕ) (hP : 0<P)
    (hcop : P.Coprime 2) (N : ℕ) :
    (vacuumRootOrderTotal (2/(P : ℂ)-2) N : ℚ) +
      PowerSeries.coeff N
        ((PowerSeries.expand P (Nat.ne_of_gt hP) (euler : PowerSeries ℚ))^3 * reciprocalEuler^3) =
      PowerSeries.coeff N (reciprocalEuler^3 : PowerSeries ℚ) := by
  rw [vacuumRootOrderTotal_eq_weylPairTail P hP hcop]
  exact weylPairTail_add_product P (Nat.ne_of_gt hP) N

/-- The same identity with the actual universal VOA grade dimension. -/
theorem vacuumRootOrderTotal_add_product_eq_universal_finrank (P : ℕ) (hP : 0<P)
    (hcop : P.Coprime 2) (hk : 2/(P : ℂ)-2+2 ≠ 0) (N : ℕ) :
    (vacuumRootOrderTotal (2/(P : ℂ)-2) N : ℚ) +
      PowerSeries.coeff N
        ((PowerSeries.expand P (Nat.ne_of_gt hP) (euler : PowerSeries ℚ))^3 * reciprocalEuler^3) =
      (Module.finrank ℂ ((universal (2/(P : ℂ)-2) hk).grading N) : ℚ) := by
  rw [universal_grading_finrank_eq_reciprocalEuler_cube]
  exact vacuumRootOrderTotal_add_product P hP hcop N

end
end VOA.AffineSl2GeneralRigidity
