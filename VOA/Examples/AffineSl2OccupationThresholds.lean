/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestWeightLeading

/-!
# Removing repeated oscillators in actual affine joint occupations

Marking an occurrence of a root oscillator amounts to removing a positive
number of its copies and retaining an unrestricted joint descendant
occupation. The zero-energy gamma oscillator is included; positive principal
weight supplies the finite multiplicity bound that energy alone cannot give.
-/
namespace VOA.Wak.Charged
open scoped BigOperators
noncomputable section
local instance thresholdFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- Fixed joint energy and charge bound every oscillator multiplicity by
the positive principal label, including gamma-zero multiplicity. -/
theorem jointIndex_multiplicity_le (n : ℕ) (c : ℤ) (d : JointIndex n c) (v : Fin 3×ℕ) :
    d.val v≤(2*(n : ℤ)-c).toNat :=
  principalIndex_bound _ ⟨d.val,jointIndex_principal n c d⟩ v

/-- Removing r available copies subtracts exactly their oscillator energy. -/
theorem occupationEnergy_remove (d : Occupation) (v : Fin 3×ℕ) (r : ℕ) (hr : r≤d v) :
    occupationEnergy (d-Finsupp.single v r)+r*oscillatorEnergy v=occupationEnergy d := by
  have he := congrArg occupationEnergy (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hr))
  simpa only [map_add,occupationEnergy,Finsupp.weight_single,nsmul_eq_mul] using he

/-- Removing r available copies subtracts their signed charge, without
natural-number truncation in this weight. -/
theorem occupationCharge_remove (d : Occupation) (v : Fin 3×ℕ) (r : ℕ) (hr : r≤d v) :
    occupationCharge (d-Finsupp.single v r)+(r : ℤ)*oscillatorCharge v=occupationCharge d := by
  have he := congrArg occupationCharge (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hr))
  simpa only [map_add,occupationCharge,Finsupp.weight_single,nsmul_eq_mul] using he

/-- An available multiplicity cannot spend more than the original energy;
this statement permits zero-energy gamma copies. -/
theorem jointIndex_copies_energy_le (n : ℕ) (c : ℤ) (d : JointIndex n c)
    (v : Fin 3×ℕ) (r : ℕ) (hr : r≤d.val v) : r*oscillatorEnergy v≤n := by
  have he := occupationEnergy_remove d.val v r hr
  rw [d.property.1] at he
  omega

/-- Removing and restoring a fixed oscillator multiplicity is an exact
bijection between a threshold subset and the full lower joint index set. -/
def removeOccupationEquiv (n : ℕ) (c : ℤ) (v : Fin 3×ℕ) (r : ℕ)
    (he : r*oscillatorEnergy v≤n) :
    {d : JointIndex n c // r≤d.val v} ≃
      JointIndex (n-r*oscillatorEnergy v) (c-(r : ℤ)*oscillatorCharge v) where
  toFun d := ⟨d.val.val-Finsupp.single v r,by
    constructor
    · have hh := occupationEnergy_remove d.val.val v r d.property
      rw [d.val.property.1] at hh
      omega
    · have hh := occupationCharge_remove d.val.val v r d.property
      rw [d.val.property.2] at hh
      omega⟩
  invFun d := ⟨⟨d.val+Finsupp.single v r,by
    constructor
    · rw [map_add,d.property.1]
      simpa only [occupationEnergy,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id] using Nat.sub_add_cancel he
    · rw [map_add,d.property.2]
      simp only [occupationCharge,Finsupp.weight_single,nsmul_eq_mul]
      omega⟩,by simp⟩
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr d.property)
  right_inv d := by
    apply Subtype.ext
    exact add_tsub_cancel_right _ _

/-- Threshold cardinality is the exact descendant occupation count when
the energy fits, and zero otherwise. The explicit zero branch is essential. -/
theorem occupationThreshold_card (n : ℕ) (c : ℤ) (v : Fin 3×ℕ) (r : ℕ) :
    Fintype.card {d : JointIndex n c // r≤d.val v}=
      if r*oscillatorEnergy v≤n then
        Fintype.card (JointIndex (n-r*oscillatorEnergy v) (c-(r : ℤ)*oscillatorCharge v)) else 0 := by
  classical
  by_cases he : r*oscillatorEnergy v≤n
  · rw [if_pos he,Fintype.card_congr (removeOccupationEquiv n c v r he)]
  · rw [if_neg he]
    letI : IsEmpty {d : JointIndex n c // r≤d.val v} :=
      ⟨fun d => he (jointIndex_copies_energy_le n c d.val v r d.property)⟩
    exact Fintype.card_eq_zero

/-- A finite natural multiplicity is the sum of its positive threshold indicators. -/
theorem multiplicity_threshold_sum (N m : ℕ) (hm : m≤N) :
    m=∑ r∈Finset.range N,if r+1≤m then 1 else 0 := by
  have he : (Finset.range N).filter (fun r => r+1≤m)=Finset.range m := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Finset.sum_filter,he]
  simp

/-- Summing a fixed oscillator's multiplicity over the actual joint basis
is exactly the sum of its descendant counts over positive thresholds. -/
theorem jointIndex_sum_multiplicity (n : ℕ) (c : ℤ) (v : Fin 3×ℕ) :
    (∑ d : JointIndex n c,d.val v)=
      ∑ r∈Finset.range (2*(n : ℤ)-c).toNat,
        if (r+1)*oscillatorEnergy v≤n then
          Fintype.card (JointIndex (n-(r+1)*oscillatorEnergy v)
            (c-((r+1 : ℕ) : ℤ)*oscillatorCharge v)) else 0 := by
  classical
  calc
    _ = ∑ d : JointIndex n c,∑ r∈Finset.range (2*(n : ℤ)-c).toNat,
        if r+1≤d.val v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact multiplicity_threshold_sum _ _ (jointIndex_multiplicity_le n c d v)
    _ = ∑ r∈Finset.range (2*(n : ℤ)-c).toNat,
        ∑ d : JointIndex n c,if r+1≤d.val v then 1 else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← occupationThreshold_card]
      simp only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]

end
end VOA.Wak.Charged
