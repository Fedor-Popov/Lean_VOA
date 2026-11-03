/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalReflection
import VOA.Examples.AffineSl2HorizontalRadical
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # The actual horizontal radical and norm at arbitrary integral highest weight -/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering Polynomial
open NormalOrdering (currentWord)
open Wak.Charged (occupationWord lowerLetter)
noncomputable section

/-- Literal reflection descendants append the exact horizontal relation. -/
theorem horizontalReflection_indexedWord (k : ℂ) (d : ℕ) (w : List (Fin 3×ℕ)) :
    horizontalReflection k d (indexedWord k (-(d : ℂ)-2) w) =
      indexedWord k d (w ++ List.replicate (d+1) (1,0)) := by
  rw [indexedWord,horizontalReflection,universalMap_word]
  simp only [indexedWord,List.map_append,List.map_replicate,NormalOrdering.currentWord_append,
    horizontalState,lowerLetter,Module.End.mul_apply]
  rfl

/-- Adjoint creation modes kill the actual horizontal reflected highest state. -/
theorem horizontalState_reflection_adjoint (k : ℂ) (d : ℕ)
    (a : Fin 3) (n : ℤ) (hn : IsLower a n) :
    mode k d (adjointColour a) (-n) (horizontalState k d (d+1)) = 0 := by
  have hp : ¬IsLower (adjointColour a) (-n) := by
    fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
  have hh : ¬(-n=0 ∧ adjointColour a=2) := by
    fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
  simpa only [if_neg hh] using (horizontalState_reflection_highest k d).modes _ _ hp

/-- The reflected highest state lies in the full actual canonical radical. -/
theorem horizontalState_reflection_radical (k : ℂ) (d : ℕ) :
    contravariant k d (horizontalState k d (d+1)) = 0 := by
  apply (occupationBasis k d).ext
  intro e
  rw [occupationBasis_apply]
  cases hw : occupationWord e with
  | nil =>
    change contravariant k d (horizontalState k d (d+1)) (highestVector k d) = 0
    rw [contravariant_highest_right,horizontalState_succ]
    exact highestCoordinate_creation k d 1 0 (by simp [IsLower]) _
  | cons an w =>
    have hl := Wak.Charged.occupationWord_lower e an (by rw [hw]; simp)
    change contravariant k d (horizontalState k d (d+1)) (mode k d an.1 an.2 _) = 0
    rw [contravariant_symm,contravariant_adj,horizontalState_reflection_adjoint k d _ _ hl,map_zero]

/-- Every actual reflected Verma descendant is radical. -/
theorem horizontalReflection_radical (k : ℂ) (d : ℕ) (v : Verma k (-(d : ℂ)-2)) :
    contravariant k d (horizontalReflection k d v) = 0 := by
  have he : (contravariant k d).comp (horizontalReflection k d) = 0 := by
    apply (occupationBasis k (-(d : ℂ)-2)).ext
    intro e
    simp only [LinearMap.comp_apply,occupationBasis_apply,horizontalReflection,
      universalMap_word,LinearMap.zero_apply]
    exact descendant_radical k d _ _ (horizontalState_reflection_radical k d)
  exact LinearMap.congr_fun he v

/-- The exact horizontal raising coefficient at arbitrary complex highest weight. -/
theorem horizontalState_raising (k h : ℂ) (r : ℕ) :
    mode k h 0 0 (horizontalState k h (r+1)) =
      (((r+1 : ℕ) : ℂ) * (h-r)) • horizontalState k h r := by
  induction r with
  | zero =>
    rw [horizontalState_succ]
    have hc := HighestNormalOrdering.push (mode k h) k (mode_comm k h)
      0 1 0 0 (highestVector k h)
    have he : mode k h 0 0 (highestVector k h) = 0 := by
      simpa using mode_highest k h 0 0 (by simp [IsLower])
    have hh : mode k h 2 0 (highestVector k h) = h • highestVector k h := by
      simpa using mode_highest k h 2 0 (by simp [IsLower])
    simpa [horizontalState_zero,he,hh,Fin.sum_univ_three,fabc] using hc
  | succ r ih =>
    rw [horizontalState_succ]
    have hc := HighestNormalOrdering.push (mode k h) k (mode_comm k h)
      0 1 0 0 (horizontalState k h (r+1))
    simp only [add_zero,ih,map_smul,horizontalState_charge] at hc
    simp only [Fin.sum_univ_three,fabc] at hc
    simp only [zero_smul,one_smul,zero_add,add_zero,zero_mul,smul_zero] at hc
    simp only [horizontalState_charge,ite_true,Int.cast_zero,Nat.cast_zero,zero_mul,zero_smul,add_zero] at hc
    rw [hc]
    rw [← horizontalState_succ,← add_smul]
    congr 1
    push_cast
    ring

/-- The exact canonical horizontal norm, with no unspecified scalar. -/
theorem horizontalState_norm (k h : ℂ) (r : ℕ) :
    contravariant k h (horizontalState k h r) (horizontalState k h r) =
      (r.factorial : ℂ) * (descPochhammer ℂ r).eval h := by
  induction r with
  | zero => simp [horizontalState_zero,contravariant_normalized]
  | succ r ih =>
    rw [horizontalState_succ,contravariant_adj]
    change contravariant k h (horizontalState k h r)
      (mode k h 0 0 (horizontalState k h (r+1))) = _
    rw [horizontalState_raising,map_smul,smul_eq_mul,ih,
      descPochhammer_succ_eval,Nat.factorial_succ]
    push_cast
    ring

end
end VOA.AffineVOA.HighestModule
