/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaRadical

/-!
# Actual joint grades and radical membership of independent descendants

Descendant energies and charges add to those of the starting vector. These
statements concern actual simultaneous eigenspaces and the full canonical
radical, and are valid for arbitrary starting vectors in those spaces.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open NormalOrdering (currentWord)
open Wak.Charged (Occupation JointIndex occupationWord wordEnergy wordCharge)
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Wak.Charged.jointIndexFintype n c

/-- A literal word adds its mode energy to the degree of any eigenvector. -/
theorem degree_word_eigen (k h : ℂ) (w : List (Fin 3×ℤ)) (v : Verma k h) (z : ℂ)
    (hv : rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v=z • v) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) (currentWord (mode k h) w v)=
      (z-(wordEnergy w : ℂ)) • currentWord (mode k h) w v := by
  induction w with
  | nil => simpa [currentWord,wordEnergy] using hv
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ (Verma k h) => T (currentWord (mode k h) w v))
        (degree_mode_comm k h an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      simp only [currentWord,Module.End.mul_apply,wordEnergy,List.map_cons,List.sum_cons,Int.cast_add,Int.cast_neg]
      rw [hc]
      simp only [wordEnergy,Int.cast_list_sum]
      module

/-- A literal word adds twice its root charge to any Cartan eigenvalue. -/
theorem cartan_word_eigen (k h : ℂ) (w : List (Fin 3×ℤ)) (v : Verma k h) (z : ℂ)
    (hv : mode k h 2 0 v=z • v) :
    mode k h 2 0 (currentWord (mode k h) w v)=
      (z+2*(wordCharge w : ℂ)) • currentWord (mode k h) w v := by
  induction w with
  | nil => simpa [currentWord,wordCharge] using hv
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ (Verma k h) => T (currentWord (mode k h) w v))
        (cartan_mode_comm k h an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      simp only [currentWord,Module.End.mul_apply,wordCharge,List.map_cons,List.sum_cons,Int.cast_add]
      rw [hc]
      simp only [wordCharge,Int.cast_list_sum]
      module

/-- Occupation descendants lie in the actual joint eigenspace with added
energy and charge, including descendants of horizontal energy zero. -/
theorem descendant_mem_joint (k h : ℂ) (n m : ℕ) (c d : ℤ) (v : Verma k h)
    (hv : v∈jointSpace k h n c) (i : JointIndex m d) :
    currentWord (mode k h) (occupationWord i.val) v∈jointSpace k h (n+m) (c+d) := by
  apply (mem_jointSpace_iff k h (n+m) (c+d) _).mpr
  have hh := (mem_jointSpace_iff k h n c v).mp hv
  constructor
  · rw [degree_word_eigen k h _ v _ hh.1,Wak.Charged.occupationWord_energy,i.property.1,Int.cast_natCast,Nat.cast_add]
    congr 1
    ring
  · rw [cartan_word_eigen k h _ v _ hh.2,Wak.Charged.occupationWord_charge,i.property.2,Int.cast_add]
    congr 1
    ring

/-- Mode stability of the actual radical extends to arbitrary finite words. -/
theorem descendant_radical (k h : ℂ) (w : List (Fin 3×ℤ)) (v : Verma k h)
    (hv : contravariant k h v=0) : contravariant k h (currentWord (mode k h) w v)=0 := by
  induction w with
  | nil => exact hv
  | cons an w ih =>
      apply LinearMap.ext
      intro u
      change contravariant k h (mode k h an.1 an.2 _) u=0
      rw [contravariant_adj,ih]
      rfl

/-- The actual graded descendant, regarded inside its exact joint space. -/
def jointDescendant (k h : ℂ) (n m : ℕ) (c d : ℤ) (v : jointSpace k h n c)
    (i : JointIndex m d) : jointSpace k h (n+m) (c+d) :=
  ⟨currentWord (mode k h) (occupationWord i.val) v,descendant_mem_joint k h n m c d v v.property i⟩

/-- The full finite occupation family of descendants is independent in
its actual joint space whenever the starting vector is nonzero. -/
theorem jointDescendants_independent (k h : ℂ) (n m : ℕ) (c d : ℤ)
    (v : jointSpace k h n c) (hv : v≠0) :
    LinearIndependent ℂ (jointDescendant k h n m c d v) := by
  have hv' : (v : Verma k h)≠0 := fun he => hv (Subtype.ext he)
  have hi := (descendants_independent k h v hv').comp
    (fun i : JointIndex m d => i.val) Subtype.val_injective
  exact LinearIndependent.of_comp (jointSpace k h (n+m) (c+d)).subtype hi

end
end VOA.AffineVOA.HighestModule
