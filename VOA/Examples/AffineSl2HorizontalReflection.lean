/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaDescendants
import Mathlib.Algebra.Lie.Sl2

/-! # The genuine horizontal reflection embedding between affine Verma modules -/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering NormalOrdering
open Wak.Charged (Occupation occupationWord lowerLetter occupationCharge oscillatorCharge)
noncomputable section

/-- Every nonzero highest state in an actual Verma module generates an
injective copy of its own actual Verma module. -/
theorem universalMap_into_Verma_injective (k h h' : ℂ) (v : Verma k h)
    (hv : IsHighest (rho k h) v k h') (hne : v ≠ 0) :
    Function.Injective (universalMap (rho k h) v hv) := by
  apply LinearMap.injective_of_linearIndependent (occupationBasis k h').span_eq
  have hi := descendants_independent k h v hne
  convert hi using 1
  funext d
  rw [Function.comp_apply,occupationBasis_apply,universalMap_word]
  rfl

/-- The literal horizontal lowering string in the full Verma module. -/
def horizontalState (k h : ℂ) (r : ℕ) : Verma k h :=
  currentWord (mode k h) (List.replicate r (1,0)) (highestVector k h)

theorem horizontalState_zero (k h : ℂ) : horizontalState k h 0 = highestVector k h := rfl

theorem horizontalState_succ (k h : ℂ) (r : ℕ) :
    horizontalState k h (r+1) = mode k h 1 0 (horizontalState k h r) := by
  simp [horizontalState,List.replicate_succ,currentWord,Module.End.mul_apply]

theorem horizontalState_eq_pow (k h : ℂ) (r : ℕ) :
    horizontalState k h r = (mode k h 1 0 ^ r) (highestVector k h) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [horizontalState_succ,ih,pow_succ',Module.End.mul_apply]

theorem horizontalState_eq_basis (k h : ℂ) (r : ℕ) :
    horizontalState k h r = occupationBasis k h (Finsupp.single (1,0) r) := by
  have hl : (Multiset.replicate r ((1,0) : Fin 3 × ℕ)).toList = List.replicate r (1,0) := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp
    · intro x hx
      exact (Multiset.mem_replicate.mp (by simpa using hx)).2
  simp [horizontalState,occupationBasis_apply,occupationWord,Finsupp.toMultiset_single,
    Multiset.nsmul_singleton,hl,lowerLetter]

theorem horizontalState_ne_zero (k h : ℂ) (r : ℕ) : horizontalState k h r ≠ 0 := by
  rw [horizontalState_eq_basis]
  exact (occupationBasis k h).ne_zero _

theorem horizontalState_charge (k h : ℂ) (r : ℕ) :
    mode k h 2 0 (horizontalState k h r) = (h-2*(r : ℂ)) • horizontalState k h r := by
  rw [horizontalState_eq_basis,cartan_basis]
  congr 1
  simp [occupationCharge,Finsupp.weight_single,oscillatorCharge,nsmul_eq_mul]
  ring

/-- The horizontal operators on a Verma module form an actual sl2 triple,
including highest weight zero. -/
theorem verma_horizontalTriple (k : ℂ) (d : ℕ) :
    IsSl2Triple (mode k d 2 0) (mode k d 0 0) (mode k d 1 0) where
  h_ne_zero := by
    intro hz
    have hh := horizontalState_charge k d (d+1)
    rw [hz,LinearMap.zero_apply] at hh
    have hc : (d : ℂ)-2*((d+1 : ℕ) : ℂ) ≠ 0 := by
      have hp : ((d+2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      intro he
      apply hp
      push_cast at he ⊢
      linear_combination -he
    exact (smul_ne_zero hc (horizontalState_ne_zero k d (d+1))) hh.symm
  lie_e_f := by
    simpa [Fin.sum_univ_succ,fabc] using mode_comm k d 0 1 0 0
  lie_h_e_nsmul := by
    have h := mode_comm k d 2 0 0 0
    norm_num [Fin.sum_univ_succ,fabc] at h
    simpa only [two_smul] using h
  lie_h_f_nsmul := by
    have h := mode_comm k d 2 1 0 0
    norm_num [Fin.sum_univ_succ,fabc] at h
    rw [h]
    rfl

/-- The first horizontal relation is again a highest vector. -/
theorem horizontalState_reflection_raising (k : ℂ) (d : ℕ) :
    mode k d 0 0 (horizontalState k d (d+1)) = 0 := by
  have hp : (verma_horizontalTriple k d).HasPrimitiveVectorWith
      (highestVector k d) (d : ℂ) := {
    ne_zero := highestVector_ne_zero k d
    lie_h := by simpa using mode_highest k d 2 0 (by simp [IsLower])
    lie_e := by simpa using mode_highest k d 0 0 (by simp [IsLower]) }
  have h := hp.lie_e_pow_succ_toEnd_f d
  simpa [horizontalState_eq_pow] using h

/-- Positive affine currents kill every vector in the horizontal string. -/
theorem horizontalState_positive (k h : ℂ) (r : ℕ) :
    ∀ a n, 0 < n → mode k h a n (horizontalState k h r) = 0 := by
  induction r with
  | zero =>
    intro a n hn
    simpa [horizontalState_zero,ne_of_gt hn] using mode_highest k h a n (by
      simp only [IsLower]; omega)
  | succ r ih =>
    intro a n hn
    rw [horizontalState_succ]
    have hc := HighestNormalOrdering.push (mode k h) k (mode_comm k h)
      a 1 n 0 (horizontalState k h r)
    have hs : (∑ c : Fin 3, fabc a 1 c • mode k h c n (horizontalState k h r)) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [ih c n hn,smul_zero]
    simpa only [add_zero,ih a n hn,map_zero,hs,zero_add,if_neg (ne_of_gt hn)] using hc

/-- The horizontal string has zero relative energy. -/
theorem horizontalState_degree (k h : ℂ) (r : ℕ) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) (horizontalState k h r) = 0 := by
  rw [horizontalState_eq_basis,degree_basis]
  simp [Wak.Charged.occupationEnergy,Finsupp.weight_single,Wak.Charged.oscillatorEnergy]

/-- The nonzero horizontal relation is an actual highest vector with reflected
highest weight, at the original relative energy zero. -/
theorem horizontalState_reflection_highest (k : ℂ) (d : ℕ) :
    IsHighest (rho k d) (horizontalState k d (d+1)) k (-(d : ℂ)-2) where
  central := rho_central k d
  degree := horizontalState_degree k d (d+1)
  modes := by
    intro a n hn
    have hn0 : 0 ≤ n := by simp only [IsLower] at hn; omega
    by_cases hnz : n = 0
    · subst n
      fin_cases a
      · simpa using horizontalState_reflection_raising k d
      · simp [IsLower] at hn
      · simpa [Nat.cast_add,Nat.cast_one,show (d : ℂ)-2*((d : ℂ)+1)=-(d : ℂ)-2 by ring]
          using horizontalState_charge k d (d+1)
    · simpa [hnz] using horizontalState_positive k d (d+1) a n (by omega)

/-- The actual injective simple-reflection map, whose cokernel is the
finite-horizontal parabolic module. -/
def horizontalReflection (k : ℂ) (d : ℕ) : Verma k (-(d : ℂ)-2) →ₗ[ℂ] Verma k d :=
  universalMap (rho k d) (horizontalState k d (d+1)) (horizontalState_reflection_highest k d)

theorem horizontalReflection_injective (k : ℂ) (d : ℕ) :
    Function.Injective (horizontalReflection k d) :=
  universalMap_into_Verma_injective k d _ _ (horizontalState_reflection_highest k d)
    (horizontalState_ne_zero k d (d+1))

end
end VOA.AffineVOA.HighestModule
