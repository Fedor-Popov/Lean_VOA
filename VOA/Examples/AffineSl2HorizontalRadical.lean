/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumExactSequence
import VOA.Examples.AffineSl2VermaUniformCoordinates

/-!
# The horizontal radical and its exact first norm

The kernel of the actual vacuum projection lies in the canonical radical.
The same horizontal vector at variable highest weight has norm exactly h,
which fixes the normalization of the future first-order restricted form.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter)
noncomputable section

/-- A creation current's Chevalley adjoint kills the horizontal singular
vector, including the adjoint E_0 of horizontal lowering. -/
theorem horizontal_adjoint_creation (k : ℂ) (a : Fin 3) (n : ℤ) (hn : IsLower a n) :
    mode k 0 (adjointColour a) (-n) (horizontalVector k)=0 := by
  have hp : ¬IsLower (adjointColour a) (-n) := by
    fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
  have hh : ¬(-n=0 ∧ adjointColour a=2) := by
    fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
  rw [horizontalVector_mode k _ _ hp,if_neg hh]

/-- The actual horizontal singular vector pairs to zero with every Verma
state, not merely with its own joint block. -/
theorem horizontalVector_radical (k : ℂ) : contravariant k 0 (horizontalVector k)=0 := by
  apply (occupationBasis k 0).ext
  intro d
  rw [occupationBasis_apply]
  cases hw : occupationWord d with
  | nil =>
    change contravariant k 0 (horizontalVector k) (highestVector k 0)=0
    rw [contravariant_highest_right,horizontalVector]
    exact highestCoordinate_creation k 0 1 0 (by simp [IsLower]) _
  | cons an w =>
    have hl := Wak.Charged.occupationWord_lower d an (by rw [hw]; simp)
    change contravariant k 0 (horizontalVector k) (mode k 0 an.1 an.2 _)=0
    rw [contravariant_symm,contravariant_adj,horizontal_adjoint_creation k _ _ hl,map_zero]

/-- Every vector in the embedded weight-minus-two module belongs to the
full canonical radical of the weight-zero Verma form. -/
theorem horizontalEmbedding_radical (k : ℂ) (v : Verma k (-2)) :
    contravariant k 0 (horizontalEmbedding k v)=0 := by
  have he : (contravariant k 0).comp (horizontalEmbedding k)=0 := by
    apply (occupationBasis k (-2)).ext
    intro d
    simp only [LinearMap.comp_apply,horizontalEmbedding_basis,LinearMap.zero_apply]
    exact descendant_radical k 0 _ _ (horizontalVector_radical k)
  exact LinearMap.congr_fun he v

/-- The actual vacuum projection kernel is contained in the canonical
radical; the form can therefore descend to the genuine vacuum quotient. -/
theorem vacuumProjection_ker_radical (k : ℂ) (v : Verma k 0)
    (hv : vacuumProjection k v=0) : contravariant k 0 v=0 := by
  have hm : v∈LinearMap.ker (vacuumProjection k) := hv
  rw [vacuumProjection_ker] at hm
  obtain ⟨u,rfl⟩ := hm
  exact horizontalEmbedding_radical k u

/-- At arbitrary highest weight, the horizontal lowering vector has
canonical squared norm h. Its first variation at h=0 is exactly one. -/
theorem horizontal_norm (k h : ℂ) :
    contravariant k h (mode k h 1 0 (highestVector k h))
      (mode k h 1 0 (highestVector k h))=h := by
  rw [contravariant_adj]
  have hh : mode k h 0 0 (highestVector k h)=0 := by
    simpa using mode_highest k h 0 0 (by simp [IsLower])
  have hc := congrArg (fun T : End ℂ (Verma k h) => T (highestVector k h))
    (mode_comm k h 0 1 0 0)
  dsimp only at hc
  simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,hh,map_zero,sub_zero] at hc
  have hz := mode_highest k h 2 0 (by simp [IsLower])
  have hm : mode k h 0 0 (mode k h 1 0 (highestVector k h))=h • highestVector k h := by
    simpa [Fin.sum_univ_three,fabc,kappa,hz] using hc
  change contravariant k h (highestVector k h)
    (mode k h 0 0 (mode k h 1 0 (highestVector k h)))=h
  rw [hm,map_smul,contravariant_normalized,smul_eq_mul,mul_one]

/-- Literal indexed creation words are embedded by appending one F_0,
with no reordering and no parameter-dependent coefficient. -/
theorem horizontalEmbedding_indexedWord (k : ℂ) (w : List (Fin 3×ℕ)) :
    horizontalEmbedding k (indexedWord k (-2) w)=indexedWord k 0 (w++[(1,0)]) := by
  rw [indexedWord,horizontalEmbedding,universalMap_word]
  simp only [indexedWord,List.map_append,List.map_cons,List.map_nil,
    NormalOrdering.currentWord_append,currentWord,Module.End.mul_apply,Module.End.one_apply]
  rfl

end
end VOA.AffineVOA.HighestModule
