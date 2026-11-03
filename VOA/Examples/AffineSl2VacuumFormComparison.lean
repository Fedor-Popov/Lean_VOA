/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumChevalley

/-!
# Comparing the actual Verma and vacuum bilinear forms

The Chevalley involution converts the opposite-colour Verma adjoint into
minus the same-colour VOA adjoint. The vacuum normalization then determines
all word pairings, with no determinant or nondegeneracy assumption.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst AffineVOA.HighestModule
open NormalOrdering (currentWord)
open Wak.Charged (occupationWord)
noncomputable section

/-- Actual current adjointness in the normalized vacuum form, including
zero modes. Its minus sign is the weight-one VOA convention. -/
theorem vacuumForm_current_adj (k : ℂ) (hk : k+2≠0) (a : Fin 3) (n : ℤ)
    (u v : WakModule k) :
    (universalForm k hk).form (J k a n u) v =
      -(universalForm k hk).form u (J k a (-n) v) := by
  simpa only [smul_currentState_eq_J] using
    LQ43.weightOne_adj (universalForm_invariant k hk)
      (currentState_mem_grading k hk a)
      (LQ43.L1_grading_one k hk _ (currentState_mem_grading k hk a)) n u v

/-- Projection intertwines the literal current notation on the two actual
modules. This includes the horizontal zero modes. -/
theorem vacuumProjection_mode (k : ℂ) (a : Fin 3) (n : ℤ) (v : Verma k 0) :
    vacuumProjection k (HighestModule.mode k 0 a n v)=J k a n (vacuumProjection k v) :=
  vacuumProjection_intertwines k (modeElement a n) v

/-- Vacuum projection preserves the normalized highest-coordinate functional.
Every nonempty creation word has zero vacuum pairing, including words with F0. -/
theorem vacuumForm_highest_coordinate (k : ℂ) (hk : k+2≠0) (v : Verma k 0) :
    (universalForm k hk).form (vacuumA k) (vacuumProjection k v)=
      highestCoordinate k 0 v := by
  have hw : ∀w : List (Fin 3×ℤ),
      (∀an∈w,HighestNormalOrdering.IsLower an.1 an.2) →
      (universalForm k hk).form (vacuumA k)
        (vacuumProjection k (NormalOrdering.currentWord (HighestModule.mode k 0) w (highestVector k 0)))=
      highestCoordinate k 0 (NormalOrdering.currentWord (HighestModule.mode k 0) w (highestVector k 0)) := by
    intro w hl
    cases w with
    | nil =>
      change (universalForm k hk).form (vacuumA k)
        (vacuumProjection k (highestVector k 0))=_
      simp only [NormalOrdering.currentWord,Module.End.one_apply] at *
      rw [vacuumProjection_highest,highestCoordinate_highest]
      exact universalForm_normalized k hk
    | cons an w =>
      rw [highestCoordinate_lower_word k 0 (an::w) hl (by simp)]
      change (universalForm k hk).form (vacuumA k)
        (vacuumProjection k (HighestModule.mode k 0 an.1 an.2 _))=0
      rw [vacuumProjection_mode]
      have hn : 0≤ -an.2 := by
        have hh := hl an (by simp)
        simp only [HighestNormalOrdering.IsLower] at hh
        omega
      have ha := vacuumForm_current_adj k hk an.1 (-an.2) (vacuumA k)
        (vacuumProjection k (NormalOrdering.currentWord (HighestModule.mode k 0) w (highestVector k 0)))
      rw [J_vacuum_nonneg k an.1 hn,map_zero,LinearMap.zero_apply,neg_neg] at ha
      exact neg_eq_zero.mp ha.symm
  have he : ((universalForm k hk).form (vacuumA k)).comp (vacuumProjection k)=
      highestCoordinate k 0 := by
    apply (occupationBasis k 0).ext
    intro d
    simp only [LinearMap.comp_apply,occupationBasis_apply]
    exact hw (occupationWord d) (Wak.Charged.occupationWord_lower d)
  exact LinearMap.congr_fun he v

/-- The actual weight-zero Verma form is exactly the canonical vacuum form
with the Chevalley involution on its first argument. This fixes all signs
and normalization before using the vacuum determinant in rigidity. -/
theorem contravariant_vacuum_form (k : ℂ) (hk : k+2≠0) (u v : Verma k 0) :
    contravariant k 0 u v=(universalForm k hk).form
      (vacuumChevalley k (vacuumProjection k u)) (vacuumProjection k v) := by
  have hw : ∀w : List (Fin 3×ℤ),∀v : Verma k 0,
      contravariant k 0 (NormalOrdering.currentWord (HighestModule.mode k 0) w (highestVector k 0)) v=
      (universalForm k hk).form
        (vacuumChevalley k (vacuumProjection k
          (NormalOrdering.currentWord (HighestModule.mode k 0) w (highestVector k 0)))) (vacuumProjection k v) := by
    intro w
    induction w with
    | nil =>
      intro v
      change contravariant k 0 (highestVector k 0) v=_
      simp only [NormalOrdering.currentWord,Module.End.one_apply]
      rw [contravariant_highest_left,vacuumProjection_highest]
      change highestCoordinate k 0 v=(universalForm k hk).form
        (vacuumChevalley k (vacuumA k)) (vacuumProjection k v)
      rw [vacuumChevalley_vacuum]
      exact (vacuumForm_highest_coordinate k hk v).symm
    | cons an w ih =>
      intro v
      change contravariant k 0 (HighestModule.mode k 0 an.1 an.2 _) v=_
      rw [contravariant_adj,ih,vacuumProjection_mode]
      change _=(universalForm k hk).form
        (vacuumChevalley k (vacuumProjection k (HighestModule.mode k 0 an.1 an.2 _))) _
      rw [vacuumProjection_mode,vacuumChevalley_current,map_neg,
        LinearMap.neg_apply,vacuumForm_current_adj,neg_neg]
  have he : (contravariant k 0).flip v=
      ((universalForm k hk).form.flip (vacuumProjection k v)).comp
        ((vacuumChevalley k).comp (vacuumProjection k)) := by
    apply (occupationBasis k 0).ext
    intro d
    simp only [LinearMap.flip_apply,LinearMap.comp_apply,occupationBasis_apply]
    exact hw (occupationWord d) v
  exact LinearMap.congr_fun he u

end
end VOA.AffineSl2GeneralRigidity
