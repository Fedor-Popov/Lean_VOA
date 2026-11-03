/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaJointSpaces
import VOA.Examples.AffineSl2WakimotoDescendants

/-!
# All affine creation descendants are independent on every nonzero Verma state

Project the actual tensor realization to its first shifted vacuum factor.
This map is injective on the Verma module and intertwines every creation
mode on arbitrary inputs. The already proved polynomial-domain symbol
argument therefore applies to any nonzero state, including singular states.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak Wak.Charged
noncomputable section

/-- Projection of the tensor representation intertwines each creation
current on EVERY input, not only on the tensor highest vector. -/
theorem tensorProjection_creation (a b c : ℂ) (i : Fin 3) (n : ℤ)
    (hn : IsLower i n) (v : HighestTensorFock) :
    highestTensorProjection (highestTensorJ a b c i n v)=
      shiftedJ 2 a i n (highestTensorProjection v) := by
  change rightVacuumProjection (rightVacuumProjection
    (tensorCurrent (tensorCurrent (shiftedJ 2 a) (shiftedJ 3 b)) (shiftedJ 4 c) i n v))=_
  rw [rightVacuumProjection_current _ 4 (by decide) c i n hn,
    rightVacuumProjection_current _ 3 (by decide) b i n hn]
  rfl

/-- At every level and highest weight there is an injective actual linear
map into one Wakimoto polynomial space, intertwining all creation modes.
It need not intertwine annihilation modes, and no such claim is used. -/
theorem exists_injective_creation_model (k h : ℂ) :
    ∃ a : ℂ,∃ Φ : Verma k h→ₗ[ℂ]WakFock,
      Function.Injective Φ ∧ Φ (highestVector k h)=1 ∧
      ∀ i n,IsLower i n → ∀ v,Φ (mode k h i n v)=shiftedJ 2 a i n (Φ v) := by
  obtain ⟨a,b,c,ha,hb,hc,hk,hh⟩ := exists_highest_tensor_levels k h
  let R := highestTensorRho a b c ha hb hc
  have hv : IsHighest R highestTensorVacuum k h := {
    central := by simpa only [R,highestTensorRho_central,hk]
    degree := by simpa only [R,highestTensorRho_degree,highestTensorDegree_vacuum]
    modes := by
      intro i n hn
      simpa only [R,modeElement,highestTensorRho_mode,highestTensorJ_highest a b c i n hn,hh] }
  let Φ : Verma k h→ₗ[ℂ]WakFock := highestTensorProjection.comp (universalMap R highestTensorVacuum hv)
  have hΦword : ∀ d : Occupation,Φ (occupationBasis k h d)=
      currentWord (shiftedJ 2 a) (occupationWord d) (1 : WakFock) := by
    intro d
    rw [occupationBasis_apply]
    change highestTensorProjection (universalMap R highestTensorVacuum hv _)=_
    rw [universalMap_word]
    simp only [R,modeElement,highestTensorRho_mode]
    exact highestTensorProjection_word a b c _ (occupationWord_lower d)
  refine ⟨a,Φ,?_,?_,?_⟩
  · apply LinearMap.injective_of_linearIndependent (occupationBasis k h).span_eq
    change LinearIndependent ℂ (fun d : Occupation => Φ (occupationBasis k h d))
    simp_rw [hΦword]
    exact shiftedOccupationWord_independent a
  · change highestTensorProjection (universalMap R highestTensorVacuum hv (highestVector k h))=1
    rw [universalMap_highest,highestTensorProjection_vacuum]
  · intro i n hn v
    change highestTensorProjection (universalMap R highestTensorVacuum hv (rho k h (modeElement i n) v))=_
    rw [universalMap_intertwines]
    simp only [R,modeElement,highestTensorRho_mode]
    exact tensorProjection_creation a b c i n hn _

/-- The shifted creation occupation word equals the relabelled negative
Wakimoto word on every starting polynomial, with all indices unchanged. -/
theorem shiftedOccupationWord_descendant (a : ℂ) (d : Occupation) (P : WakFock) :
    currentWord (shiftedJ 2 a) (occupationWord d) P=
      negativeDescendant a (relabelledWord doubleDepth d) P := by
  have hw : ∀ w : List (Fin 3×ℕ),currentWord (Wak.Charged.J a 0)
      (w.map (fun v => (v.1,-(v.2 : ℤ)-1)))=negativeDescendant a w := by
    intro w
    induction w with
    | nil => rfl
    | cons v w ih =>
        rw [List.map_cons,currentWord,ih,J_zero_eq_Jw]
        rfl
  rw [shiftedWord_lower 2 a _ (occupationWord_lower d),occupationWord,List.map_map]
  simp only [Function.comp_def,shifted_lowerLetter_two]
  have he := hw (relabelledWord doubleDepth d)
  simp only [relabelledWord,List.map_map,Function.comp_def] at he
  rw [he]
  rfl

/-- ALL fixed occupation creation words, INCLUDING F_0, acting on ANY
nonzero vector of an ACTUAL affine Verma module are linearly independent.
This is uniform in both complex parameters and needs no singularity premise. -/
theorem descendants_independent (k h : ℂ) (v : Verma k h) (hv : v≠0) :
    LinearIndependent ℂ (fun d : Occupation => currentWord (mode k h) (occupationWord d) v) := by
  obtain ⟨a,Φ,hΦ,hhigh,hmode⟩ := exists_injective_creation_model k h
  have hPv : Φ v≠0 := by intro he; apply hv; exact hΦ (he.trans (map_zero Φ).symm)
  have hw : ∀ w : List (Fin 3×ℤ),(∀ an∈w,IsLower an.1 an.2) → ∀ u : Verma k h,
      Φ (currentWord (mode k h) w u)=currentWord (shiftedJ 2 a) w (Φ u) := by
    intro w
    induction w with
    | nil => intro hl u; rfl
    | cons an w ih =>
        intro hl u
        simp only [currentWord,Module.End.mul_apply]
        rw [hmode an.1 an.2 (hl an (by simp)),ih (fun bn hb => hl bn (by simp [hb]))]
  have hi := negativeDescendants_independent a doubleDepth doubleDepth_injective (Φ v) hPv
  have he : (fun d : Occupation => Φ (currentWord (mode k h) (occupationWord d) v))=
      (fun d : Occupation => negativeDescendant a (relabelledWord doubleDepth d) (Φ v)) := by
    funext d
    rw [hw _ (occupationWord_lower d),shiftedOccupationWord_descendant]
  rw [← he] at hi
  exact LinearIndependent.of_comp Φ hi

end
end VOA.AffineVOA.HighestModule
