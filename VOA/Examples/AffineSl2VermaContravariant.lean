/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaDual

/-!
# The actual normalized contravariant form on every affine Verma module

The highest-coordinate functional is highest in the genuine Chevalley dual.
Universal evaluation constructs the form. Symmetry and adjointness are
consequences of that construction, not assumptions about a proposed pairing.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord)
noncomputable section

/-- Creation currents have zero highest coefficient on every vector,
including F_0, because every resulting creation word is nonempty. -/
theorem highestCoordinate_creation (k h : ℂ) (a : Fin 3) (n : ℤ)
    (hn : IsLower a n) (v : Verma k h) :
    highestCoordinate k h (mode k h a n v)=0 := by
  have he : (highestCoordinate k h).comp (mode k h a n)=0 := by
    apply (occupationBasis k h).ext
    intro d
    simp only [LinearMap.comp_apply,LinearMap.zero_apply,occupationBasis_apply]
    exact highestCoordinate_lower_word k h ((a,n)::occupationWord d)
      (by intro an ha; rcases List.mem_cons.mp ha with rfl|ha; exact hn; exact Wak.Charged.occupationWord_lower d an ha)
      (by simp)
  exact LinearMap.congr_fun he v

/-- Except for H_0 itself, every noncreation mode has a genuine creation
mode as its Chevalley adjoint. -/
theorem adjoint_isLower (a : Fin 3) (n : ℤ)
    (hn : ¬IsLower a n) (hh : ¬(n=0 ∧ a=2)) : IsLower (adjointColour a) (-n) := by
  fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega

/-- The actual highest coefficient is a highest vector in the full dual
representation, with the same level, weight and degree. -/
theorem highestCoordinate_isHighest (k h : ℂ) :
    IsHighest (dualRho k h) (highestCoordinate k h) k h where
  central := dualRho_central k h
  degree := by
    rw [dualRho_degree]
    apply LinearMap.ext
    intro v
    exact highestCoordinate_degree k h v
  modes a n hn := by
    rw [dualRho_mode]
    apply LinearMap.ext
    intro v
    by_cases hh : n=0 ∧ a=2
    · rcases hh with ⟨rfl,rfl⟩
      simp only [dualMode,adjointColour,neg_zero,LinearMap.dualMap_apply]
      exact highestCoordinate_cartan k h v
    · rw [if_neg hh]
      exact highestCoordinate_creation k h _ _ (adjoint_isLower a n hn hh) v

/-- The genuine bilinear contravariant form, obtained from the actual
highest-module universal property and its actual dual representation. -/
def contravariant (k h : ℂ) : Verma k h→ₗ[ℂ]Module.Dual ℂ (Verma k h) :=
  universalMap (dualRho k h) (highestCoordinate k h) (highestCoordinate_isHighest k h)

/-- Pairing the highest vector on the left extracts the normalized highest
coordinate on the right. -/
theorem contravariant_highest_left (k h : ℂ) (v : Verma k h) :
    contravariant k h (highestVector k h) v=highestCoordinate k h v := by
  rw [contravariant,universalMap_highest]

/-- The actual highest vector has squared norm one, even when the form at
higher joint weights is degenerate. -/
theorem contravariant_normalized (k h : ℂ) :
    contravariant k h (highestVector k h) (highestVector k h)=1 := by
  rw [contravariant_highest_left,highestCoordinate_highest]

/-- Each current is adjoint to its opposite-index Chevalley current in the
actual form. No conjugation of either parameter occurs. -/
theorem contravariant_adj (k h : ℂ) (a : Fin 3) (n : ℤ) (u v : Verma k h) :
    contravariant k h (mode k h a n u) v=
      contravariant k h u (mode k h (adjointColour a) (-n) v) := by
  have he := universalMap_intertwines (dualRho k h) (highestCoordinate k h)
    (highestCoordinate_isHighest k h) (modeElement a n) u
  change contravariant k h (mode k h a n u)=dualRho k h (modeElement a n) (contravariant k h u) at he
  rw [he,dualRho_mode]
  rfl

/-- The affine derivation is also self-adjoint in the actual form. -/
theorem contravariant_degree_adj (k h : ℂ) (u v : Verma k h) :
    contravariant k h (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) u) v=
      contravariant k h u (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v) := by
  have he := universalMap_intertwines (dualRho k h) (highestCoordinate k h)
    (highestCoordinate_isHighest k h) (AffineLie.ell0 kappaForm kappaForm_isInvariant) u
  change contravariant k h (rho k h _ u)=dualRho k h _ (contravariant k h u) at he
  rw [he,dualRho_degree]
  rfl

/-- A creation mode's adjoint kills the actual highest vector. -/
theorem adjoint_creation_highest (k h : ℂ) (a : Fin 3) (n : ℤ) (hn : IsLower a n) :
    mode k h (adjointColour a) (-n) (highestVector k h)=0 := by
  have hp : ¬IsLower (adjointColour a) (-n) := by
    fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
  rw [mode_highest k h _ _ hp]
  split_ifs with hh
  · have hf : False := by
      fin_cases a <;> simp [IsLower,adjointColour,Fin.ext_iff] at * <;> omega
    exact hf.elim
  · rfl

/-- Pairing the highest vector on the right gives the same highest
coordinate; every nonempty creation word moves to annihilators. -/
theorem contravariant_highest_right (k h : ℂ) (v : Verma k h) :
    contravariant k h v (highestVector k h)=highestCoordinate k h v := by
  have he : (contravariant k h).flip (highestVector k h)=highestCoordinate k h := by
    apply (occupationBasis k h).ext
    intro d
    simp only [LinearMap.flip_apply,occupationBasis_apply]
    cases hw : occupationWord d with
    | nil => simp only [currentWord,Module.End.one_apply,contravariant_normalized,highestCoordinate_highest]
    | cons an w =>
      have hl : IsLower an.1 an.2 := Wak.Charged.occupationWord_lower d an (by rw [hw]; simp)
      rw [highestCoordinate_lower_word k h _ (by simpa only [hw] using Wak.Charged.occupationWord_lower d) (by simp)]
      change contravariant k h (mode k h an.1 an.2 _) (highestVector k h)=0
      rw [contravariant_adj,adjoint_creation_highest k h _ _ hl,map_zero]
  exact LinearMap.congr_fun he v

/-- The actual contravariant form is symmetric, as follows from the proved
adjoint identities, normalization and creation spanning. -/
theorem contravariant_symm (k h : ℂ) (u v : Verma k h) :
    contravariant k h u v=contravariant k h v u := by
  have hw : ∀ w : List (Fin 3×ℤ),∀ v : Verma k h,
      contravariant k h (currentWord (mode k h) w (highestVector k h)) v=
        contravariant k h v (currentWord (mode k h) w (highestVector k h)) := by
    intro w
    induction w with
    | nil => intro v; simp only [currentWord,Module.End.one_apply,contravariant_highest_left,contravariant_highest_right]
    | cons an w ih =>
      intro v
      change contravariant k h (mode k h an.1 an.2 _) v=_
      rw [contravariant_adj,ih,contravariant_adj,adjointColour_involutive,neg_neg]
      rfl
  have he : contravariant k h=(contravariant k h).flip := by
    apply (occupationBasis k h).ext
    intro d
    apply LinearMap.ext
    intro v
    simpa only [occupationBasis_apply,LinearMap.flip_apply] using hw (occupationWord d) v
  exact LinearMap.congr_fun (LinearMap.congr_fun he u) v

/-- The actual radical is stable under every current, using its opposite
adjoint. This is an ordinary submodule statement, not a determinant premise. -/
theorem contravariant_radical_mode (k h : ℂ) (a : Fin 3) (n : ℤ) (u : Verma k h)
    (hu : ∀ v,contravariant k h u v=0) : ∀ v,contravariant k h (mode k h a n u) v=0 := by
  intro v
  rw [contravariant_adj,hu]

end
end VOA.AffineVOA.HighestModule
