/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumJointBasis

/-!
# A parameter-independent adapted affine PBW basis

The exact sequence supplies a basis at the reference level one and highest
weight zero. Constant creation coordinates transport its literal words to
every level and highest weight. Thus the determinant change of basis is a
single nonzero constant, independent of both variables.
-/
namespace VOA.AffineVOA.HighestModule
open Wak.Charged (Occupation occupationWord lowerLetter)
noncomputable section
local instance adaptedFamilyFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c

/-- Identify actual Verma carriers by their proved occupation coordinates.
This is a vector-space identification, not an intertwiner of all currents. -/
def vermaCoordinateTransport (k h k' h' : ℂ) : Verma k h≃ₗ[ℂ]Verma k' h' :=
  (occupationBasis k h).repr.trans (occupationBasis k' h').repr.symm

/-- Coordinate transport sends each actual PBW vector to the same indexed vector. -/
theorem vermaCoordinateTransport_basis (k h k' h' : ℂ) (d : Occupation) :
    vermaCoordinateTransport k h k' h' (occupationBasis k h d)=occupationBasis k' h' d := by
  simp [vermaCoordinateTransport]

/-- Every literal creation word is transported without changing any coefficients. -/
theorem vermaCoordinateTransport_word (k h k' h' : ℂ) (w : List (Fin 3×ℕ)) :
    vermaCoordinateTransport k h k' h' (indexedWord k h w)=indexedWord k' h' w := by
  apply (occupationBasis k' h').repr.injective
  change (occupationBasis k' h').repr ((occupationBasis k' h').repr.symm
    ((occupationBasis k h).repr (indexedWord k h w)))=_
  rw [LinearEquiv.apply_symm_apply,indexedWord_coordinates_independent k h k' h' w]

/-- The same coordinate identification on a finite joint space. -/
def jointCoordinateTransport (k h k' h' : ℂ) (n : ℕ) (c : ℤ) :
    jointSpace k h n c≃ₗ[ℂ]jointSpace k' h' n c :=
  (jointBasis k h n c).equiv (jointBasis k' h' n c) (Equiv.refl _)

/-- Finite joint transport agrees with the global occupation transport. -/
theorem jointCoordinateTransport_coe (k h k' h' : ℂ) (n : ℕ) (c : ℤ)
    (v : jointSpace k h n c) :
    (jointCoordinateTransport k h k' h' n c v : Verma k' h')=
      vermaCoordinateTransport k h k' h' v := by
  have he : (jointSpace k' h' n c).subtype.comp
      (jointCoordinateTransport k h k' h' n c).toLinearMap=
      (vermaCoordinateTransport k h k' h').toLinearMap.comp (jointSpace k h n c).subtype := by
    apply (jointBasis k h n c).ext
    intro d
    simp only [LinearMap.comp_apply]
    change (((jointBasis k h n c).equiv (jointBasis k' h' n c) (Equiv.refl _))
      (jointBasis k h n c d) : Verma k' h')=vermaCoordinateTransport k h k' h' (jointBasis k h n c d)
    rw [Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply,jointBasis_apply,vermaCoordinateTransport_basis]
  exact LinearMap.congr_fun he v

/-- The literal word for each adapted index. The second group appends F_0
to an ordinary shifted Verma occupation word. -/
def vacuumAdaptedWord {n : ℕ} {c : ℤ} : VacuumAdaptedIndex n c→List (Fin 3×ℕ)
  | Sum.inl i => vacuumLiftWord i.val
  | Sum.inr i => i.val.toMultiset.toList++[(1,0)]

/-- At highest weight zero the adapted basis has exactly these fixed words. -/
theorem vacuumAdaptedBasis_word (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i : VacuumAdaptedIndex n c) :
    (vacuumAdaptedBasis k hk n c i : Verma k 0)=indexedWord k 0 (vacuumAdaptedWord i) := by
  cases i with
  | inl i => exact vacuumAdaptedBasis_left k hk n c i
  | inr i =>
    rw [vacuumAdaptedBasis_right,occupationBasis_apply]
    exact horizontalEmbedding_indexedWord k _

/-- An actual adapted basis at every complex level and highest weight,
obtained from the proved reference basis through constant PBW coordinates. -/
def vacuumAdaptedFamilyBasis (k h : ℂ) (n : ℕ) (c : ℤ) :
    Module.Basis (VacuumAdaptedIndex n c) ℂ (jointSpace k h n c) :=
  (vacuumAdaptedBasis 1 (by norm_num) n c).map (jointCoordinateTransport 1 0 k h n c)

/-- All transported basis vectors remain exactly their original literal
creation words; no level-dependent normalization enters the determinant. -/
theorem vacuumAdaptedFamilyBasis_word (k h : ℂ) (n : ℕ) (c : ℤ)
    (i : VacuumAdaptedIndex n c) :
    (vacuumAdaptedFamilyBasis k h n c i : Verma k h)=indexedWord k h (vacuumAdaptedWord i) := by
  rw [vacuumAdaptedFamilyBasis,Module.Basis.map_apply,jointCoordinateTransport_coe,
    vacuumAdaptedBasis_word,vermaCoordinateTransport_word]

/-- The literal adapted words lie in the same joint space at all parameters. -/
theorem vacuumAdaptedWord_mem_joint (k h : ℂ) (n : ℕ) (c : ℤ)
    (i : VacuumAdaptedIndex n c) : indexedWord k h (vacuumAdaptedWord i)∈jointSpace k h n c := by
  rw [← vacuumAdaptedFamilyBasis_word k h n c i]
  exact (vacuumAdaptedFamilyBasis k h n c i).property

/-- Exact dimension additivity for the actual vacuum quotient, deduced
from an actual basis rather than used as a character assumption. -/
theorem joint_vacuum_dimension (n : ℕ) (c : ℤ) :
    Fintype.card (Wak.Charged.JointIndex n c)=
      Fintype.card (AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c))+
        Fintype.card (Wak.Charged.JointIndex n (c+1)) := by
  have h := Module.finrank_eq_card_basis (vacuumAdaptedFamilyBasis 1 0 n c)
  rw [jointSpace_finrank] at h
  simpa only [Fintype.card_sum] using h

end
end VOA.AffineVOA.HighestModule
