/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaDescendantGrading

/-!
# The actual horizontal singular embedding and vacuum projection

At highest weight zero, F_0 applied to the highest vector is a nonzero
highest vector of weight minus two. Its universal map embeds the full
Verma module M(k,-2). The actual projection to the universal vacuum module
kills this embedded module. No determinant or character premise is used.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord)
noncomputable section

/-- The horizontal lowering of the actual zero-weight highest vector. -/
def horizontalVector (k : ℂ) : Verma k 0 := mode k 0 1 0 (highestVector k 0)

/-- Horizontal lowering does not kill the universal highest vector. This
uses actual creation independence, not a presumed singular-vector formula. -/
theorem horizontalVector_ne_zero (k : ℂ) : horizontalVector k≠0 := by
  have hi := descendants_independent k 0 (highestVector k 0) (highestVector_ne_zero k 0)
  have he := hi.ne_zero (Finsupp.single (1,0) 1)
  simpa [occupationWord,Wak.Charged.lowerLetter,currentWord,horizontalVector] using he

/-- Every noncreation current acts on the horizontal singular vector by
the highest equations of weight minus two. -/
theorem horizontalVector_mode (k : ℂ) (a : Fin 3) (n : ℤ) (hn : ¬IsLower a n) :
    mode k 0 a n (horizontalVector k)=
      if n=0 ∧ a=2 then (-2 : ℂ) • horizontalVector k else 0 := by
  have hh := mode_highest k 0 a n hn
  simp only [zero_smul,ite_self] at hh
  have hc := congrArg (fun T : End ℂ (Verma k 0) => T (highestVector k 0))
    (mode_comm k 0 a 1 n 0)
  dsimp only at hc
  rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
    hh,map_zero,sub_zero] at hc
  change mode k 0 a n (horizontalVector k)=_ at hc
  rw [hc]
  fin_cases a
  · have hpos : 0≤n := by simp [IsLower] at hn; omega
    have hm := mode_highest k 0 2 n (by simp [IsLower]; omega)
    simp [Fin.sum_univ_three,fabc,kappa,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.zero_apply,hm]
    split_ifs with hz <;> simp [hz]
  · have hpos : 0<n := by simp [IsLower] at hn; omega
    simp [Fin.sum_univ_three,fabc,kappa,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.zero_apply,show n≠0 by omega]
  · have hpos : 0≤n := by simp [IsLower] at hn; omega
    by_cases hz : n=0
    · subst n
      simp [Fin.sum_univ_three,fabc,kappa,LinearMap.add_apply,LinearMap.smul_apply,
        LinearMap.zero_apply,horizontalVector]
    · have hm := mode_highest k 0 1 n (by simp [IsLower]; omega)
      simp [Fin.sum_univ_three,fabc,kappa,LinearMap.add_apply,LinearMap.smul_apply,
        LinearMap.zero_apply,hz,hm]

/-- The horizontal vector is genuinely highest for the full affine Lie
representation, including its central and degree equations. -/
theorem horizontalVector_isHighest (k : ℂ) :
    IsHighest (rho k 0) (horizontalVector k) k (-2) where
  central := rho_central k 0
  degree := by
    have hc := congrArg (fun T : End ℂ (Verma k 0) => T (highestVector k 0))
      (degree_mode_comm k 0 1 0)
    simpa [Ring.lie_def,degree_highest,horizontalVector] using hc
  modes := horizontalVector_mode k

/-- The actual affine-module map from weight minus two to weight zero,
sending its highest vector to F_0 of the target highest vector. -/
def horizontalEmbedding (k : ℂ) : Verma k (-2)→ₗ[ℂ]Verma k 0 :=
  universalMap (rho k 0) (horizontalVector k) (horizontalVector_isHighest k)

/-- Every creation basis vector maps to its literal descendant of F_0. -/
theorem horizontalEmbedding_basis (k : ℂ) (d : Occupation) :
    horizontalEmbedding k (occupationBasis k (-2) d)=
      currentWord (mode k 0) (occupationWord d) (horizontalVector k) := by
  rw [occupationBasis_apply,horizontalEmbedding,universalMap_word]
  rfl

/-- The horizontal singular map is injective, by full descendant
independence on its proved nonzero starting vector. -/
theorem horizontalEmbedding_injective (k : ℂ) : Function.Injective (horizontalEmbedding k) := by
  apply LinearMap.injective_of_linearIndependent (occupationBasis k (-2)).span_eq
  change LinearIndependent ℂ (fun d : Occupation => horizontalEmbedding k (occupationBasis k (-2) d))
  simp_rw [horizontalEmbedding_basis]
  exact descendants_independent k 0 _ (horizontalVector_ne_zero k)

/-- The universal vacuum is an actual highest vector of weight zero in
the full vacuum affine representation. -/
theorem vacuum_isHighest (k : ℂ) :
    IsHighest (AffineLie.vacuumRho kappaForm kappaForm_isInvariant k)
      (AffineLie.vacuumVector kappaForm kappaForm_isInvariant k) k 0 where
  central := AffineLie.vacuum_acts_central kappaForm kappaForm_isInvariant k
  degree := AffineLie.vacuum_ell0_annihilate kappaForm kappaForm_isInvariant k
  modes a n hn := by
    have hnon : 0≤n := by simp [IsLower] at hn; omega
    rw [modeElement,AffineLie.vacuum_pos_annihilate _ _ _ _ _ hnon]
    simp

/-- Canonical actual projection of the zero-weight Verma module onto the
universal affine vacuum module. -/
def vacuumProjection (k : ℂ) : Verma k 0→ₗ[ℂ]WakModule k :=
  universalMap (AffineLie.vacuumRho kappaForm kappaForm_isInvariant k)
    (AffineLie.vacuumVector kappaForm kappaForm_isInvariant k) (vacuum_isHighest k)

/-- The projection preserves the normalized highest/vacuum vector. -/
theorem vacuumProjection_highest (k : ℂ) :
    vacuumProjection k (highestVector k 0)=AffineLie.vacuumVector kappaForm kappaForm_isInvariant k :=
  universalMap_highest _ _ _

/-- The canonical projection intertwines every actual affine operator. -/
theorem vacuumProjection_intertwines (k : ℂ) (x : AffSl2) (v : Verma k 0) :
    vacuumProjection k (rho k 0 x v)=
      AffineLie.vacuumRho kappaForm kappaForm_isInvariant k x (vacuumProjection k v) :=
  universalMap_intertwines _ _ _ _ _

/-- On enveloping representatives the projection is the literal quotient
map. This also proves surjectivity without a dimension argument. -/
theorem vacuumProjection_mk (k : ℂ) (u : U) :
    vacuumProjection k (Submodule.Quotient.mk u)=Submodule.Quotient.mk u := by
  have hl : UniversalEnvelopingAlgebra.lift ℂ
      (AffineLie.vacuumRho kappaForm kappaForm_isInvariant k)=
      Algebra.lsmul ℂ ℂ (WakModule k) := by
    symm
    apply (UniversalEnvelopingAlgebra.lift_unique ℂ _ _).mp
    rfl
  rw [vacuumProjection,universalMap_mk]
  change (UniversalEnvelopingAlgebra.lift ℂ
    (AffineLie.vacuumRho kappaForm kappaForm_isInvariant k) u)
    (AffineLie.vacuumVector kappaForm kappaForm_isInvariant k)=_
  rw [hl]
  change u • (Submodule.Quotient.mk (1 : U) : WakModule k)=_
  rw [← Submodule.Quotient.mk_smul,smul_eq_mul,mul_one]

/-- Every universal vacuum state has an actual weight-zero Verma lift. -/
theorem vacuumProjection_surjective (k : ℂ) : Function.Surjective (vacuumProjection k) := by
  intro v
  obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective
    (AffineLie.vacuumIdeal kappaForm kappaForm_isInvariant k) v
  exact ⟨Submodule.Quotient.mk u,vacuumProjection_mk k u⟩

/-- The defining horizontal singular vector vanishes in the vacuum module. -/
theorem vacuumProjection_horizontal (k : ℂ) : vacuumProjection k (horizontalVector k)=0 := by
  rw [horizontalVector,mode,vacuumProjection_intertwines,vacuumProjection_highest,modeElement]
  exact AffineLie.vacuum_pos_annihilate _ _ _ _ _ (by omega)

/-- The entire embedded weight-minus-two Verma module is killed by the
actual vacuum projection, not just its highest vector. -/
theorem vacuumProjection_horizontalEmbedding (k : ℂ) :
    (vacuumProjection k).comp (horizontalEmbedding k)=0 := by
  apply (occupationBasis k (-2)).ext
  intro d
  simp only [LinearMap.comp_apply,horizontalEmbedding_basis,LinearMap.zero_apply]
  have hw : ∀ w : List (Fin 3×ℤ),vacuumProjection k
      (currentWord (mode k 0) w (horizontalVector k))=0 := by
    intro w
    induction w with
    | nil => exact vacuumProjection_horizontal k
    | cons an w ih =>
      change vacuumProjection k (rho k 0 (modeElement an.1 an.2) _)=0
      rw [vacuumProjection_intertwines,ih,map_zero]
  exact hw _

end
end VOA.AffineVOA.HighestModule
