/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaStraightening

/-!
# Actual highest-coordinate functional and affine word weights

Energy alone does not separate the highest line from horizontal F_0 powers.
The principal degree 2*energy-charge does. This constructs the normalized
highest coefficient in the actual Verma basis and proves it kills every
nonempty creation word, without excluding critical level.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open NormalOrdering (currentWord)
open HighestNormalOrdering
open Wak.Charged (Occupation occupationWord colourCharge wordEnergy wordCharge wordPrincipal)
noncomputable section

/-- H_0 measures twice the root charge of each current. -/
theorem cartan_mode_comm (k h : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅mode k h 2 0,mode k h a n⁆=(2*(colourCharge a : ℂ)) • mode k h a n := by
  rw [mode_comm]
  fin_cases a <;> simp [fabc,kappa,colourCharge,Fin.sum_univ_three]

/-- Every literal current word has its exact relative energy under the
affine derivation D=-energy. -/
theorem degree_word (k h : ℂ) (w : List (Fin 3×ℤ)) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant)
      (currentWord (mode k h) w (highestVector k h))=
      (-(wordEnergy w : ℂ)) • currentWord (mode k h) w (highestVector k h) := by
  induction w with
  | nil => simp [currentWord,wordEnergy,degree_highest]
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ (Verma k h) =>
        T (currentWord (mode k h) w (highestVector k h))) (degree_mode_comm k h an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      simp only [currentWord,Module.End.mul_apply,wordEnergy,List.map_cons,List.sum_cons,
        Int.cast_add,Int.cast_neg,neg_add,neg_neg,add_smul]
      exact hc

/-- Every current word has highest Cartan weight plus twice its root charge. -/
theorem cartan_word (k h : ℂ) (w : List (Fin 3×ℤ)) :
    mode k h 2 0 (currentWord (mode k h) w (highestVector k h))=
      (h+2*(wordCharge w : ℂ)) • currentWord (mode k h) w (highestVector k h) := by
  induction w with
  | nil => simpa [currentWord,wordCharge] using mode_highest k h 2 0 (by simp [IsLower])
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ (Verma k h) =>
        T (currentWord (mode k h) w (highestVector k h))) (cartan_mode_comm k h an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      simp only [currentWord,Module.End.mul_apply,wordCharge,List.map_cons,List.sum_cons,Int.cast_add]
      rw [hc]
      simp only [wordCharge,Int.cast_list_sum]
      module

/-- Principal degree is twice energy minus root charge; its highest
normalization removes the scalar Cartan weight. -/
def principal (k h : ℂ) : End ℂ (Verma k h) :=
  (-2 : ℂ) • rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant)-
    (1/2 : ℂ) • mode k h 2 0+(h/2) • 1

/-- The principal eigenvalue of a literal word is its exact integer weight. -/
theorem principal_word (k h : ℂ) (w : List (Fin 3×ℤ)) :
    principal k h (currentWord (mode k h) w (highestVector k h))=
      (wordPrincipal w : ℂ) • currentWord (mode k h) w (highestVector k h) := by
  have he : wordPrincipal w=2*wordEnergy w-wordCharge w := by
    induction w with
    | nil => rfl
    | cons an w ih => simp [wordPrincipal,wordEnergy,wordCharge,ih]; ring
  simp only [principal,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,degree_word,cartan_word,he,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  module

/-- Extract the coefficient of the genuine highest vector in the proved
occupation basis. This is a complex-linear, not conjugate-linear, functional. -/
def highestCoordinate (k h : ℂ) : Module.Dual ℂ (Verma k h) :=
  (Finsupp.lapply (0 : Occupation)).comp (occupationBasis k h).repr.toLinearMap

/-- The empty occupation basis vector is the actual highest vector. -/
theorem occupationBasis_zero (k h : ℂ) : occupationBasis k h 0=highestVector k h := by
  rw [occupationBasis_apply]
  simp [occupationWord,currentWord]

/-- On basis vectors, highest-coordinate extraction is the expected delta. -/
theorem highestCoordinate_basis (k h : ℂ) (d : Occupation) :
    highestCoordinate k h (occupationBasis k h d)=if d=0 then 1 else 0 := by
  change (occupationBasis k h).repr (occupationBasis k h d) 0=_
  rw [Module.Basis.repr_self]
  simp [Finsupp.single_apply,eq_comm]

/-- Highest-coordinate normalization fixes the form normalization later. -/
theorem highestCoordinate_highest (k h : ℂ) : highestCoordinate k h (highestVector k h)=1 := by
  rw [← occupationBasis_zero,highestCoordinate_basis,if_pos rfl]

/-- The principal operator has zero highest coefficient on every vector. -/
theorem highestCoordinate_principal (k h : ℂ) (v : Verma k h) :
    highestCoordinate k h (principal k h v)=0 := by
  have he : (highestCoordinate k h).comp (principal k h)=0 := by
    apply (occupationBasis k h).ext
    intro d
    simp only [LinearMap.comp_apply,LinearMap.zero_apply,occupationBasis_apply,principal_word,map_smul]
    rw [← occupationBasis_apply,highestCoordinate_basis]
    by_cases hd : d=0
    · subst d
      simp [occupationWord,wordPrincipal]
    · simp [hd]
  exact LinearMap.congr_fun he v

/-- Every nonempty creation word has positive principal degree, hence no
highest component. This includes words consisting only of F_0 powers. -/
theorem highestCoordinate_lower_word (k h : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) (hne : w≠[]) :
    highestCoordinate k h (currentWord (mode k h) w (highestVector k h))=0 := by
  have he := highestCoordinate_principal k h (currentWord (mode k h) w (highestVector k h))
  rw [principal_word,map_smul,smul_eq_mul] at he
  have hn : (wordPrincipal w : ℂ)≠0 := by
    exact_mod_cast (fun hz => hne ((Wak.Charged.lower_wordPrincipal w hw).2.mp hz))
  exact (mul_eq_zero.mp he).resolve_left hn

/-- D has zero highest coefficient on every actual vector. -/
theorem highestCoordinate_degree (k h : ℂ) (v : Verma k h) :
    highestCoordinate k h (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v)=0 := by
  have he : (highestCoordinate k h).comp (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant))=0 := by
    apply (occupationBasis k h).ext
    intro d
    simp only [LinearMap.comp_apply,LinearMap.zero_apply,occupationBasis_apply,degree_word,map_smul]
    rw [← occupationBasis_apply,highestCoordinate_basis]
    by_cases hd : d=0
    · subst d; simp [occupationWord,wordEnergy]
    · simp [hd]
  exact LinearMap.congr_fun he v

/-- H_0 acts by h on the highest coefficient, regardless of other weights. -/
theorem highestCoordinate_cartan (k h : ℂ) (v : Verma k h) :
    highestCoordinate k h (mode k h 2 0 v)=h*highestCoordinate k h v := by
  have he : (highestCoordinate k h).comp (mode k h 2 0)=h • highestCoordinate k h := by
    apply (occupationBasis k h).ext
    intro d
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,occupationBasis_apply,cartan_word,map_smul]
    rw [← occupationBasis_apply,highestCoordinate_basis]
    by_cases hd : d=0
    · subst d; simp [occupationWord,wordCharge]
    · simp [hd]
  exact LinearMap.congr_fun he v

end
end VOA.AffineVOA.HighestModule
