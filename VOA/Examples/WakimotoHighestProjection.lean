/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestNormalOrdering

/-!
# Actual highest projection in the charged Wakimoto module

The principal grading 2 energy minus ghost charge is positive on every
highest-weight creation mode, including F_0. It proves that nonempty creation
words have zero constant coefficient. This supplies the actual scalar
projection for general two-parameter highest-weight pairings.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Ghost charge of each colour, half its horizontal Cartan shift. -/
def colourCharge (a : Fin 3) : ℤ := if a=0 then 1 else if a=1 then -1 else 0

/-- Actual charged currents have the same ghost charge as their colour. -/
theorem charge_J (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅Dch,J k lam a n⁆=(colourCharge a : ℂ) • J k lam a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [J_E,Dch_lie_Ecur]; norm_num [colourCharge]
  · rw [J_F,F,lie_add,lie_smul,Dch_lie_Fcur,Dch_lie_Gam]
    rw [show colourCharge 1 = -1 by decide,Int.cast_neg,Int.cast_one]
    module
  · rw [J_H,H,lie_add,Dch_lie_Hcur]
    split_ifs
    · rw [lie_smul,lie_one',smul_zero,add_zero]
      rw [show colourCharge 2 = 0 by decide,Int.cast_zero,zero_smul]
    · simp [colourCharge]

/-- Principal degree operator: twice energy minus ghost charge. -/
def principalD : End ℂ WakFock := (2 : ℂ) • Dwt-Dch

/-- Every actual current changes principal degree by its root height. -/
theorem principalD_J (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅principalD,J k lam a n⁆=((-2*n-colourCharge a : ℤ) : ℂ) • J k lam a n := by
  rw [principalD,sub_lie,smul_lie,degree_J,charge_J]
  push_cast
  module

/-- Highest-weight creation modes all have strictly positive principal degree. -/
theorem lower_principal_positive (a : Fin 3) (n : ℤ) (h : IsLower a n) :
    0< -2*n-colourCharge a := by
  rcases fin3_cases a with rfl|rfl|rfl <;> norm_num [IsLower,colourCharge] at h ⊢ <;> omega

/-- An Euler derivative has zero constant coefficient on every polynomial. -/
theorem constantCoeff_Eul (w : Fin 3×ℕ→ℂ) (P : WakFock) :
    constantCoeff (Eul w P)=0 := by
  induction P using MvPolynomial.induction_on with
  | C z => rw [Eul_C',map_zero]
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ,add_zero]
  | mul_X P v ih =>
      rw [Eul_mul,Eul_X,map_add,map_mul,map_mul]
      simp

/-- Principal differentiation also has zero constant coefficient. -/
theorem constantCoeff_principalD (P : WakFock) : constantCoeff (principalD P)=0 := by
  simp only [principalD,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,
    Dwt,Dch,smul_eq_C_mul,map_mul,constantCoeff_C,constantCoeff_Eul,mul_zero,sub_zero]

/-- The principal degree of a finite creation word is additive. -/
def wordPrincipal : List (Fin 3×ℤ)→ℤ
  | [] => 0
  | an::w => -2*an.2-colourCharge an.1+wordPrincipal w

/-- Every literal current word acting on the actual highest polynomial is
an eigenvector of the principal operator, with its computed integer degree. -/
theorem currentWord_principal (k lam : ℂ) (w : List (Fin 3×ℤ)) :
    principalD (currentWord (J k lam) w (1 : WakFock))=
      (wordPrincipal w : ℂ) • currentWord (J k lam) w (1 : WakFock) := by
  induction w with
  | nil => simp [currentWord,wordPrincipal,principalD,Dwt,Dch,Eul_one']
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ WakFock => T (currentWord (J k lam) w 1))
        (principalD_J k lam an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply] at hc
      simp only [currentWord,Module.End.mul_apply,wordPrincipal,Int.cast_add,add_smul]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]

/-- Creation words have nonnegative principal degree, and degree zero
occurs only for the empty word. -/
theorem lower_wordPrincipal (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    0≤wordPrincipal w ∧ (wordPrincipal w=0 ↔ w=[]) := by
  induction w with
  | nil => simp [wordPrincipal]
  | cons an w ih =>
      have hpos := lower_principal_positive an.1 an.2 (hw an (by simp))
      have ht := ih (fun bn hb => hw bn (by simp [hb]))
      simp only [wordPrincipal,List.cons_ne_nil,iff_false]
      constructor <;> omega

/-- The ACTUAL highest projection kills every nonempty creation word,
including horizontal lowering powers, and sends the empty word to one. -/
theorem constantCoeff_lower_word (k lam : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    constantCoeff (currentWord (J k lam) w (1 : WakFock))=if w=[] then 1 else 0 := by
  by_cases he : w=[]
  · subst w; simp [currentWord]
  · rw [if_neg he]
    have hn : (wordPrincipal w : ℂ)≠0 := by
      exact_mod_cast (fun h => he ((lower_wordPrincipal w hw).2.mp h))
    have hc := congrArg constantCoeff (currentWord_principal k lam w)
    rw [constantCoeff_principalD,smul_eq_C_mul,map_mul,constantCoeff_C] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left hn

/-- The actual charged polynomial 1 satisfies the general highest-vector
boundary rule used by two-parameter normal ordering. -/
theorem one_highest_rule (k lam : ℂ) (a : Fin 3) (m : ℤ) (hm : ¬IsLower a m) :
    J k lam a m (1 : WakFock)=if m=0 ∧ a=2 then lam • (1 : WakFock) else 0 := by
  have hm0 : 0≤m := by simp only [IsLower,not_or] at hm; omega
  by_cases he : m=0
  · subst m
    rcases fin3_cases a with rfl|rfl|rfl
    · rw [J_E,E_one,if_neg (by decide : ¬ ((0 : ℤ)=0 ∧ (0 : Fin 3)=2))]
    · exact False.elim (hm (Or.inr ⟨rfl,rfl⟩))
    · rw [J_H,H_one]; norm_num
  · rw [J_one_positive k lam a m (by omega),if_neg (by simp [he])]

/-- General normal ordering evaluates to the actual charged Wakimoto word
at every noncritical level and arbitrary highest weight. -/
theorem highest_normal_evaluation (k lam : ℂ) (hk : k+2≠0)
    (w : List (Fin 3×ℤ)) :
    evaluate (J k lam) k lam (1 : WakFock) (wordNormal w)=
      currentWord (J k lam) w (1 : WakFock) :=
  evaluate_wordNormal _ _ _ _ (J_comm k lam hk) (one_highest_rule k lam) w

end
end VOA.Wak.Charged
