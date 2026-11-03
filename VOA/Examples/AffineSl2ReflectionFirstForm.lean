/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ReflectionTangent
import VOA.Examples.AffineSl2HorizontalFirstForm

/-! # The reflected first-order form with its exact factorial normalization -/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Polynomial HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter wordPrincipal)
noncomputable section

/-- Exact first horizontal norm at highest weight d. -/
def reflectionNormScale (d : ℕ) : ℂ := ((d+1).factorial : ℂ) * (d.factorial : ℂ)

theorem reflectionNormScale_ne_zero (d : ℕ) : reflectionNormScale d ≠ 0 := by
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The entire highest norm is the usual sl2 falling-factorial polynomial. -/
theorem reflectionPairPolynomial_highest (k : ℂ) (d : ℕ) :
    reflectionPairPolynomial k d [] (List.replicate (d+1) (1,0)) =
      Polynomial.C ((d+1).factorial : ℂ) *
        (descPochhammer ℂ (d+1)).comp (X+Polynomial.C (d : ℂ)) := by
  apply Polynomial.funext
  intro h
  rw [reflectionPairPolynomial_eval]
  simpa [indexedWord,List.map_replicate,lowerLetter,horizontalState] using
    horizontalState_norm k (h+(d : ℂ)) (d+1)

/-- Differentiating once removes precisely the simple horizontal zero. -/
theorem reflectionPairPolynomial_highest_first (k : ℂ) (d : ℕ) :
    (reflectionPairPolynomial k d [] (List.replicate (d+1) (1,0))).coeff 1 =
      reflectionNormScale d := by
  rw [reflectionPairPolynomial_highest,coeff_C_mul,descPochhammer_succ_right]
  simp only [mul_comp,sub_comp,X_comp,natCast_comp]
  have hs : (X + Polynomial.C (d : ℂ) - (d : ℂ[X])) = X := by simp
  rw [hs,coeff_mul_X]
  simp [coeff_zero_eq_eval_zero,descPochhammer_eval_eq_descFactorial,Nat.descFactorial_self,
    reflectionNormScale]

/-- Every nonempty relative creation word is orthogonal to the horizontal
highest vector at all highest weights, by positive principal degree. -/
theorem reflectionPairPolynomial_highest_other (k : ℂ) (d : ℕ) (w : List (Fin 3×ℕ)) (hw : w≠[]) :
    reflectionPairPolynomial k d [] ((w++List.replicate (d+1) (1,0)).map lowerLetter)=0 := by
  apply Polynomial.funext
  intro h
  rw [reflectionPairPolynomial_eval,eval_zero]
  apply contravariant_principal_orthogonal k (h+(d : ℂ)) _ _
    (wordPrincipal ((List.replicate (d+1) (1,0)).map lowerLetter) : ℂ)
    (wordPrincipal ((w++List.replicate (d+1) (1,0)).map lowerLetter) : ℂ)
  · exact principal_word k (h+(d : ℂ)) _
  · exact principal_word k (h+(d : ℂ)) _
  · have hn : wordPrincipal (w.map lowerLetter)≠0 := by
      intro hz
      have he := (Wak.Charged.lower_wordPrincipal _ (indexed_letters_lower w)).2.mp hz
      exact hw (List.map_eq_nil_iff.mp he)
    rw [List.map_append,wordPrincipal_append,Int.cast_add]
    have hc : (wordPrincipal (w.map lowerLetter) : ℂ)≠0 := by exact_mod_cast hn
    intro he
    apply hc
    linear_combination -he

/-- The initial tangent row is exactly the normalized highest-vector row
of M(k,-d-2), multiplied by its proved factorial normalization. -/
theorem reflectionTangentRow_highest (k : ℂ) (d : ℕ) (v : Verma k (-(d : ℂ)-2)) :
    reflectionTangentRow k d [] (horizontalReflection k d v)=
      reflectionNormScale d * contravariant k (-(d : ℂ)-2) (highestVector k (-(d : ℂ)-2)) v := by
  have he : (reflectionTangentRow k d []).comp (horizontalReflection k d)=
      reflectionNormScale d • contravariant k (-(d : ℂ)-2) (highestVector k (-(d : ℂ)-2)) := by
    apply (occupationBasis k (-(d : ℂ)-2)).ext
    intro e
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [occupationBasis_apply]
    change reflectionTangentRow k d []
      (horizontalReflection k d (indexedWord k (-(d : ℂ)-2) e.toMultiset.toList))=_
    rw [horizontalReflection_indexedWord,reflectionTangentRow_indexed]
    by_cases hd : e.toMultiset.toList=[]
    · have hw : occupationWord e=[] := by simp [occupationWord,hd]
      rw [hd,hw]
      simp [reflectionPairPolynomial_highest_first,currentWord,lowerLetter,contravariant_normalized]
    · rw [reflectionPairPolynomial_highest_other k d _ hd,coeff_zero,
        contravariant_highest_left,highestCoordinate_lower_word k (-(d : ℂ)-2) _
          (Wak.Charged.occupationWord_lower e)]
      · simp
      · exact fun hz => hd (List.map_eq_nil_iff.mp hz)
  exact LinearMap.congr_fun he v

/-- Moving one creation current through the first-order form gives its
actual Chevalley adjoint on the embedded module. Derivatives of normal
ordering coefficients vanish by the proved radical cancellation. -/
theorem reflectionTangentRow_adj (k : ℂ) (d : ℕ) (a : Fin 3×ℕ) (u : List (Fin 3×ℕ))
    (v : Verma k (-(d : ℂ)-2)) :
    reflectionTangentRow k d (a::u) (horizontalReflection k d v)=
      reflectionTangentRow k d u (horizontalReflection k d
        (mode k (-(d : ℂ)-2) (adjointColour (lowerLetter a).1) (-(lowerLetter a).2) v)) := by
  have he : (reflectionTangentRow k d (a::u)).comp (horizontalReflection k d)=
      ((reflectionTangentRow k d u).comp (horizontalReflection k d)).comp
        (mode k (-(d : ℂ)-2) (adjointColour (lowerLetter a).1) (-(lowerLetter a).2)) := by
    apply (occupationBasis k (-(d : ℂ)-2)).ext
    intro e
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [occupationBasis_apply]
    change reflectionTangentRow k d (a::u)
      (horizontalReflection k d (indexedWord k (-(d : ℂ)-2) e.toMultiset.toList))=_
    rw [horizontalReflection_indexedWord,reflectionTangentRow_indexed]
    let w := (e.toMultiset.toList++List.replicate (d+1) (1,0)).map lowerLetter
    have hp : reflectionPairPolynomial k d (a::u) w=
        reflectionPairPolynomial k d u
          ((adjointColour (lowerLetter a).1,-(lowerLetter a).2)::w) := by
      apply Polynomial.funext
      intro h
      rw [reflectionPairPolynomial_eval,reflectionPairPolynomial_eval]
      change contravariant k (h+(d : ℂ)) (mode k (h+(d : ℂ)) (lowerLetter a).1 (lowerLetter a).2 _) _=_
      rw [contravariant_adj]
      rfl
    change (reflectionPairPolynomial k d (a::u) w).coeff 1=_
    rw [hp,← reflectionTangentRow_word]
    change reflectionTangentRow k d u
      (rho k d (modeElement (adjointColour (lowerLetter a).1) (-(lowerLetter a).2))
        (indexedWord k d (e.toMultiset.toList++List.replicate (d+1) (1,0))))=_
    rw [← horizontalReflection_indexedWord]
    congr 1
    exact (universalMap_intertwines (rho k d) (horizontalState k d (d+1))
      (horizontalState_reflection_highest k d) _ _).symm
  exact LinearMap.congr_fun he v

/-- The entire first-order horizontal form is the ACTUAL normalized
contravariant form on M(k,-d-2), with exact nonzero factorial scale. -/
theorem reflectionTangentRow_eq_verma (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (v : Verma k (-(d : ℂ)-2)) :
    reflectionTangentRow k d u (horizontalReflection k d v)=
      reflectionNormScale d * contravariant k (-(d : ℂ)-2) (indexedWord k (-(d : ℂ)-2) u) v := by
  induction u generalizing v with
  | nil => exact reflectionTangentRow_highest k d v
  | cons a u ih =>
    rw [reflectionTangentRow_adj,ih,indexedWord_cons,creationMode,contravariant_adj]

/-- Every first horizontal Gram coefficient equals the corresponding
actual reflected-weight pairing, with its exact nonzero factorial factor. -/
theorem reflectionPairPolynomial_first (k : ℂ) (d : ℕ) (u v : List (Fin 3×ℕ)) :
    (reflectionPairPolynomial k d u ((v++List.replicate (d+1) (1,0)).map lowerLetter)).coeff 1=
      reflectionNormScale d * contravariant k (-(d : ℂ)-2) (indexedWord k (-(d : ℂ)-2) u) (indexedWord k (-(d : ℂ)-2) v) := by
  rw [← reflectionTangentRow_indexed,← horizontalReflection_indexedWord,
    reflectionTangentRow_eq_verma]


end
end VOA.AffineVOA.HighestModule
