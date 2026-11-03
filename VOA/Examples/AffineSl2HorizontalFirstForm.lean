/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalTangent

/-!
# The horizontal first-order form is the actual weight-minus-two form

Radical cancellation preserves the Chevalley adjoints on the embedded
module. Its highest norm is one. Creation-word induction therefore fixes
all first-order entries, without a determinant or nondegeneracy premise.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Polynomial HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter wordPrincipal)
noncomputable section

/-- Principal degree is self-adjoint in the actual canonical form. The
highest-weight scalar in its definition is bilinear, not conjugated. -/
theorem contravariant_principal_adj (k h : ℂ) (u v : Verma k h) :
    contravariant k h (principal k h u) v=contravariant k h u (principal k h v) := by
  simp only [principal,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,map_add,map_sub,map_smul]
  rw [contravariant_degree_adj,contravariant_adj]
  rfl

/-- Different principal eigenvalues are orthogonal; using principal
degree also separates horizontal descendants at the same energy. -/
theorem contravariant_principal_orthogonal (k h : ℂ) (u v : Verma k h) (a b : ℂ)
    (hu : principal k h u=a • u) (hv : principal k h v=b • v) (hab : a≠b) :
    contravariant k h u v=0 := by
  have he := contravariant_principal_adj k h u v
  rw [hu,hv,map_smul,LinearMap.smul_apply,map_smul,smul_eq_mul,smul_eq_mul] at he
  exact (mul_eq_zero.mp (show (a-b)*contravariant k h u v=0 by linear_combination he)).resolve_left
    (sub_ne_zero.mpr hab)

/-- Principal degrees add when literal words are concatenated. -/
theorem wordPrincipal_append (u v : List (Fin 3×ℤ)) :
    wordPrincipal (u++v)=wordPrincipal u+wordPrincipal v := by
  induction u with
  | nil => simp [wordPrincipal]
  | cons an u ih => simp [wordPrincipal,ih]; ring

/-- Indexed creation letters are genuine creation modes, including F_0. -/
theorem indexed_letters_lower (w : List (Fin 3×ℕ)) :
    ∀an∈w.map lowerLetter,IsLower an.1 an.2 := by
  intro an ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  rcases v with ⟨a,n⟩
  by_cases he : a=1 <;> simp [lowerLetter,IsLower,he] <;> omega

/-- Pairing the horizontal highest vector with itself is the polynomial
X, so the first-order normalization is precisely one. -/
theorem horizontalPairPolynomial_highest (k : ℂ) :
    horizontalPairPolynomial k [] [(1,0)]=X := by
  apply Polynomial.funext
  intro h
  rw [horizontalPairPolynomial_eval,eval_X]
  simpa [indexedWord,lowerLetter,currentWord] using horizontal_norm k h

/-- Every nonempty relative creation word is orthogonal to the horizontal
highest vector at all highest weights, by positive principal degree. -/
theorem horizontalPairPolynomial_highest_other (k : ℂ) (w : List (Fin 3×ℕ)) (hw : w≠[]) :
    horizontalPairPolynomial k [] ((w++[(1,0)]).map lowerLetter)=0 := by
  apply Polynomial.funext
  intro h
  rw [horizontalPairPolynomial_eval,eval_zero]
  apply contravariant_principal_orthogonal k h _ _
    (wordPrincipal ([(1,0)].map lowerLetter) : ℂ)
    (wordPrincipal ((w++[(1,0)]).map lowerLetter) : ℂ)
  · exact principal_word k h _
  · exact principal_word k h _
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
of M(k,-2), with its actual highest coefficient on all vectors. -/
theorem horizontalTangentRow_highest (k : ℂ) (v : Verma k (-2)) :
    horizontalTangentRow k [] (horizontalEmbedding k v)=
      contravariant k (-2) (highestVector k (-2)) v := by
  have he : (horizontalTangentRow k []).comp (horizontalEmbedding k)=
      contravariant k (-2) (highestVector k (-2)) := by
    apply (occupationBasis k (-2)).ext
    intro d
    simp only [LinearMap.comp_apply]
    rw [occupationBasis_apply]
    change horizontalTangentRow k []
      (horizontalEmbedding k (indexedWord k (-2) d.toMultiset.toList))=_
    rw [horizontalEmbedding_indexedWord,horizontalTangentRow_indexed]
    by_cases hd : d.toMultiset.toList=[]
    · have hw : occupationWord d=[] := by simp [occupationWord,hd]
      rw [hd,hw]
      simp [horizontalPairPolynomial_highest,currentWord,lowerLetter,contravariant_normalized]
    · rw [horizontalPairPolynomial_highest_other k _ hd,coeff_zero,
        contravariant_highest_left,highestCoordinate_lower_word k (-2) _
          (Wak.Charged.occupationWord_lower d)]
      · exact fun hz => hd (List.map_eq_nil_iff.mp hz)
  exact LinearMap.congr_fun he v

/-- Moving one creation current through the first-order form gives its
actual Chevalley adjoint on the embedded module. Derivatives of normal
ordering coefficients vanish by the proved radical cancellation. -/
theorem horizontalTangentRow_adj (k : ℂ) (a : Fin 3×ℕ) (u : List (Fin 3×ℕ))
    (v : Verma k (-2)) :
    horizontalTangentRow k (a::u) (horizontalEmbedding k v)=
      horizontalTangentRow k u (horizontalEmbedding k
        (mode k (-2) (adjointColour (lowerLetter a).1) (-(lowerLetter a).2) v)) := by
  have he : (horizontalTangentRow k (a::u)).comp (horizontalEmbedding k)=
      ((horizontalTangentRow k u).comp (horizontalEmbedding k)).comp
        (mode k (-2) (adjointColour (lowerLetter a).1) (-(lowerLetter a).2)) := by
    apply (occupationBasis k (-2)).ext
    intro d
    simp only [LinearMap.comp_apply]
    rw [occupationBasis_apply]
    change horizontalTangentRow k (a::u)
      (horizontalEmbedding k (indexedWord k (-2) d.toMultiset.toList))=_
    rw [horizontalEmbedding_indexedWord,horizontalTangentRow_indexed]
    let w := (d.toMultiset.toList++[(1,0)]).map lowerLetter
    have hp : horizontalPairPolynomial k (a::u) w=
        horizontalPairPolynomial k u
          ((adjointColour (lowerLetter a).1,-(lowerLetter a).2)::w) := by
      apply Polynomial.funext
      intro h
      rw [horizontalPairPolynomial_eval,horizontalPairPolynomial_eval]
      change contravariant k h (mode k h (lowerLetter a).1 (lowerLetter a).2 _) _=_
      rw [contravariant_adj]
      rfl
    change (horizontalPairPolynomial k (a::u) w).coeff 1=_
    rw [hp,← horizontalTangentRow_word]
    change horizontalTangentRow k u
      (rho k 0 (modeElement (adjointColour (lowerLetter a).1) (-(lowerLetter a).2))
        (indexedWord k 0 (d.toMultiset.toList++[(1,0)])))=_
    rw [← horizontalEmbedding_indexedWord]
    congr 1
    exact (universalMap_intertwines (rho k 0) (horizontalVector k)
      (horizontalVector_isHighest k) _ _).symm
  exact LinearMap.congr_fun he v

/-- The entire first-order horizontal form is the ACTUAL normalized
contravariant form on M(k,-2), at every complex level. -/
theorem horizontalTangentRow_eq_verma (k : ℂ) (u : List (Fin 3×ℕ)) (v : Verma k (-2)) :
    horizontalTangentRow k u (horizontalEmbedding k v)=
      contravariant k (-2) (indexedWord k (-2) u) v := by
  induction u generalizing v with
  | nil => exact horizontalTangentRow_highest k v
  | cons a u ih =>
    rw [horizontalTangentRow_adj,ih,indexedWord_cons,creationMode,contravariant_adj]

/-- Every first horizontal Gram coefficient equals the corresponding
actual weight-minus-two pairing, with normalization one and no omitted factor. -/
theorem horizontalPairPolynomial_first (k : ℂ) (u v : List (Fin 3×ℕ)) :
    (horizontalPairPolynomial k u ((v++[(1,0)]).map lowerLetter)).coeff 1=
      contravariant k (-2) (indexedWord k (-2) u) (indexedWord k (-2) v) := by
  rw [← horizontalTangentRow_indexed,← horizontalEmbedding_indexedWord,
    horizontalTangentRow_eq_verma]

end
end VOA.AffineVOA.HighestModule
