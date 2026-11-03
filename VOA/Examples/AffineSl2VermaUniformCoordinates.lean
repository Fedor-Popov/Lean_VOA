/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaStraightening

/-!
# Parameter-independent actual affine creation coordinates

Creation commutators contain neither the level nor the highest weight.
Straightening in the product of all actual Verma modules proves that every
literal creation word has the same PBW coordinates at every parameter.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Wak.Charged (Occupation occupationWord lowerLetter)
noncomputable section

/-- One actual state at each complex level and highest weight. -/
abbrev VermaFamily := ∀ k h : ℂ,Verma k h

/-- The same indexed creation word evaluated in every actual module. -/
def familyWord (w : List (Fin 3×ℕ)) : VermaFamily := fun k h => indexedWord k h w

/-- Adjacent exchanges have constant shorter-word errors throughout the
whole family, because creation commutators have no scalar term. -/
theorem familyWord_adjacent (pre post : List (Fin 3×ℕ)) (a b : Fin 3×ℕ) :
    familyWord (pre++a::b::post)-familyWord (pre++b::a::post)=
      ∑c : Fin 3,fabc a.1 b.1 c • familyWord (pre++(c,bracketDepth a b)::post) := by
  funext k h
  simpa only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,familyWord] using
    indexedWord_adjacent k h pre post a b

/-- Simultaneous span of the fixed occupation representatives. Membership
means that one finite set of constant coefficients works for every parameter. -/
def familySpan : Submodule ℂ VermaFamily := Submodule.span ℂ
  (Set.range (fun d : Occupation => familyWord d.toMultiset.toList))

/-- Once all shorter words are in a subspace, permuting a word changes its
state by an element of that subspace. The prefix is retained during induction. -/
theorem family_perm_difference_mem (S : Submodule ℂ VermaFamily)
    (N : ℕ) (hs : ∀ w : List (Fin 3×ℕ),w.length<N → familyWord w∈S)
    {u v : List (Fin 3×ℕ)} (hp : u.Perm v) :
    ∀ pre : List (Fin 3×ℕ),pre.length+u.length≤N →
      familyWord (pre++u)-familyWord (pre++v)∈S := by
  induction hp with
  | nil => intro pre hb; rw [sub_self]; exact S.zero_mem
  | cons a hp ih =>
      intro pre hb
      simpa only [List.append_assoc,List.singleton_append] using
        ih (pre++[a]) (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *; omega)
  | swap a b w =>
      intro pre hb
      rw [familyWord_adjacent]
      apply S.sum_mem
      intro c hc
      apply S.smul_mem
      apply hs
      simp only [List.length_append,List.length_cons] at *
      omega
  | trans hp hq ihp ihq =>
      intro pre hb
      have hh := S.add_mem (ihp pre hb) (ihq pre (by simpa only [← hp.length_eq] using hb))
      simpa only [sub_add_sub_cancel] using hh

/-- Every indexed creation word lies in the span of its fixed occupation
representatives. Commutator corrections strictly decrease word length. -/
theorem familyWord_mem_span (w : List (Fin 3×ℕ)) :
    familyWord w∈familySpan := by
  have H : ∀ n : ℕ,∀ w : List (Fin 3×ℕ),w.length=n → familyWord w∈familySpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      let d : Occupation := (w : Multiset (Fin 3×ℕ)).toFinsupp
      have hp : w.Perm d.toMultiset.toList := by
        apply Multiset.coe_eq_coe.mp
        simp only [Multiset.coe_toList,d,Multiset.toFinsupp_toMultiset]
      have hd : familyWord d.toMultiset.toList∈familySpan :=
        Submodule.subset_span ⟨d,rfl⟩
      have he := family_perm_difference_mem (familySpan) n
        (fun v hv => ih v.length hv v rfl) hp [] (by simpa using hn.le)
      simpa only [List.nil_append,sub_add_cancel] using (familySpan).add_mem he hd
  exact H w.length w rfl

/-- Actual PBW coordinates extracted from one member of a family. -/
def familyCoordinates (k h : ℂ) : VermaFamily→ₗ[ℂ](Occupation→₀ℂ) where
  toFun v := (occupationBasis k h).repr (v k h)
  map_add' _ _ := map_add _ _ _
  map_smul' z v := (occupationBasis k h).repr.map_smul z (v k h)

/-- A fixed occupation representative has the same unit coordinate at
every level and highest weight. -/
theorem familyCoordinates_basis (k h : ℂ) (d : Occupation) :
    familyCoordinates k h (familyWord d.toMultiset.toList)=Finsupp.single d 1 := by
  change (occupationBasis k h).repr (indexedWord k h d.toMultiset.toList)=_
  change (occupationBasis k h).repr
    (NormalOrdering.currentWord (mode k h) (occupationWord d) (highestVector k h))=_
  rw [← occupationBasis_apply]
  exact (occupationBasis k h).repr_self d

/-- Every actual creation word has parameter-independent coordinates.
This includes horizontal F_0 and arbitrary, unsorted word order. -/
theorem indexedWord_coordinates_independent (k h k' h' : ℂ) (w : List (Fin 3×ℕ)) :
    (occupationBasis k h).repr (indexedWord k h w)=
      (occupationBasis k' h').repr (indexedWord k' h' w) := by
  have hm := familyWord_mem_span w
  change familyCoordinates k h (familyWord w)=familyCoordinates k' h' (familyWord w)
  generalize he : familyWord w=v at hm ⊢
  clear he
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨d,rfl⟩ := hv
    rw [familyCoordinates_basis,familyCoordinates_basis]
  | zero => simp
  | add a b ha hb iha ihb => simp only [map_add,iha,ihb]
  | smul z a ha iha => simp only [map_smul,iha]

end
end VOA.AffineVOA.HighestModule
