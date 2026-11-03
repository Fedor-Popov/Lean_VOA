/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaCreationSpan

/-!
# Finite straightening without a sorted-order assumption

Occupation words use one arbitrary representative of each finite multiset.
Adjacent exchanges differ by a shorter creation word. Induction on length
therefore proves spanning for exactly those representatives, regardless of
the order chosen by Multiset.toList.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter)
noncomputable section

/-- Indexed creation operator, including F_0 at colour one and depth zero. -/
def creationMode (k h : ℂ) (v : Fin 3×ℕ) : End ℂ (Verma k h) :=
  mode k h (lowerLetter v).1 (lowerLetter v).2

/-- Actual state of a literal list of creation occupations. -/
def indexedWord (k h : ℂ) (w : List (Fin 3×ℕ)) : Verma k h :=
  currentWord (mode k h) (w.map lowerLetter) (highestVector k h)

/-- Prefixing a list applies its indexed creation operator. -/
theorem indexedWord_cons (k h : ℂ) (v : Fin 3×ℕ) (w : List (Fin 3×ℕ)) :
    indexedWord k h (v::w)=creationMode k h v (indexedWord k h w) := rfl

/-- The depth of the bracket of two creation letters. A Cartan letter
contributes one extra unit because its first creation mode is H_-1. -/
def bracketDepth (a b : Fin 3×ℕ) : ℕ := a.2+b.2+if a.1=2 ∨ b.1=2 then 1 else 0

/-- Creation commutators are linear combinations of single creation modes.
There is no central contribution, including the possible pair F_0,F_0. -/
theorem creationMode_comm (k h : ℂ) (a b : Fin 3×ℕ) :
    ⁅creationMode k h a,creationMode k h b⁆=
      ∑ c : Fin 3,fabc a.1 b.1 c • creationMode k h (c,bracketDepth a b) := by
  rcases a with ⟨a,i⟩; rcases b with ⟨b,j⟩
  simp only [creationMode,lowerLetter,mode_comm]
  fin_cases a <;> fin_cases b <;>
    simp [fabc,kappa,bracketDepth,Fin.sum_univ_succ,lowerLetter,Nat.cast_add,
      Nat.cast_one,neg_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] <;> omega

/-- Exchanging adjacent letters in any context adds only one shorter
bracket word, with the actual sl2 structure constants. -/
theorem indexedWord_adjacent (k h : ℂ) (pre post : List (Fin 3×ℕ)) (a b : Fin 3×ℕ) :
    indexedWord k h (pre++a::b::post)-indexedWord k h (pre++b::a::post)=
      ∑ c : Fin 3,fabc a.1 b.1 c • indexedWord k h (pre++(c,bracketDepth a b)::post) := by
  induction pre with
  | nil =>
      have hc := congrArg (fun T : End ℂ (Verma k h) => T (indexedWord k h post))
        (creationMode_comm k h a b)
      dsimp only at hc
      simpa only [List.nil_append,indexedWord_cons,Ring.lie_def,
        LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] using hc
  | cons x pre ih =>
      simp only [List.cons_append,indexedWord_cons]
      rw [← map_sub,ih,map_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [map_smul])

/-- Span of the exact fixed occupation representatives used in the
independence theorem, with no hidden sorting convention. -/
def occupationSpan (k h : ℂ) : Submodule ℂ (Verma k h) :=
  Submodule.span ℂ (Set.range (fun d : Occupation =>
    currentWord (mode k h) (occupationWord d) (highestVector k h)))

/-- Once all shorter words are in a subspace, permuting a word changes its
state by an element of that subspace. The prefix is retained during induction. -/
theorem perm_difference_mem (k h : ℂ) (S : Submodule ℂ (Verma k h))
    (N : ℕ) (hs : ∀ w : List (Fin 3×ℕ),w.length<N → indexedWord k h w∈S)
    {u v : List (Fin 3×ℕ)} (hp : u.Perm v) :
    ∀ pre : List (Fin 3×ℕ),pre.length+u.length≤N →
      indexedWord k h (pre++u)-indexedWord k h (pre++v)∈S := by
  induction hp with
  | nil => intro pre hb; rw [sub_self]; exact S.zero_mem
  | cons a hp ih =>
      intro pre hb
      simpa only [List.append_assoc,List.singleton_append] using
        ih (pre++[a]) (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *; omega)
  | swap a b w =>
      intro pre hb
      rw [indexedWord_adjacent]
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
theorem indexedWord_mem_occupationSpan (k h : ℂ) (w : List (Fin 3×ℕ)) :
    indexedWord k h w∈occupationSpan k h := by
  have H : ∀ n : ℕ,∀ w : List (Fin 3×ℕ),w.length=n → indexedWord k h w∈occupationSpan k h := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      let d : Occupation := (w : Multiset (Fin 3×ℕ)).toFinsupp
      have hp : w.Perm d.toMultiset.toList := by
        apply Multiset.coe_eq_coe.mp
        simp only [Multiset.coe_toList,d,Multiset.toFinsupp_toMultiset]
      have hd : indexedWord k h d.toMultiset.toList∈occupationSpan k h :=
        Submodule.subset_span ⟨d,rfl⟩
      have he := perm_difference_mem k h (occupationSpan k h) n
        (fun v hv => ih v.length hv v rfl) hp [] (by simpa using hn.le)
      simpa only [List.nil_append,sub_add_cancel] using (occupationSpan k h).add_mem he hd
  exact H w.length w rfl

/-- Recover the occupation depth from any genuine creation letter. -/
def lowerIndex (an : Fin 3×ℤ) : Fin 3×ℕ :=
  (an.1,(-an.2-if an.1=1 then 0 else 1).toNat)

/-- The index conversion recovers every negative current and F_0 exactly. -/
theorem lowerLetter_lowerIndex (an : Fin 3×ℤ) (ha : IsLower an.1 an.2) :
    lowerLetter (lowerIndex an)=an := by
  rcases an with ⟨a,n⟩
  simp only [lowerIndex,lowerLetter,Prod.mk.injEq,true_and]
  by_cases h : a=1
  · simp only [h,if_true,sub_zero]
    simp only [IsLower] at ha
    omega
  · simp only [h,if_false]
    simp only [IsLower] at ha
    omega

/-- Every literal creation word can be written in indexed form, with no
reordering and no change to its state. -/
theorem lower_word_indexed (k h : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    indexedWord k h (w.map lowerIndex)=currentWord (mode k h) w (highestVector k h) := by
  rw [indexedWord,List.map_map]
  congr 2
  induction w with
  | nil => rfl
  | cons an w ih =>
      simp only [List.map_cons,Function.comp_apply]
      rw [lowerLetter_lowerIndex an (hw an (by simp)),ih (fun bn hb => hw bn (by simp [hb]))]

/-- The fixed occupation family spans the actual Verma quotient. This uses
finite permutation straightening, so arbitrary representative order is harmless. -/
theorem occupationSpan_eq_top (k h : ℂ) : occupationSpan k h=⊤ := by
  have hs : creationSpan k h≤occupationSpan k h := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨w,hw,rfl⟩ := hv
    rw [← lower_word_indexed k h w hw]
    exact indexedWord_mem_occupationSpan k h _
  rw [creationSpan_eq_top] at hs
  exact top_unique hs

/-- The genuine PBW basis of the actual affine Verma module at every complex
level and highest weight, including the critical level and horizontal F_0 powers. -/
def occupationBasis (k h : ℂ) : Module.Basis Occupation ℂ (Verma k h) :=
  Module.Basis.mk (occupationWords_independent k h)
    (by change ⊤≤occupationSpan k h; rw [occupationSpan_eq_top])

/-- The basis vectors are precisely the already specified occupation words. -/
theorem occupationBasis_apply (k h : ℂ) (d : Occupation) :
    occupationBasis k h d=currentWord (mode k h) (occupationWord d) (highestVector k h) :=
  Module.Basis.mk_apply _ _ d

end
end VOA.AffineVOA.HighestModule
