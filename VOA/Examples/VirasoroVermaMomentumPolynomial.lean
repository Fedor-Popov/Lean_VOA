/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaTensorFock
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polynomial dependence of Verma creation words on free momentum

All family members evaluate the same Verma module. The coefficient at the
word length is the product of momentum creation operators; projecting away
two bosons leaves a distinct oscillator monomial for each sorted word.
-/
namespace VOA.InverseDS.VirasoroVerma
open Module (End)
open VirModule LeeYangFockExponential LeeYangFockVirasoro LeeYangWardClosure

/-- Multiplication by the polynomial variable shifts a vector coefficient up
one index. We use this explicit rule to track maximal momentum degree. -/
theorem polynomialModule_X_coeff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : PolynomialModule ℂ V) (n : ℕ) :
    ((Polynomial.X : Polynomial ℂ) • q) n=if 0<n then q (n-1) else 0 := by
  rw [← Polynomial.monomial_one_one_eq_X,PolynomialModule.monomial_smul_apply]
  simp only [one_smul,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]

/-- Applying a linear map to a vector polynomial acts separately on every
coefficient; it does not change the momentum degree. -/
theorem polynomialModule_map_coeff {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (q : PolynomialModule ℂ V) (n : ℕ) :
    (PolynomialModule.map ℂ f q) n=f (q n) := rfl

/-- A vector polynomial vanishing at every complex number has all coefficients
zero. Scalar functionals reduce the claim to ordinary polynomial identity. -/
theorem polynomialModule_eq_zero_of_eval {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : PolynomialModule ℂ V) (hq : ∀ z : ℂ, PolynomialModule.eval z q=0) : q=0 := by
  apply Finsupp.ext
  intro n
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (q n)).mp
  intro f
  let p : Polynomial ℂ := PolynomialModule.equivPolynomial (PolynomialModule.map ℂ f q)
  have hp : p=0 := by
    apply Polynomial.funext
    intro z
    have he := PolynomialModule.aeval_equivPolynomial (PolynomialModule.map ℂ f q) z
    simp only [Polynomial.aeval_def,Polynomial.eval₂_id] at he
    have he' : p.eval z=PolynomialModule.eval z (PolynomialModule.map ℂ f q) := by
      simpa [p] using he
    rw [he']
    have hm := PolynomialModule.eval_map ℂ f q z
    change PolynomialModule.eval z (PolynomialModule.map ℂ f q)=f (PolynomialModule.eval z q) at hm
    rw [hm,hq,map_zero]
    simp
  have hh := congrArg (fun p : Polynomial ℂ => p.coeff n) hp
  exact hh

/-- The actual image of a Verma creation word, as a vector polynomial in the
free momentum. Every letter contributes either its fixed mode or one power
of the momentum times its creation coefficient. -/
noncomputable def vermaWordPolynomial (ell p : ℂ) : List ℕ → PolynomialModule ℂ VermaFockFamily
  | [] => PolynomialModule.single ℂ 0 vermaFockFamilyVacuum
  | i::w => PolynomialModule.map ℂ ((vermaFockFamilyData ell p 0).L (-(i:ℤ)-1))
      (vermaWordPolynomial ell p w) +
      (Polynomial.X : Polynomial ℂ) • PolynomialModule.map ℂ (vermaMomentumMode i)
        (vermaWordPolynomial ell p w)

/-- Evaluating the vector polynomial is exactly the universal family map
on the corresponding creation word. This bridges its coefficients to actual
Verma relations, without assuming independence. -/
theorem vermaWordPolynomial_eval (ell p z : ℂ) (w : List ℕ) :
    PolynomialModule.eval z (vermaWordPolynomial ell p w) =
      vermaFockFamilyMap ell p z (negWord (3-24*ell^2) (p^2-2*ell*p) w) := by
  induction w with
  | nil => simp [vermaWordPolynomial,PolynomialModule.eval_single,vermaFockFamilyMap_highest]
  | cons i w ih =>
    rw [vermaWordPolynomial,map_add,PolynomialModule.eval_smul,
      Polynomial.eval_X,PolynomialModule.eval_map',PolynomialModule.eval_map',ih]
    rw [negWord_cons]
    change _ = universalMap _ _ _ (vermaRho _ _ _ _)
    rw [universalMap_intertwines]
    change _ = virMode (vermaFockFamilyRep ell p z) (-(i:ℤ)-1) _
    rw [vermaFockFamilyRep_mode,vermaFockFamily_negative_linear ell p z]
    rfl

/-- A word of length k has momentum degree at most k. The statement uses
coefficients directly, including the zero-polynomial case. -/
theorem vermaWordPolynomial_coeff_above (ell p : ℂ) (w : List ℕ) (n : ℕ)
    (hn : w.length<n) : vermaWordPolynomial ell p w n=0 := by
  induction w generalizing n with
  | nil => simp [vermaWordPolynomial,PolynomialModule.single_apply,show 0≠n by simpa using Nat.ne_of_lt hn]
  | cons i w ih =>
    rw [vermaWordPolynomial,PolynomialModule.add_apply,polynomialModule_X_coeff,
      polynomialModule_map_coeff,if_pos (by simp only [List.length_cons] at hn; omega),
      polynomialModule_map_coeff,ih n (by simp only [List.length_cons] at hn; omega),
      ih (n-1) (by simp only [List.length_cons] at hn; omega)]
    simp

/-- The exponent vector recording a word's oscillator content. Sorting will
make this content distinguish words uniquely. -/
noncomputable def vermaWordExponent : List ℕ → ((ℕ × Fin 1) →₀ ℕ)
  | [] => 0
  | i::w => Finsupp.single (i,0) 1 + vermaWordExponent w

/-- After symbol projection, the maximal momentum coefficient of any word
is exactly its oscillator monomial with coefficient one. -/
theorem vermaWordPolynomial_top (ell p : ℂ) (w : List ℕ) :
    vermaSymbolProjection (vermaWordPolynomial ell p w w.length) =
      MvPolynomial.monomial (vermaWordExponent w) 1 := by
  induction w with
  | nil => simp [vermaWordPolynomial,PolynomialModule.single_apply,vermaWordExponent,
      vermaSymbolProjection_vacuum]
  | cons i w ih =>
    rw [vermaWordPolynomial,List.length_cons,PolynomialModule.add_apply,
      polynomialModule_map_coeff,vermaWordPolynomial_coeff_above ell p w _ (by omega),
      map_zero,zero_add,polynomialModule_X_coeff,if_pos (by omega),
      Nat.add_sub_cancel,polynomialModule_map_coeff,vermaSymbolProjection_momentum,ih]
    simp [vermaWordExponent,MvPolynomial.monomial_single_add]

/-- Each exponent records how many times the corresponding mode occurs. -/
theorem vermaWordExponent_count (w : List ℕ) (i : ℕ) :
    vermaWordExponent w (i,0)=w.count i := by
  induction w with
  | nil => simp [vermaWordExponent]
  | cons j w ih =>
    by_cases he : i=j
    · subst j; simp [vermaWordExponent,ih,Nat.add_comm]
    · simp [vermaWordExponent,ih,he,Ne.symm he]

/-- Two sorted words with the same oscillator monomial are equal. Equality
of counts first gives a permutation; their common order removes that freedom. -/
theorem vermaWordExponent_injective_sorted {u w : List ℕ}
    (hu : SortedWord u) (hw : SortedWord w) (he : vermaWordExponent u=vermaWordExponent w) :
    u=w := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hba hab) hu hw
  apply List.perm_iff_count.mpr
  intro i
  have hh := congrArg (fun x => x (i,0)) he
  simpa only [vermaWordExponent_count] using hh

/-- At the maximal allowed word length, extracting a chosen oscillator
monomial selects exactly its sorted word. Shorter words contribute zero. -/
theorem vermaWordPolynomial_top_selector (ell p : ℂ) (K : ℕ) (u w : List ℕ)
    (hu : SortedWord u) (hw : SortedWord w) (huK : u.length≤K) (hwK : w.length=K) :
    MvPolynomial.coeff (vermaWordExponent w)
      (vermaSymbolProjection (vermaWordPolynomial ell p u K)) = if u=w then 1 else 0 := by
  classical
  by_cases he : u=w
  · subst u
    rw [← hwK,vermaWordPolynomial_top]
    simp
  · rw [if_neg he]
    by_cases hl : u.length=K
    · rw [← hl,vermaWordPolynomial_top,MvPolynomial.coeff_monomial]
      exact if_neg (fun he' => he (vermaWordExponent_injective_sorted hu hw he'))
    · rw [vermaWordPolynomial_coeff_above ell p u K (by omega),map_zero]
      simp

/-- In any vanishing finite polynomial relation, each word of maximal
length has zero coefficient, selected by its unique top oscillator monomial. -/
theorem vermaWordPolynomial_max_coeff (ell p : ℂ) (K : ℕ)
    (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hs : ∀ w ∈ s, SortedWord w) (hl : ∀ w ∈ s, w.length≤K)
    (he : ∑ w ∈ s, coef w • vermaWordPolynomial ell p w=0)
    (w : List ℕ) (hw : w∈s) (hwK : w.length=K) : coef w=0 := by
  classical
  let C : PolynomialModule ℂ VermaFockFamily →ₗ[ℂ] VermaFockFamily :=
    { toFun := fun q => q K
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let E := (MvPolynomial.lcoeff ℂ (vermaWordExponent w)).comp (vermaSymbolProjection.comp C)
  have hh := congrArg E he
  simp only [map_sum,map_smul,map_zero,smul_eq_mul] at hh
  change (∑ u ∈ s, coef u * MvPolynomial.coeff (vermaWordExponent w)
    (vermaSymbolProjection (vermaWordPolynomial ell p u K)))=0 at hh
  have heq : (∑ u ∈ s, coef u * MvPolynomial.coeff (vermaWordExponent w)
      (vermaSymbolProjection (vermaWordPolynomial ell p u K)))=coef w := by
    rw [Finset.sum_eq_single w]
    · rw [vermaWordPolynomial_top_selector ell p K w w (hs w hw) (hs w hw) (hl w hw) hwK]
      simp
    · intro u hu huw
      rw [vermaWordPolynomial_top_selector ell p K u w (hs u hu) (hs w hw) (hl u hu) hwK]
      simp [huw]
    · exact fun h => (h hw).elim
  rwa [heq] at hh

/-- Removing the maximal-length terms successively proves independence of
all sorted word polynomials. This argument treats finite relations only. -/
theorem vermaWordPolynomial_coef_zero (ell p : ℂ) (K : ℕ)
    (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hs : ∀ w ∈ s, SortedWord w) (hl : ∀ w ∈ s, w.length≤K)
    (he : ∑ w ∈ s, coef w • vermaWordPolynomial ell p w=0) :
    ∀ w ∈ s, coef w=0 := by
  classical
  induction K generalizing s with
  | zero =>
    intro w hw
    exact vermaWordPolynomial_max_coeff ell p 0 s coef hs hl he w hw (by have := hl w hw; omega)
  | succ K ih =>
    have ht := vermaWordPolynomial_max_coeff ell p (K+1) s coef hs hl he
    let t := s.filter (fun w => w.length≤K)
    have het : ∑ w ∈ t, coef w • vermaWordPolynomial ell p w=0 := by
      rw [Finset.sum_filter]
      have heq : (∑ w ∈ s, if w.length≤K then coef w • vermaWordPolynomial ell p w else 0) =
          ∑ w ∈ s, coef w • vermaWordPolynomial ell p w := by
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hh : w.length≤K
        · simp [hh]
        · simp [hh,ht w hw (by have := hl w hw; omega)]
      exact heq.trans he
    have hi := ih t (fun w hw => hs w (Finset.mem_filter.mp hw).1)
      (fun w hw => (Finset.mem_filter.mp hw).2) het
    intro w hw
    by_cases hh : w.length≤K
    · exact hi w (Finset.mem_filter.mpr ⟨hw,hh⟩)
    · exact ht w hw (by have := hl w hw; omega)

/-- An actual relation in a Verma module gives a polynomial relation, since
it evaluates to zero in every member of the same fixed-weight Fock family. -/
theorem verma_relation_polynomial (ell p : ℂ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (he : ∑ w ∈ s, coef w • negWord (3-24*ell^2) (p^2-2*ell*p) w=0) :
    ∑ w ∈ s, coef w • vermaWordPolynomial ell p w=0 := by
  apply polynomialModule_eq_zero_of_eval
  intro z
  have hh := congrArg (vermaFockFamilyMap ell p z) he
  simpa only [map_sum,map_smul,map_zero,vermaWordPolynomial_eval] using hh

/-- ALL ordered negative-mode words, including L₋₁, are independent in
M(c,h) for EVERY complex charge and highest weight. The free-momentum
family separates their highest polynomial coefficients without a PBW axiom. -/
theorem verma_negWord_coef_zero (c h : ℂ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hs : ∀ w ∈ s, SortedWord w)
    (he : ∑ w ∈ s, coef w • negWord c h w=0) : ∀ w ∈ s, coef w=0 := by
  obtain ⟨ell,p,hc,hh⟩ := exists_vermaFockFamily_parameters c h
  subst c
  subst h
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨w,hw,hm⟩ := s.exists_max_image List.length hne
    exact vermaWordPolynomial_coef_zero ell p w.length s coef hs hm
      (verma_relation_polynomial ell p s coef he)

/-- Transport finite-relation independence through any injective indexing
of sorted words, so later basis index types need no repeated argument. -/
theorem verma_negWord_coef_zero_indexed {ι : Type*} (v : ι → List ℕ)
    (hinj : Function.Injective v) (hv : ∀ i, SortedWord (v i))
    (c h : ℂ) (s : Finset ι) (coef : ι → ℂ)
    (he : ∑ i ∈ s, coef i • negWord c h (v i)=0) : ∀ i ∈ s, coef i=0 := by
  classical
  have hc : ∀ i, Function.extend v coef 0 (v i)=coef i := fun i => hinj.extend_apply coef 0 i
  have he' : ∑ w ∈ s.image v, Function.extend v coef 0 w • negWord c h w=0 := by
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    simpa only [hc] using he
  have hs : ∀ w ∈ s.image v, SortedWord w := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact hv i
  intro i hi
  simpa only [hc] using verma_negWord_coef_zero c h (s.image v)
    (Function.extend v coef 0) hs he' (v i) (Finset.mem_image_of_mem v hi)

/-- Global PBW independence for the general Verma module at every (c,h),
including all ordered L₋₁ descendants. No project PBW axiom is used. -/
theorem verma_sortedWord_linearIndependent (c h : ℂ) :
    LinearIndependent ℂ (fun w : {w : List ℕ // SortedWord w} => negWord c h w.val) := by
  rw [linearIndependent_iff']
  intro s coef he i hi
  exact verma_negWord_coef_zero_indexed Subtype.val Subtype.val_injective
    (fun w => w.property) c h s coef he i hi

end VOA.InverseDS.VirasoroVerma
