/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoHighestProjection

/-!
# Actual two-parameter affine highest-pairing polynomials

Normal forms contain only highest-weight creation words. Their actual
Wakimoto highest projection therefore keeps exactly the empty-word terms.
This constructs one polynomial in level and highest weight for every
finite current word, with its actual evaluation theorem.
-/
namespace VOA.AffineVOA.HighestNormalOrdering
open Module (End)
open MvPolynomial
open NormalOrdering (currentWord)
open scoped BigOperators
noncomputable section

/-- Normal forms supported on genuine highest-weight creation words,
expressed as the span of their unit coefficient terms. -/
def lowerForms : Submodule ℂ NormalForm := Submodule.span ℂ
  {f | ∃ t : Label,(∀ an∈t.2.2,IsLower an.1 an.2) ∧ f=Finsupp.single t 1}

/-- Every scalar multiple of a genuine creation term lies in the span. -/
theorem single_mem_lowerForms (t : Label) (z : ℂ)
    (ht : ∀ an∈t.2.2,IsLower an.1 an.2) : Finsupp.single t z∈lowerForms := by
  have h : Finsupp.single t (1 : ℂ)∈lowerForms :=
    Submodule.subset_span ⟨t,ht,rfl⟩
  simpa using lowerForms.smul_mem z h

/-- Prefixing a creation letter preserves the genuine-creation span. -/
theorem prepend_mem_lowerForms (i : Fin 3×ℤ) (hi : IsLower i.1 i.2)
    (f : NormalForm) (hf : f∈lowerForms) : prepend i f∈lowerForms := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [prepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
      exact single_mem_lowerForms _ _ (by simp only [List.mem_cons]; intro a ha; rcases ha with rfl|ha; exact hi; exact ht a ha)
  | zero => simp
  | add f g hf hg ihf ihg => rw [map_add]; exact lowerForms.add_mem ihf ihg
  | smul z f hf ih => rw [map_smul]; exact lowerForms.smul_mem z ih

/-- Scalar exponents do not affect whether the remaining word is a
highest-weight creation word. -/
theorem scalarShift_mem_lowerForms (p h : ℕ) (f : NormalForm) (hf : f∈lowerForms) :
    scalarShift p h f∈lowerForms := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [scalarShift,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
      exact single_mem_lowerForms _ _ ht
  | zero => simp
  | add f g hf hg ihf ihg => rw [map_add]; exact lowerForms.add_mem ihf ihg
  | smul z f hf ih => rw [map_smul]; exact lowerForms.smul_mem z ih

/-- Recursive mode reduction never introduces noncreation letters in its
normal terms, even when the input mode is positive or horizontal Cartan. -/
theorem modeNormal_mem_lowerForms (a : Fin 3) (m : ℤ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) : modeNormal a m w∈lowerForms := by
  induction w generalizing a m with
  | nil =>
      rw [modeNormal]
      split_ifs with hm hh
      · exact single_mem_lowerForms _ _ (by simpa using hm)
      · exact single_mem_lowerForms _ _ (by simp)
      · exact lowerForms.zero_mem
  | cons i w ih =>
      have hi := hw i (by simp)
      have ht : ∀ an∈w,IsLower an.1 an.2 := fun an han => hw an (by simp [han])
      rw [modeNormal]
      split_ifs with hm hz
      · exact single_mem_lowerForms _ _ (by simpa using And.intro hm (by simpa using hw))
      · apply lowerForms.add_mem
        · apply lowerForms.add_mem
          · exact prepend_mem_lowerForms i hi _ (ih _ _ ht)
          · exact lowerForms.sum_mem (fun c hc => lowerForms.smul_mem _ (ih c _ ht))
        · exact single_mem_lowerForms _ _ ht
      · apply lowerForms.add_mem
        · apply lowerForms.add_mem
          · exact prepend_mem_lowerForms i hi _ (ih _ _ ht)
          · exact lowerForms.sum_mem (fun c hc => lowerForms.smul_mem _ (ih c _ ht))
        · exact lowerForms.zero_mem

/-- The linear current action preserves the genuine-creation normal span. -/
theorem actNormal_mem_lowerForms (a : Fin 3) (m : ℤ) (f : NormalForm)
    (hf : f∈lowerForms) : actNormal a m f∈lowerForms := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [actNormal,Finsupp.linearCombination_single,one_smul]
      exact scalarShift_mem_lowerForms _ _ _ (modeNormal_mem_lowerForms _ _ _ ht)
  | zero => simp
  | add f g hf hg ihf ihg => rw [map_add]; exact lowerForms.add_mem ihf ihg
  | smul z f hf ih => rw [map_smul]; exact lowerForms.smul_mem z ih

/-- The complete reduction of every finite word consists solely of
creation words with their two scalar powers. -/
theorem wordNormal_mem_lowerForms (w : List (Fin 3×ℤ)) : wordNormal w∈lowerForms := by
  induction w with
  | nil => exact single_mem_lowerForms _ _ (by simp)
  | cons an w ih => exact actNormal_mem_lowerForms _ _ _ ih

/-- Retain only empty creation words, recording level as variable zero and
highest Cartan weight as variable one. -/
def highestPolynomial : NormalForm →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Finsupp.linearCombination ℂ (fun t => if t.2.2=[] then X 0^t.1*X 1^t.2.1 else 0)

/-- The actual highest-pairing polynomial of a literal finite current word. -/
def wordPolynomial (w : List (Fin 3×ℤ)) : MvPolynomial (Fin 2) ℂ :=
  highestPolynomial (wordNormal w)

/-- On the proved normal span, the ACTUAL charged Fock highest projection
is evaluation of the two-variable polynomial. -/
theorem highestPolynomial_evaluate (k lam : ℂ) (f : NormalForm) (hf : f∈lowerForms) :
    constantCoeff (evaluate (Wak.Charged.J k lam) k lam (1 : Wak.WakFock) f)=
      MvPolynomial.eval ![k,lam] (highestPolynomial f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [evaluate_single,one_smul,smul_eq_C_mul,map_mul,constantCoeff_C,Wak.Charged.constantCoeff_lower_word k lam _ ht,
        highestPolynomial,Finsupp.linearCombination_single,one_smul]
      split_ifs <;> simp [map_mul,map_pow]
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul z f hf ih => simp only [map_smul,smul_eq_C_mul,map_mul,constantCoeff_C,eval_C,ih]

/-- Every actual finite charged Wakimoto word has the constructed
polynomial highest coefficient at every noncritical level and every
highest weight. This identifies the actual scalar, not an assumed form. -/
theorem wordPolynomial_actual (k lam : ℂ) (hk : k+2≠0) (w : List (Fin 3×ℤ)) :
    constantCoeff (currentWord (Wak.Charged.J k lam) w (1 : Wak.WakFock))=
      MvPolynomial.eval ![k,lam] (wordPolynomial w) := by
  rw [← Wak.Charged.highest_normal_evaluation k lam hk]
  exact highestPolynomial_evaluate k lam _ (wordNormal_mem_lowerForms w)

end
end VOA.AffineVOA.HighestNormalOrdering
