/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Verma

/-!
# Creation-word spanning in the actual affine Verma quotient

Normal ordering makes the span of literal creation words stable under all
currents. The degree operator preserves it as well. Cyclicity of the actual
enveloping quotient therefore proves spanning, without any PBW assumption.
Ordering the creation letters is a separate finite straightening step.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open UniversalEnvelopingAlgebra
open HighestNormalOrdering
open NormalOrdering (currentWord)
noncomputable section

/-- The actual quotient currents obey the affine commutator at every level,
including the critical level. The centre is the prescribed scalar. -/
theorem mode_comm (k h : ℂ) (a b : Fin 3) (m n : ℤ) :
    ⁅mode k h a m,mode k h b n⁆ =
      (∑ c,fabc a b c • mode k h c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ (Verma k h)) else 0 := by
  change ⁅rho k h (modeElement a m),rho k h (modeElement b n)⁆=_
  rw [← (rho k h).map_lie,modeElement,modeElement,AffineLie.affine_bracket,
    map_add]
  congr 1
  · rw [ofLoop_bracket_eq,map_sum]
    exact Finset.sum_congr rfl (fun c _ => by rw [map_smul]; rfl)
  · by_cases hmn : m+n=0
    · rw [if_pos hmn,if_pos hmn,map_smul,rho_central,kappaForm_basis_eq_kappa,
        smul_smul]
      congr 1
      ring
    · rw [if_neg hmn,if_neg hmn,map_zero]

/-- Span of all literal creation words on the highest vector. The letters
may occur in any order; no ordering or independence is built into this definition. -/
def creationSpan (k h : ℂ) : Submodule ℂ (Verma k h) := Submodule.span ℂ
  {v | ∃ w : List (Fin 3×ℤ),(∀ an∈w,IsLower an.1 an.2) ∧
    v=currentWord (mode k h) w (highestVector k h)}

/-- Every genuine creation word belongs to the stated span. -/
theorem creationWord_mem (k h : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    currentWord (mode k h) w (highestVector k h)∈creationSpan k h :=
  Submodule.subset_span ⟨w,hw,rfl⟩

/-- Evaluating a normal form supported on creation words stays in the actual
creation span; the recorded powers of level and weight are only scalars. -/
theorem evaluate_mem_creationSpan (k h : ℂ) (f : NormalForm) (hf : f∈lowerForms) :
    HighestNormalOrdering.evaluate (mode k h) k h (highestVector k h) f∈creationSpan k h := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [evaluate_single,one_smul]
      exact (creationSpan k h).smul_mem _ (creationWord_mem k h _ ht)
  | zero => rw [map_zero]; exact (creationSpan k h).zero_mem
  | add f g hf hg ihf ihg => rw [map_add]; exact (creationSpan k h).add_mem ihf ihg
  | smul z f hf ih => rw [map_smul]; exact (creationSpan k h).smul_mem z ih

/-- Any current word, even one containing annihilation modes, reduces to
creation words in the actual quotient. -/
theorem anyWord_mem_creationSpan (k h : ℂ) (w : List (Fin 3×ℤ)) :
    currentWord (mode k h) w (highestVector k h)∈creationSpan k h := by
  rw [← evaluate_wordNormal (mode k h) k h (highestVector k h)
    (mode_comm k h) (mode_highest k h)]
  exact evaluate_mem_creationSpan k h _ (wordNormal_mem_lowerForms w)

/-- Every current preserves the creation span, by finite normal ordering. -/
theorem mode_creationSpan (k h : ℂ) (a : Fin 3) (n : ℤ)
    {v : Verma k h} (hv : v∈creationSpan k h) : mode k h a n v∈creationSpan k h := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w,hw,rfl⟩ := hv
      exact anyWord_mem_creationSpan k h ((a,n)::w)
  | zero => rw [map_zero]; exact (creationSpan k h).zero_mem
  | add v w hv hw ihv ihw => rw [map_add]; exact (creationSpan k h).add_mem ihv ihw
  | smul z v hv ih => rw [map_smul]; exact (creationSpan k h).smul_mem z ih

/-- The derivation-current commutator in the actual quotient records the
integer mode index, with the derivation convention D=-energy. -/
theorem degree_mode_comm (k h : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant),mode k h a n⁆=
      (n : ℂ) • mode k h a n := by
  rw [mode,← (rho k h).map_lie,modeElement,AffineLie.ell0_lie_ofLoop,map_smul]

/-- The degree operator preserves creation words, without requiring an
ordered PBW family or a pre-existing direct-sum grading. -/
theorem degree_word_mem (k h : ℂ) (w : List (Fin 3×ℤ)) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant)
      (currentWord (mode k h) w (highestVector k h))∈creationSpan k h := by
  induction w with
  | nil => simpa only [currentWord,Module.End.one_apply,degree_highest] using
      (creationSpan k h).zero_mem
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ (Verma k h) =>
        T (currentWord (mode k h) w (highestVector k h))) (degree_mode_comm k h an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      change rho k h _ (mode k h an.1 an.2 _)∈_
      rw [hc]
      exact (creationSpan k h).add_mem
        ((creationSpan k h).smul_mem _ (mode_creationSpan k h _ _ (anyWord_mem_creationSpan k h w)))
        (mode_creationSpan k h _ _ ih)

/-- Stability under the derivation extends from words to their finite span. -/
theorem degree_creationSpan (k h : ℂ) {v : Verma k h} (hv : v∈creationSpan k h) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v∈creationSpan k h := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨w,hw,rfl⟩ := hv; exact degree_word_mem k h w
  | zero => rw [map_zero]; exact (creationSpan k h).zero_mem
  | add v w hv hw ihv ihw => rw [map_add]; exact (creationSpan k h).add_mem ihv ihw
  | smul z v hv ih => rw [map_smul]; exact (creationSpan k h).smul_mem z ih

/-- An arbitrary Lie-algebra loop is a linear combination of the three
basis-coloured currents, and therefore preserves the creation span. -/
theorem loop_creationSpan (k h : ℂ) (x : Sl2) (n : ℤ)
    {v : Verma k h} (hv : v∈creationSpan k h) :
    rho k h (AffineLie.ofLoop kappaForm kappaForm_isInvariant x n) v∈creationSpan k h := by
  have hx : x=∑ a : Fin 3,x a • basis a := by
    ext b
    simp [basis,Pi.single_apply]
  rw [← AffineLie.ofLoopₗ_apply,hx,map_sum,map_sum,LinearMap.sum_apply]
  apply (creationSpan k h).sum_mem
  intro a ha
  rw [map_smul,map_smul,LinearMap.smul_apply]
  exact (creationSpan k h).smul_mem _ (mode_creationSpan k h a n hv)

/-- The creation span is invariant under the whole affine Lie algebra,
including its centre and degree derivation. -/
theorem rho_creationSpan (k h : ℂ) (x : AffSl2)
    {v : Verma k h} (hv : v∈creationSpan k h) : rho k h x v∈creationSpan k h := by
  induction (AffineLie.mem_span_gens kappaForm kappaForm_isInvariant x)
      using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨⟨y,n⟩,rfl⟩|hx
      · exact loop_creationSpan k h y n hv
      · rcases hx with rfl|hx
        · rw [rho_central,LinearMap.smul_apply,Module.End.one_apply]
          exact (creationSpan k h).smul_mem k hv
        · rw [Set.mem_singleton_iff] at hx
          subst x
          exact degree_creationSpan k h hv
  | zero => rw [map_zero,LinearMap.zero_apply]; exact (creationSpan k h).zero_mem
  | add x y hx hy ihx ihy => rw [map_add,LinearMap.add_apply]; exact (creationSpan k h).add_mem ihx ihy
  | smul z x hx ih => rw [map_smul,LinearMap.smul_apply]; exact (creationSpan k h).smul_mem z ih

/-- Invariance under Lie generators extends to their actual enveloping
algebra by tensor-algebra induction. -/
theorem enveloping_creationSpan (k h : ℂ) (u : U)
    {v : Verma k h} (hv : v∈creationSpan k h) : u • v∈creationSpan k h := by
  suffices H : ∀ p : TensorAlgebra ℂ AffSl2,∀ v∈creationSpan k h,
      (mkAlgHom ℂ _ p) • v∈creationSpan k h by
    obtain ⟨p,rfl⟩ := (RingQuot.mkAlgHom_surjective ℂ (Rel ℂ AffSl2)) u
    exact H p v hv
  intro p
  induction p using TensorAlgebra.induction with
  | algebraMap z =>
      intro v hv
      rw [AlgHom.commutes,algebraMap_smul]
      exact (creationSpan k h).smul_mem z hv
  | ι x => intro v hv; exact rho_creationSpan k h x hv
  | mul p q hp hq => intro v hv; rw [map_mul,mul_smul]; exact hp _ (hq v hv)
  | add p q hp hq => intro v hv; rw [map_add,add_smul]; exact (creationSpan k h).add_mem (hp v hv) (hq v hv)

/-- Every vector of the ACTUAL affine Verma quotient is a finite linear
combination of creation words, at every level and highest weight. This
spanning statement does not yet impose a chosen ordering on the words. -/
theorem creationSpan_eq_top (k h : ℂ) : creationSpan k h=⊤ := by
  rw [eq_top_iff]
  intro v hv
  obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k h) v
  have htop : highestVector k h∈creationSpan k h := by
    simpa only [currentWord,Module.End.one_apply] using
      creationWord_mem k h [] (by simp)
  have hu := enveloping_creationSpan k h u htop
  simpa only [highestVector,← Submodule.Quotient.mk_smul,smul_eq_mul,mul_one] using hu

end
end VOA.AffineVOA.HighestModule
