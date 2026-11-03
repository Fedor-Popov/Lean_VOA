/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletW2AbeRelations
import VOA.Examples.TripletW2Nilpotent

/-!
# The quotient-generation gate for `SF(1)^+ = W(2)`

The four Abe classes are already nilpotent in the same-carrier Poisson algebra
`A₂(tripletW2)`.  Thus the minimal remaining input for `C₂`-cofiniteness is not full
strong generation of the vertex algebra, but generation of this quotient algebra by those
four classes.  This file isolates that gate and packages its consequences without using the
ambient symplectic-fermion `C₂` quotient.
-/

set_option linter.style.longLine false

namespace VOA.AbeAdjoin

open VOA VOA.SympFerm
open VOA.AbeGens VOA.AbeRel
open VOA.TripletNilp

/-! ## A symbolic Wick-support API for the even-word induction -/

/-- A nonnegative fermion mode kills a word unless its mode number matches one of the
creation levels in that word.  This is the recursive CAR statement needed to use
`genProd_of_support` on a symbolic word rather than on a fixed low-weight example. -/
theorem chiM_nonneg_stWordSF_eq_zero (c : Fin 2) {p : ℤ} (hp : 0 ≤ p) :
    ∀ (l : SFWord),
      (∀ q ∈ l, p ≠ (q.1 : ℤ) + 1) → chiM c p (stWordSF l) = 0
  | [], _ => chiM_nonneg_nil c hp
  | (k, a) :: l, h => by
      rw [← chiM_cons a k l, chiM_swap]
      have htail : ∀ q ∈ l, p ≠ (q.1 : ℤ) + 1 := by
        intro q hq
        exact h q (by simp [hq])
      rw [chiM_nonneg_stWordSF_eq_zero c hp l htail, map_zero, neg_zero, zero_add]
      rw [carC_eq_zero_of_ne]
      · exact zero_smul ℂ (stWordSF l)
      · intro hsum
        exact h (k, a) (by simp) (by omega)

/-- The only possible normal-ordering indices in `Gᵃᵇ₍₋₁₎(stWordSF l)`:
`0` is the no-contraction term, `k+2` contracts the second field against a level-`k`
letter, and `-k-3` contracts the first field. -/
noncomputable def wordGSupport (l : SFWord) : Finset ℤ :=
  insert 0
    ((l.toFinset.image fun q => (q.1 : ℤ) + 2) ∪
      (l.toFinset.image fun q => -(q.1 : ℤ) - 3))

/-- The distinguished support index `0` is exactly the no-contraction word obtained by
prepending the two letters of `Gᵃᵇ`. -/
theorem gTerm_zero_stWordSF (a b : Fin 2) (l : SFWord) :
    gTerm a b (stWordSF l) 0 =
      stWordSF ([((1 : ℕ), a), ((0 : ℕ), b)] ++ l) := by
  rw [gTerm_pos a b (stWordSF l) (le_refl 0)]
  norm_num
  have h0 := chiM_cons b 0 l
  have h1 := chiM_cons a 1 ((0, b) :: l)
  norm_num at h0 h1
  rw [h0, h1]

/-- `genProd_of_support` with a support finset computed uniformly from an arbitrary word. -/
theorem genProd_stWordSF_of_support (a b : Fin 2) (l : SFWord) :
    mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), b)])) (-1) (stWordSF l) =
      ∑ m ∈ wordGSupport l, gTerm a b (stWordSF l) m := by
  apply genProd_of_support a b (stWordSF l) (wordGSupport l)
  intro m hm
  refine gTerm_vanish a b (stWordSF l) m (fun hm0 => ?_) (fun hmneg => ?_)
  · by_cases hmzero : m = 0
    · subst m
      exact absurd (by simp [wordGSupport]) hm
    · apply chiM_nonneg_stWordSF_eq_zero b (p := m - 1) (by omega) l
      intro q hq heq
      apply hm
      rw [wordGSupport]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨q, List.mem_toFinset.mpr hq, by omega⟩
  · apply chiM_nonneg_stWordSF_eq_zero a (p := -m - 2) (by omega) l
    intro q hq heq
    apply hm
    rw [wordGSupport]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨q, List.mem_toFinset.mpr hq, by omega⟩

/-- The Wick expansion solved for its longest (no-contraction) word.  Every term in the
remaining finite sum has two fewer letters than the displayed left-hand side. -/
theorem pair_cons_eq_genProd_sub_contractions (a b : Fin 2) (l : SFWord) :
    stWordSF ([((1 : ℕ), a), ((0 : ℕ), b)] ++ l) =
      mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), b)])) (-1) (stWordSF l) -
        ∑ m ∈ (wordGSupport l).erase 0, gTerm a b (stWordSF l) m := by
  rw [genProd_stWordSF_of_support]
  have hzero : 0 ∈ wordGSupport l := by simp [wordGSupport]
  rw [← Finset.sum_erase_add (wordGSupport l) (fun m => gTerm a b (stWordSF l) m) hzero,
    gTerm_zero_stWordSF]
  abel

/-- The minimal same-carrier generation gate: the four concrete classes generate
`A₂(SF(1)^+)` as a commutative complex algebra. -/
def AbeQuotientGeneration : Prop :=
  Algebra.adjoin ℂ ({wbar, Ebar, Hbar, Fbar} : Set (A₂ tripletW2)) = ⊤

private theorem mk₂_image_abeGens :
    mk₂ tripletW2 '' abeGens = ({wbar, Ebar, Hbar, Fbar} : Set (A₂ tripletW2)) := by
  ext x
  simp [abeGens, wbar, Ebar, Hbar, Fbar, eq_comm]

/-- Full strong generation implies the smaller quotient-generation gate.  The converse is
neither claimed nor needed. -/
theorem abeQuotientGeneration_of_strongGenAbe (h : StrongGenAbe) :
    AbeQuotientGeneration := by
  have htop := adjoin_mk₂_image_eq_top tripletW2 abeGens h
  rw [mk₂_image_abeGens] at htop
  exact htop

/-- The already proved same-carrier relations make the four quotient generators nilpotent. -/
theorem abe_four_isNilpotent :
    IsNilpotent wbar ∧ IsNilpotent Ebar ∧ IsNilpotent Hbar ∧ IsNilpotent Fbar :=
  ⟨wbar_isNilpotent, Ebar_isNilpotent, Hbar_isNilpotent, Fbar_isNilpotent⟩

/-- Once quotient generation is closed, `SF(1)^+` is `C₂`-cofinite.  Every algebra and
nilpotence statement here is formed with `tripletW2`'s own vertex operators. -/
theorem c2Cofinite_tripletW2_of_abeQuotientGeneration
    (h : AbeQuotientGeneration) : C2Cofinite tripletW2 := by
  exact NilpotentGenerators.finiteDimensional_of_four_isNilpotent
    wbar Ebar Hbar Fbar wbar_isNilpotent Ebar_isNilpotent Hbar_isNilpotent
      Fbar_isNilpotent h

/-- The current exponents give the unconditional numerical consequence `6·2·4·2 = 96`
as soon as quotient generation is supplied. -/
theorem finrank_A₂_tripletW2_le_96_of_abeQuotientGeneration
    (h : AbeQuotientGeneration) : Module.finrank ℂ (A₂ tripletW2) ≤ 96 := by
  have hE : Ebar ^ 2 = 0 := by rw [pow_two]; exact Ebar_sq
  have hF : Fbar ^ 2 = 0 := by rw [pow_two]; exact Fbar_sq
  have hle := NilpotentGenerators.finrank_le_of_four
    wbar Ebar Hbar Fbar 6 2 4 2 wbar_pow_six hE Hbar_pow_four hF h
  norm_num at hle ⊢
  exact hle

end VOA.AbeAdjoin

section AxiomAudit
#print axioms VOA.AbeAdjoin.abeQuotientGeneration_of_strongGenAbe
#print axioms VOA.AbeAdjoin.c2Cofinite_tripletW2_of_abeQuotientGeneration
#print axioms VOA.AbeAdjoin.finrank_A₂_tripletW2_le_96_of_abeQuotientGeneration
end AxiomAudit
