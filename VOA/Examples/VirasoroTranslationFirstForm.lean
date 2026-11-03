/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroTranslationTangent

/-!
# Identifying the translated first-order form

The first-order form inherits the actual weight-one mode adjoints because
the translation map intertwines at weight zero and its image is radical.
Its highest norm is two. Induction over left creation words therefore
identifies it with twice the normalized weight-one Verma form, fixing the
remaining normalization in the vacuum determinant coefficient identity.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule Polynomial Module
open scoped Classical

/-- On the embedded weight-one module, moving a creation mode in the
first-order row is exactly the opposite actual positive mode on the right.
Parameter derivatives disappear by the proved radical cancellation. -/
theorem translationTangentRow_adj (c : ℂ) (i : ℕ) (u : List ℕ) (v : Verma c 1) :
    translationTangentRow c (i::u) (translationEmbedding c v) =
      translationTangentRow c u
        (translationEmbedding c (vermaMode c 1 ((i:ℤ)+1) v)) := by
  have he : (translationTangentRow c (i::u)).comp (translationEmbedding c) =
      ((translationTangentRow c u).comp (translationEmbedding c)).comp
        (vermaMode c 1 ((i:ℤ)+1)) := by
    apply (vermaSortedBasis c 1).ext
    intro w
    simp only [vermaSortedBasis_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    change translationTangentRow c (i::u) (translationEmbedding c (negWord c 1 w.val)) = _
    rw [translationEmbedding_negWord, translationTangentRow_word]
    change (vermaPairPolynomial (Polynomial.C c) X (i :: (u ++ [0]))
      (Finsupp.single (w.val ++ [0]) 1)).coeff 1 = _
    rw [vermaPairPolynomial, translationTangentRow_evaluate,
      vermaWeightEvaluate_mode, vermaWeightEvaluate_single]
    simp only [Polynomial.eval_one, one_smul]
    change translationTangentRow c u
      (vermaMode c 0 ((i:ℤ)+1) (negWord c 0 (w.val ++ [0]))) = _
    rw [← translationEmbedding_negWord, ← translationEmbedding_mode]
  exact LinearMap.congr_fun he v

/-- The translated highest-vector pairing is exactly 2X. Its first
coefficient is therefore two, fixing the shifted form's normalization. -/
theorem translationPairPolynomial_highest (c : ℂ) :
    translationPairPolynomial c [] [0] = Polynomial.C 2 * X := by
  apply Polynomial.funext
  intro h
  rw [translationPairPolynomial_eval]
  simpa using vermaContravariant_translation_norm c h

/-- A translated highest vector is orthogonal to every translated word
of positive relative energy, at every highest weight, so its polynomial
pairing vanishes identically. -/
theorem translationPairPolynomial_highest_other (c : ℂ) (w : List ℕ) (hw : w ≠ []) :
    translationPairPolynomial c [] (w ++ [0]) = 0 := by
  apply Polynomial.funext
  intro h
  rw [translationPairPolynomial_eval, Polynomial.eval_zero]
  apply vermaContravariant_orthogonal c h 1 (energyHW (w ++ [0]))
  · exact negWord_mem_sortedSpan c h [0]
  · exact negWord_mem_sortedSpan c h (w ++ [0])
  · rw [verma_energy_append_zero]
    have hn : energyHW w ≠ 0 := fun he => hw ((verma_energy_zero_iff w).mp he)
    omega

/-- The initial first-order row is twice the highest-vector row of the
weight-one Verma form, with no unspecified proportionality constant. -/
theorem translationTangentRow_highest (c : ℂ) (v : Verma c 1) :
    translationTangentRow c [] (translationEmbedding c v) =
      2 * vermaContravariant c 1 (highestVector c 1) v := by
  have he : (translationTangentRow c []).comp (translationEmbedding c) =
      (2 : ℂ) • vermaContravariant c 1 (highestVector c 1) := by
    apply (vermaSortedBasis c 1).ext
    intro w
    simp only [vermaSortedBasis_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    change translationTangentRow c [] (translationEmbedding c (negWord c 1 w.val)) =
      2 * vermaContravariant c 1 (highestVector c 1) (negWord c 1 w.val)
    rw [translationEmbedding_negWord, translationTangentRow_word]
    by_cases hw : w.val = []
    · rw [hw]
      simp [translationPairPolynomial_highest, vermaContravariant_normalized]
    · rw [translationPairPolynomial_highest_other c w.val hw, coeff_zero]
      have hh : vermaContravariant c 1 (highestVector c 1) (negWord c 1 w.val) = 0 := by
        apply vermaContravariant_orthogonal c 1 0 (energyHW w.val)
        · exact negWord_mem_sortedSpan c 1 []
        · exact negWord_mem_sortedSpan c 1 w.val
        · exact Ne.symm (fun he => hw ((verma_energy_zero_iff w.val).mp he))
      rw [hh, mul_zero]
  exact LinearMap.congr_fun he v

/-- At every charge, the actual first-order translated pairing is twice
the actual normalized weight-one Verma form. The proof uses the inherited
adjoints and the highest norm, not a determinant or character formula. -/
theorem translationTangentRow_eq_verma (c : ℂ) (u : List ℕ) (v : Verma c 1) :
    translationTangentRow c u (translationEmbedding c v) =
      2 * vermaContravariant c 1 (negWord c 1 u) v := by
  induction u generalizing v with
  | nil => exact translationTangentRow_highest c v
  | cons i u ih =>
    rw [translationTangentRow_adj, ih, negWord_cons, vermaContravariant_adj]
    rw [show -(-(i:ℤ)-1) = (i:ℤ)+1 by omega]

/-- The entire first-order translated Gram matrix is twice the genuine
weight-one Gram matrix in the same partition indices. -/
theorem translationFirstGram_eq (c : ℂ) (n : ℕ) :
    translationFirstGram c n = (2 : ℂ) • vermaGramMatrix c 1 n := by
  ext i j
  have he := translationTangentRow_eq_verma c i.val (negWord c 1 j.val)
  rw [translationEmbedding_negWord, translationTangentRow_word] at he
  exact he

/-- The first possible highest-weight determinant coefficient equals
2 to the number of translated rows, times the actual vacuum determinant,
times the actual weight-one Verma determinant. This uniform identity supplies
the precise ordinary normalization needed for a future Kac-to-vacuum transfer. -/
theorem vermaWeightDeterminant_vacuum_coefficient (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c (n+1)).det.coeff (Fintype.card (VermaPartitions n)) =
      (2 : ℂ) ^ Fintype.card (VermaPartitions n) *
        ((VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1)).map
          (Polynomial.eval c)).det * (vermaGramMatrix c 1 n).det := by
  rw [vermaWeightDeterminant_vacuum_first, translationFirstGram_eq, Matrix.det_smul]
  ring

end VOA.InverseDS.VirasoroVerma
