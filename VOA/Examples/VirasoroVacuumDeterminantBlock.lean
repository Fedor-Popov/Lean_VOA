/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDeterminantFirstBlock
import VOA.Examples.VirasoroVermaVacuumForm
import VOA.Examples.VirasoroVermaSingularEmbedding

/-!
# The actual vacuum block in the highest-weight determinant

Split every Verma partition into a word without translation and a word
ending in translation. At highest weight zero the latter is the actual
embedded M(c,1) radical. Removing one highest-weight factor from each such
row gives the first possible determinant coefficient as the vacuum determinant
times a precisely defined first-order translation Gram determinant.
Identifying that first-order form with twice the weight-one Verma form is
a further step; neither singular existence nor simple roots are assumed here.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes.NormalOrdering Polynomial Matrix
open scoped Classical

/-- Appending a translation increases the Verma energy by exactly one. -/
theorem verma_energy_append_zero (w : List ℕ) :
    energyHW (w ++ [0]) = energyHW w + 1 := by
  induction w with
  | nil => simp [energyHW]
  | cons i w ih => simp only [List.cons_append, energyHW_cons, ih]; omega

/-- Translation partitions at level n+1 are indexed by all Verma partitions
at level n; the appended index is the actual translation embedding. -/
def translationVermaPartition (n : ℕ) (w : VermaPartitions n) : VermaPartitions (n+1) :=
  ⟨w.val ++ [0], sortedWord_append_zero w.property.1,
    by rw [verma_energy_append_zero, w.property.2]⟩

/-- The two types of partitions give the complete level-n+1 PBW index map. -/
def vacuumTranslationPartition (n : ℕ) :
    SortedOfEnergy (n+1) ⊕ VermaPartitions n → VermaPartitions (n+1) :=
  Sum.elim (vacuumVermaPartition (n+1)) (translationVermaPartition n)

/-- A vacuum partition contains no translation index. This separates the
two blocks before any determinant manipulation. -/
theorem vacuumVermaPartition_zero_not_mem (n : ℕ) (w : SortedOfEnergy n) :
    0 ∉ (vacuumVermaPartition n w).val := by
  simp [vacuumVermaPartition]

/-- The vacuum and translation index map is one-to-one and onto. A decreasing
word containing zero ends in zero; otherwise subtracting one from its indices
gives its unique vacuum word. -/
theorem vacuumTranslationPartition_bijective (n : ℕ) :
    Function.Bijective (vacuumTranslationPartition n) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (vacuumVermaPartition_injective _ hab)
      | inr b =>
        have he := congrArg Subtype.val hab
        have hz := vacuumVermaPartition_zero_not_mem (n+1) a
        rw [show (vacuumVermaPartition (n+1) a).val = b.val ++ [0] from he] at hz
        simp at hz
    | inr a =>
      cases b with
      | inl b =>
        have he := congrArg Subtype.val hab
        have hz := vacuumVermaPartition_zero_not_mem (n+1) b
        rw [show (vacuumVermaPartition (n+1) b).val = a.val ++ [0] from he.symm] at hz
        simp at hz
      | inr b =>
        have he : a.val ++ [0] = b.val ++ [0] := congrArg Subtype.val hab
        exact congrArg Sum.inr (Subtype.ext (List.append_cancel_right he))
  · intro w
    by_cases hz : 0 ∈ w.val
    · obtain ⟨u,hu,he⟩ := sortedWord_zero_suffix w.property.1 hz
      have henergy : energyHW u = n := by
        have hh := w.property.2
        rw [he, verma_energy_append_zero] at hh
        omega
      exact ⟨Sum.inr ⟨u,hu,henergy⟩, Subtype.ext he.symm⟩
    · obtain ⟨u,hu,he⟩ := sortedWord_without_zero w.property.1 hz
      have henergy : energyVir u = n+1 := by
        rw [← vacuumWord_vermaEnergy, ← he]
        exact w.property.2
      exact ⟨Sum.inl ⟨u,hu,henergy⟩, Subtype.ext he.symm⟩

/-- Reindex the actual partition basis into vacuum words and translated
words. The same equivalence is used on rows and columns, so no sign remains. -/
noncomputable def vacuumTranslationEquiv (n : ℕ) :
    SortedOfEnergy (n+1) ⊕ VermaPartitions n ≃ VermaPartitions (n+1) :=
  Equiv.ofBijective (vacuumTranslationPartition n) (vacuumTranslationPartition_bijective n)

/-- The constant highest-weight coefficient is the actual weight-zero
contravariant pairing, including on translated words. -/
theorem vermaWeightGramPolynomial_coeff_zero (c : ℂ) (n : ℕ)
    (i j : VermaPartitions n) :
    (vermaWeightGramPolynomial c n i j).coeff 0 =
      vermaContravariant c 0 (negWord c 0 i.val) (negWord c 0 j.val) := by
  have he := congrFun (congrFun (vermaWeightGramPolynomial_eval c 0 n) i) j
  simpa only [Matrix.map_apply, ← Polynomial.coeff_zero_eq_eval_zero, vermaGramMatrix] using he

/-- Every translated row vanishes at weight zero because the actual
translation embedding lies in the canonical radical. -/
theorem vermaWeightGramPolynomial_translation_zero (c : ℂ) (n : ℕ)
    (i : VermaPartitions n) (j : VermaPartitions (n+1)) :
    (vermaWeightGramPolynomial c (n+1) (translationVermaPartition n i) j).coeff 0 = 0 := by
  rw [vermaWeightGramPolynomial_coeff_zero]
  change vermaContravariant c 0 (negWord c 0 (i.val ++ [0])) _ = 0
  rw [← translationEmbedding_negWord, translationEmbedding_mem_verma_radical,
    LinearMap.zero_apply]

/-- The first-order restricted form on the translated PBW block. Its
entries are extracted from the actual highest-weight Gram polynomials;
no identification with a guessed shifted Verma form is built into this definition. -/
noncomputable def translationFirstGram (c : ℂ) (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) ℂ := fun i j =>
  (vermaWeightGramPolynomial c (n+1)
    (translationVermaPartition n i) (translationVermaPartition n j)).coeff 1

/-- At every charge and positive level, the first possible highest-weight
determinant coefficient is the actual vacuum determinant times the determinant
of the actual first-order translated form. This is an exact normalization
bridge, without a Kac formula or any nonvanishing hypothesis. -/
theorem vermaWeightDeterminant_vacuum_first (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c (n+1)).det.coeff (Fintype.card (VermaPartitions n)) =
      ((partitionGramPolynomial (n+1)).map (Polynomial.eval c)).det *
        (translationFirstGram c n).det := by
  classical
  let e := vacuumTranslationEquiv n
  let M := (vermaWeightGramPolynomial c (n+1)).submatrix e e
  have hrow : ∀ i j, (M (Sum.inr i) j).coeff 0 = 0 := by
    intro i j
    exact vermaWeightGramPolynomial_translation_zero c n i (e j)
  have hcol : ∀ i j, (M (Sum.inl i) (Sum.inr j)).coeff 0 = 0 := by
    intro i j
    change (vermaWeightGramPolynomial c (n+1) (e (Sum.inl i)) (e (Sum.inr j))).coeff 0 = 0
    rw [vermaWeightGramPolynomial_coeff_zero, vermaContravariant_symm]
    rw [← vermaWeightGramPolynomial_coeff_zero]
    exact vermaWeightGramPolynomial_translation_zero c n j (e (Sum.inl i))
  have he := PolynomialBlock.det_first_radical_coefficient M hrow hcol
  have hdet : M.det = (vermaWeightGramPolynomial c (n+1)).det :=
    Matrix.det_submatrix_equiv_self e _
  rw [hdet] at he
  have hvac : (fun i j : SortedOfEnergy (n+1) =>
      (M (Sum.inl i) (Sum.inl j)).coeff 0) =
      (partitionGramPolynomial (n+1)).map (Polynomial.eval c) := by
    ext i j
    change (vermaWeightGramPolynomial c (n+1) (e (Sum.inl i)) (e (Sum.inl j))).coeff 0 = _
    rw [vermaWeightGramPolynomial_coeff_zero]
    exact congrFun (congrFun (vermaGramMatrix_vacuum_submatrix c (n+1)) i) j
  rw [hvac] at he
  exact he

end VOA.InverseDS.VirasoroVerma
