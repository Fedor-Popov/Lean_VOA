/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaGramPolynomial
import VOA.Examples.VirasoroVacuumExactSequence
import VOA.Examples.VirasoroPartitionObstruction

/-!
# Identifying the ordinary Verma form with the vacuum form

At highest weight zero, the actual Verma form is exactly the pullback of
the normalized vacuum form along the proved quotient map. Consequently
the vacuum polynomial Gram matrix is the submatrix on words without L-minus-one.
This is a proved normalization and quotient comparison, not a determinant
factorization or a claim that vacuum roots are simple.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule Module VirDeformModes.NormalOrdering

/-- Pull the actual normalized vacuum form back to the weight-zero Verma
module through the actual quotient map in both variables. -/
noncomputable def vermaVacuumPullback (c : ℂ) :
    Verma c 0 →ₗ[ℂ] Module.Dual ℂ (Verma c 0) :=
  (VirGram4.canB c).form.compl₁₂ (vacuumProjection c) (vacuumProjection c)

/-- At highest weight zero, the constructed Verma form is exactly the
vacuum pullback. Both forms have highest norm one and the same mode adjoints,
so the proved uniqueness theorem fixes every entry. -/
theorem vermaVacuumPullback_eq (c : ℂ) :
    vermaVacuumPullback c = vermaContravariant c 0 := by
  apply vermaContravariant_unique
  · change (VirGram4.canB c).form (vacuumProjection c (highestVector c 0))
      (vacuumProjection c (highestVector c 0)) = 1
    rw [vacuumProjection_highest, VirGram4.canB_vac]
  · intro m u v
    change (VirGram4.canB c).form (vacuumProjection c (vermaMode c 0 m u))
      (vacuumProjection c v) =
      (VirGram4.canB c).form (vacuumProjection c u)
        (vacuumProjection c (vermaMode c 0 (-m) v))
    rw [vacuumProjection_mode, vacuumProjection_mode, VirGram4.canB_adj]

/-- Pairing arbitrary weight-zero Verma states can be performed after
actual vacuum projection, without any unspecified scalar factor. -/
theorem vermaContravariant_vacuum (c : ℂ) (u v : Verma c 0) :
    vermaContravariant c 0 u v =
      (VirGram4.canB c).form (vacuumProjection c u) (vacuumProjection c v) := by
  rw [← vermaVacuumPullback_eq]
  rfl

/-- The entire embedded weight-one Verma module lies in the weight-zero
Verma radical. This follows from exact vacuum projection, not from an
assumed character or determinant formula. -/
theorem translationEmbedding_mem_verma_radical (c : ℂ) (u : Verma c 1) :
    vermaContravariant c 0 (translationEmbedding c u) = 0 := by
  apply LinearMap.ext
  intro v
  rw [vermaContravariant_vacuum]
  have hz := LinearMap.congr_fun (vacuumProjection_translationEmbedding c) u
  change vacuumProjection c (translationEmbedding c u) = 0 at hz
  rw [hz, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- Incrementing every vacuum index gives the same total energy under the
Verma convention, where index zero instead denotes L-minus-one. -/
theorem vacuumWord_vermaEnergy (w : List ℕ) :
    energyHW (w.map Nat.succ) = energyVir w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, energyHW_cons, energyVir_cons, ih]

/-- Embed the vacuum partition indices at a fixed level into the full
Verma partition indices by retaining the same actual modes. -/
def vacuumVermaPartition (n : ℕ) (w : SortedOfEnergy n) : VermaPartitions n :=
  ⟨w.val.map Nat.succ, w.property.1.map Nat.succ (fun _ _ hab => Nat.succ_le_succ hab),
    (vacuumWord_vermaEnergy w.val).trans w.property.2⟩

/-- Different vacuum partitions remain different inside the Verma index
set; incrementing natural indices is injective. -/
theorem vacuumVermaPartition_injective (n : ℕ) : Function.Injective (vacuumVermaPartition n) := by
  intro a b hab
  apply Subtype.ext
  have he := congrArg (fun w : List ℕ => w.map Nat.pred) (congrArg Subtype.val hab)
  simpa [vacuumVermaPartition, List.map_map, Function.comp_def] using he

/-- The actual vacuum Gram matrix is the corresponding submatrix of the
actual highest-weight-zero Verma Gram matrix, with precisely the same form
normalization and negative-mode partition words. -/
theorem vermaGramMatrix_vacuum_submatrix (c : ℂ) (n : ℕ) :
    (vermaGramMatrix c 0 n).submatrix (vacuumVermaPartition n) (vacuumVermaPartition n) =
      (partitionGramPolynomial n).map (Polynomial.eval c) := by
  ext i j
  change vermaContravariant c 0
    (negWord c 0 (i.val.map Nat.succ)) (negWord c 0 (j.val.map Nat.succ)) =
    (partitionGramPolynomial n i j).eval c
  rw [vermaContravariant_vacuum, vacuumProjection_succ_word, vacuumProjection_succ_word]
  have he := congrFun (congrFun (partitionGramPolynomial_eval c n) i) j
  simp only [Matrix.map_apply, GramMat.gramMatrix_apply] at he
  change (partitionGramPolynomial n i j).eval c =
    (VirGram4.canB c).form (gradedBasis c n i) (gradedBasis c n j) at he
  rw [gradedBasis_apply, gradedBasis_apply, gradedWord_val, gradedWord_val] at he
  exact he.symm

end VOA.InverseDS.VirasoroVerma
