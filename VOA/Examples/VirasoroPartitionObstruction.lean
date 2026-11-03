/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroUniformObstruction

/-!
# Polynomial Gram matrices at every partition level

Every level has a charge-independent finite index set: partitions into parts
at least two. Normal ordering constructs a polynomial matrix on this set.
Its scalar values are the actual canonical Gram matrices, and its dual-number
values are the actual normalized deformation pairings. This supplies the
uniform bridge; a general first-singular-level root proof remains required.
-/
namespace VOA.VirDeformModes.NormalOrdering
open VirModule VertexOperatorAlgebra Deform Polynomial

/-- Translate a partition index into its actual negative Virasoro mode list.
The entry i represents the part i+2, hence the mode -i-2. -/
def partitionWord (n : ℕ) (w : SortedOfEnergy n) : List ℤ :=
  w.val.map (fun (i : ℕ) => -(i:ℤ)-2)

/-- Evaluating a partition's mode list reproduces its universal creation
monomial. The natural-number encoding changes only the indices, not the action. -/
theorem creationWord_eq_negWord (c : ℂ) (w : List ℕ) :
    virWord (virasoroVOA c).L (w.map (fun (i : ℕ) => -(i:ℤ)-2)) (vacVec c) =
      negWordVir c w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, virWord, Module.End.mul_apply, ih,
      virasoroVOA_L_eq_Lop, negWordVir_cons]

/-- The partition basis is exactly the family used in the polynomial pairing
construction, so no independent choice of basis or change-of-basis assumption
is needed to connect the two Gram matrices. -/
theorem partitionWord_basis (c : ℂ) (n : ℕ) (i : SortedOfEnergy n) :
    (gradedBasis c n i : VirUniv c) =
      virWord (virasoroVOA c).L (partitionWord n i) (vacVec c) := by
  simp only [gradedBasis_apply, gradedWord_val, partitionWord, creationWord_eq_negWord]

/-- The canonical vacuum Gram matrix over the central-charge polynomial ring,
at an arbitrary level. Its indices do not depend on the central charge. -/
noncomputable def partitionGramPolynomial (n : ℕ) :
    Matrix (SortedOfEnergy n) (SortedOfEnergy n) (Polynomial ℂ) :=
  fun i j => wordPolynomial ((partitionWord n i).reverse.map Neg.neg ++ partitionWord n j)

/-- Scalar specialization of the polynomial matrix gives the actual canonical
invariant-form Gram matrix in the partition basis, at every charge and level. -/
theorem partitionGramPolynomial_eval (c : ℂ) (n : ℕ) :
    (partitionGramPolynomial n).map (Polynomial.eval c) =
      GramMat.gramMatrix (VirGram4.canB c) (n:ℤ) (gradedBasis c n) := by
  ext i j
  simp only [Matrix.map_apply, partitionGramPolynomial, GramMat.gramMatrix_apply,
    universal_gram_entry]
  exact congrArg₂ (fun (x y : VirUniv c) => (VirGram4.canB c).form x y)
    (partitionWord_basis c n i).symm (partitionWord_basis c n j).symm

/-- The same matrix evaluated at c+δt gives the actual lifted adjoint-word
pairings of every graded deformation. No determinant equation and no deformed
invariant form is assumed in this identification. -/
theorem partitionGramPolynomial_actual (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
      (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
      (VirSimple.virasoroSimple c).conformalVector =
        β • (VirSimple.virasoroSimple c).conformalVector)
    (n : ℕ) (i j : SortedOfEnergy n) :
    (partitionGramPolynomial n i j).aeval (TrivSqZeroExt.inl c +
      TrivSqZeroExt.inr (2*α-β*c)) =
    vacuumPair (VirQuotForm.Bsimp c)
      (virWord (normalizedL D β) ((partitionWord n i).reverse.map Neg.neg)
        (virWord (normalizedL D β) (partitionWord n j)
          ((VirSimple.virasoroSimple c).vacuum,0))) := by
  rw [← Module.End.mul_apply, ← virWord_append]
  exact (simple_normalized_word_pairing c D hD α β ha hb _).symm

/-- A row of a partition Gram kernel whose norm has nonzero charge derivative
proves graded rigidity. All basis and deformation-pairing identifications are
already discharged; only these ordinary polynomial facts remain as inputs. -/
theorem graded_rigidity_of_partition_gram (c : ℂ) (n : ℕ)
    (r : SortedOfEnergy n → ℂ)
    (hr : ∀ j, ∑ i, r i * (partitionGramPolynomial n i j).eval c = 0)
    (hd : (relationPolynomial (partitionWord n) r).derivative.eval c ≠ 0) :
    IsRigidGraded (VirSimple.virasoroSimple c) :=
  graded_rigidity_of_word_gram c (gradedBasis c n) (partitionWord n) r
    (partitionWord_basis c n) hr hd

end VOA.VirDeformModes.NormalOrdering
