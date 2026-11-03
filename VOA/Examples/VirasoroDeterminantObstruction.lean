/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroPartitionObstruction
import VOA.Examples.VirasoroRigidityGramLift

/-!
# From an ordinary determinant root to actual graded rigidity

A relation among partition states lifts because their images span the fixed
homogeneous space of the simple quotient. Applying the actual lifted row
operators gives a dual-number kernel with a nonzero constant coefficient.
The actual determinant therefore vanishes. The uniform polynomial pairing
identification then makes a simple determinant root obstruct central motion.
The uniform minimal-model Kac/root theorem itself is still a separate task.
-/
namespace VOA.VirDeformModes.NormalOrdering
open VirModule VirSimple VertexOperatorAlgebra Deform Polynomial TrivSqZeroExt
open VirRigidGramLift Module
open scoped Matrix

/-- A finite ordinary relation can be corrected to first order whenever each
state correction belongs to the span of the original states. This formulation
works in an ambient space larger than the homogeneous component being studied. -/
theorem det_pairing_of_corrections_mem_span
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u u₁ : ι → V) (a a₁ : ι → V →ₗ[ℂ] ℂ)
    (hu : ∀ j, u₁ j ∈ Submodule.span ℂ (Set.range u))
    (r : ι → ℂ) (hr : ∑ j, r j • u j = 0) (i : ι) (hi : r i ≠ 0) :
    (firstOrderPairingMatrix u u₁ a a₁).det = 0 := by
  have hm : -(∑ j, r j • u₁ j) ∈ Submodule.span ℂ (Set.range u) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hu j)))
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
  have hc : ∑ j, (r j • u₁ j + s j • u j) = 0 := by
    rw [Finset.sum_add_distrib, hs, add_neg_cancel]
  apply det_eq_zero_of_lifted_kernel _ (fun j => inl (r j) + inr (s j))
    (pairingMatrix_mulVec_lifted_relation u u₁ a a₁ r s hr hc) i
  simpa using hi

/-- Quotient images of the universal partition basis span the entire simple
homogeneous component. A homogeneous state lifts to the universal component,
where its basis expansion descends through the quotient map. -/
theorem simple_partition_mem_span (c : ℂ) (n : ℕ)
    (x : VirUniv c ⧸ maxIdealVir c) (hx : x ∈ (virasoroSimple c).grading (n:ℤ)) :
    x ∈ Submodule.span ℂ (Set.range (fun i : SortedOfEnergy n =>
      virWord (virasoroSimple c).L (partitionWord n i) (virasoroSimple c).vacuum)) := by
  rw [virasoroSimple_grading] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun i => (gradedBasis c n).repr ⟨y,hy⟩ i, ?_⟩
  have he := congrArg (fun z : gradingVir c (n:ℤ) => (maxIdealVir c).mkQ z)
    ((gradedBasis c n).sum_repr ⟨y,hy⟩)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    partitionWord_basis, virWord_mkQ, ← virasoroSimple_vacuum] using he

/-- The actual tangent coordinate of every partition state lies in the span
of the ordinary quotient partition states, by grading in both coordinates. -/
theorem partition_tangent_mem_span (c : ℂ)
    (D : FirstOrderDeformation (virasoroSimple c)) (hD : D.IsGraded)
    (β : ℂ) (n : ℕ) (j : SortedOfEnergy n) :
    (virWord (normalizedL D β) (partitionWord n j) ((virasoroSimple c).vacuum,0)).2 ∈
      Submodule.span ℂ (Set.range (fun i : SortedOfEnergy n =>
        virWord (virasoroSimple c).L (partitionWord n i) (virasoroSimple c).vacuum)) := by
  apply simple_partition_mem_span
  have h := (creationWord_grading D hD β j.val).2
  simpa only [creationWord, j.property.2] using h

/-- The first-order part of a lifted word, followed by ordinary vacuum pairing,
is an ordinary complex linear functional on the input state. -/
noncomputable def wordTangentFunctional {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W) (β : ℂ)
    (B : InvariantForm W) (w : List ℤ) : V →ₗ[ℂ] ℂ :=
  (B.form W.vacuum).comp ((LinearMap.snd ℂ V V).comp
    ((virWord (normalizedL D β) w).comp (LinearMap.inl ℂ V V)))

/-- A lifted word has the usual first-order block pairing: the input correction
is tested by the ordinary row, and the ordinary input by the corrected row. -/
theorem vacuumPair_word_block {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W) (β : ℂ)
    (B : InvariantForm W) (w : List ℤ) (x : V × V) :
    vacuumPair B (virWord (normalizedL D β) w x) =
      inl (B.form W.vacuum (virWord W.L w x.1)) +
      inr (B.form W.vacuum (virWord W.L w x.2) + wordTangentFunctional D β B w x.1) := by
  have hx : x = (x.1,0) + (0,x.2) := by ext <;> simp
  rw [hx, map_add, virWord_tangent]
  ext <;> simp [vacuumPair_apply, virWord_fst, wordTangentFunctional, add_comm]

/-- Every polynomial partition pairing is the actual first-order pairing of
the ordinary partition states and their tangent corrections with the actual
ordinary and tangent row functionals. -/
theorem partition_matrix_firstOrder (c : ℂ)
    (D : FirstOrderDeformation (virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple c).conformalVector 3
      (virasoroSimple c).conformalVector = α • (virasoroSimple c).vacuum)
    (hb : D.smul₁ (virasoroSimple c).conformalVector 1
      (virasoroSimple c).conformalVector = β • (virasoroSimple c).conformalVector)
    (n : ℕ) :
    (aeval (inl c + inr (2*α-β*c) : DualNumber ℂ)).toRingHom.mapMatrix
      (partitionGramPolynomial n) =
    firstOrderPairingMatrix
      (fun j => virWord (virasoroSimple c).L (partitionWord n j) (virasoroSimple c).vacuum)
      (fun j => (virWord (normalizedL D β) (partitionWord n j)
        ((virasoroSimple c).vacuum,0)).2)
      (fun i => ((VirQuotForm.Bsimp c).form (virasoroSimple c).vacuum).comp
        (virWord (virasoroSimple c).L ((partitionWord n i).reverse.map Neg.neg)))
      (fun i => wordTangentFunctional D β (VirQuotForm.Bsimp c)
        ((partitionWord n i).reverse.map Neg.neg)) := by
  apply Matrix.ext
  intro i j
  change (partitionGramPolynomial n i j).aeval (inl c + inr (2*α-β*c)) = _
  rw [partitionGramPolynomial_actual c D hD α β ha hb,
    vacuumPair_word_block]
  simp only [firstOrderPairingMatrix, LinearMap.comp_apply, virWord_fst]

/-- An ordinary zero of the partition determinant persists in every actual
normalized graded deformation. The lifted kernel is constructed from an
ordinary Gram row and the spanning of the simple homogeneous component. -/
theorem actual_partition_determinant_zero (c : ℂ)
    (D : FirstOrderDeformation (virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple c).conformalVector 3
      (virasoroSimple c).conformalVector = α • (virasoroSimple c).vacuum)
    (hb : D.smul₁ (virasoroSimple c).conformalVector 1
      (virasoroSimple c).conformalVector = β • (virasoroSimple c).conformalVector)
    (n : ℕ) (hroot : (partitionGramPolynomial n).det.eval c = 0) :
    (partitionGramPolynomial n).det.aeval (inl c + inr (2*α-β*c) : DualNumber ℂ) = 0 := by
  have hM : ((evalRingHom c).mapMatrix (partitionGramPolynomial n)).det = 0 := by
    rw [← RingHom.map_det]
    exact hroot
  obtain ⟨r, hrne, hr⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hM
  have hrow (j : SortedOfEnergy n) :
      ∑ i, r i * (partitionGramPolynomial n i j).eval c = 0 := by
    have hh := congrFun hr j
    simpa only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply,
      Matrix.map_apply, Pi.zero_apply] using hh
  have hrel := quotient_relation_of_word_gram c (gradedBasis c n)
    (partitionWord n) r (partitionWord_basis c n) hrow
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra hn
    apply hrne
    funext j
    exact not_ne_iff.mp (not_exists.mp hn j)
  have hz := det_pairing_of_corrections_mem_span
    (fun j => virWord (virasoroSimple c).L (partitionWord n j) (virasoroSimple c).vacuum)
    (fun j => (virWord (normalizedL D β) (partitionWord n j)
      ((virasoroSimple c).vacuum,0)).2)
    (fun i => ((VirQuotForm.Bsimp c).form (virasoroSimple c).vacuum).comp
      (virWord (virasoroSimple c).L ((partitionWord n i).reverse.map Neg.neg)))
    (fun i => wordTangentFunctional D β (VirQuotForm.Bsimp c)
      ((partitionWord n i).reverse.map Neg.neg))
    (partition_tangent_mem_span c D hD β n) r hrel i hi
  rw [← partition_matrix_firstOrder c D hD α β ha hb n, ← RingHom.map_det] at hz
  exact hz

/-- A simple zero of an ordinary partition Gram determinant obstructs every
actual central variation. Both determinant preservation and the polynomial
identification are proved here, rather than required as deformation inputs. -/
theorem central_variation_zero_of_simple_determinant (c : ℂ)
    (D : FirstOrderDeformation (virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple c).conformalVector 3
      (virasoroSimple c).conformalVector = α • (virasoroSimple c).vacuum)
    (hb : D.smul₁ (virasoroSimple c).conformalVector 1
      (virasoroSimple c).conformalVector = β • (virasoroSimple c).conformalVector)
    (n : ℕ) (hroot : (partitionGramPolynomial n).det.eval c = 0)
    (hsimple : (partitionGramPolynomial n).det.derivative.eval c ≠ 0) :
    2*α-β*c = 0 :=
  VirRigidTangent.tangent_eq_zero_of_simple_root _ _ _ hsimple
    (actual_partition_determinant_zero c D hD α β ha hb n hroot)

/-- At any charge with a simple zero of any partition Gram determinant,
every graded first-order VOA deformation is a coordinate change. Only the
ordinary polynomial root and derivative remain as inputs. Proving those facts
uniformly for minimal-model parameters is not asserted by this theorem. -/
theorem graded_rigidity_of_simple_determinant (c : ℂ) (n : ℕ)
    (hroot : (partitionGramPolynomial n).det.eval c = 0)
    (hsimple : (partitionGramPolynomial n).det.derivative.eval c ≠ 0) :
    IsRigidGraded (virasoroSimple c) := by
  intro D hD
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData c D hD
  exact isTrivial_of_zero_central_variation c D hD α β ha hb
    (central_variation_zero_of_simple_determinant c D hD α β ha hb n hroot hsimple)

end VOA.VirDeformModes.NormalOrdering
