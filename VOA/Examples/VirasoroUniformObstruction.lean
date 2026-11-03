/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroUniversalPairing

/-!
# A uniform singular-relation obstruction

A finite linear combination of words has a charge-independent norm polynomial.
If the combination vanishes in the simple quotient, its actual lifted norm has
zero tangent coordinate. The uniform pairing formula identifies that coordinate
with the derivative of the norm polynomial times the central variation.
A nonzero derivative therefore proves graded rigidity by reconstruction.

This is a general reduction, NOT yet the uniform minimal-model theorem: one
still has to construct appropriate relations and prove the derivative nonzero
for every coprime pair of minimal-model parameters.
-/
namespace VOA.VirDeformModes.NormalOrdering
open VertexOperatorAlgebra Deform Polynomial Module
variable {ι : Type*} [Fintype ι]

/-- The norm polynomial of a finite word combination. The same coefficients
are used in the state and its ordinary bilinear adjoint; no complex conjugation
occurs because the invariant form is bilinear. -/
noncomputable def relationPolynomial (w : ι → List ℤ) (r : ι → ℂ) : Polynomial ℂ :=
  ∑ i, ∑ j, (r i * r j) • wordPolynomial ((w i).reverse.map Neg.neg ++ w j)

/-- At any charge the relation polynomial is exactly the ordinary universal
norm of the chosen word combination, including all cross terms. -/
theorem relationPolynomial_eval (c : ℂ) (w : ι → List ℤ) (r : ι → ℂ) :
    (relationPolynomial w r).eval c =
      (VirGram4.canB c).form
        (∑ i, r i • virWord (VirModule.virasoroVOA c).L (w i) (VirModule.vacVec c))
        (∑ j, r j • virWord (VirModule.virasoroVOA c).L (w j) (VirModule.vacVec c)) := by
  simp only [relationPolynomial, eval_finsetSum, eval_smul, universal_gram_entry,
    map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every actual normalized lifted relation has tangent norm equal to the
charge derivative of its universal norm times the actual central variation. -/
theorem relation_tangent (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
      (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
      (VirSimple.virasoroSimple c).conformalVector = β • (VirSimple.virasoroSimple c).conformalVector)
    (w : ι → List ℤ) (r : ι → ℂ) :
    (VirQuotForm.Bsimp c).form (VirSimple.virasoroSimple c).vacuum
      ((∑ i, r i • virWord (normalizedL D β) ((w i).reverse.map Neg.neg))
        (∑ j, r j • virWord (normalizedL D β) (w j)
          ((VirSimple.virasoroSimple c).vacuum,0))).2 =
      (relationPolynomial w r).derivative.eval c * (2*α-β*c) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Prod.snd_sum, Prod.smul_snd, smul_eq_mul, ← Module.End.mul_apply,
    ← virWord_append, simple_normalized_word_tangent c D hD α β ha hb,
    relationPolynomial, eval_finsetSum, eval_smul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- An ordinary quotient relation with a nonzero universal norm derivative
forces zero central variation for every actual graded deformation. The proof
uses the ordinary adjoint row relation, not a deformed invariant form. -/
theorem central_variation_zero_of_relation (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
      (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
      (VirSimple.virasoroSimple c).conformalVector = β • (VirSimple.virasoroSimple c).conformalVector)
    (w : ι → List ℤ) (r : ι → ℂ)
    (hr : ∑ i, r i • virWord (VirSimple.virasoroSimple c).L (w i)
      (VirSimple.virasoroSimple c).vacuum = 0)
    (hd : (relationPolynomial w r).derivative.eval c ≠ 0) :
    2*α-β*c = 0 := by
  have hz := virWord_pairing_obstruction D β (VirQuotForm.Bsimp c) w r hr
  rw [relation_tangent c D hD α β ha hb] at hz
  exact (mul_eq_zero.mp hz).resolve_left hd

/-- A charge admitting a finite quotient relation with nonzero universal norm
derivative is graded rigid. This theorem is valid at every weight; proving its
two concrete algebraic inputs uniformly for minimal models remains separate. -/
theorem graded_rigidity_of_relation (c : ℂ) (w : ι → List ℤ) (r : ι → ℂ)
    (hr : ∑ i, r i • virWord (VirSimple.virasoroSimple c).L (w i)
      (VirSimple.virasoroSimple c).vacuum = 0)
    (hd : (relationPolynomial w r).derivative.eval c ≠ 0) :
    IsRigidGraded (VirSimple.virasoroSimple c) := by
  intro D hD
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData c D hD
  exact isTrivial_of_zero_central_variation c D hD α β ha hb
    (central_variation_zero_of_relation c D hD α β ha hb w r hr hd)

/-- A kernel row of the universal polynomial Gram matrix gives an actual
relation in the simple quotient, provided the chosen words form a homogeneous
universal basis. Thus the criterion can be checked entirely in the universal
module, without constructing the simple quotient explicitly. -/
theorem quotient_relation_of_word_gram (c : ℂ) {n : ℤ}
    (e : Basis ι ℂ ((VirModule.virasoroVOA c).grading n))
    (w : ι → List ℤ) (r : ι → ℂ)
    (hw : ∀ i, (e i : VirModule.VirUniv c) =
      virWord (VirModule.virasoroVOA c).L (w i) (VirModule.vacVec c))
    (hr : ∀ j, ∑ i, r i *
      (wordPolynomial ((w i).reverse.map Neg.neg ++ w j)).eval c = 0) :
    ∑ i, r i • virWord (VirSimple.virasoroSimple c).L (w i)
      (VirSimple.virasoroSimple c).vacuum = 0 := by
  have hb : ∀ j, ∑ i, r i * (VirGram4.canB c).form
      (e i : VirModule.VirUniv c) (e j : VirModule.VirUniv c) = 0 := by
    intro j
    simpa only [hw, universal_gram_entry] using hr j
  have hm := gram_row_relation_mem_maxIdeal (VirGram4.canB c)
    (VirGram4.canB_isFullyInvariant c) (VirGram4.canB_normalized c) e r hb
  have hz : (VirSimple.maxIdealVir c).mkQ
      (∑ i, r i • (e i : VirModule.VirUniv c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  simpa only [map_sum, map_smul, hw, virWord_mkQ,
    VirSimple.virasoroSimple_vacuum] using hz

/-- A homogeneous universal word basis, a row of its polynomial Gram kernel,
and a nonzero derivative of that row's norm suffice for graded rigidity.
These are ordinary finite-dimensional algebraic inputs. Their existence at
all minimal-model charges is the remaining uniform mathematical problem. -/
theorem graded_rigidity_of_word_gram (c : ℂ) {n : ℤ}
    (e : Basis ι ℂ ((VirModule.virasoroVOA c).grading n))
    (w : ι → List ℤ) (r : ι → ℂ)
    (hw : ∀ i, (e i : VirModule.VirUniv c) =
      virWord (VirModule.virasoroVOA c).L (w i) (VirModule.vacVec c))
    (hr : ∀ j, ∑ i, r i *
      (wordPolynomial ((w i).reverse.map Neg.neg ++ w j)).eval c = 0)
    (hd : (relationPolynomial w r).derivative.eval c ≠ 0) :
    IsRigidGraded (VirSimple.virasoroSimple c) :=
  graded_rigidity_of_relation c w r (quotient_relation_of_word_gram c e w r hw hr) hd

end VOA.VirDeformModes.NormalOrdering
