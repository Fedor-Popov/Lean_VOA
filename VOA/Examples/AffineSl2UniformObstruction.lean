/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralPairing

/-!
# An actual level-derivative obstruction from finite affine relations

The two finite relations may differ, which is essential when the bilinear form
pairs opposite Cartan weights. Their pairing polynomial is constructed by
uniform affine normal ordering. Its derivative times the actual pole parameter
vanishes in every normalized deformation, by the ordinary adjoint row relation.
A nonzero ordinary derivative gives rigidity using completed reconstruction.
This does not construct admissible-level relations or prove their derivative
nonzero: that ordinary representation-theoretic problem remains separate.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA Deform VertexOperatorAlgebra Polynomial
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)

/-- The universal bilinear Gram entry for two current words. The sign is one
minus sign for each adjointed current; coefficients are not conjugated. -/
noncomputable def wordGramPolynomial (u v : List (Fin 3 × ℤ)) : Polynomial ℂ :=
  ((-1:ℂ)^u.length) • NormalOrdering.wordPolynomial (adjointIndices u ++ v)

include hk0 in
/-- Evaluate the constructed Gram entry to get the actual ordinary invariant
pairing in the simple quotient, including at levels where relations occur. -/
theorem wordGramPolynomial_eval (u v : List (Fin 3 × ℤ)) :
    (wordGramPolynomial u v).eval k = (simpleForm k hk).form
      (currentWord k hk u (simple k hk).vacuum)
      (currentWord k hk v (simple k hk).vacuum) := by
  rw [simpleForm_currentWord, adjointCurrentWord_eq]
  simp only [wordGramPolynomial, eval_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [wordPolynomial_eval k hk hk0]
  rw [currentWord_eq, NormalOrdering.currentWord_append, Module.End.mul_apply]
  simp only [currentWord_eq]

/-- The tangent of any actual row-column word pairing is its universal Gram
entry's level derivative multiplied by the actual normalized pole scalar. -/
theorem wordGram_tangent (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    (u v : List (Fin 3 × ℤ)) :
    (simpleForm k hk).form (simple k hk).vacuum
      (liftedAdjointCurrentWord k hk D u
        (liftedCurrentWord k hk D v ((simple k hk).vacuum,0))).2 =
      (wordGramPolynomial u v).derivative.eval k * δ := by
  rw [liftedAdjointCurrentWord_eq]
  simp only [LinearMap.smul_apply, Prod.smul_snd, map_smul, smul_eq_mul]
  have he : liftedCurrentWord k hk D (adjointIndices u)
      (liftedCurrentWord k hk D v ((simple k hk).vacuum,0)) =
      liftedCurrentWord k hk D (adjointIndices u ++ v) ((simple k hk).vacuum,0) := by
    simp only [liftedCurrentWord_eq, NormalOrdering.currentWord_append, Module.End.mul_apply]
  rw [he, simple_normalized_word_tangent k hk hk0 D hD hnorm δ hδ]
  simp only [wordGramPolynomial, map_smul, eval_smul, smul_eq_mul, mul_assoc]

/-- The polynomial pairing of two finite word combinations, with every cross
term retained. Distinct combinations allow opposite Cartan weights. -/
noncomputable def relationPairPolynomial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → List (Fin 3 × ℤ)) (c : ι → ℂ)
    (v : κ → List (Fin 3 × ℤ)) (d : κ → ℂ) : Polynomial ℂ :=
  ∑ i, ∑ j, (c i * d j) • wordGramPolynomial (u i) (v j)

include hk0 in
/-- The finite polynomial computes the ordinary bilinear pairing of the two
word combinations at every nonzero noncritical level. -/
theorem relationPairPolynomial_eval {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → List (Fin 3 × ℤ)) (c : ι → ℂ)
    (v : κ → List (Fin 3 × ℤ)) (d : κ → ℂ) :
    (relationPairPolynomial u c v d).eval k = (simpleForm k hk).form
      (∑ i, c i • currentWord k hk (u i) (simple k hk).vacuum)
      (∑ j, d j • currentWord k hk (v j) (simple k hk).vacuum) := by
  simp only [relationPairPolynomial, eval_finsetSum, eval_smul,
    wordGramPolynomial_eval k hk hk0, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual tangent pairing of arbitrary finite word combinations is the
level derivative of their constructed polynomial. Only the deformation's own
normalization and pole parameter enter; no tangent pairing is postulated. -/
theorem relationPair_tangent (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → List (Fin 3 × ℤ)) (c : ι → ℂ)
    (v : κ → List (Fin 3 × ℤ)) (d : κ → ℂ) :
    (simpleForm k hk).form (simple k hk).vacuum
      ((∑ i, c i • liftedAdjointCurrentWord k hk D (u i))
        (∑ j, d j • liftedCurrentWord k hk D (v j) ((simple k hk).vacuum,0))).2 =
      (relationPairPolynomial u c v d).derivative.eval k * δ := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Prod.snd_sum, Prod.smul_snd, smul_eq_mul,
    wordGram_tangent k hk hk0 D hD hnorm δ hδ,
    relationPairPolynomial, eval_finsetSum, eval_smul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A pair of ordinary quotient relations with nonzero pairing derivative
forces the actual normalized pole parameter to vanish. All deformation-to-
polynomial and adjoint-row steps are discharged by the preceding theorems. -/
theorem pole_parameter_zero_of_relations (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → List (Fin 3 × ℤ)) (c : ι → ℂ)
    (v : κ → List (Fin 3 × ℤ)) (d : κ → ℂ)
    (hc : ∑ i, c i • currentWord k hk (u i) (simple k hk).vacuum = 0)
    (hd : ∑ j, d j • currentWord k hk (v j) (simple k hk).vacuum = 0)
    (hp : (relationPairPolynomial u c v d).derivative.eval k ≠ 0) : δ = 0 := by
  have hz := (actual_word_relation_obstruction k hk D c u d v hc hd).2
  rw [relationPair_tangent k hk hk0 D hD hnorm δ hδ u c v d] at hz
  exact (mul_eq_zero.mp hz).resolve_left hp

include hk0 in
/-- An ordinary pair of finite quotient relations and a nonzero level
pairing derivative suffice for graded rigidity at any nonzero noncritical
level. Producing those algebraic inputs uniformly at admissible levels is
still required; they are not assumed as new axioms. -/
theorem graded_rigidity_of_relations {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → List (Fin 3 × ℤ)) (c : ι → ℂ)
    (v : κ → List (Fin 3 × ℤ)) (d : κ → ℂ)
    (hc : ∑ i, c i • currentWord k hk (u i) (simple k hk).vacuum = 0)
    (hd : ∑ j, d j • currentWord k hk (v j) (simple k hk).vacuum = 0)
    (hp : (relationPairPolynomial u c v d).derivative.eval k ≠ 0) :
    IsRigidGraded (simple k hk) := by
  apply simple_isRigidGraded_of_normalisedPoleVanishes k hk hk0
  intro D hD hnorm a ha b hb
  obtain ⟨δ, hδ, _⟩ := simple_existsUnique_pole_parameter k hk hk0 D hD hnorm
  have hz := pole_parameter_zero_of_relations k hk hk0 D hD hnorm δ hδ u c v d hc hd hp
  simpa only [hz, mul_zero, zero_smul] using hδ ⟨a,ha⟩ ⟨b,hb⟩

end VOA.AffineSl2GeneralRigidity
