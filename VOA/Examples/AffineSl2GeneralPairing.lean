/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralWordRelations
import VOA.Examples.AffineSl2UniversalPairing

/-!
# Every actual normalized affine word pairing has its universal polynomial

This module applies the uniform reduction to the actual simple-quotient
currents. The dual scalar is the level k plus the uniquely extracted pole
variation δ. The tangent coordinate is therefore δ times the derivative of
the same polynomial that computes the ordinary pairing at level k.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA Deform VertexOperatorAlgebra TrivSqZeroExt
open Module (End)
open VirDeformModes.NormalOrdering (vacuumPair vacuumPair_apply)
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
local notation "Q" => WakModule k ⧸ QuotVOA.maxGradedIdeal (universal k hk)

/-- The abstract colour current of the constructed affine representation is
literally the actual lifted quotient current, in colour order (e,f,h). -/
theorem simple_normalizedCurrentData_J (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    (a : Fin 3) (n : ℤ) :
    SingularNorm.J (simple_normalizedCurrentData k hk hk0 D hD hnorm δ hδ) a n =
      liftedMode D (simpleCurrent k hk a) n := by
  change liftedMode D (affineCurrent k hk hk0 (basis a)) n = _
  rw [affineCurrent_basis]
  rfl

/-- The word notation used for quotient relations agrees with the generic
normal-ordering notation, including the order of composition. -/
theorem liftedCurrentWord_eq (D : FirstOrderDeformation (simple k hk))
    (w : List (Fin 3 × ℤ)) :
    liftedCurrentWord k hk D w =
      NormalOrdering.currentWord (fun a n => liftedMode D (simpleCurrent k hk a) n) w := by
  induction w with
  | nil => rfl
  | cons an w ih => simp only [liftedCurrentWord, NormalOrdering.currentWord, ih]

/-- The same identification for undeformed currents. -/
theorem currentWord_eq (w : List (Fin 3 × ℤ)) :
    currentWord k hk w = NormalOrdering.currentWord
      (fun a n => mode ((simple k hk).Y (simpleCurrent k hk a)) n) w := by
  induction w with
  | nil => rfl
  | cons an w ih => simp only [currentWord, NormalOrdering.currentWord, ih]

/-- At every nonzero noncritical level, every normalized graded deformation
has the actual word pairing prescribed by the universal polynomial at k+δt.
No singular-vector or determinant premise occurs in this identity. -/
theorem simple_normalized_word_pairing (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    (w : List (Fin 3 × ℤ)) :
    vacuumPair (simpleForm k hk)
      (liftedCurrentWord k hk D w ((simple k hk).vacuum,0)) =
        (NormalOrdering.wordPolynomial w).aeval (inl k + inr δ) := by
  let A := simple_normalizedCurrentData k hk hk0 D hD hnorm δ hδ
  have hA : SingularNorm.J A = fun a n => liftedMode D (simpleCurrent k hk a) n := by
    funext a n
    exact simple_normalizedCurrentData_J k hk hk0 D hD hnorm δ hδ a n
  have hK : A.central = dualScalarAction (inl k + inr δ) := by
    simp only [dualScalarAction, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
      add_zero, zero_add, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl
  rw [liftedCurrentWord_eq]
  exact NormalOrdering.vacuumPair_word D hD (simpleCurrent k hk) (simpleCurrent_mem k hk)
    (simpleForm k hk) (simpleForm_normalized k hk) A hA _ hK w

/-- The actual tangent pairing is the ordinary derivative of the constructed
level polynomial multiplied by the actual normalized pole scalar. -/
theorem simple_normalized_word_tangent (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * δ) • (simple k hk).vacuum)
    (w : List (Fin 3 × ℤ)) :
    (simpleForm k hk).form (simple k hk).vacuum
      (liftedCurrentWord k hk D w ((simple k hk).vacuum,0)).2 =
        (NormalOrdering.wordPolynomial w).derivative.eval k * δ := by
  have h := congrArg TrivSqZeroExt.snd
    (simple_normalized_word_pairing k hk hk0 D hD hnorm δ hδ w)
  rw [VirRigidTangent.aeval_dual] at h
  simpa [vacuumPair_apply] using h

include hk0 in
/-- Scalar specialization of the same constructed polynomial is the actual
ordinary simple-quotient vacuum pairing. This follows by taking the constant
coordinate of the zero deformation, and holds even when the quotient has relations. -/
theorem wordPolynomial_eval (w : List (Fin 3 × ℤ)) :
    (NormalOrdering.wordPolynomial w).eval k = (simpleForm k hk).form (simple k hk).vacuum
      (currentWord k hk w (simple k hk).vacuum) := by
  let D := zeroDeformation (simple k hk)
  have hD : D.IsGraded := by intro p q u hu v hv n; exact Submodule.zero_mem _
  have hn : D.InPoleForm := by intro a ha b hb; rfl
  have hd : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * (0:ℂ)) • (simple k hk).vacuum := by
    intro a b
    simp [D, FirstOrderDeformation.poleVec, FirstOrderDeformation.smul₁, zeroDeformation]
  have h := congrArg TrivSqZeroExt.fst
    (simple_normalized_word_pairing k hk hk0 D hD hn 0 hd w)
  rw [VirRigidTangent.aeval_dual] at h
  simpa [vacuumPair_apply, liftedCurrentWord_fst] using h.symm

/-- Reversing a word and negating its literal mode indices gives the adjoint
indices. Each weight-one adjoint also contributes a separate minus sign. -/
def adjointIndices (w : List (Fin 3 × ℤ)) : List (Fin 3 × ℤ) :=
  w.reverse.map (fun an => (an.1,-an.2))

/-- The explicit lifted adjoint is the reversed mode word with one minus sign
per current. This is an operator identity, not an invariance assumption. -/
theorem liftedAdjointCurrentWord_eq (D : FirstOrderDeformation (simple k hk))
    (w : List (Fin 3 × ℤ)) :
    liftedAdjointCurrentWord k hk D w =
      ((-1:ℂ)^w.length) • liftedCurrentWord k hk D (adjointIndices w) := by
  induction w with
  | nil => simp [liftedAdjointCurrentWord, adjointIndices, liftedCurrentWord]
  | cons an w ih =>
    rw [liftedAdjointCurrentWord, ih]
    simp only [adjointIndices, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      liftedCurrentWord_eq, NormalOrdering.currentWord_append, NormalOrdering.currentWord,
      mul_one, List.length_cons, pow_succ, smul_mul_assoc, mul_neg, neg_smul]

/-- Ordinary adjoint words have the same explicit sign and index reversal. -/
theorem adjointCurrentWord_eq (w : List (Fin 3 × ℤ)) :
    adjointCurrentWord k hk w = ((-1:ℂ)^w.length) • currentWord k hk (adjointIndices w) := by
  induction w with
  | nil => simp [adjointCurrentWord, adjointIndices, currentWord]
  | cons an w ih =>
    rw [adjointCurrentWord, ih]
    simp only [adjointIndices, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      currentWord_eq, NormalOrdering.currentWord_append, NormalOrdering.currentWord,
      mul_one, List.length_cons, pow_succ, smul_mul_assoc, mul_neg, neg_smul]

end VOA.AffineSl2GeneralRigidity
