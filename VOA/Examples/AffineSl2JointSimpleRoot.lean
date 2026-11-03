/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointChargeFlip
import VOA.Core.PolynomialMatrixSimpleRoot

/-!
# A simple joint affine determinant root implies graded rigidity

The adjugate supplies two ordinary kernel vectors with nonzero derivative
pairing. The left and right radicals of the canonical form both equal the
maximal ideal, so both vectors give actual simple-quotient relations. The
existing two-relation deformation obstruction then proves rigidity. No
preservation of Cartan weight by a deformed state is required. This theorem
still requires an ordinary simple determinant root; it does not prove the
affine admissible determinant formula or its multiplicities.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA Deform VertexOperatorAlgebra Polynomial
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- A state in the opposite joint space belongs to the maximal ideal exactly
when its column on the original joint PBW basis vanishes. Equality of the
left and right radicals suffices; full symmetry of the form is not assumed. -/
theorem joint_mem_maxIdeal_iff_right (n h : ℤ) (x : WakModule k)
    (hx : x ∈ jointSpace k hk n (-h)) :
    x ∈ I ↔ ∀ i : JointIndex n h,
      (universalForm k hk).form (currentPBWBasis k hk i.val) x = 0 := by
  rw [← LiRadical.rightRadical_eq_maxGradedIdeal
    (universalForm_invariant k hk) (universalForm_normalized k hk), SingVec.mem_rightRadical]
  constructor
  · intro hz i; exact hz _
  · intro hz y
    have he : (universalForm k hk).form.flip x = 0 := by
      apply (currentPBWBasis k hk).ext
      intro mu
      change (universalForm k hk).form (currentPBWBasis k hk mu) x = 0
      by_cases hm : currentEnergy mu = n ∧ currentCharge mu = h
      · exact hz ⟨mu,hm⟩
      · have hy : currentPBWBasis k hk mu ∈
            jointSpace k hk (currentEnergy mu) (currentCharge mu) :=
          Submodule.subset_span ⟨⟨mu,rfl,rfl⟩,rfl⟩
        apply universalForm_joint_orthogonal k hk _ _ n (-h) _ x hy hx
        omega
    exact LinearMap.congr_fun he y

include hk0

/-- A column kernel of the square joint Gram block becomes an actual
opposite-charge word relation in the simple quotient. -/
theorem jointGramSquare_column_relation (n h : ℤ) (c : JointIndex n h → ℂ)
    (hc : ∀ i, ∑ j, (jointGramSquare n h i j).eval k * c j = 0) :
    ∑ j, c j • currentWord k hk
      (jointWord n (-h) (jointChargeEquiv n h j)) (simple k hk).vacuum = 0 := by
  have hx : (∑ j, c j • currentPBWBasis k hk (jointChargeEquiv n h j).val) ∈
      jointSpace k hk n (-h) :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨jointChargeEquiv n h j,rfl⟩))
  have hm := (joint_mem_maxIdeal_iff_right k hk n h _ hx).mpr (fun i => by
    simpa only [jointGramSquare, jointGramPolynomial_eval k hk hk0,
      map_sum, map_smul, smul_eq_mul, mul_comm] using hc i)
  have hz : (I).mkQ (∑ j, c j • currentPBWBasis k hk (jointChargeEquiv n h j).val) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  simpa only [map_sum, map_smul, ← jointWord_state, universalWord_mkQ] using hz

/-- A simple zero of the actual joint determinant produces two ordinary
quotient relations with nonzero derivative of their universal pairing.
Both kernel vectors and both relations are constructed internally. -/
theorem jointDeterminant_simple_root_relations (n h : ℤ)
    (hz : (jointDeterminant n h).eval k = 0)
    (hd : (jointDeterminant n h).derivative.eval k ≠ 0) :
    ∃ r c : JointIndex n h → ℂ,
      (∑ i, r i • currentWord k hk (jointWord n h i) (simple k hk).vacuum = 0) ∧
      (∑ j, c j • currentWord k hk (jointWord n (-h) (jointChargeEquiv n h j))
        (simple k hk).vacuum = 0) ∧
      (relationPairPolynomial (jointWord n h) r
        (fun j => jointWord n (-h) (jointChargeEquiv n h j)) c).derivative.eval k ≠ 0 := by
  classical
  obtain ⟨r,c,hr,hc,hp⟩ := PolynomialMatrix.kernel_pair_of_simple_root
    (jointGramSquare n h) k hz hd
  refine ⟨r,c,jointGram_row_relation k hk hk0 n h r ?_,
    jointGramSquare_column_relation k hk hk0 n h c hc, ?_⟩
  · intro j
    obtain ⟨i,rfl⟩ := (jointChargeEquiv n h).surjective j
    exact hr i
  · simpa only [relationPairPolynomial, map_sum, map_smul, eval_finsetSum,
      eval_smul, smul_eq_mul, jointGramSquare, jointGramPolynomial, wordGramMatrix] using hp

/-- At any nonzero noncritical level, a simple zero of any actual joint
energy/Cartan determinant forces every graded first-order deformation to be
trivial. The ordinary root and derivative are the only remaining inputs;
no singular presentation, deformed Cartan condition or pairing premise is
assumed. -/
theorem graded_rigidity_of_joint_simple_root (n h : ℤ)
    (hz : (jointDeterminant n h).eval k = 0)
    (hd : (jointDeterminant n h).derivative.eval k ≠ 0) :
    IsRigidGraded (simple k hk) := by
  obtain ⟨r,c,hr,hc,hp⟩ := jointDeterminant_simple_root_relations k hk hk0 n h hz hd
  exact graded_rigidity_of_relations k hk hk0 (jointWord n h) r
    (fun j => jointWord n (-h) (jointChargeEquiv n h j)) c hr hc hp

end VOA.AffineSl2GeneralRigidity
