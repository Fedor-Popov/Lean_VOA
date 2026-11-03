/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumChevalleyGram

/-!
# Using the actual Chevalley vacuum determinant for deformation rigidity

Its two kernel vectors give actual quotient relations. The first is twisted
by the fixed Chevalley involution, while invariance of the actual radical
untwists the second. The explicit signed word polynomial supplies precisely
the derivative already controlled by the deformation obstruction.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule VertexOperatorAlgebra
open scoped Classical
noncomputable section
variable (k : ℂ) (hk : k+2≠0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- The actual Chevalley involution preserves membership in the maximal
ideal. This follows from the canonical radical, not from a singular presentation. -/
theorem vacuumChevalley_ideal_iff (x : WakModule k) : vacuumChevalley k x∈I ↔ x∈I := by
  have hf : ∀x : WakModule k,vacuumChevalley k x∈I → x∈I := by
    intro x hx
    have hr := (LiRadical.mem_maxGradedIdeal_iff (universalForm_invariant k hk)
      (universalForm_normalized k hk)).mp hx
    rw [← LiRadical.rightRadical_eq_maxGradedIdeal
      (universalForm_invariant k hk) (universalForm_normalized k hk),SingVec.mem_rightRadical]
    intro y
    have he := vacuumChevalley_form_symm k hk x (vacuumChevalley k y)
    rw [vacuumChevalley_involutive k hk y] at he
    exact he.symm.trans (hr _)
  refine ⟨hf x,fun hx => hf (vacuumChevalley k x) ?_⟩
  rwa [vacuumChevalley_involutive k hk x]

/-- The Chevalley vacuum matrix is genuinely symmetric, with coefficients
fixed as central polynomials rather than only at the selected level. -/
theorem vacuumChevalleyPolynomial_symm (n : ℕ) (c : ℤ) (i j : JointIndex n (2*c)) :
    vacuumChevalleyPolynomial n c i j=vacuumChevalleyPolynomial n c j i := by
  apply Polynomial.funext
  intro z
  rw [vacuumChevalleyPolynomial_eval,vacuumChevalleyPolynomial_eval]
  exact contravariant_symm z 0 _ _

/-- A row kernel in the Chevalley block gives an actual maximal-ideal
state after applying the fixed involution to its PBW combination. -/
theorem vacuumChevalley_kernel_ideal (n : ℕ) (c : ℤ) (r : JointIndex n (2*c)→ℂ)
    (hr : ∀j,∑i,r i*(vacuumChevalleyPolynomial n c i j).eval k=0) :
    vacuumChevalley k (∑i,r i • currentPBWBasis k hk i.val)∈I := by
  have hx : (∑i,r i • currentPBWBasis k hk i.val)∈jointSpace k hk n (2*c) :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have ht := vacuumChevalley_mem_joint k hk n (2*c) _ hx
  apply (joint_mem_maxIdeal_iff k hk n (-(2*c)) _ ht).mpr
  intro j
  have hj : currentEnergy j.val=(n : ℤ) ∧ currentCharge j.val=2*c := by
    simpa only [neg_neg] using j.property
  let jj : JointIndex n (2*c) := ⟨j.val,hj⟩
  simpa only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
    vacuumChevalleyPolynomial_actual k hk] using hr jj

/-- A simple root of the actual Chevalley vacuum determinant forces
triviality of every graded first-order deformation at a nonzero noncritical level. -/
theorem graded_rigidity_of_vacuum_simple_root (hk0 : k≠0) (n : ℕ) (c : ℤ)
    (hz : (vacuumChevalleyPolynomial n c).det.eval k=0)
    (hd : (vacuumChevalleyPolynomial n c).det.derivative.eval k≠0) :
    Deform.IsRigidGraded (simple k hk) := by
  obtain ⟨r,s,hr,hs,hp⟩ := PolynomialMatrix.kernel_pair_of_simple_root
    (vacuumChevalleyPolynomial n c) k hz hd
  have hir := vacuumChevalley_kernel_ideal k hk n c r hr
  have his : (∑i,s i • currentPBWBasis k hk i.val)∈I := by
    apply (vacuumChevalley_ideal_iff k hk _).mp
    apply vacuumChevalley_kernel_ideal k hk n c s
    intro j
    have he := hs j
    simpa only [vacuumChevalleyPolynomial_symm n c j,mul_comm] using he
  have hqr : (I).mkQ (vacuumChevalley k (∑i,r i • currentPBWBasis k hk i.val))=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hir
  have hqs : (I).mkQ (∑i,s i • currentPBWBasis k hk i.val)=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr his
  let u := fun i : JointIndex n (2*c) => flipCurrentWord (jointWord n (2*c) i)
  let a := fun i : JointIndex n (2*c) => r i*((-1 : ℂ)^(jointWord n (2*c) i).length)
  have hru : ∑i,a i • currentWord k hk (u i) (simple k hk).vacuum=0 := by
    simp only [map_sum,map_smul,← jointWord_state k hk n (2*c)] at hqr
    change (∑i,r i • (I).mkQ (vacuumChevalley k
      (NormalOrdering.currentWord (J k) (jointWord n (2*c) i) (vacuumA k))))=0 at hqr
    simp only [vacuumChevalley_word,map_smul,smul_smul,universalWord_mkQ] at hqr
    exact hqr
  have hsv : ∑i,s i • currentWord k hk (jointWord n (2*c) i) (simple k hk).vacuum=0 := by
    simpa only [map_sum,map_smul,← jointWord_state k hk n (2*c),universalWord_mkQ] using hqs
  apply graded_rigidity_of_relations k hk hk0 u a (jointWord n (2*c)) s hru hsv
  have he : relationPairPolynomial u a (jointWord n (2*c)) s=
      ∑i,∑j,(r i*s j) • vacuumChevalleyPolynomial n c i j := by
    simp only [relationPairPolynomial,vacuumChevalleyPolynomial_word,smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [u,a]
    congr 1
    ring
  rw [he]
  simpa only [map_sum,map_smul,Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul] using hp

end
end VOA.AffineSl2GeneralRigidity
