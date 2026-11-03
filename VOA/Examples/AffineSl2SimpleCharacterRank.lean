/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleCharacterRange
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Actual simple affine joint dimensions as explicit finite Gram ranks

This is an unconditional all-degree identification with the genuine maximal-ideal
quotient. It does not assume or assert the unresolved full character product.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule VertexOperatorAlgebra
noncomputable section

/-- Synthesis of a finite joint block using the proved actual current PBW basis. -/
def jointSynthesis (k : ℂ) (hk : k + 2 ≠ 0) (n : ℕ) (c : ℤ) :
    (JointIndex n (2 * c) → ℂ) →ₗ[ℂ] WakModule k where
  toFun r := ∑ i, r i • currentPBWBasis k hk i.val
  map_add' r s := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a r := by simp [Finset.smul_sum, smul_smul]

theorem jointSynthesis_range (k : ℂ) (hk : k + 2 ≠ 0) (n : ℕ) (c : ℤ) :
    (jointSynthesis k hk n c).range = jointSpace k hk n (2 * c) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  · intro hx
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    exact ⟨r, hr⟩

/-- The concrete central-polynomial Gram matrix specialized at the actual level. -/
def actualJointGram (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n (2 * c)) (JointIndex n (2 * c)) ℂ := by
  classical
  exact (Polynomial.evalRingHom k).mapMatrix (vacuumChevalleyPolynomial n c)

/-- The exact row-kernel equals the genuine maximal-ideal relations among
these PBW states, at every energy and charge. -/
theorem jointSynthesis_mem_maxIdeal_iff (k : ℂ) (hk : k + 2 ≠ 0)
    (n : ℕ) (c : ℤ) (r : JointIndex n (2 * c) → ℂ) :
    jointSynthesis k hk n c r ∈ QuotVOA.maxGradedIdeal (universal k hk) ↔
      (actualJointGram k n c).vecMulLinear r = 0 := by
  constructor
  · intro hi
    have ht := (vacuumChevalley_ideal_iff k hk _).mpr hi
    have hz := (LiRadical.mem_maxGradedIdeal_iff (universalForm_invariant k hk)
      (universalForm_normalized k hk)).mp ht
    funext j
    change (∑ i, r i * (vacuumChevalleyPolynomial n c i j).eval k) = 0
    have he := hz (currentPBWBasis k hk j.val)
    simpa only [jointSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      vacuumChevalleyPolynomial_actual k hk, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he
  · intro hr
    apply (vacuumChevalley_ideal_iff k hk _).mp
    apply vacuumChevalley_kernel_ideal k hk n c r
    intro j
    exact congrFun hr j

/-- The actual simple quotient has precisely the rank of the explicit Gram
block in every degree; no admissibility assumption is needed. -/
theorem simpleJointPiece_finrank_eq_gramRank (k : ℂ) (hk : k + 2 ≠ 0)
    (n : ℕ) (c : ℤ) :
    Module.finrank ℂ (simpleJointPiece k hk n (2 * c)) = (actualJointGram k n c).rank := by
  let Q := (QuotVOA.maxGradedIdeal (universal k hk)).mkQ.comp (jointSynthesis k hk n c)
  have hker : Q.ker = (actualJointGram k n c).vecMulLinear.ker := by
    ext r
    change (QuotVOA.maxGradedIdeal (universal k hk)).mkQ (jointSynthesis k hk n c r) = 0 ↔ _
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact jointSynthesis_mem_maxIdeal_iff k hk n c r
  have hrange : Q.range = simpleJointPiece k hk n (2 * c) := by
    rw [LinearMap.range_comp, jointSynthesis_range]
    rfl
  have hq := Q.finrank_range_add_finrank_ker
  have hg := (actualJointGram k n c).vecMulLinear.finrank_range_add_finrank_ker
  rw [hker, hrange] at hq
  have hd : Module.finrank ℂ (simpleJointPiece k hk n (2 * c)) =
      Module.finrank ℂ (actualJointGram k n c).vecMulLinear.range := by omega
  rw [hd, ← Matrix.mulVecLin_transpose, ← Matrix.rank, Matrix.rank_transpose]

end
end VOA.AffineSl2GeneralRigidity
