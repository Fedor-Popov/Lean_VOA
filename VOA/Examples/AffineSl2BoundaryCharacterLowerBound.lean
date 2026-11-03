import VOA.Commutative.PolynomialMatrixRootOrder
import VOA.Examples.AffineSl2VacuumDeterminantOrder
import VOA.Examples.AffineSl2ChargeDecomposition

/-! # The actual simple-character lower bound from determinant root orders

This bound concerns the actual maximal-ideal quotient, using its proved Gram
rank identification. No resolution or radical-generation premise is required.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule VertexOperatorAlgebra
noncomputable section
open scoped Classical

/-- The actual simple joint dimension loses no more than the determinant root order. -/
theorem simpleJointPiece_finrank_add_rootOrder_ge (k : ℂ) (hk : k+2 ≠ 0)
    (n : ℕ) (c : ℤ) :
    Fintype.card (JointIndex n (2*c)) ≤
      Module.finrank ℂ (simpleJointPiece k hk n (2*c)) +
        (vacuumChevalleyPolynomial n c).det.rootMultiplicity k := by
  rw [simpleJointPiece_finrank_eq_gramRank]
  have h := PolynomialMatrix.finrank_ker_le_rootMultiplicity
    (vacuumChevalleyPolynomial n c) k
    (Wak.Charged.vacuumChevalleyPolynomial_det_ne_zero n c)
  have he := (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at he
  change Module.finrank ℂ (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).mulVecLin.range +
      Module.finrank ℂ (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).mulVecLin.ker =
      Fintype.card (JointIndex n (2*c)) at he
  change (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).rank +
      Module.finrank ℂ (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).mulVecLin.ker = _ at he
  change Fintype.card (JointIndex n (2*c)) ≤
      (PolynomialMatrix.evaluate (vacuumChevalleyPolynomial n c) k).rank + _
  omega

/-- Total root order of the actual finite vacuum Gram blocks in one conformal grade. -/
def vacuumRootOrderTotal (k : ℂ) (N : ℕ) : ℕ :=
  ∑ c ∈ chargeWindow N, (vacuumChevalleyPolynomial N c).det.rootMultiplicity k

/-- The actual ordinary simple character loses at most the total determinant root order. -/
theorem universal_grading_finrank_le_simple_add_rootOrder (k : ℂ) (hk : k+2 ≠ 0)
    (N : ℕ) :
    Module.finrank ℂ ((universal k hk).grading N) ≤
      Module.finrank ℂ ((simple k hk).grading N) + vacuumRootOrderTotal k N := by
  have h := Finset.sum_le_sum (fun c (_ : c ∈ chargeWindow N) =>
    simpleJointPiece_finrank_add_rootOrder_ge k hk N c)
  rw [Finset.sum_add_distrib, ← universal_grading_finrank_eq_sum_joint k hk N,
    ← simple_grading_finrank_eq_sum_joint k hk N] at h
  exact h

end
end VOA.AffineSl2GeneralRigidity
