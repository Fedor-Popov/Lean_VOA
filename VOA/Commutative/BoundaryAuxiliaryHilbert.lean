/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.BoundaryAuxiliaryGrading
import VOA.Commutative.WeightedInitialAssociated

/-!
# The genuine auxiliary degeneration Hilbert inequality

The fixed conformal pieces are images in the actual infinite arc quotients.
Initial-relation containment and the finite auxiliary filtration prove that
`B_m` has no larger conformal pieces than `C_m`.
-/
namespace VOA.BoundaryAuxiliary
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Conformal weight `N` in the original arc presentation. -/
def sourcePiece (m N : ℕ) : Submodule K (Source (R := K) m) :=
  (MvPolynomial.weightedHomogeneousSubmodule K conformalWeight N).map
    (Ideal.Quotient.mkₐ K (sourceIdeal (R := K) m)).toLinearMap

/-- Conformal weight `N` in the auxiliary arc presentation. -/
def auxiliaryPiece (m N : ℕ) : Submodule K (Auxiliary (R := K) m) :=
  (MvPolynomial.weightedHomogeneousSubmodule K conformalWeight N).map
    (Ideal.Quotient.mkₐ K (auxiliaryIdeal (R := K) m)).toLinearMap

/-- Every original homogeneous projection stays in the actual relation ideal. -/
theorem sourceIdeal_component_mem (m N : ℕ) (f : JetPoly K)
    (hf : f ∈ sourceIdeal (R := K) m) :
    MvPolynomial.weightedHomogeneousComponent conformalWeight N f ∈
      sourceIdeal (R := K) m := by
  letI := MvPolynomial.weightedGradedAlgebra K conformalWeight
  have h := sourceIdeal_conformalHomogeneous (R := K) m N hf
  change (MvPolynomial.decompose' K conformalWeight f N : JetPoly K) ∈ _ at h
  simpa only [MvPolynomial.decompose'_apply] using h

/-- The original arc piece is genuinely finite dimensional. -/
theorem finiteDimensional_sourcePiece (m N : ℕ) :
    FiniteDimensional K (sourcePiece (K := K) m N) := by
  letI := finiteDimensional_conformalPiece (K := K) N
  exact Module.Finite.map _ _

/-- The auxiliary arc piece is genuinely finite dimensional. -/
theorem finiteDimensional_auxiliaryPiece (m N : ℕ) :
    FiniteDimensional K (auxiliaryPiece (K := K) m N) := by
  letI := finiteDimensional_conformalPiece (K := K) N
  exact Module.Finite.map _ _

/-- Proposition 2.3 on actual arc algebras, with no degeneration map or Hilbert
inequality supplied as an assumption. -/
theorem sourcePiece_finrank_le_auxiliaryPiece (m N : ℕ) :
    Module.finrank K (sourcePiece (K := K) m N) ≤
      Module.finrank K (auxiliaryPiece (K := K) m N) := by
  letI := finiteDimensional_conformalPiece (K := K) N
  exact VOA.WeightedInitial.quotientMap_finrank_le auxWeight conformalWeight
    (sourceIdeal (R := K) m) (auxiliaryIdeal (R := K) m) N
    auxWeight_le_conformalWeight (sourceIdeal_component_mem m N)
    (auxiliaryIdeal_le_initialIdeal m)

end
end VOA.BoundaryAuxiliary
