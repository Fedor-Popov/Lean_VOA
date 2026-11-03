import VOA.DeligneAudit.DeligneFusionCVResidualThetaIdeal
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCases
import VOA.DeligneAudit.DeligneFusionCVRectFilteredIdeal

/-!
# Actual residual theta coefficient-ideal inclusion and dimension transfer

Every adjoint polynomial coefficient annihilates the actual PBW cyclic
source. The quotient map and filtered transfer are the proved generic ones;
the source's finite-dimensionality is a conclusion of the polynomial bound.
-/

namespace VOA.DeligneAudit.A2.CVResidualThetaRelations

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectFiltered VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectStarIdeal VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectStarBase VOA.DeligneAudit.A2.CVRectAdjointFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ϱ : Weight}

/-- All mixed graded source relations follow from actual residual CV data. -/
theorem graded_all_residual (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (p q r s : ℕ)
    (hs : clippedSum (parts ϱ.1 0 1) (p + q) +
      clippedSum (parts ϱ.2 0 1) (q + r) < s + (p + q + r)) :
    gradedOrderedCoeff R w p q r s = 0 :=
  graded_all_of_two_theta (weaken h) (theta_second_two_graded h)
    (first_theta_two_graded h) p q r s hs

/-- The residual first-root current has its actual source cutoff. -/
theorem first_high (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (q : ℕ) (hq : ϱ.1 + 1 ≤ q) : R.op 3 q w = 0 := by
  apply trunc_of_cvrel h.first
  simpa only [parts_length, Nat.zero_add, Nat.add_zero] using hq

/-- The residual second-root current has its actual source cutoff. -/
theorem second_high (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (q : ℕ) (hq : ϱ.2 + 1 ≤ q) : R.op 4 q w = 0 := by
  apply trunc_of_cvrel h.second
  simpa only [parts_length, Nat.zero_add, Nat.add_zero] using hq

/-- The entire canonical adjoint coefficient ideal annihilates the actual
residual PBW generator. No ideal inclusion is assumed. -/
theorem residual_ideal_le_ker (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) :
    (CVRectAdjointFamily.ideal (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1)
      (residualOrder ϱ)).restrictScalars ℂ ≤ LinearMap.ker
        (polyEval R w (modeLetter (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1))) := by
  apply span_le_polyEval_ker
  rintro P ⟨p, q, r, j, hj, rfl⟩
  by_cases hD : j ≤ reverseDegree (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) p q r
  · rw [starCoeff_eval R w _ _ _ p q r j (first_high h) (theta_high h) (second_high h) hD]
    exact graded_all_residual h p q r _ (residual_reverse_region ϱ p q r j hj hD)
  · exact starCoeff_eval_high R w _ _ _ p q r j (by omega)

/-- Actual source dimension transfer from the canonical adjoint polynomial
quotient. Its finiteness premise will be supplied by the proved polynomial
count, independently of the source CV representation. -/
theorem source_bound_of_adjoint_polynomial
    (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) (hspan : currentCyclic R w = ⊤)
    [FiniteDimensional ℂ (StarRing (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) ⧸
      (CVRectAdjointFamily.ideal (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1)
        (residualOrder ϱ)).restrictScalars ℂ)] :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ Module.finrank ℂ
      (StarRing (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) ⧸
        (CVRectAdjointFamily.ideal (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1)
          (residualOrder ϱ)).restrictScalars ℂ) :=
  source_bound_of_polynomial h hspan
    (modeLetter (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1))
    (CVRectAdjointFamily.ideal (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) (residualOrder ϱ))
    (residual_ideal_le_ker h)
    (modeLetter_cover R w _ _ _ (first_high h) (theta_high h) (second_high h))

end
end VOA.DeligneAudit.A2.CVResidualThetaRelations

#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.graded_all_residual
#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.residual_ideal_le_ker
#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.source_bound_of_adjoint_polynomial
