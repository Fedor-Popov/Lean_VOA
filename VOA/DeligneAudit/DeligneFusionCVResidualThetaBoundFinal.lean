import VOA.DeligneAudit.DeligneFusionCVResidualThetaBound
import VOA.DeligneAudit.DeligneFusionCVRectAdjointBound
import VOA.DeligneAudit.DeligneFusionCVTotal
import VOA.DeligneAudit.DeligneFusionCVUnivQuotient

/-!
# The proved residual level-three theta bound

The actual residual coefficient-ideal inclusion and the independent proved
adjoint polynomial count give the source bound. Universal word spanning
then supplies the residual base proposition. No ideal,
fusion identification, dimension estimate or recurrence is assumed.
-/

namespace VOA.DeligneAudit.A2.CVResidualThetaRelations

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectFiltered
open VOA.DeligneAudit.A2.CVRectStarBase VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectAdjointFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ϱ : Weight}

set_option maxHeartbeats 20000 in
-- Transport whole coordinate propositions before quotient dimension inference.
/-- The complete actual residual source has the sharp published product upper
bound, from proved source relations and the actual polynomial quotient count. -/
theorem residual_source_bound (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (hspan : currentCyclic R w = ⊤) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ 8 * 10 ^ (ϱ.1 + ϱ.2) := by
  have hb := CVRectAdjointBound.adjoint_cubes_bound ϱ.1 ϱ.2
  let P : (ℕ × ℕ × ℕ) → Prop := fun d =>
    FiniteDimensional ℂ (Model d.1 d.2.1 d.2.2 (residualOrder ϱ)) ∧
      Module.finrank ℂ (Model d.1 d.2.1 d.2.2 (residualOrder ϱ)) ≤
        8 * 10 ^ (ϱ.1 + ϱ.2)
  have hb0 : P ((List.replicate ϱ.1 3).length + 1,
      (List.replicate ϱ.1 3).length + (List.replicate ϱ.2 3).length +
        ([] : List ℕ).length + 1, (List.replicate ϱ.2 3).length + 1) :=
    hb
  have hcoord : ((List.replicate ϱ.1 3).length + 1,
      (List.replicate ϱ.1 3).length + (List.replicate ϱ.2 3).length +
        ([] : List ℕ).length + 1, (List.replicate ϱ.2 3).length + 1) =
        (ϱ.1 + 1, ϱ.1 + ϱ.2 + 1, ϱ.2 + 1) := by
    simp only [List.length_replicate, List.length_nil, Nat.add_zero]
  have hpoly : P (ϱ.1 + 1, ϱ.1 + ϱ.2 + 1, ϱ.2 + 1) := (congrArg P hcoord).mp hb0
  let I := CVRectAdjointFamily.ideal (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1)
    (residualOrder ϱ)
  haveI := hpoly.1
  let E : (StarRing (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) ⧸ I.restrictScalars ℂ) ≃ₗ[ℂ]
      (StarRing (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) ⧸ I) :=
    Submodule.Quotient.restrictScalarsEquiv ℂ I
  haveI := E.symm.finiteDimensional
  obtain ⟨hFD, hdim⟩ := source_bound_of_adjoint_polynomial h hspan
  exact ⟨hFD, hdim.trans (E.finrank_eq.le.trans hpoly.2)⟩

end
end VOA.DeligneAudit.A2.CVResidualThetaRelations

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.DeligneAudit.A2.CVRectFiltered
open VOA.DeligneAudit.A2.CVResidualThetaRelations

noncomputable section

/-- The actual residual level-three base family is proved. -/
theorem residualTheta3Bound : ResidualTheta3Bound := by
  intro ϱ
  exact residual_source_bound (cvUniv_rel (0, 0) (0, 0) ϱ 1)
    (cv_span_top (0, 0) (0, 0) ϱ 1)

end
end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.residual_source_bound
#print axioms VOA.DeligneAudit.A2.CVUniv.residualTheta3Bound
